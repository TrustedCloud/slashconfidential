using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.IO;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;

namespace CfiVerifier
{
    public class EnvironmentSetup : StandardVisitor
    {
        private Function load_64, lt_64, ge_64, minus_64;
        private Function writable;
        private Function addrInStack;
        private Function triggerFn;

        private Constant _guard_writeTable_ptr;
        private Constant _guard_callTable_ptr;
        private Constant _bitmap_low;
        private Constant _bitmap_high;
        private Constant _stack_low;
        private Constant _stack_high;
        private Constant _virtual_address_space_low;
        private Constant _virtual_address_space_high;

        private GlobalVariable mem;
        private GlobalVariable mem_stack;
        private GlobalVariable mem_bitmap;
        private GlobalVariable RSP;

        Program _prog;

        /*
         * Memory layout:
         *   1073745920 (_bitmap_low / virtual_high / data_high) to 1090523136 (_bitmap_high) 
         *        holds the bitmap corresponding to addresses virtual_low to virtual_high
         *   0537919488 (_stack_high) to 1073745920 (_bitmap_low / _data_high) holds regular memory (which includes the heap)
         *   0536870912 (_stack_low / _data_low)  to 0537919488 (_stack_high) holds the stack of 1 MB size
         *   0536866816 (_guard_low) to 0536870912 (_stack_low) holds a guard page of 4 KB size, which is non readable and non-writable
         *   0 (_virtual_low) to _guard_low holds non-data pages
         */

        //returns <vspace_low, vspace_high, bitmap_low, bitmap_high, stack_low, stack_high, RSP_lowerbound, RSP_upperbound>
        private Tuple<Tuple<int, int>, Tuple<int, int>, Tuple<int, int>, Tuple<int, int>> computeMemoryLayout(Implementation impl)
        {
            //The assumption is that the bitmap covers all addresses from 0 until 0x40000000
            int vspace_low, vspace_high, bitmap_low, bitmap_high, stack_low, stack_high, RSP_lowerbound, RSP_upperbound;

            //const unsigned __int64 enclaveStart = 0x20000000; //536870912 
            int enclaveStart = 536870912;
            //const unsigned __int64 enclaveSize = 1 << 29; //512MB //536870912
            int enclaveSize = 536870912;
            vspace_low = 0; //was enclaveStart;
            vspace_high = enclaveStart + enclaveSize;
            int vspace_size = vspace_high - vspace_low;

            StackSizeEstimator estimator = new StackSizeEstimator();
            estimator.Visit(impl); //necessary before querying the stack size estimate
            int stack_size = estimator.getStackEstimate(1024); //default size of 1 KB. //TODO: this affects constraints on init RSP, so think about soundness
            Console.WriteLine("Estimated stack size: {0}", stack_size);
            //Utils.Assert(stack_size + 128 < 8388608, "computeMemoryLayout: UNEXPECTED! this function uses a stack larger than 8MB");

            //stack_high = (stack_size + 128) rounded up to the next MB
            int padded_stack_size = stack_size + 128; //padded with 64 bytes on either end
            stack_high = enclaveStart + (((padded_stack_size >> 20) + 1) << 20);
            stack_low = enclaveStart;

            RSP_lowerbound = stack_low + 64 + stack_size; //at least enough room for stack_size
            RSP_upperbound = stack_high - 64;

            //bitmap_low starts at the next MB boundary after stack_high
            int bitmap_size = (vspace_size % 64 == 0) ? vspace_size >> 6 :
                  (int)Math.Ceiling((double)(vspace_size / 64));
            Console.WriteLine("Estimated bitmap size: {0}", bitmap_size);
            //bitmap_low = ((stack_high >> 20) + 1) << 20; 
            bitmap_low = vspace_high + 4096; //FIXME: putting bitmap outside enclave region because we need to assume bitmap is writable
            bitmap_high = bitmap_low + bitmap_size;

            return new Tuple<Tuple<int, int>, Tuple<int, int>, Tuple<int, int>, Tuple<int, int>>
              (new Tuple<int, int>(vspace_low, vspace_high),
               new Tuple<int, int>(bitmap_low, bitmap_high),
               new Tuple<int, int>(stack_low, stack_high),
               new Tuple<int, int>(RSP_lowerbound, RSP_upperbound));
        }

        public override Program VisitProgram(Program node)
        {
            this._prog = node;

            this.load_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LOAD_LE_64"));
            Utils.Assert(this.load_64 != null, "Could not find LOAD_LE_64(.,.) function");
            this.lt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LT_64"));
            Utils.Assert(this.lt_64 != null, "Could not find LT_64(.,.) function");
            this.ge_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GE_64"));
            Utils.Assert(this.ge_64 != null, "Could not find GE_64(.,.) function");
            this.minus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("MINUS_64"));
            Utils.Assert(this.minus_64 != null, "Could not find MINUS_64(.,.) function");
            this.writable = node.Functions.FirstOrDefault(f => f.Name.Equals("writable"));
            Utils.Assert(this.writable != null, "Could not find writable(.,.) function");
            this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
            Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");

            this._guard_writeTable_ptr = node.Constants.FirstOrDefault(c => c.Name.Equals("_guard_writeTable_ptr"));
            Utils.Assert(this._guard_writeTable_ptr != null, "Could not find _guard_writeTable_ptr constant");
            this._guard_callTable_ptr = node.Constants.FirstOrDefault(c => c.Name.Equals("_guard_callTable_ptr"));
            Utils.Assert(this._guard_callTable_ptr != null, "Could not find _guard_callTable_ptr constant");
            this._bitmap_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_bitmap_low"));
            Utils.Assert(this._bitmap_low != null, "Could not find _bitmap_low constant");
            this._bitmap_high = node.Constants.FirstOrDefault(c => c.Name.Equals("_bitmap_high"));
            Utils.Assert(this._bitmap_high != null, "Could not find _bitmap_high constant");
            this._stack_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_stack_low"));
            Utils.Assert(this._stack_low != null, "Could not find _stack_low constant");
            this._stack_high = node.Constants.FirstOrDefault(c => c.Name.Equals("_stack_high"));
            Utils.Assert(this._stack_high != null, "Could not find _stack_high constant");
            this._virtual_address_space_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_virtual_address_space_low"));
            Utils.Assert(this._virtual_address_space_low != null, "Could not find _virtual_address_space_low constant");
            this._virtual_address_space_high = node.Constants.FirstOrDefault(c => c.Name.Equals("_virtual_address_space_high"));
            Utils.Assert(this._virtual_address_space_high != null, "Could not find _virtual_address_space_high constant");
            this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
            Utils.Assert(this.mem != null, "Could not find mem variable");
            if (Options.splitMemoryModel)
            {
                this.mem_stack = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_stack"));
                Utils.Assert(this.mem_stack != null, "Could not find mem_stack variable");
                this.mem_bitmap = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_bitmap"));
                Utils.Assert(this.mem_bitmap != null, "Could not find mem_bitmap variable");
            }
            else
            {
                this.mem_bitmap = this.mem;
                this.mem_stack = this.mem;
            }
            this.RSP = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RSP"));
            Utils.Assert(this.RSP != null, "Could not find RSP variable");

            this.triggerFn = node.Functions.FirstOrDefault(f => f.Name.Equals("T"));
            if (this.triggerFn == null)
            {
                this.triggerFn = new Function(Token.NoToken,
                                "T",
                                new List<TypeVariable>() { },
                                new List<Variable>() { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]), true) },
                                new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "result", BType.Bool), false),
                                null,
                                new QKeyValue(Token.NoToken, "expand", new List<object>() { Expr.False }, null));
                node.AddTopLevelDeclaration(this.triggerFn);

                BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                Expr axiomExpr = new ForallExpr(Token.NoToken,
                    new List<TypeVariable>(),
                    new List<Variable> { i },
                    new QKeyValue(Token.NoToken, "expand", new List<object>() { Expr.False }, null),
                    new Trigger(Token.NoToken, true, new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(this.triggerFn), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) }) }),
                    Expr.Iff(new NAryExpr(Token.NoToken, new FunctionCall(this.triggerFn), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) }), Expr.True));
                node.AddTopLevelDeclaration(new Axiom(Token.NoToken, axiomExpr));
            }
            Utils.Assert(this.triggerFn != null, "Could not find trigger fn T");

            /*
            //extract axiom on vspace
            foreach (Axiom axiom in node.Axioms)
            {
              if (!(axiom.Expr is NAryExpr)) { continue; }
              if (!((NAryExpr) axiom.Expr).Fun.FunctionName.Equals("==")) { continue; }
              if (!(((NAryExpr) axiom.Expr).Args.ElementAt(0) is IdentifierExpr)) { continue; }
              if ((((NAryExpr) axiom.Expr).Args.ElementAt(0) as IdentifierExpr).Name.Equals("_virtual_address_space_high"))
              {
                Utils.Assert((((NAryExpr)axiom.Expr).Args.ElementAt(1) is LiteralExpr), 
                  "Expected axiom to have a literal second argument");
                Utils.Assert((((NAryExpr)axiom.Expr).Args.ElementAt(1) as LiteralExpr).Type == BType.GetBvType(64), 
                  "Expected axiom to have a literal second argument of size bv64");

                _vspace_high = ((((NAryExpr) axiom.Expr).Args.ElementAt(1) as LiteralExpr).asBvConst).Value.ToInt;
              } 
              else if ((((NAryExpr)axiom.Expr).Args.ElementAt(0) as IdentifierExpr).Name.Equals("_virtual_address_space_low"))
              {
                Utils.Assert((((NAryExpr)axiom.Expr).Args.ElementAt(1) is LiteralExpr),
                  "Expected axiom to have a literal second argument");
                Utils.Assert((((NAryExpr)axiom.Expr).Args.ElementAt(1) as LiteralExpr).Type == BType.GetBvType(64),
                  "Expected axiom to have a literal second argument of size bv64");

                _vspace_low = ((((NAryExpr)axiom.Expr).Args.ElementAt(1) as LiteralExpr).asBvConst).Value.ToInt;
              }
            }

            Utils.Assert(_vspace_high != -1 && _vspace_low != -1, 
              "Expected axioms on _virtual_address_space_high and _virtual_address_space_low");
             * */

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            //<vspace_low, vspace_high, bitmap_low, bitmap_high, stack_low, stack_high, RSP_lowerbound, RSP_upperbound>
            Tuple<Tuple<int, int>, Tuple<int, int>, Tuple<int, int>, Tuple<int, int>> layout = computeMemoryLayout(node);
            StackSizeEstimator estimator = new StackSizeEstimator();
            estimator.Visit(node); //necessary before querying the stack size estimate
            int stack_size_estimate = estimator.getStackEstimate(-1);

            /* Add the the requirements on initial state */
            //requires LOAD_LE_64(mem, _guard_writeTable_ptr) == _bitmap_low
            NAryExpr load_ptr = new NAryExpr(Token.NoToken, new FunctionCall(load_64),
                new List<Expr>() { new IdentifierExpr(Token.NoToken, mem), new IdentifierExpr(Token.NoToken, _guard_writeTable_ptr) });
            Expr linker_invariant = Expr.Eq(load_ptr, new IdentifierExpr(Token.NoToken, _bitmap_low));
            node.Proc.Requires.Add(new Requires(false, linker_invariant));

            //requires (forall i : bv64 :: LT_64(i, RSP) ==> !writable(mem, i)), but instantiated for locations on the current frame
            if (Options.instantiateQuantifiers && stack_size_estimate != -1) //Stack size estimator worked
            {
                //Expr instantiation = Expr.True;
                int addr_offset = 8;
                while (addr_offset <= (stack_size_estimate + 8))
                {
                    Expr addr = new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64),
                      new List<Expr>() { 
                      new IdentifierExpr(Token.NoToken, this.RSP), 
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(addr_offset), 64) });

                    Expr addr_not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                      new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), addr }));
                    node.Proc.Requires.Add(new Requires(false, addr_not_writable));

                    Expr triggered = new NAryExpr(Token.NoToken, new FunctionCall(this.triggerFn), new List<Expr>() { addr });
                    node.Proc.Requires.Add(new Requires(false, triggered));
                    addr_offset += 8;
                }
                //node.Proc.Requires.Add(new Requires(false, instantiation));
            }
            else
            {
                //requires (forall i : bv64 :: LT_64(i, RSP) ==> !writable(mem, i));
                BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                NAryExpr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                  new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new IdentifierExpr(Token.NoToken, RSP) });
                NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack),
                    new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                //Expr aligned = Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, i), 3, 0),
                //                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));
                Expr i_not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                  new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                Expr T_of_i = new NAryExpr(Token.NoToken, new FunctionCall(triggerFn),
                    new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });

                Expr assume_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i },
                  new Trigger(Token.NoToken, true, new List<Expr>() { T_of_i }),
                  Expr.Imp(T_of_i, Expr.Imp(Expr.And(in_stack, in_local_frame), i_not_writable)));
                node.Proc.Requires.Add(new Requires(false, assume_mem_false_expr));

                //this is needed for procedures which dont use any stack space, since they dont incur triggers
                assume_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i },
                  Expr.Imp(Expr.And(in_stack, in_local_frame), i_not_writable));
                node.Proc.Requires.Add(new Requires(false, assume_mem_false_expr));
            }


            //requires RSP >= RSP_lowerbound && RSP < RSP_upperbound //note that these are not the stack bounds
            Expr initial_RSP = Expr.And(Expr.And(
              new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item4.Item1), 64) }),
              new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item4.Item2), 64) })),
              Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP), 3, 0),
                                                       new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3)));
            node.Proc.Requires.Add(new Requires(false, initial_RSP));


            /* Add axioms on memory layout -- these axioms dont sacrifice soundness BTW */
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _virtual_address_space_low),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item1.Item1), 64))));
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _virtual_address_space_high),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item1.Item2), 64))));
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _stack_low),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item3.Item1), 64))));
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _stack_high),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item3.Item2), 64))));
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _bitmap_low),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item2.Item1), 64))));
            this._prog.AddTopLevelDeclaration(new Axiom(Token.NoToken,
              Expr.Eq(new IdentifierExpr(Token.NoToken, _bitmap_high),
                      new LiteralExpr(Token.NoToken, BigNum.FromInt(layout.Item2.Item2), 64))));

            return base.VisitImplementation(node);
        }
    }


    public class ModularVerificationSetup : StandardVisitor
    {
        public override Program VisitProgram(Program node)
        {
            (new ProcedureCallCleaner()).Visit(node);
            (new ProcedureCallModeler()).Visit(node);
            return base.VisitProgram(node);
        }
    }

    public class ProcedureCallCleaner : StandardVisitor
    {
        private bool isCallInstruction = false;
        private bool isRetInstruction = false;

        public override Block VisitBlock(Block node)
        {
            Func<Cmd, bool> isCallCmd = delegate(Cmd c)
            {
                if (c is AssertCmd) //call and return instructions are marked with attributes
                {
                    AssertCmd ac = c as AssertCmd;
                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    string attribute_identifier = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCallTarget");
                    if (attribute_cmdtype != null && attribute_identifier != null && attribute_cmdtype.Equals("call")) { return true; }
                }
                return false;
            };

            Func<Cmd, bool> isRetCmd = delegate(Cmd c)
            {
                if (c is AssertCmd) //call and return instructions are marked with attributes
                {
                    AssertCmd ac = c as AssertCmd;
                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    if (attribute_cmdtype != null && attribute_cmdtype.Equals("ret")) { return true; }
                }
                return false;
            };

            Func<Cmd, bool> isRemoteIndirectJmp = delegate(Cmd c)
            {
                if (c is AssertCmd)
                {
                    AssertCmd ac = c as AssertCmd;
                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    string attribute_jmptarget = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpTarget");
                    if (attribute_cmdtype != null && attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget != null && attribute_jmptarget.Equals("remote")) { return true; }
                }
                return false;
            };

            this.isCallInstruction = node.Cmds.Any(c => isCallCmd(c)); //do the statements in this block model an x64 call?
            this.isRetInstruction = node.Cmds.Any(c => isRetCmd(c));   //do the statements in this block model an x64 ret?

            //jumps outsde the procedure dont come back. Model them as returns
            if (node.Cmds.Any(c => isRemoteIndirectJmp(c)))
            {
                node.TransferCmd = new ReturnCmd(Token.NoToken);
            }
            return base.VisitBlock(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();

            foreach (Cmd c in cmdSeq)
            {
                bool skipStatement = false;
                if (c is AssignCmd)
                {
                    bool assignmentToMem = (c as AssignCmd).Lhss.Any(lhs => lhs.DeepAssignedIdentifier.Name.Contains("mem")); //catches mem, mem_stack, mem_bitmap
                    bool assignmentToRSP = (c as AssignCmd).Lhss.Any(lhs => lhs.DeepAssignedIdentifier.Name.Equals("RSP"));
                    //Calls and Returns do not use their x64 modeling. We omit inc/dec of RSP and load/store of return address.
                    skipStatement = this.isRetInstruction || (this.isCallInstruction && (assignmentToMem || assignmentToRSP));
                }

                if (!skipStatement) { newCmdSeq.Add(c); }
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }

    public class ProcedureCallModeler : StandardVisitor
    {
        private Function rep_stosb;
        private Function not_1;
        private Function ge_64;
        private Function lt_64;
        private Function plus_64;
        private Function minus_64;
        private Function load_64;
        private Function addrInBitmap;
        private Function addrInStack;
        private Function policy;
        private Function writable;
        private Function addrToBitmapAddrByte;

        private GlobalVariable mem;
        private GlobalVariable mem_stack;
        private GlobalVariable mem_bitmap;
        private GlobalVariable RSP;
        private GlobalVariable RAX;
        private GlobalVariable RDI;
        private GlobalVariable RDX;
        private GlobalVariable R8;
        private GlobalVariable R9;
        private GlobalVariable R10;
        private GlobalVariable R11;
        private GlobalVariable RCX;
        private GlobalVariable CF;

        private Constant _bitmap_low;
        private Constant _bitmap_high;
        private Constant _stack_low;
        private Constant _stack_high;
        private Constant _guard_writeTable_ptr;

        private bool isFunctionNew = false;
        private bool isFunctionGuardCheckIcallCfw = false;

        private int mem_var_count = 0;
        private Program prog;
        private Implementation impl;
        private bool bound_stacksize_option = false;
        private int bound_stacksize_offset = -1;

        public override Program VisitProgram(Program node)
        {
            this.prog = node;

            this.addrToBitmapAddrByte = node.Functions.FirstOrDefault(f => f.Name.Equals("addrToBitmapAddrByte"));
            Utils.Assert(this.addrToBitmapAddrByte != null, "Could not find addrToBitmapAddrByte(.) function");
            this.load_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LOAD_LE_64"));
            Utils.Assert(this.load_64 != null, "Could not find LOAD_LE_64(.,.) function");
            this.ge_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GE_64"));
            Utils.Assert(this.ge_64 != null, "Could not find GE_64(.,.) function");
            this.lt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LT_64"));
            Utils.Assert(this.lt_64 != null, "Could not find LT_64(.,.) function");
            this.plus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("PLUS_64"));
            Utils.Assert(this.plus_64 != null, "Could not find PLUS_64(.,.) function");
            this.minus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("MINUS_64"));
            Utils.Assert(this.minus_64 != null, "Could not find MINUS_64(.,.) function");
            this.not_1 = node.Functions.FirstOrDefault(f => f.Name.Equals("NOT_1"));
            Utils.Assert(this.not_1 != null, "Could not find NOT_1(.,.) function");
            this.rep_stosb = node.Functions.FirstOrDefault(f => f.Name.Equals("REP_STOSB"));
            Utils.Assert(this.rep_stosb != null, "Could not find REP_STOSB(.,.,.) function");
            this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
            Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
            this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
            Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");
            this.policy = node.Functions.FirstOrDefault(f => f.Name.Equals("policy"));
            Utils.Assert(this.policy != null, "Could not find policy(.,.,.) function");
            this.writable = node.Functions.FirstOrDefault(f => f.Name.Equals("writable"));
            Utils.Assert(this.writable != null, "Could not find writable(.,.) function");

            this._bitmap_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_bitmap_low"));
            Utils.Assert(this._bitmap_low != null, "Could not find _bitmap_low constant");
            this._bitmap_high = node.Constants.FirstOrDefault(c => c.Name.Equals("_bitmap_high"));
            Utils.Assert(this._bitmap_high != null, "Could not find _bitmap_high constant");
            this._stack_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_stack_low"));
            Utils.Assert(this._stack_low != null, "Could not find _stack_low constant");
            this._stack_high = node.Constants.FirstOrDefault(c => c.Name.Equals("_stack_high"));
            this._guard_writeTable_ptr = node.Constants.FirstOrDefault(c => c.Name.Equals("_guard_writeTable_ptr"));
            Utils.Assert(this._guard_writeTable_ptr != null, "Could not find _guard_writeTable_ptr constant");

            this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
            Utils.Assert(this.mem != null, "Could not find mem variable");
            if (Options.splitMemoryModel)
            {

                this.mem_stack = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_stack"));
                Utils.Assert(this.mem_stack != null, "Could not find mem_stack variable");
                this.mem_bitmap = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_bitmap"));
                Utils.Assert(this.mem_bitmap != null, "Could not find mem_bitmap variable");
            }
            else
            {
                this.mem_stack = this.mem;
                this.mem_bitmap = this.mem;
            }
            this.RSP = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RSP"));
            Utils.Assert(this.RSP != null, "Could not find RSP variable");
            this.RAX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RAX"));
            Utils.Assert(this.RAX != null, "Could not find RAX variable");
            this.RDI = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDI"));
            Utils.Assert(this.RDI != null, "Could not find RDI variable");
            this.RDX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDX"));
            Utils.Assert(this.RDX != null, "Could not find RDX variable");
            this.R8 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R8"));
            Utils.Assert(this.R8 != null, "Could not find R8 variable");
            this.R9 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R9"));
            Utils.Assert(this.R9 != null, "Could not find R9 variable");
            this.R10 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R10"));
            Utils.Assert(this.R10 != null, "Could not find R10 variable");
            this.R11 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R11"));
            Utils.Assert(this.R11 != null, "Could not find R11 variable");
            this.RCX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RCX"));
            Utils.Assert(this.RCX != null, "Could not find RCX variable");
            this.CF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("CF"));
            Utils.Assert(this.CF != null, "Could not find CF variable");

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            this.impl = node;
            StackSizeEstimator estimator = new StackSizeEstimator();
            estimator.Visit(node); //necessary before querying the stack size estimate
            int stack_size_estimate = estimator.getStackEstimate(-1);
            if (stack_size_estimate > 0)
            {
                this.bound_stacksize_option = true;
                this.bound_stacksize_offset = stack_size_estimate;
            }
            return base.VisitImplementation(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();

            foreach (Cmd c in cmdSeq)
            {
                newCmdSeq.Add(c);

                if (c is AssertCmd) //need to identify special functions
                {
                    AssertCmd ac = c as AssertCmd;

                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    if (attribute_cmdtype != null && attribute_cmdtype.Equals("call"))
                    {
                        string attribute_identifier = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCallTarget");
                        this.isFunctionNew = attribute_identifier != null ?
                            attribute_identifier.Equals("0x" + Options.funcNew) :
                            false;
                        this.isFunctionGuardCheckIcallCfw = attribute_identifier != null ?
                            attribute_identifier.Equals("0x" + Options.funcGuardCheckIcallCfw) :
                            false;
                    }
                }
                else if (c is CallCmd)
                {
                    if (this.isFunctionNew) //we evaluate this predicate when the corresponding assert shows up (i.e. assert {..} true; call arbitraryfunc(); )
                    {
                        //havoc RAX
                        newCmdSeq.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>() { new IdentifierExpr(Token.NoToken, RAX) }));

                        Expr _heap_high = new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64),
                            new List<Expr> { new IdentifierExpr(Token.NoToken, this._bitmap_low), 
                                                 new LiteralExpr(Token.NoToken, BigNum.FromInt(64), 64) });

                        Expr _heap_low = new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64),
                            new List<Expr> { new IdentifierExpr(Token.NoToken, this._stack_high), 
                                                 new LiteralExpr(Token.NoToken, BigNum.FromInt(64), 64) });

                        //assume RAX is a value within heap
                        Expr rax_plus_rcx_minus_1 = new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64),
                                                      new List<Expr>() { new IdentifierExpr(Token.NoToken, this.RAX), 
                                                                   new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64), 
                                                                       new List<Expr> () { new IdentifierExpr(Token.NoToken, this.RCX), 
                                                                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 64) }) });
                        Expr rax_plus_rcx_minus_1_lower_than_bitmap_low = new NAryExpr(Token.NoToken, new FunctionCall(this.lt_64),
                            new List<Expr>() { rax_plus_rcx_minus_1, _heap_high });
                        Expr rax_plus_rcx_minus_1_higher_than_stack_high = new NAryExpr(Token.NoToken, new FunctionCall(this.ge_64),
                            new List<Expr>() { rax_plus_rcx_minus_1, _heap_low });
                        Expr rax_lower_than_bitmap_low = new NAryExpr(Token.NoToken, new FunctionCall(this.lt_64),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, this.RAX), _heap_high });
                        Expr rax_higher_than_stack_high = new NAryExpr(Token.NoToken, new FunctionCall(this.ge_64),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, this.RAX), _heap_low });

                        // we assume that the heap is between the top of stack and bottom of bitmap
                        Expr range_check = Expr.And(Expr.And(rax_plus_rcx_minus_1_lower_than_bitmap_low, rax_plus_rcx_minus_1_higher_than_stack_high),
                                                    Expr.And(rax_lower_than_bitmap_low, rax_higher_than_stack_high));

                        //Expr aligned = Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RAX), 3, 0),
                        //                                     new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));

                        //we know this will not be in stack or bitmap
                        BoundVariable i = new BoundVariable(Token.NoToken,
                            new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                        Expr mem_of_i_writable = new NAryExpr(Token.NoToken, new FunctionCall(this.writable),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), new IdentifierExpr(Token.NoToken, i) });
                        Expr malloced_region = Expr.And(
                            new NAryExpr(Token.NoToken, new FunctionCall(this.ge_64),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new IdentifierExpr(Token.NoToken, this.RAX) }),
                            new NAryExpr(Token.NoToken, new FunctionCall(this.lt_64),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, i), 
                                                       new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64), new List<Expr>() { 
                                                            new IdentifierExpr(Token.NoToken, this.RAX), 
                                                            new IdentifierExpr(Token.NoToken, this.RCX) }) }));
                        Expr rcx_bytes_made_writable = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(malloced_region, mem_of_i_writable));

                        //malloc makes the returned region writable
                        newCmdSeq.Add(new AssumeCmd(Token.NoToken, Expr.And(rcx_bytes_made_writable, range_check)));

                        //calling convention requires havocing of RAX,RCX,RDX,R8,R9,R10,R11
                        //newCmdSeq.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>() { new IdentifierExpr(Token.NoToken, this.RCX),
                        //                                                                       new IdentifierExpr(Token.NoToken, this.RDX), 
                        //                                                                       new IdentifierExpr(Token.NoToken, this.R8), 
                        //                                                                       new IdentifierExpr(Token.NoToken, this.R9), 
                        //                                                                       new IdentifierExpr(Token.NoToken, this.R10), 
                        //                                                                       new IdentifierExpr(Token.NoToken, this.R11) }));

                        this.isFunctionNew = false; //reset the flag
                    }
                    else if (this.isFunctionGuardCheckIcallCfw) //we evaluate this predicate when the corresponding assert shows up (i.e. assert {..} true; call arbitraryfunc(); )
                    {
                        //Note that calling this function doesn't call the intended procedure (whose addr is in RCX)
                        //_guard_check_icallcfw just checks policy for the address in RCX, and invokes int 3 if policy is violated
                        //So no havoc is needed

                        Expr rcx_satisfies_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                          new List<Expr>() { new IdentifierExpr(Token.NoToken, RCX) });
                        newCmdSeq.Add(new AssumeCmd(Token.NoToken, rcx_satisfies_policy));

                        this.isFunctionGuardCheckIcallCfw = false; //reset the flag
                    }
                    else
                    {
                        //call to a normal procedure

                        //we need to havoc memory, so lets add a fresh variable
                        GlobalVariable new_mem = Utils.MkGlobalVar("fresh_" + this.mem_var_count.ToString(), this.mem.TypedIdent.Type);
                        this.prog.AddTopLevelDeclaration(new_mem); //add as global variable

                        //we need to trigger the quantifier, so introduce the necessary T_fresh_n function
                        Function T_fresh_n = new Function(Token.NoToken,
                            "T_fresh_" + this.mem_var_count.ToString(),
                            new List<TypeVariable>() { },
                            new List<Variable>() { new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]), true) },
                            new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "result", BType.Bool), false),
                            null,
                            new QKeyValue(Token.NoToken, "expand", new List<object>() { Expr.False }, null));
                        this.prog.AddTopLevelDeclaration(T_fresh_n);

                        BoundVariable i = new BoundVariable(Token.NoToken,
                            new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                        Expr axiomExpr = new ForallExpr(Token.NoToken,
                            new List<TypeVariable>(),
                            new List<Variable> { i },
                            new QKeyValue(Token.NoToken, "expand", new List<object>() { Expr.False }, null),
                            new Trigger(Token.NoToken, true, new List<Expr> { new NAryExpr(Token.NoToken, new FunctionCall(T_fresh_n), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) }) }),
                            Expr.Iff(new NAryExpr(Token.NoToken, new FunctionCall(T_fresh_n), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) }), Expr.True));
                        this.prog.AddTopLevelDeclaration(new Axiom(Token.NoToken, axiomExpr));

                        this.mem_var_count += 1; //this will force the fresh_x variables to be fresh,symbolic constants

                        //Assume T_fresh_n(i) for each i in the stack
                        if (this.bound_stacksize_option && Options.instantiateQuantifiers) //Stack size estimator worked
                        {
                            Expr instantiation = Expr.True;
                            int addr_offset = 8;
                            while (addr_offset <= this.bound_stacksize_offset)
                            {
                                Expr addr = new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64),
                                  new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RSP)), new LiteralExpr(Token.NoToken, BigNum.FromInt(addr_offset), 64) });
                                instantiation = Expr.And(instantiation, new NAryExpr(Token.NoToken, new FunctionCall(T_fresh_n), new List<Expr>() { addr }));
                                addr_offset += 8;
                            }
                            //assume T_fresh_n(old(rsp - 8) /\ T_fresh_n(rsp - 16) /\ ...
                            newCmdSeq.Add(new AssumeCmd(Token.NoToken, instantiation));
                        }


                        //collect some useful expressions for use later
                        Expr addrToBitmapAddrByte_of_i = new NAryExpr(Token.NoToken, new FunctionCall(this.addrToBitmapAddrByte),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                        Expr i_in_stack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                        Expr mem_of_i_writable = new NAryExpr(Token.NoToken, new FunctionCall(this.writable),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), new IdentifierExpr(Token.NoToken, i) });
                        Expr T_fresh_of_i = new NAryExpr(Token.NoToken, new FunctionCall(T_fresh_n),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });


                        //preserve non-writable stack: ∀i. addrInStack(i) /\ i < old(RSP) /\ !writable(mem, i) ==> ld_64(mem_stack,i) == ld_64(fresh,i)

                        Expr preserved_addr =
                          Expr.And(Expr.And(
                                      i_in_stack,
                                      new NAryExpr(Token.NoToken, new FunctionCall(this.lt_64), new List<Expr>() 
                                    { new IdentifierExpr(Token.NoToken, i), 
                                      new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RSP)) })),
                                      Expr.Not(mem_of_i_writable));
                        //Expr preserved_addr = Expr.Not(mem_of_i_writable); //FIXME: maybe use this for performance
                        Expr preserved_val = Expr.Eq(new NAryExpr(Token.NoToken, new FunctionCall(this.load_64),
                                                      new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_stack),
                                                                   new IdentifierExpr(Token.NoToken, i)}),
                                                     new NAryExpr(Token.NoToken, new FunctionCall(this.load_64),
                                                      new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem),
                                                                   new IdentifierExpr(Token.NoToken, i)}));
                        Expr preserved = new ForallExpr(Token.NoToken,
                            new List<Variable>() { i },  //quantified variable
                            new Trigger(Token.NoToken, true, new List<Expr>() { T_fresh_of_i }), //trigger for instantiation
                            Expr.Imp(T_fresh_of_i, Expr.Imp(preserved_addr, preserved_val))); //quantifier-free formula
                        newCmdSeq.Add(new AssumeCmd(Token.NoToken, preserved));


                        //preserve bitmap: ∀i. addrInStack(i) ==> mem_bitmap[addrToBitmapAddrByte(i)] == fresh[addrToBitmapAddrByte(i)]
                        preserved_addr = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                        preserved_val = Expr.Eq(
                            new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), addrToBitmapAddrByte_of_i }),
                            new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem), addrToBitmapAddrByte_of_i }));
                        preserved = new ForallExpr(Token.NoToken,
                            new List<Variable>() { i },  //quantified variable
                            new Trigger(Token.NoToken, true, new List<Expr>() { T_fresh_of_i }), //trigger for instantiation
                            Expr.Imp(T_fresh_of_i, Expr.Imp(preserved_addr, preserved_val))); //quantifier-free formula
                        //FIXME: remove for performance
                        newCmdSeq.Add(new AssumeCmd(Token.NoToken, preserved));

                        //preserve stack backing space
                        for (int offset = 8; offset < 40; offset += 8)
                        {
                            //old(rsp) - {8,16,24,32}
                            Expr offset_expr = new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64),
                                new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RSP)),
                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(offset), 64) });
                            Expr preserved_val_at_offset = Expr.Eq(new NAryExpr(Token.NoToken, new FunctionCall(this.load_64),
                                                        new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem), offset_expr }),
                                                                   new NAryExpr(Token.NoToken, new FunctionCall(this.load_64),
                                                        new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem), offset_expr }));
                            //newCmdSeq.Add(new AssumeCmd(Token.NoToken, preserved_val_at_offset)); //doubt we need this
                        }


                        //base of bitmap is preserved
                        NAryExpr load_ptr = new NAryExpr(Token.NoToken, new FunctionCall(load_64),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem), new IdentifierExpr(Token.NoToken, _guard_writeTable_ptr) });
                        Expr linker_invariant = Expr.Eq(load_ptr, new IdentifierExpr(Token.NoToken, _bitmap_low));
                        newCmdSeq.Add(new AssumeCmd(Token.NoToken, linker_invariant));

                        if (Options.splitMemoryModel)
                        {
                            //mem_stack := new_mem;
                            newCmdSeq.Add(new AssignCmd(Token.NoToken,
                                new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem) }));
                            //FIXME: remove for performance
                            newCmdSeq.Add(new AssignCmd(Token.NoToken,
                                  new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                  new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem) }));
                        }

                        //mem := fresh;
                        newCmdSeq.Add(new AssignCmd(Token.NoToken,
                          new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem)) },
                          new List<Expr>() { new IdentifierExpr(Token.NoToken, new_mem) }));


                        //calling convention requires havocing of RAX,RCX,RDX,R8,R9,R10,R11
                        newCmdSeq.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>() { new IdentifierExpr(Token.NoToken, this.RAX),
                                                                                         new IdentifierExpr(Token.NoToken, this.RCX), 
                                                                                         new IdentifierExpr(Token.NoToken, this.RDX), 
                                                                                         new IdentifierExpr(Token.NoToken, this.R8), 
                                                                                         new IdentifierExpr(Token.NoToken, this.R9), 
                                                                                         new IdentifierExpr(Token.NoToken, this.R10), 
                                                                                         new IdentifierExpr(Token.NoToken, this.R11) }));
                    }
                }
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
