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
    public class LoadAddressDecider : StandardVisitor
    {
        private Function addrInBitmap;
        private Function addrInStack;
        private GlobalVariable mem;

        private string current_label;

        public override Program VisitProgram(Program node)
        {
            this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
            this.addrInStack = Utils.FindFunctionInProgram(node, "addrInStack");

            this.mem = Utils.FindGlobalVariableInProgram(node, "mem");

            return base.VisitProgram(node);
        }

        public override Block VisitBlock(Block node)
        {
            //Console.WriteLine("Visiting block with label {0}", node.Label);
            this.current_label = node.Label;
            return base.VisitBlock(node);
        }

        public List<Expr> getNestedLoadAddresses(Expr e)
        {
            //if there is no load, no point in recursing
            if (!(Utils.getNestedFunctions(e).Any(x => x.FunctionName.Contains("LOAD_LE")))) { return new List<Expr>(); }

            //we have one or more load expressions here. so let's recursively find them and substitute.
            if (e is NAryExpr)
            {
                //this is a load expression
                if ((e as NAryExpr).Fun.FunctionName.Contains("LOAD_LE"))
                {
                    Tuple<Expr, Expr> load_args = Utils.getLoadArgs(e);
                    List<Expr> exprs = new List<Expr>() { load_args.Item2 };
                    exprs.AddRange(getNestedLoadAddresses(load_args.Item2));
                    return exprs;
                }
                else
                {
                    //not a load expression, but we need to recurse
                    List<Expr> exprs = new List<Expr>();
                    foreach (Expr arg in (e as NAryExpr).Args)
                    {
                        exprs.AddRange(getNestedLoadAddresses(arg));
                    }
                    return exprs;
                }
            }
            else if (e is BvExtractExpr)
            {
                return getNestedLoadAddresses((e as BvExtractExpr).Bitvector);
            }
            else if (e is BvConcatExpr)
            {
                List<Expr> exprs = new List<Expr>();
                exprs.AddRange(getNestedLoadAddresses((e as BvConcatExpr).E0));
                exprs.AddRange(getNestedLoadAddresses((e as BvConcatExpr).E1));
                return exprs;
            }
            else if (e is IdentifierExpr) { return new List<Expr>(); }
            else if (e is LiteralExpr) { return new List<Expr>(); }
            else { Utils.Assert(false, "Should not get here"); return null; }
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                    List<Expr> loadAddresses = getNestedLoadAddresses(ac.Rhss[0]);
                    Utils.Assert(loadAddresses.Select(x => x.ToString()).Distinct().Count() < 2,
                        "Found multiple load expressions in " + ac.Rhss[0].ToString());
                    Expr load_addr = loadAddresses.Any() ? loadAddresses[0] : null;

                    if (load_addr != null)
                    {
                        Action<NAryExpr, string> RecordAssertion = delegate(NAryExpr assertCondition, string attribute)
                        {
                            AssertCmd assertion = new AssertCmd(Token.NoToken, assertCondition);
                            assertion.Attributes = new QKeyValue(Token.NoToken, "region", new List<object> {attribute}, assertion.Attributes);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));
                        };

                        NAryExpr condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { load_addr });
                        RecordAssertion(condition, "addrInBitmap");

                        condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { load_addr });
                        RecordAssertion(condition, "addrInStack");

                        condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { load_addr });
                        condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                        RecordAssertion(condition, "!addrInBitmap");

                        condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { load_addr });
                        condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                        RecordAssertion(condition, "!addrInStack");
                    }
                }

                //The assert gets placed prior to the original command
                newCmdSeq.Add(c);
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }

    public class StoreAddressDecider : StandardVisitor
    {
        private Function addrInBitmap;
        private Function addrInStack;
        private Function lt_64, ge_64;
        private GlobalVariable mem;

        private Constant stack_low;
        private Constant stack_high;
        private Constant bitmap_low;
        private Constant bitmap_high;

        private bool splitProgram;

        private string current_label;

        public override Program VisitProgram(Program node)
        {
            this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
            this.addrInStack = Utils.FindFunctionInProgram(node, "addrInStack");
            this.lt_64 = Utils.FindFunctionInProgram(node, "LT_64");
            this.ge_64 = Utils.FindFunctionInProgram(node, "GE_64");

            this.stack_low = Utils.FindConstantInProgram(node, "_stack_low");
            this.stack_high = Utils.FindConstantInProgram(node, "_stack_high");
            this.bitmap_low = Utils.FindConstantInProgram(node, "_bitmap_low");
            this.bitmap_high = Utils.FindConstantInProgram(node, "_bitmap_high");

            this.mem = Utils.FindGlobalVariableInProgram(node, "mem");

            if (node.GlobalVariables.FirstOrDefault(i => i.Name.Equals("mem_stack")) != null
                  && node.GlobalVariables.FirstOrDefault(i => i.Name.Equals("mem_bitmap")) != null)
                this.splitProgram = true;

            return base.VisitProgram(node);
        }

        public override Block VisitBlock(Block node)
        {
            //Console.WriteLine("Visiting block with label {0}", node.Label);
            this.current_label = node.Label;
            return base.VisitBlock(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();

            Action<NAryExpr, string, AssignCmd> RecordAssertion = delegate(NAryExpr assertCondition, string attribute, AssignCmd memAssignCmd)
            {
                AssertCmd assertion = new AssertCmd(Token.NoToken, assertCondition);
                //we use the attribute in a separate pass within the split memory modeler
                assertion.Attributes = new QKeyValue(Token.NoToken, "region", new List<object> { attribute }, assertion.Attributes);
                newCmdSeq.Add(assertion);
                //current_label is the current block, ac is the STORE associated with the assertiion
                VCSplitter.Instance.RecordAssertion(this.current_label, memAssignCmd, assertion, Utils.getSlashVerifyCmdType(memAssignCmd));
            };

            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                    //Console.Write(".");
                    switch (Utils.getSlashVerifyCmdType(ac))
                    {
                        case SlashVerifyCmdType.Store8:
                        case SlashVerifyCmdType.Store16:
                        case SlashVerifyCmdType.Store32:
                        case SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                            {
                                Tuple<Variable, Expr, Expr> storeArgs = Utils.getStoreArgs(ac);
                                Expr store_addr = storeArgs.Item2;
                                Expr store_value = storeArgs.Item3;

                                if (splitProgram) {
                                    newCmdSeq.Add(c);
                                    break;
                                }


                                NAryExpr condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { store_addr });
                                RecordAssertion(condition, "addrInBitmap", ac);

                                condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { store_addr });
                                RecordAssertion(condition, "addrInStack", ac);

                                condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { store_addr });
                                condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                                RecordAssertion(condition, "!addrInBitmap", ac);

                                condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { store_addr });
                                condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                                RecordAssertion(condition, "!addrInStack", ac);

                                //Expr addr_in_mem =
                                //    Expr.And(
                                //        new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                //            new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                //        new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                //            new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.bitmap_low) }));
                                //RecordAssertion(addr_in_mem, "!addrInStack");

                                break;
                            }

                        case SlashVerifyCmdType.RepStosB: //x := REP_STOSB(mem, e1, e2, e3)
                            {
                                break;
                            }

                        default: //x:=e
                            {
                                if (ac.Lhss.First().DeepAssignedVariable.Name.Equals("mem_stack")) {
                                    Expr address = Utils.getSplitMemoryOperationAddress(ac);
                                    NAryExpr condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { address });
                                    RecordAssertion(condition, "addrInStack", ac);

                                    condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr> { address });
                                    condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                                    RecordAssertion(condition, "!addrInStack", ac);
                                }
                                else if (ac.Lhss.First().DeepAssignedVariable.Name.Equals("mem_bitmap")) {
                                    Expr address = Utils.getSplitMemoryOperationAddress(ac);
                                    NAryExpr condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { address });
                                    RecordAssertion(condition, "addrInBitmap", ac);

                                    condition = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr> { address });
                                    condition = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> {condition});
                                    RecordAssertion(condition, "!addrInBitmap", ac);
                                }
                                break;
                            }
                    }

          // TODO handle ITE case
                }

                //The assert gets placed prior to the original command
                newCmdSeq.Add(c);
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }

    public class SplitMemoryModeler : StandardVisitor
    {
        private GlobalVariable mem, mem_stack, mem_bitmap;
        private Function addrInBitmap, addrInStack;
        private string current_label;
        private Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB;
        private Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB;
        private bool splitProgram;

        enum AddrType { Unknown, StackAddress, BitmapAddress, MemAddress };

        public SplitMemoryModeler(
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB,
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB,
            bool splitProgram)
        {
            this.storeAddressRegionDB = storeAddressRegionDB;
            this.loadAddressRegionDB = loadAddressRegionDB;
            this.splitProgram = splitProgram;
        }

        public override Program VisitProgram(Program node)
        {
            if (!Options.splitMemoryModel) { return base.VisitProgram(node); }

            this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
            this.addrInStack = Utils.FindFunctionInProgram(node, "addrInStack");
            this.mem = Utils.FindGlobalVariableInProgram(node, "mem");

            if (!this.splitProgram)
            {
              this.mem_stack = Utils.MkGlobalVar("mem_stack", this.mem.TypedIdent.Type);
              node.AddTopLevelDeclaration(this.mem_stack); //add as global variable
              this.mem_bitmap = Utils.MkGlobalVar("mem_bitmap", this.mem.TypedIdent.Type);
              node.AddTopLevelDeclaration(this.mem_bitmap); //add as global variable
            }
            else
            {
              this.mem_stack = Utils.FindGlobalVariableInProgram(node, "mem_stack");
              this.mem_bitmap = Utils.FindGlobalVariableInProgram(node, "mem_bitmap");
            }

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            if (!Options.splitMemoryModel) { return base.VisitImplementation(node); }
            if (this.splitProgram)         { return base.VisitImplementation(node); }

            node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_bitmap));
            node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_stack));
            return base.VisitImplementation(node);
        }

        //public static bool isStackAddressSyntactically(Expr addr)
        //{
        //    return getSubExpressions(addr).Any(x => x.Name.Equals("RSP")); //FIXME: clearly unsound, but lets roll with it
        //}

        /* argument label refers to the block label where the assertion lives */
        private bool isRegionAddress(string label, Cmd c, string region_id, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            foreach (Tuple<string, Cmd, AssertCmd> t in db.Keys)
            {
                if (!t.Item1.Equals(label)) { continue; }
                if (!t.Item2.ToString().Equals(c.ToString())) { continue; }
                if (!(QKeyValue.FindStringAttribute(t.Item3.Attributes, "region") == region_id)) { continue; }
                //if (!Utils.getNestedFunctions(t.Item3.Expr).Any(x => x.FunctionName.Equals(region_id))) { continue; }
                return db[t];
            }
            return false;
        }

        private bool isStackAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "addrInStack", db);
        }

        private bool isNotStackAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "!addrInStack", db);
        }

        private bool isBitmapAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "addrInBitmap", db);
        }

        private bool isNotBitmapAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "!addrInBitmap", db);
        }

        //private bool isMemAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        //{
        //    return isRegionAddress(label, c, "GE_64", db);
        //}

        //takes an expression and substitutes desired mem for each load(mem,..) sub-expression
        private Expr splitMemoryOnAllLoads(Expr e, AddrType addrType, bool notBitmap, bool notStack)
        {
            //takes as input the addr expr of LOAD(mem,addr), and returns the desired expression for mem : ITE(addrInBitmap(.), mem_bitmap, ITE(..))
            Func<Expr, Expr> getDesiredMemExpr = delegate(Expr addr)
            {
                if (addrType == AddrType.StackAddress)
                {
                    return new IdentifierExpr(Token.NoToken, this.mem_stack);
                }
                else if (addrType == AddrType.BitmapAddress)
                {
                    return new IdentifierExpr(Token.NoToken, this.mem_bitmap);
                }
                else
                {
                    Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr> { addr });
                    Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr> { addr });

                    Expr tmp = new IdentifierExpr(Token.NoToken, mem);
                    if (!notBitmap) //may target the bitmap
                    {
                        tmp = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                            isAddrInBitmap, new IdentifierExpr(Token.NoToken, this.mem_bitmap), tmp});
                    }

                    if (!notStack) //may target the stack
                    {
                        tmp = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                            isAddrInStack, new IdentifierExpr(Token.NoToken, this.mem_stack), tmp});
                    }
                    return tmp;
                }
            };

            //if there is no load, no point in recursing
            if (!(Utils.getNestedFunctions(e).Any(x => x.FunctionName.Contains("LOAD_LE")))) { return e; }

            //we have one or more load expressions here. so let's recursively find them and substitute.
            if (e is NAryExpr)
            {
                //this is a load expression
                if ((e as NAryExpr).Fun.FunctionName.Contains("LOAD_LE"))
                {
                    Tuple<Expr, Expr> load_args = Utils.getLoadArgs(e);
                    Expr desired_mem = getDesiredMemExpr(load_args.Item2);
                    //even the address expression can have a load
                    return new NAryExpr(Token.NoToken, (e as NAryExpr).Fun, new List<Expr>() { desired_mem, splitMemoryOnAllLoads(load_args.Item2, addrType, notBitmap, notStack) });
                }
                else
                {
                    //not a load expression, but we need to recurse
                    List<Expr> new_args = new List<Expr>();
                    foreach (Expr arg in (e as NAryExpr).Args)
                    {
                        new_args.Add(splitMemoryOnAllLoads(arg, addrType, notBitmap, notStack));
                    }
                    return new NAryExpr(Token.NoToken, (e as NAryExpr).Fun, new_args);
                }
            }
            else if (e is BvExtractExpr)
            {
                return new BvExtractExpr(Token.NoToken,
                    splitMemoryOnAllLoads((e as BvExtractExpr).Bitvector, addrType, notBitmap, notStack),
                    (e as BvExtractExpr).End,
                    (e as BvExtractExpr).Start);
            }
            else if (e is BvConcatExpr)
            {
                return new BvConcatExpr(Token.NoToken,
                    splitMemoryOnAllLoads((e as BvConcatExpr).E0, addrType, notBitmap, notStack),
                    splitMemoryOnAllLoads((e as BvConcatExpr).E1, addrType, notBitmap, notStack));
            }
            else if (e is IdentifierExpr)
            {
                return e; //cant
            }
            else if (e is LiteralExpr)
            {
                return e;
            }
            else
            {
                Utils.Assert(false, "Should not get here");
                return null;
            }
        }

        private Expr transformLoad(string label, Cmd c, Expr toTransform)
        {
            AddrType addrType = AddrType.Unknown;
            if (Options.optimizeLoadITE)
            {
                addrType = (isStackAddress(this.current_label, c, this.loadAddressRegionDB)) ? AddrType.StackAddress :
                    ((isBitmapAddress(this.current_label, c, this.loadAddressRegionDB)) ? AddrType.BitmapAddress : AddrType.Unknown);
            }

            return splitMemoryOnAllLoads(toTransform, addrType,
                isNotBitmapAddress(this.current_label, c, this.loadAddressRegionDB),
                isNotStackAddress(this.current_label, c, this.loadAddressRegionDB));
        }

        public override Block VisitBlock(Block node)
        {
            this.current_label = node.Label;
            return base.VisitBlock(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            if (!Options.splitMemoryModel) { return base.VisitCmdSeq(cmdSeq); }

            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                    ac = new AssignCmd(Token.NoToken, new List<AssignLhs> { ac.Lhss[0] }, new List<Expr> { transformLoad(this.current_label, c, ac.Rhss[0]) });

                    switch (Utils.getSlashVerifyCmdType(ac))
                    {
                        case SlashVerifyCmdType.Store8:
                        case SlashVerifyCmdType.Store16:
                        case SlashVerifyCmdType.Store32:
                        case SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                            {
                                Tuple<Variable, Expr, Expr> storeArgs = Utils.getStoreArgs(ac);
                                Expr store_addr = storeArgs.Item2;
                                Expr store_value = storeArgs.Item3;

                                AddrType addrType = AddrType.Unknown;
                                if (Options.optimizeStoreITE)
                                {
                                    if (isStackAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.StackAddress; }
                                    else if (isBitmapAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.BitmapAddress; }
                                    //else if (isMemAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.MemAddress; }
                                    else { addrType = AddrType.Unknown; }
                                }

                                if (addrType == AddrType.StackAddress)
                                {
                                    //adds mem_stack := STORE(mem_stack, addr, value);
                                    AssignCmd new_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                        new List<Expr> { new NAryExpr(Token.NoToken,
                                                                            (ac.Rhss[0] as NAryExpr).Fun,
                                                                            new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_stack),
                                                                                               store_addr,
                                                                                               store_value }) });
                                    newCmdSeq.Add(new_ac);
                                }
                                else if (addrType == AddrType.BitmapAddress)
                                {
                                    //adds mem_bitmap := STORE(mem_bitmap, addr, value);
                                    AssignCmd new_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                        new List<Expr> { new NAryExpr(Token.NoToken,
                                                                            (ac.Rhss[0] as NAryExpr).Fun,
                                                                            new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_bitmap),
                                                                                               store_addr,
                                                                                               store_value }) });
                                    newCmdSeq.Add(new_ac);
                                }
                                else
                                {
                                    if (this.splitProgram) {
                                        if (!isBitmapAddress(this.current_label, c, this.storeAddressRegionDB)
                                                && !isStackAddress(this.current_label, c, this.storeAddressRegionDB))
                                            newCmdSeq.Add(ac);
                                        break;
                                    }

                                    Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr> { store_addr });
                                    Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr> { store_addr });

                                    newCmdSeq.Add(ac);

                                    Expr rhs;
                                    //may exist an execution such that the stack is written
                                    // mem_stack := ITE(isAddrInStack(storeAddr), STORE(mem_stack, addr, value), mem_stack);
                                    if (!isNotStackAddress(this.current_label, c, this.storeAddressRegionDB))
                                    {
                                        rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                                isAddrInStack,
                                                new NAryExpr(Token.NoToken, (ac.Rhss[0] as NAryExpr).Fun, new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_stack), store_addr, store_value }),
                                                new IdentifierExpr(Token.NoToken, this.mem_stack) });
                                        AssignCmd stack_ac = new AssignCmd(Token.NoToken,
                                            new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                            new List<Expr> { rhs });
                                        newCmdSeq.Add(stack_ac);
                                    }

                                    //may exist an execution such that the bitmap is written
                                    // mem_bitmap := ITE(isAddrInBitmap(storeAddr), STORE(mem_bitmap, addr, value), mem_bitmap);
                                    if (!isNotBitmapAddress(this.current_label, c, this.storeAddressRegionDB))
                                    {
                                        rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                            isAddrInBitmap,
                                            new NAryExpr(Token.NoToken, (ac.Rhss[0] as NAryExpr).Fun, new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_bitmap), store_addr, store_value }),
                                            new IdentifierExpr(Token.NoToken, this.mem_bitmap) });
                                        AssignCmd bitmap_ac = new AssignCmd(Token.NoToken,
                                            new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                            new List<Expr> { rhs });
                                        newCmdSeq.Add(bitmap_ac);
                                    }
                                }

                                break;
                            }

                        case SlashVerifyCmdType.RepStosB:
                            {
                                Tuple<Variable, Expr, Expr, Expr> repstosArgs = Utils.getRepStosbArgs(ac);
                                Expr base_addr = repstosArgs.Item3;
                                Expr length = repstosArgs.Item2;

                                Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr> { base_addr });
                                Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr> { base_addr });

                                Expr rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                            isAddrInStack,
                                            new NAryExpr(Token.NoToken,
                                                (ac.Rhss[0] as NAryExpr).Fun,
                                                new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_stack), repstosArgs.Item2, repstosArgs.Item3, repstosArgs.Item4 }),
                                            new IdentifierExpr(Token.NoToken, this.mem_stack) });
                                AssignCmd stack_ac = new AssignCmd(Token.NoToken,
                                    new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                    new List<Expr> { rhs });

                                rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> {
                                            isAddrInBitmap,
                                            new NAryExpr(Token.NoToken,
                                                (ac.Rhss[0] as NAryExpr).Fun,
                                                new List<Expr> { new IdentifierExpr(Token.NoToken, this.mem_bitmap), repstosArgs.Item2, repstosArgs.Item3, repstosArgs.Item4 }),
                                            new IdentifierExpr(Token.NoToken, this.mem_bitmap) });
                                AssignCmd bitmap_ac = new AssignCmd(Token.NoToken,
                                    new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                    new List<Expr>() { rhs });

                                newCmdSeq.Add(ac);
                                newCmdSeq.Add(stack_ac);
                                newCmdSeq.Add(bitmap_ac);

                                break;
                            }

                        default:
                            {
                                if (ac.Lhss.First().DeepAssignedVariable.Name.Equals("mem_stack")) {
                                    if (isBitmapAddress(this.current_label, c, this.storeAddressRegionDB)
                                          || isNotStackAddress(this.current_label, c, this.storeAddressRegionDB))
                                        break;
                                    else if (isStackAddress(this.current_label, c, this.storeAddressRegionDB)) {
                                        AssignCmd updateStack = new AssignCmd(Token.NoToken, new List<AssignLhs> {new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack))}, new List<Expr> { Utils.getSplitMemoryUpdateExpr(ac) });
                                        newCmdSeq.Add(updateStack);
                                        break;
                                    }
                                }
                                else if (ac.Lhss.First().DeepAssignedVariable.Name.Equals("mem_bitmap")) {
                                    if (isStackAddress(this.current_label, c, this.storeAddressRegionDB)
                                          || isNotBitmapAddress(this.current_label, c, this.storeAddressRegionDB))
                                        break;
                                    else if (isBitmapAddress(this.current_label, c, this.storeAddressRegionDB)) {
                                        AssignCmd updateBitmap = new AssignCmd(Token.NoToken, new List<AssignLhs> {new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap))}, new List<Expr> { Utils.getSplitMemoryUpdateExpr(ac) });
                                        newCmdSeq.Add(updateBitmap);
                                        break;
                                    }
                                }
                                newCmdSeq.Add(ac);
                                break;
                            }

                    }
                }
                else
                {
                    newCmdSeq.Add(c);
                }
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
