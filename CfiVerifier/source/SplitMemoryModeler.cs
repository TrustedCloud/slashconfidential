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
                    Tuple<Variable, Expr> load_args = Utils.getLoadArgs(e);
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
                    Expr load_addr = loadAddresses.Count() > 0 ? loadAddresses[0] : null;

                    if (load_addr != null)
                    {
                        AssertCmd assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr>() { load_addr }));
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));

                        assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { load_addr }));
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));
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

                                AssertCmd assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr>() { store_addr }));
                                newCmdSeq.Add(assertion);
                                VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));

                                assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { store_addr }));
                                newCmdSeq.Add(assertion);
                                VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));

                                //Expr addr_in_mem =
                                //    Expr.And(
                                //        new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                //            new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                //        new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                //            new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.bitmap_low) }));
                                //assertion = new AssertCmd(Token.NoToken, addr_in_mem);
                                //newCmdSeq.Add(assertion);
                                //VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion, Utils.getSlashVerifyCmdType(ac));

                                break;
                            }

                        case SlashVerifyCmdType.RepStosB: //x := REP_STOSB(mem, e1, e2, e3)
                            {
                                break;
                            }

                        default: //x:=e
                            {
                                break;
                            }
                    }
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

        enum AddrType { Unknown, StackAddress, BitmapAddress, MemAddress };

        public SplitMemoryModeler(
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB,
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB)
        {
            this.storeAddressRegionDB = storeAddressRegionDB;
            this.loadAddressRegionDB = loadAddressRegionDB;
        }

        public override Program VisitProgram(Program node)
        {
            if (!Options.splitMemoryModel) { return base.VisitProgram(node); }

            this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
            this.addrInStack = Utils.FindFunctionInProgram(node, "addrInStack");
            this.mem = Utils.FindGlobalVariableInProgram(node, "mem");

            this.mem_stack = Utils.MkGlobalVar("mem_stack", this.mem.TypedIdent.Type);
            node.AddTopLevelDeclaration(this.mem_stack); //add as global variable
            this.mem_bitmap = Utils.MkGlobalVar("mem_bitmap", this.mem.TypedIdent.Type);
            node.AddTopLevelDeclaration(this.mem_bitmap); //add as global variable

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            if (!Options.splitMemoryModel) { return base.VisitImplementation(node); }

            node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_bitmap));
            node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_stack));
            return base.VisitImplementation(node);
        }

        //public static bool isStackAddressSyntactically(Expr addr)
        //{
        //    return getSubExpressions(addr).Any(x => x.Name.Equals("RSP")); //FIXME: clearly unsound, but lets roll with it
        //}

        private bool isRegionAddress(string label, Cmd c, string region_id, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            foreach (Tuple<string, Cmd, AssertCmd> t in db.Keys)
            {
                if (!t.Item1.Equals(label)) { continue; }
                if (!t.Item2.ToString().Equals(c.ToString())) { continue; }
                if (!Utils.getNestedFunctions(t.Item3.Expr).Any(x => x.FunctionName.Equals(region_id))) { continue; }
                return db[t];
            }
            return false;
        }

        private bool isStackAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "addrInStack", db);
        }

        private bool isBitmapAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        {
            return isRegionAddress(label, c, "addrInBitmap", db);
        }

        //private bool isMemAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
        //{
        //    return isRegionAddress(label, c, "GE_64", db);
        //}

        //takes an expression and substitutes desired mem for each load(mem,..) sub-expression
        private Expr splitMemoryOnAllLoads(Expr e, AddrType addrType)
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
                    Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr>() { addr });
                    Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr>() { addr });

                    Expr tmp = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInBitmap, new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, mem) });
                    return new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInStack, new IdentifierExpr(Token.NoToken, this.mem_stack), tmp });
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
                    Tuple<Variable, Expr> load_args = Utils.getLoadArgs(e);
                    Expr desired_mem = getDesiredMemExpr(load_args.Item2);
                    //even the address expression can have a load
                    return new NAryExpr(Token.NoToken, (e as NAryExpr).Fun, new List<Expr>() { desired_mem, splitMemoryOnAllLoads(load_args.Item2, addrType) });
                }
                else
                {
                    //not a load expression, but we need to recurse
                    List<Expr> new_args = new List<Expr>();
                    foreach (Expr arg in (e as NAryExpr).Args)
                    {
                        new_args.Add(splitMemoryOnAllLoads(arg, addrType));
                    }
                    return new NAryExpr(Token.NoToken, (e as NAryExpr).Fun, new_args);
                }
            }
            else if (e is BvExtractExpr)
            {
                return new BvExtractExpr(Token.NoToken,
                    splitMemoryOnAllLoads((e as BvExtractExpr).Bitvector, addrType),
                    (e as BvExtractExpr).End,
                    (e as BvExtractExpr).Start);
            }
            else if (e is BvConcatExpr)
            {
                return new BvConcatExpr(Token.NoToken,
                    splitMemoryOnAllLoads((e as BvConcatExpr).E0, addrType),
                    splitMemoryOnAllLoads((e as BvConcatExpr).E1, addrType));
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

            return splitMemoryOnAllLoads(toTransform, addrType);
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
                    ac = new AssignCmd(Token.NoToken, new List<AssignLhs>() { ac.Lhss[0] }, new List<Expr>() { transformLoad(this.current_label, c, ac.Rhss[0]) });

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
                                    AssignCmd new_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                        new List<Expr>() { new NAryExpr(Token.NoToken, 
                                                                            (ac.Rhss[0] as NAryExpr).Fun, 
                                                                            new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_stack), 
                                                                                               store_addr,
                                                                                               store_value }) });
                                    newCmdSeq.Add(new_ac);
                                }
                                else if (addrType == AddrType.BitmapAddress)
                                {
                                    AssignCmd new_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                        new List<Expr>() { new NAryExpr(Token.NoToken, 
                                                                            (ac.Rhss[0] as NAryExpr).Fun, 
                                                                            new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), 
                                                                                               store_addr,
                                                                                               store_value }) });
                                    newCmdSeq.Add(new_ac);
                                }
                                else
                                {
                                    Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr>() { store_addr });
                                    Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr>() { store_addr });

                                    Expr rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInStack, 
                                            new NAryExpr(Token.NoToken, (ac.Rhss[0] as NAryExpr).Fun, new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_stack), store_addr, store_value }),
                                            new IdentifierExpr(Token.NoToken, this.mem_stack) });
                                    AssignCmd stack_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                        new List<Expr>() { rhs });

                                    rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInBitmap, 
                                            new NAryExpr(Token.NoToken, (ac.Rhss[0] as NAryExpr).Fun, new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), store_addr, store_value }),
                                            new IdentifierExpr(Token.NoToken, this.mem_bitmap) });
                                    AssignCmd bitmap_ac = new AssignCmd(Token.NoToken,
                                        new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_bitmap)) },
                                        new List<Expr>() { rhs });

                                    newCmdSeq.Add(ac);
                                    newCmdSeq.Add(stack_ac);
                                    newCmdSeq.Add(bitmap_ac);
                                }

                                break;
                            }

                        case SlashVerifyCmdType.RepStosB:
                            {
                                Tuple<Variable, Expr, Expr, Expr> repstosArgs = Utils.getRepStosbArgs(ac);
                                Expr base_addr = repstosArgs.Item3;
                                Expr length = repstosArgs.Item2;

                                Expr isAddrInBitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr>() { base_addr });
                                Expr isAddrInStack = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInStack), new List<Expr>() { base_addr });

                                Expr rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInStack, 
                                            new NAryExpr(Token.NoToken, 
                                                (ac.Rhss[0] as NAryExpr).Fun, 
                                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_stack), repstosArgs.Item2, repstosArgs.Item3, repstosArgs.Item4 }),
                                            new IdentifierExpr(Token.NoToken, this.mem_stack) });
                                AssignCmd stack_ac = new AssignCmd(Token.NoToken,
                                    new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_stack)) },
                                    new List<Expr>() { rhs });

                                rhs = new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr>() { 
                                            isAddrInBitmap, 
                                            new NAryExpr(Token.NoToken, 
                                                (ac.Rhss[0] as NAryExpr).Fun, 
                                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), repstosArgs.Item2, repstosArgs.Item3, repstosArgs.Item4 }),
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
