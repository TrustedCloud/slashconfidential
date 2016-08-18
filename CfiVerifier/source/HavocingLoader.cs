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
    public class HavocingLoader : StandardVisitor
    {
        private GlobalVariable mem, mem_stack, mem_bitmap;
        private Function addrInBitmap, addrInStack;
        private int havocedConstantsCount;
        private Program prog;

        /* Precondition: Memory is modeled as 3 maps: mem, mem_stack, mem_bitmap
         * */
        public override Program VisitProgram(Program node)
        {
            if (!Options.splitMemoryModel) { return base.VisitProgram(node); }

            this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
            this.addrInStack = Utils.FindFunctionInProgram(node, "addrInStack");
            this.mem = Utils.FindGlobalVariableInProgram(node, "mem");
            this.mem_stack = Utils.FindGlobalVariableInProgram(node, "mem_stack");
            this.mem_bitmap = Utils.FindGlobalVariableInProgram(node, "mem_bitmap");

            this.havocedConstantsCount = 0;
            this.prog = node;

            return base.VisitProgram(node);
        }

        private Constant MkHavocConst(int size)
        {
            Constant c = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "loadHavoc_" + this.havocedConstantsCount.ToString(), new BvType(size)));
            this.havocedConstantsCount += 1;
            this.prog.AddTopLevelDeclaration(c);
            return c;
        }

        private Expr havocLoad(Expr e)
        {
            //if there is no load, no point in recursing
            if (!(Utils.getNestedFunctions(e).Any(x => x.FunctionName.Contains("LOAD_LE")))) { return e; }

            //we have one or more load expressions here. so let's recursively find them and substitute.
            if (e is NAryExpr)
            {
                //this is a load expression
                if ((e as NAryExpr).Fun.FunctionName.Contains("LOAD_LE"))
                {
                    var identifiers = Utils.getNestedVars((e as NAryExpr).Args[0]);
                    if (!identifiers.Any(v => v.Name.Equals("mem_stack") || v.Name.Equals("mem_bitmap")))
                    {
                        //safe to abstract away if not loading from mem_stack or mem_bitmap
                        string[] separators = { "LOAD_LE_" };
                        int size = Int32.Parse((e as NAryExpr).Fun.FunctionName.Split(separators, StringSplitOptions.None)[1]);
                        return new IdentifierExpr(Token.NoToken, MkHavocConst(size));
                    }
                }

                //not a load expression that we can abstract, so we need to recurse
                List<Expr> new_args = new List<Expr>();
                foreach (Expr arg in (e as NAryExpr).Args)
                {
                    new_args.Add(havocLoad(arg));
                }
                return new NAryExpr(Token.NoToken, (e as NAryExpr).Fun, new_args);
            }
            else if (e is BvExtractExpr)
            {
                return new BvExtractExpr(Token.NoToken,
                    havocLoad((e as BvExtractExpr).Bitvector),
                    (e as BvExtractExpr).End,
                    (e as BvExtractExpr).Start);
            }
            else if (e is BvConcatExpr)
            {
                return new BvConcatExpr(Token.NoToken,
                    havocLoad((e as BvConcatExpr).E0),
                    havocLoad((e as BvConcatExpr).E1));
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
                    ac = new AssignCmd(Token.NoToken, new List<AssignLhs>() { ac.Lhss[0] }, new List<Expr>() { havocLoad(ac.Rhss[0]) });
                    newCmdSeq.Add(ac);
                }
                else if (c is AssumeCmd)
                {
                    AssumeCmd ac = c as AssumeCmd;
                    ac = new AssumeCmd(Token.NoToken, havocLoad(ac.Expr), ac.Attributes);
                    newCmdSeq.Add(ac);
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
