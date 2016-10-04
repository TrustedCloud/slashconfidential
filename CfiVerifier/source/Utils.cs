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

    public enum SlashVerifyCmdType
    {
        None,
        Store8,
        Store16,
        Store32,
        Store64,
        RepStosB,
        Call,
        Ret,
        RemoteJmp,
        RemoteIndirectJmp,
        SetRSP
    };

    public static class Utils
    {

        public static void Assert(bool b, string msg = "")
        {
            if (!b) throw new Exception("assertion failure: " + msg);
        }

        public static void PrintProg(Program p)
        {
            var filename = Options.outputPath + @"/" + Options.instrumentedFile;
            var tuo = new TokenTextWriter(filename);
            try { p.Emit(tuo); } finally { tuo.Close(); }
        }

        public static void ExtractProgAndImpl(string fname, out Program prog, out Implementation impl)
        {
            if (!Utils.ParseProgram(fname, out prog)) {
                Utils.Assert(false, "Unable to parse file " + fname);
            }

            impl = prog.TopLevelDeclarations.Where(x => x is Implementation &&
                ((Implementation)x).Name.Contains("dll_func")).ElementAt(0) as Implementation;

            Utils.Assert(impl != null, "Unable to find Boogie implementation named \"dll_func\"");

        }

        public static bool ParseProgram(string fname, out Program prog)
        {
            prog = null;
            int errCount;
            try
            {
                errCount = Parser.Parse(fname, new List<string>(), out prog);
                if (errCount != 0 || prog == null)
                {
                    Console.WriteLine("WARNING: {0} parse errors detected in {1}", errCount, fname);
                    return false;
                }
            }
            catch (IOException e)
            {
                Console.WriteLine("WARNING: Error opening file \"{0}\": {1}", fname, e.Message);
                return false;
            }

            errCount = prog.Resolve();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} name resolution errors in {1}", errCount, fname);
                return false;
            }
            errCount = prog.Typecheck();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} type checking errors in {1}", errCount, fname);
                return false;
            }
            //var s = new FindLocationAssertion();
            //s.Visit(prog);
            return true;
        }

        public static bool ParseString(string fstring, out Program prog)
        {
            prog = null;
            int errCount;
            try
            {
                errCount = Parser.Parse(fstring, "<no file>", out prog);
                if (errCount != 0 || prog == null)
                {
                    Console.WriteLine("WARNING: {0} parse errors detected in {1}", errCount, fstring);
                    return false;
                }
            }
            catch (IOException e)
            {
                Console.WriteLine("WARNING: Error opening file \"{0}\": {1}", fstring, e.Message);
                return false;
            }

            errCount = prog.Resolve();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} name resolution errors in {1}", errCount, fstring);
                return false;
            }
            errCount = prog.Typecheck();
            if (errCount > 0)
            {
                Console.WriteLine("WARNING: {0} type checking errors in {1}", errCount, fstring);
                return false;
            }
            //var s = new FindLocationAssertion();
            //s.Visit(prog);
            return true;
        }

        public static LocalVariable MkLocalVar(string v, BType t)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v, t));
        }
        public static GlobalVariable MkGlobalVar(string v, BType t)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v, t));
        }

        public static Function FindFunctionInProgram(Program node, string name) {
            Function func = node.Functions.FirstOrDefault(f => f.Name.Equals(name));
            Utils.Assert(func != null, "Could not find function " + name);
            return func;
        }

        public static GlobalVariable FindGlobalVariableInProgram(Program node, string name)
        {
            GlobalVariable gv = node.GlobalVariables.FirstOrDefault(f => f.Name.Equals(name));
            Utils.Assert(gv != null, "Could not find global variable " + name);
            return gv;
        }

        public static Constant FindConstantInProgram(Program node, string name)
        {
            Constant c = node.Constants.FirstOrDefault(f => f.Name.Equals(name));
            Utils.Assert(c != null, "Could not find constant " + name);
            return c;
        }


        /* looks at the function used in the NAryExpr to determine the type: LOAD8, LOAD16,...,STORE64 */
        public static SlashVerifyCmdType getSlashVerifyCmdType(Cmd c)
        {
            Func<Expr, string, bool> RhsMatch = delegate(Expr x, String s)
            {
                return (x is NAryExpr && ((NAryExpr) x).Fun.FunctionName.Equals(s));
            };

            if (c is AssignCmd)
            {
                AssignCmd ac = c as AssignCmd;

                Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "getSlashVerifyCmdType not handling parallel assignCmds");
                AssignLhs lhs = ac.Lhss[0];
                Expr rhs = ac.Rhss[0];

                if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_8"))
                {
                    return SlashVerifyCmdType.Store8;
                }
                else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_16"))
                {
                    return SlashVerifyCmdType.Store16;
                }
                else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_32"))
                {
                    return SlashVerifyCmdType.Store32;
                }
                else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_64"))
                {
                    return SlashVerifyCmdType.Store64;
                }
                else if (lhs.Type.IsMap && RhsMatch(rhs, "REP_STOSB"))
                {
                    return SlashVerifyCmdType.RepStosB;
                }
                else if (lhs.Type.IsBv && lhs.DeepAssignedIdentifier.Name.Equals("RSP"))
                {
                    return SlashVerifyCmdType.SetRSP;
                }
            }
            else if (c is AssertCmd)
            {
                AssertCmd ac = c as AssertCmd;

                //extract instruction type
                string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                string attribute_jmptarget = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpTarget");

                if (attribute_cmdtype != null &&
                    attribute_cmdtype.Equals("ret"))
                {
                    return SlashVerifyCmdType.Ret;
                }
                else if (attribute_cmdtype != null &&
                    attribute_cmdtype.Equals("call"))
                {
                    return SlashVerifyCmdType.Call;
                }
                else if (attribute_cmdtype != null && attribute_jmptarget != null &&
                    attribute_cmdtype.Equals("remotejmp"))
                {
                    return SlashVerifyCmdType.RemoteJmp;
                }
                else if (attribute_cmdtype != null && attribute_jmptarget != null &&
                    attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget.Equals("remote"))
                {
                    return SlashVerifyCmdType.RemoteIndirectJmp;
                }
            }

            return SlashVerifyCmdType.None;
        }

        //input must be a load expression
		public static Tuple<Expr,Expr> getLoadArgs(Expr e)
        {
            Func<Expr, string, bool> RhsMatch = delegate(Expr x, String s)
            {
                return (x is NAryExpr && ((NAryExpr)x).Fun.FunctionName.Equals(s));
            };

            Utils.Assert( RhsMatch(e, "LOAD_LE_8") ||
                          RhsMatch(e, "LOAD_LE_16") ||
                          RhsMatch(e, "LOAD_LE_32") ||
                          RhsMatch(e, "LOAD_LE_64"),
                "Expected load expression");
            return Tuple.Create<Expr, Expr>(((NAryExpr) e).Args[0], ((NAryExpr) e).Args[1]);
        }

        /* returns (mem, addr, data) */
        public static Tuple<Variable, Expr, Expr> getStoreArgs(AssignCmd c)
        {
            Func<Expr, string, bool> RhsMatch = delegate(Expr x, String s)
            {
                return (x is NAryExpr && ((NAryExpr)x).Fun.FunctionName.Equals(s));
            };

            Utils.Assert(c.Lhss.Count == 1 && c.Rhss.Count == 1, "getStoreArgs not handling parallel assignCmds");
            AssignLhs lhs = c.Lhss[0];
            Expr rhs = c.Rhss[0];

            Utils.Assert(RhsMatch(rhs, "STORE_LE_8") || RhsMatch(rhs, "STORE_LE_16") || RhsMatch(rhs, "STORE_LE_32") || RhsMatch(rhs, "STORE_LE_64"),
                "Expected store expression");

            Utils.Assert(((NAryExpr)rhs).Args.Count == 3, "Store must have 3 arguments");
            return Tuple.Create<Variable, Expr, Expr>((((NAryExpr)rhs).Args[0] as IdentifierExpr).Decl,
                ((NAryExpr)rhs).Args[1],
                ((NAryExpr)rhs).Args[2]);
        }

        /* returns (mem, rcx, rdi, al) */
        public static Tuple<Variable, Expr, Expr, Expr> getRepStosbArgs(AssignCmd c)
        {
            Utils.Assert(getSlashVerifyCmdType(c) == SlashVerifyCmdType.RepStosB, "getRepStosbArgs not a RepStosb command");
            Utils.Assert(c.Lhss.Count == 1 && c.Rhss.Count == 1, "getRepStosbArgs not handling parallel assignCmds");
            AssignLhs lhs = c.Lhss[0];
            Expr rhs = c.Rhss[0];
            Utils.Assert(((NAryExpr) rhs).Args.Count == 4, "RepStosb must have 4 arguments");
            return Tuple.Create<Variable, Expr, Expr, Expr>((((NAryExpr) rhs).Args[0] as IdentifierExpr).Decl,
                ((NAryExpr) rhs).Args[1],
                ((NAryExpr) rhs).Args[2],
                ((NAryExpr) rhs).Args[3]);
        }

        #region recursive utilities for Expr
        public static List<Variable> getNestedVars(Expr e)
        {
            if (e is IdentifierExpr)
            {
                return new List<Variable>() { (e as IdentifierExpr).Decl };
            }
            else if (e is BvConcatExpr)
            {
                List<Variable> tmp = getNestedVars((e as BvConcatExpr).E0).Union(getNestedVars((e as BvConcatExpr).E1)).ToList();
                return tmp;
            }
            else if (e is BvExtractExpr)
            {
                List<Variable> tmp = getNestedVars((e as BvExtractExpr).Bitvector);
                return tmp;
            }
            else if (e is NAryExpr)
            {
                List<Variable> tmp = (e as NAryExpr).Args.Aggregate(new List<Variable>(), (acc, expr) =>
                    acc.Union(getNestedVars(expr)).ToList<Variable>());
                return tmp;
            }
            else
            {
                return new List<Variable>();
            }
        }

        public static List<IAppliable> getNestedFunctions(Expr e)
        {
            if (e is IdentifierExpr)
            {
                return new List<IAppliable>();
            }
            else if (e is LiteralExpr)
            {
                return new List<IAppliable>();
            }
            else if (e is BvExtractExpr)
            {
                return getNestedFunctions((e as BvExtractExpr).Bitvector);
            }
            else if (e is BvConcatExpr)
            {
                return getNestedFunctions((e as BvConcatExpr).E0).ToList().
                    Concat(getNestedFunctions((e as BvConcatExpr).E1)).ToList();
            }
            else if (e is NAryExpr)
            {
                List<IAppliable> result = new List<IAppliable>() { (e as NAryExpr).Fun };
                foreach (Expr e_sub in (e as NAryExpr).Args)
                {
                    result.AddRange(getNestedFunctions(e_sub));
                }
                return result.ToList();
            }
            Utils.Assert(false, "should not get here: " + e);
            return new List<IAppliable>();
        }

        public static Expr substituteForIdentifierExpr(Expr original, IdentifierExpr id, Expr replacement)
        {
            if (original is IdentifierExpr) { return ((original as IdentifierExpr).Name.Equals(id.Name)) ? replacement : original; }
            else if (original is LiteralExpr) { return original; }
            else if (original is BvExtractExpr)
            {
                BvExtractExpr tmp = (original as BvExtractExpr);
                return new BvExtractExpr(Token.NoToken, substituteForIdentifierExpr(tmp.Bitvector, id, replacement), tmp.End, tmp.Start);
            }
            else if (original is BvConcatExpr)
            {
                BvConcatExpr tmp = (original as BvConcatExpr);
                return new BvConcatExpr(Token.NoToken,
                    substituteForIdentifierExpr(tmp.E0, id, replacement),
                    substituteForIdentifierExpr(tmp.E1, id, replacement));
            }
            else if (original is NAryExpr)
            {
                NAryExpr tmp = (original as NAryExpr);
                List<Expr> new_args = new List<Expr>();
                foreach (Expr e in tmp.Args) {
                    new_args.Add(substituteForIdentifierExpr(e, id, replacement));
                }
                return new NAryExpr(Token.NoToken, tmp.Fun, new_args);
            }

            Utils.Assert(false, "should not get here: " + original);
            return original;
        }

        public static List<IdentifierExpr> getSubExpressions(Expr e)
        {
            if (e is IdentifierExpr)
            {
                return new List<IdentifierExpr>() { e as IdentifierExpr };
            }
            else if (e is LiteralExpr)
            {
                return new List<IdentifierExpr>();
            }
            else if (e is BvExtractExpr)
            {
                return getSubExpressions((e as BvExtractExpr).Bitvector);
            }
            else if (e is BvConcatExpr)
            {
                return getSubExpressions((e as BvConcatExpr).E0).ToList().
                    Concat(getSubExpressions((e as BvConcatExpr).E1)).ToList();
            }
            else if (e is NAryExpr)
            {
                List<IdentifierExpr> result = new List<IdentifierExpr>();
                foreach (Expr e_sub in (e as NAryExpr).Args)
                {
                    result.AddRange(getSubExpressions(e_sub));
                }
                return result.Distinct().ToList();
            }
            Utils.Assert(false, "should not get here: " + e);
            return new List<IdentifierExpr>();
        }
        #endregion


        public static void InstrumentLoopInvariant(Program prog, Implementation impl, String memCheckpointLabel, List<String> loopHeaderLabels)
        {
            (new LoopInvariantInstrumenter(memCheckpointLabel, loopHeaderLabels)).Visit(prog);
        }

        public static Tuple<String, List<String>> HandleLoops(Program prog, Implementation impl)
        {
            LoopDetector loopDetector = new LoopDetector();
            loopDetector.Visit(impl); //necessary before querying the stack size estimate
            List<Block> blocksInNaturalLoops = loopDetector.getBlocksInNaturalLoops();
            List<Block> loopHeaders = loopDetector.getLoopHeaders();
            List<String> loopHeaderLabels = new List<string>();
            loopHeaders.Iter(l => loopHeaderLabels.Add(l.Label));
            //if (loopHeaders.Count > 0) { Console.WriteLine("LOOP HEADERS: {0}", loopHeaders.MapConcat(x => x.Label, ",")); }

            var graph = Program.GraphFromImpl(impl);
            //Utils.Assert(graph.Reducible, "Irreducible flow graphs are unsupported.");
            Utils.Assert(graph.Nodes.Count() > 1, "Doesn't work for graphs with 1 node");
            //figure out the source node. that's where the program starts.
            IEnumerable<Block> sourceNodes = graph.Nodes.Where(n => graph.Predecessors(n).Count() == 0);
            //Also assert that there is only one source node (unless there is unreachable node in the CFG)
            Utils.Assert(sourceNodes.Count() == 1);
            Block sourceNode = sourceNodes.ElementAt(0);
            //Console.WriteLine("SOURCE NODE: {0}", sourceNode.Label);
            //traverse starting from source node until you get nondeterministic goto, or a loop header
            Block currentNode = sourceNode;
            while (graph.Successors(currentNode).Count() < 2)
            {
                IEnumerable<Block> successors = graph.Successors(currentNode);
                //we know this is a loopy program, so we should not get to a sink node in this loop.
                Utils.Assert(successors.Count() > 0, "We got to a sink node. why???");

                Block nextNode = successors.ElementAt(0);
                //encountered a loop header before a CFG split?
                if (loopHeaderLabels.Contains(nextNode.Label))
                {
                    break;
                }
                currentNode = nextNode;
            }
            //Console.WriteLine("We should capture mem here: {0}", currentNode.Label);
            return new Tuple<string, List<string>>(currentNode.Label, loopHeaderLabels);
        }

		public static bool ProgramIsSplit(Program prog) {
			Utils.Assert (prog.Implementations.Count() == 1, "Expected program with a single implementation!");
			return prog.GlobalVariables.FirstOrDefault(i => i.Name.Equals("mem_bitmap")) != null
				&& prog.GlobalVariables.FirstOrDefault(i => i.Name.Equals("mem_stack")) != null;
        }
    }
}
