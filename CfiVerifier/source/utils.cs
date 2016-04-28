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
    static class Utils
    {
        #region debugging aid
        //Testing the crash when looking up the type of vars in a havoc cmd
        class TestHavocStmtsVisitor : StandardVisitor
        {
            public override Cmd VisitHavocCmd(HavocCmd node)
            {
                foreach (IdentifierExpr e in node.Vars)
                    Debug.Assert(e.Type != null);
                return base.VisitHavocCmd(node);
            }
        }

        public static bool verbosityLevel(int level) { return (Options.verbose >= level); }
        #endregion

        #region Various Boogie utilities
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
        #endregion

        public static LocalVariable MkLocalVar(string v, BType t)
        {
            return new LocalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v, t));
        }
        public static GlobalVariable MkGlobalVar(string v, BType t)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, v, t));
        }

        #region AssignCmd classifiers
        enum SlashVerifyCmdType { None, Load8, Load16, Load32, Load64, Store8, Store16, Store32, Store64, RepStosB };
        /* looks at the function used in the NAryExpr to determine the type: LOAD8, LOAD16,...,STORE64 */
        private static SlashVerifyCmdType getSlashVerifyCmdType(AssignCmd c)
        {
            Func<Expr, string, bool> RhsMatch = delegate(Expr x, String s)
            {
                return (x is NAryExpr && ((NAryExpr) x).Fun.FunctionName.Equals(s));
            };

            Utils.Assert(c.Lhss.Count == 1 && c.Rhss.Count == 1, "getSlashVerifyCmdType not handling parallel assignCmds");
            AssignLhs lhs = c.Lhss[0];
            Expr rhs = c.Rhss[0];

            if (lhs.Type.IsBv && RhsMatch(rhs, "LOAD_LE_8")) { return SlashVerifyCmdType.Load8; }
            else if (lhs.Type.IsBv && RhsMatch(rhs, "LOAD_LE_16")) { return SlashVerifyCmdType.Load16; }
            else if (lhs.Type.IsBv && RhsMatch(rhs, "LOAD_LE_32")) { return SlashVerifyCmdType.Load32; }
            else if (lhs.Type.IsBv && RhsMatch(rhs, "LOAD_LE_64")) { return SlashVerifyCmdType.Load64; }
            /* sometimes loads are cast to larger sizes with 0bvn */
            /*
            else if (lhs.Type.IsBv &&
                    (rhs is BvConcatExpr) &&
                    (rhs as BvConcatExpr).E0 is LiteralExpr &&
                    (RhsMatch((rhs as BvConcatExpr).E1, "LOAD_LE_8"))) { return SlashVerifyCmdType.Load8; }
            else if (lhs.Type.IsBv &&
                    (rhs is BvConcatExpr) &&
                    (rhs as BvConcatExpr).E0 is LiteralExpr &&
                    (RhsMatch((rhs as BvConcatExpr).E1, "LOAD_LE_16"))) { return SlashVerifyCmdType.Load16; }
            else if (lhs.Type.IsBv &&
                    (rhs is BvConcatExpr) &&
                    (rhs as BvConcatExpr).E0 is LiteralExpr &&
                    (RhsMatch((rhs as BvConcatExpr).E1, "LOAD_LE_32"))) { return SlashVerifyCmdType.Load32; }
            else if (lhs.Type.IsBv &&
                    (rhs is NAryExpr) &&
                    ((rhs as NAryExpr).Fun.FunctionName.Equals("MINUS_64") || (rhs as NAryExpr).Fun.FunctionName.Equals("PLUS_64")) &&
                    ((rhs as NAryExpr).Args[0] is NAryExpr) &&
                    ((rhs as NAryExpr).Args[0] as NAryExpr).Fun.FunctionName.Equals("LOAD_LE_64")) { return SlashVerifyCmdType.Load64; }
             * */
            else if (lhs.Type.IsBv && getNestedFunctions(rhs).Any(x => x.FunctionName.Equals("LOAD_LE_8"))) { return SlashVerifyCmdType.Load8; }
            else if (lhs.Type.IsBv && getNestedFunctions(rhs).Any(x => x.FunctionName.Equals("LOAD_LE_16"))) { return SlashVerifyCmdType.Load16; }
            else if (lhs.Type.IsBv && getNestedFunctions(rhs).Any(x => x.FunctionName.Equals("LOAD_LE_32"))) { return SlashVerifyCmdType.Load32; }
            else if (lhs.Type.IsBv && getNestedFunctions(rhs).Any(x => x.FunctionName.Equals("LOAD_LE_64"))) { return SlashVerifyCmdType.Load64; }
            else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_8")) { return SlashVerifyCmdType.Store8; }
            else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_16")) { return SlashVerifyCmdType.Store16; }
            else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_32")) { return SlashVerifyCmdType.Store32; }
            else if (lhs.Type.IsMap && RhsMatch(rhs, "STORE_LE_64")) { return SlashVerifyCmdType.Store64; }
            else if (lhs.Type.IsMap && RhsMatch(rhs, "REP_STOSB")) { return SlashVerifyCmdType.RepStosB; }
            else { return SlashVerifyCmdType.None; }
        }

        //input must be a load expression
        private static Tuple<Variable,Expr> getLoadArgs(Expr e)
        {
            Func<Expr, string, bool> RhsMatch = delegate(Expr x, String s)
            {
                return (x is NAryExpr && ((NAryExpr)x).Fun.FunctionName.Equals(s));
            };

            Utils.Assert( RhsMatch(e, "LOAD_LE_8") || RhsMatch(e, "LOAD_LE_16") || RhsMatch(e, "LOAD_LE_32") || RhsMatch(e, "LOAD_LE_64"),
                "Expected load expression");
            return Tuple.Create<Variable, Expr>((((NAryExpr) e).Args[0] as IdentifierExpr).Decl, ((NAryExpr) e).Args[1]);
        }

        /* returns (mem, addr, data) */
        private static Tuple<Variable, Expr, Expr> getStoreArgs(AssignCmd c)
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
        private static Tuple<Variable, Expr, Expr, Expr> getRepStosbArgs(AssignCmd c)
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
        #endregion

        #region recursive utilities for Expr
        private static List<Variable> getNestedVars(Expr e)
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

        private static List<IAppliable> getNestedFunctions(Expr e)
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

        private static Expr substituteForIdentifierExpr(Expr original, IdentifierExpr id, Expr replacement)
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

        private static List<IdentifierExpr> getSubExpressions(Expr e)
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

        #region Instrument havoc based on adversary model
        public class HavocingAdversary : StandardVisitor
        {
            public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
            {
                List<Cmd> newCmdSeq = new List<Cmd>();
                foreach (Cmd c in cmdSeq)
                {
                    if (c is AssignCmd)
                    {
                        AssignCmd ac = c as AssignCmd;
                        Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                        if (getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load8 ||
                            getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load16 ||
                            getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load32 ||
                            getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load64)
                        {
                            //__SlashVerify__tmpmem := mem; havoc mem; assume forall i: enc(i) ==> mem[i] == __SlashVerify__tmpmem[i]
                            // modeled within call __SlashVerify__MNEMAdversary();
                            newCmdSeq.Add(new CallCmd(Token.NoToken, "__SlashVerify__HavocingAdversary", 
                                new List<Expr>(), new List<IdentifierExpr>()));
                        }
                    }
                    newCmdSeq.Add(c);
                }
                return base.VisitCmdSeq(newCmdSeq);
            } 
        }
        #endregion

        //Conservative estimate of stack space used by the function
        public class StackSizeEstimator : StandardVisitor
        {
          List<int> rsp_subtractions = new List<int>();
          bool visit_happened = false;
          List<Block> blocksWithinNautralLoops;

          public override Implementation VisitImplementation(Implementation node)
          {
              LoopDetector loopDetector = new LoopDetector();
              loopDetector.Visit(node);
              this.blocksWithinNautralLoops = loopDetector.getBlocksInNaturalLoops();
              this.visit_happened = true;
              return base.VisitImplementation(node);
          }

          public override Block VisitBlock(Block node)
          {
              foreach (Cmd c in node.Cmds)
              {
                  AssignCmd ac = c as AssignCmd;
                  if (ac == null) { continue; }
                  Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Expected assignments to have 1 lhs and 1 rhs");
                  AssignLhs lhs = ac.Lhss.ElementAt(0);
                  Expr rhs = ac.Rhss.ElementAt(0);

                  if (!(lhs.Type.IsBv && lhs.DeepAssignedIdentifier.Name.Equals("RSP"))) { continue; } //lhs is RSP
                  if (!(rhs is NAryExpr)) { continue; } //rhs is function application
                  if (!((NAryExpr)rhs).Fun.FunctionName.Equals("MINUS_64")) { continue; } //rhs is a minus operation
                  if (!(((NAryExpr)rhs).Args.ElementAt(0) is IdentifierExpr)) { continue; } //1st argument is a id like RHS
                  if (!(((NAryExpr)rhs).Args.ElementAt(0) as IdentifierExpr).Name.Equals("RSP")) { continue; } //1st argument is a id like RHS
                  if (!(((NAryExpr)rhs).Args.ElementAt(1) is LiteralExpr)) { continue; } //2nd argument is a constant like 384bv64
                  if (!((((NAryExpr)rhs).Args.ElementAt(1) as LiteralExpr).Type == BType.GetBvType(64))) { continue; } //2nd argument is bitvector literal       

                  int operand = ((((NAryExpr)rhs).Args.ElementAt(1) as LiteralExpr).asBvConst).Value.ToInt;

                  Utils.Assert(blocksWithinNautralLoops.All(x => x.Label != node.Label),
                      "Setting RSP within a loop: " + ac + " at label " + node.Label);

                  rsp_subtractions.Add(operand);
              }

              return base.VisitBlock(node);
          }

          public int getStackEstimate(int default_size) {
            Utils.Assert(visit_happened, "StackSizeEstimator: must call visit before querying stack size estimate");
            //sum up all the subtractions
            return this.rsp_subtractions.Count > 0 ? this.rsp_subtractions.Sum() : default_size;
          }
        }

        public class LoopDetector : StandardVisitor
        {
          List<Block> blocksInNaturalLoops = new List<Block>();
          List<Block> loopHeaders = new List<Block>();
          bool visit_happened = false;

          public override Implementation VisitImplementation(Implementation impl)
          {
            Graph<Block> g = Program.GraphFromImpl(impl);
            g.ComputeLoops(); // this is the call that does all of the processing
            Utils.Assert(g.Reducible, "Irreducible flow graphs are unsupported.");
            foreach (Block header in cce.NonNull(g.Headers)) {
              this.loopHeaders.Add(header);
              foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header))) {
                foreach (Block b in g.NaturalLoops(header, backEdgeNode)) {
                  this.blocksInNaturalLoops.Add(b);
                }
              }
            }
            visit_happened = true;
            return base.VisitImplementation(impl);
          }

          public List<Block> getBlocksInNaturalLoops()
          {
            Utils.Assert(visit_happened, "LoopDetector: must call visit before querying for loops");
            //sum up all the subtractions
            return this.blocksInNaturalLoops;
          }

          public List<Block> getLoopHeaders()
          {
            Utils.Assert(visit_happened, "LoopDetector: must call visit before querying for loopHeaders");
            return this.loopHeaders;
          }
        }

        public class LiveVariableAnalyzer
        {
            private GlobalVariable mem, mem_bitmap, mem_stack;
            private GlobalVariable R8, R9, RAX, RCX, RDX, R10, R11, RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15;
            //private GlobalVariable AF, CF, OF, PF, SF, ZF;

            public LiveVariableAnalyzer(Program node)
            {
                this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
                Utils.Assert(this.mem != null, "Could not find mem variable");
                if (Options.splitMemoryModel)
                {
                    this.mem_stack = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_stack"));
                    Utils.Assert(this.mem_stack != null, "Could not find mem_stack variable");
                    this.mem_bitmap = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_bitmap"));
                    Utils.Assert(this.mem_bitmap != null, "Could not find mem_bitmap variable");
                }
                this.R8 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R8"));
                Utils.Assert(this.R8 != null, "Could not find R8 variable");
                this.R9 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R9"));
                Utils.Assert(this.R9 != null, "Could not find R9 variable");
                this.RAX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RAX"));
                Utils.Assert(this.RAX != null, "Could not find RAX variable");
                this.RCX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RCX"));
                Utils.Assert(this.RCX != null, "Could not find RCX variable");
                this.RDX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDX"));
                Utils.Assert(this.RDX != null, "Could not find RDX variable");
                this.R10 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R10"));
                Utils.Assert(this.R10 != null, "Could not find R10 variable");
                this.R11 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R11"));
                Utils.Assert(this.R11 != null, "Could not find R11 variable");
                this.RBX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RBX"));
                Utils.Assert(this.RBX != null, "Could not find RBX variable");
                this.RBP = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RBP"));
                Utils.Assert(this.RBP != null, "Could not find RBP variable");
                this.RDI = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDI"));
                Utils.Assert(this.RDI != null, "Could not find RDI variable");
                this.RSI = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RSI"));
                Utils.Assert(this.RSI != null, "Could not find RSI variable");
                this.RSP = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RSP"));
                Utils.Assert(this.RSP != null, "Could not find RSP variable");
                this.R12 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R12"));
                Utils.Assert(this.R12 != null, "Could not find R12 variable");
                this.R13 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R13"));
                Utils.Assert(this.R13 != null, "Could not find R13 variable");
                this.R14 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R14"));
                Utils.Assert(this.R14 != null, "Could not find R14 variable");
                this.R15 = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("R15"));
                Utils.Assert(this.R15 != null, "Could not find R15 variable");
                //this.AF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("AF"));
                //Utils.Assert(this.AF != null, "Could not find AF variable");
                //this.CF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("CF"));
                //Utils.Assert(this.CF != null, "Could not find CF variable");
                //this.OF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("OF"));
                //Utils.Assert(this.OF != null, "Could not find OF variable");
                //this.PF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("PF"));
                //Utils.Assert(this.PF != null, "Could not find PF variable");
                //this.SF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("SF"));
                //Utils.Assert(this.SF != null, "Could not find SF variable");
                //this.ZF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("ZF"));
                //Utils.Assert(this.ZF != null, "Could not find ZF variable");
            }

            public static Dictionary<Block, HashSet<Block>> buildSuccessorRelation(Implementation impl)
            {
                Dictionary<Block, HashSet<Block>> successors = new Dictionary<Block, HashSet<Block>>();
                impl.Blocks.ForEach(x => successors.Add(x, new HashSet<Block>()));
                foreach (Block b in impl.Blocks)
                {
                    //found edge from x to b and now adding it to successors
                    //b.Predecessors.ForEach(x => successors[x].Add(b));
                    if (b.TransferCmd is GotoCmd)
                    {
                        (b.TransferCmd as GotoCmd).labelTargets.ForEach(x => successors[b].Add(x));
                    }
                }
                return successors;
            }

            /*
              for i = 1 to n do live[i] := {}
                while (live[] changes) do
                  for i = 1 to n do
                    live[i] = ( (\union_{s \in succ(i)}{live(s)}) \ def(i)) U ref(i)
             * */
            public Dictionary<Block, Dictionary<Cmd, List<Variable>>> getLiveVariables(Implementation impl)
            {
                Func<List<Variable>, Cmd, List<Variable>> transformStmt =
                    delegate(List<Variable> out_live, Cmd c)
                {
                    List<Variable> in_live = new List<Variable>();
                    foreach (Variable v in out_live) { in_live.Add(v); }

                    if (c is AssignCmd)
                    {
                        Utils.Assert((c as AssignCmd).Lhss.Count == 1 && (c as AssignCmd).Rhss.Count == 1, "Expected only one lhs and one rhs");
                        Variable lhs = (c as AssignCmd).Lhss[0].DeepAssignedVariable;
                        if (in_live.Contains(lhs)) { in_live.Remove(lhs); }
                        in_live = in_live.Union(getNestedVars((c as AssignCmd).Rhss[0])).ToList();
                    }
                    else if (c is AssertCmd || c is AssumeCmd)
                    {
                        Expr pred = (c is AssertCmd) ? (c as AssertCmd).Expr : (c as AssumeCmd).Expr;
                        in_live = in_live.Union(getNestedVars(pred)).ToList();
                    }
                    else if (c is HavocCmd)
                    {
                        //havoc is essentially an assignment whose RHS doesnt reference any variables
                        foreach (IdentifierExpr e in (c as HavocCmd).Vars)
                        {
                            Variable v = in_live.Find(x => x.Name.Equals(e.Name));
                            in_live.Remove(v);
                        }
                    }
                    else if (c is CallCmd)
                    {
                        //Windows calling convention uses RCX,RDX,R8,R9, and mem for passing inputs
                        in_live = Options.splitMemoryModel ?
                            in_live.Union(new List<Variable>() { this.RCX, this.RDX, this.R8, this.R9, this.mem, this.mem_bitmap, this.mem_stack }).ToList() :
                            in_live.Union(new List<Variable>() { this.RCX, this.RDX, this.R8, this.R9, this.mem }).ToList();

                    }

                    return in_live;
                };

                Func<List<Variable>, Block, List<Variable>> transformBlock =
                    delegate(List<Variable> out_live, Block block)
                {
                    List<Variable> in_live = new List<Variable>();
                    foreach (Variable v in out_live) { in_live.Add(v); }
                    List<Cmd> cmds = new List<Cmd>(block.Cmds);
                    cmds.Reverse(); //process in the oposite direction
                    foreach (Cmd c in cmds)
                    {
                        in_live = transformStmt(in_live, c);
                    }
                    return in_live;
                };

                Func<List<Variable>, Block, Dictionary<Cmd, List<Variable>>> transformCmdSeq =
                    delegate(List<Variable> out_live, Block block)
                {
                    Dictionary<Cmd, List<Variable>> dict = new Dictionary<Cmd, List<Variable>>();
                    List<Variable> in_live = new List<Variable>();
                    foreach (Variable v in out_live) { in_live.Add(v); }
                    List<Cmd> cmds = new List<Cmd>(block.Cmds);
                    cmds.Reverse(); //process in the oposite direction
                    foreach (Cmd c in cmds)
                    {
                        List<Variable> in_live_tmp = new List<Variable>(in_live);
                        dict.Add(c, in_live_tmp);

                        in_live = transformStmt(in_live, c);
                    }
                    return dict;
                };

                Dictionary<Block, List<Variable>> live = new Dictionary<Block, List<Variable>>();
                Dictionary<Block, HashSet<Block>> successors = buildSuccessorRelation(impl);

                //empty live variable sets to start with: for i = 1 to n do live[i] := {}
                foreach (Block b in impl.Blocks) { live.Add(b, new List<Variable>()); }
                //return nodes should have all state variables
                List<Variable> allVars = Options.splitMemoryModel ?
                    new List<Variable>() { R8, R9, RAX, RCX, RDX, R10, R11, RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15, mem, mem_bitmap, mem_stack } :
                    new List<Variable>() { R8, R9, RAX, RCX, RDX, R10, R11, RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15, mem };

                //first compute live vars at the block granularity (for efficiency)
                bool live_changes = true;
                while (live_changes) //while (live[] changes) do
                {
                    live_changes = false;
                    foreach (Block b in impl.Blocks) //for i = 1 to n do
                    {
                        //live[i] = ( (\union_{s \in succ(i)}{live(s)}) \ def(i)) U ref(i)
                        List<Variable> union_successors;
                        if (successors[b].Count > 0)
                        {
                            union_successors = successors[b].Aggregate(
                                new List<Variable>(), (acc, succ) => acc.Union(live[succ]).ToList());
                        }
                        else
                        {
                            union_successors = new List<Variable>(); union_successors.AddRange(allVars);
                        }
                        List<Variable> new_live = transformBlock(union_successors, b);
                        if (! new HashSet<Variable>(new_live).SetEquals(live[b]))
                        {
                            live[b] = new_live;
                            live_changes = true;
                        }
                    }
                }

                //now that we have a fixed point, compute live vars for each cmd within a block
                Dictionary<Block, Dictionary<Cmd, List<Variable>>> result = 
                    new Dictionary<Block, Dictionary<Cmd, List<Variable>>>();
                foreach (Block b in impl.Blocks)
                {
                    List<Variable> union_successors;
                    if (successors[b].Count > 0)
                    {
                        union_successors = successors[b].Aggregate(
                            new List<Variable>(), (acc, succ) => acc.Union(live[succ]).ToList());
                    }
                    else
                    {
                        union_successors = new List<Variable>(); union_successors.AddRange(allVars);
                    }

                    result.Add(b, transformCmdSeq(union_successors, b));
                }

                return result;
            }

        }

        public class DeadCodeEliminator : StandardVisitor
        {
            private Dictionary<Block, HashSet<Block>> successors;
            private Dictionary<Block, Dictionary<Cmd, List<Variable>>> live;
            private Block current_block;
            private Program prog;
            private LiveVariableAnalyzer liveVarAnalyzer;

            public override Program VisitProgram(Program node)
            {
                this.prog = node;
                this.liveVarAnalyzer = new LiveVariableAnalyzer(this.prog);
                return base.VisitProgram(node);
            }

            public override Implementation VisitImplementation(Implementation impl)
            {
                this.successors = LiveVariableAnalyzer.buildSuccessorRelation(impl);
                this.live = this.liveVarAnalyzer.getLiveVariables(impl);
                return base.VisitImplementation(impl);
            }

            public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
            {
                List<Cmd> newCmdSeq = new List<Cmd>();

                foreach (Cmd c in cmdSeq)
                {
                    if (c is AssignCmd)
                    {
                        Variable lhs = (c as AssignCmd).Lhss[0].DeepAssignedVariable;
                        List<string> mainVars = new List<string>() //only assignments to these variables can be eliminated
                                                {"R8", "R9", "RAX", "RCX", "RDX", "R10", 
                                                 "R11", "RBX", "RBP", "RDI", "RSI", "RSP", 
                                                 "R12", "R13", "R14", "R15", "mem", "mem_stack", "mem_bitmap",
                                                 "AF", "CF", "OF", "PF", "SF", "ZF"};
                        if (this.live[this.current_block][c].Contains(lhs) ||
                            !mainVars.Contains(lhs.Name)) //include all the assignments to target variables
                        {
                            newCmdSeq.Add(c);
                        }
                        else
                        {
                            //only assignments to these variables do I really expect to be elimiated :)
                            List<string> flagVars = new List<string>() { "AF", "CF", "OF", "PF", "SF", "ZF" };
                            //this is where assignments come to die, and my intuition is that only flags get eliminated
                            //Utils.Assert(flagVars.Contains(lhs.Name), "Deadcode elimination eliminated " + c + " at " + this.current_block.Label);
                        }
                    }
                    else
                    {
                        newCmdSeq.Add(c);
                    }
                }
                return base.VisitCmdSeq(newCmdSeq);
            }

            public override Block VisitBlock(Block node)
            {
                this.current_block = node;
                return base.VisitBlock(node);
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

                this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
                Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
                this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
                Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");

                this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
                Utils.Assert(this.mem != null, "Could not find mem variable");

                this.mem_stack = MkGlobalVar("mem_stack", this.mem.TypedIdent.Type);
                node.AddTopLevelDeclaration(this.mem_stack); //add as global variable
                this.mem_bitmap = MkGlobalVar("mem_bitmap", this.mem.TypedIdent.Type);
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
                    if (! getNestedFunctions(t.Item3.Expr).Any(x => x.FunctionName.Equals(region_id))) { continue; }
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

            private bool isMemAddress(string label, Cmd c, Dictionary<Tuple<string, Cmd, AssertCmd>, bool> db)
            {
                return isRegionAddress(label, c, "GE_64", db);
            }

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
                if (! (getNestedFunctions(e).Any(x => x.FunctionName.Contains("LOAD_LE")))) { return e; }

                //we have one or more load expressions here. so let's recursively find them and substitute.
                if (e is NAryExpr)
                {
                    //this is a load expression
                    if ((e as NAryExpr).Fun.FunctionName.Contains("LOAD_LE"))
                    {
                        Tuple<Variable,Expr> load_args = getLoadArgs(e);
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

                        switch (getSlashVerifyCmdType(ac))
                        {
                            case SlashVerifyCmdType.Store8:
                            case SlashVerifyCmdType.Store16:
                            case SlashVerifyCmdType.Store32:
                            case SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                                {
                                    Tuple<Variable, Expr, Expr> storeArgs = getStoreArgs(ac);
                                    Expr store_addr = storeArgs.Item2;
                                    Expr store_value = storeArgs.Item3;

                                    AddrType addrType = AddrType.Unknown;
                                    if (Options.optimizeStoreITE)
                                    {
                                        if (isStackAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.StackAddress; }
                                        else if (isBitmapAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.BitmapAddress; }
                                        else if (isMemAddress(this.current_label, c, this.storeAddressRegionDB)) { addrType = AddrType.MemAddress; }
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
                                        if (addrType == AddrType.Unknown) { newCmdSeq.Add(bitmap_ac); } //if going to mem, then no need to update bitmaps
                                    }

                                    break;
                                }

                            case SlashVerifyCmdType.RepStosB:
                                {
                                    Tuple<Variable, Expr, Expr, Expr> repstosArgs = getRepStosbArgs(ac);
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

        public class SpecialInstructionLifter : StandardVisitor
        {
            private Function rep_stosb;
            private Function not_1;
            private Function plus_64;
            private Function policy;

            private GlobalVariable mem;
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


            public override Program VisitProgram(Program node)
            {
                this.plus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("PLUS_64"));
                Utils.Assert(this.plus_64 != null, "Could not find PLUS_64(.,.) function");
                this.not_1 = node.Functions.FirstOrDefault(f => f.Name.Equals("NOT_1"));
                Utils.Assert(this.not_1 != null, "Could not find NOT_1(.,.) function");
                this.rep_stosb = node.Functions.FirstOrDefault(f => f.Name.Equals("REP_STOSB"));
                Utils.Assert(this.rep_stosb != null, "Could not find REP_STOSB(.,.,.) function");
                this.policy = node.Functions.FirstOrDefault(f => f.Name.Equals("policy"));
                Utils.Assert(this.policy != null, "Could not find policy(.,.,.) function");

                this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
                Utils.Assert(this.mem != null, "Could not find mem variable");

                //this has been moved to Bap2Boogie, but let's just have it here as well
                foreach (String name in new List<String>()
                    { "R8","R9","R10","R11","R12","R13","R14","R15","RAX","RBX","RCX","RDX","RBP","RDI","RSI","RSP" })
                {
                    GlobalVariable gv = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals(name));
                    if (gv == null) //not found, so let's add it in ourself
                    {
                        node.AddTopLevelDeclaration(new GlobalVariable(Token.NoToken, 
                            new TypedIdent(Token.NoToken, name, BType.GetBvType(64))));
                    }
                }

                foreach (String name in new List<String>() 
                    { "AF", "CF", "OF", "PF", "SF", "ZF" })
                {
                    GlobalVariable gv = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals(name));
                    if (gv == null) //not found, so let's add it in ourself
                    {
                        node.AddTopLevelDeclaration(new GlobalVariable(Token.NoToken,
                            new TypedIdent(Token.NoToken, name, BType.GetBvType(1))));
                    }
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

                foreach (String s in new HashSet<String>() { Options.funcMemcmp, Options.funcMemcpy, Options.funcMemset, Options.funcSGXFree, Options.funcSGXMalloc })
                {
                    int location = Int32.Parse(s.ToUpper(), System.Globalization.NumberStyles.HexNumber);
                    node.AddTopLevelDeclaration(new Axiom(Token.NoToken,
                        new NAryExpr(Token.NoToken, new FunctionCall(this.policy),
                            new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(location), 64) })));
                }

                return base.VisitProgram(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                foreach (GlobalVariable v in new List<GlobalVariable>()
                { this.mem, this.RSP, this.RAX, this.RDI, this.RDX,
                  this.R8, this.R9, this.R10, this.R11, this.RCX, this.CF })
                {
                    if (!node.Proc.Modifies.Contains(new IdentifierExpr(Token.NoToken, v)))
                    {
                        node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, v));
                    }
                }

                return base.VisitImplementation(node);
            }

            public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
            {
                List<Cmd> newCmdSeq = new List<Cmd>();

                foreach (Cmd c in cmdSeq)
                {
                    //Do special stuff for those whose BAP modeling is broken
                    if (c is AssertCmd) //call and return instructions are marked with attributes
                    {
                        AssertCmd ac = c as AssertCmd;

                        string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                        if (attribute_cmdtype != null && attribute_cmdtype.Equals("btc_rax_1d"))
                        {
                            //BAP has a bug with this. Model it explicitly ourselves.

                            //CF := RAX[30:29];
                            newCmdSeq.Add(new AssignCmd(Token.NoToken,
                              new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.CF)) },
                              new List<Expr>() { new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 30, 29) }
                            ));
                            //RAX := RAX[64:30] ++ NOT(RAX[30:29]) ++ RAX[29:0];
                            Expr e1 = new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 64, 30);
                            Expr e2 = new NAryExpr(Token.NoToken, new FunctionCall(this.not_1),
                              new List<Expr>() { new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 30, 29) });
                            Expr e3 = new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 29, 0);
                            newCmdSeq.Add(new AssignCmd(Token.NoToken,
                              new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX)) },
                              new List<Expr>() { new BvConcatExpr(Token.NoToken, new BvConcatExpr(Token.NoToken, e1, e2), e3) }
                            ));
                        }
                        else if (attribute_cmdtype != null && attribute_cmdtype.Equals("rep_stosb"))
                        {
                            //BAP does not model this either. Model rep stosb as sequence: mem := repstosb(mem, rcx, rdi, al); rdi := rdi + rcx; rcx := 0;

                            //forall i. rdi <= i < rdi + rcx ==> new_mem[i] == al;
                            newCmdSeq.Add(new AssignCmd(Token.NoToken,
                              new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem)) },
                              new List<Expr>() { 
                                  new NAryExpr(Token.NoToken, new FunctionCall(rep_stosb), new List<Expr>() {
                                    new IdentifierExpr(Token.NoToken, this.mem), 
                                    new IdentifierExpr(Token.NoToken, this.RCX), 
                                    new IdentifierExpr(Token.NoToken, this.RDI), 
                                    new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 8, 0) 
                                  })
                                }
                              ));

                            //RDI := RDI + RCX;
                            newCmdSeq.Add(new AssignCmd(Token.NoToken, new List<AssignLhs>() { 
                                new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RDI)) },
                                new List<Expr>() {  
                                    new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64), new List<Expr>() 
                                    { new IdentifierExpr(Token.NoToken, this.RDI), new IdentifierExpr(Token.NoToken, this.RCX) } )
                                }
                            ));

                            //RCX := 0;
                            newCmdSeq.Add(new AssignCmd(Token.NoToken, new List<AssignLhs>() { 
                                new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RCX)) },
                                new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.ZERO, 64) }));
                        }

                    }


                    //The assert gets placed prior to the original command
                    newCmdSeq.Add(c);
                }

                return base.VisitCmdSeq(newCmdSeq);
            }
        }

        public class ModularVerificationSetup : StandardVisitor
        {
            public override Program VisitProgram(Program node)
            {
                (new Utils.ProcedureCallCleaner()).Visit(node);
                (new Utils.ProcedureCallModeler()).Visit(node);
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
                StackSizeEstimator estimator = new Utils.StackSizeEstimator();
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
                            GlobalVariable new_mem = MkGlobalVar("fresh_" + this.mem_var_count.ToString(), this.mem.TypedIdent.Type);
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
                                      new List<Expr>() {  new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RSP)), new LiteralExpr(Token.NoToken, BigNum.FromInt(addr_offset), 64) });
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

            StackSizeEstimator estimator = new Utils.StackSizeEstimator();
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

            return new Tuple<Tuple<int,int>,Tuple<int,int>,Tuple<int,int>,Tuple<int,int>>
              (new Tuple<int,int>(vspace_low, vspace_high), 
               new Tuple<int,int>(bitmap_low, bitmap_high), 
               new Tuple<int,int>(stack_low, stack_high), 
               new Tuple<int,int>(RSP_lowerbound, RSP_upperbound));
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
            StackSizeEstimator estimator = new Utils.StackSizeEstimator();
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

        public class VCSplitter : StandardVisitor
        {
          private static VCSplitter instance;
          private static List<Tuple<string, Cmd, AssertCmd>> assertions;
          private static Implementation original_impl;

          private string current_label; //ugly hack of using global
          private string target_label; //ugly hack of using global
          private Cmd target_typedCmd;
          private AssertCmd target_assertion;
          private bool target_acquired;

          private VCSplitter() { }

          public static void LaunchVCSplitter(Implementation impl)
          {
              instance = new VCSplitter();
              assertions = new List<Tuple<string, Cmd, AssertCmd>>();
              original_impl = new Duplicator().VisitImplementation(impl);
          }

          public static VCSplitter Instance
          {
              get
              {
                  Utils.Assert(instance != null, "Must invoke launchService before getting instance");
                  return instance;
              }
          }

          public override Block VisitBlock(Block node)
          {
              this.current_label = node.Label;
              return base.VisitBlock(node);
          }

          public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
          {
              List<Cmd> newCmdSeq = new List<Cmd>();
              foreach (Cmd c in cmdSeq)
              {
                  if (this.current_label == this.target_label && EquivalentCmd(c, this.target_typedCmd))
                  {
                      newCmdSeq.Add(this.target_assertion);
                      this.target_acquired = true;
                  }
                  newCmdSeq.Add(c);
              }
              return base.VisitCmdSeq(newCmdSeq);
          }

          //precondition: each block contains at most one assert with SlashVerifyCommandType attribute, 
          //              which is true since we use a block for each instruction
          private bool EquivalentCmd(Cmd c1, Cmd c2)
          {
              //Note: The assumption here is that we only instrument assignments and attributed-asserts in the original sourcefile
              if (c1.GetType() != c2.GetType()) { return false; }
              if (c1 is AssignCmd && c2 is AssignCmd)
              {
                  AssignCmd c1_assignment = c1 as AssignCmd;
                  AssignCmd c2_assignment = c2 as AssignCmd;
                  //ASSUME: only 1 assignment to a variable in a block
                  return ((c1_assignment.Lhss[0].DeepAssignedVariable == c2_assignment.Lhss[0].DeepAssignedVariable) &&
                      (c1_assignment.Rhss[0].ToString() == c2_assignment.Rhss[0].ToString())); //TODO: need better equality here
              }
              else if (c1 is AssertCmd && c2 is AssertCmd)
              {
                  AssertCmd c1_assertion = c1 as AssertCmd;
                  AssertCmd c2_assertion = c2 as AssertCmd;
                  string c1_attribute = QKeyValue.FindStringAttribute(c1_assertion.Attributes, "SlashVerifyCommandType");
                  string c2_attribute = QKeyValue.FindStringAttribute(c2_assertion.Attributes, "SlashVerifyCommandType");
                  return (c1_attribute != null && c2_attribute != null && c1_attribute.Equals(c2_attribute));
              }
              return false;
          }

          public void RecordAssertion(string label, Cmd typedCmd, AssertCmd assertion)
          {
              if (!Options.splitFiles) { return; }
              assertions.Add(new Tuple<string,Cmd,AssertCmd>(label,typedCmd,assertion));
          }

          public int getCurrentAssertionCount() 
          { 
              return assertions.Count(); 
          }

          public Implementation instrumentAssertion(Implementation impl, string label, Cmd typedCmd, AssertCmd assertion)
          {
              Implementation new_impl = new Duplicator().VisitImplementation(impl);
              this.target_label = label;
              this.target_typedCmd = typedCmd;
              this.target_assertion = assertion;
              this.target_acquired = false;
              this.Visit(new_impl); //this step performs the instrumentation
              Utils.Assert(target_acquired, "Unable to instrument assertion: " + assertion.ToString() + " at label " + label);
              return new_impl;
          }

          private static bool ExecuteBoogieBinary(string arguments)
          {
              var delim = Options.IsLinux() ? @"/" : @"\";
              string binaryName = @"." + delim + "references" + delim + "Boogie.exe";
              //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
              Func<string, bool> result = delegate(string s)
              {
                  if (s.Contains("Boogie program verifier finished with 1 verified, 0 errors")) { return true; }
                  else { return false; }
              };

              //Console.WriteLine("\tSTART Executing {0} {1}", binaryName, arguments);
              try
              {
                  ProcessStartInfo procInfo = new ProcessStartInfo();
                  procInfo.UseShellExecute = false;
                  procInfo.FileName = binaryName;
                  procInfo.Arguments = arguments;
                  procInfo.WindowStyle = ProcessWindowStyle.Hidden;
                  procInfo.RedirectStandardOutput = true;
                  Process proc = new Process();
                  proc.StartInfo = procInfo;
                  proc.EnableRaisingEvents = false;
                  Stopwatch sw = Stopwatch.StartNew();
                  proc.Start();
                  string output = "";
                  output = proc.StandardOutput.ReadToEnd();
                  proc.WaitForExit();
                  //Console.WriteLine("\tEND Executing {0} {1}", binaryName, arguments);
                  return result(output);
              }
              catch (Exception e)
              {
                  //Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
                  return false;
              }
          }

          Dictionary<int,bool> shared_result_struct;
          public Dictionary<Tuple<string, Cmd, AssertCmd>, bool> VerifyInstrumentedProcedures(Program prog)
          {
              Dictionary<Tuple<string, Cmd, AssertCmd>, int> intermediate = new Dictionary<Tuple<string, Cmd, AssertCmd>, int>();
              Dictionary<Tuple<string, Cmd, AssertCmd>, bool> result = new Dictionary<Tuple<string, Cmd, AssertCmd>, bool>();
              int numAssertions = 0;
              foreach (Tuple<string, Cmd, AssertCmd> assertion in assertions)
              {
                  var filename = Options.outputPath + @"/" + Options.splitFilesDir + @"/intermediate_" + numAssertions.ToString() + ".bpl";
                  var tuo = new TokenTextWriter(filename);
                  try
                  {
                      //emit all the vars, consts, functions, axioms, and typedecls
                      foreach (Declaration d in prog.TopLevelDeclarations)
                      {
                          if (!(d is Implementation))
                          {
                              d.Emit(tuo, 0);
                          }
                      }
                      //emit the instrumented implementation
                      Implementation new_impl = instrumentAssertion(original_impl, assertion.Item1, assertion.Item2, assertion.Item3);
                      new_impl.Emit(tuo, 0);
                  }
                  finally
                  {
                      tuo.Close();
                  }
                  //prove it using Boogie
                  intermediate[assertion] = numAssertions;
                  numAssertions++;
              }

              shared_result_struct = new Dictionary<int, bool>();
              Parallel.For(0, numAssertions, new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount }, i => CheckAssertion(i));
              foreach (Tuple<string, Cmd, AssertCmd> assertion in assertions)
              {
                  result[assertion] = shared_result_struct[intermediate[assertion]];
              }
              return result;
          }

          private void CheckAssertion(int i)
          {
              string args = Options.outputPath + @"/" + Options.splitFilesDir + @"/intermediate_" + i.ToString() + ".bpl /timeLimit:300 /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0";
              bool boogie_result = ExecuteBoogieBinary(args);
              shared_result_struct.Add(i, boogie_result);
          }

          public void PrintInstrumentedProcedures(Program prog)
          {
              if (!Options.splitFiles) { return; }

              int impl_counter = 0;
              foreach (Tuple<string, Cmd, AssertCmd> assertion in assertions)
              {
                  string tag = Options.tag != "" ? @"." + Options.tag : "";
                  var filename = Options.outputPath + @"/" + Options.splitFilesDir + @"/split_" + impl_counter.ToString() + tag + @".bpl";
                  var tuo = new TokenTextWriter(filename);
                  try
                  {
                      //emit all the vars, consts, functions, axioms, and typedecls
                      foreach (Declaration d in prog.TopLevelDeclarations)
                      {
                          if (!(d is Implementation))
                          {
                              d.Emit(tuo, 0);
                          }
                      }
                      //emit the instrumented implementation
                      Implementation new_impl = instrumentAssertion(original_impl, assertion.Item1, assertion.Item2, assertion.Item3);
                      new_impl.Emit(tuo, 0);
                  }
                  finally
                  {
                      tuo.Close();
                  }
                  impl_counter++;
              }
              Console.WriteLine("VCSplitter generated {0} assertions", assertions.Count);
          }

        }

        #region Adding candidate Loop invariant
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

        public class LoopInvariantInstrumenter : StandardVisitor
        {
            private GlobalVariable mem;
            private GlobalVariable mem_stack;
            private GlobalVariable mem_bitmap;
            private Function addrInBitmap;
            private Constant _guard_writeTable_ptr;
            private Constant _bitmap_low;
            private Function load_64;
            private GlobalVariable mem_oldbitmap;
            private String memCheckpointLabel;
            private List<String> loopHeaderLabels;
            private String currentLabel;
            private Queue<Constant> existentials;

            public LoopInvariantInstrumenter(String memCheckpointLabel, List<String> loopHeaderLabels)
            {
                this.memCheckpointLabel = memCheckpointLabel;
                this.loopHeaderLabels = loopHeaderLabels;
            }

            public override Program VisitProgram(Program node)
            {
                //find a mem variable and add mem_oldbitmap of the same type as mem
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
                this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
                Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
                this.load_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LOAD_LE_64"));
                Utils.Assert(this.load_64 != null, "Could not find LOAD_LE_64(.,.) function");
                this._bitmap_low = node.Constants.FirstOrDefault(c => c.Name.Equals("_bitmap_low"));
                Utils.Assert(this._bitmap_low != null, "Could not find _bitmap_low constant");
                this._guard_writeTable_ptr = node.Constants.FirstOrDefault(c => c.Name.Equals("_guard_writeTable_ptr"));
                Utils.Assert(this._guard_writeTable_ptr != null, "Could not find _guard_writeTable_ptr constant");

                this.mem_oldbitmap = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "mem_oldbitmap", this.mem.TypedIdent.Type));
                node.AddTopLevelDeclaration(this.mem_oldbitmap);

                existentials = new Queue<Constant>();
                for (int i = 0; i < 2 * loopHeaderLabels.Count; i++)
                {
                    Constant existential = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "existential_b" + i.ToString(), BType.Bool));
                    existential.AddAttribute("existential");
                    node.AddTopLevelDeclaration(existential);
                    this.existentials.Enqueue(existential);
                }

                return base.VisitProgram(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_oldbitmap));
                return base.VisitImplementation(node);
            }

            public override Block VisitBlock(Block node)
            {
                this.currentLabel = node.Label;
                return base.VisitBlock(node);
            }

            public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
            {
                List<Cmd> newCmdSeq = new List<Cmd>();
                if (this.currentLabel == this.memCheckpointLabel)
                {
                    //mem_oldbitmap := mem
                    AssignCmd ac = new AssignCmd(Token.NoToken, new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_oldbitmap)) },
                                                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap) });
                    newCmdSeq.Add(ac);
                }
                else if (this.loopHeaderLabels.Contains(this.currentLabel))
                {
                    //assert (forall i: bv64 :: addrInBitmap(i) ==> mem[i] == mem_oldbitmap[i]);
                    BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                    Expr in_bitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });

                    Expr assert_expr;
                    Expr mem_bitmap_of_i = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                        new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), 
                                       new IdentifierExpr(Token.NoToken, i) });
                    Expr mem_oldbitmap_of_i = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                        new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_oldbitmap), 
                                       new IdentifierExpr(Token.NoToken, i) });
                    assert_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(in_bitmap, Expr.Eq(mem_bitmap_of_i, mem_oldbitmap_of_i)));
                    //for Houdini
                    Constant existential = this.existentials.Dequeue();
                    assert_expr = Expr.Imp(new IdentifierExpr(Token.NoToken, existential), assert_expr);
                    newCmdSeq.Add(new AssertCmd(Token.NoToken, assert_expr));

                    //assert (LOAD_LE_64(mem, _guard_writeTable_ptr) == _bitmap_low);
                    Expr load_mem_guardptr = new NAryExpr(Token.NoToken, new FunctionCall(this.load_64), new List<Expr>() { 
                        new IdentifierExpr(Token.NoToken, this.mem), 
                        new IdentifierExpr(Token.NoToken, this._guard_writeTable_ptr) });
                    assert_expr = Expr.Eq(load_mem_guardptr, new IdentifierExpr(Token.NoToken, _bitmap_low));
                    //for Houdini
                    existential = this.existentials.Dequeue(); 
                    assert_expr = Expr.Imp(new IdentifierExpr(Token.NoToken, existential), assert_expr);
                    newCmdSeq.Add(new AssertCmd(Token.NoToken, assert_expr));
                }
                newCmdSeq.AddRange(cmdSeq);
                return base.VisitCmdSeq(newCmdSeq);
            }

        }
        #endregion

        public class LoadAddressDecider : StandardVisitor
        {
            private Function addrInBitmap;
            private Function addrInStack;
            private GlobalVariable mem;

            private string current_label;

            public override Program VisitProgram(Program node)
            {
                this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
                Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
                this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
                Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");

                this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
                Utils.Assert(this.mem != null, "Could not find mem variable");

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
                if (!(getNestedFunctions(e).Any(x => x.FunctionName.Contains("LOAD_LE")))) { return new List<Expr>(); }

                //we have one or more load expressions here. so let's recursively find them and substitute.
                if (e is NAryExpr)
                {
                    //this is a load expression
                    if ((e as NAryExpr).Fun.FunctionName.Contains("LOAD_LE"))
                    {
                        Tuple<Variable, Expr> load_args = getLoadArgs(e);
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
                            Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                            assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { load_addr }));
                            newCmdSeq.Add(assertion);
                            Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
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
                this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
                Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
                this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
                Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");

                this.lt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LT_64"));
                Utils.Assert(this.lt_64 != null, "Could not find LT_64(.,.) function");
                this.ge_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GE_64"));
                Utils.Assert(this.ge_64 != null, "Could not find GE_64(.,.) function");
                this.stack_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_low"));
                Utils.Assert(this.stack_low != null, "Could not find _stack_low variable");
                this.stack_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_high"));
                Utils.Assert(this.stack_high != null, "Could not find _stack_high variable");
                this.bitmap_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_low"));
                Utils.Assert(this.bitmap_low != null, "Could not find _bitmap_low variable");
                this.bitmap_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_high"));
                Utils.Assert(this.bitmap_high != null, "Could not find _bitmap_high variable");

                this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
                Utils.Assert(this.mem != null, "Could not find mem variable");

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
                        switch (getSlashVerifyCmdType(ac))
                        {
                            case SlashVerifyCmdType.Store8:
                            case SlashVerifyCmdType.Store16:
                            case SlashVerifyCmdType.Store32:
                            case SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                                {
                                    Tuple<Variable, Expr, Expr> storeArgs = getStoreArgs(ac);
                                    Expr store_addr = storeArgs.Item2;
                                    Expr store_value = storeArgs.Item3;

                                    AssertCmd assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap), new List<Expr>() { store_addr }));
                                    newCmdSeq.Add(assertion);
                                    Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                                    assertion = new AssertCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { store_addr }));
                                    newCmdSeq.Add(assertion);
                                    Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                                    Expr addr_in_mem =
                                        Expr.And(
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                            new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                new List<Expr>() { store_addr, new IdentifierExpr(Token.NoToken, this.bitmap_low) }));
                                    assertion = new AssertCmd(Token.NoToken, addr_in_mem);
                                    newCmdSeq.Add(assertion);
                                    Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

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

        #region Instrument with typing assertions
        public class TypeChecker : StandardVisitor
        {
            private Function plus_64, minus_64, lt_64, le_64, ge_64, gt_64;
            private Function writable;
            private Function addrInBitmap;
            private Function addrInStack;
            private Function largestAddrAffected_8;
            private Function smallestAddrAffected_8;
            private Function anyAddrAffected_8;
            private Function rep_stosb;
            private Function policy;

            private Constant stack_low;
            private Constant stack_high;
            private Constant bitmap_low;
            private Constant bitmap_high;

            private GlobalVariable mem;
            private GlobalVariable mem_stack;
            private GlobalVariable mem_bitmap;
            private GlobalVariable RSP;
            private GlobalVariable RAX;
            private GlobalVariable RDI;
            private GlobalVariable RCX;
            private GlobalVariable CF;

            private string current_label;
            private bool bound_stacksize_option = false; //true if applying trick
            private int bound_stacksize_offset = -1;

            private List<GlobalVariable> globals = new List<GlobalVariable>();

            public override Program VisitProgram(Program node)
            {
              this.globals.AddRange(node.GlobalVariables);

              this.plus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("PLUS_64"));
              Utils.Assert(this.plus_64 != null, "Could not find PLUS_64(.,.) function");
              this.minus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("MINUS_64"));
              Utils.Assert(this.minus_64 != null, "Could not find MINUS_64(.,.) function");
              this.lt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LT_64"));
              Utils.Assert(this.lt_64 != null, "Could not find LT_64(.,.) function");
              this.le_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LE_64"));
              Utils.Assert(this.le_64 != null, "Could not find LE_64(.,.) function");
              this.ge_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GE_64"));
              Utils.Assert(this.ge_64 != null, "Could not find GE_64(.,.) function");
              this.gt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GT_64"));
              Utils.Assert(this.gt_64 != null, "Could not find GT_64(.,.) function");
              this.writable = node.Functions.FirstOrDefault(f => f.Name.Equals("writable"));
              Utils.Assert(this.writable != null, "Could not find writable(.,.) function");
              this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
              Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
              this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
              Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");
              this.largestAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("largestAddrAffected_8"));
              Utils.Assert(this.largestAddrAffected_8 != null, "Could not find largestAddrAffected_8(.,.,.) function");
              this.smallestAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("smallestAddrAffected_8"));
              Utils.Assert(this.smallestAddrAffected_8 != null, "Could not find smallestAddrAffected_8(.,.,.) function");
              this.anyAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("anyAddrAffected_8"));
              Utils.Assert(this.anyAddrAffected_8 != null, "Could not find anyAddrAffected_8(.,.,.) function");
              this.rep_stosb = node.Functions.FirstOrDefault(f => f.Name.Equals("REP_STOSB"));
              Utils.Assert(this.rep_stosb != null, "Could not find REP_STOSB(.,.,.) function");
              this.policy = node.Functions.FirstOrDefault(f => f.Name.Equals("policy"));
              Utils.Assert(this.policy != null, "Could not find policy(.,.,.) function");

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
              this.RAX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RAX"));
              Utils.Assert(this.RAX != null, "Could not find RAX variable");
              this.RDI = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDI"));
              Utils.Assert(this.RDI != null, "Could not find RDI variable");
              this.RCX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RCX"));
              Utils.Assert(this.RCX != null, "Could not find RCX variable");
              this.CF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("CF"));
              Utils.Assert(this.CF != null, "Could not find CF variable");

              this.stack_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_low"));
              Utils.Assert(this.stack_low != null, "Could not find _stack_low variable");
              this.stack_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_high"));
              Utils.Assert(this.stack_high != null, "Could not find _stack_high variable");
              this.bitmap_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_low"));
              Utils.Assert(this.bitmap_low != null, "Could not find _bitmap_low variable");
              this.bitmap_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_high"));
              Utils.Assert(this.bitmap_high != null, "Could not find _bitmap_high variable");

              return base.VisitProgram(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
              StackSizeEstimator estimator = new Utils.StackSizeEstimator();
              estimator.Visit(node); //necessary before querying the stack size estimate
              int stack_size_estimate = estimator.getStackEstimate(-1);
              if (stack_size_estimate > 0)
              {
                bound_stacksize_option = true;
                bound_stacksize_offset = stack_size_estimate;
              }

              return base.VisitImplementation(node);
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
                        switch (getSlashVerifyCmdType(ac))
                        {
                            case SlashVerifyCmdType.Store8:
                            case SlashVerifyCmdType.Store16:
                            case SlashVerifyCmdType.Store32: 
                            case SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                            {
                              Tuple<Variable, Expr, Expr> storeArgs = getStoreArgs(ac);
                              Expr store_addr = storeArgs.Item2;
                              Expr store_value = storeArgs.Item3;
                              Expr old_RSP = new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP));
                              AssertCmd assertion;

                              Func<int, Expr> OffsetExpr = delegate(int n)
                              {
                                LiteralExpr x = new LiteralExpr(Token.NoToken, BigNum.FromInt(Math.Abs(n)), 64);
                                if (n >= 0) {
                                  return new NAryExpr(Token.NoToken, new FunctionCall(plus_64), new List<Expr>() { storeArgs.Item2, x });
                                } else {
                                  return new NAryExpr(Token.NoToken, new FunctionCall(minus_64), new List<Expr>() { storeArgs.Item2, x });
                                }
                              };

                              //Console.WriteLine("store to {0} at addr {1} with value {2}", storeArgs.Item1, storeArgs.Item2, storeArgs.Item3);
                              int iterations =
                                getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Store8 ? 1 :
                                getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Store16 ? 2 :
                                getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Store32 ? 4 : 8;

                              //instrument assert ((addrInStack(PLUS_64(t_a, 0bv64)) && GE_64(PLUS_64(t_a, 0bv64), old(RSP))) ==> 
                              //    writable(mem,PLUS_64(t_a, 0bv64)) || writable(mem,MINUS_64(t_a, 8bv64))) && (addrInBitmap(PLUS_64(t_a, 0bv64)) ==> 
                              //    LT_64(largestAddrAffected_8(mem, PLUS_64(t_a, 0bv64), t_v[8:0]), old(RSP - 8)));
                              Expr is_checkworthy_store = Expr.False;
                              foreach (int iter in new List<int>() { 0, iterations - 1}.Distinct()) //disjunction over a, a+n-1
                              {
                                Expr addr_in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack),
                                    new List<Expr>() { OffsetExpr(iter) });
                                Expr addr_in_parent_frame = new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                    new List<Expr>() { OffsetExpr(iter), old_RSP });
                                Expr addr_not_in_backing_space = Expr.Not(Expr.And(
                                    new NAryExpr(Token.NoToken, new FunctionCall(ge_64), 
                                        new List<Expr>() { OffsetExpr(iter),
                                                           new NAryExpr(Token.NoToken, 
                                                                new FunctionCall(plus_64), 
                                                                  new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) }) }),
                                    new NAryExpr(Token.NoToken, new FunctionCall(lt_64), 
                                        new List<Expr>() { OffsetExpr(iter),
                                                           new NAryExpr(Token.NoToken, 
                                                                new FunctionCall(plus_64), 
                                                                  new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(40), 64) }) })));
                                is_checkworthy_store = Expr.Or(is_checkworthy_store, Expr.And(addr_in_stack, Expr.And(addr_not_in_backing_space, addr_in_parent_frame)));
                              }
                                //Fix for the padding issue. Enough to check writability of (addr + 0). It's an invariant that /guard:cfw maintains
                              Expr is_writable = new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                  new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(0) });
                              Expr check_for_stack_store = Expr.Imp(is_checkworthy_store, is_writable);
                              assertion = new AssertCmd(Token.NoToken, check_for_stack_store);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                              for (int iter = 0; iter < iterations; iter++)
                              {
                                Expr addr_in_bitmap = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap),
                                    new List<Expr>() { OffsetExpr(iter) });
                                Expr largest_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(largestAddrAffected_8),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                //Expr addr_in_own_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                //    new List<Expr>() { largest_addr_affected, old_RSP }); //Not using this because of padding issue
                                Expr largest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                      new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) });
                                Expr addr_in_own_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                      new List<Expr>() { largest_addr_affected, largest_allowed_address });
                                if (this.bound_stacksize_option)
                                {
                                  Utils.Assert(this.bound_stacksize_offset % 8 == 0, "Need stack size estimate to be a multiple of 8");
                                  Expr smallest_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(smallestAddrAffected_8),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                  Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                      new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) });
                                  addr_in_own_frame = Expr.And(addr_in_own_frame,
                                      new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                        new List<Expr>() { smallest_addr_affected, smallest_allowed_address }));
                                }

                                Expr any_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(anyAddrAffected_8),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                Expr value_not_zero = Expr.Neq(new BvExtractExpr(Token.NoToken, store_value, 8 * (iter + 1), 8 * iter), 
                                                               new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 8));

                                Expr check_for_bitmap_store = Expr.Imp(Expr.And(Expr.And(addr_in_bitmap, any_addr_affected), value_not_zero), addr_in_own_frame);

                                assertion = new AssertCmd(Token.NoToken, check_for_bitmap_store);
                                newCmdSeq.Add(assertion);
                                Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                              }

                              if (Options.confidentiality) 
                              {
                                  Expr addr_in_U = 
                                      Expr.And(
                                        Expr.And(
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                new List<Expr>() { OffsetExpr(0), new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                            new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                new List<Expr>() { OffsetExpr(0), new IdentifierExpr(Token.NoToken, this.bitmap_high) })),
                                        Expr.And(
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                new List<Expr>() { OffsetExpr(iterations - 1), new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                            new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                new List<Expr>() { OffsetExpr(iterations - 1), new IdentifierExpr(Token.NoToken, this.bitmap_high) }))
                                      );

                                  Expr _data_low = new LiteralExpr(Token.NoToken, BigNum.FromInt(Int32.Parse(Options.dataLow.ToUpper(), System.Globalization.NumberStyles.HexNumber)), 64);
                                  Expr _data_high = new LiteralExpr(Token.NoToken, BigNum.FromInt(Int32.Parse(Options.dataHigh.ToUpper(), System.Globalization.NumberStyles.HexNumber)), 64);
                                  Expr addr_in_Data =
                                      Expr.And(
                                        Expr.And(
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                new List<Expr>() { OffsetExpr(0), _data_low }),
                                            new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                new List<Expr>() { OffsetExpr(0), _data_high })),
                                        Expr.And(
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                new List<Expr>() { OffsetExpr(iterations - 1), _data_low }),
                                            new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                new List<Expr>() { OffsetExpr(iterations - 1), _data_high }))
                                      );

                                  assertion = new AssertCmd(Token.NoToken, Expr.Or(addr_in_U, addr_in_Data));
                                  newCmdSeq.Add(assertion);
                                  Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                              }

                              break;
                            }

                            case SlashVerifyCmdType.RepStosB: //x := REP_STOSB(mem, e1, e2, e3)
                            {
                                //TODO: might want to assert that it writes to the bitmap
                                //if its writing zeros to bitmap, we dont need to assert anything
                                break;
                            }

                            default: //x:=e
                            {
                              Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Expected assignments to have 1 lhs and 1 rhs");

                              AssignLhs lhs = ac.Lhss.ElementAt(0);
                              Expr rhs = ac.Rhss.ElementAt(0);

                                // is x rsp?
                              if (lhs.Type.IsBv && lhs.DeepAssignedIdentifier.Name.Equals("RSP"))
                              {
                                Expr alignment = Expr.Eq(new BvExtractExpr(Token.NoToken, rhs, 3, 0), 
                                                       new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));
                                Expr le_old_RSP = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                                    new List<Expr>() { rhs, new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)) });
                                AssertCmd assertion = new AssertCmd(Token.NoToken, Expr.And(alignment, le_old_RSP));
                                newCmdSeq.Add(assertion);
                                Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                              }
                              
                              break;
                            }
                        }
                    }
                    else if (c is AssertCmd) //call and return instructions are marked with attributes
                    {
                      AssertCmd ac = c as AssertCmd;

                      //extract instruction type
                      string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                      string attribute_jmptarget = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpTarget");

                      //return
                      if (attribute_cmdtype != null && attribute_cmdtype.Equals("ret"))
                      {
                          int numAssertsBeforeReturn = Utils.VCSplitter.Instance.getCurrentAssertionCount();
                          //these are the asserts we place on return statement. why not just make them postconditions?
                          //forall i. i < old(rsp) && i[3:0] == 0bv3 ==> ¬writable(mem,i)
                          AssertCmd assertion;
                          if (this.bound_stacksize_option && Options.instantiateQuantifiers) //can only instantiate quantifiers on bounded 
                          {
                              Expr instantiation = Expr.True;
                              int addr_offset = 8;
                              while (addr_offset <= (this.bound_stacksize_offset))
                              {
                                  Expr addr = new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64),
                                    new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                 new LiteralExpr(Token.NoToken, BigNum.FromInt(addr_offset), 64) });
                                  Expr addr_not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), addr }));
                                  //instantiation = Expr.And(instantiation, addr_not_writable);
                                  Expr precondition = 
                                      Expr.And(Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP), 3, 0), new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3)),
                                               Expr.Eq(new IdentifierExpr(Token.NoToken, RSP),  new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                                  assertion = new AssertCmd(Token.NoToken, Expr.Imp(precondition, addr_not_writable));
                                  newCmdSeq.Add(assertion);
                                  Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                                  addr_offset += 8;
                              }
                              int numAssertsAfterReturn = Utils.VCSplitter.Instance.getCurrentAssertionCount();
                              Console.WriteLine("VCSplitter says that ret produced assertions ({0},{1})", numAssertsBeforeReturn, numAssertsAfterReturn - 1);
                              //assertion = new AssertCmd(Token.NoToken, instantiation);
                          }
                          else
                          {
                              BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                              Expr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)) });
                              if (this.bound_stacksize_option)
                              {
                                  Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                              new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                         new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) });
                                  in_local_frame = Expr.And(in_local_frame,
                                    new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                      new List<Expr>() { new IdentifierExpr(Token.NoToken, i), smallest_allowed_address }));
                              }
                              NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                              Expr aligned = Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, i), 3, 0),
                                                             new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));
                              Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                              Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i },
                                Expr.Imp(Expr.And(Expr.And(in_local_frame, in_stack), aligned), not_writable));
                              assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                          }


                          //rsp == old(rsp)
                          assertion = new AssertCmd(Token.NoToken, Expr.Eq(new IdentifierExpr(Token.NoToken, RSP),
                                                                             new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                          newCmdSeq.Add(assertion);
                          Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                      }
                      else if (attribute_cmdtype != null && attribute_cmdtype.Equals("call"))
                      {
                          AssertCmd assertion;

                          string attribute_target = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCallTarget");
                          Utils.Assert(attribute_target != null, "Expected SlashVerifyCallTarget attribute on call");

                          //assert policy(target);
                          Expr is_policy;
                          if (attribute_target.Substring(0, 2).Equals("0x"))
                          {
                              int target = Int32.Parse(attribute_target.ToUpper().Substring(2), System.Globalization.NumberStyles.HexNumber);
                              is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                  new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(target), 64) });
                          }
                          else
                          {
                              GlobalVariable target = this.globals.FirstOrDefault(v => v.Name.Equals(attribute_target));
                              Utils.Assert(target != null, "Could not find " + attribute_target);
                              is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                  new List<Expr>() { new IdentifierExpr(Token.NoToken, target) });
                          }

                          if (!Options.disablePolicyChecking)
                          {
                              assertion = new AssertCmd(Token.NoToken, is_policy);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                          }

                          if (!this.bound_stacksize_option)
                          {
                              //forall i. i < (rsp - 8) ==> ¬writable(mem,i) //rsp - 8 holds return address, and everything below that must start off as non writable
                              BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                              NAryExpr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, i), 
                                             new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                new List<Expr>() { 
                                                  new IdentifierExpr(Token.NoToken, RSP), 
                                                  new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) })});
                              NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                              Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                              Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(Expr.And(in_stack, in_local_frame), not_writable));
                              assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                              //assert !writable(mem, rsp-8)
                              not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                                    new List<Expr>() { 
                                              new IdentifierExpr(Token.NoToken, this.mem_bitmap), 
                                              new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                new List<Expr>() { 
                                                  new IdentifierExpr(Token.NoToken, RSP), 
                                                  new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) })
                                            }));
                              assertion = new AssertCmd(Token.NoToken, not_writable);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                          }
                          else
                          {
                              //assert that RSP is not lower than bound_stacksize_offset. if RSP has not gotten lower, than we know everything is writable below
                              Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                          new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                         new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) }); 

                              NAryExpr rsp_in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), smallest_allowed_address });
                              assertion = new AssertCmd(Token.NoToken, rsp_in_local_frame);
                              newCmdSeq.Add(assertion);
                              Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                          }

                          //assert RSP <= (old(RSP) - 32)
                          NAryExpr stack_backing_space = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), 
                                             new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                 new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                                    new LiteralExpr(Token.NoToken, BigNum.FromInt(32), 64) }) });
                          assertion = new AssertCmd(Token.NoToken, stack_backing_space);
                          newCmdSeq.Add(assertion);
                          Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                      }
                      else if (attribute_cmdtype != null && attribute_jmptarget != null &&
                                (attribute_cmdtype.Equals("remotejmp") || 
                                (attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget.Equals("remote"))))
                      {
                          AssertCmd assertion;

                          //assert policy(target);
                          Expr is_policy;
                          if (attribute_cmdtype.Equals("remotejmp"))
                          {
                              int target = Int32.Parse(attribute_jmptarget.ToUpper().Substring(2), System.Globalization.NumberStyles.HexNumber);
                              is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                  new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(target), 64) });
                          }
                          else if (attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget.Equals("remote"))
                          {
                              string attribute_jmpregister = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpRegister");
                              Utils.Assert(attribute_jmpregister != null, "Exprected jmp register annotation on indirect jump");
                              GlobalVariable global_register = this.globals.FirstOrDefault(x => x.Name.Equals(attribute_jmpregister));
                              Utils.Assert(global_register != null, "Could not find global variable " + attribute_jmpregister);

                              is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                  new List<Expr>() { new IdentifierExpr(Token.NoToken, global_register) });
                          }
                          else
                          {
                              Utils.Assert(false, "Unexpected case");
                              is_policy = Expr.False;
                          }
                          assertion = new AssertCmd(Token.NoToken, is_policy);
                          newCmdSeq.Add(assertion);
                          Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                          assertion = new AssertCmd(Token.NoToken, Expr.Eq(new IdentifierExpr(Token.NoToken, RSP),
                                                                           new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                          newCmdSeq.Add(assertion);
                          Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                          //forall i. i < rsp ==> ¬writable(mem,i)
                          BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                          NAryExpr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new IdentifierExpr(Token.NoToken, RSP) });
                          NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                          Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                            new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                          Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(Expr.And(in_stack, in_local_frame), not_writable));
                          assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                          newCmdSeq.Add(assertion);
                          Utils.VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                      }
                    }

                    //The assert gets placed prior to the original command
                    newCmdSeq.Add(c);
                }
                
                return base.VisitCmdSeq(newCmdSeq);
            }
        }
        #endregion
    }
}
