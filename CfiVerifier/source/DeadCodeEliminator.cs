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

namespace CfiVerifier
{
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
                        in_live = in_live.Union(Utils.getNestedVars((c as AssignCmd).Rhss[0])).ToList();
                    }
                    else if (c is AssertCmd || c is AssumeCmd)
                    {
                        Expr pred = (c is AssertCmd) ? (c as AssertCmd).Expr : (c as AssumeCmd).Expr;
                        in_live = in_live.Union(Utils.getNestedVars(pred)).ToList();
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
                    if (!new HashSet<Variable>(new_live).SetEquals(live[b]))
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
}
