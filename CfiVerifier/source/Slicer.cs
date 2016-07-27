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
    public class Slicer : StandardVisitor
    {
        private Program prog;
        private Implementation impl;
        private AssertCmd source_assert;
        private Expr return_instrumentation_address = null;
        private List<Function> call_trigger_functions = new List<Function>();
    
        private HashSet<Cmd> keep_set;
        private Dictionary<Cmd, HashSet<Variable>> live_set;
    
        public Slicer(Program prog)
        {
            Utils.Assert(prog.Implementations.Count() == 1, "Expecting a single implementation");
            this.impl = prog.Implementations.ElementAt(0);
            this.prog = prog;
            this.live_set = new Dictionary<Cmd, HashSet<Variable>>();
            this.keep_set = new HashSet<Cmd>();
            foreach (Block b in this.impl.Blocks)
            {
                foreach (Cmd c in b.Cmds)
                {
                    this.live_set.Add(c, new HashSet<Variable>());
                    if (c is AssertCmd)
                    {
                        if (QKeyValue.FindBoolAttribute((c as AssertCmd).Attributes, "source_assert"))
                        {
                            this.source_assert = c as AssertCmd;
                        }
                    }
                    /* This command sets this.return_instrumentation_address if the source_assert is a
                     * return type instrumentation with the corresponding attributes set; commenting
                     * this function ensures that triggers for call instrumentation are not sliced away */
                    IdentifyReturnInstrumentationAddress(c);
                }
            }
            Utils.Assert(this.source_assert != null);
            this.keep_set.Add(this.source_assert);
            this.live_set[this.source_assert] = GetReferencedVars(this.source_assert);

            /* This performs data-flow analysis to remove most of the instructions in the program which do not have
             * information flowing into the source_assert; this generally affects only AssignCmd's*/
            PerformTaintAnalysisAlternate();

            /* This removes unused policy axioms; in almost all cases, this will remove ALL policy axioms. The exception
             * is when the source_assert itself asserts that an address is a policy; in this case, all but the corresponding
             * axiom will be removed */
            SlicePolicyAxioms();
        }
        
        private void PerformTaintAnalysisAlternate()
        {
            bool fixed_point = false;
            ICFG cfg = new ICFG(this.impl);
            while (!fixed_point)
            {
                fixed_point = true;
                foreach (Block b in this.impl.Blocks.AsEnumerable().Reverse())
                {
                    if (!b.Cmds.Any())
                    {
                        continue;
                    }
                    fixed_point &= !PerformCommandAnalysis(b.Cmds);
                    foreach (Cmd pred_cmd in FindPredCmds(b, cfg))
                    {
                        fixed_point &= !PerformCommandAnalysis(new List<Cmd> { pred_cmd, b.Cmds.First() });
                    }
                }
            }
        }
    
        private HashSet<Cmd> FindPredCmds(Block b, ICFG cfg)
        {
            HashSet<Cmd> pred_cmds = new HashSet<Cmd>();
            List<Block> pred_blocks = cfg.predEdges[b].ToList();
            List<Block> visited_blocks = new List<Block> { b };
            Block current_block;
            while (pred_blocks.Any())
            {
                current_block = pred_blocks.First();
                pred_blocks.Remove(current_block);
                if (current_block.Cmds.Any())
                {
                    pred_cmds.Add(current_block.Cmds.Last());
                }
                else
                {
                    pred_blocks.AddRange(cfg.predEdges[current_block].Except(visited_blocks));
                }
                visited_blocks.Add(current_block);
            }
            return pred_cmds;
        }
    
        private bool PerformCommandAnalysis(List<Cmd> cmds)
        {
            int size_before;
            bool keep_before, changed = false;
            Cmd this_cmd, prev_cmd;
            for (int i = cmds.Count - 1; i > 0; i--)
            {
                this_cmd = cmds.ElementAt(i);
                prev_cmd = cmds.ElementAt(i - 1);
                size_before = this.live_set[prev_cmd].Count;
                keep_before = this.keep_set.Contains(prev_cmd);
        
                AssignCmd as_assign_cmd = prev_cmd is AssignCmd ? prev_cmd as AssignCmd : null;
                HashSet<Variable> to_union = new HashSet<Variable>(this.live_set[this_cmd]);
                Variable assign_cmd_lhs_var = null;
                if (as_assign_cmd != null)
                {
                    assign_cmd_lhs_var = GetReferencedVars(as_assign_cmd.Lhss.First().AsExpr).First();
                    to_union.Remove(assign_cmd_lhs_var);
                }
                this.live_set[prev_cmd].UnionWith(to_union);
                if (as_assign_cmd != null) 
                {
                    Utils.Assert(as_assign_cmd.Lhss.Count == 1);
                    Utils.Assert(assign_cmd_lhs_var != null);
                    HashSet<Variable> assign_cmd_rhs_vars = new HashSet<Variable>();
                    foreach (Expr rhs_expr in as_assign_cmd.Rhss) 
                    {
                        assign_cmd_rhs_vars.UnionWith(GetReferencedVars(rhs_expr));
                    }
                    if (this.live_set[this_cmd].Contains(assign_cmd_lhs_var)) 
                    {
                        this.live_set[prev_cmd].UnionWith(assign_cmd_rhs_vars);
                        this.keep_set.Add(prev_cmd);
                    }
                }
                if (prev_cmd is AssumeCmd) 
                {
                    this.live_set[prev_cmd].UnionWith(GetReferencedVars(prev_cmd));
                    this.keep_set.Add(prev_cmd);
                }
                Utils.Assert(this.live_set[prev_cmd].Count >= size_before);
                if (this.live_set[prev_cmd].Count > size_before || this.keep_set.Contains(prev_cmd) != keep_before) {
                    changed = true;
                }
            }
            return changed;
        }
    
        private HashSet<Variable> GetReferencedVars(Cmd c)
        {
            if (c is AssignCmd)
            {
                HashSet<Variable> referenced_vars = new HashSet<Variable>();
                Utils.Assert((c as AssignCmd).Lhss.Count == 1);
                referenced_vars.UnionWith(GetReferencedVars((c as AssignCmd).Lhss.First().AsExpr));
                foreach (Expr rhs in (c as AssignCmd).Rhss)
                {
                referenced_vars.UnionWith(GetReferencedVars(rhs));
                }
                return referenced_vars;
            }
            else if (c is AssertCmd)
            {
                return GetReferencedVars((c as AssertCmd).Expr);
            }
            else if (c is AssumeCmd)
            {
                return GetReferencedVars((c as AssumeCmd).Expr);
            }

            Utils.Assert(false, "Unhandled Cmd type: " + c.GetType().ToString());
            return null;
        }
    
        private HashSet<Variable> GetReferencedVars(Expr e)
        {
            HashSet<Variable> referenced_vars = new HashSet<Variable>();
            if (e is NAryExpr) 
            {
                foreach (Expr sub_e in (e as NAryExpr).Args)
                    referenced_vars.UnionWith(GetReferencedVars(sub_e));
                return referenced_vars;
            }
            else if (e is IdentifierExpr)
            {
                Variable var = (e as IdentifierExpr).Decl;
                referenced_vars.Add(var);
                return referenced_vars;
            }
            else if (e is BvExtractExpr)
            {
                referenced_vars.UnionWith(GetReferencedVars((e as BvExtractExpr).Bitvector));
                return referenced_vars;
            }
            else if (e is BvConcatExpr)
            {
                referenced_vars.UnionWith(GetReferencedVars((e as BvConcatExpr).E0));
                referenced_vars.UnionWith(GetReferencedVars((e as BvConcatExpr).E1));
                return referenced_vars;
            }
            else if (e is ForallExpr)
            {
                referenced_vars.UnionWith(GetReferencedVars((e as ForallExpr).Body));
                (e as ForallExpr).Dummies.ForEach(i => referenced_vars.Remove(i));
                return referenced_vars;
            }
            else if (e is LiteralExpr || e is OldExpr)
            {
                return referenced_vars;
            }
            Utils.Assert(false, "Unhandled Expr type detected: " + e.GetType().ToString());
            return null;
        }

        private void SlicePolicyAxioms()
        {
            LiteralExpr policy_target = null;
            if (this.source_assert.Expr is NAryExpr && ((this.source_assert.Expr) as NAryExpr).Fun.FunctionName == "policy") {
                Utils.Assert(((this.source_assert.Expr) as NAryExpr).Args.Count == 1, "Expecting \"policy\" axiom with a single argument");
                Utils.Assert(((this.source_assert.Expr) as NAryExpr).Args.First() is LiteralExpr, "Expecting \"policy\" axiom with a LiteralExpr argument");
                policy_target = ((this.source_assert.Expr) as NAryExpr).Args.First() as LiteralExpr;
            }

            foreach (Declaration d in this.prog.TopLevelDeclarations.ToList())
            {
                if (d is Axiom && (d as Axiom).Expr is NAryExpr && ((d as Axiom).Expr as NAryExpr).Fun.FunctionName == "policy")
                {
                    if (policy_target != null && policy_target.ToString().Equals(((d as Axiom).Expr as NAryExpr).Args.First().ToString()))
                    {
                        continue;
                    }
                    else
                    {
                        this.prog.RemoveTopLevelDeclaration(d);
                    }
                }
            }
        }

        private void IdentifyReturnInstrumentationAddress(Cmd c)
        {
            if (c is AssertCmd) 
            {
                Expr return_instrumentation_addr = QKeyValue.FindExprAttribute((c as AssertCmd).Attributes, "return_instrumentation");
                if (return_instrumentation_addr != null)
                {
                    Utils.Assert(this.return_instrumentation_address == null);
                    this.return_instrumentation_address = return_instrumentation_addr;
                }
            }
            else if (c is AssumeCmd)
            {
                string trigger_func_name = QKeyValue.FindStringAttribute((c as AssumeCmd).Attributes, "call_func_trigger_declaration");
                if (trigger_func_name != null)
                {
                    this.call_trigger_functions.Add(Utils.FindFunctionInProgram(this.prog, trigger_func_name));
                }
            }
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            List<System.Type> removedCmdTypes = new List<System.Type>() {typeof(AssignCmd)};
            foreach (Cmd c in cmdSeq)
            {
                string fresh_func_name;
                if (this.return_instrumentation_address != null && c is AssumeCmd
                    && (fresh_func_name = QKeyValue.FindStringAttribute((c as AssumeCmd).Attributes, "call_func_trigger_declaration")) != null)
                {
                    Function fresh_func = this.call_trigger_functions.Where(i => i.Name.Equals(fresh_func_name)).First();
                    Utils.Assert(fresh_func != null);
                    newCmdSeq.Add(new AssumeCmd(Token.NoToken, new NAryExpr(Token.NoToken, new FunctionCall(fresh_func), new List<Expr> { this.return_instrumentation_address })));
                }
                else if (!removedCmdTypes.Contains(c.GetType()) || this.keep_set.Contains(c))
                {
                    newCmdSeq.Add(c);
                }
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
