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
    public class TaintPreserver : StandardVisitor
    {
        private Program prog;
        private Implementation impl;
        private int count;
    
        private HashSet<Cmd> keep_set;
        private Dictionary<Cmd, HashSet<Variable>> live_set;
    
        public TaintPreserver(Program prog, Tuple<string, Cmd, AssertCmd> assertion_info, int count)
        {
    	Utils.Assert(prog.Implementations.Count() == 1, "Expecting a single implementation");
    	this.impl = prog.Implementations.ElementAt(0);
    	this.prog = prog;
    	this.count = count;
    	this.live_set = new Dictionary<Cmd, HashSet<Variable>>();
    	this.keep_set = new HashSet<Cmd>();
    	AssertCmd source_assert = null;
    	foreach (Block b in this.impl.Blocks)
    	{
    	    foreach (Cmd c in b.Cmds)
    	    {
    		this.live_set.Add(c, new HashSet<Variable>());
    		if (b.Label == assertion_info.Item1 && c is AssertCmd && (c as AssertCmd).Expr.ToString() == assertion_info.Item3.Expr.ToString())
    		    source_assert = c as AssertCmd;
    	    }
    	}
    	Utils.Assert(source_assert != null);
    	this.keep_set.Add(source_assert);
    	this.live_set[source_assert] = GetReferencedVars(source_assert);
    	PerformTaintAnalysisAlternate();
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
    	    this.live_set[prev_cmd].UnionWith(this.live_set[this_cmd]);
    	    if (as_assign_cmd != null) 
    	    {
    		Utils.Assert(as_assign_cmd.Lhss.Count == 1);
    		Variable assign_cmd_lhs_var = GetReferencedVars(as_assign_cmd.Lhss.First().AsExpr).First();
    		HashSet<Variable> assign_cmd_rhs_vars = new HashSet<Variable>();
    		this.live_set[prev_cmd].Remove(assign_cmd_lhs_var);
    		foreach (Expr rhs_expr in as_assign_cmd.Rhss) 
    		{
    		    assign_cmd_rhs_vars.UnionWith(GetReferencedVars(rhs_expr));
    		}
    		if (this.live_set[this_cmd].Contains(assign_cmd_lhs_var)) 
    		{
    		    this.live_set[prev_cmd].UnionWith(assign_cmd_rhs_vars);
    		    this.keep_set.Add(prev_cmd);
    		}
    		if (assign_cmd_rhs_vars.Contains(assign_cmd_lhs_var))
    		{
    		    this.live_set[prev_cmd].Add(assign_cmd_lhs_var);
    		}
    	    }
    	    if (prev_cmd is AssumeCmd) 
    	    {
    		this.live_set[prev_cmd].UnionWith(GetReferencedVars(prev_cmd));
    		this.keep_set.Add(prev_cmd);
    	    }
    	    Utils.Assert(this.live_set[prev_cmd].Count >= size_before);
    	    if (this.live_set[prev_cmd].Count > size_before || this.keep_set.Contains(prev_cmd) != keep_before) {
    		//Console.WriteLine("Changing {0} -- {1}.", this_cmd.ToString(), prev_cmd.ToString());
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
    	return new HashSet<Variable>();
        }
    
        private HashSet<Variable> GetReferencedVars(Expr e)
        {
    	HashSet<Variable> referenced_vars = new HashSet<Variable>();
    	if (e is NAryExpr)
    	    foreach (Expr sub_e in (e as NAryExpr).Args)
    		referenced_vars.UnionWith(GetReferencedVars(sub_e));
    	else if (e is IdentifierExpr)
    	{
    	    Variable var = (e as IdentifierExpr).Decl;
    	    referenced_vars.Add(var);
    	}
    	else if (e is BvExtractExpr)
    	{
    	    referenced_vars.UnionWith(GetReferencedVars((e as BvExtractExpr).Bitvector));
    	}
    	else if (e is BvConcatExpr)
    	{
    	    referenced_vars.UnionWith(GetReferencedVars((e as BvConcatExpr).E0));
    	    referenced_vars.UnionWith(GetReferencedVars((e as BvConcatExpr).E1));
    	}
    	else if (e is ForallExpr)
    	{
    	    referenced_vars.UnionWith(GetReferencedVars((e as ForallExpr).Body));
    	    (e as ForallExpr).Dummies.ForEach(i => referenced_vars.Remove(i));
    	}
    	return referenced_vars;
        }
    
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
    	List<Cmd> newCmdSeq = new List<Cmd>();
    	List<System.Type> removedCmdTypes = new List<System.Type>() {typeof(AssignCmd)};
    	foreach (Cmd c in cmdSeq)
    	{
    	    if (!removedCmdTypes.Contains(c.GetType()) || this.keep_set.Contains(c))
    	    {
    		newCmdSeq.Add(c);
    	    }
    	}
    	return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
