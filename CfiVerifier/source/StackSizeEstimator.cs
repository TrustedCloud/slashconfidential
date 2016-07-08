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

        public int getStackEstimate(int default_size)
        {
            Utils.Assert(visit_happened, "StackSizeEstimator: must call visit before querying stack size estimate");
            //sum up all the subtractions
            return this.rsp_subtractions.Count > 0 ? this.rsp_subtractions.Sum() : default_size;
        }
    }
}
