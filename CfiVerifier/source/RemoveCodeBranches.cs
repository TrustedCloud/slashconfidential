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
using System.Collections.Generic;

namespace CfiVerifier
{
    public class RemoveCodeBranches
    {
        public static readonly string InstrumentationBranch = "InstrumenedBranch";

        public static void MarkInstrumentationBranches(Implementation impl)
        {
            var graph = Program.GraphFromImpl(impl);

            foreach (var blk in impl.Blocks)
            {
                // Find assume false
                if (!blk.Cmds.OfType<AssumeCmd>().Any(ac => (ac.Expr is LiteralExpr) && (ac.Expr as LiteralExpr).IsFalse))
                    continue;
                // Unique pred
                if (graph.Predecessors(blk).Count() != 1)
                    continue;

                var pred1 = graph.Predecessors(blk).First();
                // has assume?
                if (pred1.Cmds.Count != 1 || !(pred1.Cmds[0] is AssumeCmd))
                    continue;

                // Unique pred
                if (graph.Predecessors(pred1).Count() != 1)
                    continue;
                var pred2 = graph.Predecessors(pred1).First();

                // has no cmds
                if (pred2.Cmds.Count != 0)
                    continue;
                // has two successors
                if (!(pred2.TransferCmd is GotoCmd) || (pred2.TransferCmd as GotoCmd).labelTargets.Count != 2)
                    continue;

                var otherblock = (pred2.TransferCmd as GotoCmd).labelTargets.Where(l => l != pred1).First();

                // has single assume
                if (otherblock.Cmds.Count != 1 || !(otherblock.Cmds[0] is AssumeCmd))
                    continue;

                // mark as instrumentation branches
                var ac1 = pred1.Cmds[0] as AssumeCmd;
                var ac2 = otherblock.Cmds[0] as AssumeCmd;

                ac1.Attributes = new QKeyValue(Token.NoToken, InstrumentationBranch, new List<object>(), ac1.Attributes);
                ac2.Attributes = new QKeyValue(Token.NoToken, InstrumentationBranch, new List<object>(), ac2.Attributes);
            }
        }

        public static void Run(Implementation impl)
        {
            MarkInstrumentationBranches(impl);

            foreach (var blk in impl.Blocks)
            {
                foreach (var cmd in blk.Cmds.OfType<AssumeCmd>())
                {
                    if (cmd.Expr is LiteralExpr && (cmd.Expr as LiteralExpr).IsFalse) continue;
                    if (QKeyValue.FindBoolAttribute(cmd.Attributes, InstrumentationBranch)) continue;
                    if (!QKeyValue.FindBoolAttribute(cmd.Attributes, "partition")) continue;
                    cmd.Expr = Expr.True;
                }
            }
        }




    }



}
