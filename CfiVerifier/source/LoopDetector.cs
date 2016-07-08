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
            foreach (Block header in cce.NonNull(g.Headers))
            {
                this.loopHeaders.Add(header);
                foreach (Block backEdgeNode in cce.NonNull(g.BackEdgeNodes(header)))
                {
                    foreach (Block b in g.NaturalLoops(header, backEdgeNode))
                    {
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
}
