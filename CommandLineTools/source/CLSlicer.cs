using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using CfiVerifier;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.GraphUtil;

namespace CommandLineTools
{
    class CLSlicer
    {
        public static void Run(Program input)
        {
            (new CfiVerifier.Slicer(input)).Visit(input);
            CommandLineOptions.Clo.PruneInfeasibleEdges = true;
            input.Implementations.First().PruneUnreachableBlocks();
        }
    }
}
