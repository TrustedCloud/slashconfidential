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
        public static void Run(string inputFile, string outputFile)
        {
            Program prog = null;
            Utils.ParseProgram(inputFile, out prog);
            (new CfiVerifier.Slicer(prog)).Visit(prog);
            CommandLineOptions.Clo.PruneInfeasibleEdges = true;
            Utils.Assert(prog.Implementations.Count() == 1, "Expecting a single implementation in the program");
            prog.Implementations.First().PruneUnreachableBlocks();
            using (TokenTextWriter ttw = new TokenTextWriter(outputFile))
            {
                prog.Emit(ttw);
            }
        }
    }
}
