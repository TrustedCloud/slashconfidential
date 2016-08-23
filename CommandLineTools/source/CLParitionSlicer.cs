using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using CfiVerifier;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.GraphUtil;

namespace CommandLineTools
{
    class CLParitionSlicer
    {
        public static void Run(string inputFile, string outputFile)
        {
            Program prog = null;
            Utils.ParseProgram(inputFile, out prog);
            Utils.Assert(prog.Implementations.Count() == 1, "Expecting program with a single implementation.");
            (new PartitionAssumeSlicer()).Visit(prog.Implementations.First());
            using (TokenTextWriter ttw = new TokenTextWriter(outputFile))
            {
                prog.Emit(ttw);
            }
        }
    }
}
