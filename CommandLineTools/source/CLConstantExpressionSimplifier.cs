using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using CfiVerifier;
using Microsoft.Boogie;

namespace CommandLineTools
{
    class CLConstantExpressionSimplifier
    {
        public static void Run(string inputFile, string outputFile)
        {
            Program prog = null;
            Utils.ParseProgram(inputFile, out prog);
            Utils.Assert(prog.Implementations.Count() == 1, "Expecting program with a single implementation.");
            (new CfiVerifier.ConstantExpressionSimplifier()).Visit(prog);
            using (TokenTextWriter ttw = new TokenTextWriter(outputFile))
            {
                prog.Emit(ttw);
            }

        }
    }
}
