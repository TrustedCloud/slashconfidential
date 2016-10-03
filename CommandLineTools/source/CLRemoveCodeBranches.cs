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
    class CLRemoveCodeBranches
    {
        public static void Run(Program input)
        {
            CfiVerifier.RemoveCodeBranches.Run(input.Implementations.First());
        }
    }

}
