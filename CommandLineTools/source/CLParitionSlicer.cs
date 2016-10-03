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
        public static void Run(Program input)
        {
            (new PartitionAssumeSlicer()).Visit(input.Implementations.First());
        }
    }
}
