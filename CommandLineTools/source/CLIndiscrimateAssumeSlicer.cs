using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using CfiVerifier;
using Microsoft.Boogie;

namespace CommandLineTools
{
    class CLIndiscrimateAssumeSlicer
    {
        public static void Run(Program input)
        {
			(new CfiVerifier.IndiscriminateAssumeSlicer()).Visit(input);
        }
    }
}
