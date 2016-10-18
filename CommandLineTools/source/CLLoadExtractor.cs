using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using CfiVerifier;
using Microsoft.Boogie;

namespace CommandLineTools
{
    class CLLoadExtractor
    {
        public static void Run(Program input)
        {
            (new LoadExtractor()).Visit(input);
        }
    }
}
