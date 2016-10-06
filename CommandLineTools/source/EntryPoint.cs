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
    class EntryPoint
    {
        enum ProgramChoice {
            SLICE,
            SLICE_PARTITIONS,
            GRAPH,
            REMOVE_CODE_BRANCHES,
            SPLIT_MEMORY,
            SPLIT_MEMORY_OPT,
            SIMPLIFY_CONSTANT_EXPRS
        }

        public static void Main(string[] args)
        {
            if (!CfiVerifier.Options.ParseCommandLine(String.Join(" ", args))) return;
            // Arguments: string inputFile, string outputFile
            Program inputProgram;
            Utils.ParseProgram(args[1], out inputProgram);
            Utils.Assert(inputProgram.Implementations.Count() == 1, "Expecting a single implementation in the program");
            string outputName = args[2];
            string outputBasename = Path.GetFileName(args[2]);

            foreach (string choiceString in args[0].Split(',')) {
                ProgramChoice choice = (ProgramChoice)Enum.Parse(typeof(ProgramChoice), choiceString);
                switch (choice)
                {
                  case ProgramChoice.SLICE:
                      CLSlicer.Run(inputProgram);
                      break;
                  case ProgramChoice.GRAPH:
                      CLGraphEmitter.Run(inputProgram, outputBasename.Split('.')[0]);
                      break;
                  case ProgramChoice.REMOVE_CODE_BRANCHES:
                      CLRemoveCodeBranches.Run(inputProgram);
                      break;
                  case ProgramChoice.SPLIT_MEMORY:
                      CLMemorySplitter.Run(inputProgram);
                      break;
                  case ProgramChoice.SLICE_PARTITIONS:
                      CLParitionSlicer.Run(inputProgram);
                      break;
                  case ProgramChoice.SIMPLIFY_CONSTANT_EXPRS:
                      CLConstantExpressionSimplifier.Run(inputProgram);
                      break;
                  default:
                      throw new Exception("Not implemented");
              }
            }
        TokenTextWriter ttw = new TokenTextWriter(outputName);
        inputProgram.Emit(ttw);
        ttw.Close();
        }
    }
}
