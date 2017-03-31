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
    public enum ProgramChoice {
        SLICE,
        SLICE_PARTITIONS,
        GRAPH_DOT,
        GRAPH_DGML,
        REMOVE_CODE_BRANCHES,
        SPLIT_MEMORY,
        SIMPLIFY_CONSTANT_EXPRS,
        EXTRACT_LOADS,
        VERIFY,
        SLICE_ASSUMES,
        ABSTRACT_MEM,
		ABSTRACT_USER_CALL_MEM
    }

    class EntryPoint
    {

        public static void Main(string[] args)
        {
            if (!CfiVerifier.Options.ParseCommandLine(String.Join(" ", args))) return;
            Utils.Assert(args.Length == 3, "Expecting three given arguments (<passes> <inputFile> <outputFile>)!");
            // Arguments: string inputFile, string outputFile
            Program inputProgram;
            Utils.ParseProgram(args[1], out inputProgram);
            Utils.Assert(inputProgram.Implementations.Count() == 1, "Expecting a single implementation in the program");
            string outputName = args[2];
            string outputBasename = Path.GetFileName(args[2]);

            foreach (string choiceString in args[0].Split(',')) {
                ProgramChoice choice;
                if (choiceString.Contains("VERIFY"))
                    choice = ProgramChoice.VERIFY;
                else
                    choice = (ProgramChoice)Enum.Parse(typeof(ProgramChoice), choiceString);
                Console.WriteLine(choiceString);
                switch (choice)
                {
                  case ProgramChoice.SLICE:
                      CLSlicer.Run(inputProgram);
                      break;
                  case ProgramChoice.GRAPH_DGML:
                      CL_DGML_GraphEmitter.Run(inputProgram, outputName.Substring(0, outputName.LastIndexOf(".")));
                      break;
                    case ProgramChoice.GRAPH_DOT:
                      CL_DOT_GraphEmitter.Run(inputProgram, outputName.Substring(0, outputName.LastIndexOf(".")));
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
                  case ProgramChoice.EXTRACT_LOADS:
                      CLLoadExtractor.Run(inputProgram);
                      break;
                  case ProgramChoice.VERIFY:
                      int timeout = 600;
                      if (choiceString.Contains("_"))
                        timeout = Int32.Parse(choiceString.Split('_')[1]);
                      CLVerifier.Run(inputProgram, timeout);
                      break;
                  case ProgramChoice.SLICE_ASSUMES:
                      CLIndiscrimateAssumeSlicer.Run(inputProgram);
                      break;
                  case ProgramChoice.ABSTRACT_MEM:
                      CLMemAbstractor.Run(inputProgram);
                      break;
				  case ProgramChoice.ABSTRACT_USER_CALL_MEM:
				      CLUserDefinedCallMemAbstractor.Run(inputProgram);
					  break;
                  default:
                      throw new Exception("Not implemented");
              }
            }
            if (!(args[0].Equals("GRAPH_DOT") || args[0].Equals("GRAPH_DGML") || args[0].Equals("VERIFY"))) {
                TokenTextWriter ttw = new TokenTextWriter(outputName);
                inputProgram.Emit(ttw);
                ttw.Close();
            }
        }
    }
}
