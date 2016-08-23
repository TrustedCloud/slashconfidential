using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using CfiVerifier;

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
            ProgramChoice choice = (ProgramChoice)Enum.Parse(typeof(ProgramChoice), args[0]);
            switch (choice)
            {
                case ProgramChoice.SLICE:
                    // Arguments: string inputFile, string outputFile
                    Utils.Assert(args.Length == 3);
                    CLSlicer.Run(args[1], args[2]);
                    return;
                case ProgramChoice.GRAPH:
                    // Arguments: string inputFile, string outputFile
                    Utils.Assert(args.Length == 3);
                    CLGraphEmitter.Run(args[1], args[2]);
                    return;
                case ProgramChoice.REMOVE_CODE_BRANCHES:
                    // Arguments: string inputFile, string outputFile
                    Utils.Assert(args.Length == 3);
                    CLRemoveCodeBranches.Run(args[1], args[2]);
                    return;
                case ProgramChoice.SPLIT_MEMORY:
                    // Arguments: string inputFile, string outputFile, bool processed 
                    Utils.Assert(args.Length == 3);
                    CLMemorySplitter.Run(args[1], args[2], false);
                    return;
                case ProgramChoice.SPLIT_MEMORY_OPT:
                    // Arguments: string inputFile, string outputFile, bool processed
                    Utils.Assert(args.Length == 3);
                    CLMemorySplitter.Run(args[1], args[2], true);
                    return;
                case ProgramChoice.SLICE_PARTITIONS:
                    Utils.Assert(args.Length == 3);
                    CLParitionSlicer.Run(args[1], args[2]);
                    return;
                case ProgramChoice.SIMPLIFY_CONSTANT_EXPRS:
                    Utils.Assert(args.Length == 3);
                    CLConstantExpressionSimplifier.Run(args[1], args[2]);
                    return;
                default:
                    throw new Exception("Not implemented");
            }
        }
    }
}
