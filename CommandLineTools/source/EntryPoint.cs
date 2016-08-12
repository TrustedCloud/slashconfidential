using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace CommandLineTools
{
    class EntryPoint 
    {
        enum ProgramChoice {
            SLICE,
            GRAPH,
            REMOVE_CODE_BRANCHES
        }

        public static void Main(string[] args)
        {
            if (!CfiVerifier.Options.ParseCommandLine(String.Join(" ", args))) return;
            ProgramChoice choice = (ProgramChoice)Enum.Parse(typeof(ProgramChoice), args[0]);
            switch (choice)
            {
                case ProgramChoice.SLICE:
                    System.Diagnostics.Debug.Assert(args.Length == 3);
                    CLSlicer.Run(args[1], args[2]);
                    return;
                case ProgramChoice.GRAPH:
                    System.Diagnostics.Debug.Assert(args.Length == 3);
                    CLGraphEmitter.Run(args[1], args[2]);
                    return;
                case ProgramChoice.REMOVE_CODE_BRANCHES:
                    System.Diagnostics.Debug.Assert(args.Length == 3);
                    CLRemoveCodeBranches.Run(args[1], args[2]);
                    return;
                default:
                    throw new Exception("Not implemented");
            }
        }
    }
}
