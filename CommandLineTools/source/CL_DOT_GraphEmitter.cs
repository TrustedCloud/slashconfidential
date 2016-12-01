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
    class CL_DOT_GraphEmitter
    {
        enum MemoryOperation {
            STORE_BITMAP,
            STORE_STACK,
            STORE_REST,
            CALL
        }

        static Dictionary<MemoryOperation, string> OperationColours = new Dictionary<MemoryOperation, string>{
            { MemoryOperation.STORE_BITMAP, "blue"  },
            { MemoryOperation.STORE_STACK,  "red"   },
            { MemoryOperation.STORE_REST,   "green" },
            { MemoryOperation.CALL,         "brown" }
        };

        public static void Run(Program input, string outputFile)
        {
            Implementation impl = input.Implementations.First();
            CommandLineOptions.Clo.PruneInfeasibleEdges = true;
            impl.PruneUnreachableBlocks();
            ICFG cfg = new ICFG(impl);
            EmitCFGGraph(outputFile, cfg);
        }

        private static void EmitCFGGraph(string file, ICFG cfg)
        {
            using (System.IO.StreamWriter writer = new System.IO.StreamWriter(file))
            {
                /* Document setup */
                writer.WriteLine("digraph slash_conf_assert_graph {");

                /* Emitting Nodes */
                foreach (Block b in cfg.nodes)
                {
                    writer.Write("\t");
                    writer.Write(b.Label);
                    HashSet<string> blockMemoryWrites = GatherMemoryAccesses(b);
					if (blockMemoryWrites.Count > 1)
					{
						writer.Write("[style=wedged,fillcolor=\"" + String.Join(":", blockMemoryWrites) + "\"]");
					}
					else if (blockMemoryWrites.Count == 1)
					{
						writer.Write("[style=filled, color=" + blockMemoryWrites.First() + "]");
					}
					else if (b.Cmds.Count == 0)
					{
						writer.Write("[style=filled, color=black, fontcolor=white]");
					}
                    writer.Write(";\n");
                }

                /* Emitting Links */
				foreach (Block b in cfg.nodes)
				{
					foreach (Block succ in cfg.succEdges[b])
					{
						writer.Write(b.Label + "->" + succ.Label + ";\n");
					}
				}

                /* Emitting Document end */
                writer.Write("}");
                writer.Close();
            }
        }

        private static HashSet<string> GatherMemoryAccesses(Block b)
        {
            HashSet<string> memoryLocations = new HashSet<string>();
            foreach (Cmd c in b.Cmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assignCmd = c as AssignCmd;
                    string lhsName = assignCmd.Lhss.First().DeepAssignedVariable.Name;
                    if (lhsName.Equals("mem"))
                        memoryLocations.Add(OperationColours[MemoryOperation.STORE_REST]);
                    else if (lhsName.Equals("mem_bitmap"))
                        memoryLocations.Add(OperationColours[MemoryOperation.STORE_BITMAP]);
                    else if (lhsName.Equals("mem_stack"))
                        memoryLocations.Add(OperationColours[MemoryOperation.STORE_STACK]);
                }
                else if (c is CallCmd)
                {
                    memoryLocations.Add(OperationColours[MemoryOperation.CALL]);
                }
            }
            return memoryLocations;
        }

    }
}
