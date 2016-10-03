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
    class CLGraphEmitter
    {
        enum MemoryOperation {
            STORE_BITMAP,
            STORE_STACK,
            STORE_REST,
            CALL
        }

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
            using (System.Xml.XmlTextWriter writer = new System.Xml.XmlTextWriter(file, Encoding.UTF8))
            {
                /* Document setup */
                writer.WriteStartDocument(true);
                writer.Formatting = System.Xml.Formatting.Indented;
                writer.Indentation = 2;
                writer.WriteStartElement("DirectedGraph", @"http://schemas.microsoft.com/vs/2009/dgml");

                /* Emitting Nodes */
                writer.WriteStartElement("Nodes");
                foreach (Block b in cfg.nodes)
                {
                    writer.WriteStartElement("Node");
                    writer.WriteAttributeString("Id", b.Label);
                    HashSet<MemoryOperation> blockMemoryWrites = GatherMemoryAccesses(b);
                    if (blockMemoryWrites.Any())
                    {
                        writer.WriteAttributeString("Group", "Expanded");
                    }
                    if (!b.Cmds.Any())
                    {
                        writer.WriteAttributeString("Background", "Black");
                        writer.WriteAttributeString("Foreground", "White");
                    }
                    else if (blockMemoryWrites.Contains(MemoryOperation.CALL))
                    {
                        writer.WriteAttributeString("Background", "Brown");
                    }
                    else if (blockMemoryWrites.Contains(MemoryOperation.STORE_BITMAP))
                    {
                        writer.WriteAttributeString("Background", "Blue");
                    }
                    else if (blockMemoryWrites.Contains(MemoryOperation.STORE_STACK))
                    {
                        writer.WriteAttributeString("Background", "Red");
                    }
                    else if (blockMemoryWrites.Contains(MemoryOperation.STORE_REST))
                    {
                        writer.WriteAttributeString("Background", "Green");
                    }
                    writer.WriteEndElement();
                }
                writer.WriteEndElement();

                /* Emitting Links */
                writer.WriteStartElement("Links");
                foreach (Block b in cfg.nodes)
                {
                    foreach (Block succ in cfg.succEdges[b])
                    {
                        writer.WriteStartElement("Link");
                        writer.WriteAttributeString("Source", b.Label);
                        writer.WriteAttributeString("Target", succ.Label);
                        writer.WriteEndElement();
                    }
                    foreach (MemoryOperation ml in GatherMemoryAccesses(b))
                    {
                        writer.WriteStartElement("Link");
                        writer.WriteAttributeString("Source", b.Label);
                        writer.WriteAttributeString("Target", b.Label + "_" + ml);
                        writer.WriteAttributeString("Category", "Contains");
                        writer.WriteEndElement();
                    }
                }
                writer.WriteEndElement();

                /* Emitting DirectedGraph end */
                writer.WriteEndElement();
                /* Emitting Document end */
                writer.WriteEndDocument();
            }
        }

        private static HashSet<MemoryOperation> GatherMemoryAccesses(Block b)
        {
            HashSet<MemoryOperation> memoryLocations = new HashSet<MemoryOperation>();
            foreach (Cmd c in b.Cmds)
            {
                if (c is AssignCmd)
                {
                    AssignCmd assignCmd = c as AssignCmd;
                    string lhsName = assignCmd.Lhss.First().DeepAssignedVariable.Name;
                    if (lhsName.Equals("mem"))
                        memoryLocations.Add(MemoryOperation.STORE_REST);
                    else if (lhsName.Equals("mem_bitmap"))
                        memoryLocations.Add(MemoryOperation.STORE_BITMAP);
                    else if (lhsName.Equals("mem_stack"))
                        memoryLocations.Add(MemoryOperation.STORE_STACK);
                }
                else if (c is CallCmd)
                {
                    memoryLocations.Add(MemoryOperation.CALL);
                }
            }
            return memoryLocations;
        }

    }
}
