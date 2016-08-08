using System;
using System.Collections.Generic;
using System.Collections;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.IO;
using System.Diagnostics;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;


namespace CfiVerifier
{
    class CfiVerifierMain
    {
        static void ExtractProgAndImpl(string fname, out Program prog, out Implementation impl)
        {
            if (!Utils.ParseProgram(fname, out prog)) {
                Utils.Assert(false, "Unable to parse file " + fname);
            }
            
            impl = prog.TopLevelDeclarations.Where(x => x is Implementation &&
                ((Implementation)x).Name.Contains("dll_func")).ElementAt(0) as Implementation;

            Utils.Assert(impl != null, "Unable to find Boogie implementation named \"dll_func\"");

        }

        static void Main(string[] args)
        {
            /* Command line parsing */
            if (!Options.ParseCommandLine(String.Join(" ", args))) return;

            foreach (var f in CommandLineOptions.Clo.Files.Where(x => x != ""))
            {
                Console.WriteLine("Processing file {0}", f);

                Program prog; Implementation impl;

                try
                {
                    // NOTE: Below, we have to reextract prog and impl because we want to purge the instrumentation from the previous phase
                    //Phase 0
                    ExtractProgAndImpl(f, out prog, out impl);
                    (new Validator()).Visit(prog);

                    //Phase 1
                    Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeDB = null, loadDB = null;
                    if (Options.optimizeStoreITE) 
                    {
                        ExtractProgAndImpl(f, out prog, out impl);
                        storeDB = DecideAddressRegions(prog, impl, true);
                    }

                    if (Options.optimizeLoadITE) 
                    {
                        ExtractProgAndImpl(f, out prog, out impl);
                        loadDB = DecideAddressRegions(prog, impl, false);
                    }

                    //Phase 2
                    ExtractProgAndImpl(f, out prog, out impl);
                    InstrumentEnclave(prog, impl, storeDB, loadDB);
                }
                catch (Exception e)
                {
                    Console.WriteLine("CfiVerifier terminated with an exception {0}", e);
                }
            }
        }

        private static Dictionary<Tuple<string, Cmd, AssertCmd>, bool> DecideAddressRegions(Program prog, Implementation impl, bool store)
        {
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> addressRegionDB;
            bool old_option = Options.splitMemoryModel;
            Options.splitMemoryModel = false;

            (new SpecialInstructionLifter()).Visit(prog);
            (new ModularVerificationSetup()).Visit(prog);
            (new EnvironmentSetup()).Visit(prog);
            (new IndiscriminateAssumeSlicer()).Visit(prog);

            VCSplitter.LaunchVCSplitter(impl);
            if (store) { 
                (new StoreAddressDecider()).Visit(prog);
                addressRegionDB = VCSplitter.Instance.VerifyInstrumentedProcedures(prog);
            } else { 
                (new LoadAddressDecider()).Visit(prog);
                addressRegionDB = VCSplitter.Instance.VerifyInstrumentedProcedures(prog);
            }

            Options.splitMemoryModel = old_option;

            return addressRegionDB;
        }

        private static void InstrumentEnclave(
            Program prog, 
            Implementation impl,
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB, 
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool>  loadAddressRegionDB )
        {
            Console.WriteLine("CfiVerifier found " + impl.Blocks.Count + " basic blocks");
            (new SpecialInstructionLifter()).Visit(prog);
            Utils.PrintProg(prog);
            if (Options.splitMemoryModel) { (new SplitMemoryModeler(storeAddressRegionDB, loadAddressRegionDB)).Visit(prog); }
            Utils.PrintProg(prog);
            (new ModularVerificationSetup()).Visit(prog);
            Utils.PrintProg(prog);
            //(new Utils.DeadCodeEliminator()).Visit(prog); //mostly to remove assingments to useless CPU flags

            //if (Utils.verbosityLevel(2)) { Console.WriteLine("InstrumentEnclave: replacing call instructions with CallCmd"); }
            // (new Utils.HavocingAdversary()).Visit(impl); //FIXME: this should be enabled.
            LoopDetector loopDetector = new LoopDetector();
            loopDetector.Visit(impl); //necessary before querying the stack size estimate
            List<Block> blocksInNaturalLoops = loopDetector.getBlocksInNaturalLoops();
            if (blocksInNaturalLoops.Count > 0)
            {
                Console.WriteLine("CfiVerifier found one or more loops");
                Console.WriteLine("Blocks in loops: {0}", blocksInNaturalLoops.MapConcat(x => x.Label, ","));
            }

            List<Block> loopHeaders = loopDetector.getLoopHeaders();
            if (loopHeaders.Count > 0)
            {
                Console.WriteLine("LOOP HEADERS: {0}", loopHeaders.MapConcat(x => x.Label, ","));
                Tuple<String, List<String>> result = Utils.HandleLoops(prog, impl);
                String memCheckpointLabel = result.Item1;
                List<String> loopHeaderLabels = result.Item2;
                Utils.InstrumentLoopInvariant(prog, impl, memCheckpointLabel, loopHeaderLabels);
            }

            VCSplitter.LaunchVCSplitter(impl);

            (new EnvironmentSetup()).Visit(prog); //TODO move this earlier, maybe before DeadCodeEliminator
            (new ProofObligations()).Visit(prog);
            Console.WriteLine("\nInstrumented Program with CFI assertions and generated output file {0}", Options.instrumentedFile);
            Utils.PrintProg(prog);
            VCSplitter.Instance.PrintInstrumentedProcedures(prog);
            VCSplitter.Instance.PrintAssertionTypes();
        }

    }
}
