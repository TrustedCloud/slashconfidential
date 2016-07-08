﻿using System;
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
                    Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeDB = null, loadDB = null;
                    //Phase 1
                    if (Options.optimizeStoreITE)
                    {
                        if (!Utils.ParseProgram(f, out prog)) return;
                        impl = prog.TopLevelDeclarations.Where(x => x is Implementation &&
                            ((Implementation)x).Name.Contains("dll_func")).ElementAt(0) as Implementation;
                        Utils.Assert(impl != null, "Unable to find Boogie implementation named \"dll_func\"");
                        storeDB = DecideAddressRegions(prog, impl, true);
                    }

                    if (Options.optimizeLoadITE)
                    {
                        if (!Utils.ParseProgram(f, out prog)) return;
                        impl = prog.TopLevelDeclarations.Where(x => x is Implementation &&
                            ((Implementation)x).Name.Contains("dll_func")).ElementAt(0) as Implementation;
                        loadDB = DecideAddressRegions(prog, impl, false);
                    }

                    //Phase 2
                    if (!Utils.ParseProgram(f, out prog)) return;
                    impl = prog.TopLevelDeclarations.Where(x => x is Implementation &&
                        ((Implementation)x).Name.Contains("dll_func")).ElementAt(0) as Implementation;
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
                Console.WriteLine("Found loop");
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
        }

    }
}
