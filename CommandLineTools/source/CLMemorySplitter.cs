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
    class CLMemorySplitter
    {
        public static void Run(string inputFile, string outputFile, bool processed)
        {
            Program prog = null;
            Implementation impl = null;

            Options.splitMemoryModel = false;
            Options.splitFiles = true; // HACK
            Utils.ExtractProgAndImpl(inputFile, out prog, out impl);
            if (!processed)
                CodeProcess(prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB = DecideAddressRegions(prog, true);
            Utils.ExtractProgAndImpl(inputFile, out prog, out impl);
            if (!processed)
                CodeProcess(prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB = DecideAddressRegions(prog, false);
            Utils.ExtractProgAndImpl(inputFile, out prog, out impl);
            Options.splitMemoryModel = true;
            (new SplitMemoryModeler(storeAddressRegionDB, loadAddressRegionDB)).Visit(prog);

            using (TokenTextWriter ttw = new TokenTextWriter(outputFile))
            {
                prog.Emit(ttw);
            }
        }

        private static void CodeProcess(Program prog) {
            try
            {
                // SpecialInstructionLifter requires addresses for functions passed as arguments
                //(new SpecialInstructionLifter()).Visit(prog);
                (new ModularVerificationSetup()).Visit(prog);
                (new EnvironmentSetup()).Visit(prog);
                (new IndiscriminateAssumeSlicer()).Visit(prog);
            }
            catch (Exception e)
            {
                Console.WriteLine("Exception: " + e);
                Environment.Exit(1);
            }
        }

        private static Dictionary<Tuple<string, Cmd, AssertCmd>, bool> DecideAddressRegions(Program prog, bool store)
        {
            VCSplitter.LaunchVCSplitter(prog.Implementations.First());
            if (store)
                (new StoreAddressDecider()).Visit(prog);
            else
                (new LoadAddressDecider()).Visit(prog);
            return VCSplitter.Instance.VerifyInstrumentedProcedures(prog);
        }
    }
}
