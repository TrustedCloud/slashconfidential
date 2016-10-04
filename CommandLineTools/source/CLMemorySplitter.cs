using System;
using System.Collections.Generic;
using System.IO;
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
        public static void Run(Program input, bool processed)
        {
            StringWriter sw = new StringWriter();
            TokenTextWriter ttw = new TokenTextWriter(sw);
            input.Emit(ttw);
            ttw.Close();

            Options.splitMemoryModel = false;
            Options.splitFiles = true; // HACK
            Program prog;
            Utils.ParseString(sw.ToString(), out prog);
            if (!processed)
                CodeProcess(prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB = DecideAddressRegions(prog, true);
            Utils.ParseString(sw.ToString(), out prog);
            if (!processed)
                CodeProcess(prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB = DecideAddressRegions(prog, false);
            Utils.ParseString(sw.ToString(), out prog);
            Options.splitMemoryModel = true;
			(new SplitMemoryModeler(storeAddressRegionDB, loadAddressRegionDB, Utils.ProgramIsSplit(input))).Visit(input);
            sw.Close();
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
