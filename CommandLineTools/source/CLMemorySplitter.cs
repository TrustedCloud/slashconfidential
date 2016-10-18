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
        public static void Run(Program input)
        {
            StringWriter sw = new StringWriter();
            TokenTextWriter ttw = new TokenTextWriter(sw);
            input.Emit(ttw);
            ttw.Close();

            Options.splitMemoryModel = false;
            Options.splitFiles = true; // HACK
            Program prog;
            Utils.ParseString(sw.ToString(), out prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> loadAddressRegionDB = DecideAddressRegions(prog, false);
            Utils.ParseString(sw.ToString(), out prog);
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> storeAddressRegionDB = DecideAddressRegions(prog, true);
            Options.splitMemoryModel = true;
            (new SplitMemoryModeler(storeAddressRegionDB, loadAddressRegionDB, Utils.ProgramIsSplit(input))).Visit(input);
            sw.Close();
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
