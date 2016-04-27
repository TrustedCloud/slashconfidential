using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;


namespace CfiVerifier
{
    public static class Options
    {
        //Options: Add them to ParseAndRemoveNonBoogieOptions
        public static int verbose = 0;

        public static bool IsLinux()
        {
            int p = (int)Environment.OSVersion.Platform;
            return (p == 4) || (p == 6) || (p == 128); //4 is for UNIX, 6 is for Mac, 128 for older Mono
        }
        public static string outputPath = @"."; //path for dump files model.dmp, tmp.bpl
        public static string instrumentedFile = "instrumented.bpl";
        public static string splitFilesDir = "";
        public static bool splitFiles = false;
        public static string tag = "";
        public static bool instantiateQuantifiers = false;
        public static string funcNew = "";
        public static string funcGuardCheckIcallCfw = "";
        public static string funcMemset = "";
        public static string funcMemcmp = "";
        public static string funcMemcpy = "";
        public static string funcSGXFree = "";
        public static string funcSGXMalloc = "";
        public static string dataLow = "";
        public static string dataHigh = "";
        public static bool switch1 = false;
        public static bool confidentiality = false;
        public static bool disablePolicyChecking = false;
        public static bool splitMemoryModel = false;
        public static bool optimizeStoreITE = false;
        public static bool optimizeLoadITE = false;

        public static int boogieTimeout = 200;    //timeout for Boogie


        public static List<string> predFuns = new List<string>();


        #region Parsing routines
        public static bool ParseCommandLine(string clo)
        {
            //without the next line, it fails to find the right prover!!
            var boogieOptions = "/typeEncoding:m -timeLimit:" + boogieTimeout + " -removeEmptyBlocks:0 /printModel:1 /printInstrumented " + clo;
            boogieOptions += " /errorLimit:1 ";
            var oldArgs = boogieOptions.Split(' ');
            string[] args;
            //Custom parser to look and remove RootCause specific options
            var help = ParseAndRemoveNonBoogieOptions(oldArgs, out args);
            CommandLineOptions.Install(new CommandLineOptions());
            CommandLineOptions.Clo.RunningBoogieFromCommandLine = true;
            //Options.htmlTag, Options.outputPath gets parsed only after ParseAndRemove...
            var modelArgs = " /printModelToFile:" + Options.outputPath + @"\cfi_model" + @".dmp";
            var dumpVC = " /proverLog:" + Options.outputPath + @"\cfi_vc" + @".z3";
            args = (args.ToList()).Concat(new List<string>() { modelArgs, dumpVC }).ToArray();
            CommandLineOptions.Clo.Parse(args);
            return !help;
        }

        public static bool CheckBooleanFlag(string s, string flagName, ref bool flag, bool valueWhenPresent)
        {
            if (s == "/" + flagName || s == "-" + flagName)
            {
                flag = valueWhenPresent;
                return true;
            }
            return false;
        }
        public static bool CheckBooleanFlag(string s, string flagName, ref bool flag)
        {
            return CheckBooleanFlag(s, flagName, ref flag, true)
                || CheckBooleanFlag(s, flagName + "+", ref flag, true)
                || CheckBooleanFlag(s, flagName + "-", ref flag, false);
        }

        public static bool CheckIntegerOption(string s, string flagName, ref int flag)
        {
            //eg. /hintline:1
            if (s.Contains("/" + flagName + ":"))
            {
                string numericString = s.Substring(flagName.Length + 2); //1 for / and 1 for :
                try
                {
                    flag = int.Parse(numericString); return true;
                }
                catch (Exception e) { Console.WriteLine(e); return false; }
            }
            return false;
        }

        public static bool CheckIntegerListOption(string s, string flagName, ref List<int> flag)
        {
            //eg. /hintline:1
            if (s.Contains("/" + flagName + ":"))
            {
                string numericString = s.Substring(flagName.Length + 2); //1 for / and 1 for :
                try
                {
                    char[] delimiters = { '@' };
                    foreach (String linestr in numericString.Split(delimiters))
                    {
                        int line = int.Parse(linestr);
                        flag.Add(line);
                    }
                    return true;
                    //flag = int.Parse(numericString); return true;
                }
                catch (Exception e) { Console.WriteLine(e); return false; }
            }
            return false;
        }

        public static bool CheckStringOption(string s, string flagName, ref string flag)
        {
            //eg. /html:abc.html
            if (s.Contains("/" + flagName + ":"))
            {
                string str = s.Substring(flagName.Length + 2); //1 for / and 1 for :
                try
                {
                    flag = str; return true;
                }
                catch (Exception e) { Console.WriteLine(e); return false; }
            }
            return false;
        }

        //currently only Boolean options are supported
        //returns true if help is required
        //TODO: make it parameterized by using Reflection
        public static bool ParseAndRemoveNonBoogieOptions(string[] args, out string[] newargs)
        {
            var retArgs = new List<string>();
            bool help = false;
            foreach (var a in args)
            {
                if (CheckIntegerOption(a, "verbose", ref verbose)
                    || CheckStringOption(a, "instrumentedFile", ref instrumentedFile)
                    || CheckStringOption(a, "tag", ref tag)
                    || CheckBooleanFlag(a, "splitFiles", ref splitFiles)
                    || CheckStringOption(a, "splitFilesDir", ref splitFilesDir)
                    || CheckBooleanFlag(a, "instantiateQuantifiers", ref instantiateQuantifiers)
                    || CheckStringOption(a, "dataLow", ref dataLow)
                    || CheckStringOption(a, "dataHigh", ref dataHigh)
                    || CheckStringOption(a, "funcSGXMalloc", ref funcSGXMalloc)
                    || CheckStringOption(a, "funcSGXFree", ref funcSGXFree)
                    || CheckStringOption(a, "funcMemcmp", ref funcMemcmp)
                    || CheckStringOption(a, "funcMemcpy", ref funcMemcpy)
                    || CheckStringOption(a, "funcMemset", ref funcMemset)
                    || CheckStringOption(a, "funcNew", ref funcNew)
                    || CheckStringOption(a, "funcGuardCheckIcallCfw", ref funcGuardCheckIcallCfw)
                    || CheckBooleanFlag(a, "switch1", ref switch1)
                    || CheckBooleanFlag(a, "confidentiality", ref confidentiality)
                    || CheckBooleanFlag(a, "disablePolicyChecking", ref disablePolicyChecking)
                    || CheckBooleanFlag(a, "splitMemoryModel", ref splitMemoryModel)
                    || CheckBooleanFlag(a, "optimizeStoreITE", ref optimizeStoreITE)
                    || CheckBooleanFlag(a, "optimizeLoadITE", ref optimizeLoadITE)

                    ) continue;
                if (a.StartsWith("/predFun:"))
                {
                    predFuns.Add(a.Substring("/predFun:".Length));
                    continue;
                }
                retArgs.Add(a);
                if (a == "-?" || a == "/?") { help = true; retArgs.Remove(a); continue; } //add it to Boogie as well
            }
            Utils.Assert(!(splitFiles) || (splitFilesDir != ""), "Must provide splitFilesDir option if splitFiles is enabled");
            newargs = retArgs.ToArray();
            if (help)
            {
                Console.WriteLine("\n  ---- Cfi Verifier options ----------------------------------------\n");
                Console.WriteLine("  Boolean options: \n\tuse /option or /option+ to set, use /option- to unset\n");
                Console.WriteLine("  /break: \n\tBreak into the debugger\n");
                Console.WriteLine("  To see additional Boogie options, use /help\n");
                Console.WriteLine("  /verbose:  \n\tMakes output verbose (default {0})\n", verbose);
                Console.WriteLine("  /instrumentedFile:  \n\t Output file after transformation (default instrumented.bpl)\n");
                Console.WriteLine("  /splitFiles:  \n\t One Assert per BPL program? (if you set this, you must also set splitFilesDir)\n");
                Console.WriteLine("  /splitFilesDir:  \n\t where to place split files\n");
                Console.WriteLine("  /instantiateQuantifiers:  \n\t instantiate quantifiers in predicates, wherever possible\n");
                Console.WriteLine("  /splitMemoryModel:  \n\t Divide memory into separate maps for the stack, bitmap, and rest of memory\n");
                Console.WriteLine("  /optimizeStoreITE:  \n\t Optimize ITE expressions \n");
                Console.WriteLine("  /optimizeLoadITE:  \n\t Optimize ITE expressions \n");
                Console.WriteLine("\n  ----------------------------------------------------------------\n");
                return true;
            }
            return false;
        }
        #endregion
    }
}
