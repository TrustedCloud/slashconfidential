using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using CfiVerifier;
using Microsoft.Boogie;
using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie.GraphUtil;

namespace CommandLineTools
{
    static class CLVerifier
    {
        public static void Run(Program input)
        {
            string tempFilename = @".temp.bpl";
            TokenTextWriter ttw = new TokenTextWriter(tempFilename);
            input.Emit(ttw);
            ttw.Close();

            char delim = Options.IsLinux() ? '/' : '\\';
            string binaryName = @"." + delim + "references" + delim + "Boogie.exe";
            string z3Path = @"." + delim + "references" + delim + "z3.4.4.1.exe";
            string arguments = "/z3exe:" + z3Path + @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0 /timeLimit:300 /errorLimit:1 " + tempFilename;
            Utils.Assert(File.Exists(binaryName), "Could not find provided Boogie executable!");

            //Console.WriteLine("\tSTART Executing {0} {1}", binaryName, arguments);
            try
            {
                ProcessStartInfo procInfo = new ProcessStartInfo();
                procInfo.UseShellExecute = false;
                procInfo.FileName = binaryName;
                procInfo.Arguments = arguments;
                procInfo.WindowStyle = ProcessWindowStyle.Hidden;
                procInfo.RedirectStandardOutput = true;
                Process proc = new Process();
                proc.StartInfo = procInfo;
                proc.EnableRaisingEvents = false;
                Stopwatch sw = new Stopwatch();
                sw.Start();
                proc.Start();
                string output;
                output = proc.StandardOutput.ReadToEnd();
                proc.WaitForExit();
                sw.Stop();
                //Console.WriteLine("\tEND Executing {0} {1}", binaryName, arguments);
                Console.WriteLine("======================");
                Console.WriteLine(output);
                Console.WriteLine("Time taken: " + sw.ElapsedMilliseconds / 1000 + "s");
                Console.WriteLine("======================");
            }
            catch (Exception e)
            {
                //Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
                Console.WriteLine("Exception: " + e);
            }
        }
    }

}

