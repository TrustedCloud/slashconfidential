using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Reflection;
using System.Diagnostics;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace CfiDriver
{
    /// <summary>
    /// This module runs rootcause.exe as a black box on a set of directories, with various options and 
    /// generates a HTML report of the results
    /// </summary>
  class CfiDriver
    {
        enum BoogieResult { VERIFIED, ERROR, UNKNOWN }; 

        static Dictionary<string, List<Tuple<string,int,bool,int,BoogieResult,int>>> results; //dir -> result
        static List<Tuple<string, string, string, string>> benchmarks; //<directory, input bpl, options, run_type_name>

        private void Usage()
        {
            Console.WriteLine("Usage:\n");
            Console.WriteLine("CfiDriver.exe [options]");
        }
        static void Main(string[] args)
        {
            Console.WriteLine("Environment has {0} processors", Environment.ProcessorCount);
            results = new Dictionary<string, List<Tuple<string,int,bool,int,BoogieResult,int>>>();
            benchmarks = new List<Tuple<string, string, string, string>>();

            //all benchmark options should be in options.cs to avoid changes to this file except for logic changes
            Options.CollectBenchmarks(args, ref benchmarks);

            if (args.Any(x => x.Contains("/time:")))
            {
                string s = args.FirstOrDefault(x => x.Contains("/time:"));
                string[] separators = {":"};
                Options.timeoutPerProcess = Int32.Parse(s.Split(separators, StringSplitOptions.RemoveEmptyEntries)[1]);
            }

            Tuple<int, int, int> stats = RunBenchmarks(benchmarks,
                args.Contains("/option:norun"),
                args.Contains("/option:splitmemory"),
                args.Contains("/option:optimizestore"),
                args.Contains("/option:optimizeload"));

            var dateString = DateTime.Now.Hour.ToString() + "_" + DateTime.Now.Minute.ToString() + "_" + DateTime.Now.Second.ToString();
            GenerateResultOutput(@"CfiResultsSummary_" + dateString + ".txt", stats);
        }

        public static Tuple<int, int, int> RunBenchmarks(List<Tuple<string, string, string, string>> benchmarks, bool doNotRunBenchmarks, bool splitMemory, bool optimizeStore, bool optimizeLoad)
        {
          //item1 = benchmarks\StackExample\func_0000000000001000, item2 = dllfunc.bpl, item3 = "", item4 = "baseline"
          var delim = Options.IsLinux() ? @"/" : @"\";
          int numVerified = 0, numError = 0, numUnknown = 0;

          foreach (Tuple<string, string, string, string> benchmark in benchmarks)
          {
              if (!Directory.Exists(benchmark.Item1))
              {
                  throw new Exception("Directory " + benchmark.Item1 + " does not exist");
              }
              else
              {
                  Console.WriteLine("\n>>>>>>> Processing directory {0}", benchmark.Item1);
              }
              //Func<string, string> WrapPath = delegate(string s) { return benchmark.Item1 + separator + s; };
              string args = @" " + benchmark.Item1 + delim + benchmark.Item2;
              args += @" /instrumentedFile:" + benchmark.Item1 + delim + "dll_func_instrumented.bpl";
              args += @" /splitFiles /splitFilesDir:" + benchmark.Item1 + " ";
              args += @" " + benchmark.Item3;
              args += @" /tag:" + benchmark.Item4;
              if (splitMemory) { args += @" /splitMemoryModel+"; }
              if (optimizeStore) { args += @" /optimizeStoreITE+"; }
              if (optimizeLoad) { args += @" /optimizeLoadITE+"; }
              Tuple<int, bool, List<Tuple<int, int>>> result = ExecuteCfiVerifierBinary(args);
              int numAssertions = result.Item1;
              bool foundLoops = result.Item2;
              if (numAssertions < 0)
              {
                  throw new Exception("Benchmark " + benchmark.Item1 + " did not generate any assertions");
              }
              Console.WriteLine("\tFOUND {0} assertions in benchmark {1}, Running them in parallel...", numAssertions, benchmark.Item1);
              if (!doNotRunBenchmarks) { CheckAssertionsInParallel(benchmark.Item1, benchmark.Item4, numAssertions, foundLoops); }

              {
                  TextWriter output = new StreamWriter("script");
                  for (int i = 0; i < numAssertions; i++)
                  {
                      string boogie_args = @" " + benchmark.Item1 + delim + @"split_" + i.ToString() + @"." + 
                          benchmark.Item4 + ".bpl /timeLimit:" + Options.timeoutPerProcess + 
                          @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0";
                      string boogie_bin = @"." + delim + "boogie" + delim + "Binaries" + delim + "Boogie.exe";
                      output.WriteLine(boogie_bin + boogie_args);
                  }
                  output.Flush();
                  output.Close();
              }

              foreach (Tuple<int, int> t in result.Item3)
              {
                  Console.WriteLine("\tFOUND grouped assertions: ({0},{1})", t.Item1, t.Item2);
              }
              Tuple<int, int, int> stats = ComputeStatisticsForDirectory(benchmark.Item1, result.Item3);
              numVerified += stats.Item1; numError += stats.Item2; numUnknown += stats.Item3;
          }

          return new Tuple<int, int, int>(numVerified, numError, numUnknown);
        }

        private static Tuple<int, int, int> ComputeStatisticsForDirectory(string directory, List<Tuple<int,int>> mergedAsserts)
        {
            // results[directory].Add(Tuple.Create(tag, i, foundLoops, option, result, timeInSeconds));
            int numVerified = 0, numError = 0, numUnknown = 0;
            BoogieResult mergedAssertResult = BoogieResult.VERIFIED;
            if (!results.ContainsKey(directory)) { return new Tuple<int, int, int>(0, 0, 0); }
            foreach (Tuple<string, int, bool, int, BoogieResult, int> t in results[directory])
            {
                bool isMergedAssert = mergedAsserts.Any(x => t.Item2 >= x.Item1 && t.Item2 <= x.Item2);
                if (!isMergedAssert)
                {
                    if (t.Item5 == BoogieResult.VERIFIED) { numVerified++; }
                    if (t.Item5 == BoogieResult.ERROR) { numError++; }
                    if (t.Item5 == BoogieResult.UNKNOWN) { numUnknown++; }
                }
                else
                {
                    if (mergedAssertResult == BoogieResult.ERROR) { mergedAssertResult = BoogieResult.ERROR; }
                    else if (mergedAssertResult == BoogieResult.UNKNOWN && t.Item5 == BoogieResult.ERROR) { mergedAssertResult = BoogieResult.ERROR; }
                    else if (mergedAssertResult == BoogieResult.VERIFIED && t.Item5 == BoogieResult.UNKNOWN) { mergedAssertResult = BoogieResult.UNKNOWN; }
                    else if (mergedAssertResult == BoogieResult.VERIFIED && t.Item5 == BoogieResult.ERROR) { mergedAssertResult = BoogieResult.ERROR; }
                }
            }
            if (mergedAssertResult == BoogieResult.VERIFIED) { return new Tuple<int, int, int>(numVerified + 1, numError, numUnknown); }
            else if (mergedAssertResult == BoogieResult.ERROR) { return new Tuple<int, int, int>(numVerified, numError + 1, numUnknown); }
            else { return new Tuple<int, int, int>(numVerified, numError, numUnknown + 1); }
        }

        private static void CheckAssertionsInParallel(string directory, string tag, int numAssertions, bool foundLoops)
        {
            Parallel.For(0, numAssertions, 
              new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount },
              i => CheckAssertion(directory, tag, i, foundLoops));
        }

        private static void CheckAssertion(string directory, string tag, int i, bool foundLoops)
        {
            //join is commutative. join(VERIFIED,_) = VERIFIED. join(UNKNOWN,x) = x. join(ERROR,ERROR) = ERROR.
            Func<BoogieResult, BoogieResult, BoogieResult> join = delegate(BoogieResult r1, BoogieResult r2)
            {
              if (r1 == BoogieResult.VERIFIED || r2 == BoogieResult.VERIFIED) { return BoogieResult.VERIFIED; }
              else if (r1 == BoogieResult.UNKNOWN) { return r2; }
              else if (r2 == BoogieResult.UNKNOWN) { return r1; }
              else { return BoogieResult.ERROR; } //both r1 and r2 are ERROR in this case }
            };

            var delim = Options.IsLinux() ? @"/" : @"\";
            bool forNuno = false;
            if (forNuno)
            {
                string args0 = @" " + directory + delim + @"split_" + i.ToString() + @"." + tag + ".bpl /timeLimit:" + Options.timeoutPerProcess;
                string args1 = args0 + @" /proverLog:" + directory + delim + @"split_" + i.ToString() + @"." + "baseline" + ".z3" + @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0";
                string args2 = args0 + @" /proverLog:" + directory + delim + @"split_" + i.ToString() + @"." + "tharray" + ".z3" + @" /typeEncoding:m /useArrayTheory";
                Tuple<BoogieResult, int> args1_result = ExecuteBoogieBinary(args1);
            }
            else
            {
                string args0 = @" " + directory + delim + @"split_" + i.ToString() + @"." + tag + ".bpl /timeLimit:" + Options.timeoutPerProcess;
                string args1 = args0 + @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0";
                //string args2 = args0 + @" /typeEncoding:m /useArrayTheory";
                Tuple<BoogieResult, int> args1_result = ExecuteBoogieBinary(args1);
                RegisterResult(directory, tag, i, foundLoops, 1, args1_result.Item1, args1_result.Item2);
            }

          /* //Seems like args2 very rarely gives VERIFIED when args1 gives ERROR/UNKNOWN. This happened 4 / ~10000 times. Not worth it.
            if (args1_result.Item1 == BoogieResult.VERIFIED)
            {
              RegisterResult(directory, tag, i, foundLoops, 1, BoogieResult.VERIFIED, args1_result.Item2);
            }
            //if ERROR or UNKNOWN, try another run with no options. Sometimes this gives a proof!
            else
            {
              Tuple<BoogieResult, int> args2_result = ExecuteBoogieBinary(args2);
              if (args2_result.Item1 == BoogieResult.VERIFIED)
              {
                RegisterResult(directory, tag, i, foundLoops, 2, BoogieResult.VERIFIED, args2_result.Item2);
              }
              else
              {
                //BoogieResult args0_result = ExecuteBoogieBinary(args0);
                //RegisterResult(directory, tag, i, join(args0_result, join(args1_result, args2_result)));
                RegisterResult(directory, tag, i, foundLoops, 2, join(args1_result.Item1, args2_result.Item1), Math.Max(args1_result.Item2, args2_result.Item2));
              }
            }
          */
        }

        private static Tuple<BoogieResult, int> ExecuteBoogieBinary(string arguments)
        {
          var delim = Options.IsLinux() ? @"/" : @"\";
          string binaryName = @"." + delim + "boogie" + delim + "Binaries" + delim + "Boogie.exe";
          //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
          Func<string, BoogieResult> result = delegate(string s)
          {
            if (s.Contains("Boogie program verifier finished with 1 verified, 0 errors")) { return BoogieResult.VERIFIED; }
            else if (s.Contains("Boogie program verifier finished with 0 verified, 1 error") && 
                     s.Contains("This assertion might not hold")) { return BoogieResult.ERROR; }

            return BoogieResult.UNKNOWN;
          };

          Console.WriteLine("\tSTART Executing {0} {1}", binaryName, arguments);
          try
          {
            ProcessStartInfo procInfo = new ProcessStartInfo();
            //System.Diagnostics.Process proc = new System.Diagnostics.Process();
            procInfo.UseShellExecute = false;
            procInfo.FileName = binaryName;
            procInfo.Arguments = arguments;
            procInfo.WindowStyle = ProcessWindowStyle.Hidden;
            procInfo.RedirectStandardOutput = true;
            Process proc = new Process();
            proc.StartInfo = procInfo;
            proc.EnableRaisingEvents = false;
            Stopwatch sw = Stopwatch.StartNew();
            proc.Start();
            string output = "";
            output = proc.StandardOutput.ReadToEnd();
            proc.WaitForExit();
            Console.WriteLine("\tEND Executing {0} {1}", binaryName, arguments);
            return new Tuple<BoogieResult, int>(result(output), sw.Elapsed.Minutes * 60 + sw.Elapsed.Seconds);
          }
          catch (Exception e)
          {
            Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
            return new Tuple<BoogieResult, int>(BoogieResult.UNKNOWN, 0);
          }
        }

        private static string GetBinaryPath()
        {
            var asmbly = Assembly.GetExecutingAssembly();
            var path  =  asmbly.Location.Substring(0, asmbly.Location.IndexOf(asmbly.ManifestModule.Name));
            //Console.WriteLine("Current assembly is {0}, {1}, {2}", asmbly.FullName, asmbly.Location, path);
            var s = Options.IsLinux() ? @"/" : @"\";
            return path + @".."+s+".."+s+".."+s+"CfiVerifier"+s+"bin"+s+"Debug"+s;
        }
        private static Tuple<int, bool, List<Tuple<int, int>>> ExecuteCfiVerifierBinary(string arguments)
        {
            string binaryName = GetBinaryPath() + @"CfiVerifier.exe";
            //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
            Func<string, int> BenchmarkCount = delegate(string s)
            {
              if (s.Contains("VCSplitter generated") && s.Contains("assertions"))
              {
                string countString = s.Split(new string[] { "VCSplitter generated " }, StringSplitOptions.None)[1].
                                       Split(new string[] { " assertions" }, StringSplitOptions.None)[0];
                return Int32.Parse(countString);
              }

              return -1;
            };

            Func<string, bool> FoundLoop = delegate(string s)
            {
              return (s.Contains("Found loop"));
            };

            Func<string, List<Tuple<int, int>>> MergedAsserts = delegate(string s)
            {
                List<Tuple<int, int>> result = new List<Tuple<int, int>>();
                if (!s.Contains("VCSplitter says that ret produced assertions")) { return result; }

                foreach (string suffix in s.Split(new string[] { "\n" }, StringSplitOptions.None).
                    Where(x => x.Contains("VCSplitter says that ret produced assertions")))
                {
                    int start = Int32.Parse(suffix.Split(new String[] { "(" }, StringSplitOptions.None)[1].Split(new string[] { "," }, StringSplitOptions.None)[0]);
                    int end = Int32.Parse(suffix.Split(new String[] { "," }, StringSplitOptions.None)[1].Split(new string[] { ")" }, StringSplitOptions.None)[0]);
                    result.Add(new Tuple<int, int>(start,end));
                }
                return result;
            };

            Console.WriteLine("\tSTART Executing {0} {1}", binaryName, arguments);
            try
            {
                ProcessStartInfo procInfo = new ProcessStartInfo();
                //System.Diagnostics.Process proc = new System.Diagnostics.Process();
                procInfo.UseShellExecute = false;
                procInfo.FileName = binaryName;
                procInfo.Arguments = arguments;
                procInfo.WindowStyle = ProcessWindowStyle.Hidden;
                procInfo.RedirectStandardOutput = true;
                Process proc = new Process();
                proc.StartInfo = procInfo;
                proc.EnableRaisingEvents = false;
                proc.Start();
                string output = "";
                output = proc.StandardOutput.ReadToEnd();
                proc.WaitForExit();
                
                # region deprecated logic for forcing a timeout
                //
                // Caution: Using proc.WaitForExit(1200000) causes processes to be idle
                //
                //bool exitInTime = proc.WaitForExit(1200000);
                //if (!exitInTime) { Console.WriteLine("TIMEOUT"); }
                //while (proc.StandardOutput.Peek() > -1)
                //{
                //    output = output + proc.StandardOutput.ReadLine() + "\n";
                //}
                //if (!exitInTime)
                //{
                //    proc.Kill();
                //    return new Tuple<string, string, string, string>("TIMEOUT", "UNKNOWN", "TIMEOUT", "TIMEOUT");
                //}
                #endregion 
                Console.WriteLine("\tEND Executing {0} {1}", binaryName, arguments);
                return new Tuple<int, bool, List<Tuple<int, int>>>(BenchmarkCount(output), FoundLoop(output), MergedAsserts(output));
            }
            catch (Exception e)
            {
                Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
                return new Tuple<int, bool, List<Tuple<int, int>>>(-1, false, null);
            }
        }

        private static void RegisterResult(string directory, string tag, int i, bool foundLoops, int option, BoogieResult result, int timeInSeconds)
        {
          if (!results.ContainsKey(directory))
          {
            results[directory] = new List<Tuple<string, int, bool, int, BoogieResult, int>>();
          }
          results[directory].Add(Tuple.Create(tag, i, foundLoops, option, result, timeInSeconds));
        }

        private static void GenerateResultOutput(string resultFileName, Tuple<int,int,int> stats)
        {
          Dictionary<string,int> sum = new Dictionary<string,int>();
          TextWriter output = new StreamWriter(resultFileName); 
          foreach (string directory in results.Keys)
          {
            List<Tuple<string, int, bool, int, BoogieResult,int>> entries = results[directory].OrderBy(x => x.Item2).ToList();
            foreach (Tuple<string, int, bool, int, BoogieResult,int> entry in entries)
            {
              output.WriteLine(directory + "<" + entry.Item1 + "," + entry.Item2.ToString() + "> : " +
                  entry.Item5 + (entry.Item3 ? "[LOOP]" : "") + ("[option:" + entry.Item4 + "]") + ("[time:" + entry.Item6 + "]"));
              if (!sum.ContainsKey(entry.Item1))
              {
                sum[entry.Item1] = entry.Item6;
              }
              else
              {
                sum[entry.Item1] += entry.Item6;
              }
            }
          }
          foreach (string s in sum.Keys)
          {
            output.WriteLine("[{0}]: {1}", s, sum[s]);
          }
          output.WriteLine("Stats Verified: {0}", stats.Item1);
          output.WriteLine("Stats Error: {0}", stats.Item2);
          output.WriteLine("Stats Unknown: {0}", stats.Item3);
          output.Flush();
          output.Close();
        }

    }
}
