﻿using System;
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

  class CfiDriver
    {
        enum BoogieResult { VERIFIED, ERROR, UNKNOWN };

        static bool verbose = true;
        static string resultFileName = @"ResultSummary_" + DateTime.Now.Hour.ToString() + "_" 
            + DateTime.Now.Minute.ToString() + "_" + DateTime.Now.Second.ToString() + ".txt";

        //key: directory, value: [tag, splitId, attributes, boogieResult, timeInSeconds]
        static Dictionary<string, List<Tuple<string,int,ProgramAttributes,BoogieResult,int>>> results;
        static List<Tuple<string, string, string, string>> benchmarks; //<directory, input bpl, options, run_type_name>

        private void Usage()
        {
            Console.WriteLine("Usage:\n");
            Console.WriteLine("CfiDriver.exe [options]");
        }
        static void Main(string[] args)
        {
            Console.WriteLine("Environment has {0} processors", Environment.ProcessorCount);
            results = new Dictionary<string, List<Tuple<string, int, ProgramAttributes, BoogieResult, int>>>();
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

            if (!args.Contains("/option:norun"))
            {
                GenerateResultOutput(resultFileName, stats);
            }
        }

        public static Tuple<int, int, int> RunBenchmarks(List<Tuple<string, string, string, string>> benchmarks, bool doNotRunBenchmarks, bool splitMemory, bool optimizeStore, bool optimizeLoad)
        {
          //item1 = benchmarks\StackExample\func_0000000000001000, item2 = dllfunc.bpl, item3 = "", item4 = "baseline"
          var delim = Options.IsLinux() ? @"/" : @"\";
          int numVerified = 0, numError = 0, numUnknown = 0;
          if (splitMemory)
          {
              optimizeLoad = true;
              optimizeStore = true;
          }

          //item1: directory, item2: bpl file, item3: options, item4: tag
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
              ProgramAttributes attributes = ExecuteCfiVerifierBinary(args);

              if (attributes.numSplits < 0)
              {
                  Console.WriteLine("Benchmark " + benchmark.Item1 + " did not generate any assertions");
                  continue;
              }
              Console.WriteLine("\tFOUND {0} assertions in benchmark {1}, Running them in parallel...", 
                  attributes.numSplits, 
                  benchmark.Item1);
              if (!doNotRunBenchmarks) {
                  CheckAssertionsInParallel(benchmark.Item1, benchmark.Item4, attributes);
                  Tuple<int, int, int> stats = ComputeStatisticsForDirectory(benchmark.Item1);
                  numVerified += stats.Item1;
                  numError += stats.Item2;
                  numUnknown += stats.Item3;
                  EmitBenchmarkResults(resultFileName, benchmark.Item1);
              }

              // generate a script in case we want to run benchmarks later manually
              //TextWriter fileWriter = new StreamWriter("script");
              //for (int i = 0; i < attributes.numSplits; i++)
              //{
              //    string boogie_args = @" " + benchmark.Item1 + delim + @"split_" + i.ToString() + @"." + 
              //        benchmark.Item4 + ".bpl /timeLimit:" + Options.timeoutPerProcess + 
              //        @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0 /errorLimit:1";
              //    string boogie_bin = @"." + delim + "references" + delim + "Boogie.exe";
              //    fileWriter.WriteLine(boogie_bin + boogie_args);
              //}
              //fileWriter.Flush();
              //fileWriter.Close();
          }

          return new Tuple<int, int, int>(numVerified, numError, numUnknown);
        }

        private static Tuple<int, int, int> ComputeStatisticsForDirectory(string directory)
        {
            // results[directory].Add(Tuple.Create(tag, i, foundLoops, option, result, timeInSeconds));
            int numVerified = 0, numError = 0, numUnknown = 0;
            if (!results.ContainsKey(directory)) { return new Tuple<int, int, int>(0, 0, 0); }
            foreach (Tuple<string, int, ProgramAttributes, BoogieResult, int> t in results[directory])
            {
              if (t.Item4 == BoogieResult.VERIFIED) { numVerified++; }
              if (t.Item4 == BoogieResult.ERROR) { numError++; }
              if (t.Item4 == BoogieResult.UNKNOWN) { numUnknown++; }
            }
            return new Tuple<int, int, int>(numVerified, numError, numUnknown);
        }

        private static System.Collections.Concurrent.ConcurrentBag<Tuple<string, string, int, ProgramAttributes>> workItems;

        private static void CheckAssertionsInParallel(string directory, string tag, ProgramAttributes attributes)
        {
            //Parallel.For(0, attributes.numSplits, 
            //  new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount },
            //  i => CheckAssertion(directory, tag, i, attributes));

            // work stealing parallel implementation 
            workItems = new System.Collections.Concurrent.ConcurrentBag<Tuple<string, string, int, ProgramAttributes>>();
            for (int i = 0; i < attributes.numSplits; i++)
                workItems.Add(Tuple.Create(directory, tag, i, attributes));

            var threads = new List<Thread>();
            for (int i = 0; i < Environment.ProcessorCount; i++)
            {
                threads.Add(new Thread(new ThreadStart(CheckAssertions)));
            }

            threads.ForEach(t => t.Start());
            threads.ForEach(t => t.Join());

        }
        private static void CheckAssertions()
        {
            while (true)
            {
                // grab work
                Tuple<string, string, int, ProgramAttributes> work;
                if (!workItems.TryTake(out work)) break;

                CheckAssertion(work.Item1, work.Item2, work.Item3, work.Item4);
            }
        }

        private static void CheckAssertion(string directory, string tag, int splitId, ProgramAttributes attributes)
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

            string args0 = @" " + directory + delim + @"split_" + splitId.ToString() + @"." + tag + ".bpl /timeLimit:" + Options.timeoutPerProcess;
            string args1 = args0 + @" /contractInfer /z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0 /errorLimit:1";

            //item1: error / unknown / verified, item2: time spent in boogie
            Tuple<BoogieResult, int> args1_result = ExecuteBoogieBinary(args1);
            RegisterResult(directory, tag, splitId, attributes, args1_result.Item1, args1_result.Item2);

        }

        private static Tuple<BoogieResult, int> ExecuteBoogieBinary(string arguments)
        {
          var delim = Options.IsLinux() ? @"/" : @"\";
          string binaryName = @"." + delim + "references" + delim + "Boogie.exe";
          //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
          Func<string, BoogieResult> result = delegate(string s)
          {
            if (s.Contains("Boogie program verifier finished with 1 verified, 0 errors")) { return BoogieResult.VERIFIED; }
            else if (s.Contains("Boogie program verifier finished with 0 verified, 1 error") && 
                     s.Contains("This assertion might not hold")) { return BoogieResult.ERROR; }

            return BoogieResult.UNKNOWN;
          };

          if (verbose)
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
            if (verbose)
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

        public struct ProgramAttributes
        {
            public int numSplits;  //how many asserts do we have?
            public bool foundLoop; //does this benchmark program contain a loop?
            public Dictionary<int, String> assertionTypes; //what kind of statement does the assertion capture?
            public int numBasicBlocks; //number of basic blocks
        }

        // first: number of assertions, second: found a loop
        private static ProgramAttributes ExecuteCfiVerifierBinary(string arguments)
        {
            string binaryName = GetBinaryPath() + @"CfiVerifier.exe";
            //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
            Func<string, int> BenchmarkCount = delegate(string s)
            {
                string HEADER = "VCSplitter generated ";
                string BODY = " assertions";

                if (s.Contains(HEADER) && s.Contains(BODY))
                {
                  string countString = s.Split(new string[] { HEADER }, StringSplitOptions.None)[1].
                                         Split(new string[] { BODY }, StringSplitOptions.None)[0];
                  return Int32.Parse(countString);
                }

                return -1;
            };

            Func<string, bool> FoundLoop = delegate(string s)
            {
                return (s.Contains("CfiVerifier found one or more loops"));
            };

            Func<string, int> BasicBlockCount = delegate(string s)
            {
                string HEADER = "CfiVerifier found ";
                string BODY = " basic blocks";

                if (s.Contains(HEADER) && s.Contains(BODY))
                {
                    string countString = s.Split(new string[] { HEADER }, StringSplitOptions.None)[1].
                                           Split(new string[] { BODY }, StringSplitOptions.None)[0];
                    return Int32.Parse(countString);
                }
                return -1;
            };

            Func<string, Dictionary<int, String>> AssertionType = delegate(string input)
            {
                String HEADER = "VCSplitter found split id ";
                String BODY = " with type ";
                //Console.WriteLine(s);
                Dictionary<int,string> result = new Dictionary<int, string>();
                String[] splits = input.Split(new String[] { HEADER }, StringSplitOptions.None);
                foreach (String s in splits) {
                    if (!s.Contains(BODY)) { continue; }
                    int splitId = Int32.Parse(s.Split(new String[] { BODY }, StringSplitOptions.None)[0]);
                    string assertionType = s.Split(new String[] { BODY }, StringSplitOptions.None)[1];
                    result.Add(splitId, assertionType);
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

                ProgramAttributes attributes = new ProgramAttributes();
                attributes.foundLoop = FoundLoop(output);
                attributes.numSplits = BenchmarkCount(output);
                attributes.assertionTypes = AssertionType(output);
                attributes.numBasicBlocks = BasicBlockCount(output);

                return attributes;
            }
            catch (Exception e)
            {
                ProgramAttributes attributes = new ProgramAttributes();
                attributes.foundLoop = false;
                attributes.numSplits = -1;

                Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
                return attributes;
            }
        }

        private static void RegisterResult(
            string directory, 
            string tag, 
            int splitId, 
            ProgramAttributes attributes,
            BoogieResult result, 
            int timeInSeconds )
        {
          if (!results.ContainsKey(directory))
          {
            results[directory] = new List<Tuple<string, int, ProgramAttributes, BoogieResult, int>>();
          }
          results[directory].Add(Tuple.Create(tag, splitId, attributes, result, timeInSeconds));
        }

        private static void EmitBenchmarkResults(string resultFileName, string directory)
        {
            TextWriter tw = new StreamWriter(resultFileName, true);
            List<Tuple<string, int, ProgramAttributes, BoogieResult, int>> entries = results[directory].OrderBy(x => x.Item2).ToList();
            foreach (Tuple<string, int, ProgramAttributes, BoogieResult, int> entry in entries)
            {
                tw.WriteLine(directory + "<" + entry.Item1 + "," + entry.Item2.ToString() + "> :" +
                  entry.Item4 +
                  "[" + entry.Item3.assertionTypes[entry.Item2] + "]" +
                  "[blocks:" + entry.Item3.numBasicBlocks.ToString() + "]" +
                  (entry.Item3.foundLoop ? "[LOOP]" : "[NOLOOP]") + 
                  ("[time:" + entry.Item5 + "]"));
            }
            tw.WriteLine("==== " + directory + " total duration:" + results[directory].Sum(i => i.Item5));
            tw.Flush();
            tw.Close();
        }

        private static void GenerateResultOutput(string resultFileName, Tuple<int,int,int> stats)
        {
          Dictionary<string,int> sum = new Dictionary<string,int>();
          TextWriter output = new StreamWriter(resultFileName, true); 
          foreach (string directory in results.Keys)
          {
            List<Tuple<string, int, ProgramAttributes, BoogieResult,int>> entries = results[directory].OrderBy(x => x.Item2).ToList(); // order by split id
            foreach (Tuple<string, int, ProgramAttributes, BoogieResult,int> entry in entries)
            {
                sum[entry.Item1] = !sum.ContainsKey(entry.Item1) ? entry.Item5 : sum[entry.Item1] + entry.Item5;
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
          Console.WriteLine("Log file saved in " + resultFileName + ".");
        }

    }
}
