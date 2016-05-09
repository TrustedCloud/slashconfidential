using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;
using System.Threading;
using System.Collections.Concurrent;

namespace z3flagoptimizer
{


    class Program {

        static readonly string[] flags = {
@"(set-option :pp.bv_literals false)",
@"(set-option :smt.PHASE_SELECTION 0)",
@"(set-option :smt.RESTART_STRATEGY 0)",
@"(set-option :smt.RESTART_FACTOR |1.5|)",
@"(set-option :smt.ARITH.RANDOM_INITIAL_VALUE true)",
@"(set-option :smt.CASE_SPLIT 3)",
@"(set-option :smt.CASE_SPLIT 0)",
@"(set-option :smt.RELEVANCY 0)",
@"(set-option :smt.DELAY_UNITS true)",
@"(set-option :NNF.SK_HACK true)",
@"(set-option :smt.MBQI false)",
@"(set-option :smt.QI.EAGER_THRESHOLD 100)",
@"(set-option :smt.BV.REFLECT true)"
                                             };

        static string z3Exe = "";
        static bool[] counter = null;
        static bool work_done = false;
        static string[] query = null;

        static void Main(string[] args)
        {
            Console.CancelKeyPress += Console_CancelKeyPress;

            z3Exe = Path.Combine(Environment.CurrentDirectory, "z3.exe");
            if (!File.Exists(z3Exe))
            {
                Console.WriteLine("Z3.exe not found in the current directory. Aborting");
                return;
            }

            if (args.Length < 1)
            {
                Console.WriteLine("Usage: opt.exe query.smt2");
                return;
            }
            if (args.Any(s => s == "/break"))
                System.Diagnostics.Debugger.Launch();

            query = File.ReadAllLines(args[0]);

            // Create work
            counter = new bool[flags.Length];
            for (int i = 0; i < counter.Length; i++)
                counter[i] = false;
            

            var threads = new List<Thread>();
            for (int i = 0; i < Environment.ProcessorCount; i++)
            {
                // Tmp directory
                var dirname = "tmp" + i.ToString();
                if(Directory.Exists(dirname)) Directory.Delete(dirname, true);
                Directory.CreateDirectory(dirname);
                
                var w = new Worker(dirname);
                threads.Add(new Thread(new ThreadStart(w.Run)));
            }

            threads.ForEach(t => t.Start());
            threads.ForEach(t => t.Join());

            Console.WriteLine("Answer not found");
        }

        public class Worker
        {
            string dirname;

            public Worker(string dirname)
            {
                this.dirname = dirname;
            }

            public void Run()
            {
                while (true)
                {
                    var mycopy = new bool[counter.Length];

                    // Get work
                    lock (counter)
                    {
                        if (!work_done)
                        {
                            for (int i = 0; i < counter.Length; i++)
                                mycopy[i] = counter[i];


                            var more_available = GetNext(counter);
                            if (!more_available)
                                work_done = true;
                        }
                    }

                    if (work_done) break;
                    var str = "";
                    for (int i = 0; i < mycopy.Length; i++)
                        str += mycopy[i] ? "1" : "0";

                    Console.WriteLine("Trying {0}", str);
                    var found = RunQuery(dirname, query, mycopy);

                    if (found)
                    {
                        Console.WriteLine("Answer found: {0}", dirname);
                        KillSpawnedProcesses();
                        System.Diagnostics.Process.GetCurrentProcess().Kill();
                    }
                }
            }
        }

        static bool RunQuery(string dir, string []query, bool []counter)
        {
            // Construct the new query
            var nflags = new List<string>();
            for(int i = 0; i < counter.Length; i++)
                if(!counter[i]) nflags.Add(flags[i]);

            var nqeuery = new string[query.Length + nflags.Count];
            for (int i = 0; i < nqeuery.Length; i++)
            {
                nqeuery[i] = (i < nflags.Count) ? nflags[i] : query[i - nflags.Count];
            }
            var queryfile = Path.Combine(dir, "q.smt2");
            File.WriteAllLines(queryfile, nqeuery);

            // run it
            var ret = RunShell(Path.Combine(Environment.CurrentDirectory, dir), z3Exe, "q.smt2");

            if (ret.Any(s => s.Contains("unsat") || s.Contains("sat")))
                return true;

            return false;
        }

        static bool GetNext(bool[] counter)
        {
            int i = 0;
            while (i < counter.Length)
            {
                if (counter[i] == false)
                {
                    counter[i] = true;
                    break;
                }
                counter[i] = false;
                i++;
            }
            if (i == counter.Length) return false;
            return true;
        }

        static bool debugOutput = true;
        static List<Process> SpawnedProcesses = new List<Process>();

        static List<string> RunShell(string dir, string cmd, string args)
        {
            var ret = new List<string>();

            if (debugOutput)
            {
                Console.WriteLine("-----------------------------------");
                Console.WriteLine("Running: " + cmd + " " + args);
            }

            var proc = new System.Diagnostics.Process();
            proc.StartInfo.UseShellExecute = false;
            proc.StartInfo.CreateNoWindow = !debugOutput;
            proc.StartInfo.FileName = cmd;
            proc.StartInfo.Arguments = args;
            proc.StartInfo.WorkingDirectory = dir;
            Debug.Assert(System.IO.Path.IsPathRooted(dir));
            proc.StartInfo.RedirectStandardOutput = true;

            lock (SpawnedProcesses)
            {
                SpawnedProcesses.Add(proc);
            }

            proc.Start();
            var str = proc.StandardOutput.ReadToEnd();
            proc.WaitForExit();


            lock (SpawnedProcesses)
            {
                SpawnedProcesses.Remove(proc);
            }

            foreach (var s in str.Split(new string[] { System.Environment.NewLine, "\n" }, StringSplitOptions.None))
            {
                ret.Add(s);
            }

            if (debugOutput)
            {
                Console.WriteLine("-----------------------------------");
            }

            return ret;
        }

        static void Console_CancelKeyPress(object sender, ConsoleCancelEventArgs e)
        {
            Console.WriteLine("Got Ctrl-C");

            KillSpawnedProcesses();

            System.Diagnostics.Process.GetCurrentProcess()
                .Kill();
        }

        public static void KillSpawnedProcesses()
        {
            lock (SpawnedProcesses)
            {
                foreach (var p in SpawnedProcesses)
                    p.Kill();
                SpawnedProcesses.Clear();
            }
        }
    }
}
