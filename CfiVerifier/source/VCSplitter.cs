﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.IO;
using System.Diagnostics;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;

namespace CfiVerifier
{
    public class VCSplitter : StandardVisitor
    {
        private static VCSplitter instance;
        private static List<Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType>> assertions;
        private static Implementation original_impl;

        private string current_label; //ugly hack of using global
        private string target_label; //ugly hack of using global
        private Cmd target_typedCmd;
        private AssertCmd target_assertion;
        private bool target_acquired;
        private bool splitting = false;

        private VCSplitter() { }

        public static void LaunchVCSplitter(Implementation impl)
        {
            instance = new VCSplitter();
            assertions = new List<Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType>>();
            original_impl = new Duplicator().VisitImplementation(impl);
        }

        public static VCSplitter Instance
        {
            get
            {
                Utils.Assert(instance != null, "Must invoke launchService before getting instance");
                return instance;
            }
        }

        public override Block VisitBlock(Block node)
        {
            this.current_label = node.Label;
            return base.VisitBlock(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (this.splitting && c is AssertCmd && QKeyValue.FindBoolAttribute((c as AssertCmd).Attributes, "source_assert"))
                    continue;
                if (this.current_label == this.target_label && EquivalentCmd(c, this.target_typedCmd))
                {
                    newCmdSeq.Add(this.target_assertion);
                    this.target_acquired = true;
                }
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }

        //precondition: each block contains at most one assert with SlashVerifyCommandType attribute,
        //              which is true since we use a block for each instruction
        private bool EquivalentCmd(Cmd c1, Cmd c2)
        {
            //Note: The assumption here is that we only instrument assignments and attributed-asserts in the original sourcefile
            if (c1.GetType() != c2.GetType()) { return false; }
            if (c1 is AssignCmd && c2 is AssignCmd)
            {
                AssignCmd c1_assignment = c1 as AssignCmd;
                AssignCmd c2_assignment = c2 as AssignCmd;
                //ASSUME: only 1 assignment to a variable in a block
                return ((c1_assignment.Lhss[0].DeepAssignedVariable == c2_assignment.Lhss[0].DeepAssignedVariable) &&
                    (c1_assignment.Rhss[0].ToString() == c2_assignment.Rhss[0].ToString())); //TODO: need better equality here
            }
            else if (c1 is AssertCmd && c2 is AssertCmd)
            {
                AssertCmd c1_assertion = c1 as AssertCmd;
                AssertCmd c2_assertion = c2 as AssertCmd;
                string c1_attribute = QKeyValue.FindStringAttribute(c1_assertion.Attributes, "SlashVerifyCommandType");
                string c2_attribute = QKeyValue.FindStringAttribute(c2_assertion.Attributes, "SlashVerifyCommandType");
                return (c1_attribute != null && c2_attribute != null && c1_attribute.Equals(c2_attribute));
            }
            return false;
        }

        public void RecordAssertion(string label, Cmd typedCmd, AssertCmd assertion, SlashVerifyCmdType cmdType)
        {
            if (!Options.splitFiles) { return; }
            assertions.Add(new Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType>(label, typedCmd, assertion, cmdType));
        }

        public int getCurrentAssertionCount()
        {
            return assertions.Count();
        }

        public Implementation instrumentAssertion(Implementation impl, string label, Cmd typedCmd, AssertCmd assertion)
        {
            Implementation new_impl = new Duplicator().VisitImplementation(impl);
            this.target_label = label;
            this.target_typedCmd = typedCmd;
            this.target_assertion = assertion;
            if (this.target_assertion.Attributes != null)
            {
                this.target_assertion.Attributes.AddLast(new QKeyValue(Token.NoToken, "source_assert", new List<object> (), null));
            }
            else
            {
                this.target_assertion.Attributes = new QKeyValue(Token.NoToken, "source_assert", new List<object> (), null);
            }
            this.target_acquired = false;
            this.Visit(new_impl); //this step performs the instrumentation
            Utils.Assert(target_acquired, "Unable to instrument assertion: " + assertion.ToString() + " at label " + label);
            return new_impl;
        }

        private static bool ExecuteBoogieBinary(string arguments)
        {
            var delim = Options.IsLinux() ? @"/" : @"\";
            string binaryName = @"." + delim + "references" + delim + "Boogie.exe";
			//string binaryName = @"../../../references/Boogie.exe";
            Utils.Assert(File.Exists(binaryName), "Could not find provided Boogie executable!");
            //Func<string, string> ProcessOutput = delegate(string s) { return ("The number of lines in output = " + s.Split('\n').Count().ToString()); };
            Func<string, bool> result = delegate(string s)
            {
                if (s.Contains("Boogie program verifier finished with 1 verified, 0 errors")) { return true; }
                else { return false; }
            };

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
                proc.Start();
                string output = "";
                output = proc.StandardOutput.ReadToEnd();
                proc.WaitForExit();
                //Console.WriteLine("\tEND Executing {0} {1}", binaryName, arguments);
                return result(output);
            }
            catch (Exception e)
            {
                //Console.WriteLine("\tEND Executing {0} {1} with Exception {2}", binaryName, arguments, e);
                return false;
            }
        }

        private static void AddSolver(List<Tuple<string, string>> solvers, string solverName, string solverPath, string solverFlags) {
          if (File.Exists(solverPath))
            solvers.Add(new Tuple<string, string>(solverName, @"/z3exe:" + solverPath + " " + solverFlags));
        }

        System.Collections.Concurrent.ConcurrentDictionary<int, bool> shared_result_struct;
        public Dictionary<Tuple<string, Cmd, AssertCmd>, bool> VerifyInstrumentedProcedures(Program prog)
        {
            Dictionary<Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType>, int> intermediate = new Dictionary<Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType>, int>();
            Dictionary<Tuple<string, Cmd, AssertCmd>, bool> result = new Dictionary<Tuple<string, Cmd, AssertCmd>, bool>();
            int numAssertions = 0;
            foreach (Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType> assertion in assertions)
            {
                var filename = Options.outputPath + @"/" + Options.splitFilesDir + @"/intermediate_" + numAssertions.ToString() + ".bpl";

                StringWriter sw = new StringWriter();
                TokenTextWriter ttw = new TokenTextWriter(sw);
                Program new_prog = new Program();
                Implementation new_impl = null;
                foreach (Declaration d in prog.TopLevelDeclarations)
                    if (!(d is Implementation))
                        new_prog.AddTopLevelDeclaration(d);
                    else
                    {
                        this.splitting = true;
                        new_impl = instrumentAssertion(original_impl, assertion.Item1, assertion.Item2, assertion.Item3);
                        new_prog.AddTopLevelDeclaration(new_impl);
                    }
                new_prog.Emit(ttw);
                Utils.ParseString(sw.ToString(), out new_prog);
                RemoveCodeBranches.Run(new_impl);
                (new Slicer(new_prog)).Visit(new_prog);
                sw.Close();
                ttw.Close();
                ttw = new TokenTextWriter(filename);
                new_prog.Emit(ttw);
                ttw.Close();
                intermediate[assertion] = numAssertions;
                numAssertions++;
            }

            shared_result_struct = new System.Collections.Concurrent.ConcurrentDictionary<int, bool>();

            //Parallel.For(0, numAssertions, new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount }, i => CheckAssertion(i));
            var delim = Options.IsLinux() ? @"/" : @"\";
            List<Tuple<string, string>> solvers = new List<Tuple<string, string>>();
            AddSolver(solvers, "Z3_441", @"." + delim + "references" + delim + "z3.4.4.1.exe", "/z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0");
            AddSolver(solvers, "Z3_441", @"../../../references/z3.4.4.1.exe", "/z3opt:smt.RELEVANCY=0 /z3opt:smt.CASE_SPLIT=0");

            // work stealing parallel implementation
            workItems = new System.Collections.Concurrent.ConcurrentBag<Tuple<string, string, int>>();
            foreach (Tuple<string, string> solver in solvers)
                for (int i = 0; i < numAssertions; i++)
                    workItems.Add(new Tuple<string, string, int>(solver.Item1, solver.Item2, i));


            var threads = new List<Thread>();
            for (int i = 0; i < Environment.ProcessorCount; i++)
            {
                threads.Add(new Thread(new ThreadStart(CheckAssertions)));
            }

            threads.Iter(t => t.Start());
            threads.Iter(t => t.Join());


            foreach (Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType> assertion in assertions)
            {
                result[new Tuple<string, Cmd, AssertCmd>(assertion.Item1, assertion.Item2, assertion.Item3)] =
                    shared_result_struct[intermediate[assertion]];
            }
            return result;
        }

        private System.Collections.Concurrent.ConcurrentBag<Tuple<string, string, int>> workItems;

        private void CheckAssertions()
        {
            while (true)
            {
                // grab work
                Tuple<string, string, int> work;
                if (!workItems.TryTake(out work)) break;
                if (!shared_result_struct.ContainsKey(work.Item3))
                {
                    CheckAssertion(work.Item1, work.Item2, work.Item3);
                }
            }
        }

        private void CheckAssertion(string solverName, string solverCallArg, int i)
        {
            string args = Options.outputPath + @"/" + Options.splitFilesDir + @"/intermediate_" + i.ToString() + ".bpl " +
                solverCallArg + @" /timeLimit:10 /errorLimit:1";
            bool boogie_result = ExecuteBoogieBinary(args);
            shared_result_struct.AddOrUpdate(i, boogie_result, (x,y) => boogie_result);
        }

        public void PrintAssertionTypes()
        {
            Func<SlashVerifyCmdType, String> printCmdType = delegate(SlashVerifyCmdType x)
            {
                switch (x)
                {
                    case SlashVerifyCmdType.Store8: { return "STORE8"; }
                    case SlashVerifyCmdType.Store16: { return "STORE16"; }
                    case SlashVerifyCmdType.Store32: { return "STORE32"; }
                    case SlashVerifyCmdType.Store64: { return "STORE64"; }
                    case SlashVerifyCmdType.Call: { return "CALL"; }
                    case SlashVerifyCmdType.RemoteJmp: { return "REMOTEJMP"; }
                    case SlashVerifyCmdType.RemoteIndirectJmp: { return "REMOTEINDIRECTJMP"; }
                    case SlashVerifyCmdType.RepStosB: { return "REPSTOSB"; }
                    case SlashVerifyCmdType.Ret: { return "RET"; }
                    case SlashVerifyCmdType.SetRSP: { return "SETRSP"; }
                    default: { return "INVALID"; }
                }
            };

            int assertionCounter = 0;
            foreach (Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType> assertion in assertions)
            {

                Console.Write("VCSplitter found split id " + assertionCounter + " with type " + printCmdType(assertion.Item4) );
                assertionCounter++;
            }
        }

        public void PrintInstrumentedProcedures(Program prog)
        {
            if (!Options.splitFiles) { return; }

            int impl_counter = 0;
            foreach (Tuple<string, Cmd, AssertCmd, SlashVerifyCmdType> assertion in assertions)
            {
                string tag = Options.tag != "" ? @"." + Options.tag : "";
                var filename = Options.outputPath + @"/" + Options.splitFilesDir + @"/split_" + impl_counter.ToString() + tag + @".bpl";
                StringWriter sw = new StringWriter();
                TokenTextWriter ttw = new TokenTextWriter(sw);
                Program new_prog = new Program();
                Implementation new_impl = null;
                foreach (Declaration d in prog.TopLevelDeclarations)
                    if (!(d is Implementation))
                        new_prog.AddTopLevelDeclaration(d);
                    else
                    {
                        new_impl = instrumentAssertion(original_impl, assertion.Item1, assertion.Item2, assertion.Item3);
                        new_prog.AddTopLevelDeclaration(new_impl);
                    }
                new_prog.Emit(ttw);
                Utils.ParseString(sw.ToString(), out new_prog);
                Console.WriteLine("Now analysing split {0}.", impl_counter);
                (new Slicer(new_prog)).Visit(new_prog);
                sw.Close();
                ttw.Close();
                ttw = new TokenTextWriter(filename);
                new_prog.Emit(ttw);
                ttw.Close();
                impl_counter++;
            }
            Console.WriteLine("VCSplitter generated {0} assertions", assertions.Count);
        }

    }

}
