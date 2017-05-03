using System;
using CommandLineTools;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.IO;
using System.Xml;

namespace RandomSearch
{
    public enum BoogieResult { VERIFIED, ERROR, TIMEOUT };

    class SearchConfig {
        public int maxChoiceCount {get; set;}
        public int minChoiceCount {get; set;}
        public int runCount {get; set;}
        public string helperBinaryPath {get; set;}

        public string outputFolder {get; set;}
        public string outputTempName {get; set;}

        public SearchConfig(int maxCC, int minCC, int rC, string hBP, string oF, string oTN) {
            this.maxChoiceCount = maxCC;
            this.minChoiceCount = minCC;
            this.runCount = rC;
            this.helperBinaryPath = hBP;
            this.outputFolder = oF;
            this.outputTempName = oTN;
        }

        public SearchConfig(string XMLConfigPath) {
            XmlDocument config = new XmlDocument();
            config.Load(XMLConfigPath);
            XmlNode constantsRootNode = config.SelectSingleNode("/RandomSearch/Constants");
            XmlNode pathsRootNode = config.SelectSingleNode("/RandomSearch/Paths");

            this.maxChoiceCount = Int32.Parse(constantsRootNode.SelectSingleNode("MaxChoiceCount").InnerText);
            this.minChoiceCount = Int32.Parse(constantsRootNode.SelectSingleNode("MinChoiceCount").InnerText);
            this.runCount = Int32.Parse(constantsRootNode.SelectSingleNode("RunCount").InnerText);
            this.outputFolder = pathsRootNode.SelectSingleNode("OutputFolder").InnerText;
            this.outputTempName = pathsRootNode.SelectSingleNode("OutputTempName").InnerText;
            this.helperBinaryPath = pathsRootNode.SelectSingleNode("BinaryPath").InnerText;
        }
    }

    class ExecuteSearch
    {
        private static SearchConfig config = new SearchConfig("/home/sentenced/Documents/slashconf/slashconfidential/RandomSearch/SlashConfRandomSearchConfig.xml");

        private static List<CommandLineTools.ProgramChoice> duplicateChoices =
            new List<CommandLineTools.ProgramChoice> {
                CommandLineTools.ProgramChoice.SLICE,
                CommandLineTools.ProgramChoice.SPLIT_MEMORY,
        };

        private static List<CommandLineTools.ProgramChoice> forbiddenChoices =
            new List<CommandLineTools.ProgramChoice> {
                CommandLineTools.ProgramChoice.VERIFY,
                CommandLineTools.ProgramChoice.GRAPH_DOT,
                CommandLineTools.ProgramChoice.GRAPH_DGML,
                CommandLineTools.ProgramChoice.EXTRACT_LOADS
        };



        public static void Main(string[] args) {
            if (args.Length != 1) {
                System.Console.WriteLine("Required argument: input Boogie file or folder with containing files.");
                return;
            }

            if (Directory.Exists(config.outputFolder)) {
                Directory.Delete(config.outputFolder, true);
            }
            Directory.CreateDirectory(config.outputFolder);
            if (!(File.Exists(args[0]) || Directory.Exists(args[0]))) {
                System.Console.WriteLine("Given path does not exist!");
                return;
            }
            Random randomChoice = new Random(42);
            if (Directory.Exists(args[0])) {
                foreach (string file in
                    Directory.EnumerateFiles(args[0]).Where(i => i.ToLower().Contains(".bpl"))) {
                    TreeNode startNode = new TreeNode(ProgramChoice.SIMPLIFY_CONSTANT_EXPRS);
                    TreeNode startNodeChild = startNode.CreateChild(ProgramChoice.SLICE);
                    startNodeChild.SetTreeChild(Tree.CreateRandomTree(randomChoice, 3, 3));
                    new Tree(startNode).VerifyTree(file, 500);
                }
            }
            else {
                TreeNode startNode = new TreeNode(ProgramChoice.SIMPLIFY_CONSTANT_EXPRS);
                TreeNode startNodeChild = startNode.CreateChild(ProgramChoice.SLICE);
                startNodeChild.SetTreeChild(Tree.CreateRandomTree(randomChoice, 3, 3));
                new Tree(startNode).PruneTree(args[0]);
                new Tree(startNode).VerifyTree(args[0], 500);
            }
        }

        public static void RunOnce(string inputFile, Random randomChoice) {
            /* Choice string, verified, time taken (s) */
            List<Tuple<string, bool, int>> results = new List<Tuple<string, bool, int>>();
            Stopwatch sw = new Stopwatch();
            for (int i = 0; i < config.runCount; i++) {
                System.Console.WriteLine("*** Run count " + i);
                Process runInstance = new Process();
                String choiceString = GetChoices(randomChoice);
                runInstance.StartInfo.UseShellExecute = false;
                runInstance.StartInfo.FileName = config.helperBinaryPath;
                runInstance.StartInfo.Arguments = choiceString + @" " + inputFile + @" " + config.outputTempName;
                runInstance.StartInfo.RedirectStandardOutput = true;
                Console.WriteLine(runInstance.StartInfo.FileName + " " + runInstance.StartInfo.Arguments);
                sw.Start();
                runInstance.Start();
                runInstance.WaitForExit();
                sw.Stop();
                string boogieVerifyOutput = runInstance.StandardOutput.ReadToEnd();
                System.Console.WriteLine(boogieVerifyOutput);
                results.Add(new Tuple<string, bool, int>(choiceString,
                    boogieVerifyOutput.Contains("1 verified"),
                    (int) (sw.ElapsedMilliseconds / 1000)));
                if (boogieVerifyOutput.Contains("1 verified")) {
                    File.Copy(inputFile, config.outputFolder + inputFile.Split('/').Last().Split('.').First() + "_" + i + ".bpl");
                }

            }
            foreach (Tuple<string, bool, int> entry in results) {
                System.Console.WriteLine("Choice string: " + entry.Item1);
                System.Console.WriteLine("Verified: " + (entry.Item2 ? "Yes" : "No"));
                System.Console.WriteLine("Time taken: " + entry.Item3 + "s");
                System.Console.WriteLine("------------------------------");
            }
        }

        public static BoogieResult VerifySequence(string sequence, string inputFile, int timeout) {
            Debug.Assert(!sequence.Contains("VERIFY"));
            sequence += ",VERIFY_" + timeout;
            Console.WriteLine("***** Verifying random sequence: " + sequence + "; timeout = " + timeout + "s");
            Process verifyInstance = new Process();
            verifyInstance.StartInfo.UseShellExecute = false;
            verifyInstance.StartInfo.FileName = config.helperBinaryPath;
            verifyInstance.StartInfo.Arguments = sequence + @" " + inputFile + @" " + config.outputTempName;
            verifyInstance.StartInfo.RedirectStandardOutput = true;
            Console.WriteLine(verifyInstance.StartInfo.FileName + " " + verifyInstance.StartInfo.Arguments);
            verifyInstance.Start();
            verifyInstance.WaitForExit();
            string boogieVerifyOutput = verifyInstance.StandardOutput.ReadToEnd();
            System.Console.WriteLine(boogieVerifyOutput);
            if (boogieVerifyOutput.Contains("1 verified"))
                return BoogieResult.VERIFIED;
            if (boogieVerifyOutput.Contains("1 error"))
                return BoogieResult.ERROR;
            if (boogieVerifyOutput.Contains("1 time out"))
                return BoogieResult.TIMEOUT;
            Debug.Assert (false);
            return BoogieResult.ERROR;
        }

        public static String GetChoices(Random randomChoice)
        {
            int choiceCount = 0;
            CommandLineTools.ProgramChoice currChoice;
            String choiceString = "";
            List<CommandLineTools.ProgramChoice> choiceValues =
                Enum.GetValues(typeof(CommandLineTools.ProgramChoice))
                    .Cast<CommandLineTools.ProgramChoice>()
                    .ToList();
            choiceValues = choiceValues.Except(forbiddenChoices).ToList();
            while (choiceCount <= config.maxChoiceCount)
            {
                currChoice = choiceValues.ElementAt(randomChoice.Next(choiceValues.Count));
                if (!duplicateChoices.Contains(currChoice))
                    choiceValues.Remove(currChoice);
                choiceString += currChoice.ToString() + ",";
                if (choiceCount > config.minChoiceCount && randomChoice.Next(config.maxChoiceCount) < choiceCount)
                    break;
                choiceCount++;
            }
            choiceString += "GRAPH_DOT,VERIFY";
            return choiceString;
        }

        // TODO: Make this general, taking a list of passes and how many insertions;
        private static string InsertSplitMemory(string sequence, int maxCount) {
            Random randomInsert = new Random();
            List<string> splitSequence = sequence.Split(',').ToList();
            for (int i = 0; i < maxCount; i++) {
                splitSequence.Insert(randomInsert.Next(splitSequence.Count), "SPLIT_MEMORY");
                if (randomInsert.Next(maxCount) <= i)
                    break;
            }
            return String.Join(",", splitSequence);
        }
    }
}
