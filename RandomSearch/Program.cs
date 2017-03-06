﻿using System;
using CommandLineTools;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace RandomSearch
{
	class ExecuteSearch
	{
		private const int maxChoiceCount = 15;
		private const int minChoiceCount = 5;
		private const int runCount = 5;
		private const String outputTmpName = "out.tmp";

		private static String binaryPath = "/home/sentenced/Documents/slashconf/slashconfidential/CommandLineTools/bin/Debug/CommandLineTools.exe";


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
				System.Console.WriteLine("Required argument: input Boogie file.");
				return;
			}
			String inputFile = args[0];
			Random randomChoice = new Random(42);
			/* Choice string, verified, time taken (s) */
			List<Tuple<string, bool, int>> results = new List<Tuple<string, bool, int>>();
			Stopwatch sw = new Stopwatch();
			for (int i = 0; i < runCount; i++) {
				Process runInstance = new Process();
				String choiceString = GetChoices(randomChoice);
				runInstance.StartInfo.UseShellExecute = false;
				runInstance.StartInfo.FileName = binaryPath;
				runInstance.StartInfo.Arguments = choiceString + @" " + inputFile + @" " + outputTmpName;
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
			}
			foreach (Tuple<string, bool, int> entry in results) {
				System.Console.WriteLine("Choice string: " + entry.Item1);
				System.Console.WriteLine("Verified: " + (entry.Item2 ? "Yes" : "No"));
				System.Console.WriteLine("Time taken: " + entry.Item3 + "s");
				System.Console.WriteLine("------------------------------");
			}
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
			while (choiceCount <= maxChoiceCount)
			{
				currChoice = choiceValues.ElementAt(randomChoice.Next(choiceValues.Count));
				if (!duplicateChoices.Contains(currChoice))
					choiceValues.Remove(currChoice);
				choiceString += currChoice.ToString() + ",";
				if (choiceCount > minChoiceCount && randomChoice.Next(maxChoiceCount) < choiceCount)
					break;
				choiceCount++;
			}
			choiceString += "GRAPH_DOT,VERIFY";
			return choiceString;
		}
	}
}