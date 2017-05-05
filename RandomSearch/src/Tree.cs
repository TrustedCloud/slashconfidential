using System;
using CommandLineTools;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace RandomSearch
{
    class TreeNode {
        protected ProgramChoice pass;
        public BoogieResult nodeState {get; set;}

        public List<TreeNode> children {get; set;}
        public TreeNode parent {get; set;}

        public TreeNode(ProgramChoice _pass) {
            this.pass = _pass;
            this.children = new List<TreeNode>();
            this.parent = null;
            this.nodeState = BoogieResult.TIMEOUT;
        }

        public TreeNode CreateChild(ProgramChoice pc) {
            TreeNode newChild = new TreeNode(pc);
            newChild.parent = this;
            this.children.Add(newChild);
            return newChild;
        }

        public void SetNodeChild(TreeNode node) {
            node.parent = this;
            this.children.Add(node);
        }

        public void SetTreeChild(Tree treeChild) {
            treeChild.baseNode.parent = this;
            this.children.Add(treeChild.baseNode);
        }

        public string GetPass() {
            return this.pass.ToString();
        }

        public string ComputeSequence() {
            if (this.parent != null)
                return this.parent.ComputeSequence() + "," + this.GetPass();
            return this.GetPass();
        }
    }

    class Tree {
        public TreeNode baseNode {get; set;}

        public static List<ProgramChoice> allAllowedPasses = new List<ProgramChoice>{
            ProgramChoice.ABSTRACT_MEM,
            ProgramChoice.ABSTRACT_USER_CALL_MEM,
            ProgramChoice.REMOVE_CODE_BRANCHES,
            ProgramChoice.SLICE_ASSUMES,
            ProgramChoice.SLICE_PARTITIONS,
            //ProgramChoice.SPLIT_MEMORY
        };

        public Tree(TreeNode _baseNode) {
            this.baseNode = _baseNode;
        }

        public Tree(ProgramChoice _programChoice) {
            this.baseNode = new TreeNode(_programChoice);
        }

        public List<string> GetAllSequences() {
            List<string> sequences = new List<string>();
            if (baseNode.nodeState.Equals(BoogieResult.VERIFIED) ||
                (!baseNode.children.Any() && !baseNode.nodeState.Equals(BoogieResult.ERROR)))
                sequences.Add(this.baseNode.GetPass());
            else
                foreach (TreeNode child in baseNode.children)
                {
                    Tree childTree = new Tree(child);
                    List<string> childSequences = childTree.GetAllSequences();
                    foreach (string childSeq in childSequences)
                    {
                        sequences.Add(this.baseNode.GetPass() + "," + childSeq);
                    }
                }
            return sequences;
        }

        public void PrintTree() {
            foreach(string sequence in this.GetAllSequences()) {
                Console.WriteLine(sequence);
            }
        }

        private static ProgramChoice GetRandomPass(Random randomChoice, List<ProgramChoice> allowedPasses) {
            return allowedPasses.ElementAt(randomChoice.Next(allowedPasses.Count));
        }

        public void PruneTree(string inputFile) {
            foreach (TreeNode child in this.baseNode.children) {
                child.ComputeSequence();
                BoogieResult result = ExecuteSearch.VerifySequence(child.ComputeSequence(), inputFile, 10);
                child.nodeState = result;
                if (result.Equals(BoogieResult.TIMEOUT))
                    new Tree(child).PruneTree(inputFile);
            }
        }

        public List<string> VerifyAndPruneTree(string inputFile, Random randomChoice, int maxCount = -1, int memSplitCount = 0) {
            List<string> verifiedSequences = new List<string>();
            List<string> toVerify = this.GetAllSequences();
            List<string> invalidSubseqs = new List<string>();
            int count = 0;
            while (toVerify.Any() && count++ < maxCount) {
                string sequence = toVerify.ElementAt(randomChoice.Next(toVerify.Count));
                string splitMemSeq = ExecuteSearch.InsertSplitMemory(sequence, memSplitCount);
                if (invalidSubseqs.Where(i => sequence.StartsWith(i)).Any()) {
                    Console.WriteLine("Found invalid subsequence in given sequence {0}.", sequence);
                    continue;
                }
                BoogieResult sequenceResult = ExecuteSearch.VerifySequence(splitMemSeq, inputFile, 600);
                if (sequenceResult.Equals(BoogieResult.VERIFIED))
                    verifiedSequences.Add(splitMemSeq);
                else if (sequenceResult.Equals(BoogieResult.ERROR)) {
                    Console.WriteLine ("::: Found ERROR sequence - {0}", sequence);
                    string subseq = GetInvalidSubseq(sequence, inputFile);
                    if (subseq != null) {
                        Console.WriteLine ("::: Adding invalid subsequence - {0}", subseq);
                        invalidSubseqs.Add (subseq);
                    }
                }
                toVerify.Remove(sequence);
            }
            return verifiedSequences;
        }

        private string GetInvalidSubseq(string sequence, string inputFile) {
            List<string> splitSeq = sequence.Split(',').ToList();
            int splitIndex = splitSeq.Count;
            int maxSplitCount = (int) Math.Ceiling(Math.Log (splitIndex, 2));
            int lastInvalidSubseqIndex = splitSeq.Count;
            int splitCount = 0;
            while (splitCount <= maxSplitCount) {
                Console.WriteLine (":::: Attempting invalid check for split {0} - {1}", splitCount, String.Join(",", splitSeq.Take(splitIndex)));
                splitCount++;
                if (ExecuteSearch.VerifySequence(String.Join(",", splitSeq.Take(splitIndex)), inputFile, 30).Equals(BoogieResult.ERROR)) {
                    lastInvalidSubseqIndex = splitIndex;
                    splitIndex -= splitSeq.Count / (2 * splitCount);
                }
                else if (splitIndex != splitSeq.Count)
                    splitIndex += splitSeq.Count / (2 * splitCount);
                else
                    break;
            }
            return String.Join(",", splitSeq.Take (lastInvalidSubseqIndex));
        }

        public List<string> VerifyTree(string inputFile, Random randomChoice, int maxCount = -1, int memSplitCount = 0) {
            List<string> verifiedSequences = new List<string>();
            List<string> toVerify = this.GetAllSequences();
            int count = 0;
            while (toVerify.Any() && count++ < maxCount) {
                string sequence = toVerify.ElementAt(randomChoice.Next(toVerify.Count));
                string splitMemSeq = ExecuteSearch.InsertSplitMemory(sequence, memSplitCount);
                if (ExecuteSearch.VerifySequence(splitMemSeq, inputFile, 600).Equals(BoogieResult.VERIFIED))
                    verifiedSequences.Add(splitMemSeq);
                toVerify.Remove(sequence);
            }
            return verifiedSequences;
        }

        public static Tree CreateRandomTree(Random randomChoice, int maxDepth, int splitCount) {
            Debug.Assert(maxDepth >= 0);
            return CreateRandomSubTree(randomChoice, maxDepth, splitCount, GetRandomPass(randomChoice, allAllowedPasses));
        }

        private static Tree CreateRandomSubTree(Random randomChoice, int maxDepth, int splitCount, ProgramChoice basePass) {
            Debug.Assert(maxDepth >= 0);
            Tree newRandomSubTree = new Tree(basePass);
            List<ProgramChoice> allowedPasses = new List<ProgramChoice>(allAllowedPasses);
            if (maxDepth > 0)
                for (int i = 0; i < splitCount; i++) {
                    if (!allowedPasses.Any())
                        break;
                    ProgramChoice chosenPass = GetRandomPass(randomChoice, allowedPasses);
                    allowedPasses.Remove(chosenPass);
                    newRandomSubTree.baseNode.SetTreeChild(CreateRandomSubTree(randomChoice, maxDepth - 1, splitCount, chosenPass));
                }
            return newRandomSubTree;
        }
    }
}
