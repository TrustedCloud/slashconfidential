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

        public List<string> VerifyTree(string inputFile, int maxCount = -1, int memSplitCount = 0) {
            List<string> verifiedSequences = new List<string>();
            int count = 0;
            foreach (string sequence in this.GetAllSequences()) {
                if (count++ > maxCount)
                    break;
                string splitMemSeq = ExecuteSearch.InsertSplitMemory(sequence, memSplitCount);
                if (ExecuteSearch.VerifySequence(splitMemSeq, inputFile, 600).Equals(BoogieResult.VERIFIED))
                    verifiedSequences.Add(splitMemSeq);
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
