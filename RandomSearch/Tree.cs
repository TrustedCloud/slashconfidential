using System;
using CommandLineTools;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.IO;
using System.Xml;

namespace RandomSearch
{
    class TreeNode {
        protected ProgramChoice pass;
        public bool failNode {get; set;}
        public string boogieFile {get; set;}

        public List<TreeNode> children {get; set;}
        public TreeNode parent {get; set;}

        public TreeNode(ProgramChoice _pass) {
            this.pass = _pass;
            this.children = new List<TreeNode>();
            this.parent = null;
            this.failNode = false;
            this.boogieFile = null;
        }

        public TreeNode(ProgramChoice _pass, string _boogieFile) {
            this.pass = _pass;
            this.children = new List<TreeNode>();
            this.parent = null;
            this.failNode = false;
            this.boogieFile = _boogieFile;
        }

        public TreeNode CreateChild(ProgramChoice pc) {
            TreeNode newChild = new TreeNode(pc);
            newChild.parent = this;
            newChild.boogieFile = this.boogieFile;
            this.children.Add(newChild);
            return newChild;
        }

        public void SetNodeChild(TreeNode node) {
            node.parent = this;
            node.boogieFile = this.boogieFile;
            this.children.Add(node);
        }

        public void SetTreeChild(Tree treeChild) {
            treeChild.baseNode.parent = this;
            treeChild.UpdateBoogieFile(this.boogieFile);
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

        public static List<ProgramChoice> allowedPasses = new List<ProgramChoice>{
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

        public List<string> GetAllSequences() {
            List<string> sequences = new List<string>();
            if (!baseNode.children.Any())
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

        public void UpdateBoogieFile(string file) {
            this.baseNode.boogieFile = file;
            foreach (TreeNode child in this.baseNode.children)
                new Tree(child).UpdateBoogieFile(file);
        }

        public static Tree CreateRandomTree(Random randomChoice, int maxDepth, ProgramChoice? baseNodePass = null, int depth = 0, TreeNode parent = null) {
            if (!baseNodePass.HasValue)
                baseNodePass = allowedPasses.ElementAt(randomChoice.Next(allowedPasses.Count));
            Debug.Assert(baseNodePass.HasValue);
            TreeNode baseNode = new TreeNode(baseNodePass.Value);
            if (parent != null)
                parent.SetNodeChild(baseNode);
            if (depth < maxDepth) {
                int maxChildren = randomChoice.Next(2) + 3;
                List<ProgramChoice> currAllowedPasses = new List<ProgramChoice>(allowedPasses);
                for (int childCount = 0; childCount < maxChildren; childCount++) {
                    if (!currAllowedPasses.Any())
                        break;
                    ProgramChoice chosenChildPass = currAllowedPasses.ElementAt(randomChoice.Next(currAllowedPasses.Count()));
                    if (RandomSearch.ExecuteSearch.VerifySequence(baseNode.ComputeSequence() + "," + chosenChildPass.ToString(), baseNode.boogieFile, 10)) {
                        CreateRandomTree(randomChoice, maxDepth, chosenChildPass, depth + 1, baseNode);
                    }
                    else
                    {
                        TreeNode childNode = baseNode.CreateChild(chosenChildPass);
                        childNode.failNode = true;
                    }
                    currAllowedPasses.Remove(chosenChildPass);
                }
            }
            return new Tree(baseNode);
        }
    }
}
