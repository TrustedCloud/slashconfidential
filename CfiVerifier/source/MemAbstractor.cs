using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Boogie.GraphUtil;
using Microsoft.Boogie.VCExprAST;
using VC;
using Microsoft.Basetypes;
using BType = Microsoft.Boogie.Type;

namespace CfiVerifier
{
    public class MemAbstractor : StandardVisitor
    {
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
				if (c is AssignCmd && (c as AssignCmd).Lhss.First().DeepAssignedVariable.Name == "mem")
                    continue;
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}

