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
    public class PartitionAssumeSlicer : StandardVisitor
    {
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssumeCmd && QKeyValue.FindBoolAttribute((c as AssumeCmd).Attributes, "partition"))
                    continue;
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
