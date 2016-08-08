using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace CfiVerifier
{
    class IndiscriminateAssumeSlicer : StandardVisitor
    {
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssumeCmd)
                {
                    continue;
                }
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
