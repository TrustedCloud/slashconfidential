using System;
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
namespace CfiVerifier
{
    // enforces several assumptions that CfiVerifier makes about the input Boogie program.
    public class Validator : StandardVisitor
    {
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                }
            }
            return base.VisitCmdSeq(cmdSeq);
        }
    }
}
