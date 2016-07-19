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
using BType = Microsoft.Boogie.Type;

namespace CfiVerifier
{
    #region Instrument havoc based on adversary model
    public class HavocingAdversary : StandardVisitor
    {
        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                    if (Utils.getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load8 ||
                        Utils.getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load16 ||
                        Utils.getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load32 ||
                        Utils.getSlashVerifyCmdType(ac) == SlashVerifyCmdType.Load64)
                    {
                        //__SlashVerify__tmpmem := mem; havoc mem; assume forall i: enc(i) ==> mem[i] == __SlashVerify__tmpmem[i]
                        // modeled within call __SlashVerify__MNEMAdversary();
                        newCmdSeq.Add(new CallCmd(Token.NoToken, "__SlashVerify__HavocingAdversary",
                            new List<Expr>(), new List<IdentifierExpr>()));
                    }
                }
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
    #endregion
}
