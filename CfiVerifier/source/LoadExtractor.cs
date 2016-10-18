using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace CfiVerifier
{
    public class LoadExtractor : StandardVisitor
    {
        private GlobalVariable mem_temp;

        public override Program VisitProgram(Program node)
        {
            if (node.GlobalVariables.FirstOrDefault(i => i.Name.Equals("mem_temp")) != null)
            {
                this.mem_temp = Utils.FindGlobalVariableInProgram(node, "mem_temp");
            }
            else
            {
                this.mem_temp = Utils.MkGlobalVar("mem_temp",
                    Utils.FindGlobalVariableInProgram(node, "mem").TypedIdent.Type);
                node.AddTopLevelDeclaration(this.mem_temp);
            }

			return base.VisitProgram(node);
        }


        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            LoadAddressDecider lad = new LoadAddressDecider();
            List<Expr> exprLoads;

            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd) {
                    Utils.Assert((c as AssignCmd).Rhss.Count == 1, "Expecting one rhs argument!");
                    exprLoads = lad.getNestedLoadAddresses((c as AssignCmd).Rhss[0]).Select(i => i.Item2).ToList();
                    AssignCmd memTempAssign = new AssignCmd(Token.NoToken,
                        new List<AssignLhs> { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_temp)) },
                        new List<Expr> { exprLoads[0] });
                    newCmdSeq.Add(memTempAssign);
                }
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}


