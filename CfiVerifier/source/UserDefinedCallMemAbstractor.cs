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
    public class UserDefinedCallMemAbstractor : StandardVisitor
    {
		IdentifierExpr mem_stack_expr;
		IdentifierExpr mem_expr;

		public override Program VisitProgram(Program node)
		{
			this.mem_stack_expr = new IdentifierExpr(Token.NoToken, Utils.FindGlobalVariableInProgram(node, "mem_stack"));
			this.mem_expr = new IdentifierExpr(Token.NoToken, Utils.FindGlobalVariableInProgram(node, "mem"));
			return base.VisitProgram(node);
		}

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
				if (c is CallCmd && (c as CallCmd).callee.Equals("arbitrary_func"))
				{
					newCmdSeq.Add(new HavocCmd(Token.NoToken, new List<IdentifierExpr>{this.mem_stack_expr, this.mem_expr})); 
				}
                newCmdSeq.Add(c);
            }
            return base.VisitCmdSeq(newCmdSeq);
        }
    }
}
