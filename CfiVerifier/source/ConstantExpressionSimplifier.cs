using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace CfiVerifier
{
    /* This simplifies arithmetic operations with constant expressions, e.g.:
     *      > PLUS_64(1bv64, 7bv64) -> 8bv64
     * */
    public class ConstantExpressionSimplifier : StandardVisitor
    {
        public override Expr VisitExpr(Expr node)
        {
            Expr newExpr = null;
            if (node is NAryExpr)
            {
                newExpr = EvaluateNAryExpr(node as NAryExpr);
            }
            return base.VisitExpr(newExpr == null ? node : newExpr);
        }

        private LiteralExpr EvaluateNAryExpr(NAryExpr node)
        {
            if (node.Args.Count == 2)
            {
                try
                {
                    LiteralExpr arg1 = DecideArg(node.Args.ElementAt(0));
                    LiteralExpr arg2 = DecideArg(node.Args.ElementAt(1));
                    if (arg1 == null || arg2 == null)
                    {
                        return null;
                    }
                    Utils.Assert(arg1.asBvConst.Bits == arg2.asBvConst.Bits, "Expected operation on same width bit-vectors.");
                    if (node.Fun.FunctionName.Contains("PLUS"))
                    {
                        return new LiteralExpr(Token.NoToken, arg1.asBvConst.Value + arg2.asBvConst.Value, arg1.asBvConst.Bits);
                    }
                    else if (node.Fun.FunctionName.Contains("MINUS"))
                    {
                        return new LiteralExpr(Token.NoToken, arg1.asBvConst.Value - arg2.asBvConst.Value, arg1.asBvConst.Bits);
                    }
                }
                catch (InvalidCastException) { };
            }
            return null;
        }

        private LiteralExpr DecideArg(Expr arg)
        {
            if (arg is LiteralExpr)
                return arg as LiteralExpr;
            else if (arg is NAryExpr)
                return EvaluateNAryExpr(arg as NAryExpr);
            else return null;
        }
    }
}
