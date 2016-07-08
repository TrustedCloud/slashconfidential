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
    public class SpecialInstructionLifter : StandardVisitor
    {
        private Function rep_stosb;
        private Function not_1;
        private Function plus_64;
        private Function policy;

        private GlobalVariable mem;
        private GlobalVariable RSP;
        private GlobalVariable RAX;
        private GlobalVariable RDI;
        private GlobalVariable RDX;
        private GlobalVariable R8;
        private GlobalVariable R9;
        private GlobalVariable R10;
        private GlobalVariable R11;
        private GlobalVariable RCX;
        private GlobalVariable CF;


        public override Program VisitProgram(Program node)
        {
            this.plus_64 = Utils.FindFunctionInProgram(node, "PLUS_64");
            this.not_1 = Utils.FindFunctionInProgram(node, "NOT_1");
            this.rep_stosb = Utils.FindFunctionInProgram(node, "REP_STOSB");
            this.policy = Utils.FindFunctionInProgram(node, "policy");

            this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
            Utils.Assert(this.mem != null, "Could not find mem variable");

            //this has been moved to Bap2Boogie, but let's just have it here as well
            foreach (String name in new List<String>() { "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "RAX", "RBX", "RCX", "RDX", "RBP", "RDI", "RSI", "RSP" })
            {
                GlobalVariable gv = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals(name));
                if (gv == null) //not found, so let's add it in ourself
                {
                    node.AddTopLevelDeclaration(new GlobalVariable(Token.NoToken,
                        new TypedIdent(Token.NoToken, name, BType.GetBvType(64))));
                }
            }

            foreach (String name in new List<String>() { "AF", "CF", "OF", "PF", "SF", "ZF" })
            {
                GlobalVariable gv = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals(name));
                if (gv == null) //not found, so let's add it in ourself
                {
                    node.AddTopLevelDeclaration(new GlobalVariable(Token.NoToken,
                        new TypedIdent(Token.NoToken, name, BType.GetBvType(1))));
                }
            }

            this.RSP = Utils.FindGlobalVariableInProgram(node, "RSP");
            this.RAX = Utils.FindGlobalVariableInProgram(node, "RAX");
            this.RDI = Utils.FindGlobalVariableInProgram(node, "RDI");
            this.RDX = Utils.FindGlobalVariableInProgram(node, "RDX");
            this.R8 = Utils.FindGlobalVariableInProgram(node, "R8");
            this.R9 = Utils.FindGlobalVariableInProgram(node, "R9");
            this.R10 = Utils.FindGlobalVariableInProgram(node, "R10");
            this.R11 = Utils.FindGlobalVariableInProgram(node, "R11");
            this.RCX = Utils.FindGlobalVariableInProgram(node, "RCX");
            this.CF = Utils.FindGlobalVariableInProgram(node, "CF");

            foreach (String s in new HashSet<String>() { Options.funcMemcmp, Options.funcMemcpy, Options.funcMemset, Options.funcSGXFree, Options.funcSGXMalloc })
            {
                int location = Int32.Parse(s.ToUpper(), System.Globalization.NumberStyles.HexNumber);
                node.AddTopLevelDeclaration(new Axiom(Token.NoToken,
                    new NAryExpr(Token.NoToken, new FunctionCall(this.policy),
                        new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(location), 64) })));
            }

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            foreach (GlobalVariable v in new List<GlobalVariable>()
                { this.mem, this.RSP, this.RAX, this.RDI, this.RDX,
                  this.R8, this.R9, this.R10, this.R11, this.RCX, this.CF })
            {
                if (!node.Proc.Modifies.Contains(new IdentifierExpr(Token.NoToken, v)))
                {
                    node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, v));
                }
            }

            return base.VisitImplementation(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();

            foreach (Cmd c in cmdSeq)
            {
                //Do special stuff for those whose BAP modeling is broken
                if (c is AssertCmd) //call and return instructions are marked with attributes
                {
                    AssertCmd ac = c as AssertCmd;

                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    if (attribute_cmdtype != null && attribute_cmdtype.Equals("btc_rax_1d"))
                    {
                        //BAP has a bug with this. Model it explicitly ourselves.

                        //CF := RAX[30:29];
                        newCmdSeq.Add(new AssignCmd(Token.NoToken,
                          new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.CF)) },
                          new List<Expr>() { new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 30, 29) }
                        ));
                        //RAX := RAX[64:30] ++ NOT(RAX[30:29]) ++ RAX[29:0];
                        Expr e1 = new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 64, 30);
                        Expr e2 = new NAryExpr(Token.NoToken, new FunctionCall(this.not_1),
                          new List<Expr>() { new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 30, 29) });
                        Expr e3 = new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 29, 0);
                        newCmdSeq.Add(new AssignCmd(Token.NoToken,
                          new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX)) },
                          new List<Expr>() { new BvConcatExpr(Token.NoToken, new BvConcatExpr(Token.NoToken, e1, e2), e3) }
                        ));
                    }
                    else if (attribute_cmdtype != null && attribute_cmdtype.Equals("rep_stosb"))
                    {
                        //BAP does not model this either. Model rep stosb as sequence: mem := repstosb(mem, rcx, rdi, al); rdi := rdi + rcx; rcx := 0;

                        //forall i. rdi <= i < rdi + rcx ==> new_mem[i] == al;
                        newCmdSeq.Add(new AssignCmd(Token.NoToken,
                          new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem)) },
                          new List<Expr>() { 
                                  new NAryExpr(Token.NoToken, new FunctionCall(rep_stosb), new List<Expr>() {
                                    new IdentifierExpr(Token.NoToken, this.mem), 
                                    new IdentifierExpr(Token.NoToken, this.RCX), 
                                    new IdentifierExpr(Token.NoToken, this.RDI), 
                                    new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RAX), 8, 0) 
                                  })
                                }
                          ));

                        //RDI := RDI + RCX;
                        newCmdSeq.Add(new AssignCmd(Token.NoToken, new List<AssignLhs>() { 
                                new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RDI)) },
                            new List<Expr>() {  
                                    new NAryExpr(Token.NoToken, new FunctionCall(this.plus_64), new List<Expr>() 
                                    { new IdentifierExpr(Token.NoToken, this.RDI), new IdentifierExpr(Token.NoToken, this.RCX) } )
                                }
                        ));

                        //RCX := 0;
                        newCmdSeq.Add(new AssignCmd(Token.NoToken, new List<AssignLhs>() { 
                                new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.RCX)) },
                            new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.ZERO, 64) }));
                    }

                }


                //The assert gets placed prior to the original command
                newCmdSeq.Add(c);
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }

}
