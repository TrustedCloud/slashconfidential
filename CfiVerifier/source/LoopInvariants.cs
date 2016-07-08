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
        #region Adding candidate Loop invariant

        public class LoopInvariantInstrumenter : StandardVisitor
        {
            private GlobalVariable mem;
            private GlobalVariable mem_stack;
            private GlobalVariable mem_bitmap;
            private Function addrInBitmap;
            private Constant _guard_writeTable_ptr;
            private Constant _bitmap_low;
            private Function load_64;
            private GlobalVariable mem_oldbitmap;
            private String memCheckpointLabel;
            private List<String> loopHeaderLabels;
            private String currentLabel;
            private Queue<Constant> existentials;

            public LoopInvariantInstrumenter(String memCheckpointLabel, List<String> loopHeaderLabels)
            {
                this.memCheckpointLabel = memCheckpointLabel;
                this.loopHeaderLabels = loopHeaderLabels;
            }

            public override Program VisitProgram(Program node)
            {
                //find a mem variable and add mem_oldbitmap of the same type as mem
                this.mem = Utils.FindGlobalVariableInProgram(node, "mem");
                if (Options.splitMemoryModel)
                {
                    this.mem_stack = Utils.FindGlobalVariableInProgram(node, "mem_stack");
                    this.mem_bitmap = Utils.FindGlobalVariableInProgram(node, "mem_bitmap");
                }
                else
                {
                    this.mem_bitmap = this.mem;
                    this.mem_stack = this.mem;
                }

                this.addrInBitmap = Utils.FindFunctionInProgram(node, "addrInBitmap");
                this.load_64 = Utils.FindFunctionInProgram(node, "LOAD_LE_64");
                this._bitmap_low = Utils.FindConstantInProgram(node, "_bitmap_low");
                this._guard_writeTable_ptr = Utils.FindConstantInProgram(node, "_guard_writeTable_ptr");

                this.mem_oldbitmap = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "mem_oldbitmap", this.mem.TypedIdent.Type));
                node.AddTopLevelDeclaration(this.mem_oldbitmap);

                existentials = new Queue<Constant>();
                for (int i = 0; i < 2 * loopHeaderLabels.Count; i++)
                {
                    Constant existential = new Constant(Token.NoToken, new TypedIdent(Token.NoToken, "existential_b" + i.ToString(), BType.Bool));
                    existential.AddAttribute("existential");
                    node.AddTopLevelDeclaration(existential);
                    this.existentials.Enqueue(existential);
                }

                return base.VisitProgram(node);
            }

            public override Implementation VisitImplementation(Implementation node)
            {
                node.Proc.Modifies.Add(new IdentifierExpr(Token.NoToken, this.mem_oldbitmap));
                return base.VisitImplementation(node);
            }

            public override Block VisitBlock(Block node)
            {
                this.currentLabel = node.Label;
                return base.VisitBlock(node);
            }

            public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
            {
                List<Cmd> newCmdSeq = new List<Cmd>();
                if (this.currentLabel == this.memCheckpointLabel)
                {
                    //mem_oldbitmap := mem
                    AssignCmd ac = new AssignCmd(Token.NoToken, new List<AssignLhs>() { new SimpleAssignLhs(Token.NoToken, new IdentifierExpr(Token.NoToken, this.mem_oldbitmap)) },
                                                                new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap) });
                    newCmdSeq.Add(ac);
                }
                else if (this.loopHeaderLabels.Contains(this.currentLabel))
                {
                    //assert (forall i: bv64 :: addrInBitmap(i) ==> mem[i] == mem_oldbitmap[i]);
                    BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                    Expr in_bitmap = new NAryExpr(Token.NoToken, new FunctionCall(this.addrInBitmap), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });

                    Expr assert_expr;
                    Expr mem_bitmap_of_i = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                        new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), 
                                       new IdentifierExpr(Token.NoToken, i) });
                    Expr mem_oldbitmap_of_i = new NAryExpr(Token.NoToken, new MapSelect(Token.NoToken, 1),
                        new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_oldbitmap), 
                                       new IdentifierExpr(Token.NoToken, i) });
                    assert_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(in_bitmap, Expr.Eq(mem_bitmap_of_i, mem_oldbitmap_of_i)));
                    //for Houdini
                    Constant existential = this.existentials.Dequeue();
                    assert_expr = Expr.Imp(new IdentifierExpr(Token.NoToken, existential), assert_expr);
                    newCmdSeq.Add(new AssertCmd(Token.NoToken, assert_expr));

                    //assert (LOAD_LE_64(mem, _guard_writeTable_ptr) == _bitmap_low);
                    Expr load_mem_guardptr = new NAryExpr(Token.NoToken, new FunctionCall(this.load_64), new List<Expr>() { 
                        new IdentifierExpr(Token.NoToken, this.mem), 
                        new IdentifierExpr(Token.NoToken, this._guard_writeTable_ptr) });
                    assert_expr = Expr.Eq(load_mem_guardptr, new IdentifierExpr(Token.NoToken, _bitmap_low));
                    //for Houdini
                    existential = this.existentials.Dequeue(); 
                    assert_expr = Expr.Imp(new IdentifierExpr(Token.NoToken, existential), assert_expr);
                    newCmdSeq.Add(new AssertCmd(Token.NoToken, assert_expr));
                }
                newCmdSeq.AddRange(cmdSeq);
                return base.VisitCmdSeq(newCmdSeq);
            }

        }
        #endregion
}
