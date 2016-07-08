﻿using System;
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
    #region Instrument with typing assertions
    public class ProofObligations : StandardVisitor
    {
        private Function plus_64, minus_64, lt_64, le_64, ge_64, gt_64;
        private Function writable;
        private Function addrInBitmap;
        private Function addrInStack;
        private Function largestAddrAffected_8;
        private Function smallestAddrAffected_8;
        private Function anyAddrAffected_8;
        private Function rep_stosb;
        private Function policy;

        private Constant stack_low;
        private Constant stack_high;
        private Constant bitmap_low;
        private Constant bitmap_high;

        private GlobalVariable mem;
        private GlobalVariable mem_stack;
        private GlobalVariable mem_bitmap;
        private GlobalVariable RSP;
        private GlobalVariable RAX;
        private GlobalVariable RDI;
        private GlobalVariable RCX;
        private GlobalVariable CF;

        private string current_label;
        private bool bound_stacksize_option = false; //true if applying trick
        private int bound_stacksize_offset = -1;

        private List<GlobalVariable> globals = new List<GlobalVariable>();

        public override Program VisitProgram(Program node)
        {
            this.globals.AddRange(node.GlobalVariables);

            this.plus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("PLUS_64"));
            Utils.Assert(this.plus_64 != null, "Could not find PLUS_64(.,.) function");
            this.minus_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("MINUS_64"));
            Utils.Assert(this.minus_64 != null, "Could not find MINUS_64(.,.) function");
            this.lt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LT_64"));
            Utils.Assert(this.lt_64 != null, "Could not find LT_64(.,.) function");
            this.le_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("LE_64"));
            Utils.Assert(this.le_64 != null, "Could not find LE_64(.,.) function");
            this.ge_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GE_64"));
            Utils.Assert(this.ge_64 != null, "Could not find GE_64(.,.) function");
            this.gt_64 = node.Functions.FirstOrDefault(f => f.Name.Equals("GT_64"));
            Utils.Assert(this.gt_64 != null, "Could not find GT_64(.,.) function");
            this.writable = node.Functions.FirstOrDefault(f => f.Name.Equals("writable"));
            Utils.Assert(this.writable != null, "Could not find writable(.,.) function");
            this.addrInBitmap = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInBitmap"));
            Utils.Assert(this.addrInBitmap != null, "Could not find addrInBitmap(.) function");
            this.addrInStack = node.Functions.FirstOrDefault(f => f.Name.Equals("addrInStack"));
            Utils.Assert(this.addrInStack != null, "Could not find addrInStack(.) function");
            this.largestAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("largestAddrAffected_8"));
            Utils.Assert(this.largestAddrAffected_8 != null, "Could not find largestAddrAffected_8(.,.,.) function");
            this.smallestAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("smallestAddrAffected_8"));
            Utils.Assert(this.smallestAddrAffected_8 != null, "Could not find smallestAddrAffected_8(.,.,.) function");
            this.anyAddrAffected_8 = node.Functions.FirstOrDefault(f => f.Name.Equals("anyAddrAffected_8"));
            Utils.Assert(this.anyAddrAffected_8 != null, "Could not find anyAddrAffected_8(.,.,.) function");
            this.rep_stosb = node.Functions.FirstOrDefault(f => f.Name.Equals("REP_STOSB"));
            Utils.Assert(this.rep_stosb != null, "Could not find REP_STOSB(.,.,.) function");
            this.policy = node.Functions.FirstOrDefault(f => f.Name.Equals("policy"));
            Utils.Assert(this.policy != null, "Could not find policy(.,.,.) function");

            this.mem = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem"));
            Utils.Assert(this.mem != null, "Could not find mem variable");
            if (Options.splitMemoryModel)
            {
                this.mem_stack = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_stack"));
                Utils.Assert(this.mem_stack != null, "Could not find mem_stack variable");
                this.mem_bitmap = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("mem_bitmap"));
                Utils.Assert(this.mem_bitmap != null, "Could not find mem_bitmap variable");
            }
            else
            {
                this.mem_bitmap = this.mem;
                this.mem_stack = this.mem;
            }
            this.RSP = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RSP"));
            Utils.Assert(this.RSP != null, "Could not find RSP variable");
            this.RAX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RAX"));
            Utils.Assert(this.RAX != null, "Could not find RAX variable");
            this.RDI = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RDI"));
            Utils.Assert(this.RDI != null, "Could not find RDI variable");
            this.RCX = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("RCX"));
            Utils.Assert(this.RCX != null, "Could not find RCX variable");
            this.CF = node.GlobalVariables.FirstOrDefault(x => x.Name.Equals("CF"));
            Utils.Assert(this.CF != null, "Could not find CF variable");

            this.stack_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_low"));
            Utils.Assert(this.stack_low != null, "Could not find _stack_low variable");
            this.stack_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_stack_high"));
            Utils.Assert(this.stack_high != null, "Could not find _stack_high variable");
            this.bitmap_low = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_low"));
            Utils.Assert(this.bitmap_low != null, "Could not find _bitmap_low variable");
            this.bitmap_high = node.Constants.FirstOrDefault(x => x.Name.Equals("_bitmap_high"));
            Utils.Assert(this.bitmap_high != null, "Could not find _bitmap_high variable");

            return base.VisitProgram(node);
        }

        public override Implementation VisitImplementation(Implementation node)
        {
            StackSizeEstimator estimator = new StackSizeEstimator();
            estimator.Visit(node); //necessary before querying the stack size estimate
            int stack_size_estimate = estimator.getStackEstimate(-1);
            if (stack_size_estimate > 0)
            {
                bound_stacksize_option = true;
                bound_stacksize_offset = stack_size_estimate;
            }

            return base.VisitImplementation(node);
        }

        public override Block VisitBlock(Block node)
        {
            //Console.WriteLine("Visiting block with label {0}", node.Label);
            this.current_label = node.Label;
            return base.VisitBlock(node);
        }

        public override List<Cmd> VisitCmdSeq(List<Cmd> cmdSeq)
        {
            List<Cmd> newCmdSeq = new List<Cmd>();
            foreach (Cmd c in cmdSeq)
            {
                if (c is AssignCmd)
                {
                    AssignCmd ac = c as AssignCmd;
                    Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Not handling parallel AssignCmd");
                    //Console.Write(".");
                    switch (Utils.getSlashVerifyCmdType(ac))
                    {
                        case Utils.SlashVerifyCmdType.Store8:
                        case Utils.SlashVerifyCmdType.Store16:
                        case Utils.SlashVerifyCmdType.Store32:
                        case Utils.SlashVerifyCmdType.Store64: //mem := store(mem, y, e)
                            {
                                Tuple<Variable, Expr, Expr> storeArgs = Utils.getStoreArgs(ac);
                                Expr store_addr = storeArgs.Item2;
                                Expr store_value = storeArgs.Item3;
                                Expr old_RSP = new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP));
                                AssertCmd assertion;

                                Func<int, Expr> OffsetExpr = delegate(int n)
                                {
                                    LiteralExpr x = new LiteralExpr(Token.NoToken, BigNum.FromInt(Math.Abs(n)), 64);
                                    if (n >= 0)
                                    {
                                        return new NAryExpr(Token.NoToken, new FunctionCall(plus_64), new List<Expr>() { storeArgs.Item2, x });
                                    }
                                    else
                                    {
                                        return new NAryExpr(Token.NoToken, new FunctionCall(minus_64), new List<Expr>() { storeArgs.Item2, x });
                                    }
                                };

                                //Console.WriteLine("store to {0} at addr {1} with value {2}", storeArgs.Item1, storeArgs.Item2, storeArgs.Item3);
                                int iterations =
                                  Utils.getSlashVerifyCmdType(ac) == Utils.SlashVerifyCmdType.Store8 ? 1 :
                                  Utils.getSlashVerifyCmdType(ac) == Utils.SlashVerifyCmdType.Store16 ? 2 :
                                  Utils.getSlashVerifyCmdType(ac) == Utils.SlashVerifyCmdType.Store32 ? 4 : 8;

                                //instrument assert ((addrInStack(PLUS_64(t_a, 0bv64)) && GE_64(PLUS_64(t_a, 0bv64), old(RSP))) ==> 
                                //    writable(mem,PLUS_64(t_a, 0bv64)) || writable(mem,MINUS_64(t_a, 8bv64))) && (addrInBitmap(PLUS_64(t_a, 0bv64)) ==> 
                                //    LT_64(largestAddrAffected_8(mem, PLUS_64(t_a, 0bv64), t_v[8:0]), old(RSP - 8)));
                                Expr is_checkworthy_store = Expr.False;
                                foreach (int iter in new List<int>() { 0, iterations - 1 }.Distinct()) //disjunction over a, a+n-1
                                {
                                    Expr addr_in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack),
                                        new List<Expr>() { OffsetExpr(iter) });
                                    Expr addr_in_parent_frame = new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                        new List<Expr>() { OffsetExpr(iter), old_RSP });
                                    Expr addr_not_in_backing_space = Expr.Not(Expr.And(
                                        new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                            new List<Expr>() { OffsetExpr(iter),
                                                           new NAryExpr(Token.NoToken, 
                                                                new FunctionCall(plus_64), 
                                                                  new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) }) }),
                                        new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                            new List<Expr>() { OffsetExpr(iter),
                                                           new NAryExpr(Token.NoToken, 
                                                                new FunctionCall(plus_64), 
                                                                  new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(40), 64) }) })));
                                    is_checkworthy_store = Expr.Or(is_checkworthy_store, Expr.And(addr_in_stack, Expr.And(addr_not_in_backing_space, addr_in_parent_frame)));
                                }
                                //Fix for the padding issue. Enough to check writability of (addr + 0). It's an invariant that /guard:cfw maintains
                                Expr is_writable = new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(0) });
                                Expr check_for_stack_store = Expr.Imp(is_checkworthy_store, is_writable);
                                assertion = new AssertCmd(Token.NoToken, check_for_stack_store);
                                newCmdSeq.Add(assertion);
                                VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                                for (int iter = 0; iter < iterations; iter++)
                                {
                                    Expr addr_in_bitmap = new NAryExpr(Token.NoToken, new FunctionCall(addrInBitmap),
                                        new List<Expr>() { OffsetExpr(iter) });
                                    Expr largest_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(largestAddrAffected_8),
                                        new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                    //Expr addr_in_own_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                    //    new List<Expr>() { largest_addr_affected, old_RSP }); //Not using this because of padding issue
                                    Expr largest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                          new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) });
                                    Expr addr_in_own_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                          new List<Expr>() { largest_addr_affected, largest_allowed_address });
                                    if (this.bound_stacksize_option)
                                    {
                                        Utils.Assert(this.bound_stacksize_offset % 8 == 0, "Need stack size estimate to be a multiple of 8");
                                        Expr smallest_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(smallestAddrAffected_8),
                                          new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                        Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                            new List<Expr>() { old_RSP, new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) });
                                        addr_in_own_frame = Expr.And(addr_in_own_frame,
                                            new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                              new List<Expr>() { smallest_addr_affected, smallest_allowed_address }));
                                    }

                                    Expr any_addr_affected = new NAryExpr(Token.NoToken, new FunctionCall(anyAddrAffected_8),
                                        new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), OffsetExpr(iter), 
                                                       new BvExtractExpr(Token.NoToken, store_value, 8*(iter+1), 8*iter) });
                                    Expr value_not_zero = Expr.Neq(new BvExtractExpr(Token.NoToken, store_value, 8 * (iter + 1), 8 * iter),
                                                                   new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 8));

                                    Expr check_for_bitmap_store = Expr.Imp(Expr.And(Expr.And(addr_in_bitmap, any_addr_affected), value_not_zero), addr_in_own_frame);

                                    assertion = new AssertCmd(Token.NoToken, check_for_bitmap_store);
                                    newCmdSeq.Add(assertion);
                                    VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                                }

                                if (Options.confidentiality)
                                {
                                    Expr addr_in_U =
                                        Expr.And(
                                          Expr.And(
                                              new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                  new List<Expr>() { OffsetExpr(0), new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                              new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                  new List<Expr>() { OffsetExpr(0), new IdentifierExpr(Token.NoToken, this.bitmap_high) })),
                                          Expr.And(
                                              new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                  new List<Expr>() { OffsetExpr(iterations - 1), new IdentifierExpr(Token.NoToken, this.stack_low) }),
                                              new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                  new List<Expr>() { OffsetExpr(iterations - 1), new IdentifierExpr(Token.NoToken, this.bitmap_high) }))
                                        );

                                    Expr _data_low = new LiteralExpr(Token.NoToken, BigNum.FromInt(Int32.Parse(Options.dataLow.ToUpper(), System.Globalization.NumberStyles.HexNumber)), 64);
                                    Expr _data_high = new LiteralExpr(Token.NoToken, BigNum.FromInt(Int32.Parse(Options.dataHigh.ToUpper(), System.Globalization.NumberStyles.HexNumber)), 64);
                                    Expr addr_in_Data =
                                        Expr.And(
                                          Expr.And(
                                              new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                  new List<Expr>() { OffsetExpr(0), _data_low }),
                                              new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                  new List<Expr>() { OffsetExpr(0), _data_high })),
                                          Expr.And(
                                              new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                                  new List<Expr>() { OffsetExpr(iterations - 1), _data_low }),
                                              new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                                                  new List<Expr>() { OffsetExpr(iterations - 1), _data_high }))
                                        );

                                    assertion = new AssertCmd(Token.NoToken, Expr.Or(addr_in_U, addr_in_Data));
                                    newCmdSeq.Add(assertion);
                                    VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                                }

                                break;
                            }

                        case Utils.SlashVerifyCmdType.RepStosB: //x := REP_STOSB(mem, e1, e2, e3)
                            {
                                //TODO: might want to assert that it writes to the bitmap
                                //if its writing zeros to bitmap, we dont need to assert anything
                                break;
                            }

                        default: //x:=e
                            {
                                Utils.Assert(ac.Lhss.Count == 1 && ac.Rhss.Count == 1, "Expected assignments to have 1 lhs and 1 rhs");

                                AssignLhs lhs = ac.Lhss.ElementAt(0);
                                Expr rhs = ac.Rhss.ElementAt(0);

                                // is x rsp?
                                if (lhs.Type.IsBv && lhs.DeepAssignedIdentifier.Name.Equals("RSP"))
                                {
                                    Expr alignment = Expr.Eq(new BvExtractExpr(Token.NoToken, rhs, 3, 0),
                                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));
                                    Expr le_old_RSP = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                                        new List<Expr>() { rhs, new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)) });
                                    AssertCmd assertion = new AssertCmd(Token.NoToken, Expr.And(alignment, le_old_RSP));
                                    newCmdSeq.Add(assertion);
                                    VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                                }

                                break;
                            }
                    }
                }
                else if (c is AssertCmd) //call and return instructions are marked with attributes
                {
                    AssertCmd ac = c as AssertCmd;

                    //extract instruction type
                    string attribute_cmdtype = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCommandType");
                    string attribute_jmptarget = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpTarget");

                    //return
                    if (attribute_cmdtype != null && attribute_cmdtype.Equals("ret"))
                    {
                        int numAssertsBeforeReturn = VCSplitter.Instance.getCurrentAssertionCount();
                        //these are the asserts we place on return statement. why not just make them postconditions?
                        //forall i. i < old(rsp) && i[3:0] == 0bv3 ==> ¬writable(mem,i)
                        AssertCmd assertion;
                        if (this.bound_stacksize_option && Options.instantiateQuantifiers) //can only instantiate quantifiers on bounded 
                        {
                            Expr instantiation = Expr.True;
                            int addr_offset = 8;
                            while (addr_offset <= (this.bound_stacksize_offset))
                            {
                                Expr addr = new NAryExpr(Token.NoToken, new FunctionCall(this.minus_64),
                                  new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                 new LiteralExpr(Token.NoToken, BigNum.FromInt(addr_offset), 64) });
                                Expr addr_not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                  new List<Expr>() { new IdentifierExpr(Token.NoToken, mem_bitmap), addr }));
                                //instantiation = Expr.And(instantiation, addr_not_writable);
                                Expr precondition =
                                    Expr.And(Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP), 3, 0), new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3)),
                                             Expr.Eq(new IdentifierExpr(Token.NoToken, RSP), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                                assertion = new AssertCmd(Token.NoToken, Expr.Imp(precondition, addr_not_writable));
                                newCmdSeq.Add(assertion);
                                VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                                addr_offset += 8;
                            }
                            int numAssertsAfterReturn = VCSplitter.Instance.getCurrentAssertionCount();
                            Console.WriteLine("VCSplitter says that ret produced assertions ({0},{1})", numAssertsBeforeReturn, numAssertsAfterReturn - 1);
                            //assertion = new AssertCmd(Token.NoToken, instantiation);
                        }
                        else
                        {
                            BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                            Expr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)) });
                            if (this.bound_stacksize_option)
                            {
                                Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                            new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                         new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) });
                                in_local_frame = Expr.And(in_local_frame,
                                  new NAryExpr(Token.NoToken, new FunctionCall(ge_64),
                                    new List<Expr>() { new IdentifierExpr(Token.NoToken, i), smallest_allowed_address }));
                            }
                            NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                            Expr aligned = Expr.Eq(new BvExtractExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, i), 3, 0),
                                                           new LiteralExpr(Token.NoToken, BigNum.FromInt(0), 3));
                            Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                            Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i },
                              Expr.Imp(Expr.And(Expr.And(in_local_frame, in_stack), aligned), not_writable));
                            assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                        }


                        //rsp == old(rsp)
                        assertion = new AssertCmd(Token.NoToken, Expr.Eq(new IdentifierExpr(Token.NoToken, RSP),
                                                                           new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                    }
                    else if (attribute_cmdtype != null && attribute_cmdtype.Equals("call"))
                    {
                        AssertCmd assertion;

                        string attribute_target = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyCallTarget");
                        Utils.Assert(attribute_target != null, "Expected SlashVerifyCallTarget attribute on call");

                        //assert policy(target);
                        Expr is_policy;
                        if (attribute_target.Substring(0, 2).Equals("0x"))
                        {
                            int target = Int32.Parse(attribute_target.ToUpper().Substring(2), System.Globalization.NumberStyles.HexNumber);
                            is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(target), 64) });
                        }
                        else
                        {
                            GlobalVariable target = this.globals.FirstOrDefault(v => v.Name.Equals(attribute_target));
                            Utils.Assert(target != null, "Could not find " + attribute_target);
                            is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, target) });
                        }

                        if (!Options.disablePolicyChecking)
                        {
                            assertion = new AssertCmd(Token.NoToken, is_policy);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                        }

                        if (!this.bound_stacksize_option)
                        {
                            //forall i. i < (rsp - 8) ==> ¬writable(mem,i) //rsp - 8 holds return address, and everything below that must start off as non writable
                            BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                            NAryExpr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, i), 
                                             new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                new List<Expr>() { 
                                                  new IdentifierExpr(Token.NoToken, RSP), 
                                                  new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) })});
                            NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                            Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                            Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(Expr.And(in_stack, in_local_frame), not_writable));
                            assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                            //assert !writable(mem, rsp-8)
                            not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                                                  new List<Expr>() { 
                                              new IdentifierExpr(Token.NoToken, this.mem_bitmap), 
                                              new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                new List<Expr>() { 
                                                  new IdentifierExpr(Token.NoToken, RSP), 
                                                  new LiteralExpr(Token.NoToken, BigNum.FromInt(8), 64) })
                                            }));
                            assertion = new AssertCmd(Token.NoToken, not_writable);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                        }
                        else
                        {
                            //assert that RSP is not lower than bound_stacksize_offset. if RSP has not gotten lower, than we know everything is writable below
                            Expr smallest_allowed_address = new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                        new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                         new LiteralExpr(Token.NoToken, BigNum.FromInt(this.bound_stacksize_offset), 64) });

                            NAryExpr rsp_in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                              new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), smallest_allowed_address });
                            assertion = new AssertCmd(Token.NoToken, rsp_in_local_frame);
                            newCmdSeq.Add(assertion);
                            VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                        }

                        //assert RSP <= (old(RSP) - 32)
                        NAryExpr stack_backing_space = new NAryExpr(Token.NoToken, new FunctionCall(le_64),
                          new List<Expr>() { new IdentifierExpr(Token.NoToken, RSP), 
                                             new NAryExpr(Token.NoToken, new FunctionCall(minus_64),
                                                 new List<Expr>() { new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP)), 
                                                                    new LiteralExpr(Token.NoToken, BigNum.FromInt(32), 64) }) });
                        assertion = new AssertCmd(Token.NoToken, stack_backing_space);
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                    }
                    else if (attribute_cmdtype != null && attribute_jmptarget != null &&
                              (attribute_cmdtype.Equals("remotejmp") ||
                              (attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget.Equals("remote"))))
                    {
                        AssertCmd assertion;

                        //assert policy(target);
                        Expr is_policy;
                        if (attribute_cmdtype.Equals("remotejmp"))
                        {
                            int target = Int32.Parse(attribute_jmptarget.ToUpper().Substring(2), System.Globalization.NumberStyles.HexNumber);
                            is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                new List<Expr>() { new LiteralExpr(Token.NoToken, BigNum.FromInt(target), 64) });
                        }
                        else if (attribute_cmdtype.Equals("indirectjmp") && attribute_jmptarget.Equals("remote"))
                        {
                            string attribute_jmpregister = QKeyValue.FindStringAttribute(ac.Attributes, "SlashVerifyJmpRegister");
                            Utils.Assert(attribute_jmpregister != null, "Exprected jmp register annotation on indirect jump");
                            GlobalVariable global_register = this.globals.FirstOrDefault(x => x.Name.Equals(attribute_jmpregister));
                            Utils.Assert(global_register != null, "Could not find global variable " + attribute_jmpregister);

                            is_policy = new NAryExpr(Token.NoToken, new FunctionCall(policy),
                                new List<Expr>() { new IdentifierExpr(Token.NoToken, global_register) });
                        }
                        else
                        {
                            Utils.Assert(false, "Unexpected case");
                            is_policy = Expr.False;
                        }
                        assertion = new AssertCmd(Token.NoToken, is_policy);
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                        assertion = new AssertCmd(Token.NoToken, Expr.Eq(new IdentifierExpr(Token.NoToken, RSP),
                                                                         new OldExpr(Token.NoToken, new IdentifierExpr(Token.NoToken, RSP))));
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);

                        //forall i. i < rsp ==> ¬writable(mem,i)
                        BoundVariable i = new BoundVariable(Token.NoToken, new TypedIdent(Token.NoToken, "i", this.mem.TypedIdent.Type.AsMap.Arguments[0]));
                        NAryExpr in_local_frame = new NAryExpr(Token.NoToken, new FunctionCall(lt_64),
                          new List<Expr>() { new IdentifierExpr(Token.NoToken, i), new IdentifierExpr(Token.NoToken, RSP) });
                        NAryExpr in_stack = new NAryExpr(Token.NoToken, new FunctionCall(addrInStack), new List<Expr>() { new IdentifierExpr(Token.NoToken, i) });
                        Expr not_writable = Expr.Not(new NAryExpr(Token.NoToken, new FunctionCall(writable),
                          new List<Expr>() { new IdentifierExpr(Token.NoToken, this.mem_bitmap), new IdentifierExpr(Token.NoToken, i) }));
                        Expr assert_mem_false_expr = new ForallExpr(Token.NoToken, new List<Variable>() { i }, Expr.Imp(Expr.And(in_stack, in_local_frame), not_writable));
                        assertion = new AssertCmd(Token.NoToken, assert_mem_false_expr);
                        newCmdSeq.Add(assertion);
                        VCSplitter.Instance.RecordAssertion(this.current_label, ac, assertion);
                    }
                }

                //The assert gets placed prior to the original command
                newCmdSeq.Add(c);
            }

            return base.VisitCmdSeq(newCmdSeq);
        }
    }
    #endregion
}