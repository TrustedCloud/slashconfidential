/*
  Invoke Boogie as follows:
    boogie prelude.bpl proof_soundness_theorem2.bpl
      /z3opt:smt.RELEVANCY=0
      /z3opt:smt.CASE_SPLIT=0
      /proverOpt:OPTIMIZE_FOR_BV=true
      /errorLimit:1
  Takes 21 seconds to verify on a macbook machine.

  The proof is structured as follows.
  A trace \pi of user code (U) starts with a call into main (the entrypoint).
  \pi contains statements of type Stmt, defined as follows; we use BAP to lift x64 to Stmt.

  type Stmt = store expr expr
            | load reg expr
            | reg := expr
            | jmp expr
            | call expr -- procedure in U
            | call expr -- api of L: send,recv,malloc,free
            | ret

  \pi contains statements from different procedures in U, wherein
  control transfers between procedures happens via call and ret.
  Statements in \pi can be labeled as belonging to unique procedure in U, such that
  a procedure is all the statements between the matching call and ret statements in \pi.
  To decouple the verification of U from L, we only let \pi "step into" procedures of U.
  API calls into L execute "atomically", and contribute with one state transition to \pi.
  For instance:

  main () { call g; }
  g() { push rbp; call send; rax := 0; pop rbp; ret }
  send() { push rbp; ... }

  produces a set of concrete traces { \pi }, and we can write \pi symbolically as:
  [ call g; push rbp; call send; rax := 0; pop rbp; ret ]

  We write a meta program (P) that models the execution of an arbitrary procedure of U.
  The execution of P starts with a call and ends in a ret, with an unbounded
  number of statements of type Stmt in between --- nested call to a procedure is modeled by
  recursively calling P, thus modeling executions that reach arbitrary stack depths.
  Since any procedure in U (including main) fits this template, it sufficies to use
  the meta program P to prove Theorem 2.
  Recall that our verifier instruments static assertions in U --- it replaces each statements
  s in U with I(s). To prove theorem 2, we prove that for any statement s in U,
  if the assertions in I(s) are valid in all traces of U, then the pushdown automaton (PDA)
  from definition 3 makes a valid transition i.e. it does not get stuck i.e. \pi satisfies WCFI-RW.
  We use the PDA to store all the return addresses, like a shadow stack used in CFI defenses.
  For each matching call and ret, we assert that the return address on program stack is equal to that
  on the PDA --- if this holds, then the PDA executes the ret and does not get stuck.

  To prove this theorem, our meta program P assumes that all the assertions in I(s)
  are valid, and then asserts the validity check (from defn 3) on the corresponding
  transition in PDA. To that end, we define an instrumentation function I^,
  which replaces each assert produced by I(s) with an assume; P uses I^ instead of I.

  The justification for why P models an arbitrary U involves an inductive use of WCFI-RW itself.
  The argument requires that
  1) U cannot jump into the code of L at locations other than API entrypoints of L
  2) U follows a stack discipline of procedure calls and returns
  Each of these properties are assumed for the construction of P, but also asserted by P itself.
  For each control transfer statement (call and jmp to outside the current procedure),
  the policy predicate in the assert (see I) constrains the target location to be a procedure in U.
  Further, the assertions on ret enforce the stack discipline: ret returns to the maching call.

  We have to manually supply some inductive invariants, which helps Boogie prove P.
 */

 var pushdown_stack_contents : [int] bv64; //pushdown stack holds all return addresses in the call chain
 var pushdown_stack_top      : int;        //head or top index of the pushdown stack
 var mem                     : [bv64] bv8; //machine's virtual address space, 64-bit address to 8-bit data
 var rsp                     : bv64;       //stack pointer
 var pc                      : bv64;       //program counter or rip

 //SIR address space is contiguous, and bounded between _virtual_address_space_low and _virtual_address_space_high
 const _virtual_address_space_low  :  bv64;     //base address of SIR's virtual address space
 axiom _virtual_address_space_low  == 0bv64;
 const _virtual_address_space_high :  bv64;     //high address of SIR's virtual address space
 axiom _virtual_address_space_high == 320bv64;
 function AddrInSIR(x: bv64) : bool { GE_64(x, _virtual_address_space_low) && LT_64(x, _virtual_address_space_high) }

 const _U_low  :  bv64;          //base address of U's virtual address space
 axiom _U_low  == _virtual_address_space_low;
 const _U_high :  bv64;          //high address of U's virtual address space
 axiom _U_high == _bitmap_high;
 function AddrInU(x: bv64) : bool { GE_64(x, _U_low) && LT_64(x, _U_high) }

 const _L_low  :  bv64;          //base address of L's virtual address space
 axiom _L_low  == _bitmap_high;
 const _L_high :  bv64;          //high address of L's virtual address space
 axiom _L_high == _virtual_address_space_high;
 function AddrInL(x: bv64) : bool { GE_64(x, _L_low) && LT_64(x, _L_high) }

 const _bitmap_low  : bv64;      //base address of write_bitmap
 const _bitmap_high : bv64;
 axiom _bitmap_low  == 256bv64;  //high address of write_bitmap
 axiom _bitmap_high == 260bv64;
 function AddrInBitmap(x: bv64) : bool { GE_64(x, _bitmap_low) && LT_64(x, _bitmap_high) }

 const _stack_low  : bv64;       //base address of stack. Guard page below stack_low.
 const _stack_high : bv64;
 axiom _stack_low  == 64bv64;    //high address of stack. Note that RSP starts at high.
 axiom _stack_high == 192bv64;
 function AddrInStack(x: bv64) : bool { GE_64(x, _stack_low) && LT_64(x, _stack_high) }

 //Guard page below the stack to prevent stack overflow
 function AddrInGuardPage(x: bv64) : bool { GE_64(x, _virtual_address_space_low) && LT_64(x, _stack_low) }

 function startingAddress (id: bv64) : bv64; //starting address of a procedure with name "id"
 function endingAddress (id: bv64) : bv64;   //does id hold the first instruction of a procedure in U?
 function legal(addr: bv64) : bool;          //does addr hold the starting address of an instruction?
 function policy(addr: bv64) : bool;         //does addr hold the starting address of a procedure?
 function instructionLength(addr: bv64) : bv64; //how many bytes does the instruction at addr occupy?
 function {:inline} within_procedure(pc : bv64, id: bv64) : bool //is pc within the bounds of procedure id?
 {
   GE_64(pc, startingAddress(id)) && LT_64(pc, endingAddress(id)) && legal(pc)
 }

 // We only need to implement one procedure, which models an arbitrary x64 procedure.
 const fid_P : bv64; //function id
 axiom startingAddress(fid_P) == 2000bv64; //arbitrarily chosen
 axiom endingAddress(fid_P) == 2100bv64;   //arbitrarily chosen
 axiom policy(startingAddress(fid_P));
 axiom legal(startingAddress(fid_P));


 procedure theorem2_proof ()
 modifies mem, pc, rsp, pushdown_stack_contents, pushdown_stack_top;
 {
   //set up state by assuming predicates guaranteed to hold prior to entering arbitrary procedure P
   call init();
   //P contains all asserts needed to prove theorem 2
   call P();
 }

 // Helper function to initialize state before invoking P.
 // The postcondition of init is guaranteed to hold prior to entering arbitrary procedure of U
procedure {:inline 1} init()
modifies pc, rsp, pushdown_stack_contents, pushdown_stack_top;
{
  //Before calling into P, the program counter can be anywhere within U's code
  havoc pc;
  //Before calling into P, the stack pointer can be anywhere in the stack region, but aligned
  havoc rsp; assume AddrInStack(rsp) && rsp[3:0] == 0bv3;
  //arbitrary depth in the call chain, so pushdown_stack_top is arbitrary non-negative integer

  //havoc pushdown_stack_top; assume pushdown_stack_top >= 0;
  pushdown_stack_top := 0; //TODO:
}

//an arbitrary function in the dll
procedure {:inline 1} P()
modifies mem, pc, rsp, pushdown_stack_contents, pushdown_stack_top;
{
  var nestedOldMem, oldMem : [bv64] bv8;
  var nestedOldrsp, oldrsp : bv64;
  var nestedOldPc : bv64;

  var a_64 : bv64;
  var d_8 : bv8;
  var d_16: bv16;
  var d_32: bv32;
  var d_64: bv64;

  //unbounded sequence of instructions starting with a call and ending with ret
  call proof_call(startingAddress(fid_P), PLUS_64(rsp, 32bv64));

  oldrsp := rsp; oldMem := mem;
  assume (forall i: bv64 :: (AddrInStack(i) && LT_64(i,rsp)) ==> !writable(mem, i));

  //Arbitrary length sequence of arbitrary instructions
  while (*)
    invariant (forall i: bv64 :: (AddrInStack(i) && GE_64(i, oldrsp)) ==> (writable(oldMem, i) <==> writable(mem, i)));
    invariant LOAD_LE_64(mem, oldrsp) == LOAD_LE_64(oldMem, oldrsp);
    invariant LE_64(rsp, oldrsp) && rsp[3:0] == 0bv3;
    invariant !writable(mem, oldrsp);
    invariant (forall i: bv64 :: (AddrInStack(i) && GE_64(i, PLUS_64(oldrsp, 40bv64))) ==>
                                 (!writable(oldMem, i) ==> (LOAD_LE_64(oldMem, i[64:3] ++ 0bv3) == LOAD_LE_64(mem, i[64:3] ++ 0bv3))));
    invariant within_procedure(pc, fid_P);
  {
    havoc a_64; havoc d_8; havoc d_16; havoc d_32; havoc d_64;

    if (*) {
      call proof_store_8(a_64, d_8, oldrsp);

      pc := PLUS_64(pc, instructionLength(pc));
      assume within_procedure(pc, fid_P);
    } else if (*) {
      call proof_setrsp(a_64, oldrsp);

      pc := PLUS_64(pc, instructionLength(pc));
      assume within_procedure(pc, fid_P);
    } else if (*) {
      call proof_jmp(a_64, startingAddress(fid_P), endingAddress(fid_P), oldrsp);

      if (!(GE_64(a_64, startingAddress(fid_P)) && LT_64(a_64,endingAddress(fid_P)))) {
        assert procedure_postcondition(oldMem, mem, oldrsp, rsp, old(pc), pc);
        return;
      }
    } else if (*) {
      //a procedure call is a havoc with ensures replaced by assumes
      nestedOldMem := mem; nestedOldrsp := rsp; nestedOldPc := pc;

      //NOTE: sound because we have these obligations on call sites
      assume (forall i: bv64 :: (AddrInStack(i) && LT_64(i, rsp)) ==> !writable(mem, i));
      assume (LE_64(rsp, MINUS_64(oldrsp, 40bv64)));
      //procedure call is modeled as a havoc to state, followed by an assume that is provable on returns
      havoc mem; havoc rsp; havoc pc;
      //NOTE: sound because we prove it on remote jmps and returns
      assume procedure_postcondition(nestedOldMem, mem, nestedOldrsp, rsp, nestedOldPc, pc);

      pc := PLUS_64(pc, instructionLength(pc));
      assume within_procedure(pc, fid_P);
    }
  }

  call proof_ret(oldrsp);
  assert procedure_postcondition(old(mem), mem, old(rsp), rsp, old(pc), pc);
  return;
}



//x64 semantics of call instruction
procedure {:inline 1} x64_call (target: bv64)
modifies mem, pc, rsp;
{
  rsp := MINUS_64(rsp, 8bv64);
  mem := STORE_LE_64(mem, rsp, PLUS_64(pc, instructionLength(pc)));
  pc := target;
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_call (target: bv64, oldrsp: bv64)
modifies mem, pc, rsp, pushdown_stack_contents, pushdown_stack_top;
{
  //first assume the proof obligations generated by I (see Table 1 and 2 in paper)
  assume (policy(target));
  assume (forall i: bv64 :: (AddrInStack(i) && LT_64(i, rsp)) ==> !writable(mem, i));
  assume (LE_64(rsp, MINUS_64(oldrsp, 32bv64)));
  //storing to guard page leads to exception, so safe to assume this predicate.
  //we don't explicitly model paging semantics, hence this assume.
  assume !AddrInGuardPage(MINUS_64(rsp, 8bv64));

  //perform the
  call x64_call(target);

  //push the return address on the PDA
  call push(LOAD_LE_64(mem, rsp));
  //asserted by the PDA (see defn 3 in paper)
  assert policy(pc);
}



//x64 semantics of return instruction
procedure {:inline 1} x64_ret ()
modifies pc, rsp;
{
  pc := LOAD_LE_64(mem, rsp);
  rsp := PLUS_64(rsp, 8bv64);
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_ret (oldrsp: bv64)
modifies pc, rsp, pushdown_stack_contents, pushdown_stack_top;
{
  var pushdown_stack_pc : bv64;

  //following assumes are guaranteed by the proof obligations (see Table 1)
  assume (rsp == oldrsp);
  assume (forall i: bv64 :: (AddrInStack(i) && LT_64(i,rsp)) ==> !writable(mem, i));
  //page permissions guarantee that loading from guard page causes page fault exception
  assume !AddrInGuardPage(rsp);

  call x64_ret();

  //pop the return address off the PDA
  call pushdown_stack_pc := pop();
  //asserted by the PDA (see defn 3); compares PDA's return address with that on program stack
  assert pc == pushdown_stack_pc;
}



//x64 semantics of jmp instruction
procedure {:inline 1} x64_jmp(target: bv64)
modifies pc;
{
  pc := target;
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_jmp(target: bv64, start: bv64, end: bv64, oldrsp: bv64)
modifies pc;
{
  //following assumes are guaranteed by the proof obligations (see Table 1)
  assume (GE_64(target,start) && LT_64(target,end)) ==> legal(target);
  assume (!(GE_64(target,start) && LT_64(target,end))) ==> (rsp == oldrsp);
  assume (!(GE_64(target,start) && LT_64(target,end))) ==> (policy(target));
  assume (!(GE_64(target,start) && LT_64(target,end))) ==>
           (forall i: bv64 :: (AddrInStack(i) && LT_64(i,rsp)) ==> !writable(mem, i));

  call x64_jmp(target);

  //asserted by the PDA (see defn 3)
  assert policy(pc) || legal(pc); //asserted by the PDA (see defn 3)
}


//x64 model of store
procedure {:inline 1} x64_load_8(addr: bv64)
modifies mem;
{
  var value: bv8;
  value := LOAD_LE_8(mem, addr);
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_load_8(addr: bv64, oldrsp: bv64)
modifies mem;
{
  //page permissions guarantee this
  assume !AddrInGuardPage(addr);

  call x64_load_8(addr);

  assert !AddrInL(addr);  //asserted by the PDA (see defn 3)
}

//x64 model of store
procedure {:inline 1} x64_load_16(addr: bv64)
modifies mem;
{
  var value: bv16;
  value := LOAD_LE_16(mem, addr);
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_load_16(addr: bv64, oldrsp: bv64)
modifies mem;
{
  //page permissions guarantee this
  assume !AddrInGuardPage(addr);
  assume !AddrInGuardPage(PLUS_64(addr, 8bv64));

  call x64_load_8(addr);

  assert !AddrInL(addr);  //asserted by the PDA (see defn 3)
}

//x64 model of store
procedure {:inline 1} x64_store_8(addr: bv64, value: bv8)
modifies mem;
{
  mem := STORE_LE_8(mem, addr, value);
}
//assume that the instrumented proof obligations (I) hold, and assert the validity checks on the PDA transition
procedure {:inline 1} proof_store_8(addr: bv64, value: bv8, oldrsp: bv64)
modifies mem;
{
  //following assumes are guaranteed by the proof obligations (see Table 1)
  assume (AddrInStack(addr) &&
          GE_64(addr, oldrsp) &&
          !(GE_64(addr, PLUS_64(oldrsp, 8bv64)) &&
          LT_64(addr, PLUS_64(oldrsp, 40bv64)))) ==> writable(mem,addr);
  assume (AddrInBitmap(addr)) ==> (LT_64(largestAddrAffected_8(mem, addr, value), MINUS_64(oldrsp, 8bv64)));
  assume AddrInU(addr);
  //page permissions guarantee that storing to guard page causes page fault exception
  assume !AddrInGuardPage(addr);

  call x64_store_8(addr, value);

  assert AddrInU(addr);  //asserted by the PDA (see defn 3)
}

procedure {:inline 1} x64_store_16(addr: bv64, value: bv16)
modifies mem;
{
  mem := STORE_LE_16(mem, addr, value);
}
procedure {:inline 1} proof_store_16(addr: bv64, value: bv16, oldrsp: bv64)
modifies mem;
{
  call proof_store_8(PLUS_64(addr, 1bv64), value[16:8], oldrsp);
  call proof_store_8(addr, value[8:0], oldrsp);
}

procedure {:inline 1} x64_store_32(addr: bv64, value: bv32)
modifies mem;
{
  mem := STORE_LE_32(mem, addr, value);
}
procedure {:inline 1} proof_store_32(addr: bv64, value: bv32, oldrsp: bv64)
modifies mem;
{
  call proof_store_16(PLUS_64(addr, 2bv64), value[32:16], oldrsp);
  call proof_store_16(addr, value[16:0], oldrsp);
}

procedure {:inline 1} x64_store_64(addr: bv64, value: bv64)
modifies mem;
{
  mem := STORE_LE_64(mem, addr, value);
}
procedure {:inline 1} proof_store_64(addr: bv64, value: bv64, oldrsp: bv64)
modifies mem;
{
  call proof_store_32(PLUS_64(addr, 4bv64), value[64:32], oldrsp);
  call proof_store_32(addr, value[32:0], oldrsp);
}


//x64 semantics of store to rsp
procedure {:inline 1} x64_setrsp(newrsp: bv64)
modifies rsp;
{
  rsp := newrsp;
}
procedure {:inline 1} proof_setrsp(newrsp: bv64, oldrsp: bv64)
modifies rsp;
{
  //proof obligations in Table 1
  assume (newrsp[3:0] == 0bv3 && LE_64(newrsp, oldrsp));

  call x64_setrsp(newrsp);
}






function {:inline} procedure_postcondition(mem: [bv64] bv8, mem': [bv64] bv8, rsp: bv64, rsp': bv64, pc: bv64, pc': bv64) : bool
{
  (rsp' == rsp) &&
  (forall i: bv64 :: (AddrInStack(i) && GE_64(i, rsp')) ==> (writable(mem, i) <==> writable(mem', i))) &&
  (forall i: bv64 :: (AddrInStack(i) && GE_64(i, PLUS_64(rsp',40bv64)) && !writable(mem, i) ==> (LOAD_LE_64(mem, i[64:3] ++ 0bv3) == LOAD_LE_64(mem', i[64:3] ++ 0bv3))))
}

// used to push a return address on the pushdown stack
procedure {:inline 1} push(x: bv64)
modifies pushdown_stack_contents, pushdown_stack_top;
{
  pushdown_stack_contents[pushdown_stack_top] := x;
  pushdown_stack_top := pushdown_stack_top + 1;
}

// used to pop a return address from the pushdown stack
procedure {:inline 1} pop() returns (result: bv64)
modifies pushdown_stack_top;
{
  pushdown_stack_top := pushdown_stack_top - 1;
  result := pushdown_stack_contents[pushdown_stack_top];
}
