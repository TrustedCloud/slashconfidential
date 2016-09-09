//Run as: boogie prelude.bpl proof_soundness_theorem1.bpl /useArrayTheory

var shadow_stack_contents : [bv8] bv64;
var shadow_stack_top: bv8;
var mem : [bv64] bv8;
var RSP : bv64;
var RAX : bv64;
var RBX : bv64;
var pc  : bv64;

procedure {:inline 1} init_shadow_stack()
modifies shadow_stack_contents, shadow_stack_top;
{
  shadow_stack_top := 0bv8;
}

procedure {:inline 1} push(x: bv64)
modifies shadow_stack_contents, shadow_stack_top;
{
  shadow_stack_contents[shadow_stack_top] := x;
  shadow_stack_top := PLUS_8(shadow_stack_top, 1bv8);
  assert legal(x);
}

procedure {:inline 1} pop() returns (result: bv64)
modifies shadow_stack_top;
{
  assume GT_8(shadow_stack_top, 0bv8);
  shadow_stack_top := MINUS_8(shadow_stack_top, 1bv8);
  result := shadow_stack_contents[shadow_stack_top];
  assume legal(result);
}


function legal(addr: bv64) : bool; //does addr hold the starting address of an instruction?


const _virtual_address_space_low : bv64;
const _virtual_address_space_high : bv64;
axiom _virtual_address_space_low == 0bv64; //0bv64
axiom _virtual_address_space_high == 512bv64; //1073741824bv64
function {:inline} SIR(x: bv64) : bool { GE_64(x, _virtual_address_space_low) && LT_64(x, _virtual_address_space_high) }


const _bitmap_low: bv64;
const _bitmap_high: bv64;
axiom _bitmap_low == 320bv64; //1073745920bv64
axiom _bitmap_high == 324bv64; //1090523136bv64
function {:inline} AddrInBitmap(x: bv64) : bool { GE_64(x, _bitmap_low) && LT_64(x, _bitmap_high) }


const _stack_low: bv64;
const _stack_high: bv64;
axiom _stack_low == 64bv64; //536870912bv64
axiom _stack_high == 192bv64; //537919488bv64
function {:inline} AddrInStack(x: bv64) : bool { GE_64(x, _stack_low) && LT_64(x, _stack_high) }

const _heap_low: bv64;
const _heap_high: bv64;
axiom _heap_low == 256bv64; //536870912bv64
axiom _heap_high == 288bv64; //537919488bv64
function {:inline} AddrInHeap(x: bv64) : bool { GE_64(x, _heap_low) && LT_64(x, _heap_high) }

const _L_low: bv64;
const _L_high: bv64;
axiom _L_low == 400bv64;
axiom _L_high == 440bv64;
function {:inline} AddrInU(x: bv64) : bool { GE_64(x, _stack_low) && LT_64(x, _bitmap_high) }
function {:inline} AddrInL(x: bv64) : bool { GE_64(x, _L_low) && LT_64(x, _L_high) }

//x64 semantics of call instruction
procedure {:inline 1} x64_call (target: bv64)
modifies mem, pc, RSP;
{
  RSP := MINUS_64(RSP, 8bv64);
  mem := STORE_LE_64(mem, RSP, pc); assume AddrInStack(RSP); //otherwise /guard promises page fault
  pc := target;
}
procedure {:inline 1} proof_call (target: bv64)
modifies mem, pc, RSP, shadow_stack_contents, shadow_stack_top;
{
  //perform PDA transition first
  assume legal(target);
  assume legal(PLUS_64(pc, 1bv64)); //next instruction has to be legal
  call push(PLUS_64(pc, 1bv64));

  call x64_call(target);
}



//x64 semantics of return instruction
procedure {:inline 1} x64_ret ()
modifies pc, RSP;
{
  pc := LOAD_LE_64(mem, RSP); assume AddrInStack(RSP);
  RSP := PLUS_64(RSP, 8bv64);
}
procedure {:inline 1} proof_ret ()
modifies pc, RSP, shadow_stack_contents, shadow_stack_top;
{
  var shadow_stack_pc : bv64;
  call shadow_stack_pc := pop();
  assume LOAD_LE_64(mem, RSP) == shadow_stack_pc;

  call x64_ret();
}



//x64 semantics of jmp instruction
procedure {:inline 1} x64_jmp(target: bv64)
modifies pc;
{
  pc := target;
}
procedure {:inline 1} proof_jmp(target: bv64)
modifies pc;
{
  assume legal(target);

  call x64_jmp(target);
}



//x64 model of mov instruction
procedure {:inline 1} x64_store(addr: bv64, value: bv64)
modifies mem;
{
  mem := STORE_LE_64(mem, addr, value);
}
procedure {:inline 1} proof_store(addr: bv64, value: bv64)
modifies mem;
{
  assume AddrInU(addr);

  call x64_store(addr, value);
}


//x64 model of mov instruction
procedure {:inline 1} x64_load(addr: bv64)
modifies mem, RAX, RSP;
{
  RAX := LOAD_LE_64(mem, addr);
}
procedure {:inline 1} proof_load(addr: bv64)
modifies mem, RAX, RSP;
{
  assume !AddrInL(addr);

  call x64_load(addr);
}

//x64 model of mov instruction
procedure {:inline 1} x64_setRSP(addr: bv64)
modifies RSP;
{
  RSP := addr;
}
procedure {:inline 1} proof_setRSP(addr: bv64)
modifies mem, RAX, RSP;
{
  assume AddrInStack(addr);

  call x64_setRSP(addr);
}


procedure proof ()
modifies mem, RAX, RSP, pc, shadow_stack_contents, shadow_stack_top;
{
  call init();
  call U_main();
}

procedure {:inline 1} init()
modifies pc, RSP, shadow_stack_contents, shadow_stack_top;
{
  call init_shadow_stack();
  havoc pc; assume legal(pc); //we jump to U-entry which is definitely legal
  havoc RSP; assume AddrInStack(RSP);
}

procedure {:inline 1} U_main()
modifies mem, RAX, RSP, pc, shadow_stack_contents, shadow_stack_top;
{
  var target: bv64;
  var size: bv64;
  var address: bv64;
  var data: bv64;
  var ptr: bv64;
  var mem_old: [bv64] bv8;
  var b_send : bool;
  var b_havoc : bool;

  while (*) //essentially the loop that our PDA machine runs
  invariant legal(pc);
  invariant AddrInU(RSP);
  {
    //this model is only sound if the pc is always legal i.e. not in the middle of an instruction.
    //so before decoding the next instruction, we assert legal(pc)

    mem_old := mem;
    b_send := false;
    b_havoc := false;

    //a legal instruction can be a call l_api, load, store, jmp, call, ret
    if (*) {
      havoc size;
      call L_malloc(size);
    } else if (*) {
      havoc ptr;
      call L_free(ptr);
    } else if (*) {
      b_send := true;
      havoc ptr; havoc size;
      call L_send(ptr, size);
    } else if (*) {
      havoc ptr; havoc size;
      call L_recieve(ptr, size);
    } else if (*) {
      havoc address;
      call proof_load(address);
    } else if (*) {
      havoc address; havoc data;
      call proof_store(address, data);
    } else if (*) {
      havoc target;
      call proof_jmp(target);
    } else if (*) {
      havoc target;
      call proof_call(target);
    } else if (*) {
      call proof_ret();
    } else if (*) {
      havoc address;
      call proof_setRSP(address);
    } else if (*) {
      b_havoc := true;
      havoc mem;
      assume (forall i: bv64 :: (SIR(i)) ==> mem[i] == mem_old[i]);
    }

    assert (forall i: bv64 :: (!b_send && !b_havoc && !SIR(i)) ==> mem[i] == mem_old[i]);

  }
}

procedure L_malloc(size: bv64) returns ();
modifies mem, RAX, RSP, pc;
ensures (forall a: bv64 :: (!SIR(a) || (AddrInStack(a) && GE_64(a,old(RSP)))) ==> mem[a] == old(mem)[a]);
ensures (RSP == old(RSP));
ensures (forall a: bv64 :: AddrInStack(a) ==> writable(mem,a) == writable(old(mem),a));
ensures RAX == 0bv64 || (AddrInHeap(RAX) && AddrInHeap(PLUS_64(RAX,size)) && LE_64(RAX, PLUS_64(RAX,size)));
ensures legal(pc); //follows from RSP == old(RSP)

procedure L_free(ptr: bv64) returns ();
modifies mem, RAX, RSP, pc;
ensures (forall a: bv64 :: (!SIR(a) || (AddrInStack(a) && GE_64(a,old(RSP)))) ==> mem[a] == old(mem)[a]);
ensures (RSP == old(RSP));
ensures (forall a: bv64 :: AddrInStack(a) ==> writable(mem,a) == writable(old(mem),a));
ensures legal(pc); //follows from RSP == old(RSP)

procedure L_send(ptr: bv64, size: bv64) returns (); //returns ptr to the destination
modifies mem, RAX, RSP, pc;
ensures (forall a: bv64 :: (AddrInBitmap(a) || (AddrInStack(a) && GE_64(a,old(RSP)))) ==> mem[a] == old(mem)[a]);
ensures (RSP == old(RSP));
ensures legal(pc); //follows from RSP == old(RSP)

procedure L_recieve(ptr: bv64, size: bv64) returns ();
modifies mem, RAX, RSP, pc;
ensures (RSP == old(RSP));
ensures SIR(ptr) && SIR(PLUS_64(ptr,size)) && LE_64(ptr, PLUS_64(ptr,size));
ensures (forall a: bv64 ::  (GE_64(a, ptr) && LT_64(a,PLUS_64(ptr,size))) ==> (SIR(a) && writable(old(mem),a) && !AddrInBitmap(a)));
ensures (forall a: bv64 :: !(GE_64(a, ptr) && LT_64(a,PLUS_64(ptr,size))) ==> (mem[a] == old(mem)[a]));
ensures legal(pc); //follows from RSP == old(RSP)
