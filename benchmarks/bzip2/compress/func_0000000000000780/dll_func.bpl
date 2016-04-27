/* Bitvector operations */
function {:bvbuiltin "bvand"} AND_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvor"} OR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvxor"} XOR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvnot"} NOT_1(p1: bv1) : bv1;

function {:bvbuiltin "bvadd"} PLUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsub"} MINUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmul"} TIMES_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmod"} MOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsmod"} SMOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvshl"} LSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvlshr"} RSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvashr"} ARSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvand"} AND_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvor"} OR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvxor"} XOR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvult"} LT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvule"} LE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvugt"} GT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvuge"} GE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvslt"} SLT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvsle"} SLE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvneg"} NEG_8(p1: bv8) : bv8;
function {:bvbuiltin "bvnot"} NOT_8(p1: bv8) : bv8;

function {:bvbuiltin "bvadd"} PLUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsub"} MINUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmul"} TIMES_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmod"} MOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsmod"} SMOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvshl"} LSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvlshr"} RSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvashr"} ARSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvand"} AND_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvor"} OR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvxor"} XOR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvult"} LT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvule"} LE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvugt"} GT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvuge"} GE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvslt"} SLT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvsle"} SLE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvneg"} NEG_16(p1: bv16) : bv16;
function {:bvbuiltin "bvnot"} NOT_16(p1: bv16) : bv16;

function {:bvbuiltin "bvadd"} PLUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsub"} MINUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmul"} TIMES_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmod"} MOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsmod"} SMOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvshl"} LSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvlshr"} RSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvashr"} ARSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvand"} AND_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvor"} OR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvxor"} XOR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvult"} LT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvule"} LE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvugt"} GT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvuge"} GE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvslt"} SLT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvsle"} SLE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvneg"} NEG_32(p1: bv32) : bv32;
function {:bvbuiltin "bvnot"} NOT_32(p1: bv32) : bv32;

function {:bvbuiltin "bvadd"} PLUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsub"} MINUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmul"} TIMES_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmod"} MOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsmod"} SMOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvshl"} LSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvlshr"} RSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvashr"} ARSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvand"} AND_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvor"} OR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvxor"} XOR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvult"} LT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvule"} LE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvugt"} GT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvuge"} GE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvslt"} SLT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvsle"} SLE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvneg"} NEG_64(p1: bv64) : bv64;
function {:bvbuiltin "bvnot"} NOT_64(p1: bv64) : bv64;

function {:bvbuiltin "bvmul"} TIMES_128(p1: bv128, p2: bv128) : bv128;

/* Helpers */
function {:inline} bv2bool(x: bv1): bool { if (x == 0bv1) then false else true }
function {:inline} bool2bv(x: bool): bv1 { if (!x) then 0bv1 else 1bv1 }

/* Memory Model */
type virtual_addr_t = bv64;
type data_t = bv8;
type mem_t = [virtual_addr_t] data_t;

function {:inline} STORE_LE_8(mem : mem_t, addr : virtual_addr_t, value : bv8) : mem_t
  { mem[addr := value] }
function {:inline} STORE_LE_16(mem : mem_t, addr : virtual_addr_t, value : bv16) : mem_t
  {  STORE_LE_8(STORE_LE_8(mem, addr, value[8:0]), PLUS_64(addr, 1bv64), value[16:8]) }
function {:inline} STORE_LE_32(mem: mem_t, addr: virtual_addr_t, value: bv32) : mem_t
  { STORE_LE_16(STORE_LE_16(mem, addr, value[16:0]), PLUS_64(addr, 2bv64), value[32:16]) }
function {:inline} STORE_LE_64(mem: mem_t, addr: virtual_addr_t, value: bv64) : mem_t
  { STORE_LE_32(STORE_LE_32(mem, addr, value[32:0]), PLUS_64(addr, 4bv64), value[64:32]) }

function {:inline} LOAD_LE_8(mem: mem_t, addr: virtual_addr_t) : bv8
  { mem[addr] }
function {:inline} LOAD_LE_16(mem: mem_t, addr: virtual_addr_t) : bv16
  { LOAD_LE_8(mem, PLUS_64(addr, 1bv64)) ++ LOAD_LE_8(mem, addr) }
function {:inline} LOAD_LE_32(mem: mem_t, addr: virtual_addr_t) : bv32
  { LOAD_LE_16(mem, PLUS_64(addr, 2bv64)) ++ LOAD_LE_16(mem, addr) }
function {:inline} LOAD_LE_64(mem: mem_t, addr: virtual_addr_t) : bv64
  { LOAD_LE_32(mem, PLUS_64(addr, 4bv64)) ++ LOAD_LE_32(mem, addr) }

function REP_STOSB(mem: mem_t, rcx: bv64, rdi: bv64, al: bv8) : mem_t;
//This axiom assumes that direction flag is cleared, which is the assumption made by CRT, /guard, etc.
axiom (forall mem: mem_t, rcx: bv64, rdi: bv64, al: bv8 :: {REP_STOSB(mem, rcx, rdi, al)}
  (forall i : bv64 :: (GE_64(i, rdi) && LT_64(i, PLUS_64(rdi, rcx)) ==> REP_STOSB(mem, rcx, rdi, al)[i] == al) &&
                     (LT_64(i, rdi) || GE_64(i, PLUS_64(rdi, rcx)) ==> REP_STOSB(mem, rcx, rdi, al)[i] == mem[i])));


function {:inline} ITE_1(b : bool,  x : bv1,   y : bv1) : bv1 { if (b) then x else y }
function {:inline} ITE_8(b : bool,  x : bv8,   y : bv8) : bv8 { if (b) then x else y }
function {:inline} ITE_16(b : bool, x : bv16, y : bv16) : bv16 { if (b) then x else y }
function {:inline} ITE_32(b : bool, x : bv32, y : bv32) : bv32 { if (b) then x else y }
function {:inline} ITE_64(b : bool, x : bv64, y : bv64) : bv64 { if (b) then x else y }
function {:inline} ITE_128(b : bool, x : bv128, y : bv128) : bv128 { if (b) then x else y }

function {:inline} addrInBitmap(x: bv64) : bool { GE_64(x, _bitmap_low) && LT_64(x, _bitmap_high) }
function {:inline} addrInStack(x: bv64) : bool { GE_64(x, _stack_low) && LT_64(x, _stack_high) }

function {:inline} addrToBitmapAddrByte(addr: bv64) : bv64 {
  PLUS_64(RSHIFT_64(MINUS_64(addr, _virtual_address_space_low), 6bv64), _bitmap_low)
}

function {:inline} addrToBitmapAddrBit(addr: bv64) : bv8 {
  0bv5 ++ (RSHIFT_64(AND_64(MINUS_64(addr, _virtual_address_space_low), 63bv64), 3bv64))[3:0]
}

function {:inline} writable(mem: [bv64] bv8, addr: bv64) : bool
{
  bv2bool((RSHIFT_8(AND_8(LOAD_LE_8(mem, addrToBitmapAddrByte(addr)), LSHIFT_8(1bv8, addrToBitmapAddrBit(addr))), addrToBitmapAddrBit(addr)))[1:0])
}

function {:inline} anyAddrAffected_64(mem: [bv64] bv8, addr: bv64, new_value: bv64) : bool { LOAD_LE_64(mem, addr) != new_value }
function {:inline} anyAddrAffected_32(mem: [bv64] bv8, addr: bv64, new_value: bv32) : bool { LOAD_LE_32(mem, addr) != new_value }
function {:inline} anyAddrAffected_16(mem: [bv64] bv8, addr: bv64, new_value: bv16) : bool { LOAD_LE_16(mem, addr) != new_value }
function {:inline} anyAddrAffected_8 (mem: [bv64] bv8, addr: bv64, new_value: bv8)  : bool { LOAD_LE_8(mem, addr)  != new_value }

/* computes the largest address affected in an 8-bit update
   use this only if addr is within the bitmap and the update produces a new value (anyAddrAffected)
*/
function {:inline} largestAddrAffected_8(mem: [bv64] bv8, addr: bv64, new_value: bv8) : bv64
{
  PLUS_64(_virtual_address_space_low, PLUS_64(LSHIFT_64(MINUS_64(addr, _bitmap_low), 6bv64),
  (
    if (new_value[8:7] != LOAD_LE_8(mem, addr)[8:7]) then ( 63bv64 ) else (
    if (new_value[7:6] != LOAD_LE_8(mem, addr)[7:6]) then ( 55bv64 ) else (
    if (new_value[6:5] != LOAD_LE_8(mem, addr)[6:5]) then ( 47bv64 ) else (
    if (new_value[5:4] != LOAD_LE_8(mem, addr)[5:4]) then ( 39bv64 ) else (
    if (new_value[4:3] != LOAD_LE_8(mem, addr)[4:3]) then ( 31bv64 ) else (
    if (new_value[3:2] != LOAD_LE_8(mem, addr)[3:2]) then ( 23bv64 ) else (
    if (new_value[2:1] != LOAD_LE_8(mem, addr)[2:1]) then ( 15bv64 ) else (
    7bv64
    )))))))
  )))
}

/* computes the smallest address affected in an 8-bit update
   use this only if addr is within the bitmap and the update produces a new value (anyAddrAffected)
*/
function {:inline} smallestAddrAffected_8(mem: [bv64] bv8, addr: bv64, new_value: bv8) : bv64
{
  PLUS_64(_virtual_address_space_low, PLUS_64(LSHIFT_64(MINUS_64(addr, _bitmap_low), 6bv64),
  (
    if (new_value[1:0] != LOAD_LE_8(mem, addr)[1:0]) then ( 0bv64 ) else (
    if (new_value[2:1] != LOAD_LE_8(mem, addr)[2:1]) then ( 8bv64 ) else (
    if (new_value[3:2] != LOAD_LE_8(mem, addr)[3:2]) then ( 16bv64 ) else (
    if (new_value[4:3] != LOAD_LE_8(mem, addr)[4:3]) then ( 24bv64 ) else (
    if (new_value[5:4] != LOAD_LE_8(mem, addr)[5:4]) then ( 32bv64 ) else (
    if (new_value[6:5] != LOAD_LE_8(mem, addr)[6:5]) then ( 40bv64 ) else (
    if (new_value[7:6] != LOAD_LE_8(mem, addr)[7:6]) then ( 48bv64 ) else (
    56bv64
    )))))))
  )))
}


const _guard_writeTable_ptr : bv64;
const _guard_callTable_ptr : bv64;
const _bitmap_low : bv64;
const _bitmap_high : bv64;
const _stack_low : bv64;
const _stack_high : bv64;
const _virtual_address_space_low : bv64;
const _virtual_address_space_high : bv64;
const _function_addr_low : bv64;
const _function_addr_high : bv64;
axiom _guard_writeTable_ptr == 29888bv64;
axiom _guard_callTable_ptr == 29904bv64;
axiom _function_addr_low == 1920bv64;
axiom _function_addr_high == 2624bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x780:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x785:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x789:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x78e:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x792:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x797:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))), 8bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))), 8bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))), 8bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))))), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x79e:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x945;
}

label_0x7a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7a9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 640bv64)));

label_0x7af:
origDEST_9 := RAX[32:0];
origCOUNT_10 := AND_32(24bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ RSHIFT_32((RAX[32:0]), (AND_32(24bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), CF, LSHIFT_32(origDEST_9, (MINUS_32(32bv32, origCOUNT_10)))[32:31]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_10 == 1bv32)), origDEST_9[32:31], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_10 == 0bv32)), AF, unconstrained_2);

label_0x7b2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x7b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7bb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RAX, 116bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 116bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 116bv64)))));

label_0x7bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x7c4:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 80bv64));

label_0x7c8:
t1_15 := RCX;
t2_16 := RAX;
RCX := PLUS_64(RCX, t2_16);
CF := bool2bv(LT_64(RCX, t1_15));
OF := AND_1((bool2bv((t1_15[64:63]) == (t2_16[64:63]))), (XOR_1((t1_15[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_15)), t2_16)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x7cb:
mem := STORE_LE_64(mem, RSP, RCX);

label_0x7cf:
RAX := LOAD_LE_64(mem, RSP);

label_0x7d3:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x7d9:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x7de:
t_23 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)), 2bv64)), (XOR_64((RSHIFT_64(t_23, 4bv64)), t_23)))))[1:0]));
SF := t_23[64:63];
ZF := bool2bv(0bv64 == t_23);

label_0x7e1:
if (bv2bool(ZF)) {
  goto label_0x7e4;
}

label_0x7e3:
assume false;

label_0x7e4:
RAX := LOAD_LE_64(mem, RSP);

label_0x7e8:
origDEST_27 := RAX;
origCOUNT_28 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), CF, LSHIFT_64(origDEST_27, (MINUS_64(64bv64, origCOUNT_28)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_28 == 1bv64)), origDEST_27[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_28 == 0bv64)), AF, unconstrained_6);

label_0x7ec:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x7f3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x7f7:
RCX := LOAD_LE_64(mem, RSP);

label_0x7fb:
origDEST_33 := RCX;
origCOUNT_34 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), CF, LSHIFT_64(origDEST_33, (MINUS_64(64bv64, origCOUNT_34)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_34 == 1bv64)), origDEST_33[64:63], unconstrained_7));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_34 == 0bv64)), AF, unconstrained_8);

label_0x7ff:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_9;
SF := unconstrained_10;
AF := unconstrained_11;
PF := unconstrained_12;

label_0x803:
if (bv2bool(CF)) {
  goto label_0x806;
}

label_0x805:
assume false;

label_0x806:
RAX := LOAD_LE_64(mem, RSP);

label_0x80a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 48bv64))));

label_0x80f:
mem := STORE_LE_8(mem, RAX, RCX[32:0][8:0]);

label_0x811:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x816:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 116bv64)));

label_0x819:
t_39 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_39[32:31]) == (1bv32[32:31]))), (XOR_1((t_39[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_39)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x81b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x81f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x824:
t1_43 := RAX;
t2_44 := 116bv64;
RAX := PLUS_64(RAX, t2_44);
CF := bool2bv(LT_64(RAX, t1_43));
OF := AND_1((bool2bv((t1_43[64:63]) == (t2_44[64:63]))), (XOR_1((t1_43[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_43)), t2_44)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x828:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RAX);

label_0x82d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x832:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x838:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x83d:
t_51 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x840:
if (bv2bool(ZF)) {
  goto label_0x843;
}

label_0x842:
assume false;

label_0x843:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x848:
origDEST_55 := RAX;
origCOUNT_56 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), CF, LSHIFT_64(origDEST_55, (MINUS_64(64bv64, origCOUNT_56)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_56 == 1bv64)), origDEST_55[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_56 == 0bv64)), AF, unconstrained_16);

label_0x84c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x853:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x857:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x85c:
origDEST_61 := RCX;
origCOUNT_62 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_18);

label_0x860:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_19;
SF := unconstrained_20;
AF := unconstrained_21;
PF := unconstrained_22;

label_0x864:
if (bv2bool(CF)) {
  goto label_0x867;
}

label_0x866:
assume false;

label_0x867:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x86c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x870:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x872:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x877:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 640bv64)));

label_0x87d:
origDEST_67 := RAX[32:0];
origCOUNT_68 := AND_32(8bv32, (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32(8bv32, (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), CF, RSHIFT_32(origDEST_67, (MINUS_32(32bv32, origCOUNT_68)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv32)), AF, unconstrained_24);

label_0x880:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x884:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x889:
t1_73 := RAX;
t2_74 := 640bv64;
RAX := PLUS_64(RAX, t2_74);
CF := bool2bv(LT_64(RAX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x88f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RAX);

label_0x894:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x899:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x89f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x8a4:
t_81 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)), 2bv64)), (XOR_64((RSHIFT_64(t_81, 4bv64)), t_81)))))[1:0]));
SF := t_81[64:63];
ZF := bool2bv(0bv64 == t_81);

label_0x8a7:
if (bv2bool(ZF)) {
  goto label_0x8aa;
}

label_0x8a9:
assume false;

label_0x8aa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x8af:
origDEST_85 := RAX;
origCOUNT_86 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_27));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_28);

label_0x8b3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x8ba:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x8be:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x8c3:
origDEST_91 := RCX;
origCOUNT_92 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_29));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_30);

label_0x8c7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_31;
SF := unconstrained_32;
AF := unconstrained_33;
PF := unconstrained_34;

label_0x8cb:
if (bv2bool(CF)) {
  goto label_0x8ce;
}

label_0x8cd:
assume false;

label_0x8ce:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 16bv64));

label_0x8d3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x8d7:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x8d9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x8de:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 644bv64)));

label_0x8e4:
t_97 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 8bv32));
CF := bool2bv(LT_32(t_97, 8bv32));
OF := AND_32((XOR_32(t_97, 8bv32)), (XOR_32(t_97, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_97)), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x8e7:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x8eb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x8f0:
t1_101 := RAX;
t2_102 := 644bv64;
RAX := PLUS_64(RAX, t2_102);
CF := bool2bv(LT_64(RAX, t1_101));
OF := AND_1((bool2bv((t1_101[64:63]) == (t2_102[64:63]))), (XOR_1((t1_101[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_101)), t2_102)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x8f6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RAX);

label_0x8fb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x900:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x906:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x90b:
t_109 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)), 2bv64)), (XOR_64((RSHIFT_64(t_109, 4bv64)), t_109)))))[1:0]));
SF := t_109[64:63];
ZF := bool2bv(0bv64 == t_109);

label_0x90e:
if (bv2bool(ZF)) {
  goto label_0x911;
}

label_0x910:
assume false;

label_0x911:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x916:
origDEST_113 := RAX;
origCOUNT_114 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_38);

label_0x91a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x921:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x925:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x92a:
origDEST_119 := RCX;
origCOUNT_120 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), CF, LSHIFT_64(origDEST_119, (MINUS_64(64bv64, origCOUNT_120)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_120 == 1bv64)), origDEST_119[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_120 == 0bv64)), AF, unconstrained_40);

label_0x92e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x932:
if (bv2bool(CF)) {
  goto label_0x935;
}

label_0x934:
assume false;

label_0x935:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 24bv64));

label_0x93a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)));

label_0x93e:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x940:
goto label_0x792;

label_0x945:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x94a:
RCX := (0bv32 ++ 32bv32);

label_0x94f:
t_125 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (LOAD_LE_32(mem, PLUS_64(RAX, 644bv64)))));
CF := bool2bv(LT_32(t_125, (LOAD_LE_32(mem, PLUS_64(RAX, 644bv64)))));
OF := AND_32((XOR_32(t_125, (LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))))), (XOR_32(t_125, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_125)), (LOAD_LE_32(mem, PLUS_64(RAX, 644bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x955:
RAX := (0bv32 ++ RCX[32:0]);

label_0x957:
t_129 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)))));
CF := bool2bv(LT_32(t_129, (LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)))));
OF := AND_32((XOR_32(t_129, (LOAD_LE_32(mem, PLUS_64(RSP, 104bv64))))), (XOR_32(t_129, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_129)), (LOAD_LE_32(mem, PLUS_64(RSP, 104bv64))))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x95b:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x95e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 112bv64)));

label_0x962:
origDEST_133 := RAX[32:0];
origCOUNT_134 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), CF, RSHIFT_32(origDEST_133, (MINUS_32(32bv32, origCOUNT_134)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_45));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv32)), AF, unconstrained_46);

label_0x964:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x969:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 640bv64)));

label_0x96f:
RCX := (0bv32 ++ OR_32((RCX[32:0]), (RAX[32:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x971:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RCX[32:0]);

label_0x975:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x97a:
t1_141 := RAX;
t2_142 := 640bv64;
RAX := PLUS_64(RAX, t2_142);
CF := bool2bv(LT_64(RAX, t1_141));
OF := AND_1((bool2bv((t1_141[64:63]) == (t2_142[64:63]))), (XOR_1((t1_141[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_141)), t2_142)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x980:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x985:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x98a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x990:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x995:
t_149 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_49;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))))[1:0]));
SF := t_149[64:63];
ZF := bool2bv(0bv64 == t_149);

label_0x998:
if (bv2bool(ZF)) {
  goto label_0x99b;
}

label_0x99a:
assume false;

label_0x99b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x9a0:
origDEST_153 := RAX;
origCOUNT_154 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_51);

label_0x9a4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x9ab:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x9af:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x9b4:
origDEST_159 := RCX;
origCOUNT_160 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_52));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_53);

label_0x9b8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_54;
SF := unconstrained_55;
AF := unconstrained_56;
PF := unconstrained_57;

label_0x9bc:
if (bv2bool(CF)) {
  goto label_0x9bf;
}

label_0x9be:
assume false;

label_0x9bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x9c4:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x9c8:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x9ca:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9cf:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 104bv64)));

label_0x9d3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 644bv64)));

label_0x9d9:
t1_165 := RAX[32:0];
t2_166 := RCX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_166));
CF := bool2bv(LT_32((RAX[32:0]), t1_165));
OF := AND_1((bool2bv((t1_165[32:31]) == (t2_166[32:31]))), (XOR_1((t1_165[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_165)), t2_166)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x9db:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), RAX[32:0]);

label_0x9df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x9e4:
t1_171 := RAX;
t2_172 := 644bv64;
RAX := PLUS_64(RAX, t2_172);
CF := bool2bv(LT_64(RAX, t1_171));
OF := AND_1((bool2bv((t1_171[64:63]) == (t2_172[64:63]))), (XOR_1((t1_171[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_171)), t2_172)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9ea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x9ef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x9f4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x9fa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x9ff:
t_179 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)), 2bv64)), (XOR_64((RSHIFT_64(t_179, 4bv64)), t_179)))))[1:0]));
SF := t_179[64:63];
ZF := bool2bv(0bv64 == t_179);

label_0xa02:
if (bv2bool(ZF)) {
  goto label_0xa05;
}

label_0xa04:
assume false;

label_0xa05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xa0a:
origDEST_183 := RAX;
origCOUNT_184 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), CF, LSHIFT_64(origDEST_183, (MINUS_64(64bv64, origCOUNT_184)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_184 == 1bv64)), origDEST_183[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_184 == 0bv64)), AF, unconstrained_61);

label_0xa0e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xa15:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xa19:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xa1e:
origDEST_189 := RCX;
origCOUNT_190 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), CF, LSHIFT_64(origDEST_189, (MINUS_64(64bv64, origCOUNT_190)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_190 == 1bv64)), origDEST_189[64:63], unconstrained_62));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_190 == 0bv64)), AF, unconstrained_63);

label_0xa22:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_64;
SF := unconstrained_65;
AF := unconstrained_66;
PF := unconstrained_67;

label_0xa26:
if (bv2bool(CF)) {
  goto label_0xa29;
}

label_0xa28:
assume false;

label_0xa29:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xa2e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 68bv64)));

label_0xa32:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xa34:
t1_195 := RSP;
t2_196 := 88bv64;
RSP := PLUS_64(RSP, t2_196);
CF := bool2bv(LT_64(RSP, t1_195));
OF := AND_1((bool2bv((t1_195[64:63]) == (t2_196[64:63]))), (XOR_1((t1_195[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_195)), t2_196)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xa38:

ra_201 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_10,origCOUNT_114,origCOUNT_120,origCOUNT_134,origCOUNT_154,origCOUNT_160,origCOUNT_184,origCOUNT_190,origCOUNT_28,origCOUNT_34,origCOUNT_56,origCOUNT_62,origCOUNT_68,origCOUNT_86,origCOUNT_92,origDEST_113,origDEST_119,origDEST_133,origDEST_153,origDEST_159,origDEST_183,origDEST_189,origDEST_27,origDEST_33,origDEST_55,origDEST_61,origDEST_67,origDEST_85,origDEST_9,origDEST_91,ra_201,t1_101,t1_141,t1_15,t1_165,t1_171,t1_195,t1_43,t1_73,t2_102,t2_142,t2_16,t2_166,t2_172,t2_196,t2_44,t2_74,t_1,t_109,t_125,t_129,t_149,t_179,t_23,t_39,t_5,t_51,t_81,t_97;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_12: bv1;
const unconstrained_13: bv1;
const unconstrained_14: bv1;
const unconstrained_15: bv1;
const unconstrained_16: bv1;
const unconstrained_17: bv1;
const unconstrained_18: bv1;
const unconstrained_19: bv1;
const unconstrained_2: bv1;
const unconstrained_20: bv1;
const unconstrained_21: bv1;
const unconstrained_22: bv1;
const unconstrained_23: bv1;
const unconstrained_24: bv1;
const unconstrained_25: bv1;
const unconstrained_26: bv1;
const unconstrained_27: bv1;
const unconstrained_28: bv1;
const unconstrained_29: bv1;
const unconstrained_3: bv1;
const unconstrained_30: bv1;
const unconstrained_31: bv1;
const unconstrained_32: bv1;
const unconstrained_33: bv1;
const unconstrained_34: bv1;
const unconstrained_35: bv1;
const unconstrained_36: bv1;
const unconstrained_37: bv1;
const unconstrained_38: bv1;
const unconstrained_39: bv1;
const unconstrained_4: bv1;
const unconstrained_40: bv1;
const unconstrained_41: bv1;
const unconstrained_42: bv1;
const unconstrained_43: bv1;
const unconstrained_44: bv1;
const unconstrained_45: bv1;
const unconstrained_46: bv1;
const unconstrained_47: bv1;
const unconstrained_48: bv1;
const unconstrained_49: bv1;
const unconstrained_5: bv1;
const unconstrained_50: bv1;
const unconstrained_51: bv1;
const unconstrained_52: bv1;
const unconstrained_53: bv1;
const unconstrained_54: bv1;
const unconstrained_55: bv1;
const unconstrained_56: bv1;
const unconstrained_57: bv1;
const unconstrained_58: bv1;
const unconstrained_59: bv1;
const unconstrained_6: bv1;
const unconstrained_60: bv1;
const unconstrained_61: bv1;
const unconstrained_62: bv1;
const unconstrained_63: bv1;
const unconstrained_64: bv1;
const unconstrained_65: bv1;
const unconstrained_66: bv1;
const unconstrained_67: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_10: bv32;
var origCOUNT_114: bv64;
var origCOUNT_120: bv64;
var origCOUNT_134: bv32;
var origCOUNT_154: bv64;
var origCOUNT_160: bv64;
var origCOUNT_184: bv64;
var origCOUNT_190: bv64;
var origCOUNT_28: bv64;
var origCOUNT_34: bv64;
var origCOUNT_56: bv64;
var origCOUNT_62: bv64;
var origCOUNT_68: bv32;
var origCOUNT_86: bv64;
var origCOUNT_92: bv64;
var origDEST_113: bv64;
var origDEST_119: bv64;
var origDEST_133: bv32;
var origDEST_153: bv64;
var origDEST_159: bv64;
var origDEST_183: bv64;
var origDEST_189: bv64;
var origDEST_27: bv64;
var origDEST_33: bv64;
var origDEST_55: bv64;
var origDEST_61: bv64;
var origDEST_67: bv32;
var origDEST_85: bv64;
var origDEST_9: bv32;
var origDEST_91: bv64;
var ra_201: bv64;
var t1_101: bv64;
var t1_141: bv64;
var t1_15: bv64;
var t1_165: bv32;
var t1_171: bv64;
var t1_195: bv64;
var t1_43: bv64;
var t1_73: bv64;
var t2_102: bv64;
var t2_142: bv64;
var t2_16: bv64;
var t2_166: bv32;
var t2_172: bv64;
var t2_196: bv64;
var t2_44: bv64;
var t2_74: bv64;
var t_1: bv64;
var t_109: bv64;
var t_125: bv32;
var t_129: bv32;
var t_149: bv64;
var t_179: bv64;
var t_23: bv64;
var t_39: bv32;
var t_5: bv32;
var t_51: bv64;
var t_81: bv64;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1264bv64);
axiom policy(1456bv64);
axiom policy(1920bv64);
axiom policy(2624bv64);
axiom policy(2768bv64);
axiom policy(2816bv64);
axiom policy(3200bv64);
axiom policy(6800bv64);
