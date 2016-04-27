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
axiom _guard_writeTable_ptr == 24992bv64;
axiom _guard_callTable_ptr == 25008bv64;
axiom _function_addr_low == 6960bv64;
axiom _function_addr_high == 7418bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x1b30:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RBP);

label_0x1b35:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x1b36:
t_3 := R12;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_3);

label_0x1b38:
t_5 := R15;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_5);

label_0x1b3a:
t_7 := RSP;
RSP := MINUS_64(RSP, 240bv64);
CF := bool2bv(LT_64(t_7, 240bv64));
OF := AND_64((XOR_64(t_7, 240bv64)), (XOR_64(t_7, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_7)), 240bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1b41:
R15 := LOAD_LE_64(mem, PLUS_64((PLUS_64(18008bv64, 6984bv64)), 0bv64));

label_0x1b48:
RDX := PLUS_64(RSP, 48bv64)[64:0];

label_0x1b4d:
R12 := RCX;

label_0x1b50:
origDEST_11 := RDX;
origCOUNT_12 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RDX := RSHIFT_64(RDX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), CF, LSHIFT_64(origDEST_11, (MINUS_64(64bv64, origCOUNT_12)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv64)), origDEST_11[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), SF, RDX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), ZF, bool2bv(0bv64 == RDX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv64)), AF, unconstrained_2);

label_0x1b54:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x1b59:
RAX := (0bv32 ++ 1bv32);

label_0x1b5e:
origDEST_17 := RCX;
origCOUNT_18 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_4);

label_0x1b62:
RBP := R9;

label_0x1b65:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1b68:
R10 := R8;

label_0x1b6b:
origDEST_25 := RAX;
origCOUNT_26 := AND_64(RCX, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(RCX, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), CF, RSHIFT_64(origDEST_25, (MINUS_64(64bv64, origCOUNT_26)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_26 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_26 == 0bv64)), AF, unconstrained_7);

label_0x1b6e:
mem := STORE_LE_64(mem, PLUS_64(R15, RDX), OR_64((LOAD_LE_64(mem, PLUS_64(R15, RDX))), RAX));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R15, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R15, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R15, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R15, RDX))))))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R15, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R15, RDX))))), 2bv64)), (XOR_64((RSHIFT_64((LOAD_LE_64(mem, PLUS_64(R15, RDX))), 4bv64)), (LOAD_LE_64(mem, PLUS_64(R15, RDX))))))))[1:0]));
SF := LOAD_LE_64(mem, PLUS_64(R15, RDX))[64:63];
ZF := bool2bv(0bv64 == (LOAD_LE_64(mem, PLUS_64(R15, RDX))));

label_0x1b72:
RDI := OR_64(RDI, 4294967295bv32 ++ 4294967295bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))))[1:0]));
SF := RDI[64:63];
ZF := bool2bv(0bv64 == RDI);

label_0x1b76:
RCX := RDI;

label_0x1b79:


label_0x1b80:
t_35 := RCX;
RCX := PLUS_64(RCX, 1bv64);
OF := AND_1((bool2bv((t_35[64:63]) == (1bv64[64:63]))), (XOR_1((t_35[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_35)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1b83:
t_39 := MINUS_8((LOAD_LE_8(mem, PLUS_64(R8, RCX))), 0bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(R8, RCX))), 0bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(R8, RCX))), 0bv8)), (XOR_8((LOAD_LE_8(mem, PLUS_64(R8, RCX))), t_39)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_39, (LOAD_LE_8(mem, PLUS_64(R8, RCX))))), 0bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_39, 4bv8)), t_39)), 2bv8)), (XOR_8((RSHIFT_8(t_39, 4bv8)), t_39)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_39, 4bv8)), t_39)), 2bv8)), (XOR_8((RSHIFT_8(t_39, 4bv8)), t_39)))))[1:0]));
SF := t_39[8:7];
ZF := bool2bv(0bv8 == t_39);

label_0x1b88:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1b80;
}

label_0x1b8a:
t_43 := AND_64(RCX, RCX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x1b8d:
if (bv2bool(ZF)) {
  goto label_0x1cbd;
}

label_0x1b93:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RSI);

label_0x1b9b:
RSI := (0bv32 ++ 0bv32);
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1b9d:
R8 := (0bv32 ++ RSI[32:0]);

label_0x1ba0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), R14);

label_0x1ba8:
R14 := (0bv32 ++ RSI[32:0]);

label_0x1bab:
t_47 := MINUS_8((LOAD_LE_8(mem, R10)), (RSI[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, R10)), (RSI[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, R10)), (RSI[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, R10)), t_47)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_47, (LOAD_LE_8(mem, R10)))), (RSI[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_47, 4bv8)), t_47)), 2bv8)), (XOR_8((RSHIFT_8(t_47, 4bv8)), t_47)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_47, 4bv8)), t_47)), 2bv8)), (XOR_8((RSHIFT_8(t_47, 4bv8)), t_47)))))[1:0]));
SF := t_47[8:7];
ZF := bool2bv(0bv8 == t_47);

label_0x1bae:
if (bv2bool(ZF)) {
  goto label_0x1cad;
}

label_0x1bb4:
RDX := R10;

label_0x1bb7:


label_0x1bc0:
RAX := (ITE_64(bv2bool(R8[32:0][32:31]) ,(1bv32 ++ R8[32:0]) ,(0bv32 ++ R8[32:0])));

label_0x1bc3:
t_51 := MINUS_64(RAX, RCX);
CF := bool2bv(LT_64(RAX, RCX));
OF := AND_64((XOR_64(RAX, RCX)), (XOR_64(RAX, t_51)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_51, RAX)), RCX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x1bc6:
if (bv2bool(NOT_1(CF))) {
  goto label_0x1cad;
}

label_0x1bcc:
t_55 := MINUS_8((LOAD_LE_8(mem, RDX)), 9bv8);
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDX)), 9bv8));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDX)), 9bv8)), (XOR_8((LOAD_LE_8(mem, RDX)), t_55)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_55, (LOAD_LE_8(mem, RDX)))), 9bv8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_55, 4bv8)), t_55)), 2bv8)), (XOR_8((RSHIFT_8(t_55, 4bv8)), t_55)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_55, 4bv8)), t_55)), 2bv8)), (XOR_8((RSHIFT_8(t_55, 4bv8)), t_55)))))[1:0]));
SF := t_55[8:7];
ZF := bool2bv(0bv8 == t_55);

label_0x1bcf:
if (bv2bool(ZF)) {
  goto label_0x1be1;
}

label_0x1bd1:
t_59 := RDX;
RDX := PLUS_64(RDX, 1bv64);
OF := AND_1((bool2bv((t_59[64:63]) == (1bv64[64:63]))), (XOR_1((t_59[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t_59)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x1bd4:
t_63 := R8[32:0];
R8 := (0bv32 ++ PLUS_32((R8[32:0]), 1bv32));
OF := AND_1((bool2bv((t_63[32:31]) == (1bv32[32:31]))), (XOR_1((t_63[32:31]), (R8[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((R8[32:0]), t_63)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((R8[32:0]), 4bv32)), (R8[32:0]))))))[1:0]));
SF := R8[32:0][32:31];
ZF := bool2bv(0bv32 == (R8[32:0]));

label_0x1bd7:
t_67 := MINUS_8((LOAD_LE_8(mem, RDX)), (RSI[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RDX)), (RSI[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, RDX)), (RSI[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, RDX)), t_67)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_67, (LOAD_LE_8(mem, RDX)))), (RSI[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_67, 4bv8)), t_67)), 2bv8)), (XOR_8((RSHIFT_8(t_67, 4bv8)), t_67)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_67, 4bv8)), t_67)), 2bv8)), (XOR_8((RSHIFT_8(t_67, 4bv8)), t_67)))))[1:0]));
SF := t_67[8:7];
ZF := bool2bv(0bv8 == t_67);

label_0x1bda:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1bc0;
}

label_0x1bdc:
goto label_0x1cad;

label_0x1be1:
R8 := PLUS_64(RSP, 48bv64)[64:0];

label_0x1be6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RBX);

label_0x1bee:
RDX := PLUS_64((PLUS_64(13923bv64, 7157bv64)), 0bv64)[64:0];

label_0x1bf5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RSI);

label_0x1bfa:
RCX := R10;

label_0x1bfd:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7170bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1f90"} true;
call arbitrary_func();

label_0x1c02:
RBX := (0bv32 ++ RSI[32:0]);

label_0x1c04:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x1c07:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c0d:


label_0x1c10:
t_75 := MINUS_32((RBX[32:0]), 4bv32);
CF := bool2bv(LT_32((RBX[32:0]), 4bv32));
OF := AND_32((XOR_32((RBX[32:0]), 4bv32)), (XOR_32((RBX[32:0]), t_75)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_75, (RBX[32:0]))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)), 2bv32)), (XOR_32((RSHIFT_32(t_75, 4bv32)), t_75)))))[1:0]));
SF := t_75[32:31];
ZF := bool2bv(0bv32 == t_75);

label_0x1c13:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c33;
}

label_0x1c15:
RCX := RDI;

label_0x1c18:


label_0x1c20:
t_79 := RCX;
RCX := PLUS_64(RCX, 1bv64);
OF := AND_1((bool2bv((t_79[64:63]) == (1bv64[64:63]))), (XOR_1((t_79[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_79)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1c23:
t_83 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RAX, RCX))), (R14[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RAX, RCX))), (R14[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RAX, RCX))), (R14[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, PLUS_64(RAX, RCX))), t_83)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_83, (LOAD_LE_8(mem, PLUS_64(RAX, RCX))))), (R14[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_83, 4bv8)), t_83)), 2bv8)), (XOR_8((RSHIFT_8(t_83, 4bv8)), t_83)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_83, 4bv8)), t_83)), 2bv8)), (XOR_8((RSHIFT_8(t_83, 4bv8)), t_83)))))[1:0]));
SF := t_83[8:7];
ZF := bool2bv(0bv8 == t_83);

label_0x1c27:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c20;
}

label_0x1c29:
t_87 := AND_64(RCX, RCX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_13;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))))[1:0]));
SF := t_87[64:63];
ZF := bool2bv(0bv64 == t_87);

label_0x1c2c:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c2e:
RSI := RAX;

label_0x1c31:
goto label_0x1c3a;

label_0x1c33:
t_91 := MINUS_32((RBX[32:0]), 13bv32);
CF := bool2bv(LT_32((RBX[32:0]), 13bv32));
OF := AND_32((XOR_32((RBX[32:0]), 13bv32)), (XOR_32((RBX[32:0]), t_91)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_91, (RBX[32:0]))), 13bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)), 2bv32)), (XOR_32((RSHIFT_32(t_91, 4bv32)), t_91)))))[1:0]));
SF := t_91[32:31];
ZF := bool2bv(0bv32 == t_91);

label_0x1c36:
if (bv2bool(ZF)) {
  goto label_0x1c60;
}

label_0x1c38:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x1c71;
}

label_0x1c3a:
R8 := PLUS_64(RSP, 48bv64)[64:0];

label_0x1c3f:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_14;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1c41:
RDX := PLUS_64((PLUS_64(13840bv64, 7240bv64)), 0bv64)[64:0];

label_0x1c48:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7245bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1f90"} true;
call arbitrary_func();

label_0x1c4d:
t_95 := RBX[32:0];
RBX := (0bv32 ++ PLUS_32((RBX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_95[32:31]) == (1bv32[32:31]))), (XOR_1((t_95[32:31]), (RBX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RBX[32:0]), t_95)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBX[32:0]), 4bv32)), (RBX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBX[32:0]), 4bv32)), (RBX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RBX[32:0]), 4bv32)), (RBX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RBX[32:0]), 4bv32)), (RBX[32:0]))))))[1:0]));
SF := RBX[32:0][32:31];
ZF := bool2bv(0bv32 == (RBX[32:0]));

label_0x1c4f:
t_99 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)), 2bv64)), (XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)), 2bv64)), (XOR_64((RSHIFT_64(t_99, 4bv64)), t_99)))))[1:0]));
SF := t_99[64:63];
ZF := bool2bv(0bv64 == t_99);

label_0x1c52:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c10;
}

label_0x1c54:
t_103 := MINUS_32((RBX[32:0]), 13bv32);
CF := bool2bv(LT_32((RBX[32:0]), 13bv32));
OF := AND_32((XOR_32((RBX[32:0]), 13bv32)), (XOR_32((RBX[32:0]), t_103)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_103, (RBX[32:0]))), 13bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))))[1:0]));
SF := t_103[32:31];
ZF := bool2bv(0bv32 == t_103);

label_0x1c57:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x1ca5;
}

label_0x1c59:
goto label_0x1c71;

label_0x1c5b:


label_0x1c60:
t_107 := RDI;
RDI := PLUS_64(RDI, 1bv64);
OF := AND_1((bool2bv((t_107[64:63]) == (1bv64[64:63]))), (XOR_1((t_107[64:63]), (RDI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDI, t_107)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)), 2bv64)), (XOR_64((RSHIFT_64(RDI, 4bv64)), RDI)))))[1:0]));
SF := RDI[64:63];
ZF := bool2bv(0bv64 == RDI);

label_0x1c63:
t_111 := MINUS_8((LOAD_LE_8(mem, PLUS_64(RAX, RDI))), (R14[32:0][8:0]));
CF := bool2bv(LT_8((LOAD_LE_8(mem, PLUS_64(RAX, RDI))), (R14[32:0][8:0])));
OF := AND_8((XOR_8((LOAD_LE_8(mem, PLUS_64(RAX, RDI))), (R14[32:0][8:0]))), (XOR_8((LOAD_LE_8(mem, PLUS_64(RAX, RDI))), t_111)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_111, (LOAD_LE_8(mem, PLUS_64(RAX, RDI))))), (R14[32:0][8:0]))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_111, 4bv8)), t_111)), 2bv8)), (XOR_8((RSHIFT_8(t_111, 4bv8)), t_111)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_111, 4bv8)), t_111)), 2bv8)), (XOR_8((RSHIFT_8(t_111, 4bv8)), t_111)))))[1:0]));
SF := t_111[8:7];
ZF := bool2bv(0bv8 == t_111);

label_0x1c67:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c60;
}

label_0x1c69:
t_115 := AND_64(RDI, RDI);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)), 2bv64)), (XOR_64((RSHIFT_64(t_115, 4bv64)), t_115)))))[1:0]));
SF := t_115[64:63];
ZF := bool2bv(0bv64 == t_115);

label_0x1c6c:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c6e:
R14 := RAX;

label_0x1c71:
t_119 := AND_64(RSI, RSI);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_17;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)), 2bv64)), (XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)), 2bv64)), (XOR_64((RSHIFT_64(t_119, 4bv64)), t_119)))))[1:0]));
SF := t_119[64:63];
ZF := bool2bv(0bv64 == t_119);

label_0x1c74:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c76:
t_123 := AND_64(R14, R14);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)), 2bv64)), (XOR_64((RSHIFT_64(t_123, 4bv64)), t_123)))))[1:0]));
SF := t_123[64:63];
ZF := bool2bv(0bv64 == t_123);

label_0x1c79:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c7b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, R14)));

label_0x1c7f:
t_127 := MINUS_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13783bv64, 7301bv64)), 0bv64))));
CF := bool2bv(LT_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13783bv64, 7301bv64)), 0bv64)))));
OF := AND_8((XOR_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13783bv64, 7301bv64)), 0bv64))))), (XOR_8((RAX[32:0][8:0]), t_127)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_127, (RAX[32:0][8:0]))), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13783bv64, 7301bv64)), 0bv64))))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_127, 4bv8)), t_127)), 2bv8)), (XOR_8((RSHIFT_8(t_127, 4bv8)), t_127)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_127, 4bv8)), t_127)), 2bv8)), (XOR_8((RSHIFT_8(t_127, 4bv8)), t_127)))))[1:0]));
SF := t_127[8:7];
ZF := bool2bv(0bv8 == t_127);

label_0x1c85:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1c94;
}

label_0x1c87:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(R14, 1bv64))));

label_0x1c8c:
t_131 := MINUS_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13771bv64, 7314bv64)), 0bv64))));
CF := bool2bv(LT_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13771bv64, 7314bv64)), 0bv64)))));
OF := AND_8((XOR_8((RAX[32:0][8:0]), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13771bv64, 7314bv64)), 0bv64))))), (XOR_8((RAX[32:0][8:0]), t_131)))[8:7];
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8(t_131, (RAX[32:0][8:0]))), (LOAD_LE_8(mem, PLUS_64((PLUS_64(13771bv64, 7314bv64)), 0bv64))))))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_131, 4bv8)), t_131)), 2bv8)), (XOR_8((RSHIFT_8(t_131, 4bv8)), t_131)))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8(t_131, 4bv8)), t_131)), 2bv8)), (XOR_8((RSHIFT_8(t_131, 4bv8)), t_131)))))[1:0]));
SF := t_131[8:7];
ZF := bool2bv(0bv8 == t_131);

label_0x1c92:
if (bv2bool(ZF)) {
  goto label_0x1ca5;
}

label_0x1c94:
R9 := RBP;

label_0x1c97:
R8 := R14;

label_0x1c9a:
RDX := RSI;

label_0x1c9d:
RCX := R12;

label_0x1ca0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 7333bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1df0"} true;
call arbitrary_func();

label_0x1ca5:
RBX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x1cad:
RSI := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x1cb5:
R14 := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x1cbd:
RAX := PLUS_64(RSP, 64bv64)[64:0];

label_0x1cc2:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_20);

label_0x1cc6:
RCX := PLUS_64(RSP, 64bv64)[64:0];

label_0x1ccb:
t1_141 := R15;
t2_142 := RAX;
R15 := PLUS_64(R15, t2_142);
CF := bool2bv(LT_64(R15, t1_141));
OF := AND_1((bool2bv((t1_141[64:63]) == (t2_142[64:63]))), (XOR_1((t1_141[64:63]), (R15[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(R15, t1_141)), t2_142)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(R15, 4bv64)), R15)), 2bv64)), (XOR_64((RSHIFT_64(R15, 4bv64)), R15)))))[1:0]));
SF := R15[64:63];
ZF := bool2bv(0bv64 == R15);

label_0x1cce:
origDEST_147 := RCX;
origCOUNT_148 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), CF, LSHIFT_64(origDEST_147, (MINUS_64(64bv64, origCOUNT_148)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_148 == 1bv64)), origDEST_147[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_148 == 0bv64)), AF, unconstrained_22);

label_0x1cd2:
RAX := (0bv32 ++ 254bv32);

label_0x1cd7:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_23;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1cda:
origDEST_155 := RAX[32:0][8:0];
origCOUNT_156 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), CF, RSHIFT_8(origDEST_155, (MINUS_8(8bv8, origCOUNT_156)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_156 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_156 == 0bv8)), AF, unconstrained_25);

label_0x1cdc:
mem := STORE_LE_8(mem, R15, AND_8((LOAD_LE_8(mem, R15)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_26;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, R15)), 4bv8)), (LOAD_LE_8(mem, R15)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, R15)), 4bv8)), (LOAD_LE_8(mem, R15)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, R15)), 4bv8)), (LOAD_LE_8(mem, R15)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, R15)), 4bv8)), (LOAD_LE_8(mem, R15)))))))[1:0]));
SF := LOAD_LE_8(mem, R15)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, R15)));

label_0x1cdf:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_27;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1ce1:
mem := STORE_LE_8(mem, PLUS_64(R15, 4294967295bv32 ++ 4294967295bv32), RAX[32:0][8:0]);

label_0x1ce5:
RBP := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x1ced:
t1_163 := RSP;
t2_164 := 240bv64;
RSP := PLUS_64(RSP, t2_164);
CF := bool2bv(LT_64(RSP, t1_163));
OF := AND_1((bool2bv((t1_163[64:63]) == (t2_164[64:63]))), (XOR_1((t1_163[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_163)), t2_164)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1cf4:
R15 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x1cf6:
R12 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x1cf8:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x1cf9:

ra_169 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R10,R12,R14,R15,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_12,origCOUNT_136,origCOUNT_148,origCOUNT_156,origCOUNT_18,origCOUNT_26,origDEST_11,origDEST_135,origDEST_147,origDEST_155,origDEST_17,origDEST_25,ra_169,t1_141,t1_163,t2_142,t2_164,t_1,t_103,t_107,t_111,t_115,t_119,t_123,t_127,t_131,t_3,t_35,t_39,t_43,t_47,t_5,t_51,t_55,t_59,t_63,t_67,t_7,t_71,t_75,t_79,t_83,t_87,t_91,t_95,t_99;

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
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R11: bv64;
var R13: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R10: bv64;
var R12: bv64;
var R14: bv64;
var R15: bv64;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RBP: bv64;
var RBX: bv64;
var RCX: bv64;
var RDI: bv64;
var RDX: bv64;
var RSI: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_12: bv64;
var origCOUNT_136: bv64;
var origCOUNT_148: bv64;
var origCOUNT_156: bv8;
var origCOUNT_18: bv64;
var origCOUNT_26: bv64;
var origDEST_11: bv64;
var origDEST_135: bv64;
var origDEST_147: bv64;
var origDEST_155: bv8;
var origDEST_17: bv64;
var origDEST_25: bv64;
var ra_169: bv64;
var t1_141: bv64;
var t1_163: bv64;
var t2_142: bv64;
var t2_164: bv64;
var t_1: bv64;
var t_103: bv32;
var t_107: bv64;
var t_111: bv8;
var t_115: bv64;
var t_119: bv64;
var t_123: bv64;
var t_127: bv8;
var t_131: bv8;
var t_3: bv64;
var t_35: bv64;
var t_39: bv8;
var t_43: bv64;
var t_47: bv8;
var t_5: bv64;
var t_51: bv64;
var t_55: bv8;
var t_59: bv64;
var t_63: bv32;
var t_67: bv8;
var t_7: bv64;
var t_71: bv64;
var t_75: bv32;
var t_79: bv64;
var t_83: bv8;
var t_87: bv64;
var t_91: bv32;
var t_95: bv32;
var t_99: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4240bv64);
axiom policy(4416bv64);
axiom policy(4544bv64);
axiom policy(4736bv64);
axiom policy(4784bv64);
axiom policy(4880bv64);
axiom policy(4976bv64);
axiom policy(5072bv64);
axiom policy(5168bv64);
axiom policy(5216bv64);
axiom policy(5296bv64);
axiom policy(5712bv64);
axiom policy(5856bv64);
axiom policy(5872bv64);
axiom policy(6016bv64);
axiom policy(6048bv64);
axiom policy(6640bv64);
axiom policy(6800bv64);
axiom policy(6848bv64);
axiom policy(6960bv64);
axiom policy(7424bv64);
axiom policy(7664bv64);
axiom policy(7824bv64);
axiom policy(8080bv64);
axiom policy(8832bv64);
axiom policy(5840bv64);
axiom policy(8592bv64);
axiom policy(8608bv64);
axiom policy(8720bv64);
axiom policy(10176bv64);
axiom policy(8848bv64);
axiom policy(9184bv64);
axiom policy(9232bv64);
axiom policy(9248bv64);
axiom policy(9264bv64);
axiom policy(9280bv64);
axiom policy(9296bv64);
axiom policy(9312bv64);
axiom policy(9408bv64);
axiom policy(9808bv64);
axiom policy(10080bv64);
axiom policy(10192bv64);
axiom policy(10288bv64);
axiom policy(10864bv64);
axiom policy(11360bv64);
axiom policy(11520bv64);
axiom policy(11536bv64);
axiom policy(12256bv64);
axiom policy(13216bv64);
axiom policy(15776bv64);
axiom policy(16160bv64);
axiom policy(16528bv64);
axiom policy(17408bv64);
axiom policy(17488bv64);
axiom policy(17696bv64);
axiom policy(17776bv64);
axiom policy(17792bv64);
axiom policy(17808bv64);
axiom policy(18016bv64);
axiom policy(18032bv64);
axiom policy(18048bv64);
axiom policy(18208bv64);
