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
axiom _guard_writeTable_ptr == 12352bv64;
axiom _guard_callTable_ptr == 12336bv64;
axiom _function_addr_low == 5312bv64;
axiom _function_addr_high == 5622bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x14c0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x14c5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x14ca:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x14ce:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x14d4:
if (bv2bool(ZF)) {
  goto label_0x14de;
}

label_0x14d6:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 96bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x14dc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x14e3;
}

label_0x14de:
goto label_0x15f1;

label_0x14e3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x14e8:
origDEST_13 := RAX;
origCOUNT_14 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), CF, LSHIFT_64(origDEST_13, (MINUS_64(64bv64, origCOUNT_14)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_14 == 1bv64)), origDEST_13[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_14 == 0bv64)), AF, unconstrained_2);

label_0x14ec:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x14f1:
t_19 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), t_19)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_19, (LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)), 2bv64)), (XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)), 2bv64)), (XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)))))[1:0]));
SF := t_19[64:63];
ZF := bool2bv(0bv64 == t_19);

label_0x14f7:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x1517;
}

label_0x14f9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x14fe:
t_23 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_23, 1bv64)), (XOR_64(t_23, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_23)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1501:
RCX := RAX;

label_0x1504:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5385bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1fd0"} true;
call arbitrary_func();

label_0x1509:
t_27 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)), 2bv32)), (XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)), 2bv32)), (XOR_32((RSHIFT_32(t_27, 4bv32)), t_27)))))[1:0]));
SF := t_27[32:31];
ZF := bool2bv(0bv32 == t_27);

label_0x150b:
if (bv2bool(ZF)) {
  goto label_0x1517;
}

label_0x150d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 1bv32);

label_0x1515:
goto label_0x151f;

label_0x1517:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x151f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1523:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x1527:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x152c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1531:
RAX := PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[64:0];

label_0x1536:
origDEST_31 := RAX;
origCOUNT_32 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), CF, LSHIFT_64(origDEST_31, (MINUS_64(64bv64, origCOUNT_32)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_32 == 1bv64)), origDEST_31[64:63], unconstrained_4));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), AF, unconstrained_5);

label_0x153a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x153f:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(6898bv64, 5446bv64)), 0bv64));

label_0x1546:
t_37 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_37, 1bv64)), (XOR_64(t_37, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_37)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1549:
t_41 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 64bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 64bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 64bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 64bv64))), t_41)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_41, (LOAD_LE_64(mem, PLUS_64(RSP, 64bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x154e:
if (bv2bool(NOT_1(CF))) {
  goto label_0x156e;
}

label_0x1550:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1555:
t_45 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_45[64:63]) == (1bv64[64:63]))), (XOR_1((t_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_45)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1558:
RCX := RAX;

label_0x155b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5472bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1fd0"} true;
call arbitrary_func();

label_0x1560:
t_49 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_6;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)), 2bv32)), (XOR_32((RSHIFT_32(t_49, 4bv32)), t_49)))))[1:0]));
SF := t_49[32:31];
ZF := bool2bv(0bv32 == t_49);

label_0x1562:
if (bv2bool(ZF)) {
  goto label_0x156e;
}

label_0x1564:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0x156c:
goto label_0x1576;

label_0x156e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x1576:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x157a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x157e:
t_53 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_53)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_53, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))))[1:0]));
SF := t_53[32:31];
ZF := bool2bv(0bv32 == t_53);

label_0x1583:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x159d;
}

label_0x1585:
t_57 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_57)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_57, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))))[1:0]));
SF := t_57[32:31];
ZF := bool2bv(0bv32 == t_57);

label_0x158a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x159d;
}

label_0x158c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1591:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1596:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5531bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1400"} true;
call arbitrary_func();

label_0x159b:
goto label_0x15f1;

label_0x159d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x15a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x15a7:
goto label_0x15b6;

label_0x15a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15ae:
t_61 := RAX;
RAX := PLUS_64(RAX, 1bv64);
OF := AND_1((bool2bv((t_61[64:63]) == (1bv64[64:63]))), (XOR_1((t_61[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_61)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x15b1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x15b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x15bb:
t_65 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_65)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_65, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)), 2bv64)), (XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)), 2bv64)), (XOR_64((RSHIFT_64(t_65, 4bv64)), t_65)))))[1:0]));
SF := t_65[64:63];
ZF := bool2bv(0bv64 == t_65);

label_0x15c0:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x15f1;
}

label_0x15c2:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(6767bv64, 5577bv64)), 0bv64));

label_0x15c9:
t_69 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_69)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_69, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)), 2bv64)), (XOR_64((RSHIFT_64(t_69, 4bv64)), t_69)))))[1:0]));
SF := t_69[64:63];
ZF := bool2bv(0bv64 == t_69);

label_0x15ce:
if (bv2bool(NOT_1(CF))) {
  goto label_0x15f1;
}

label_0x15d0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15d5:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5594bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1fd0"} true;
call arbitrary_func();

label_0x15da:
t_73 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x15dc:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15ef;
}

label_0x15de:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x15e3:
if (bv2bool(ZF)) {
  goto label_0x15e6;
}

label_0x15e5:
assume false;

label_0x15e6:
t_81 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_81)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_81, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)), 2bv32)), (XOR_32((RSHIFT_32(t_81, 4bv32)), t_81)))))[1:0]));
SF := t_81[32:31];
ZF := bool2bv(0bv32 == t_81);

label_0x15eb:
if (bv2bool(ZF)) {
  goto label_0x15ee;
}

label_0x15ed:
assume false;

label_0x15ee:
assume false;

label_0x15ef:
goto label_0x15a9;

label_0x15f1:
t1_85 := RSP;
t2_86 := 88bv64;
RSP := PLUS_64(RSP, t2_86);
CF := bool2bv(LT_64(RSP, t1_85));
OF := AND_1((bool2bv((t1_85[64:63]) == (t2_86[64:63]))), (XOR_1((t1_85[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_85)), t2_86)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x15f5:

ra_91 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_14,origCOUNT_32,origDEST_13,origDEST_31,ra_91,t1_85,t2_86,t_1,t_19,t_23,t_27,t_37,t_41,t_45,t_49,t_5,t_53,t_57,t_61,t_65,t_69,t_73,t_77,t_81,t_9;

const unconstrained_1: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_14: bv64;
var origCOUNT_32: bv64;
var origDEST_13: bv64;
var origDEST_31: bv64;
var ra_91: bv64;
var t1_85: bv64;
var t2_86: bv64;
var t_1: bv64;
var t_19: bv64;
var t_23: bv64;
var t_27: bv32;
var t_37: bv64;
var t_41: bv64;
var t_45: bv64;
var t_49: bv32;
var t_5: bv64;
var t_53: bv32;
var t_57: bv32;
var t_61: bv64;
var t_65: bv64;
var t_69: bv64;
var t_73: bv32;
var t_77: bv32;
var t_81: bv32;
var t_9: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4160bv64);
axiom policy(4224bv64);
axiom policy(4256bv64);
axiom policy(4416bv64);
axiom policy(4480bv64);
axiom policy(4528bv64);
axiom policy(4544bv64);
axiom policy(5008bv64);
axiom policy(5072bv64);
axiom policy(5120bv64);
axiom policy(5184bv64);
axiom policy(5248bv64);
axiom policy(5312bv64);
axiom policy(5632bv64);
axiom policy(6336bv64);
axiom policy(6432bv64);
axiom policy(6512bv64);
axiom policy(6656bv64);
axiom policy(6864bv64);
axiom policy(7008bv64);
axiom policy(7168bv64);
axiom policy(7184bv64);
axiom policy(7296bv64);
axiom policy(7440bv64);
axiom policy(7584bv64);
axiom policy(8144bv64);
axiom policy(8224bv64);
axiom policy(8384bv64);
axiom policy(8432bv64);
axiom policy(8480bv64);
axiom policy(8560bv64);
axiom policy(8608bv64);
axiom policy(8656bv64);
axiom policy(8704bv64);
axiom policy(8736bv64);
axiom policy(8768bv64);
axiom policy(8816bv64);
axiom policy(8864bv64);
axiom policy(8912bv64);
axiom policy(8944bv64);
axiom policy(8960bv64);
axiom policy(8976bv64);
axiom policy(8992bv64);
axiom policy(9008bv64);
axiom policy(9024bv64);
axiom policy(9040bv64);
axiom policy(9440bv64);
axiom policy(9472bv64);
axiom policy(9536bv64);
axiom policy(9936bv64);
axiom policy(10224bv64);
axiom policy(10480bv64);
axiom policy(10768bv64);
axiom policy(10912bv64);
axiom policy(11040bv64);
axiom policy(11184bv64);
