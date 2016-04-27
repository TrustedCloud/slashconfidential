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
axiom _function_addr_low == 4800bv64;
axiom _function_addr_high == 5198bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x12c0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x12c5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x12ca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x12cf:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x12d4:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x12d8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x12e0:
RAX := PLUS_64((PLUS_64(7489bv64, 4839bv64)), 0bv64)[64:0];

label_0x12e7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x12ec:
RAX := PLUS_64((PLUS_64(7477bv64, 4851bv64)), 0bv64)[64:0];

label_0x12f3:
t1_5 := RAX;
t2_6 := 8bv64;
RAX := PLUS_64(RAX, t2_6);
CF := bool2bv(LT_64(RAX, t1_5));
OF := AND_1((bool2bv((t1_5[64:63]) == (t2_6[64:63]))), (XOR_1((t1_5[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_5)), t2_6)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x12f7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x12fc:
RAX := PLUS_64((PLUS_64(7469bv64, 4867bv64)), 0bv64)[64:0];

label_0x1303:
t_11 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), t_11)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_11, (LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x1308:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x1316;
}

label_0x130a:
RAX := PLUS_64((PLUS_64(7455bv64, 4881bv64)), 0bv64)[64:0];

label_0x1311:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1316:
RAX := PLUS_64((PLUS_64(7443bv64, 4893bv64)), 0bv64)[64:0];

label_0x131d:
t1_15 := RAX;
t2_16 := 8bv64;
RAX := PLUS_64(RAX, t2_16);
CF := bool2bv(LT_64(RAX, t1_15));
OF := AND_1((bool2bv((t1_15[64:63]) == (t2_16[64:63]))), (XOR_1((t1_15[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_15)), t2_16)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1321:
t_21 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_21)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_21, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)), 2bv64)), (XOR_64((RSHIFT_64(t_21, 4bv64)), t_21)))))[1:0]));
SF := t_21[64:63];
ZF := bool2bv(0bv64 == t_21);

label_0x1326:
if (bv2bool(NOT_1(CF))) {
  goto label_0x1338;
}

label_0x1328:
RAX := PLUS_64((PLUS_64(7425bv64, 4911bv64)), 0bv64)[64:0];

label_0x132f:
t1_25 := RAX;
t2_26 := 8bv64;
RAX := PLUS_64(RAX, t2_26);
CF := bool2bv(LT_64(RAX, t1_25));
OF := AND_1((bool2bv((t1_25[64:63]) == (t2_26[64:63]))), (XOR_1((t1_25[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_25)), t2_26)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1333:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1338:
RAX := PLUS_64((PLUS_64(7425bv64, 4927bv64)), 0bv64)[64:0];

label_0x133f:
t_31 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), t_31)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_31, (LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)), 2bv64)), (XOR_64((RSHIFT_64(t_31, 4bv64)), t_31)))))[1:0]));
SF := t_31[64:63];
ZF := bool2bv(0bv64 == t_31);

label_0x1344:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x1352;
}

label_0x1346:
RAX := PLUS_64((PLUS_64(7411bv64, 4941bv64)), 0bv64)[64:0];

label_0x134d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1352:
RAX := PLUS_64((PLUS_64(7399bv64, 4953bv64)), 0bv64)[64:0];

label_0x1359:
t1_35 := RAX;
t2_36 := 8bv64;
RAX := PLUS_64(RAX, t2_36);
CF := bool2bv(LT_64(RAX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x135d:
t_41 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_41)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_41, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)), 2bv64)), (XOR_64((RSHIFT_64(t_41, 4bv64)), t_41)))))[1:0]));
SF := t_41[64:63];
ZF := bool2bv(0bv64 == t_41);

label_0x1362:
if (bv2bool(NOT_1(CF))) {
  goto label_0x1374;
}

label_0x1364:
RAX := PLUS_64((PLUS_64(7381bv64, 4971bv64)), 0bv64)[64:0];

label_0x136b:
t1_45 := RAX;
t2_46 := 8bv64;
RAX := PLUS_64(RAX, t2_46);
CF := bool2bv(LT_64(RAX, t1_45));
OF := AND_1((bool2bv((t1_45[64:63]) == (t2_46[64:63]))), (XOR_1((t1_45[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_45)), t2_46)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x136f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1374:
RAX := PLUS_64((PLUS_64(7357bv64, 4987bv64)), 0bv64)[64:0];

label_0x137b:
t_51 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))), t_51)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_51, (LOAD_LE_64(mem, PLUS_64(RSP, 40bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x1380:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x138e;
}

label_0x1382:
RAX := PLUS_64((PLUS_64(7343bv64, 5001bv64)), 0bv64)[64:0];

label_0x1389:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x138e:
RAX := PLUS_64((PLUS_64(7331bv64, 5013bv64)), 0bv64)[64:0];

label_0x1395:
t1_55 := RAX;
t2_56 := 8bv64;
RAX := PLUS_64(RAX, t2_56);
CF := bool2bv(LT_64(RAX, t1_55));
OF := AND_1((bool2bv((t1_55[64:63]) == (t2_56[64:63]))), (XOR_1((t1_55[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_55)), t2_56)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1399:
t_61 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_61)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_61, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))))[1:0]));
SF := t_61[64:63];
ZF := bool2bv(0bv64 == t_61);

label_0x139e:
if (bv2bool(NOT_1(CF))) {
  goto label_0x13b0;
}

label_0x13a0:
RAX := PLUS_64((PLUS_64(7313bv64, 5031bv64)), 0bv64)[64:0];

label_0x13a7:
t1_65 := RAX;
t2_66 := 8bv64;
RAX := PLUS_64(RAX, t2_66);
CF := bool2bv(LT_64(RAX, t1_65));
OF := AND_1((bool2bv((t1_65[64:63]) == (t2_66[64:63]))), (XOR_1((t1_65[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_65)), t2_66)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13ab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x13b0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x13b5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x13ba:
t_71 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_71, RAX));
OF := AND_64((XOR_64(t_71, RAX)), (XOR_64(t_71, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_71)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x13bd:
RAX := RCX;

label_0x13c0:
R9 := PLUS_64(RSP, 32bv64)[64:0];

label_0x13c5:
R8 := (0bv32 ++ 4bv32);

label_0x13cb:
RDX := RAX;

label_0x13ce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x13d3:

target_75 := LOAD_LE_64(mem, PLUS_64((PLUS_64(7231bv64, 5081bv64)), 0bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5081bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_75"} true;
call arbitrary_func();

label_0x13d9:
t_77 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0x13db:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x13e4;
}

label_0x13dd:
RAX := (0bv32 ++ 1bv32);

label_0x13e2:
goto label_0x1449;

label_0x13e4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x13e9:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(7224bv64, 5104bv64)), 0bv64), RAX);

label_0x13f0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x13f5:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(7220bv64, 5116bv64)), 0bv64), RAX);

label_0x13fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1401:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(7216bv64, 5128bv64)), 0bv64), RAX);

label_0x1408:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x140d:
mem := STORE_LE_64(mem, PLUS_64((PLUS_64(7212bv64, 5140bv64)), 0bv64), RAX);

label_0x1414:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1419:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x141e:
t_81 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_81, RAX));
OF := AND_64((XOR_64(t_81, RAX)), (XOR_64(t_81, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_81)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1421:
RAX := RCX;

label_0x1424:
R9 := PLUS_64(RSP, 36bv64)[64:0];

label_0x1429:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x142e:
RDX := RAX;

label_0x1431:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1436:

target_85 := LOAD_LE_64(mem, PLUS_64((PLUS_64(7132bv64, 5180bv64)), 0bv64));
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5180bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_85"} true;
call arbitrary_func();

label_0x143c:
t_87 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)), 2bv32)), (XOR_32((RSHIFT_32(t_87, 4bv32)), t_87)))))[1:0]));
SF := t_87[32:31];
ZF := bool2bv(0bv32 == t_87);

label_0x143e:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1447;
}

label_0x1440:
RAX := (0bv32 ++ 1bv32);

label_0x1445:
goto label_0x1449;

label_0x1447:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_3;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1449:
t1_91 := RSP;
t2_92 := 72bv64;
RSP := PLUS_64(RSP, t2_92);
CF := bool2bv(LT_64(RSP, t1_91));
OF := AND_1((bool2bv((t1_91[64:63]) == (t2_92[64:63]))), (XOR_1((t1_91[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_91)), t2_92)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x144d:

ra_97 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,ra_97,t1_15,t1_25,t1_35,t1_45,t1_5,t1_55,t1_65,t1_91,t2_16,t2_26,t2_36,t2_46,t2_56,t2_6,t2_66,t2_92,t_1,t_11,t_21,t_31,t_41,t_51,t_61,t_71,t_77,t_81,t_87,target_75,target_85;

const unconstrained_1: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
var RDI: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R8: bv64;
var R9: bv64;
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var ra_97: bv64;
var t1_15: bv64;
var t1_25: bv64;
var t1_35: bv64;
var t1_45: bv64;
var t1_5: bv64;
var t1_55: bv64;
var t1_65: bv64;
var t1_91: bv64;
var t2_16: bv64;
var t2_26: bv64;
var t2_36: bv64;
var t2_46: bv64;
var t2_56: bv64;
var t2_6: bv64;
var t2_66: bv64;
var t2_92: bv64;
var t_1: bv64;
var t_11: bv64;
var t_21: bv64;
var t_31: bv64;
var t_41: bv64;
var t_51: bv64;
var t_61: bv64;
var t_71: bv64;
var t_77: bv32;
var t_81: bv64;
var t_87: bv32;
var target_75: bv64;
var target_85: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4160bv64);
axiom policy(4240bv64);
axiom policy(4288bv64);
axiom policy(4304bv64);
axiom policy(4704bv64);
axiom policy(4736bv64);
axiom policy(4800bv64);
axiom policy(5200bv64);
axiom policy(5664bv64);
axiom policy(5728bv64);
axiom policy(5776bv64);
axiom policy(5840bv64);
axiom policy(5904bv64);
axiom policy(5968bv64);
axiom policy(6288bv64);
axiom policy(6992bv64);
axiom policy(7088bv64);
axiom policy(7168bv64);
axiom policy(7312bv64);
axiom policy(7520bv64);
axiom policy(7664bv64);
axiom policy(7824bv64);
axiom policy(7840bv64);
axiom policy(7952bv64);
axiom policy(8096bv64);
axiom policy(8240bv64);
axiom policy(8800bv64);
axiom policy(8880bv64);
axiom policy(9040bv64);
axiom policy(9088bv64);
axiom policy(9136bv64);
axiom policy(9216bv64);
axiom policy(9264bv64);
axiom policy(9312bv64);
axiom policy(9360bv64);
axiom policy(9392bv64);
axiom policy(9424bv64);
axiom policy(9472bv64);
axiom policy(9520bv64);
axiom policy(9568bv64);
axiom policy(9600bv64);
axiom policy(9616bv64);
axiom policy(9632bv64);
axiom policy(9648bv64);
axiom policy(9664bv64);
axiom policy(9680bv64);
axiom policy(9696bv64);
axiom policy(9984bv64);
axiom policy(10240bv64);
axiom policy(10528bv64);
axiom policy(10672bv64);
axiom policy(10800bv64);
axiom policy(10944bv64);
