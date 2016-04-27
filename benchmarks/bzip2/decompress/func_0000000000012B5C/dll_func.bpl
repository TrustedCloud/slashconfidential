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
axiom _function_addr_low == 76636bv64;
axiom _function_addr_high == 76816bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x12b5c:
t1_1 := LOAD_LE_8(mem, RAX);
t2_2 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_2));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_1));
OF := AND_1((bool2bv((t1_1[8:7]) == (t2_2[8:7]))), (XOR_1((t1_1[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_1)), t2_2)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b5e:
t1_7 := LOAD_LE_8(mem, RAX);
t2_8 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_8));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_7));
OF := AND_1((bool2bv((t1_7[8:7]) == (t2_8[8:7]))), (XOR_1((t1_7[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_7)), t2_8)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b60:
t1_13 := LOAD_LE_8(mem, RAX);
t2_14 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_14));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_13));
OF := AND_1((bool2bv((t1_13[8:7]) == (t2_14[8:7]))), (XOR_1((t1_13[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_13)), t2_14)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b62:
t1_19 := LOAD_LE_8(mem, RAX);
t2_20 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_20));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_19));
OF := AND_1((bool2bv((t1_19[8:7]) == (t2_20[8:7]))), (XOR_1((t1_19[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_19)), t2_20)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b64:
t1_25 := LOAD_LE_8(mem, RAX);
t2_26 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_26));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_25));
OF := AND_1((bool2bv((t1_25[8:7]) == (t2_26[8:7]))), (XOR_1((t1_25[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_25)), t2_26)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b66:
t1_31 := LOAD_LE_8(mem, RAX);
t2_32 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_32));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_31));
OF := AND_1((bool2bv((t1_31[8:7]) == (t2_32[8:7]))), (XOR_1((t1_31[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_31)), t2_32)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b68:
t1_37 := LOAD_LE_8(mem, RAX);
t2_38 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_38));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_37));
OF := AND_1((bool2bv((t1_37[8:7]) == (t2_38[8:7]))), (XOR_1((t1_37[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_37)), t2_38)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b6a:
t1_43 := LOAD_LE_8(mem, RAX);
t2_44 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_44));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_43));
OF := AND_1((bool2bv((t1_43[8:7]) == (t2_44[8:7]))), (XOR_1((t1_43[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_43)), t2_44)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b6c:
t1_49 := LOAD_LE_8(mem, RAX);
t2_50 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_50));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_49));
OF := AND_1((bool2bv((t1_49[8:7]) == (t2_50[8:7]))), (XOR_1((t1_49[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_49)), t2_50)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b6e:
t1_55 := LOAD_LE_8(mem, RAX);
t2_56 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_56));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_55));
OF := AND_1((bool2bv((t1_55[8:7]) == (t2_56[8:7]))), (XOR_1((t1_55[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_55)), t2_56)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b70:
t1_61 := LOAD_LE_8(mem, RAX);
t2_62 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_62));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_61));
OF := AND_1((bool2bv((t1_61[8:7]) == (t2_62[8:7]))), (XOR_1((t1_61[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_61)), t2_62)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b72:
t1_67 := LOAD_LE_8(mem, RAX);
t2_68 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_68));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_67));
OF := AND_1((bool2bv((t1_67[8:7]) == (t2_68[8:7]))), (XOR_1((t1_67[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_67)), t2_68)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b74:
t1_73 := LOAD_LE_8(mem, RAX);
t2_74 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_74));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_73));
OF := AND_1((bool2bv((t1_73[8:7]) == (t2_74[8:7]))), (XOR_1((t1_73[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_73)), t2_74)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b76:
t1_79 := LOAD_LE_8(mem, RAX);
t2_80 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_80));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_79));
OF := AND_1((bool2bv((t1_79[8:7]) == (t2_80[8:7]))), (XOR_1((t1_79[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_79)), t2_80)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b78:
t1_85 := LOAD_LE_8(mem, RAX);
t2_86 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_86));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_85));
OF := AND_1((bool2bv((t1_85[8:7]) == (t2_86[8:7]))), (XOR_1((t1_85[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_85)), t2_86)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b7a:
t1_91 := LOAD_LE_8(mem, RAX);
t2_92 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_92));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_91));
OF := AND_1((bool2bv((t1_91[8:7]) == (t2_92[8:7]))), (XOR_1((t1_91[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_91)), t2_92)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b7c:
t1_97 := LOAD_LE_8(mem, RAX);
t2_98 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_98));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_97));
OF := AND_1((bool2bv((t1_97[8:7]) == (t2_98[8:7]))), (XOR_1((t1_97[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_97)), t2_98)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b7e:
t1_103 := LOAD_LE_8(mem, RAX);
t2_104 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_104));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_103));
OF := AND_1((bool2bv((t1_103[8:7]) == (t2_104[8:7]))), (XOR_1((t1_103[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_103)), t2_104)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b80:
t1_109 := LOAD_LE_8(mem, RAX);
t2_110 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_110));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_109));
OF := AND_1((bool2bv((t1_109[8:7]) == (t2_110[8:7]))), (XOR_1((t1_109[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_109)), t2_110)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b82:
t1_115 := LOAD_LE_8(mem, RAX);
t2_116 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_116));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_115));
OF := AND_1((bool2bv((t1_115[8:7]) == (t2_116[8:7]))), (XOR_1((t1_115[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_115)), t2_116)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b84:
t1_121 := LOAD_LE_8(mem, RAX);
t2_122 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_122));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_121));
OF := AND_1((bool2bv((t1_121[8:7]) == (t2_122[8:7]))), (XOR_1((t1_121[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_121)), t2_122)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b86:
t1_127 := LOAD_LE_8(mem, RAX);
t2_128 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_128));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_127));
OF := AND_1((bool2bv((t1_127[8:7]) == (t2_128[8:7]))), (XOR_1((t1_127[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_127)), t2_128)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b88:
t1_133 := LOAD_LE_8(mem, RAX);
t2_134 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_134));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_133));
OF := AND_1((bool2bv((t1_133[8:7]) == (t2_134[8:7]))), (XOR_1((t1_133[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_133)), t2_134)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b8a:
t1_139 := LOAD_LE_8(mem, RAX);
t2_140 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_140));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_139));
OF := AND_1((bool2bv((t1_139[8:7]) == (t2_140[8:7]))), (XOR_1((t1_139[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_139)), t2_140)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b8c:
t1_145 := LOAD_LE_8(mem, RAX);
t2_146 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_146));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_145));
OF := AND_1((bool2bv((t1_145[8:7]) == (t2_146[8:7]))), (XOR_1((t1_145[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_145)), t2_146)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b8e:
t1_151 := LOAD_LE_8(mem, RAX);
t2_152 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_152));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_151));
OF := AND_1((bool2bv((t1_151[8:7]) == (t2_152[8:7]))), (XOR_1((t1_151[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_151)), t2_152)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b90:
t1_157 := LOAD_LE_8(mem, RAX);
t2_158 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_158));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_157));
OF := AND_1((bool2bv((t1_157[8:7]) == (t2_158[8:7]))), (XOR_1((t1_157[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_157)), t2_158)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b92:
t1_163 := LOAD_LE_8(mem, RAX);
t2_164 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_164));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_163));
OF := AND_1((bool2bv((t1_163[8:7]) == (t2_164[8:7]))), (XOR_1((t1_163[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_163)), t2_164)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b94:
t1_169 := LOAD_LE_8(mem, RAX);
t2_170 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_170));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_169));
OF := AND_1((bool2bv((t1_169[8:7]) == (t2_170[8:7]))), (XOR_1((t1_169[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_169)), t2_170)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b96:
t1_175 := LOAD_LE_8(mem, RAX);
t2_176 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_176));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_175));
OF := AND_1((bool2bv((t1_175[8:7]) == (t2_176[8:7]))), (XOR_1((t1_175[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_175)), t2_176)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b98:
t1_181 := LOAD_LE_8(mem, RAX);
t2_182 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_182));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_181));
OF := AND_1((bool2bv((t1_181[8:7]) == (t2_182[8:7]))), (XOR_1((t1_181[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_181)), t2_182)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b9a:
t1_187 := LOAD_LE_8(mem, RAX);
t2_188 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_188));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_187));
OF := AND_1((bool2bv((t1_187[8:7]) == (t2_188[8:7]))), (XOR_1((t1_187[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_187)), t2_188)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b9c:
t1_193 := LOAD_LE_8(mem, RAX);
t2_194 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_194));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_193));
OF := AND_1((bool2bv((t1_193[8:7]) == (t2_194[8:7]))), (XOR_1((t1_193[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_193)), t2_194)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12b9e:
t1_199 := LOAD_LE_8(mem, RAX);
t2_200 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_200));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_199));
OF := AND_1((bool2bv((t1_199[8:7]) == (t2_200[8:7]))), (XOR_1((t1_199[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_199)), t2_200)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12ba0:
t1_205 := LOAD_LE_8(mem, RAX);
t2_206 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_206));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_205));
OF := AND_1((bool2bv((t1_205[8:7]) == (t2_206[8:7]))), (XOR_1((t1_205[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_205)), t2_206)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12ba2:
t1_211 := LOAD_LE_8(mem, RAX);
t2_212 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_212));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_211));
OF := AND_1((bool2bv((t1_211[8:7]) == (t2_212[8:7]))), (XOR_1((t1_211[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_211)), t2_212)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12ba4:
t1_217 := LOAD_LE_8(mem, RAX);
t2_218 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_218));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_217));
OF := AND_1((bool2bv((t1_217[8:7]) == (t2_218[8:7]))), (XOR_1((t1_217[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_217)), t2_218)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12ba6:
t1_223 := LOAD_LE_8(mem, RAX);
t2_224 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_224));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_223));
OF := AND_1((bool2bv((t1_223[8:7]) == (t2_224[8:7]))), (XOR_1((t1_223[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_223)), t2_224)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12ba8:
t1_229 := LOAD_LE_8(mem, RAX);
t2_230 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_230));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_229));
OF := AND_1((bool2bv((t1_229[8:7]) == (t2_230[8:7]))), (XOR_1((t1_229[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_229)), t2_230)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12baa:
t1_235 := LOAD_LE_8(mem, RAX);
t2_236 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_236));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_235));
OF := AND_1((bool2bv((t1_235[8:7]) == (t2_236[8:7]))), (XOR_1((t1_235[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_235)), t2_236)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bac:
t1_241 := LOAD_LE_8(mem, RAX);
t2_242 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_242));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_241));
OF := AND_1((bool2bv((t1_241[8:7]) == (t2_242[8:7]))), (XOR_1((t1_241[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_241)), t2_242)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bae:
t1_247 := LOAD_LE_8(mem, RAX);
t2_248 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_248));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_247));
OF := AND_1((bool2bv((t1_247[8:7]) == (t2_248[8:7]))), (XOR_1((t1_247[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_247)), t2_248)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bb0:
t1_253 := LOAD_LE_8(mem, RAX);
t2_254 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_254));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_253));
OF := AND_1((bool2bv((t1_253[8:7]) == (t2_254[8:7]))), (XOR_1((t1_253[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_253)), t2_254)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bb2:
t1_259 := LOAD_LE_8(mem, RAX);
t2_260 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_260));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_259));
OF := AND_1((bool2bv((t1_259[8:7]) == (t2_260[8:7]))), (XOR_1((t1_259[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_259)), t2_260)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bb4:
t1_265 := LOAD_LE_8(mem, RAX);
t2_266 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_266));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_265));
OF := AND_1((bool2bv((t1_265[8:7]) == (t2_266[8:7]))), (XOR_1((t1_265[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_265)), t2_266)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bb6:
t1_271 := LOAD_LE_8(mem, RAX);
t2_272 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_272));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_271));
OF := AND_1((bool2bv((t1_271[8:7]) == (t2_272[8:7]))), (XOR_1((t1_271[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_271)), t2_272)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bb8:
t1_277 := LOAD_LE_8(mem, RAX);
t2_278 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_278));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_277));
OF := AND_1((bool2bv((t1_277[8:7]) == (t2_278[8:7]))), (XOR_1((t1_277[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_277)), t2_278)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bba:
t1_283 := LOAD_LE_8(mem, RAX);
t2_284 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_284));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_283));
OF := AND_1((bool2bv((t1_283[8:7]) == (t2_284[8:7]))), (XOR_1((t1_283[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_283)), t2_284)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bbc:
t1_289 := LOAD_LE_8(mem, RAX);
t2_290 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_290));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_289));
OF := AND_1((bool2bv((t1_289[8:7]) == (t2_290[8:7]))), (XOR_1((t1_289[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_289)), t2_290)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bbe:
t1_295 := LOAD_LE_8(mem, RAX);
t2_296 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_296));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_295));
OF := AND_1((bool2bv((t1_295[8:7]) == (t2_296[8:7]))), (XOR_1((t1_295[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_295)), t2_296)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bc0:
t1_301 := LOAD_LE_8(mem, RAX);
t2_302 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_302));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_301));
OF := AND_1((bool2bv((t1_301[8:7]) == (t2_302[8:7]))), (XOR_1((t1_301[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_301)), t2_302)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bc2:
t1_307 := LOAD_LE_8(mem, RAX);
t2_308 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_308));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_307));
OF := AND_1((bool2bv((t1_307[8:7]) == (t2_308[8:7]))), (XOR_1((t1_307[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_307)), t2_308)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bc4:
t1_313 := LOAD_LE_8(mem, RAX);
t2_314 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_314));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_313));
OF := AND_1((bool2bv((t1_313[8:7]) == (t2_314[8:7]))), (XOR_1((t1_313[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_313)), t2_314)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bc6:
t1_319 := LOAD_LE_8(mem, RAX);
t2_320 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_320));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_319));
OF := AND_1((bool2bv((t1_319[8:7]) == (t2_320[8:7]))), (XOR_1((t1_319[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_319)), t2_320)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bc8:
t1_325 := LOAD_LE_8(mem, RAX);
t2_326 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_326));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_325));
OF := AND_1((bool2bv((t1_325[8:7]) == (t2_326[8:7]))), (XOR_1((t1_325[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_325)), t2_326)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bca:
t1_331 := LOAD_LE_8(mem, RAX);
t2_332 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_332));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_331));
OF := AND_1((bool2bv((t1_331[8:7]) == (t2_332[8:7]))), (XOR_1((t1_331[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_331)), t2_332)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bcc:
t1_337 := LOAD_LE_8(mem, RAX);
t2_338 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_338));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_337));
OF := AND_1((bool2bv((t1_337[8:7]) == (t2_338[8:7]))), (XOR_1((t1_337[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_337)), t2_338)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bce:
t1_343 := LOAD_LE_8(mem, RAX);
t2_344 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_344));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_343));
OF := AND_1((bool2bv((t1_343[8:7]) == (t2_344[8:7]))), (XOR_1((t1_343[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_343)), t2_344)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bd0:
t1_349 := LOAD_LE_8(mem, RAX);
t2_350 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_350));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_349));
OF := AND_1((bool2bv((t1_349[8:7]) == (t2_350[8:7]))), (XOR_1((t1_349[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_349)), t2_350)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bd2:
t1_355 := LOAD_LE_8(mem, RAX);
t2_356 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_356));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_355));
OF := AND_1((bool2bv((t1_355[8:7]) == (t2_356[8:7]))), (XOR_1((t1_355[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_355)), t2_356)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bd4:
t1_361 := LOAD_LE_8(mem, RAX);
t2_362 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_362));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_361));
OF := AND_1((bool2bv((t1_361[8:7]) == (t2_362[8:7]))), (XOR_1((t1_361[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_361)), t2_362)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bd6:
t1_367 := LOAD_LE_8(mem, RAX);
t2_368 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_368));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_367));
OF := AND_1((bool2bv((t1_367[8:7]) == (t2_368[8:7]))), (XOR_1((t1_367[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_367)), t2_368)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bd8:
t1_373 := LOAD_LE_8(mem, RAX);
t2_374 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_374));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_373));
OF := AND_1((bool2bv((t1_373[8:7]) == (t2_374[8:7]))), (XOR_1((t1_373[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_373)), t2_374)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bda:
t1_379 := LOAD_LE_8(mem, RAX);
t2_380 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_380));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_379));
OF := AND_1((bool2bv((t1_379[8:7]) == (t2_380[8:7]))), (XOR_1((t1_379[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_379)), t2_380)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bdc:
t1_385 := LOAD_LE_8(mem, RAX);
t2_386 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_386));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_385));
OF := AND_1((bool2bv((t1_385[8:7]) == (t2_386[8:7]))), (XOR_1((t1_385[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_385)), t2_386)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bde:
t1_391 := LOAD_LE_8(mem, RAX);
t2_392 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_392));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_391));
OF := AND_1((bool2bv((t1_391[8:7]) == (t2_392[8:7]))), (XOR_1((t1_391[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_391)), t2_392)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12be0:
t1_397 := LOAD_LE_8(mem, RAX);
t2_398 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_398));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_397));
OF := AND_1((bool2bv((t1_397[8:7]) == (t2_398[8:7]))), (XOR_1((t1_397[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_397)), t2_398)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12be2:
t1_403 := LOAD_LE_8(mem, RAX);
t2_404 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_404));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_403));
OF := AND_1((bool2bv((t1_403[8:7]) == (t2_404[8:7]))), (XOR_1((t1_403[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_403)), t2_404)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12be4:
t1_409 := LOAD_LE_8(mem, RAX);
t2_410 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_410));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_409));
OF := AND_1((bool2bv((t1_409[8:7]) == (t2_410[8:7]))), (XOR_1((t1_409[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_409)), t2_410)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12be6:
t1_415 := LOAD_LE_8(mem, RAX);
t2_416 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_416));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_415));
OF := AND_1((bool2bv((t1_415[8:7]) == (t2_416[8:7]))), (XOR_1((t1_415[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_415)), t2_416)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12be8:
t1_421 := LOAD_LE_8(mem, RAX);
t2_422 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_422));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_421));
OF := AND_1((bool2bv((t1_421[8:7]) == (t2_422[8:7]))), (XOR_1((t1_421[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_421)), t2_422)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bea:
t1_427 := LOAD_LE_8(mem, RAX);
t2_428 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_428));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_427));
OF := AND_1((bool2bv((t1_427[8:7]) == (t2_428[8:7]))), (XOR_1((t1_427[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_427)), t2_428)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bec:
t1_433 := LOAD_LE_8(mem, RAX);
t2_434 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_434));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_433));
OF := AND_1((bool2bv((t1_433[8:7]) == (t2_434[8:7]))), (XOR_1((t1_433[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_433)), t2_434)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bee:
t1_439 := LOAD_LE_8(mem, RAX);
t2_440 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_440));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_439));
OF := AND_1((bool2bv((t1_439[8:7]) == (t2_440[8:7]))), (XOR_1((t1_439[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_439)), t2_440)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bf0:
t1_445 := LOAD_LE_8(mem, RAX);
t2_446 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_446));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_445));
OF := AND_1((bool2bv((t1_445[8:7]) == (t2_446[8:7]))), (XOR_1((t1_445[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_445)), t2_446)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bf2:
t1_451 := LOAD_LE_8(mem, RAX);
t2_452 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_452));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_451));
OF := AND_1((bool2bv((t1_451[8:7]) == (t2_452[8:7]))), (XOR_1((t1_451[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_451)), t2_452)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bf4:
t1_457 := LOAD_LE_8(mem, RAX);
t2_458 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_458));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_457));
OF := AND_1((bool2bv((t1_457[8:7]) == (t2_458[8:7]))), (XOR_1((t1_457[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_457)), t2_458)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bf6:
t1_463 := LOAD_LE_8(mem, RAX);
t2_464 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_464));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_463));
OF := AND_1((bool2bv((t1_463[8:7]) == (t2_464[8:7]))), (XOR_1((t1_463[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_463)), t2_464)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bf8:
t1_469 := LOAD_LE_8(mem, RAX);
t2_470 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_470));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_469));
OF := AND_1((bool2bv((t1_469[8:7]) == (t2_470[8:7]))), (XOR_1((t1_469[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_469)), t2_470)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bfa:
t1_475 := LOAD_LE_8(mem, RAX);
t2_476 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_476));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_475));
OF := AND_1((bool2bv((t1_475[8:7]) == (t2_476[8:7]))), (XOR_1((t1_475[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_475)), t2_476)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bfc:
t1_481 := LOAD_LE_8(mem, RAX);
t2_482 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_482));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_481));
OF := AND_1((bool2bv((t1_481[8:7]) == (t2_482[8:7]))), (XOR_1((t1_481[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_481)), t2_482)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

label_0x12bfe:
t1_487 := LOAD_LE_8(mem, RAX);
t2_488 := RAX[32:0][8:0];
mem := STORE_LE_8(mem, RAX, PLUS_8((LOAD_LE_8(mem, RAX)), t2_488));
CF := bool2bv(LT_8((LOAD_LE_8(mem, RAX)), t1_487));
OF := AND_1((bool2bv((t1_487[8:7]) == (t2_488[8:7]))), (XOR_1((t1_487[8:7]), (LOAD_LE_8(mem, RAX)[8:7]))));
AF := bool2bv(16bv8 == (AND_8(16bv8, (XOR_8((XOR_8((LOAD_LE_8(mem, RAX)), t1_487)), t2_488)))));
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RAX)), 4bv8)), (LOAD_LE_8(mem, RAX)))))))[1:0]));
SF := LOAD_LE_8(mem, RAX)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RAX)));

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,SF,ZF,mem,t1_1,t1_103,t1_109,t1_115,t1_121,t1_127,t1_13,t1_133,t1_139,t1_145,t1_151,t1_157,t1_163,t1_169,t1_175,t1_181,t1_187,t1_19,t1_193,t1_199,t1_205,t1_211,t1_217,t1_223,t1_229,t1_235,t1_241,t1_247,t1_25,t1_253,t1_259,t1_265,t1_271,t1_277,t1_283,t1_289,t1_295,t1_301,t1_307,t1_31,t1_313,t1_319,t1_325,t1_331,t1_337,t1_343,t1_349,t1_355,t1_361,t1_367,t1_37,t1_373,t1_379,t1_385,t1_391,t1_397,t1_403,t1_409,t1_415,t1_421,t1_427,t1_43,t1_433,t1_439,t1_445,t1_451,t1_457,t1_463,t1_469,t1_475,t1_481,t1_487,t1_49,t1_55,t1_61,t1_67,t1_7,t1_73,t1_79,t1_85,t1_91,t1_97,t2_104,t2_110,t2_116,t2_122,t2_128,t2_134,t2_14,t2_140,t2_146,t2_152,t2_158,t2_164,t2_170,t2_176,t2_182,t2_188,t2_194,t2_2,t2_20,t2_200,t2_206,t2_212,t2_218,t2_224,t2_230,t2_236,t2_242,t2_248,t2_254,t2_26,t2_260,t2_266,t2_272,t2_278,t2_284,t2_290,t2_296,t2_302,t2_308,t2_314,t2_32,t2_320,t2_326,t2_332,t2_338,t2_344,t2_350,t2_356,t2_362,t2_368,t2_374,t2_38,t2_380,t2_386,t2_392,t2_398,t2_404,t2_410,t2_416,t2_422,t2_428,t2_434,t2_44,t2_440,t2_446,t2_452,t2_458,t2_464,t2_470,t2_476,t2_482,t2_488,t2_50,t2_56,t2_62,t2_68,t2_74,t2_8,t2_80,t2_86,t2_92,t2_98;

var RCX: bv64;
var RDI: bv64;
var RSP: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var RAX: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var t1_1: bv8;
var t1_103: bv8;
var t1_109: bv8;
var t1_115: bv8;
var t1_121: bv8;
var t1_127: bv8;
var t1_13: bv8;
var t1_133: bv8;
var t1_139: bv8;
var t1_145: bv8;
var t1_151: bv8;
var t1_157: bv8;
var t1_163: bv8;
var t1_169: bv8;
var t1_175: bv8;
var t1_181: bv8;
var t1_187: bv8;
var t1_19: bv8;
var t1_193: bv8;
var t1_199: bv8;
var t1_205: bv8;
var t1_211: bv8;
var t1_217: bv8;
var t1_223: bv8;
var t1_229: bv8;
var t1_235: bv8;
var t1_241: bv8;
var t1_247: bv8;
var t1_25: bv8;
var t1_253: bv8;
var t1_259: bv8;
var t1_265: bv8;
var t1_271: bv8;
var t1_277: bv8;
var t1_283: bv8;
var t1_289: bv8;
var t1_295: bv8;
var t1_301: bv8;
var t1_307: bv8;
var t1_31: bv8;
var t1_313: bv8;
var t1_319: bv8;
var t1_325: bv8;
var t1_331: bv8;
var t1_337: bv8;
var t1_343: bv8;
var t1_349: bv8;
var t1_355: bv8;
var t1_361: bv8;
var t1_367: bv8;
var t1_37: bv8;
var t1_373: bv8;
var t1_379: bv8;
var t1_385: bv8;
var t1_391: bv8;
var t1_397: bv8;
var t1_403: bv8;
var t1_409: bv8;
var t1_415: bv8;
var t1_421: bv8;
var t1_427: bv8;
var t1_43: bv8;
var t1_433: bv8;
var t1_439: bv8;
var t1_445: bv8;
var t1_451: bv8;
var t1_457: bv8;
var t1_463: bv8;
var t1_469: bv8;
var t1_475: bv8;
var t1_481: bv8;
var t1_487: bv8;
var t1_49: bv8;
var t1_55: bv8;
var t1_61: bv8;
var t1_67: bv8;
var t1_7: bv8;
var t1_73: bv8;
var t1_79: bv8;
var t1_85: bv8;
var t1_91: bv8;
var t1_97: bv8;
var t2_104: bv8;
var t2_110: bv8;
var t2_116: bv8;
var t2_122: bv8;
var t2_128: bv8;
var t2_134: bv8;
var t2_14: bv8;
var t2_140: bv8;
var t2_146: bv8;
var t2_152: bv8;
var t2_158: bv8;
var t2_164: bv8;
var t2_170: bv8;
var t2_176: bv8;
var t2_182: bv8;
var t2_188: bv8;
var t2_194: bv8;
var t2_2: bv8;
var t2_20: bv8;
var t2_200: bv8;
var t2_206: bv8;
var t2_212: bv8;
var t2_218: bv8;
var t2_224: bv8;
var t2_230: bv8;
var t2_236: bv8;
var t2_242: bv8;
var t2_248: bv8;
var t2_254: bv8;
var t2_26: bv8;
var t2_260: bv8;
var t2_266: bv8;
var t2_272: bv8;
var t2_278: bv8;
var t2_284: bv8;
var t2_290: bv8;
var t2_296: bv8;
var t2_302: bv8;
var t2_308: bv8;
var t2_314: bv8;
var t2_32: bv8;
var t2_320: bv8;
var t2_326: bv8;
var t2_332: bv8;
var t2_338: bv8;
var t2_344: bv8;
var t2_350: bv8;
var t2_356: bv8;
var t2_362: bv8;
var t2_368: bv8;
var t2_374: bv8;
var t2_38: bv8;
var t2_380: bv8;
var t2_386: bv8;
var t2_392: bv8;
var t2_398: bv8;
var t2_404: bv8;
var t2_410: bv8;
var t2_416: bv8;
var t2_422: bv8;
var t2_428: bv8;
var t2_434: bv8;
var t2_44: bv8;
var t2_440: bv8;
var t2_446: bv8;
var t2_452: bv8;
var t2_458: bv8;
var t2_464: bv8;
var t2_470: bv8;
var t2_476: bv8;
var t2_482: bv8;
var t2_488: bv8;
var t2_50: bv8;
var t2_56: bv8;
var t2_62: bv8;
var t2_68: bv8;
var t2_74: bv8;
var t2_8: bv8;
var t2_80: bv8;
var t2_86: bv8;
var t2_92: bv8;
var t2_98: bv8;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(3271bv64);
axiom policy(4483bv64);
axiom policy(5695bv64);
axiom policy(6907bv64);
axiom policy(9187bv64);
axiom policy(10414bv64);
axiom policy(11626bv64);
axiom policy(12838bv64);
axiom policy(14050bv64);
axiom policy(15262bv64);
axiom policy(16777bv64);
axiom policy(18105bv64);
axiom policy(19433bv64);
axiom policy(20761bv64);
axiom policy(22089bv64);
axiom policy(23468bv64);
axiom policy(24792bv64);
axiom policy(26116bv64);
axiom policy(27563bv64);
axiom policy(29283bv64);
axiom policy(30684bv64);
axiom policy(31906bv64);
axiom policy(33191bv64);
axiom policy(35319bv64);
axiom policy(36601bv64);
axiom policy(37800bv64);
axiom policy(40872bv64);
axiom policy(42188bv64);
axiom policy(44072bv64);
axiom policy(45388bv64);
axiom policy(51419bv64);
axiom policy(52735bv64);
axiom policy(62337bv64);
axiom policy(63549bv64);
axiom policy(64761bv64);
axiom policy(65973bv64);
axiom policy(67185bv64);
axiom policy(68502bv64);
axiom policy(69830bv64);
axiom policy(71158bv64);
axiom policy(72486bv64);
axiom policy(73959bv64);
axiom policy(76636bv64);
axiom policy(76816bv64);
