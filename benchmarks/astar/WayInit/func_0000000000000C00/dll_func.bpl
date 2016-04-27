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
axiom _function_addr_low == 3072bv64;
axiom _function_addr_high == 3840bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xc00:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0xc05:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xc09:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc0e:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0xc10:
RCX := (0bv32 ++ 1bv32);

label_0xc15:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), RCX[32:0]);

label_0xc19:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xc1c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0xc20:
origDEST_5 := RAX[32:0];
origCOUNT_6 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), CF, RSHIFT_32(origDEST_5, (MINUS_32(32bv32, origCOUNT_6)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_6 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_6 == 0bv32)), AF, unconstrained_2);

label_0xc22:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc27:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, 4bv64)));

label_0xc2a:
origDEST_11 := RAX[32:0];
origCOUNT_12 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), CF, RSHIFT_32(origDEST_11, (MINUS_32(32bv32, origCOUNT_12)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_12 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_12 == 0bv32)), AF, unconstrained_4);

label_0xc2c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0xc30:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)))));

label_0xc35:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, RSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_6);

label_0xc38:
R8 := RAX;

label_0xc3b:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_7;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xc3d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc42:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 120bv64));

label_0xc46:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3147bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc4b"} true;
call arbitrary_func();

label_0xc4b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)))));

label_0xc50:
origDEST_23 := RAX;
origCOUNT_24 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), CF, RSHIFT_64(origDEST_23, (MINUS_64(64bv64, origCOUNT_24)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_24 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_24 == 0bv64)), AF, unconstrained_9);

label_0xc54:
R8 := RAX;

label_0xc57:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_10;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xc59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc5e:
RCX := LOAD_LE_64(mem, PLUS_64(RAX, 128bv64));

label_0xc65:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3178bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc6a"} true;
call arbitrary_func();

label_0xc6a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0xc72:
goto label_0xc7e;

label_0xc74:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xc78:
t_29 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_29[32:31]) == (1bv32[32:31]))), (XOR_1((t_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_29)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xc7a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xc7e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc83:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0xc86:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0xc8a:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xcff;
}

label_0xc8c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xc91:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0xc94:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xc97:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xc9b:
origDEST_37 := RAX[32:0];
origCOUNT_38 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), CF, RSHIFT_32(origDEST_37, (MINUS_32(32bv32, origCOUNT_38)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv32)), AF, unconstrained_12);

label_0xc9d:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xc9f:
origDEST_43 := RAX;
origCOUNT_44 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), CF, RSHIFT_64(origDEST_43, (MINUS_64(64bv64, origCOUNT_44)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_44 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_44 == 0bv64)), AF, unconstrained_14);

label_0xca2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xca7:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xcab:
t1_49 := RCX;
t2_50 := RAX;
RCX := PLUS_64(RCX, t2_50);
CF := bool2bv(LT_64(RCX, t1_49));
OF := AND_1((bool2bv((t1_49[64:63]) == (t2_50[64:63]))), (XOR_1((t1_49[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_49)), t2_50)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xcae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RCX);

label_0xcb3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xcb8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xcbe:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xcc3:
t_57 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_16;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)), 2bv64)), (XOR_64((RSHIFT_64(t_57, 4bv64)), t_57)))))[1:0]));
SF := t_57[64:63];
ZF := bool2bv(0bv64 == t_57);

label_0xcc6:
if (bv2bool(ZF)) {
  goto label_0xcc9;
}

label_0xcc8:
assume false;

label_0xcc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xcce:
origDEST_61 := RAX;
origCOUNT_62 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), CF, LSHIFT_64(origDEST_61, (MINUS_64(64bv64, origCOUNT_62)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_62 == 1bv64)), origDEST_61[64:63], unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_62 == 0bv64)), AF, unconstrained_18);

label_0xcd2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xcd9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xcdd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xce2:
origDEST_67 := RCX;
origCOUNT_68 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), CF, LSHIFT_64(origDEST_67, (MINUS_64(64bv64, origCOUNT_68)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_68 == 1bv64)), origDEST_67[64:63], unconstrained_19));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_68 == 0bv64)), AF, unconstrained_20);

label_0xce6:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_21;
SF := unconstrained_22;
AF := unconstrained_23;
PF := unconstrained_24;

label_0xcea:
if (bv2bool(CF)) {
  goto label_0xced;
}

label_0xcec:
assume false;

label_0xced:
RAX := (0bv32 ++ 4294967295bv32);

label_0xcf2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xcf7:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0xcfa:
goto label_0xc74;

label_0xcff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0xd07:
goto label_0xd13;

label_0xd09:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xd0d:
t_73 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_73[32:31]) == (1bv32[32:31]))), (XOR_1((t_73[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_73)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd0f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xd13:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xd18:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0xd1b:
t_77 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_77)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_77, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)), 2bv32)), (XOR_32((RSHIFT_32(t_77, 4bv32)), t_77)))))[1:0]));
SF := t_77[32:31];
ZF := bool2bv(0bv32 == t_77);

label_0xd1f:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xd9c;
}

label_0xd21:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xd26:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0xd29:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xd2c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xd30:
origDEST_81 := RAX[32:0];
origCOUNT_82 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), CF, RSHIFT_32(origDEST_81, (MINUS_32(32bv32, origCOUNT_82)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv32)), AF, unconstrained_26);

label_0xd32:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xd37:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RCX, 12bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_27;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd3a:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xd3c:
origDEST_89 := RAX;
origCOUNT_90 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), CF, RSHIFT_64(origDEST_89, (MINUS_64(64bv64, origCOUNT_90)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_90 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_90 == 0bv64)), AF, unconstrained_29);

label_0xd3f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xd44:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xd48:
t1_95 := RCX;
t2_96 := RAX;
RCX := PLUS_64(RCX, t2_96);
CF := bool2bv(LT_64(RCX, t1_95));
OF := AND_1((bool2bv((t1_95[64:63]) == (t2_96[64:63]))), (XOR_1((t1_95[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_95)), t2_96)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xd4b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RCX);

label_0xd50:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xd55:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_30;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xd5b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xd60:
t_103 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)), 2bv64)), (XOR_64((RSHIFT_64(t_103, 4bv64)), t_103)))))[1:0]));
SF := t_103[64:63];
ZF := bool2bv(0bv64 == t_103);

label_0xd63:
if (bv2bool(ZF)) {
  goto label_0xd66;
}

label_0xd65:
assume false;

label_0xd66:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xd6b:
origDEST_107 := RAX;
origCOUNT_108 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), CF, LSHIFT_64(origDEST_107, (MINUS_64(64bv64, origCOUNT_108)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv64)), origDEST_107[64:63], unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv64)), AF, unconstrained_33);

label_0xd6f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xd76:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xd7a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xd7f:
origDEST_113 := RCX;
origCOUNT_114 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), CF, LSHIFT_64(origDEST_113, (MINUS_64(64bv64, origCOUNT_114)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_114 == 1bv64)), origDEST_113[64:63], unconstrained_34));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_114 == 0bv64)), AF, unconstrained_35);

label_0xd83:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_36;
SF := unconstrained_37;
AF := unconstrained_38;
PF := unconstrained_39;

label_0xd87:
if (bv2bool(CF)) {
  goto label_0xd8a;
}

label_0xd89:
assume false;

label_0xd8a:
RAX := (0bv32 ++ 4294967295bv32);

label_0xd8f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0xd94:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0xd97:
goto label_0xd09;

label_0xd9c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0xda4:
goto label_0xdb0;

label_0xda6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0xdaa:
t_119 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_119[32:31]) == (1bv32[32:31]))), (XOR_1((t_119[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_119)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdac:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0xdb0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xdb5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xdb8:
t_123 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_123)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_123, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)), 2bv32)), (XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)), 2bv32)), (XOR_32((RSHIFT_32(t_123, 4bv32)), t_123)))))[1:0]));
SF := t_123[32:31];
ZF := bool2bv(0bv32 == t_123);

label_0xdbc:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xe3b;
}

label_0xdbe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xdc3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0xdc6:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_40;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xdc8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), RCX[32:0]);

label_0xdcc:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xdcf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 84bv64)));

label_0xdd3:
origDEST_127 := RAX[32:0];
origCOUNT_128 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), CF, RSHIFT_32(origDEST_127, (MINUS_32(32bv32, origCOUNT_128)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv32)), AF, unconstrained_42);

label_0xdd5:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdd9:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xddb:
origDEST_135 := RAX;
origCOUNT_136 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, RSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_45);

label_0xdde:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xde3:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xde7:
t1_141 := RCX;
t2_142 := RAX;
RCX := PLUS_64(RCX, t2_142);
CF := bool2bv(LT_64(RCX, t1_141));
OF := AND_1((bool2bv((t1_141[64:63]) == (t2_142[64:63]))), (XOR_1((t1_141[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_141)), t2_142)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xdea:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RCX);

label_0xdef:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xdf4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xdfa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xdff:
t_149 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)), 2bv64)), (XOR_64((RSHIFT_64(t_149, 4bv64)), t_149)))))[1:0]));
SF := t_149[64:63];
ZF := bool2bv(0bv64 == t_149);

label_0xe02:
if (bv2bool(ZF)) {
  goto label_0xe05;
}

label_0xe04:
assume false;

label_0xe05:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xe0a:
origDEST_153 := RAX;
origCOUNT_154 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), CF, LSHIFT_64(origDEST_153, (MINUS_64(64bv64, origCOUNT_154)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_154 == 1bv64)), origDEST_153[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_154 == 0bv64)), AF, unconstrained_49);

label_0xe0e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xe15:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xe19:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xe1e:
origDEST_159 := RCX;
origCOUNT_160 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), CF, LSHIFT_64(origDEST_159, (MINUS_64(64bv64, origCOUNT_160)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_160 == 1bv64)), origDEST_159[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_160 == 0bv64)), AF, unconstrained_51);

label_0xe22:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_52;
SF := unconstrained_53;
AF := unconstrained_54;
PF := unconstrained_55;

label_0xe26:
if (bv2bool(CF)) {
  goto label_0xe29;
}

label_0xe28:
assume false;

label_0xe29:
RAX := (0bv32 ++ 4294967295bv32);

label_0xe2e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0xe33:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0xe36:
goto label_0xda6;

label_0xe3b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0xe43:
goto label_0xe4f;

label_0xe45:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0xe49:
t_165 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_165[32:31]) == (1bv32[32:31]))), (XOR_1((t_165[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_165)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xe4b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0xe4f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xe54:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 28bv64)));

label_0xe57:
t_169 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_169)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_169, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))))[1:0]));
SF := t_169[32:31];
ZF := bool2bv(0bv32 == t_169);

label_0xe5b:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0xee6;
}

label_0xe61:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xe66:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 8bv64)));

label_0xe69:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xe6e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RCX);

label_0xe73:
RCX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0xe76:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xe7b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 16bv64)));

label_0xe7e:
origDEST_173 := RAX[32:0];
origCOUNT_174 := AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32)));
RAX := (0bv32 ++ LSHIFT_32((RAX[32:0]), (AND_32((RCX[32:0]), (MINUS_32(32bv32, 1bv32))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), CF, RSHIFT_32(origDEST_173, (MINUS_32(32bv32, origCOUNT_174)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_174 == 1bv32)), XOR_1((RAX[32:0][32:31]), CF), unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), SF, RAX[32:0][32:31]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), ZF, bool2bv(0bv32 == (RAX[32:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), PF, NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_174 == 0bv32)), AF, unconstrained_57);

label_0xe80:
RAX := (0bv32 ++ OR_32((RAX[32:0]), (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xe84:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0xe86:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, RSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_60);

label_0xe89:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0xe8e:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0xe92:
t1_187 := RCX;
t2_188 := RAX;
RCX := PLUS_64(RCX, t2_188);
CF := bool2bv(LT_64(RCX, t1_187));
OF := AND_1((bool2bv((t1_187[64:63]) == (t2_188[64:63]))), (XOR_1((t1_187[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_187)), t2_188)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe95:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RCX);

label_0xe9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xe9f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xea5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xeaa:
t_195 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))))[1:0]));
SF := t_195[64:63];
ZF := bool2bv(0bv64 == t_195);

label_0xead:
if (bv2bool(ZF)) {
  goto label_0xeb0;
}

label_0xeaf:
assume false;

label_0xeb0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xeb5:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_64);

label_0xeb9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xec0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xec4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xec9:
origDEST_205 := RCX;
origCOUNT_206 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_66);

label_0xecd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0xed1:
if (bv2bool(CF)) {
  goto label_0xed4;
}

label_0xed3:
assume false;

label_0xed4:
RAX := (0bv32 ++ 4294967295bv32);

label_0xed9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0xede:
mem := STORE_LE_16(mem, RCX, RAX[32:0][16:0]);

label_0xee1:
goto label_0xe45;

label_0xee6:
t1_211 := RSP;
t2_212 := 104bv64;
RSP := PLUS_64(RSP, t2_212);
CF := bool2bv(LT_64(RSP, t1_211));
OF := AND_1((bool2bv((t1_211[64:63]) == (t2_212[64:63]))), (XOR_1((t1_211[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_211)), t2_212)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xeea:

ra_217 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_108,origCOUNT_114,origCOUNT_12,origCOUNT_128,origCOUNT_136,origCOUNT_154,origCOUNT_160,origCOUNT_174,origCOUNT_18,origCOUNT_182,origCOUNT_200,origCOUNT_206,origCOUNT_24,origCOUNT_38,origCOUNT_44,origCOUNT_6,origCOUNT_62,origCOUNT_68,origCOUNT_82,origCOUNT_90,origDEST_107,origDEST_11,origDEST_113,origDEST_127,origDEST_135,origDEST_153,origDEST_159,origDEST_17,origDEST_173,origDEST_181,origDEST_199,origDEST_205,origDEST_23,origDEST_37,origDEST_43,origDEST_5,origDEST_61,origDEST_67,origDEST_81,origDEST_89,ra_217,t1_141,t1_187,t1_211,t1_49,t1_95,t2_142,t2_188,t2_212,t2_50,t2_96,t_1,t_103,t_119,t_123,t_149,t_165,t_169,t_195,t_29,t_33,t_57,t_73,t_77;

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
const unconstrained_68: bv1;
const unconstrained_69: bv1;
const unconstrained_7: bv1;
const unconstrained_70: bv1;
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
var origCOUNT_108: bv64;
var origCOUNT_114: bv64;
var origCOUNT_12: bv32;
var origCOUNT_128: bv32;
var origCOUNT_136: bv64;
var origCOUNT_154: bv64;
var origCOUNT_160: bv64;
var origCOUNT_174: bv32;
var origCOUNT_18: bv64;
var origCOUNT_182: bv64;
var origCOUNT_200: bv64;
var origCOUNT_206: bv64;
var origCOUNT_24: bv64;
var origCOUNT_38: bv32;
var origCOUNT_44: bv64;
var origCOUNT_6: bv32;
var origCOUNT_62: bv64;
var origCOUNT_68: bv64;
var origCOUNT_82: bv32;
var origCOUNT_90: bv64;
var origDEST_107: bv64;
var origDEST_11: bv32;
var origDEST_113: bv64;
var origDEST_127: bv32;
var origDEST_135: bv64;
var origDEST_153: bv64;
var origDEST_159: bv64;
var origDEST_17: bv64;
var origDEST_173: bv32;
var origDEST_181: bv64;
var origDEST_199: bv64;
var origDEST_205: bv64;
var origDEST_23: bv64;
var origDEST_37: bv32;
var origDEST_43: bv64;
var origDEST_5: bv32;
var origDEST_61: bv64;
var origDEST_67: bv64;
var origDEST_81: bv32;
var origDEST_89: bv64;
var ra_217: bv64;
var t1_141: bv64;
var t1_187: bv64;
var t1_211: bv64;
var t1_49: bv64;
var t1_95: bv64;
var t2_142: bv64;
var t2_188: bv64;
var t2_212: bv64;
var t2_50: bv64;
var t2_96: bv64;
var t_1: bv64;
var t_103: bv64;
var t_119: bv32;
var t_123: bv32;
var t_149: bv64;
var t_165: bv32;
var t_169: bv32;
var t_195: bv64;
var t_29: bv32;
var t_33: bv32;
var t_57: bv64;
var t_73: bv32;
var t_77: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1296bv64);
axiom policy(2592bv64);
axiom policy(2832bv64);
axiom policy(3072bv64);
axiom policy(3840bv64);
axiom policy(5200bv64);
axiom policy(5728bv64);
axiom policy(9168bv64);
axiom policy(9184bv64);
