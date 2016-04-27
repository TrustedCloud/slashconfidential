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
axiom _function_addr_low == 6768bv64;
axiom _function_addr_high == 12448bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1a70:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x1a75:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0x1a7a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x1a7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x1a84:
t_1 := RSP;
RSP := MINUS_64(RSP, 488bv64);
CF := bool2bv(LT_64(t_1, 488bv64));
OF := AND_64((XOR_64(t_1, 488bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 488bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1a8b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1a93:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 32bv64)));

label_0x1a96:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0x1a9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1aa2:
RAX := LOAD_LE_64(mem, PLUS_64(RAX, 128bv64));

label_0x1aa9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RAX);

label_0x1aae:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), 0bv32);

label_0x1ab6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), 0bv32);

label_0x1abe:
goto label_0x1aca;

label_0x1ac0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)));

label_0x1ac4:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1ac6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), RAX[32:0]);

label_0x1aca:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 512bv64)));

label_0x1ad1:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x1ad5:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x3085;
}

label_0x1adb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 24bv64)))));

label_0x1ae0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 504bv64));

label_0x1ae8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x1aeb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RAX[32:0]);

label_0x1aef:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x1af3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x1af7:
t_13 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_13, (RAX[32:0])));
OF := AND_32((XOR_32(t_13, (RAX[32:0]))), (XOR_32(t_13, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_13)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1af9:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1afb:
t_17 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_17, 1bv32)), (XOR_32(t_17, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_17)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1afd:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1b00:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1b04:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1b09:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x1b0d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1b15:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x1b1c:
t_21 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x1b1e:
if (bv2bool(ZF)) {
  goto label_0x1d6b;
}

label_0x1b24:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1b28:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1b30:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x1b34:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x1b38:
t_25 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x1b3a:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1c9a;
}

label_0x1b40:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x1b45:
origDEST_29 := RAX;
origCOUNT_30 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), CF, RSHIFT_64(origDEST_29, (MINUS_64(64bv64, origCOUNT_30)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_30 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_2));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_30 == 0bv64)), AF, unconstrained_3);

label_0x1b49:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x1b51:
t1_35 := RCX;
t2_36 := RAX;
RCX := PLUS_64(RCX, t2_36);
CF := bool2bv(LT_64(RCX, t1_35));
OF := AND_1((bool2bv((t1_35[64:63]) == (t2_36[64:63]))), (XOR_1((t1_35[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_35)), t2_36)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1b54:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RCX);

label_0x1b59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b5e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_4;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b64:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1b69:
t_43 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x1b6c:
if (bv2bool(ZF)) {
  goto label_0x1b6f;
}

label_0x1b6e:
assume false;

label_0x1b6f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b74:
origDEST_47 := RAX;
origCOUNT_48 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_7);

label_0x1b78:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1b7f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1b83:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b88:
origDEST_53 := RCX;
origCOUNT_54 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), CF, LSHIFT_64(origDEST_53, (MINUS_64(64bv64, origCOUNT_54)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_54 == 1bv64)), origDEST_53[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_54 == 0bv64)), AF, unconstrained_9);

label_0x1b8c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_10;
SF := unconstrained_11;
AF := unconstrained_12;
PF := unconstrained_13;

label_0x1b90:
if (bv2bool(CF)) {
  goto label_0x1b93;
}

label_0x1b92:
assume false;

label_0x1b93:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1b98:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1b9b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1b9d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1ba1:
t_59 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_59[32:31]) == (1bv32[32:31]))), (XOR_1((t_59[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_59)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1ba3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x1ba7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1baf:
t1_63 := RAX;
t2_64 := 170bv64;
RAX := PLUS_64(RAX, t2_64);
CF := bool2bv(LT_64(RAX, t1_63));
OF := AND_1((bool2bv((t1_63[64:63]) == (t2_64[64:63]))), (XOR_1((t1_63[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_63)), t2_64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1bb5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 352bv64), RAX);

label_0x1bbd:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1bc1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1bc6:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1bca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1bcf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1bd4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1bda:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1bdf:
t_71 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)), 2bv64)), (XOR_64((RSHIFT_64(t_71, 4bv64)), t_71)))))[1:0]));
SF := t_71[64:63];
ZF := bool2bv(0bv64 == t_71);

label_0x1be2:
if (bv2bool(ZF)) {
  goto label_0x1be5;
}

label_0x1be4:
assume false;

label_0x1be5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1bea:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_17);

label_0x1bee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1bf5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1bf9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1bfe:
origDEST_81 := RCX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_19);

label_0x1c02:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_20;
SF := unconstrained_21;
AF := unconstrained_22;
PF := unconstrained_23;

label_0x1c06:
if (bv2bool(CF)) {
  goto label_0x1c09;
}

label_0x1c08:
assume false;

label_0x1c09:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1c0e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 352bv64));

label_0x1c16:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1c19:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1c1c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1c24:
t1_87 := RAX;
t2_88 := 168bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c2a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 360bv64), RAX);

label_0x1c32:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1c36:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1c3b:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1c3f:
t1_93 := RAX;
t2_94 := 2bv64;
RAX := PLUS_64(RAX, t2_94);
CF := bool2bv(LT_64(RAX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c43:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1c48:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c4d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_24;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c53:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1c58:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_25;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x1c5b:
if (bv2bool(ZF)) {
  goto label_0x1c5e;
}

label_0x1c5d:
assume false;

label_0x1c5e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c63:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_26));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_27);

label_0x1c67:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1c6e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1c72:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c77:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_28));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_29);

label_0x1c7b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_30;
SF := unconstrained_31;
AF := unconstrained_32;
PF := unconstrained_33;

label_0x1c7f:
if (bv2bool(CF)) {
  goto label_0x1c82;
}

label_0x1c81:
assume false;

label_0x1c82:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1c87:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 360bv64));

label_0x1c8f:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1c92:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1c95:
goto label_0x1d6b;

label_0x1c9a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1c9e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1ca6:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x1caa:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x1cae:
t_117 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x1cb0:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1d6b;
}

label_0x1cb6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1cbe:
t1_121 := RAX;
t2_122 := 160bv64;
RAX := PLUS_64(RAX, t2_122);
CF := bool2bv(LT_64(RAX, t1_121));
OF := AND_1((bool2bv((t1_121[64:63]) == (t2_122[64:63]))), (XOR_1((t1_121[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_121)), t2_122)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1cc4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1cc9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1cce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1cd4:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1cd9:
t_129 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)), 2bv64)), (XOR_64((RSHIFT_64(t_129, 4bv64)), t_129)))))[1:0]));
SF := t_129[64:63];
ZF := bool2bv(0bv64 == t_129);

label_0x1cdc:
if (bv2bool(ZF)) {
  goto label_0x1cdf;
}

label_0x1cde:
assume false;

label_0x1cdf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1ce4:
origDEST_133 := RAX;
origCOUNT_134 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), CF, LSHIFT_64(origDEST_133, (MINUS_64(64bv64, origCOUNT_134)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_134 == 1bv64)), origDEST_133[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_134 == 0bv64)), AF, unconstrained_38);

label_0x1ce8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1cef:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1cf3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1cf8:
origDEST_139 := RCX;
origCOUNT_140 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), CF, LSHIFT_64(origDEST_139, (MINUS_64(64bv64, origCOUNT_140)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_140 == 1bv64)), origDEST_139[64:63], unconstrained_39));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_140 == 0bv64)), AF, unconstrained_40);

label_0x1cfc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_41;
SF := unconstrained_42;
AF := unconstrained_43;
PF := unconstrained_44;

label_0x1d00:
if (bv2bool(CF)) {
  goto label_0x1d03;
}

label_0x1d02:
assume false;

label_0x1d03:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d08:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x1d0b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1d13:
t1_145 := RAX;
t2_146 := 164bv64;
RAX := PLUS_64(RAX, t2_146);
CF := bool2bv(LT_64(RAX, t1_145));
OF := AND_1((bool2bv((t1_145[64:63]) == (t2_146[64:63]))), (XOR_1((t1_145[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_145)), t2_146)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d19:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x1d1e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d23:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1d29:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1d2e:
t_153 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)), 2bv64)), (XOR_64((RSHIFT_64(t_153, 4bv64)), t_153)))))[1:0]));
SF := t_153[64:63];
ZF := bool2bv(0bv64 == t_153);

label_0x1d31:
if (bv2bool(ZF)) {
  goto label_0x1d34;
}

label_0x1d33:
assume false;

label_0x1d34:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d39:
origDEST_157 := RAX;
origCOUNT_158 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), CF, LSHIFT_64(origDEST_157, (MINUS_64(64bv64, origCOUNT_158)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_158 == 1bv64)), origDEST_157[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_158 == 0bv64)), AF, unconstrained_48);

label_0x1d3d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1d44:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1d48:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d4d:
origDEST_163 := RCX;
origCOUNT_164 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), CF, LSHIFT_64(origDEST_163, (MINUS_64(64bv64, origCOUNT_164)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_164 == 1bv64)), origDEST_163[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_164 == 0bv64)), AF, unconstrained_50);

label_0x1d51:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_51;
SF := unconstrained_52;
AF := unconstrained_53;
PF := unconstrained_54;

label_0x1d55:
if (bv2bool(CF)) {
  goto label_0x1d58;
}

label_0x1d57:
assume false;

label_0x1d58:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1d5d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1d60:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1d62:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1d66:
goto label_0x3089;

label_0x1d6b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x1d6f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x1d73:
t_169 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_169, (RAX[32:0])));
OF := AND_32((XOR_32(t_169, (RAX[32:0]))), (XOR_32(t_169, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_169)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1d75:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1d77:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1d7a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1d7e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1d83:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x1d87:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1d8f:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x1d96:
t_173 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_173)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_173, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)), 2bv32)), (XOR_32((RSHIFT_32(t_173, 4bv32)), t_173)))))[1:0]));
SF := t_173[32:31];
ZF := bool2bv(0bv32 == t_173);

label_0x1d98:
if (bv2bool(ZF)) {
  goto label_0x1fe5;
}

label_0x1d9e:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1da2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1daa:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x1dae:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x1db2:
t_177 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_55;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)), 2bv32)), (XOR_32((RSHIFT_32(t_177, 4bv32)), t_177)))))[1:0]));
SF := t_177[32:31];
ZF := bool2bv(0bv32 == t_177);

label_0x1db4:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x1f14;
}

label_0x1dba:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x1dbf:
origDEST_181 := RAX;
origCOUNT_182 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), CF, RSHIFT_64(origDEST_181, (MINUS_64(64bv64, origCOUNT_182)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_182 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_56));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_182 == 0bv64)), AF, unconstrained_57);

label_0x1dc3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x1dcb:
t1_187 := RCX;
t2_188 := RAX;
RCX := PLUS_64(RCX, t2_188);
CF := bool2bv(LT_64(RCX, t1_187));
OF := AND_1((bool2bv((t1_187[64:63]) == (t2_188[64:63]))), (XOR_1((t1_187[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_187)), t2_188)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1dce:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RCX);

label_0x1dd3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1dd8:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_58;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1dde:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1de3:
t_195 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_59;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)), 2bv64)), (XOR_64((RSHIFT_64(t_195, 4bv64)), t_195)))))[1:0]));
SF := t_195[64:63];
ZF := bool2bv(0bv64 == t_195);

label_0x1de6:
if (bv2bool(ZF)) {
  goto label_0x1de9;
}

label_0x1de8:
assume false;

label_0x1de9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1dee:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, LSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), origDEST_199[64:63], unconstrained_60));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_61);

label_0x1df2:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1df9:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1dfd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1e02:
origDEST_205 := RCX;
origCOUNT_206 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), CF, LSHIFT_64(origDEST_205, (MINUS_64(64bv64, origCOUNT_206)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_206 == 1bv64)), origDEST_205[64:63], unconstrained_62));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_206 == 0bv64)), AF, unconstrained_63);

label_0x1e06:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_64;
SF := unconstrained_65;
AF := unconstrained_66;
PF := unconstrained_67;

label_0x1e0a:
if (bv2bool(CF)) {
  goto label_0x1e0d;
}

label_0x1e0c:
assume false;

label_0x1e0d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1e12:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1e15:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1e17:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1e1b:
t_211 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_211[32:31]) == (1bv32[32:31]))), (XOR_1((t_211[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_211)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1e1d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x1e21:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1e29:
t1_215 := RAX;
t2_216 := 170bv64;
RAX := PLUS_64(RAX, t2_216);
CF := bool2bv(LT_64(RAX, t1_215));
OF := AND_1((bool2bv((t1_215[64:63]) == (t2_216[64:63]))), (XOR_1((t1_215[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_215)), t2_216)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1e2f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 368bv64), RAX);

label_0x1e37:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1e3b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1e40:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1e44:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x1e49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1e4e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_68;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1e54:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1e59:
t_223 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_69;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)), 2bv64)), (XOR_64((RSHIFT_64(t_223, 4bv64)), t_223)))))[1:0]));
SF := t_223[64:63];
ZF := bool2bv(0bv64 == t_223);

label_0x1e5c:
if (bv2bool(ZF)) {
  goto label_0x1e5f;
}

label_0x1e5e:
assume false;

label_0x1e5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1e64:
origDEST_227 := RAX;
origCOUNT_228 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), CF, LSHIFT_64(origDEST_227, (MINUS_64(64bv64, origCOUNT_228)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_228 == 1bv64)), origDEST_227[64:63], unconstrained_70));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_228 == 0bv64)), AF, unconstrained_71);

label_0x1e68:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1e6f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1e73:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1e78:
origDEST_233 := RCX;
origCOUNT_234 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_72));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_73);

label_0x1e7c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_74;
SF := unconstrained_75;
AF := unconstrained_76;
PF := unconstrained_77;

label_0x1e80:
if (bv2bool(CF)) {
  goto label_0x1e83;
}

label_0x1e82:
assume false;

label_0x1e83:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1e88:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 368bv64));

label_0x1e90:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1e93:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1e96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1e9e:
t1_239 := RAX;
t2_240 := 168bv64;
RAX := PLUS_64(RAX, t2_240);
CF := bool2bv(LT_64(RAX, t1_239));
OF := AND_1((bool2bv((t1_239[64:63]) == (t2_240[64:63]))), (XOR_1((t1_239[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_239)), t2_240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ea4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 376bv64), RAX);

label_0x1eac:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1eb0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1eb5:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x1eb9:
t1_245 := RAX;
t2_246 := 2bv64;
RAX := PLUS_64(RAX, t2_246);
CF := bool2bv(LT_64(RAX, t1_245));
OF := AND_1((bool2bv((t1_245[64:63]) == (t2_246[64:63]))), (XOR_1((t1_245[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_245)), t2_246)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ebd:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x1ec2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1ec7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_78;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1ecd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1ed2:
t_253 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_79;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)), 2bv64)), (XOR_64((RSHIFT_64(t_253, 4bv64)), t_253)))))[1:0]));
SF := t_253[64:63];
ZF := bool2bv(0bv64 == t_253);

label_0x1ed5:
if (bv2bool(ZF)) {
  goto label_0x1ed8;
}

label_0x1ed7:
assume false;

label_0x1ed8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1edd:
origDEST_257 := RAX;
origCOUNT_258 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), CF, LSHIFT_64(origDEST_257, (MINUS_64(64bv64, origCOUNT_258)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_258 == 1bv64)), origDEST_257[64:63], unconstrained_80));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_258 == 0bv64)), AF, unconstrained_81);

label_0x1ee1:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1ee8:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1eec:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1ef1:
origDEST_263 := RCX;
origCOUNT_264 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), CF, LSHIFT_64(origDEST_263, (MINUS_64(64bv64, origCOUNT_264)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_264 == 1bv64)), origDEST_263[64:63], unconstrained_82));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_264 == 0bv64)), AF, unconstrained_83);

label_0x1ef5:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_84;
SF := unconstrained_85;
AF := unconstrained_86;
PF := unconstrained_87;

label_0x1ef9:
if (bv2bool(CF)) {
  goto label_0x1efc;
}

label_0x1efb:
assume false;

label_0x1efc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x1f01:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 376bv64));

label_0x1f09:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x1f0c:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x1f0f:
goto label_0x1fe5;

label_0x1f14:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1f18:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1f20:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x1f24:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x1f28:
t_269 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_88;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_269, 4bv32)), t_269)), 2bv32)), (XOR_32((RSHIFT_32(t_269, 4bv32)), t_269)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_269, 4bv32)), t_269)), 2bv32)), (XOR_32((RSHIFT_32(t_269, 4bv32)), t_269)))))[1:0]));
SF := t_269[32:31];
ZF := bool2bv(0bv32 == t_269);

label_0x1f2a:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1fe5;
}

label_0x1f30:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1f38:
t1_273 := RAX;
t2_274 := 160bv64;
RAX := PLUS_64(RAX, t2_274);
CF := bool2bv(LT_64(RAX, t1_273));
OF := AND_1((bool2bv((t1_273[64:63]) == (t2_274[64:63]))), (XOR_1((t1_273[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_273)), t2_274)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1f3e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x1f43:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1f48:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_89;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1f4e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1f53:
t_281 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_90;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)), 2bv64)), (XOR_64((RSHIFT_64(t_281, 4bv64)), t_281)))))[1:0]));
SF := t_281[64:63];
ZF := bool2bv(0bv64 == t_281);

label_0x1f56:
if (bv2bool(ZF)) {
  goto label_0x1f59;
}

label_0x1f58:
assume false;

label_0x1f59:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1f5e:
origDEST_285 := RAX;
origCOUNT_286 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), CF, LSHIFT_64(origDEST_285, (MINUS_64(64bv64, origCOUNT_286)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_286 == 1bv64)), origDEST_285[64:63], unconstrained_91));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_286 == 0bv64)), AF, unconstrained_92);

label_0x1f62:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1f69:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1f6d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1f72:
origDEST_291 := RCX;
origCOUNT_292 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), CF, LSHIFT_64(origDEST_291, (MINUS_64(64bv64, origCOUNT_292)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_292 == 1bv64)), origDEST_291[64:63], unconstrained_93));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_292 == 0bv64)), AF, unconstrained_94);

label_0x1f76:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_95;
SF := unconstrained_96;
AF := unconstrained_97;
PF := unconstrained_98;

label_0x1f7a:
if (bv2bool(CF)) {
  goto label_0x1f7d;
}

label_0x1f7c:
assume false;

label_0x1f7d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1f82:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x1f85:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x1f8d:
t1_297 := RAX;
t2_298 := 164bv64;
RAX := PLUS_64(RAX, t2_298);
CF := bool2bv(LT_64(RAX, t1_297));
OF := AND_1((bool2bv((t1_297[64:63]) == (t2_298[64:63]))), (XOR_1((t1_297[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_297)), t2_298)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1f93:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x1f98:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1f9d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_99;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1fa3:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1fa8:
t_305 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_100;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)), 2bv64)), (XOR_64((RSHIFT_64(t_305, 4bv64)), t_305)))))[1:0]));
SF := t_305[64:63];
ZF := bool2bv(0bv64 == t_305);

label_0x1fab:
if (bv2bool(ZF)) {
  goto label_0x1fae;
}

label_0x1fad:
assume false;

label_0x1fae:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1fb3:
origDEST_309 := RAX;
origCOUNT_310 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), CF, LSHIFT_64(origDEST_309, (MINUS_64(64bv64, origCOUNT_310)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_310 == 1bv64)), origDEST_309[64:63], unconstrained_101));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_310 == 0bv64)), AF, unconstrained_102);

label_0x1fb7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1fbe:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1fc2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1fc7:
origDEST_315 := RCX;
origCOUNT_316 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), CF, LSHIFT_64(origDEST_315, (MINUS_64(64bv64, origCOUNT_316)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_316 == 1bv64)), origDEST_315[64:63], unconstrained_103));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_316 == 0bv64)), AF, unconstrained_104);

label_0x1fcb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_105;
SF := unconstrained_106;
AF := unconstrained_107;
PF := unconstrained_108;

label_0x1fcf:
if (bv2bool(CF)) {
  goto label_0x1fd2;
}

label_0x1fd1:
assume false;

label_0x1fd2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1fd7:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x1fda:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x1fdc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x1fe0:
goto label_0x3089;

label_0x1fe5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x1fe9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x1fed:
t_321 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_321, (RAX[32:0])));
OF := AND_32((XOR_32(t_321, (RAX[32:0]))), (XOR_32(t_321, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_321)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x1fef:
RAX := (0bv32 ++ RCX[32:0]);

label_0x1ff1:
t_325 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_325[32:31]) == (1bv32[32:31]))), (XOR_1((t_325[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_325)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1ff3:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x1ff6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x1ffa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x1fff:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x2003:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x200b:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x2012:
t_329 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_329)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_329, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_329, 4bv32)), t_329)), 2bv32)), (XOR_32((RSHIFT_32(t_329, 4bv32)), t_329)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_329, 4bv32)), t_329)), 2bv32)), (XOR_32((RSHIFT_32(t_329, 4bv32)), t_329)))))[1:0]));
SF := t_329[32:31];
ZF := bool2bv(0bv32 == t_329);

label_0x2014:
if (bv2bool(ZF)) {
  goto label_0x228e;
}

label_0x201a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x201e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2026:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x202a:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x202e:
t_333 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_109;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_333, 4bv32)), t_333)), 2bv32)), (XOR_32((RSHIFT_32(t_333, 4bv32)), t_333)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_333, 4bv32)), t_333)), 2bv32)), (XOR_32((RSHIFT_32(t_333, 4bv32)), t_333)))))[1:0]));
SF := t_333[32:31];
ZF := bool2bv(0bv32 == t_333);

label_0x2030:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x219f;
}

label_0x2036:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x203b:
origDEST_337 := RAX;
origCOUNT_338 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), CF, RSHIFT_64(origDEST_337, (MINUS_64(64bv64, origCOUNT_338)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_338 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_110));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_338 == 0bv64)), AF, unconstrained_111);

label_0x203f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x2047:
t1_343 := RCX;
t2_344 := RAX;
RCX := PLUS_64(RCX, t2_344);
CF := bool2bv(LT_64(RCX, t1_343));
OF := AND_1((bool2bv((t1_343[64:63]) == (t2_344[64:63]))), (XOR_1((t1_343[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_343)), t2_344)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x204a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RCX);

label_0x204f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x2054:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_112;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x205a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x205f:
t_351 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_113;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)), 2bv64)), (XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)), 2bv64)), (XOR_64((RSHIFT_64(t_351, 4bv64)), t_351)))))[1:0]));
SF := t_351[64:63];
ZF := bool2bv(0bv64 == t_351);

label_0x2062:
if (bv2bool(ZF)) {
  goto label_0x2065;
}

label_0x2064:
assume false;

label_0x2065:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x206a:
origDEST_355 := RAX;
origCOUNT_356 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), CF, LSHIFT_64(origDEST_355, (MINUS_64(64bv64, origCOUNT_356)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_356 == 1bv64)), origDEST_355[64:63], unconstrained_114));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_356 == 0bv64)), AF, unconstrained_115);

label_0x206e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2075:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2079:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x207e:
origDEST_361 := RCX;
origCOUNT_362 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), CF, LSHIFT_64(origDEST_361, (MINUS_64(64bv64, origCOUNT_362)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_362 == 1bv64)), origDEST_361[64:63], unconstrained_116));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_362 == 0bv64)), AF, unconstrained_117);

label_0x2082:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_118;
SF := unconstrained_119;
AF := unconstrained_120;
PF := unconstrained_121;

label_0x2086:
if (bv2bool(CF)) {
  goto label_0x2089;
}

label_0x2088:
assume false;

label_0x2089:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x208e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2091:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2093:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2097:
t_367 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_367[32:31]) == (1bv32[32:31]))), (XOR_1((t_367[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_367)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2099:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x209d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x20a5:
t1_371 := RAX;
t2_372 := 170bv64;
RAX := PLUS_64(RAX, t2_372);
CF := bool2bv(LT_64(RAX, t1_371));
OF := AND_1((bool2bv((t1_371[64:63]) == (t2_372[64:63]))), (XOR_1((t1_371[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_371)), t2_372)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x20ab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 384bv64), RAX);

label_0x20b3:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x20b7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x20bc:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x20c0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RAX);

label_0x20c5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x20ca:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_122;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x20d0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x20d5:
t_379 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_123;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_379, 4bv64)), t_379)), 2bv64)), (XOR_64((RSHIFT_64(t_379, 4bv64)), t_379)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_379, 4bv64)), t_379)), 2bv64)), (XOR_64((RSHIFT_64(t_379, 4bv64)), t_379)))))[1:0]));
SF := t_379[64:63];
ZF := bool2bv(0bv64 == t_379);

label_0x20d8:
if (bv2bool(ZF)) {
  goto label_0x20db;
}

label_0x20da:
assume false;

label_0x20db:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x20e0:
origDEST_383 := RAX;
origCOUNT_384 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), CF, LSHIFT_64(origDEST_383, (MINUS_64(64bv64, origCOUNT_384)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_384 == 1bv64)), origDEST_383[64:63], unconstrained_124));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_384 == 0bv64)), AF, unconstrained_125);

label_0x20e4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x20eb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x20ef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x20f4:
origDEST_389 := RCX;
origCOUNT_390 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), CF, LSHIFT_64(origDEST_389, (MINUS_64(64bv64, origCOUNT_390)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_390 == 1bv64)), origDEST_389[64:63], unconstrained_126));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_390 == 0bv64)), AF, unconstrained_127);

label_0x20f8:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_128;
SF := unconstrained_129;
AF := unconstrained_130;
PF := unconstrained_131;

label_0x20fc:
if (bv2bool(CF)) {
  goto label_0x20ff;
}

label_0x20fe:
assume false;

label_0x20ff:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x2104:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 384bv64));

label_0x210c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x210f:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2112:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x211a:
t1_395 := RAX;
t2_396 := 168bv64;
RAX := PLUS_64(RAX, t2_396);
CF := bool2bv(LT_64(RAX, t1_395));
OF := AND_1((bool2bv((t1_395[64:63]) == (t2_396[64:63]))), (XOR_1((t1_395[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_395)), t2_396)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2120:
mem := STORE_LE_64(mem, PLUS_64(RSP, 392bv64), RAX);

label_0x2128:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x212c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2131:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2135:
t1_401 := RAX;
t2_402 := 2bv64;
RAX := PLUS_64(RAX, t2_402);
CF := bool2bv(LT_64(RAX, t1_401));
OF := AND_1((bool2bv((t1_401[64:63]) == (t2_402[64:63]))), (XOR_1((t1_401[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_401)), t2_402)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2139:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RAX);

label_0x2141:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2149:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_132;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x214f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2154:
t_409 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_133;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_409, 4bv64)), t_409)), 2bv64)), (XOR_64((RSHIFT_64(t_409, 4bv64)), t_409)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_409, 4bv64)), t_409)), 2bv64)), (XOR_64((RSHIFT_64(t_409, 4bv64)), t_409)))))[1:0]));
SF := t_409[64:63];
ZF := bool2bv(0bv64 == t_409);

label_0x2157:
if (bv2bool(ZF)) {
  goto label_0x215a;
}

label_0x2159:
assume false;

label_0x215a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2162:
origDEST_413 := RAX;
origCOUNT_414 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), CF, LSHIFT_64(origDEST_413, (MINUS_64(64bv64, origCOUNT_414)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_414 == 1bv64)), origDEST_413[64:63], unconstrained_134));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_414 == 0bv64)), AF, unconstrained_135);

label_0x2166:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x216d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2171:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x2179:
origDEST_419 := RCX;
origCOUNT_420 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), CF, LSHIFT_64(origDEST_419, (MINUS_64(64bv64, origCOUNT_420)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_420 == 1bv64)), origDEST_419[64:63], unconstrained_136));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_420 == 0bv64)), AF, unconstrained_137);

label_0x217d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_138;
SF := unconstrained_139;
AF := unconstrained_140;
PF := unconstrained_141;

label_0x2181:
if (bv2bool(CF)) {
  goto label_0x2184;
}

label_0x2183:
assume false;

label_0x2184:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x218c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 392bv64));

label_0x2194:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2197:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x219a:
goto label_0x228e;

label_0x219f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x21a3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x21ab:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x21af:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x21b3:
t_425 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_142;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)), 2bv32)), (XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)), 2bv32)), (XOR_32((RSHIFT_32(t_425, 4bv32)), t_425)))))[1:0]));
SF := t_425[32:31];
ZF := bool2bv(0bv32 == t_425);

label_0x21b5:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x228e;
}

label_0x21bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x21c3:
t1_429 := RAX;
t2_430 := 160bv64;
RAX := PLUS_64(RAX, t2_430);
CF := bool2bv(LT_64(RAX, t1_429));
OF := AND_1((bool2bv((t1_429[64:63]) == (t2_430[64:63]))), (XOR_1((t1_429[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_429)), t2_430)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21c9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RAX);

label_0x21d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x21d9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_143;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x21df:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x21e4:
t_437 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_144;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)), 2bv64)), (XOR_64((RSHIFT_64(t_437, 4bv64)), t_437)))))[1:0]));
SF := t_437[64:63];
ZF := bool2bv(0bv64 == t_437);

label_0x21e7:
if (bv2bool(ZF)) {
  goto label_0x21ea;
}

label_0x21e9:
assume false;

label_0x21ea:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x21f2:
origDEST_441 := RAX;
origCOUNT_442 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), CF, LSHIFT_64(origDEST_441, (MINUS_64(64bv64, origCOUNT_442)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_442 == 1bv64)), origDEST_441[64:63], unconstrained_145));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_442 == 0bv64)), AF, unconstrained_146);

label_0x21f6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x21fd:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2201:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x2209:
origDEST_447 := RCX;
origCOUNT_448 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), CF, LSHIFT_64(origDEST_447, (MINUS_64(64bv64, origCOUNT_448)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_448 == 1bv64)), origDEST_447[64:63], unconstrained_147));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_448 == 0bv64)), AF, unconstrained_148);

label_0x220d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_149;
SF := unconstrained_150;
AF := unconstrained_151;
PF := unconstrained_152;

label_0x2211:
if (bv2bool(CF)) {
  goto label_0x2214;
}

label_0x2213:
assume false;

label_0x2214:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x221c:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x221f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2227:
t1_453 := RAX;
t2_454 := 164bv64;
RAX := PLUS_64(RAX, t2_454);
CF := bool2bv(LT_64(RAX, t1_453));
OF := AND_1((bool2bv((t1_453[64:63]) == (t2_454[64:63]))), (XOR_1((t1_453[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_453)), t2_454)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x222d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 144bv64), RAX);

label_0x2235:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x223d:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_153;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2243:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2248:
t_461 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_154;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)), 2bv64)), (XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)), 2bv64)), (XOR_64((RSHIFT_64(t_461, 4bv64)), t_461)))))[1:0]));
SF := t_461[64:63];
ZF := bool2bv(0bv64 == t_461);

label_0x224b:
if (bv2bool(ZF)) {
  goto label_0x224e;
}

label_0x224d:
assume false;

label_0x224e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2256:
origDEST_465 := RAX;
origCOUNT_466 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), CF, LSHIFT_64(origDEST_465, (MINUS_64(64bv64, origCOUNT_466)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_466 == 1bv64)), origDEST_465[64:63], unconstrained_155));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_466 == 0bv64)), AF, unconstrained_156);

label_0x225a:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2261:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2265:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x226d:
origDEST_471 := RCX;
origCOUNT_472 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), CF, LSHIFT_64(origDEST_471, (MINUS_64(64bv64, origCOUNT_472)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_472 == 1bv64)), origDEST_471[64:63], unconstrained_157));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_472 == 0bv64)), AF, unconstrained_158);

label_0x2271:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_159;
SF := unconstrained_160;
AF := unconstrained_161;
PF := unconstrained_162;

label_0x2275:
if (bv2bool(CF)) {
  goto label_0x2278;
}

label_0x2277:
assume false;

label_0x2278:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 144bv64));

label_0x2280:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2283:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2285:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2289:
goto label_0x3089;

label_0x228e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x2292:
t_477 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_477, 1bv32)), (XOR_32(t_477, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_477)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2294:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x2297:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x229b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x22a0:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x22a4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x22ac:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x22b3:
t_481 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_481)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_481, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_481, 4bv32)), t_481)), 2bv32)), (XOR_32((RSHIFT_32(t_481, 4bv32)), t_481)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_481, 4bv32)), t_481)), 2bv32)), (XOR_32((RSHIFT_32(t_481, 4bv32)), t_481)))))[1:0]));
SF := t_481[32:31];
ZF := bool2bv(0bv32 == t_481);

label_0x22b5:
if (bv2bool(ZF)) {
  goto label_0x254d;
}

label_0x22bb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x22bf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x22c7:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x22cb:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x22cf:
t_485 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_163;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)), 2bv32)), (XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)), 2bv32)), (XOR_32((RSHIFT_32(t_485, 4bv32)), t_485)))))[1:0]));
SF := t_485[32:31];
ZF := bool2bv(0bv32 == t_485);

label_0x22d1:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x245e;
}

label_0x22d7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x22dc:
origDEST_489 := RAX;
origCOUNT_490 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), CF, RSHIFT_64(origDEST_489, (MINUS_64(64bv64, origCOUNT_490)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_490 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_164));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_490 == 0bv64)), AF, unconstrained_165);

label_0x22e0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x22e8:
t1_495 := RCX;
t2_496 := RAX;
RCX := PLUS_64(RCX, t2_496);
CF := bool2bv(LT_64(RCX, t1_495));
OF := AND_1((bool2bv((t1_495[64:63]) == (t2_496[64:63]))), (XOR_1((t1_495[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_495)), t2_496)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x22eb:
mem := STORE_LE_64(mem, PLUS_64(RSP, 152bv64), RCX);

label_0x22f3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x22fb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_166;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2301:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2306:
t_503 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_167;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)), 2bv64)), (XOR_64((RSHIFT_64(t_503, 4bv64)), t_503)))))[1:0]));
SF := t_503[64:63];
ZF := bool2bv(0bv64 == t_503);

label_0x2309:
if (bv2bool(ZF)) {
  goto label_0x230c;
}

label_0x230b:
assume false;

label_0x230c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x2314:
origDEST_507 := RAX;
origCOUNT_508 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), CF, LSHIFT_64(origDEST_507, (MINUS_64(64bv64, origCOUNT_508)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_508 == 1bv64)), origDEST_507[64:63], unconstrained_168));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_508 == 0bv64)), AF, unconstrained_169);

label_0x2318:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x231f:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2323:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x232b:
origDEST_513 := RCX;
origCOUNT_514 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), CF, LSHIFT_64(origDEST_513, (MINUS_64(64bv64, origCOUNT_514)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_514 == 1bv64)), origDEST_513[64:63], unconstrained_170));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_514 == 0bv64)), AF, unconstrained_171);

label_0x232f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_172;
SF := unconstrained_173;
AF := unconstrained_174;
PF := unconstrained_175;

label_0x2333:
if (bv2bool(CF)) {
  goto label_0x2336;
}

label_0x2335:
assume false;

label_0x2336:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 152bv64));

label_0x233e:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2341:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2343:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2347:
t_519 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_519[32:31]) == (1bv32[32:31]))), (XOR_1((t_519[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_519)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2349:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x234d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2355:
t1_523 := RAX;
t2_524 := 170bv64;
RAX := PLUS_64(RAX, t2_524);
CF := bool2bv(LT_64(RAX, t1_523));
OF := AND_1((bool2bv((t1_523[64:63]) == (t2_524[64:63]))), (XOR_1((t1_523[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_523)), t2_524)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x235b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 400bv64), RAX);

label_0x2363:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2367:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x236c:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2370:
mem := STORE_LE_64(mem, PLUS_64(RSP, 160bv64), RAX);

label_0x2378:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2380:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_176;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2386:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x238b:
t_531 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_177;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)), 2bv64)), (XOR_64((RSHIFT_64(t_531, 4bv64)), t_531)))))[1:0]));
SF := t_531[64:63];
ZF := bool2bv(0bv64 == t_531);

label_0x238e:
if (bv2bool(ZF)) {
  goto label_0x2391;
}

label_0x2390:
assume false;

label_0x2391:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x2399:
origDEST_535 := RAX;
origCOUNT_536 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), CF, LSHIFT_64(origDEST_535, (MINUS_64(64bv64, origCOUNT_536)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_536 == 1bv64)), origDEST_535[64:63], unconstrained_178));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_536 == 0bv64)), AF, unconstrained_179);

label_0x239d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x23a4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x23a8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x23b0:
origDEST_541 := RCX;
origCOUNT_542 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), CF, LSHIFT_64(origDEST_541, (MINUS_64(64bv64, origCOUNT_542)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_542 == 1bv64)), origDEST_541[64:63], unconstrained_180));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_542 == 0bv64)), AF, unconstrained_181);

label_0x23b4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_182;
SF := unconstrained_183;
AF := unconstrained_184;
PF := unconstrained_185;

label_0x23b8:
if (bv2bool(CF)) {
  goto label_0x23bb;
}

label_0x23ba:
assume false;

label_0x23bb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x23c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 400bv64));

label_0x23cb:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x23ce:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x23d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x23d9:
t1_547 := RAX;
t2_548 := 168bv64;
RAX := PLUS_64(RAX, t2_548);
CF := bool2bv(LT_64(RAX, t1_547));
OF := AND_1((bool2bv((t1_547[64:63]) == (t2_548[64:63]))), (XOR_1((t1_547[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_547)), t2_548)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x23df:
mem := STORE_LE_64(mem, PLUS_64(RSP, 408bv64), RAX);

label_0x23e7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x23eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x23f0:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x23f4:
t1_553 := RAX;
t2_554 := 2bv64;
RAX := PLUS_64(RAX, t2_554);
CF := bool2bv(LT_64(RAX, t1_553));
OF := AND_1((bool2bv((t1_553[64:63]) == (t2_554[64:63]))), (XOR_1((t1_553[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_553)), t2_554)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x23f8:
mem := STORE_LE_64(mem, PLUS_64(RSP, 168bv64), RAX);

label_0x2400:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2408:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_186;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x240e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2413:
t_561 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_187;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)), 2bv64)), (XOR_64((RSHIFT_64(t_561, 4bv64)), t_561)))))[1:0]));
SF := t_561[64:63];
ZF := bool2bv(0bv64 == t_561);

label_0x2416:
if (bv2bool(ZF)) {
  goto label_0x2419;
}

label_0x2418:
assume false;

label_0x2419:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2421:
origDEST_565 := RAX;
origCOUNT_566 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), CF, LSHIFT_64(origDEST_565, (MINUS_64(64bv64, origCOUNT_566)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_566 == 1bv64)), origDEST_565[64:63], unconstrained_188));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_566 == 0bv64)), AF, unconstrained_189);

label_0x2425:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x242c:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2430:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x2438:
origDEST_571 := RCX;
origCOUNT_572 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), CF, LSHIFT_64(origDEST_571, (MINUS_64(64bv64, origCOUNT_572)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_572 == 1bv64)), origDEST_571[64:63], unconstrained_190));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_572 == 0bv64)), AF, unconstrained_191);

label_0x243c:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_192;
SF := unconstrained_193;
AF := unconstrained_194;
PF := unconstrained_195;

label_0x2440:
if (bv2bool(CF)) {
  goto label_0x2443;
}

label_0x2442:
assume false;

label_0x2443:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x244b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 408bv64));

label_0x2453:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2456:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2459:
goto label_0x254d;

label_0x245e:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2462:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x246a:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x246e:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2472:
t_577 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_196;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_577, 4bv32)), t_577)), 2bv32)), (XOR_32((RSHIFT_32(t_577, 4bv32)), t_577)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_577, 4bv32)), t_577)), 2bv32)), (XOR_32((RSHIFT_32(t_577, 4bv32)), t_577)))))[1:0]));
SF := t_577[32:31];
ZF := bool2bv(0bv32 == t_577);

label_0x2474:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x254d;
}

label_0x247a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2482:
t1_581 := RAX;
t2_582 := 160bv64;
RAX := PLUS_64(RAX, t2_582);
CF := bool2bv(LT_64(RAX, t1_581));
OF := AND_1((bool2bv((t1_581[64:63]) == (t2_582[64:63]))), (XOR_1((t1_581[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_581)), t2_582)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2488:
mem := STORE_LE_64(mem, PLUS_64(RSP, 176bv64), RAX);

label_0x2490:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2498:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_197;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x249e:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x24a3:
t_589 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_198;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_589, 4bv64)), t_589)), 2bv64)), (XOR_64((RSHIFT_64(t_589, 4bv64)), t_589)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_589, 4bv64)), t_589)), 2bv64)), (XOR_64((RSHIFT_64(t_589, 4bv64)), t_589)))))[1:0]));
SF := t_589[64:63];
ZF := bool2bv(0bv64 == t_589);

label_0x24a6:
if (bv2bool(ZF)) {
  goto label_0x24a9;
}

label_0x24a8:
assume false;

label_0x24a9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x24b1:
origDEST_593 := RAX;
origCOUNT_594 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), CF, LSHIFT_64(origDEST_593, (MINUS_64(64bv64, origCOUNT_594)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_594 == 1bv64)), origDEST_593[64:63], unconstrained_199));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_594 == 0bv64)), AF, unconstrained_200);

label_0x24b5:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x24bc:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x24c0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x24c8:
origDEST_599 := RCX;
origCOUNT_600 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), CF, LSHIFT_64(origDEST_599, (MINUS_64(64bv64, origCOUNT_600)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_600 == 1bv64)), origDEST_599[64:63], unconstrained_201));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_600 == 0bv64)), AF, unconstrained_202);

label_0x24cc:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_203;
SF := unconstrained_204;
AF := unconstrained_205;
PF := unconstrained_206;

label_0x24d0:
if (bv2bool(CF)) {
  goto label_0x24d3;
}

label_0x24d2:
assume false;

label_0x24d3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x24db:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x24de:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x24e6:
t1_605 := RAX;
t2_606 := 164bv64;
RAX := PLUS_64(RAX, t2_606);
CF := bool2bv(LT_64(RAX, t1_605));
OF := AND_1((bool2bv((t1_605[64:63]) == (t2_606[64:63]))), (XOR_1((t1_605[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_605)), t2_606)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x24ec:
mem := STORE_LE_64(mem, PLUS_64(RSP, 184bv64), RAX);

label_0x24f4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x24fc:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_207;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2502:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2507:
t_613 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_208;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_613, 4bv64)), t_613)), 2bv64)), (XOR_64((RSHIFT_64(t_613, 4bv64)), t_613)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_613, 4bv64)), t_613)), 2bv64)), (XOR_64((RSHIFT_64(t_613, 4bv64)), t_613)))))[1:0]));
SF := t_613[64:63];
ZF := bool2bv(0bv64 == t_613);

label_0x250a:
if (bv2bool(ZF)) {
  goto label_0x250d;
}

label_0x250c:
assume false;

label_0x250d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x2515:
origDEST_617 := RAX;
origCOUNT_618 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), CF, LSHIFT_64(origDEST_617, (MINUS_64(64bv64, origCOUNT_618)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_618 == 1bv64)), origDEST_617[64:63], unconstrained_209));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_618 == 0bv64)), AF, unconstrained_210);

label_0x2519:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2520:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2524:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x252c:
origDEST_623 := RCX;
origCOUNT_624 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), CF, LSHIFT_64(origDEST_623, (MINUS_64(64bv64, origCOUNT_624)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_624 == 1bv64)), origDEST_623[64:63], unconstrained_211));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_624 == 0bv64)), AF, unconstrained_212);

label_0x2530:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_213;
SF := unconstrained_214;
AF := unconstrained_215;
PF := unconstrained_216;

label_0x2534:
if (bv2bool(CF)) {
  goto label_0x2537;
}

label_0x2536:
assume false;

label_0x2537:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x253f:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2542:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2544:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2548:
goto label_0x3089;

label_0x254d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x2551:
t_629 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_629[32:31]) == (1bv32[32:31]))), (XOR_1((t_629[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_629)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2553:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x2556:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x255a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x255f:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x2563:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x256b:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x2572:
t_633 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_633)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_633, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)), 2bv32)), (XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)), 2bv32)), (XOR_32((RSHIFT_32(t_633, 4bv32)), t_633)))))[1:0]));
SF := t_633[32:31];
ZF := bool2bv(0bv32 == t_633);

label_0x2574:
if (bv2bool(ZF)) {
  goto label_0x280c;
}

label_0x257a:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x257e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2586:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x258a:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x258e:
t_637 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_217;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_637, 4bv32)), t_637)), 2bv32)), (XOR_32((RSHIFT_32(t_637, 4bv32)), t_637)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_637, 4bv32)), t_637)), 2bv32)), (XOR_32((RSHIFT_32(t_637, 4bv32)), t_637)))))[1:0]));
SF := t_637[32:31];
ZF := bool2bv(0bv32 == t_637);

label_0x2590:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x271d;
}

label_0x2596:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x259b:
origDEST_641 := RAX;
origCOUNT_642 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), CF, RSHIFT_64(origDEST_641, (MINUS_64(64bv64, origCOUNT_642)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_642 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_218));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_642 == 0bv64)), AF, unconstrained_219);

label_0x259f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x25a7:
t1_647 := RCX;
t2_648 := RAX;
RCX := PLUS_64(RCX, t2_648);
CF := bool2bv(LT_64(RCX, t1_647));
OF := AND_1((bool2bv((t1_647[64:63]) == (t2_648[64:63]))), (XOR_1((t1_647[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_647)), t2_648)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x25aa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 192bv64), RCX);

label_0x25b2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x25ba:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_220;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x25c0:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x25c5:
t_655 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_221;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_655, 4bv64)), t_655)), 2bv64)), (XOR_64((RSHIFT_64(t_655, 4bv64)), t_655)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_655, 4bv64)), t_655)), 2bv64)), (XOR_64((RSHIFT_64(t_655, 4bv64)), t_655)))))[1:0]));
SF := t_655[64:63];
ZF := bool2bv(0bv64 == t_655);

label_0x25c8:
if (bv2bool(ZF)) {
  goto label_0x25cb;
}

label_0x25ca:
assume false;

label_0x25cb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x25d3:
origDEST_659 := RAX;
origCOUNT_660 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), CF, LSHIFT_64(origDEST_659, (MINUS_64(64bv64, origCOUNT_660)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_660 == 1bv64)), origDEST_659[64:63], unconstrained_222));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_660 == 0bv64)), AF, unconstrained_223);

label_0x25d7:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x25de:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x25e2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x25ea:
origDEST_665 := RCX;
origCOUNT_666 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), CF, LSHIFT_64(origDEST_665, (MINUS_64(64bv64, origCOUNT_666)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_666 == 1bv64)), origDEST_665[64:63], unconstrained_224));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_666 == 0bv64)), AF, unconstrained_225);

label_0x25ee:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_226;
SF := unconstrained_227;
AF := unconstrained_228;
PF := unconstrained_229;

label_0x25f2:
if (bv2bool(CF)) {
  goto label_0x25f5;
}

label_0x25f4:
assume false;

label_0x25f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 192bv64));

label_0x25fd:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2600:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2602:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2606:
t_671 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_671[32:31]) == (1bv32[32:31]))), (XOR_1((t_671[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_671)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2608:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x260c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2614:
t1_675 := RAX;
t2_676 := 170bv64;
RAX := PLUS_64(RAX, t2_676);
CF := bool2bv(LT_64(RAX, t1_675));
OF := AND_1((bool2bv((t1_675[64:63]) == (t2_676[64:63]))), (XOR_1((t1_675[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_675)), t2_676)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x261a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 416bv64), RAX);

label_0x2622:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2626:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x262b:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x262f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 200bv64), RAX);

label_0x2637:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x263f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_230;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2645:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x264a:
t_683 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_231;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)), 2bv64)), (XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)), 2bv64)), (XOR_64((RSHIFT_64(t_683, 4bv64)), t_683)))))[1:0]));
SF := t_683[64:63];
ZF := bool2bv(0bv64 == t_683);

label_0x264d:
if (bv2bool(ZF)) {
  goto label_0x2650;
}

label_0x264f:
assume false;

label_0x2650:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x2658:
origDEST_687 := RAX;
origCOUNT_688 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), CF, LSHIFT_64(origDEST_687, (MINUS_64(64bv64, origCOUNT_688)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_688 == 1bv64)), origDEST_687[64:63], unconstrained_232));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_688 == 0bv64)), AF, unconstrained_233);

label_0x265c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2663:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2667:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x266f:
origDEST_693 := RCX;
origCOUNT_694 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), CF, LSHIFT_64(origDEST_693, (MINUS_64(64bv64, origCOUNT_694)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_694 == 1bv64)), origDEST_693[64:63], unconstrained_234));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_694 == 0bv64)), AF, unconstrained_235);

label_0x2673:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_236;
SF := unconstrained_237;
AF := unconstrained_238;
PF := unconstrained_239;

label_0x2677:
if (bv2bool(CF)) {
  goto label_0x267a;
}

label_0x2679:
assume false;

label_0x267a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x2682:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 416bv64));

label_0x268a:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x268d:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2690:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2698:
t1_699 := RAX;
t2_700 := 168bv64;
RAX := PLUS_64(RAX, t2_700);
CF := bool2bv(LT_64(RAX, t1_699));
OF := AND_1((bool2bv((t1_699[64:63]) == (t2_700[64:63]))), (XOR_1((t1_699[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_699)), t2_700)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x269e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 424bv64), RAX);

label_0x26a6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x26aa:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x26af:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x26b3:
t1_705 := RAX;
t2_706 := 2bv64;
RAX := PLUS_64(RAX, t2_706);
CF := bool2bv(LT_64(RAX, t1_705));
OF := AND_1((bool2bv((t1_705[64:63]) == (t2_706[64:63]))), (XOR_1((t1_705[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_705)), t2_706)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26b7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 208bv64), RAX);

label_0x26bf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x26c7:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_240;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26cd:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x26d2:
t_713 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_241;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_713, 4bv64)), t_713)), 2bv64)), (XOR_64((RSHIFT_64(t_713, 4bv64)), t_713)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_713, 4bv64)), t_713)), 2bv64)), (XOR_64((RSHIFT_64(t_713, 4bv64)), t_713)))))[1:0]));
SF := t_713[64:63];
ZF := bool2bv(0bv64 == t_713);

label_0x26d5:
if (bv2bool(ZF)) {
  goto label_0x26d8;
}

label_0x26d7:
assume false;

label_0x26d8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x26e0:
origDEST_717 := RAX;
origCOUNT_718 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), CF, LSHIFT_64(origDEST_717, (MINUS_64(64bv64, origCOUNT_718)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_718 == 1bv64)), origDEST_717[64:63], unconstrained_242));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_718 == 0bv64)), AF, unconstrained_243);

label_0x26e4:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x26eb:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x26ef:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x26f7:
origDEST_723 := RCX;
origCOUNT_724 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), CF, LSHIFT_64(origDEST_723, (MINUS_64(64bv64, origCOUNT_724)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_724 == 1bv64)), origDEST_723[64:63], unconstrained_244));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_724 == 0bv64)), AF, unconstrained_245);

label_0x26fb:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_246;
SF := unconstrained_247;
AF := unconstrained_248;
PF := unconstrained_249;

label_0x26ff:
if (bv2bool(CF)) {
  goto label_0x2702;
}

label_0x2701:
assume false;

label_0x2702:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 208bv64));

label_0x270a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 424bv64));

label_0x2712:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2715:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2718:
goto label_0x280c;

label_0x271d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2721:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2729:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x272d:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2731:
t_729 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_250;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_729, 4bv32)), t_729)), 2bv32)), (XOR_32((RSHIFT_32(t_729, 4bv32)), t_729)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_729, 4bv32)), t_729)), 2bv32)), (XOR_32((RSHIFT_32(t_729, 4bv32)), t_729)))))[1:0]));
SF := t_729[32:31];
ZF := bool2bv(0bv32 == t_729);

label_0x2733:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x280c;
}

label_0x2739:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2741:
t1_733 := RAX;
t2_734 := 160bv64;
RAX := PLUS_64(RAX, t2_734);
CF := bool2bv(LT_64(RAX, t1_733));
OF := AND_1((bool2bv((t1_733[64:63]) == (t2_734[64:63]))), (XOR_1((t1_733[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_733)), t2_734)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2747:
mem := STORE_LE_64(mem, PLUS_64(RSP, 216bv64), RAX);

label_0x274f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x2757:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_251;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x275d:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2762:
t_741 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_252;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)), 2bv64)), (XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)), 2bv64)), (XOR_64((RSHIFT_64(t_741, 4bv64)), t_741)))))[1:0]));
SF := t_741[64:63];
ZF := bool2bv(0bv64 == t_741);

label_0x2765:
if (bv2bool(ZF)) {
  goto label_0x2768;
}

label_0x2767:
assume false;

label_0x2768:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x2770:
origDEST_745 := RAX;
origCOUNT_746 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), CF, LSHIFT_64(origDEST_745, (MINUS_64(64bv64, origCOUNT_746)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_746 == 1bv64)), origDEST_745[64:63], unconstrained_253));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_746 == 0bv64)), AF, unconstrained_254);

label_0x2774:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x277b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x277f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x2787:
origDEST_751 := RCX;
origCOUNT_752 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), CF, LSHIFT_64(origDEST_751, (MINUS_64(64bv64, origCOUNT_752)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_752 == 1bv64)), origDEST_751[64:63], unconstrained_255));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_752 == 0bv64)), AF, unconstrained_256);

label_0x278b:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_257;
SF := unconstrained_258;
AF := unconstrained_259;
PF := unconstrained_260;

label_0x278f:
if (bv2bool(CF)) {
  goto label_0x2792;
}

label_0x2791:
assume false;

label_0x2792:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x279a:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x279d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x27a5:
t1_757 := RAX;
t2_758 := 164bv64;
RAX := PLUS_64(RAX, t2_758);
CF := bool2bv(LT_64(RAX, t1_757));
OF := AND_1((bool2bv((t1_757[64:63]) == (t2_758[64:63]))), (XOR_1((t1_757[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_757)), t2_758)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x27ab:
mem := STORE_LE_64(mem, PLUS_64(RSP, 224bv64), RAX);

label_0x27b3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x27bb:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_261;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x27c1:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x27c6:
t_765 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_262;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)), 2bv64)), (XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)), 2bv64)), (XOR_64((RSHIFT_64(t_765, 4bv64)), t_765)))))[1:0]));
SF := t_765[64:63];
ZF := bool2bv(0bv64 == t_765);

label_0x27c9:
if (bv2bool(ZF)) {
  goto label_0x27cc;
}

label_0x27cb:
assume false;

label_0x27cc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x27d4:
origDEST_769 := RAX;
origCOUNT_770 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), CF, LSHIFT_64(origDEST_769, (MINUS_64(64bv64, origCOUNT_770)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_770 == 1bv64)), origDEST_769[64:63], unconstrained_263));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_770 == 0bv64)), AF, unconstrained_264);

label_0x27d8:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x27df:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x27e3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x27eb:
origDEST_775 := RCX;
origCOUNT_776 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), CF, LSHIFT_64(origDEST_775, (MINUS_64(64bv64, origCOUNT_776)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_776 == 1bv64)), origDEST_775[64:63], unconstrained_265));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_776 == 0bv64)), AF, unconstrained_266);

label_0x27ef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_267;
SF := unconstrained_268;
AF := unconstrained_269;
PF := unconstrained_270;

label_0x27f3:
if (bv2bool(CF)) {
  goto label_0x27f6;
}

label_0x27f5:
assume false;

label_0x27f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 224bv64));

label_0x27fe:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2801:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2803:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2807:
goto label_0x3089;

label_0x280c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x2810:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x2814:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[32:0]);

label_0x2818:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x281b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x281f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2824:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x2828:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2830:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x2837:
t_781 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_781)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_781, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)), 2bv32)), (XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)), 2bv32)), (XOR_32((RSHIFT_32(t_781, 4bv32)), t_781)))))[1:0]));
SF := t_781[32:31];
ZF := bool2bv(0bv32 == t_781);

label_0x2839:
if (bv2bool(ZF)) {
  goto label_0x2ad1;
}

label_0x283f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2843:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x284b:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x284f:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2853:
t_785 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_271;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_785, 4bv32)), t_785)), 2bv32)), (XOR_32((RSHIFT_32(t_785, 4bv32)), t_785)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_785, 4bv32)), t_785)), 2bv32)), (XOR_32((RSHIFT_32(t_785, 4bv32)), t_785)))))[1:0]));
SF := t_785[32:31];
ZF := bool2bv(0bv32 == t_785);

label_0x2855:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x29e2;
}

label_0x285b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x2860:
origDEST_789 := RAX;
origCOUNT_790 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), CF, RSHIFT_64(origDEST_789, (MINUS_64(64bv64, origCOUNT_790)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_790 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_272));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_790 == 0bv64)), AF, unconstrained_273);

label_0x2864:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x286c:
t1_795 := RCX;
t2_796 := RAX;
RCX := PLUS_64(RCX, t2_796);
CF := bool2bv(LT_64(RCX, t1_795));
OF := AND_1((bool2bv((t1_795[64:63]) == (t2_796[64:63]))), (XOR_1((t1_795[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_795)), t2_796)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x286f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 232bv64), RCX);

label_0x2877:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x287f:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_274;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2885:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x288a:
t_803 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_275;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_803, 4bv64)), t_803)), 2bv64)), (XOR_64((RSHIFT_64(t_803, 4bv64)), t_803)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_803, 4bv64)), t_803)), 2bv64)), (XOR_64((RSHIFT_64(t_803, 4bv64)), t_803)))))[1:0]));
SF := t_803[64:63];
ZF := bool2bv(0bv64 == t_803);

label_0x288d:
if (bv2bool(ZF)) {
  goto label_0x2890;
}

label_0x288f:
assume false;

label_0x2890:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x2898:
origDEST_807 := RAX;
origCOUNT_808 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), CF, LSHIFT_64(origDEST_807, (MINUS_64(64bv64, origCOUNT_808)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_808 == 1bv64)), origDEST_807[64:63], unconstrained_276));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_808 == 0bv64)), AF, unconstrained_277);

label_0x289c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x28a3:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x28a7:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x28af:
origDEST_813 := RCX;
origCOUNT_814 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), CF, LSHIFT_64(origDEST_813, (MINUS_64(64bv64, origCOUNT_814)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_814 == 1bv64)), origDEST_813[64:63], unconstrained_278));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_814 == 0bv64)), AF, unconstrained_279);

label_0x28b3:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_280;
SF := unconstrained_281;
AF := unconstrained_282;
PF := unconstrained_283;

label_0x28b7:
if (bv2bool(CF)) {
  goto label_0x28ba;
}

label_0x28b9:
assume false;

label_0x28ba:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 232bv64));

label_0x28c2:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x28c5:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x28c7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x28cb:
t_819 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_819[32:31]) == (1bv32[32:31]))), (XOR_1((t_819[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_819)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x28cd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x28d1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x28d9:
t1_823 := RAX;
t2_824 := 170bv64;
RAX := PLUS_64(RAX, t2_824);
CF := bool2bv(LT_64(RAX, t1_823));
OF := AND_1((bool2bv((t1_823[64:63]) == (t2_824[64:63]))), (XOR_1((t1_823[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_823)), t2_824)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x28df:
mem := STORE_LE_64(mem, PLUS_64(RSP, 432bv64), RAX);

label_0x28e7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x28eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x28f0:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x28f4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 240bv64), RAX);

label_0x28fc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2904:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_284;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x290a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x290f:
t_831 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_285;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_831, 4bv64)), t_831)), 2bv64)), (XOR_64((RSHIFT_64(t_831, 4bv64)), t_831)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_831, 4bv64)), t_831)), 2bv64)), (XOR_64((RSHIFT_64(t_831, 4bv64)), t_831)))))[1:0]));
SF := t_831[64:63];
ZF := bool2bv(0bv64 == t_831);

label_0x2912:
if (bv2bool(ZF)) {
  goto label_0x2915;
}

label_0x2914:
assume false;

label_0x2915:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x291d:
origDEST_835 := RAX;
origCOUNT_836 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), CF, LSHIFT_64(origDEST_835, (MINUS_64(64bv64, origCOUNT_836)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_836 == 1bv64)), origDEST_835[64:63], unconstrained_286));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_836 == 0bv64)), AF, unconstrained_287);

label_0x2921:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2928:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x292c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2934:
origDEST_841 := RCX;
origCOUNT_842 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), CF, LSHIFT_64(origDEST_841, (MINUS_64(64bv64, origCOUNT_842)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_842 == 1bv64)), origDEST_841[64:63], unconstrained_288));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_842 == 0bv64)), AF, unconstrained_289);

label_0x2938:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_290;
SF := unconstrained_291;
AF := unconstrained_292;
PF := unconstrained_293;

label_0x293c:
if (bv2bool(CF)) {
  goto label_0x293f;
}

label_0x293e:
assume false;

label_0x293f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 240bv64));

label_0x2947:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 432bv64));

label_0x294f:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2952:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2955:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x295d:
t1_847 := RAX;
t2_848 := 168bv64;
RAX := PLUS_64(RAX, t2_848);
CF := bool2bv(LT_64(RAX, t1_847));
OF := AND_1((bool2bv((t1_847[64:63]) == (t2_848[64:63]))), (XOR_1((t1_847[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_847)), t2_848)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2963:
mem := STORE_LE_64(mem, PLUS_64(RSP, 440bv64), RAX);

label_0x296b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x296f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2974:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2978:
t1_853 := RAX;
t2_854 := 2bv64;
RAX := PLUS_64(RAX, t2_854);
CF := bool2bv(LT_64(RAX, t1_853));
OF := AND_1((bool2bv((t1_853[64:63]) == (t2_854[64:63]))), (XOR_1((t1_853[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_853)), t2_854)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x297c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 248bv64), RAX);

label_0x2984:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x298c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_294;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2992:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2997:
t_861 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_295;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_861, 4bv64)), t_861)), 2bv64)), (XOR_64((RSHIFT_64(t_861, 4bv64)), t_861)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_861, 4bv64)), t_861)), 2bv64)), (XOR_64((RSHIFT_64(t_861, 4bv64)), t_861)))))[1:0]));
SF := t_861[64:63];
ZF := bool2bv(0bv64 == t_861);

label_0x299a:
if (bv2bool(ZF)) {
  goto label_0x299d;
}

label_0x299c:
assume false;

label_0x299d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x29a5:
origDEST_865 := RAX;
origCOUNT_866 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), CF, LSHIFT_64(origDEST_865, (MINUS_64(64bv64, origCOUNT_866)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_866 == 1bv64)), origDEST_865[64:63], unconstrained_296));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_866 == 0bv64)), AF, unconstrained_297);

label_0x29a9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x29b0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x29b4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x29bc:
origDEST_871 := RCX;
origCOUNT_872 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), CF, LSHIFT_64(origDEST_871, (MINUS_64(64bv64, origCOUNT_872)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_872 == 1bv64)), origDEST_871[64:63], unconstrained_298));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_872 == 0bv64)), AF, unconstrained_299);

label_0x29c0:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_300;
SF := unconstrained_301;
AF := unconstrained_302;
PF := unconstrained_303;

label_0x29c4:
if (bv2bool(CF)) {
  goto label_0x29c7;
}

label_0x29c6:
assume false;

label_0x29c7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 248bv64));

label_0x29cf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 440bv64));

label_0x29d7:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x29da:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x29dd:
goto label_0x2ad1;

label_0x29e2:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x29e6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x29ee:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x29f2:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x29f6:
t_877 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_304;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_877, 4bv32)), t_877)), 2bv32)), (XOR_32((RSHIFT_32(t_877, 4bv32)), t_877)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_877, 4bv32)), t_877)), 2bv32)), (XOR_32((RSHIFT_32(t_877, 4bv32)), t_877)))))[1:0]));
SF := t_877[32:31];
ZF := bool2bv(0bv32 == t_877);

label_0x29f8:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2ad1;
}

label_0x29fe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2a06:
t1_881 := RAX;
t2_882 := 160bv64;
RAX := PLUS_64(RAX, t2_882);
CF := bool2bv(LT_64(RAX, t1_881));
OF := AND_1((bool2bv((t1_881[64:63]) == (t2_882[64:63]))), (XOR_1((t1_881[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_881)), t2_882)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a0c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 256bv64), RAX);

label_0x2a14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x2a1c:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_305;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a22:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2a27:
t_889 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_306;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_889, 4bv64)), t_889)), 2bv64)), (XOR_64((RSHIFT_64(t_889, 4bv64)), t_889)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_889, 4bv64)), t_889)), 2bv64)), (XOR_64((RSHIFT_64(t_889, 4bv64)), t_889)))))[1:0]));
SF := t_889[64:63];
ZF := bool2bv(0bv64 == t_889);

label_0x2a2a:
if (bv2bool(ZF)) {
  goto label_0x2a2d;
}

label_0x2a2c:
assume false;

label_0x2a2d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x2a35:
origDEST_893 := RAX;
origCOUNT_894 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), CF, LSHIFT_64(origDEST_893, (MINUS_64(64bv64, origCOUNT_894)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_894 == 1bv64)), origDEST_893[64:63], unconstrained_307));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_894 == 0bv64)), AF, unconstrained_308);

label_0x2a39:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2a40:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2a44:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x2a4c:
origDEST_899 := RCX;
origCOUNT_900 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), CF, LSHIFT_64(origDEST_899, (MINUS_64(64bv64, origCOUNT_900)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_900 == 1bv64)), origDEST_899[64:63], unconstrained_309));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_900 == 0bv64)), AF, unconstrained_310);

label_0x2a50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_311;
SF := unconstrained_312;
AF := unconstrained_313;
PF := unconstrained_314;

label_0x2a54:
if (bv2bool(CF)) {
  goto label_0x2a57;
}

label_0x2a56:
assume false;

label_0x2a57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 256bv64));

label_0x2a5f:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x2a62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2a6a:
t1_905 := RAX;
t2_906 := 164bv64;
RAX := PLUS_64(RAX, t2_906);
CF := bool2bv(LT_64(RAX, t1_905));
OF := AND_1((bool2bv((t1_905[64:63]) == (t2_906[64:63]))), (XOR_1((t1_905[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_905)), t2_906)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a70:
mem := STORE_LE_64(mem, PLUS_64(RSP, 264bv64), RAX);

label_0x2a78:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x2a80:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_315;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2a86:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2a8b:
t_913 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_316;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_913, 4bv64)), t_913)), 2bv64)), (XOR_64((RSHIFT_64(t_913, 4bv64)), t_913)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_913, 4bv64)), t_913)), 2bv64)), (XOR_64((RSHIFT_64(t_913, 4bv64)), t_913)))))[1:0]));
SF := t_913[64:63];
ZF := bool2bv(0bv64 == t_913);

label_0x2a8e:
if (bv2bool(ZF)) {
  goto label_0x2a91;
}

label_0x2a90:
assume false;

label_0x2a91:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x2a99:
origDEST_917 := RAX;
origCOUNT_918 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), CF, LSHIFT_64(origDEST_917, (MINUS_64(64bv64, origCOUNT_918)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_918 == 1bv64)), origDEST_917[64:63], unconstrained_317));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_918 == 0bv64)), AF, unconstrained_318);

label_0x2a9d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2aa4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2aa8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x2ab0:
origDEST_923 := RCX;
origCOUNT_924 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), CF, LSHIFT_64(origDEST_923, (MINUS_64(64bv64, origCOUNT_924)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_924 == 1bv64)), origDEST_923[64:63], unconstrained_319));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_924 == 0bv64)), AF, unconstrained_320);

label_0x2ab4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_321;
SF := unconstrained_322;
AF := unconstrained_323;
PF := unconstrained_324;

label_0x2ab8:
if (bv2bool(CF)) {
  goto label_0x2abb;
}

label_0x2aba:
assume false;

label_0x2abb:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 264bv64));

label_0x2ac3:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2ac6:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2ac8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2acc:
goto label_0x3089;

label_0x2ad1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x2ad5:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x2ad9:
t1_929 := RCX[32:0];
t2_930 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_930));
CF := bool2bv(LT_32((RCX[32:0]), t1_929));
OF := AND_1((bool2bv((t1_929[32:31]) == (t2_930[32:31]))), (XOR_1((t1_929[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_929)), t2_930)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x2adb:
RAX := (0bv32 ++ RCX[32:0]);

label_0x2add:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x2ae0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2ae4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2ae9:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x2aed:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2af5:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x2afc:
t_935 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_935)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_935, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_935, 4bv32)), t_935)), 2bv32)), (XOR_32((RSHIFT_32(t_935, 4bv32)), t_935)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_935, 4bv32)), t_935)), 2bv32)), (XOR_32((RSHIFT_32(t_935, 4bv32)), t_935)))))[1:0]));
SF := t_935[32:31];
ZF := bool2bv(0bv32 == t_935);

label_0x2afe:
if (bv2bool(ZF)) {
  goto label_0x2d96;
}

label_0x2b04:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2b08:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2b10:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x2b14:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2b18:
t_939 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_325;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_939, 4bv32)), t_939)), 2bv32)), (XOR_32((RSHIFT_32(t_939, 4bv32)), t_939)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_939, 4bv32)), t_939)), 2bv32)), (XOR_32((RSHIFT_32(t_939, 4bv32)), t_939)))))[1:0]));
SF := t_939[32:31];
ZF := bool2bv(0bv32 == t_939);

label_0x2b1a:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2ca7;
}

label_0x2b20:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x2b25:
origDEST_943 := RAX;
origCOUNT_944 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), CF, RSHIFT_64(origDEST_943, (MINUS_64(64bv64, origCOUNT_944)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_944 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_326));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_944 == 0bv64)), AF, unconstrained_327);

label_0x2b29:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x2b31:
t1_949 := RCX;
t2_950 := RAX;
RCX := PLUS_64(RCX, t2_950);
CF := bool2bv(LT_64(RCX, t1_949));
OF := AND_1((bool2bv((t1_949[64:63]) == (t2_950[64:63]))), (XOR_1((t1_949[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_949)), t2_950)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x2b34:
mem := STORE_LE_64(mem, PLUS_64(RSP, 272bv64), RCX);

label_0x2b3c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x2b44:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_328;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2b4a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2b4f:
t_957 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_329;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_957, 4bv64)), t_957)), 2bv64)), (XOR_64((RSHIFT_64(t_957, 4bv64)), t_957)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_957, 4bv64)), t_957)), 2bv64)), (XOR_64((RSHIFT_64(t_957, 4bv64)), t_957)))))[1:0]));
SF := t_957[64:63];
ZF := bool2bv(0bv64 == t_957);

label_0x2b52:
if (bv2bool(ZF)) {
  goto label_0x2b55;
}

label_0x2b54:
assume false;

label_0x2b55:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x2b5d:
origDEST_961 := RAX;
origCOUNT_962 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), CF, LSHIFT_64(origDEST_961, (MINUS_64(64bv64, origCOUNT_962)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_962 == 1bv64)), origDEST_961[64:63], unconstrained_330));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_962 == 0bv64)), AF, unconstrained_331);

label_0x2b61:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2b68:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2b6c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x2b74:
origDEST_967 := RCX;
origCOUNT_968 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), CF, LSHIFT_64(origDEST_967, (MINUS_64(64bv64, origCOUNT_968)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_968 == 1bv64)), origDEST_967[64:63], unconstrained_332));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_968 == 0bv64)), AF, unconstrained_333);

label_0x2b78:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_334;
SF := unconstrained_335;
AF := unconstrained_336;
PF := unconstrained_337;

label_0x2b7c:
if (bv2bool(CF)) {
  goto label_0x2b7f;
}

label_0x2b7e:
assume false;

label_0x2b7f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 272bv64));

label_0x2b87:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2b8a:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2b8c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2b90:
t_973 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_973[32:31]) == (1bv32[32:31]))), (XOR_1((t_973[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_973)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2b92:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2b96:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2b9e:
t1_977 := RAX;
t2_978 := 170bv64;
RAX := PLUS_64(RAX, t2_978);
CF := bool2bv(LT_64(RAX, t1_977));
OF := AND_1((bool2bv((t1_977[64:63]) == (t2_978[64:63]))), (XOR_1((t1_977[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_977)), t2_978)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ba4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 448bv64), RAX);

label_0x2bac:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2bb0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2bb5:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2bb9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 280bv64), RAX);

label_0x2bc1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2bc9:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_338;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2bcf:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2bd4:
t_985 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_339;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_985, 4bv64)), t_985)), 2bv64)), (XOR_64((RSHIFT_64(t_985, 4bv64)), t_985)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_985, 4bv64)), t_985)), 2bv64)), (XOR_64((RSHIFT_64(t_985, 4bv64)), t_985)))))[1:0]));
SF := t_985[64:63];
ZF := bool2bv(0bv64 == t_985);

label_0x2bd7:
if (bv2bool(ZF)) {
  goto label_0x2bda;
}

label_0x2bd9:
assume false;

label_0x2bda:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2be2:
origDEST_989 := RAX;
origCOUNT_990 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), CF, LSHIFT_64(origDEST_989, (MINUS_64(64bv64, origCOUNT_990)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_990 == 1bv64)), origDEST_989[64:63], unconstrained_340));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_990 == 0bv64)), AF, unconstrained_341);

label_0x2be6:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2bed:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2bf1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2bf9:
origDEST_995 := RCX;
origCOUNT_996 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), CF, LSHIFT_64(origDEST_995, (MINUS_64(64bv64, origCOUNT_996)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_996 == 1bv64)), origDEST_995[64:63], unconstrained_342));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_996 == 0bv64)), AF, unconstrained_343);

label_0x2bfd:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_344;
SF := unconstrained_345;
AF := unconstrained_346;
PF := unconstrained_347;

label_0x2c01:
if (bv2bool(CF)) {
  goto label_0x2c04;
}

label_0x2c03:
assume false;

label_0x2c04:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 280bv64));

label_0x2c0c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 448bv64));

label_0x2c14:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2c17:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2c1a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2c22:
t1_1001 := RAX;
t2_1002 := 168bv64;
RAX := PLUS_64(RAX, t2_1002);
CF := bool2bv(LT_64(RAX, t1_1001));
OF := AND_1((bool2bv((t1_1001[64:63]) == (t2_1002[64:63]))), (XOR_1((t1_1001[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1001)), t2_1002)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2c28:
mem := STORE_LE_64(mem, PLUS_64(RSP, 456bv64), RAX);

label_0x2c30:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2c34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2c39:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2c3d:
t1_1007 := RAX;
t2_1008 := 2bv64;
RAX := PLUS_64(RAX, t2_1008);
CF := bool2bv(LT_64(RAX, t1_1007));
OF := AND_1((bool2bv((t1_1007[64:63]) == (t2_1008[64:63]))), (XOR_1((t1_1007[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1007)), t2_1008)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2c41:
mem := STORE_LE_64(mem, PLUS_64(RSP, 288bv64), RAX);

label_0x2c49:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x2c51:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_348;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2c57:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2c5c:
t_1015 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_349;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1015, 4bv64)), t_1015)), 2bv64)), (XOR_64((RSHIFT_64(t_1015, 4bv64)), t_1015)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1015, 4bv64)), t_1015)), 2bv64)), (XOR_64((RSHIFT_64(t_1015, 4bv64)), t_1015)))))[1:0]));
SF := t_1015[64:63];
ZF := bool2bv(0bv64 == t_1015);

label_0x2c5f:
if (bv2bool(ZF)) {
  goto label_0x2c62;
}

label_0x2c61:
assume false;

label_0x2c62:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x2c6a:
origDEST_1019 := RAX;
origCOUNT_1020 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), CF, LSHIFT_64(origDEST_1019, (MINUS_64(64bv64, origCOUNT_1020)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 1bv64)), origDEST_1019[64:63], unconstrained_350));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1020 == 0bv64)), AF, unconstrained_351);

label_0x2c6e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2c75:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2c79:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x2c81:
origDEST_1025 := RCX;
origCOUNT_1026 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), CF, LSHIFT_64(origDEST_1025, (MINUS_64(64bv64, origCOUNT_1026)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 1bv64)), origDEST_1025[64:63], unconstrained_352));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1026 == 0bv64)), AF, unconstrained_353);

label_0x2c85:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_354;
SF := unconstrained_355;
AF := unconstrained_356;
PF := unconstrained_357;

label_0x2c89:
if (bv2bool(CF)) {
  goto label_0x2c8c;
}

label_0x2c8b:
assume false;

label_0x2c8c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 288bv64));

label_0x2c94:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 456bv64));

label_0x2c9c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2c9f:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2ca2:
goto label_0x2d96;

label_0x2ca7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2cab:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2cb3:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x2cb7:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2cbb:
t_1031 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_358;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1031, 4bv32)), t_1031)), 2bv32)), (XOR_32((RSHIFT_32(t_1031, 4bv32)), t_1031)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1031, 4bv32)), t_1031)), 2bv32)), (XOR_32((RSHIFT_32(t_1031, 4bv32)), t_1031)))))[1:0]));
SF := t_1031[32:31];
ZF := bool2bv(0bv32 == t_1031);

label_0x2cbd:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x2d96;
}

label_0x2cc3:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2ccb:
t1_1035 := RAX;
t2_1036 := 160bv64;
RAX := PLUS_64(RAX, t2_1036);
CF := bool2bv(LT_64(RAX, t1_1035));
OF := AND_1((bool2bv((t1_1035[64:63]) == (t2_1036[64:63]))), (XOR_1((t1_1035[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1035)), t2_1036)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2cd1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 296bv64), RAX);

label_0x2cd9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x2ce1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_359;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ce7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2cec:
t_1043 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_360;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1043, 4bv64)), t_1043)), 2bv64)), (XOR_64((RSHIFT_64(t_1043, 4bv64)), t_1043)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1043, 4bv64)), t_1043)), 2bv64)), (XOR_64((RSHIFT_64(t_1043, 4bv64)), t_1043)))))[1:0]));
SF := t_1043[64:63];
ZF := bool2bv(0bv64 == t_1043);

label_0x2cef:
if (bv2bool(ZF)) {
  goto label_0x2cf2;
}

label_0x2cf1:
assume false;

label_0x2cf2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x2cfa:
origDEST_1047 := RAX;
origCOUNT_1048 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), CF, LSHIFT_64(origDEST_1047, (MINUS_64(64bv64, origCOUNT_1048)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 1bv64)), origDEST_1047[64:63], unconstrained_361));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1048 == 0bv64)), AF, unconstrained_362);

label_0x2cfe:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2d05:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2d09:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x2d11:
origDEST_1053 := RCX;
origCOUNT_1054 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), CF, LSHIFT_64(origDEST_1053, (MINUS_64(64bv64, origCOUNT_1054)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 1bv64)), origDEST_1053[64:63], unconstrained_363));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1054 == 0bv64)), AF, unconstrained_364);

label_0x2d15:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_365;
SF := unconstrained_366;
AF := unconstrained_367;
PF := unconstrained_368;

label_0x2d19:
if (bv2bool(CF)) {
  goto label_0x2d1c;
}

label_0x2d1b:
assume false;

label_0x2d1c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 296bv64));

label_0x2d24:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x2d27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2d2f:
t1_1059 := RAX;
t2_1060 := 164bv64;
RAX := PLUS_64(RAX, t2_1060);
CF := bool2bv(LT_64(RAX, t1_1059));
OF := AND_1((bool2bv((t1_1059[64:63]) == (t2_1060[64:63]))), (XOR_1((t1_1059[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1059)), t2_1060)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2d35:
mem := STORE_LE_64(mem, PLUS_64(RSP, 304bv64), RAX);

label_0x2d3d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x2d45:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_369;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2d4b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2d50:
t_1067 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_370;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1067, 4bv64)), t_1067)), 2bv64)), (XOR_64((RSHIFT_64(t_1067, 4bv64)), t_1067)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1067, 4bv64)), t_1067)), 2bv64)), (XOR_64((RSHIFT_64(t_1067, 4bv64)), t_1067)))))[1:0]));
SF := t_1067[64:63];
ZF := bool2bv(0bv64 == t_1067);

label_0x2d53:
if (bv2bool(ZF)) {
  goto label_0x2d56;
}

label_0x2d55:
assume false;

label_0x2d56:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x2d5e:
origDEST_1071 := RAX;
origCOUNT_1072 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), CF, LSHIFT_64(origDEST_1071, (MINUS_64(64bv64, origCOUNT_1072)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 1bv64)), origDEST_1071[64:63], unconstrained_371));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1072 == 0bv64)), AF, unconstrained_372);

label_0x2d62:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2d69:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2d6d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x2d75:
origDEST_1077 := RCX;
origCOUNT_1078 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), CF, LSHIFT_64(origDEST_1077, (MINUS_64(64bv64, origCOUNT_1078)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 1bv64)), origDEST_1077[64:63], unconstrained_373));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1078 == 0bv64)), AF, unconstrained_374);

label_0x2d79:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_375;
SF := unconstrained_376;
AF := unconstrained_377;
PF := unconstrained_378;

label_0x2d7d:
if (bv2bool(CF)) {
  goto label_0x2d80;
}

label_0x2d7f:
assume false;

label_0x2d80:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 304bv64));

label_0x2d88:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2d8b:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2d8d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2d91:
goto label_0x3089;

label_0x2d96:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 16bv64)));

label_0x2d9a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x2d9e:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 1bv64)[32:0]);

label_0x2da2:
mem := STORE_LE_32(mem, RSP, RAX[32:0]);

label_0x2da5:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2da9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2dae:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))));

label_0x2db2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2dba:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, 170bv64))));

label_0x2dc1:
t_1083 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_1083)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1083, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1083, 4bv32)), t_1083)), 2bv32)), (XOR_32((RSHIFT_32(t_1083, 4bv32)), t_1083)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1083, 4bv32)), t_1083)), 2bv32)), (XOR_32((RSHIFT_32(t_1083, 4bv32)), t_1083)))))[1:0]));
SF := t_1083[32:31];
ZF := bool2bv(0bv32 == t_1083);

label_0x2dc3:
if (bv2bool(ZF)) {
  goto label_0x3058;
}

label_0x2dc9:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2dcd:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2dd5:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x2dd9:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2ddd:
t_1087 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_379;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1087, 4bv32)), t_1087)), 2bv32)), (XOR_32((RSHIFT_32(t_1087, 4bv32)), t_1087)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1087, 4bv32)), t_1087)), 2bv32)), (XOR_32((RSHIFT_32(t_1087, 4bv32)), t_1087)))))[1:0]));
SF := t_1087[32:31];
ZF := bool2bv(0bv32 == t_1087);

label_0x2ddf:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2f6c;
}

label_0x2de5:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)))));

label_0x2dea:
origDEST_1091 := RAX;
origCOUNT_1092 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), CF, RSHIFT_64(origDEST_1091, (MINUS_64(64bv64, origCOUNT_1092)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_380));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1092 == 0bv64)), AF, unconstrained_381);

label_0x2dee:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 520bv64));

label_0x2df6:
t1_1097 := RCX;
t2_1098 := RAX;
RCX := PLUS_64(RCX, t2_1098);
CF := bool2bv(LT_64(RCX, t1_1097));
OF := AND_1((bool2bv((t1_1097[64:63]) == (t2_1098[64:63]))), (XOR_1((t1_1097[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_1097)), t2_1098)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x2df9:
mem := STORE_LE_64(mem, PLUS_64(RSP, 312bv64), RCX);

label_0x2e01:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x2e09:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_382;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e0f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2e14:
t_1105 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_383;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1105, 4bv64)), t_1105)), 2bv64)), (XOR_64((RSHIFT_64(t_1105, 4bv64)), t_1105)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1105, 4bv64)), t_1105)), 2bv64)), (XOR_64((RSHIFT_64(t_1105, 4bv64)), t_1105)))))[1:0]));
SF := t_1105[64:63];
ZF := bool2bv(0bv64 == t_1105);

label_0x2e17:
if (bv2bool(ZF)) {
  goto label_0x2e1a;
}

label_0x2e19:
assume false;

label_0x2e1a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x2e22:
origDEST_1109 := RAX;
origCOUNT_1110 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), CF, LSHIFT_64(origDEST_1109, (MINUS_64(64bv64, origCOUNT_1110)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 1bv64)), origDEST_1109[64:63], unconstrained_384));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1110 == 0bv64)), AF, unconstrained_385);

label_0x2e26:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2e2d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2e31:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x2e39:
origDEST_1115 := RCX;
origCOUNT_1116 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), CF, LSHIFT_64(origDEST_1115, (MINUS_64(64bv64, origCOUNT_1116)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 1bv64)), origDEST_1115[64:63], unconstrained_386));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1116 == 0bv64)), AF, unconstrained_387);

label_0x2e3d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_388;
SF := unconstrained_389;
AF := unconstrained_390;
PF := unconstrained_391;

label_0x2e41:
if (bv2bool(CF)) {
  goto label_0x2e44;
}

label_0x2e43:
assume false;

label_0x2e44:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 312bv64));

label_0x2e4c:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x2e4f:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x2e51:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2e55:
t_1121 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_1121[32:31]) == (1bv32[32:31]))), (XOR_1((t_1121[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1121)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2e57:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2e5b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2e63:
t1_1125 := RAX;
t2_1126 := 170bv64;
RAX := PLUS_64(RAX, t2_1126);
CF := bool2bv(LT_64(RAX, t1_1125));
OF := AND_1((bool2bv((t1_1125[64:63]) == (t2_1126[64:63]))), (XOR_1((t1_1125[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1125)), t2_1126)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e69:
mem := STORE_LE_64(mem, PLUS_64(RSP, 464bv64), RAX);

label_0x2e71:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2e75:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2e7a:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2e7e:
mem := STORE_LE_64(mem, PLUS_64(RSP, 320bv64), RAX);

label_0x2e86:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x2e8e:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_392;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2e94:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2e99:
t_1133 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_393;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1133, 4bv64)), t_1133)), 2bv64)), (XOR_64((RSHIFT_64(t_1133, 4bv64)), t_1133)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1133, 4bv64)), t_1133)), 2bv64)), (XOR_64((RSHIFT_64(t_1133, 4bv64)), t_1133)))))[1:0]));
SF := t_1133[64:63];
ZF := bool2bv(0bv64 == t_1133);

label_0x2e9c:
if (bv2bool(ZF)) {
  goto label_0x2e9f;
}

label_0x2e9e:
assume false;

label_0x2e9f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x2ea7:
origDEST_1137 := RAX;
origCOUNT_1138 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), CF, LSHIFT_64(origDEST_1137, (MINUS_64(64bv64, origCOUNT_1138)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 1bv64)), origDEST_1137[64:63], unconstrained_394));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1138 == 0bv64)), AF, unconstrained_395);

label_0x2eab:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2eb2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2eb6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x2ebe:
origDEST_1143 := RCX;
origCOUNT_1144 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), CF, LSHIFT_64(origDEST_1143, (MINUS_64(64bv64, origCOUNT_1144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 1bv64)), origDEST_1143[64:63], unconstrained_396));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1144 == 0bv64)), AF, unconstrained_397);

label_0x2ec2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_398;
SF := unconstrained_399;
AF := unconstrained_400;
PF := unconstrained_401;

label_0x2ec6:
if (bv2bool(CF)) {
  goto label_0x2ec9;
}

label_0x2ec8:
assume false;

label_0x2ec9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 320bv64));

label_0x2ed1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 464bv64));

label_0x2ed9:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2edc:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2edf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2ee7:
t1_1149 := RAX;
t2_1150 := 168bv64;
RAX := PLUS_64(RAX, t2_1150);
CF := bool2bv(LT_64(RAX, t1_1149));
OF := AND_1((bool2bv((t1_1149[64:63]) == (t2_1150[64:63]))), (XOR_1((t1_1149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1149)), t2_1150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2eed:
mem := STORE_LE_64(mem, PLUS_64(RSP, 472bv64), RAX);

label_0x2ef5:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2ef9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 8bv64));

label_0x2efe:
RAX := PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))[64:0];

label_0x2f02:
t1_1155 := RAX;
t2_1156 := 2bv64;
RAX := PLUS_64(RAX, t2_1156);
CF := bool2bv(LT_64(RAX, t1_1155));
OF := AND_1((bool2bv((t1_1155[64:63]) == (t2_1156[64:63]))), (XOR_1((t1_1155[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1155)), t2_1156)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f06:
mem := STORE_LE_64(mem, PLUS_64(RSP, 328bv64), RAX);

label_0x2f0e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x2f16:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_402;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f1c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2f21:
t_1163 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_403;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1163, 4bv64)), t_1163)), 2bv64)), (XOR_64((RSHIFT_64(t_1163, 4bv64)), t_1163)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1163, 4bv64)), t_1163)), 2bv64)), (XOR_64((RSHIFT_64(t_1163, 4bv64)), t_1163)))))[1:0]));
SF := t_1163[64:63];
ZF := bool2bv(0bv64 == t_1163);

label_0x2f24:
if (bv2bool(ZF)) {
  goto label_0x2f27;
}

label_0x2f26:
assume false;

label_0x2f27:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x2f2f:
origDEST_1167 := RAX;
origCOUNT_1168 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), CF, LSHIFT_64(origDEST_1167, (MINUS_64(64bv64, origCOUNT_1168)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 1bv64)), origDEST_1167[64:63], unconstrained_404));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1168 == 0bv64)), AF, unconstrained_405);

label_0x2f33:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2f3a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2f3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x2f46:
origDEST_1173 := RCX;
origCOUNT_1174 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), CF, LSHIFT_64(origDEST_1173, (MINUS_64(64bv64, origCOUNT_1174)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 1bv64)), origDEST_1173[64:63], unconstrained_406));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1174 == 0bv64)), AF, unconstrained_407);

label_0x2f4a:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_408;
SF := unconstrained_409;
AF := unconstrained_410;
PF := unconstrained_411;

label_0x2f4e:
if (bv2bool(CF)) {
  goto label_0x2f51;
}

label_0x2f50:
assume false;

label_0x2f51:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 328bv64));

label_0x2f59:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 472bv64));

label_0x2f61:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, RCX)));

label_0x2f64:
mem := STORE_LE_16(mem, RAX, RCX[32:0][16:0]);

label_0x2f67:
goto label_0x3058;

label_0x2f6c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, RSP)[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, RSP)) ,(0bv32 ++ LOAD_LE_32(mem, RSP))));

label_0x2f70:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2f78:
RCX := LOAD_LE_64(mem, PLUS_64(RCX, 120bv64));

label_0x2f7c:
RAX := (0bv32 ++ (ITE_32(bv2bool(LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))[16:15]) ,(1bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))) ,(0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))))));

label_0x2f80:
t_1179 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_412;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1179, 4bv32)), t_1179)), 2bv32)), (XOR_32((RSHIFT_32(t_1179, 4bv32)), t_1179)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1179, 4bv32)), t_1179)), 2bv32)), (XOR_32((RSHIFT_32(t_1179, 4bv32)), t_1179)))))[1:0]));
SF := t_1179[32:31];
ZF := bool2bv(0bv32 == t_1179);

label_0x2f82:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x3058;
}

label_0x2f88:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2f90:
t1_1183 := RAX;
t2_1184 := 160bv64;
RAX := PLUS_64(RAX, t2_1184);
CF := bool2bv(LT_64(RAX, t1_1183));
OF := AND_1((bool2bv((t1_1183[64:63]) == (t2_1184[64:63]))), (XOR_1((t1_1183[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1183)), t2_1184)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2f96:
mem := STORE_LE_64(mem, PLUS_64(RSP, 336bv64), RAX);

label_0x2f9e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x2fa6:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_413;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2fac:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x2fb1:
t_1191 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_414;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1191, 4bv64)), t_1191)), 2bv64)), (XOR_64((RSHIFT_64(t_1191, 4bv64)), t_1191)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1191, 4bv64)), t_1191)), 2bv64)), (XOR_64((RSHIFT_64(t_1191, 4bv64)), t_1191)))))[1:0]));
SF := t_1191[64:63];
ZF := bool2bv(0bv64 == t_1191);

label_0x2fb4:
if (bv2bool(ZF)) {
  goto label_0x2fb7;
}

label_0x2fb6:
assume false;

label_0x2fb7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x2fbf:
origDEST_1195 := RAX;
origCOUNT_1196 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), CF, LSHIFT_64(origDEST_1195, (MINUS_64(64bv64, origCOUNT_1196)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 1bv64)), origDEST_1195[64:63], unconstrained_415));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1196 == 0bv64)), AF, unconstrained_416);

label_0x2fc3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x2fca:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x2fce:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x2fd6:
origDEST_1201 := RCX;
origCOUNT_1202 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), CF, LSHIFT_64(origDEST_1201, (MINUS_64(64bv64, origCOUNT_1202)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 1bv64)), origDEST_1201[64:63], unconstrained_417));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1202 == 0bv64)), AF, unconstrained_418);

label_0x2fda:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_419;
SF := unconstrained_420;
AF := unconstrained_421;
PF := unconstrained_422;

label_0x2fde:
if (bv2bool(CF)) {
  goto label_0x2fe1;
}

label_0x2fe0:
assume false;

label_0x2fe1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 336bv64));

label_0x2fe9:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x2fec:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x2ff4:
t1_1207 := RAX;
t2_1208 := 164bv64;
RAX := PLUS_64(RAX, t2_1208);
CF := bool2bv(LT_64(RAX, t1_1207));
OF := AND_1((bool2bv((t1_1207[64:63]) == (t2_1208[64:63]))), (XOR_1((t1_1207[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_1207)), t2_1208)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x2ffa:
mem := STORE_LE_64(mem, PLUS_64(RSP, 344bv64), RAX);

label_0x3002:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x300a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_423;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3010:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3015:
t_1215 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_424;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1215, 4bv64)), t_1215)), 2bv64)), (XOR_64((RSHIFT_64(t_1215, 4bv64)), t_1215)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_1215, 4bv64)), t_1215)), 2bv64)), (XOR_64((RSHIFT_64(t_1215, 4bv64)), t_1215)))))[1:0]));
SF := t_1215[64:63];
ZF := bool2bv(0bv64 == t_1215);

label_0x3018:
if (bv2bool(ZF)) {
  goto label_0x301b;
}

label_0x301a:
assume false;

label_0x301b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x3023:
origDEST_1219 := RAX;
origCOUNT_1220 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), CF, LSHIFT_64(origDEST_1219, (MINUS_64(64bv64, origCOUNT_1220)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 1bv64)), origDEST_1219[64:63], unconstrained_425));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1220 == 0bv64)), AF, unconstrained_426);

label_0x3027:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x302e:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3032:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x303a:
origDEST_1225 := RCX;
origCOUNT_1226 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), CF, LSHIFT_64(origDEST_1225, (MINUS_64(64bv64, origCOUNT_1226)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 1bv64)), origDEST_1225[64:63], unconstrained_427));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_1226 == 0bv64)), AF, unconstrained_428);

label_0x303e:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_429;
SF := unconstrained_430;
AF := unconstrained_431;
PF := unconstrained_432;

label_0x3042:
if (bv2bool(CF)) {
  goto label_0x3045;
}

label_0x3044:
assume false;

label_0x3045:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 344bv64));

label_0x304d:
RCX := (0bv32 ++ LOAD_LE_32(mem, RSP));

label_0x3050:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3052:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3056:
goto label_0x3089;

label_0x3058:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x3060:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 152bv64)));

label_0x3066:
t_1231 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_1231)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_1231, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1231, 4bv32)), t_1231)), 2bv32)), (XOR_32((RSHIFT_32(t_1231, 4bv32)), t_1231)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_1231, 4bv32)), t_1231)), 2bv32)), (XOR_32((RSHIFT_32(t_1231, 4bv32)), t_1231)))))[1:0]));
SF := t_1231[32:31];
ZF := bool2bv(0bv32 == t_1231);

label_0x306a:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x3080;
}

label_0x306c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 496bv64));

label_0x3074:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 152bv64)));

label_0x307a:
t_1235 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_1235, 1bv32)), (XOR_32(t_1235, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_1235)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x307c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3080:
goto label_0x1ac0;

label_0x3085:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3089:
t1_1239 := RSP;
t2_1240 := 488bv64;
RSP := PLUS_64(RSP, t2_1240);
CF := bool2bv(LT_64(RSP, t1_1239));
OF := AND_1((bool2bv((t1_1239[64:63]) == (t2_1240[64:63]))), (XOR_1((t1_1239[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_1239)), t2_1240)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3090:

ra_1245 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_1020,origCOUNT_1026,origCOUNT_1048,origCOUNT_1054,origCOUNT_106,origCOUNT_1072,origCOUNT_1078,origCOUNT_1092,origCOUNT_1110,origCOUNT_1116,origCOUNT_112,origCOUNT_1138,origCOUNT_1144,origCOUNT_1168,origCOUNT_1174,origCOUNT_1196,origCOUNT_1202,origCOUNT_1220,origCOUNT_1226,origCOUNT_134,origCOUNT_140,origCOUNT_158,origCOUNT_164,origCOUNT_182,origCOUNT_200,origCOUNT_206,origCOUNT_228,origCOUNT_234,origCOUNT_258,origCOUNT_264,origCOUNT_286,origCOUNT_292,origCOUNT_30,origCOUNT_310,origCOUNT_316,origCOUNT_338,origCOUNT_356,origCOUNT_362,origCOUNT_384,origCOUNT_390,origCOUNT_414,origCOUNT_420,origCOUNT_442,origCOUNT_448,origCOUNT_466,origCOUNT_472,origCOUNT_48,origCOUNT_490,origCOUNT_508,origCOUNT_514,origCOUNT_536,origCOUNT_54,origCOUNT_542,origCOUNT_566,origCOUNT_572,origCOUNT_594,origCOUNT_600,origCOUNT_618,origCOUNT_624,origCOUNT_642,origCOUNT_660,origCOUNT_666,origCOUNT_688,origCOUNT_694,origCOUNT_718,origCOUNT_724,origCOUNT_746,origCOUNT_752,origCOUNT_76,origCOUNT_770,origCOUNT_776,origCOUNT_790,origCOUNT_808,origCOUNT_814,origCOUNT_82,origCOUNT_836,origCOUNT_842,origCOUNT_866,origCOUNT_872,origCOUNT_894,origCOUNT_900,origCOUNT_918,origCOUNT_924,origCOUNT_944,origCOUNT_962,origCOUNT_968,origCOUNT_990,origCOUNT_996,origDEST_1019,origDEST_1025,origDEST_1047,origDEST_105,origDEST_1053,origDEST_1071,origDEST_1077,origDEST_1091,origDEST_1109,origDEST_111,origDEST_1115,origDEST_1137,origDEST_1143,origDEST_1167,origDEST_1173,origDEST_1195,origDEST_1201,origDEST_1219,origDEST_1225,origDEST_133,origDEST_139,origDEST_157,origDEST_163,origDEST_181,origDEST_199,origDEST_205,origDEST_227,origDEST_233,origDEST_257,origDEST_263,origDEST_285,origDEST_29,origDEST_291,origDEST_309,origDEST_315,origDEST_337,origDEST_355,origDEST_361,origDEST_383,origDEST_389,origDEST_413,origDEST_419,origDEST_441,origDEST_447,origDEST_465,origDEST_47,origDEST_471,origDEST_489,origDEST_507,origDEST_513,origDEST_53,origDEST_535,origDEST_541,origDEST_565,origDEST_571,origDEST_593,origDEST_599,origDEST_617,origDEST_623,origDEST_641,origDEST_659,origDEST_665,origDEST_687,origDEST_693,origDEST_717,origDEST_723,origDEST_745,origDEST_75,origDEST_751,origDEST_769,origDEST_775,origDEST_789,origDEST_807,origDEST_81,origDEST_813,origDEST_835,origDEST_841,origDEST_865,origDEST_871,origDEST_893,origDEST_899,origDEST_917,origDEST_923,origDEST_943,origDEST_961,origDEST_967,origDEST_989,origDEST_995,ra_1245,t1_1001,t1_1007,t1_1035,t1_1059,t1_1097,t1_1125,t1_1149,t1_1155,t1_1183,t1_1207,t1_121,t1_1239,t1_145,t1_187,t1_215,t1_239,t1_245,t1_273,t1_297,t1_343,t1_35,t1_371,t1_395,t1_401,t1_429,t1_453,t1_495,t1_523,t1_547,t1_553,t1_581,t1_605,t1_63,t1_647,t1_675,t1_699,t1_705,t1_733,t1_757,t1_795,t1_823,t1_847,t1_853,t1_87,t1_881,t1_905,t1_929,t1_93,t1_949,t1_977,t2_1002,t2_1008,t2_1036,t2_1060,t2_1098,t2_1126,t2_1150,t2_1156,t2_1184,t2_1208,t2_122,t2_1240,t2_146,t2_188,t2_216,t2_240,t2_246,t2_274,t2_298,t2_344,t2_36,t2_372,t2_396,t2_402,t2_430,t2_454,t2_496,t2_524,t2_548,t2_554,t2_582,t2_606,t2_64,t2_648,t2_676,t2_700,t2_706,t2_734,t2_758,t2_796,t2_824,t2_848,t2_854,t2_88,t2_882,t2_906,t2_930,t2_94,t2_950,t2_978,t_1,t_101,t_1015,t_1031,t_1043,t_1067,t_1083,t_1087,t_1105,t_1121,t_1133,t_1163,t_117,t_1179,t_1191,t_1215,t_1231,t_1235,t_129,t_13,t_153,t_169,t_17,t_173,t_177,t_195,t_21,t_211,t_223,t_25,t_253,t_269,t_281,t_305,t_321,t_325,t_329,t_333,t_351,t_367,t_379,t_409,t_425,t_43,t_437,t_461,t_477,t_481,t_485,t_5,t_503,t_519,t_531,t_561,t_577,t_589,t_59,t_613,t_629,t_633,t_637,t_655,t_671,t_683,t_71,t_713,t_729,t_741,t_765,t_781,t_785,t_803,t_819,t_831,t_861,t_877,t_889,t_9,t_913,t_935,t_939,t_957,t_973,t_985;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_100: bv1;
const unconstrained_101: bv1;
const unconstrained_102: bv1;
const unconstrained_103: bv1;
const unconstrained_104: bv1;
const unconstrained_105: bv1;
const unconstrained_106: bv1;
const unconstrained_107: bv1;
const unconstrained_108: bv1;
const unconstrained_109: bv1;
const unconstrained_11: bv1;
const unconstrained_110: bv1;
const unconstrained_111: bv1;
const unconstrained_112: bv1;
const unconstrained_113: bv1;
const unconstrained_114: bv1;
const unconstrained_115: bv1;
const unconstrained_116: bv1;
const unconstrained_117: bv1;
const unconstrained_118: bv1;
const unconstrained_119: bv1;
const unconstrained_12: bv1;
const unconstrained_120: bv1;
const unconstrained_121: bv1;
const unconstrained_122: bv1;
const unconstrained_123: bv1;
const unconstrained_124: bv1;
const unconstrained_125: bv1;
const unconstrained_126: bv1;
const unconstrained_127: bv1;
const unconstrained_128: bv1;
const unconstrained_129: bv1;
const unconstrained_13: bv1;
const unconstrained_130: bv1;
const unconstrained_131: bv1;
const unconstrained_132: bv1;
const unconstrained_133: bv1;
const unconstrained_134: bv1;
const unconstrained_135: bv1;
const unconstrained_136: bv1;
const unconstrained_137: bv1;
const unconstrained_138: bv1;
const unconstrained_139: bv1;
const unconstrained_14: bv1;
const unconstrained_140: bv1;
const unconstrained_141: bv1;
const unconstrained_142: bv1;
const unconstrained_143: bv1;
const unconstrained_144: bv1;
const unconstrained_145: bv1;
const unconstrained_146: bv1;
const unconstrained_147: bv1;
const unconstrained_148: bv1;
const unconstrained_149: bv1;
const unconstrained_15: bv1;
const unconstrained_150: bv1;
const unconstrained_151: bv1;
const unconstrained_152: bv1;
const unconstrained_153: bv1;
const unconstrained_154: bv1;
const unconstrained_155: bv1;
const unconstrained_156: bv1;
const unconstrained_157: bv1;
const unconstrained_158: bv1;
const unconstrained_159: bv1;
const unconstrained_16: bv1;
const unconstrained_160: bv1;
const unconstrained_161: bv1;
const unconstrained_162: bv1;
const unconstrained_163: bv1;
const unconstrained_164: bv1;
const unconstrained_165: bv1;
const unconstrained_166: bv1;
const unconstrained_167: bv1;
const unconstrained_168: bv1;
const unconstrained_169: bv1;
const unconstrained_17: bv1;
const unconstrained_170: bv1;
const unconstrained_171: bv1;
const unconstrained_172: bv1;
const unconstrained_173: bv1;
const unconstrained_174: bv1;
const unconstrained_175: bv1;
const unconstrained_176: bv1;
const unconstrained_177: bv1;
const unconstrained_178: bv1;
const unconstrained_179: bv1;
const unconstrained_18: bv1;
const unconstrained_180: bv1;
const unconstrained_181: bv1;
const unconstrained_182: bv1;
const unconstrained_183: bv1;
const unconstrained_184: bv1;
const unconstrained_185: bv1;
const unconstrained_186: bv1;
const unconstrained_187: bv1;
const unconstrained_188: bv1;
const unconstrained_189: bv1;
const unconstrained_19: bv1;
const unconstrained_190: bv1;
const unconstrained_191: bv1;
const unconstrained_192: bv1;
const unconstrained_193: bv1;
const unconstrained_194: bv1;
const unconstrained_195: bv1;
const unconstrained_196: bv1;
const unconstrained_197: bv1;
const unconstrained_198: bv1;
const unconstrained_199: bv1;
const unconstrained_2: bv1;
const unconstrained_20: bv1;
const unconstrained_200: bv1;
const unconstrained_201: bv1;
const unconstrained_202: bv1;
const unconstrained_203: bv1;
const unconstrained_204: bv1;
const unconstrained_205: bv1;
const unconstrained_206: bv1;
const unconstrained_207: bv1;
const unconstrained_208: bv1;
const unconstrained_209: bv1;
const unconstrained_21: bv1;
const unconstrained_210: bv1;
const unconstrained_211: bv1;
const unconstrained_212: bv1;
const unconstrained_213: bv1;
const unconstrained_214: bv1;
const unconstrained_215: bv1;
const unconstrained_216: bv1;
const unconstrained_217: bv1;
const unconstrained_218: bv1;
const unconstrained_219: bv1;
const unconstrained_22: bv1;
const unconstrained_220: bv1;
const unconstrained_221: bv1;
const unconstrained_222: bv1;
const unconstrained_223: bv1;
const unconstrained_224: bv1;
const unconstrained_225: bv1;
const unconstrained_226: bv1;
const unconstrained_227: bv1;
const unconstrained_228: bv1;
const unconstrained_229: bv1;
const unconstrained_23: bv1;
const unconstrained_230: bv1;
const unconstrained_231: bv1;
const unconstrained_232: bv1;
const unconstrained_233: bv1;
const unconstrained_234: bv1;
const unconstrained_235: bv1;
const unconstrained_236: bv1;
const unconstrained_237: bv1;
const unconstrained_238: bv1;
const unconstrained_239: bv1;
const unconstrained_24: bv1;
const unconstrained_240: bv1;
const unconstrained_241: bv1;
const unconstrained_242: bv1;
const unconstrained_243: bv1;
const unconstrained_244: bv1;
const unconstrained_245: bv1;
const unconstrained_246: bv1;
const unconstrained_247: bv1;
const unconstrained_248: bv1;
const unconstrained_249: bv1;
const unconstrained_25: bv1;
const unconstrained_250: bv1;
const unconstrained_251: bv1;
const unconstrained_252: bv1;
const unconstrained_253: bv1;
const unconstrained_254: bv1;
const unconstrained_255: bv1;
const unconstrained_256: bv1;
const unconstrained_257: bv1;
const unconstrained_258: bv1;
const unconstrained_259: bv1;
const unconstrained_26: bv1;
const unconstrained_260: bv1;
const unconstrained_261: bv1;
const unconstrained_262: bv1;
const unconstrained_263: bv1;
const unconstrained_264: bv1;
const unconstrained_265: bv1;
const unconstrained_266: bv1;
const unconstrained_267: bv1;
const unconstrained_268: bv1;
const unconstrained_269: bv1;
const unconstrained_27: bv1;
const unconstrained_270: bv1;
const unconstrained_271: bv1;
const unconstrained_272: bv1;
const unconstrained_273: bv1;
const unconstrained_274: bv1;
const unconstrained_275: bv1;
const unconstrained_276: bv1;
const unconstrained_277: bv1;
const unconstrained_278: bv1;
const unconstrained_279: bv1;
const unconstrained_28: bv1;
const unconstrained_280: bv1;
const unconstrained_281: bv1;
const unconstrained_282: bv1;
const unconstrained_283: bv1;
const unconstrained_284: bv1;
const unconstrained_285: bv1;
const unconstrained_286: bv1;
const unconstrained_287: bv1;
const unconstrained_288: bv1;
const unconstrained_289: bv1;
const unconstrained_29: bv1;
const unconstrained_290: bv1;
const unconstrained_291: bv1;
const unconstrained_292: bv1;
const unconstrained_293: bv1;
const unconstrained_294: bv1;
const unconstrained_295: bv1;
const unconstrained_296: bv1;
const unconstrained_297: bv1;
const unconstrained_298: bv1;
const unconstrained_299: bv1;
const unconstrained_3: bv1;
const unconstrained_30: bv1;
const unconstrained_300: bv1;
const unconstrained_301: bv1;
const unconstrained_302: bv1;
const unconstrained_303: bv1;
const unconstrained_304: bv1;
const unconstrained_305: bv1;
const unconstrained_306: bv1;
const unconstrained_307: bv1;
const unconstrained_308: bv1;
const unconstrained_309: bv1;
const unconstrained_31: bv1;
const unconstrained_310: bv1;
const unconstrained_311: bv1;
const unconstrained_312: bv1;
const unconstrained_313: bv1;
const unconstrained_314: bv1;
const unconstrained_315: bv1;
const unconstrained_316: bv1;
const unconstrained_317: bv1;
const unconstrained_318: bv1;
const unconstrained_319: bv1;
const unconstrained_32: bv1;
const unconstrained_320: bv1;
const unconstrained_321: bv1;
const unconstrained_322: bv1;
const unconstrained_323: bv1;
const unconstrained_324: bv1;
const unconstrained_325: bv1;
const unconstrained_326: bv1;
const unconstrained_327: bv1;
const unconstrained_328: bv1;
const unconstrained_329: bv1;
const unconstrained_33: bv1;
const unconstrained_330: bv1;
const unconstrained_331: bv1;
const unconstrained_332: bv1;
const unconstrained_333: bv1;
const unconstrained_334: bv1;
const unconstrained_335: bv1;
const unconstrained_336: bv1;
const unconstrained_337: bv1;
const unconstrained_338: bv1;
const unconstrained_339: bv1;
const unconstrained_34: bv1;
const unconstrained_340: bv1;
const unconstrained_341: bv1;
const unconstrained_342: bv1;
const unconstrained_343: bv1;
const unconstrained_344: bv1;
const unconstrained_345: bv1;
const unconstrained_346: bv1;
const unconstrained_347: bv1;
const unconstrained_348: bv1;
const unconstrained_349: bv1;
const unconstrained_35: bv1;
const unconstrained_350: bv1;
const unconstrained_351: bv1;
const unconstrained_352: bv1;
const unconstrained_353: bv1;
const unconstrained_354: bv1;
const unconstrained_355: bv1;
const unconstrained_356: bv1;
const unconstrained_357: bv1;
const unconstrained_358: bv1;
const unconstrained_359: bv1;
const unconstrained_36: bv1;
const unconstrained_360: bv1;
const unconstrained_361: bv1;
const unconstrained_362: bv1;
const unconstrained_363: bv1;
const unconstrained_364: bv1;
const unconstrained_365: bv1;
const unconstrained_366: bv1;
const unconstrained_367: bv1;
const unconstrained_368: bv1;
const unconstrained_369: bv1;
const unconstrained_37: bv1;
const unconstrained_370: bv1;
const unconstrained_371: bv1;
const unconstrained_372: bv1;
const unconstrained_373: bv1;
const unconstrained_374: bv1;
const unconstrained_375: bv1;
const unconstrained_376: bv1;
const unconstrained_377: bv1;
const unconstrained_378: bv1;
const unconstrained_379: bv1;
const unconstrained_38: bv1;
const unconstrained_380: bv1;
const unconstrained_381: bv1;
const unconstrained_382: bv1;
const unconstrained_383: bv1;
const unconstrained_384: bv1;
const unconstrained_385: bv1;
const unconstrained_386: bv1;
const unconstrained_387: bv1;
const unconstrained_388: bv1;
const unconstrained_389: bv1;
const unconstrained_39: bv1;
const unconstrained_390: bv1;
const unconstrained_391: bv1;
const unconstrained_392: bv1;
const unconstrained_393: bv1;
const unconstrained_394: bv1;
const unconstrained_395: bv1;
const unconstrained_396: bv1;
const unconstrained_397: bv1;
const unconstrained_398: bv1;
const unconstrained_399: bv1;
const unconstrained_4: bv1;
const unconstrained_40: bv1;
const unconstrained_400: bv1;
const unconstrained_401: bv1;
const unconstrained_402: bv1;
const unconstrained_403: bv1;
const unconstrained_404: bv1;
const unconstrained_405: bv1;
const unconstrained_406: bv1;
const unconstrained_407: bv1;
const unconstrained_408: bv1;
const unconstrained_409: bv1;
const unconstrained_41: bv1;
const unconstrained_410: bv1;
const unconstrained_411: bv1;
const unconstrained_412: bv1;
const unconstrained_413: bv1;
const unconstrained_414: bv1;
const unconstrained_415: bv1;
const unconstrained_416: bv1;
const unconstrained_417: bv1;
const unconstrained_418: bv1;
const unconstrained_419: bv1;
const unconstrained_42: bv1;
const unconstrained_420: bv1;
const unconstrained_421: bv1;
const unconstrained_422: bv1;
const unconstrained_423: bv1;
const unconstrained_424: bv1;
const unconstrained_425: bv1;
const unconstrained_426: bv1;
const unconstrained_427: bv1;
const unconstrained_428: bv1;
const unconstrained_429: bv1;
const unconstrained_43: bv1;
const unconstrained_430: bv1;
const unconstrained_431: bv1;
const unconstrained_432: bv1;
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
const unconstrained_71: bv1;
const unconstrained_72: bv1;
const unconstrained_73: bv1;
const unconstrained_74: bv1;
const unconstrained_75: bv1;
const unconstrained_76: bv1;
const unconstrained_77: bv1;
const unconstrained_78: bv1;
const unconstrained_79: bv1;
const unconstrained_8: bv1;
const unconstrained_80: bv1;
const unconstrained_81: bv1;
const unconstrained_82: bv1;
const unconstrained_83: bv1;
const unconstrained_84: bv1;
const unconstrained_85: bv1;
const unconstrained_86: bv1;
const unconstrained_87: bv1;
const unconstrained_88: bv1;
const unconstrained_89: bv1;
const unconstrained_9: bv1;
const unconstrained_90: bv1;
const unconstrained_91: bv1;
const unconstrained_92: bv1;
const unconstrained_93: bv1;
const unconstrained_94: bv1;
const unconstrained_95: bv1;
const unconstrained_96: bv1;
const unconstrained_97: bv1;
const unconstrained_98: bv1;
const unconstrained_99: bv1;
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
var origCOUNT_1020: bv64;
var origCOUNT_1026: bv64;
var origCOUNT_1048: bv64;
var origCOUNT_1054: bv64;
var origCOUNT_106: bv64;
var origCOUNT_1072: bv64;
var origCOUNT_1078: bv64;
var origCOUNT_1092: bv64;
var origCOUNT_1110: bv64;
var origCOUNT_1116: bv64;
var origCOUNT_112: bv64;
var origCOUNT_1138: bv64;
var origCOUNT_1144: bv64;
var origCOUNT_1168: bv64;
var origCOUNT_1174: bv64;
var origCOUNT_1196: bv64;
var origCOUNT_1202: bv64;
var origCOUNT_1220: bv64;
var origCOUNT_1226: bv64;
var origCOUNT_134: bv64;
var origCOUNT_140: bv64;
var origCOUNT_158: bv64;
var origCOUNT_164: bv64;
var origCOUNT_182: bv64;
var origCOUNT_200: bv64;
var origCOUNT_206: bv64;
var origCOUNT_228: bv64;
var origCOUNT_234: bv64;
var origCOUNT_258: bv64;
var origCOUNT_264: bv64;
var origCOUNT_286: bv64;
var origCOUNT_292: bv64;
var origCOUNT_30: bv64;
var origCOUNT_310: bv64;
var origCOUNT_316: bv64;
var origCOUNT_338: bv64;
var origCOUNT_356: bv64;
var origCOUNT_362: bv64;
var origCOUNT_384: bv64;
var origCOUNT_390: bv64;
var origCOUNT_414: bv64;
var origCOUNT_420: bv64;
var origCOUNT_442: bv64;
var origCOUNT_448: bv64;
var origCOUNT_466: bv64;
var origCOUNT_472: bv64;
var origCOUNT_48: bv64;
var origCOUNT_490: bv64;
var origCOUNT_508: bv64;
var origCOUNT_514: bv64;
var origCOUNT_536: bv64;
var origCOUNT_54: bv64;
var origCOUNT_542: bv64;
var origCOUNT_566: bv64;
var origCOUNT_572: bv64;
var origCOUNT_594: bv64;
var origCOUNT_600: bv64;
var origCOUNT_618: bv64;
var origCOUNT_624: bv64;
var origCOUNT_642: bv64;
var origCOUNT_660: bv64;
var origCOUNT_666: bv64;
var origCOUNT_688: bv64;
var origCOUNT_694: bv64;
var origCOUNT_718: bv64;
var origCOUNT_724: bv64;
var origCOUNT_746: bv64;
var origCOUNT_752: bv64;
var origCOUNT_76: bv64;
var origCOUNT_770: bv64;
var origCOUNT_776: bv64;
var origCOUNT_790: bv64;
var origCOUNT_808: bv64;
var origCOUNT_814: bv64;
var origCOUNT_82: bv64;
var origCOUNT_836: bv64;
var origCOUNT_842: bv64;
var origCOUNT_866: bv64;
var origCOUNT_872: bv64;
var origCOUNT_894: bv64;
var origCOUNT_900: bv64;
var origCOUNT_918: bv64;
var origCOUNT_924: bv64;
var origCOUNT_944: bv64;
var origCOUNT_962: bv64;
var origCOUNT_968: bv64;
var origCOUNT_990: bv64;
var origCOUNT_996: bv64;
var origDEST_1019: bv64;
var origDEST_1025: bv64;
var origDEST_1047: bv64;
var origDEST_105: bv64;
var origDEST_1053: bv64;
var origDEST_1071: bv64;
var origDEST_1077: bv64;
var origDEST_1091: bv64;
var origDEST_1109: bv64;
var origDEST_111: bv64;
var origDEST_1115: bv64;
var origDEST_1137: bv64;
var origDEST_1143: bv64;
var origDEST_1167: bv64;
var origDEST_1173: bv64;
var origDEST_1195: bv64;
var origDEST_1201: bv64;
var origDEST_1219: bv64;
var origDEST_1225: bv64;
var origDEST_133: bv64;
var origDEST_139: bv64;
var origDEST_157: bv64;
var origDEST_163: bv64;
var origDEST_181: bv64;
var origDEST_199: bv64;
var origDEST_205: bv64;
var origDEST_227: bv64;
var origDEST_233: bv64;
var origDEST_257: bv64;
var origDEST_263: bv64;
var origDEST_285: bv64;
var origDEST_29: bv64;
var origDEST_291: bv64;
var origDEST_309: bv64;
var origDEST_315: bv64;
var origDEST_337: bv64;
var origDEST_355: bv64;
var origDEST_361: bv64;
var origDEST_383: bv64;
var origDEST_389: bv64;
var origDEST_413: bv64;
var origDEST_419: bv64;
var origDEST_441: bv64;
var origDEST_447: bv64;
var origDEST_465: bv64;
var origDEST_47: bv64;
var origDEST_471: bv64;
var origDEST_489: bv64;
var origDEST_507: bv64;
var origDEST_513: bv64;
var origDEST_53: bv64;
var origDEST_535: bv64;
var origDEST_541: bv64;
var origDEST_565: bv64;
var origDEST_571: bv64;
var origDEST_593: bv64;
var origDEST_599: bv64;
var origDEST_617: bv64;
var origDEST_623: bv64;
var origDEST_641: bv64;
var origDEST_659: bv64;
var origDEST_665: bv64;
var origDEST_687: bv64;
var origDEST_693: bv64;
var origDEST_717: bv64;
var origDEST_723: bv64;
var origDEST_745: bv64;
var origDEST_75: bv64;
var origDEST_751: bv64;
var origDEST_769: bv64;
var origDEST_775: bv64;
var origDEST_789: bv64;
var origDEST_807: bv64;
var origDEST_81: bv64;
var origDEST_813: bv64;
var origDEST_835: bv64;
var origDEST_841: bv64;
var origDEST_865: bv64;
var origDEST_871: bv64;
var origDEST_893: bv64;
var origDEST_899: bv64;
var origDEST_917: bv64;
var origDEST_923: bv64;
var origDEST_943: bv64;
var origDEST_961: bv64;
var origDEST_967: bv64;
var origDEST_989: bv64;
var origDEST_995: bv64;
var ra_1245: bv64;
var t1_1001: bv64;
var t1_1007: bv64;
var t1_1035: bv64;
var t1_1059: bv64;
var t1_1097: bv64;
var t1_1125: bv64;
var t1_1149: bv64;
var t1_1155: bv64;
var t1_1183: bv64;
var t1_1207: bv64;
var t1_121: bv64;
var t1_1239: bv64;
var t1_145: bv64;
var t1_187: bv64;
var t1_215: bv64;
var t1_239: bv64;
var t1_245: bv64;
var t1_273: bv64;
var t1_297: bv64;
var t1_343: bv64;
var t1_35: bv64;
var t1_371: bv64;
var t1_395: bv64;
var t1_401: bv64;
var t1_429: bv64;
var t1_453: bv64;
var t1_495: bv64;
var t1_523: bv64;
var t1_547: bv64;
var t1_553: bv64;
var t1_581: bv64;
var t1_605: bv64;
var t1_63: bv64;
var t1_647: bv64;
var t1_675: bv64;
var t1_699: bv64;
var t1_705: bv64;
var t1_733: bv64;
var t1_757: bv64;
var t1_795: bv64;
var t1_823: bv64;
var t1_847: bv64;
var t1_853: bv64;
var t1_87: bv64;
var t1_881: bv64;
var t1_905: bv64;
var t1_929: bv32;
var t1_93: bv64;
var t1_949: bv64;
var t1_977: bv64;
var t2_1002: bv64;
var t2_1008: bv64;
var t2_1036: bv64;
var t2_1060: bv64;
var t2_1098: bv64;
var t2_1126: bv64;
var t2_1150: bv64;
var t2_1156: bv64;
var t2_1184: bv64;
var t2_1208: bv64;
var t2_122: bv64;
var t2_1240: bv64;
var t2_146: bv64;
var t2_188: bv64;
var t2_216: bv64;
var t2_240: bv64;
var t2_246: bv64;
var t2_274: bv64;
var t2_298: bv64;
var t2_344: bv64;
var t2_36: bv64;
var t2_372: bv64;
var t2_396: bv64;
var t2_402: bv64;
var t2_430: bv64;
var t2_454: bv64;
var t2_496: bv64;
var t2_524: bv64;
var t2_548: bv64;
var t2_554: bv64;
var t2_582: bv64;
var t2_606: bv64;
var t2_64: bv64;
var t2_648: bv64;
var t2_676: bv64;
var t2_700: bv64;
var t2_706: bv64;
var t2_734: bv64;
var t2_758: bv64;
var t2_796: bv64;
var t2_824: bv64;
var t2_848: bv64;
var t2_854: bv64;
var t2_88: bv64;
var t2_882: bv64;
var t2_906: bv64;
var t2_930: bv32;
var t2_94: bv64;
var t2_950: bv64;
var t2_978: bv64;
var t_1: bv64;
var t_101: bv64;
var t_1015: bv64;
var t_1031: bv32;
var t_1043: bv64;
var t_1067: bv64;
var t_1083: bv32;
var t_1087: bv32;
var t_1105: bv64;
var t_1121: bv32;
var t_1133: bv64;
var t_1163: bv64;
var t_117: bv32;
var t_1179: bv32;
var t_1191: bv64;
var t_1215: bv64;
var t_1231: bv32;
var t_1235: bv32;
var t_129: bv64;
var t_13: bv32;
var t_153: bv64;
var t_169: bv32;
var t_17: bv32;
var t_173: bv32;
var t_177: bv32;
var t_195: bv64;
var t_21: bv32;
var t_211: bv32;
var t_223: bv64;
var t_25: bv32;
var t_253: bv64;
var t_269: bv32;
var t_281: bv64;
var t_305: bv64;
var t_321: bv32;
var t_325: bv32;
var t_329: bv32;
var t_333: bv32;
var t_351: bv64;
var t_367: bv32;
var t_379: bv64;
var t_409: bv64;
var t_425: bv32;
var t_43: bv64;
var t_437: bv64;
var t_461: bv64;
var t_477: bv32;
var t_481: bv32;
var t_485: bv32;
var t_5: bv32;
var t_503: bv64;
var t_519: bv32;
var t_531: bv64;
var t_561: bv64;
var t_577: bv32;
var t_589: bv64;
var t_59: bv32;
var t_613: bv64;
var t_629: bv32;
var t_633: bv32;
var t_637: bv32;
var t_655: bv64;
var t_671: bv32;
var t_683: bv64;
var t_71: bv64;
var t_713: bv64;
var t_729: bv32;
var t_741: bv64;
var t_765: bv64;
var t_781: bv32;
var t_785: bv32;
var t_803: bv64;
var t_819: bv32;
var t_831: bv64;
var t_861: bv64;
var t_877: bv32;
var t_889: bv64;
var t_9: bv32;
var t_913: bv64;
var t_935: bv32;
var t_939: bv32;
var t_957: bv64;
var t_973: bv32;
var t_985: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(96bv64);
axiom policy(656bv64);
axiom policy(5408bv64);
axiom policy(6768bv64);
axiom policy(12448bv64);
axiom policy(12592bv64);
axiom policy(14480bv64);
