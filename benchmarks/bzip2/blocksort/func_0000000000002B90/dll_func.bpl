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
axiom _function_addr_low == 11152bv64;
axiom _function_addr_high == 14480bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x2b90:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), R9);

label_0x2b95:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x2b9a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x2b9e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0x2ba2:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2ba9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 160bv64)));

label_0x2bb0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2bb4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 168bv64)));

label_0x2bbb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2bbf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2bc3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2bcb:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2bcf:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2bd2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2bd6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2bde:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2be2:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2be6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2bea:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2bef:
t_5 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0x2bf1:
if (bv2bool(ZF)) {
  goto label_0x2c1c;
}

label_0x2bf3:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2bf7:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2bfc:
t_9 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x2bfe:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2c0a;
}

label_0x2c00:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), 1bv32);

label_0x2c08:
goto label_0x2c12;

label_0x2c0a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), 0bv32);

label_0x2c12:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 24bv64))));

label_0x2c17:
goto label_0x3882;

label_0x2c1c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2c20:
t_13 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_13[32:31]) == (1bv32[32:31]))), (XOR_1((t_13[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_13)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2c22:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2c26:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2c2a:
t_17 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_17[32:31]) == (1bv32[32:31]))), (XOR_1((t_17[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_17)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2c2c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2c30:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2c34:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2c3c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2c40:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2c43:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2c47:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2c4f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2c53:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2c57:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2c5b:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2c60:
t_21 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_21)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_21, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)), 2bv32)), (XOR_32((RSHIFT_32(t_21, 4bv32)), t_21)))))[1:0]));
SF := t_21[32:31];
ZF := bool2bv(0bv32 == t_21);

label_0x2c62:
if (bv2bool(ZF)) {
  goto label_0x2c8d;
}

label_0x2c64:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2c68:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2c6d:
t_25 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_25)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_25, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)), 2bv32)), (XOR_32((RSHIFT_32(t_25, 4bv32)), t_25)))))[1:0]));
SF := t_25[32:31];
ZF := bool2bv(0bv32 == t_25);

label_0x2c6f:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2c7b;
}

label_0x2c71:
mem := STORE_LE_32(mem, PLUS_64(RSP, 28bv64), 1bv32);

label_0x2c79:
goto label_0x2c83;

label_0x2c7b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 28bv64), 0bv32);

label_0x2c83:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 28bv64))));

label_0x2c88:
goto label_0x3882;

label_0x2c8d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2c91:
t_29 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_29[32:31]) == (1bv32[32:31]))), (XOR_1((t_29[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_29)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2c93:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2c97:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2c9b:
t_33 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_33[32:31]) == (1bv32[32:31]))), (XOR_1((t_33[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_33)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2c9d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2ca1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2ca5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2cad:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2cb1:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2cb4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2cb8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2cc0:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2cc4:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2cc8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2ccc:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2cd1:
t_37 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_37)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_37, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)), 2bv32)), (XOR_32((RSHIFT_32(t_37, 4bv32)), t_37)))))[1:0]));
SF := t_37[32:31];
ZF := bool2bv(0bv32 == t_37);

label_0x2cd3:
if (bv2bool(ZF)) {
  goto label_0x2cfe;
}

label_0x2cd5:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2cd9:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2cde:
t_41 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_41)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_41, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)), 2bv32)), (XOR_32((RSHIFT_32(t_41, 4bv32)), t_41)))))[1:0]));
SF := t_41[32:31];
ZF := bool2bv(0bv32 == t_41);

label_0x2ce0:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2cec;
}

label_0x2ce2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 1bv32);

label_0x2cea:
goto label_0x2cf4;

label_0x2cec:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x2cf4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 32bv64))));

label_0x2cf9:
goto label_0x3882;

label_0x2cfe:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2d02:
t_45 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_45[32:31]) == (1bv32[32:31]))), (XOR_1((t_45[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_45)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2d04:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2d08:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2d0c:
t_49 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_49[32:31]) == (1bv32[32:31]))), (XOR_1((t_49[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_49)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2d0e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2d12:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2d16:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2d1e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2d22:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2d25:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2d29:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2d31:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2d35:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2d39:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2d3d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2d42:
t_53 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_53)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_53, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)), 2bv32)), (XOR_32((RSHIFT_32(t_53, 4bv32)), t_53)))))[1:0]));
SF := t_53[32:31];
ZF := bool2bv(0bv32 == t_53);

label_0x2d44:
if (bv2bool(ZF)) {
  goto label_0x2d6f;
}

label_0x2d46:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2d4a:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2d4f:
t_57 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_57)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_57, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))))[1:0]));
SF := t_57[32:31];
ZF := bool2bv(0bv32 == t_57);

label_0x2d51:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2d5d;
}

label_0x2d53:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 1bv32);

label_0x2d5b:
goto label_0x2d65;

label_0x2d5d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x2d65:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 36bv64))));

label_0x2d6a:
goto label_0x3882;

label_0x2d6f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2d73:
t_61 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_61[32:31]) == (1bv32[32:31]))), (XOR_1((t_61[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_61)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2d75:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2d79:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2d7d:
t_65 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_65[32:31]) == (1bv32[32:31]))), (XOR_1((t_65[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_65)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2d7f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2d83:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2d87:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2d8f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2d93:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2d96:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2d9a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2da2:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2da6:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2daa:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2dae:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2db3:
t_69 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_69)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_69, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)), 2bv32)), (XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)), 2bv32)), (XOR_32((RSHIFT_32(t_69, 4bv32)), t_69)))))[1:0]));
SF := t_69[32:31];
ZF := bool2bv(0bv32 == t_69);

label_0x2db5:
if (bv2bool(ZF)) {
  goto label_0x2de0;
}

label_0x2db7:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2dbb:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2dc0:
t_73 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_73)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_73, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)), 2bv32)), (XOR_32((RSHIFT_32(t_73, 4bv32)), t_73)))))[1:0]));
SF := t_73[32:31];
ZF := bool2bv(0bv32 == t_73);

label_0x2dc2:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2dce;
}

label_0x2dc4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 1bv32);

label_0x2dcc:
goto label_0x2dd6;

label_0x2dce:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 0bv32);

label_0x2dd6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 40bv64))));

label_0x2ddb:
goto label_0x3882;

label_0x2de0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2de4:
t_77 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_77[32:31]) == (1bv32[32:31]))), (XOR_1((t_77[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_77)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2de6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2dea:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2dee:
t_81 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_81[32:31]) == (1bv32[32:31]))), (XOR_1((t_81[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_81)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2df0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2df4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2df8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2e00:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2e04:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2e07:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2e0b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2e13:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2e17:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2e1b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2e1f:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2e24:
t_85 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_85)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_85, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)), 2bv32)), (XOR_32((RSHIFT_32(t_85, 4bv32)), t_85)))))[1:0]));
SF := t_85[32:31];
ZF := bool2bv(0bv32 == t_85);

label_0x2e26:
if (bv2bool(ZF)) {
  goto label_0x2e51;
}

label_0x2e28:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2e2c:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2e31:
t_89 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_89)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_89, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)), 2bv32)), (XOR_32((RSHIFT_32(t_89, 4bv32)), t_89)))))[1:0]));
SF := t_89[32:31];
ZF := bool2bv(0bv32 == t_89);

label_0x2e33:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2e3f;
}

label_0x2e35:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 1bv32);

label_0x2e3d:
goto label_0x2e47;

label_0x2e3f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 0bv32);

label_0x2e47:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 44bv64))));

label_0x2e4c:
goto label_0x3882;

label_0x2e51:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2e55:
t_93 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_93[32:31]) == (1bv32[32:31]))), (XOR_1((t_93[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_93)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2e57:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2e5b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2e5f:
t_97 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_97[32:31]) == (1bv32[32:31]))), (XOR_1((t_97[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_97)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2e61:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2e65:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2e69:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2e71:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2e75:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2e78:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2e7c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2e84:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2e88:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2e8c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2e90:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2e95:
t_101 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x2e97:
if (bv2bool(ZF)) {
  goto label_0x2ec2;
}

label_0x2e99:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2e9d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2ea2:
t_105 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_105)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_105, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)), 2bv32)), (XOR_32((RSHIFT_32(t_105, 4bv32)), t_105)))))[1:0]));
SF := t_105[32:31];
ZF := bool2bv(0bv32 == t_105);

label_0x2ea4:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2eb0;
}

label_0x2ea6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 1bv32);

label_0x2eae:
goto label_0x2eb8;

label_0x2eb0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), 0bv32);

label_0x2eb8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 48bv64))));

label_0x2ebd:
goto label_0x3882;

label_0x2ec2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2ec6:
t_109 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_109[32:31]) == (1bv32[32:31]))), (XOR_1((t_109[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_109)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2ec8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2ecc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2ed0:
t_113 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_113[32:31]) == (1bv32[32:31]))), (XOR_1((t_113[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_113)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2ed2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2ed6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2eda:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2ee2:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2ee6:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2ee9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2eed:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2ef5:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2ef9:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2efd:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2f01:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2f06:
t_117 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_117)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_117, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)), 2bv32)), (XOR_32((RSHIFT_32(t_117, 4bv32)), t_117)))))[1:0]));
SF := t_117[32:31];
ZF := bool2bv(0bv32 == t_117);

label_0x2f08:
if (bv2bool(ZF)) {
  goto label_0x2f33;
}

label_0x2f0a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2f0e:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2f13:
t_121 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_121)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_121, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))))[1:0]));
SF := t_121[32:31];
ZF := bool2bv(0bv32 == t_121);

label_0x2f15:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2f21;
}

label_0x2f17:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 1bv32);

label_0x2f1f:
goto label_0x2f29;

label_0x2f21:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), 0bv32);

label_0x2f29:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 52bv64))));

label_0x2f2e:
goto label_0x3882;

label_0x2f33:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2f37:
t_125 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_125[32:31]) == (1bv32[32:31]))), (XOR_1((t_125[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_125)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2f39:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2f3d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2f41:
t_129 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_129[32:31]) == (1bv32[32:31]))), (XOR_1((t_129[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_129)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2f43:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2f47:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2f4b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2f53:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2f57:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2f5a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2f5e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2f66:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2f6a:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2f6e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2f72:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2f77:
t_133 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_133)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_133, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)), 2bv32)), (XOR_32((RSHIFT_32(t_133, 4bv32)), t_133)))))[1:0]));
SF := t_133[32:31];
ZF := bool2bv(0bv32 == t_133);

label_0x2f79:
if (bv2bool(ZF)) {
  goto label_0x2fa4;
}

label_0x2f7b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2f7f:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2f84:
t_137 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_137)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_137, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)), 2bv32)), (XOR_32((RSHIFT_32(t_137, 4bv32)), t_137)))))[1:0]));
SF := t_137[32:31];
ZF := bool2bv(0bv32 == t_137);

label_0x2f86:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x2f92;
}

label_0x2f88:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 1bv32);

label_0x2f90:
goto label_0x2f9a;

label_0x2f92:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), 0bv32);

label_0x2f9a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 56bv64))));

label_0x2f9f:
goto label_0x3882;

label_0x2fa4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2fa8:
t_141 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_141[32:31]) == (1bv32[32:31]))), (XOR_1((t_141[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_141)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2faa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x2fae:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2fb2:
t_145 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_145[32:31]) == (1bv32[32:31]))), (XOR_1((t_145[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_145)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x2fb4:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x2fb8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x2fbc:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2fc4:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2fc8:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x2fcb:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x2fcf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x2fd7:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x2fdb:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x2fdf:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2fe3:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2fe8:
t_149 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_149)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_149, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)), 2bv32)), (XOR_32((RSHIFT_32(t_149, 4bv32)), t_149)))))[1:0]));
SF := t_149[32:31];
ZF := bool2bv(0bv32 == t_149);

label_0x2fea:
if (bv2bool(ZF)) {
  goto label_0x3015;
}

label_0x2fec:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x2ff0:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x2ff5:
t_153 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_153)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_153, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)), 2bv32)), (XOR_32((RSHIFT_32(t_153, 4bv32)), t_153)))))[1:0]));
SF := t_153[32:31];
ZF := bool2bv(0bv32 == t_153);

label_0x2ff7:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3003;
}

label_0x2ff9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), 1bv32);

label_0x3001:
goto label_0x300b;

label_0x3003:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), 0bv32);

label_0x300b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 60bv64))));

label_0x3010:
goto label_0x3882;

label_0x3015:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3019:
t_157 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_157[32:31]) == (1bv32[32:31]))), (XOR_1((t_157[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_157)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x301b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x301f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3023:
t_161 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_161[32:31]) == (1bv32[32:31]))), (XOR_1((t_161[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_161)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3025:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x3029:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x302d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3035:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3039:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x303c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3040:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3048:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x304c:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x3050:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3054:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3059:
t_165 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_165)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_165, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))))[1:0]));
SF := t_165[32:31];
ZF := bool2bv(0bv32 == t_165);

label_0x305b:
if (bv2bool(ZF)) {
  goto label_0x3086;
}

label_0x305d:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3061:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3066:
t_169 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_169)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_169, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)), 2bv32)), (XOR_32((RSHIFT_32(t_169, 4bv32)), t_169)))))[1:0]));
SF := t_169[32:31];
ZF := bool2bv(0bv32 == t_169);

label_0x3068:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3074;
}

label_0x306a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), 1bv32);

label_0x3072:
goto label_0x307c;

label_0x3074:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), 0bv32);

label_0x307c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 64bv64))));

label_0x3081:
goto label_0x3882;

label_0x3086:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x308a:
t_173 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_173[32:31]) == (1bv32[32:31]))), (XOR_1((t_173[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_173)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x308c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3090:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3094:
t_177 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_177[32:31]) == (1bv32[32:31]))), (XOR_1((t_177[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_177)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3096:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x309a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x309e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x30a6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x30aa:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x30ad:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x30b1:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x30b9:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x30bd:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x30c1:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x30c5:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x30ca:
t_181 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_181)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_181, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)), 2bv32)), (XOR_32((RSHIFT_32(t_181, 4bv32)), t_181)))))[1:0]));
SF := t_181[32:31];
ZF := bool2bv(0bv32 == t_181);

label_0x30cc:
if (bv2bool(ZF)) {
  goto label_0x30f7;
}

label_0x30ce:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x30d2:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x30d7:
t_185 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_185)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_185, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)), 2bv32)), (XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)), 2bv32)), (XOR_32((RSHIFT_32(t_185, 4bv32)), t_185)))))[1:0]));
SF := t_185[32:31];
ZF := bool2bv(0bv32 == t_185);

label_0x30d9:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x30e5;
}

label_0x30db:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), 1bv32);

label_0x30e3:
goto label_0x30ed;

label_0x30e5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), 0bv32);

label_0x30ed:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 68bv64))));

label_0x30f2:
goto label_0x3882;

label_0x30f7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x30fb:
t_189 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_189[32:31]) == (1bv32[32:31]))), (XOR_1((t_189[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_189)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x30fd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3101:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3105:
t_193 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_193[32:31]) == (1bv32[32:31]))), (XOR_1((t_193[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_193)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3107:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x310b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x3112:
t1_197 := RAX[32:0];
t2_198 := 8bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_198));
CF := bool2bv(LT_32((RAX[32:0]), t1_197));
OF := AND_1((bool2bv((t1_197[32:31]) == (t2_198[32:31]))), (XOR_1((t1_197[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_197)), t2_198)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3115:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0x3119:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x311d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3125:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3129:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x312c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3130:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3138:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x313c:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x3140:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3144:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3149:
t_203 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_203)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_203, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)), 2bv32)), (XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)), 2bv32)), (XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)))))[1:0]));
SF := t_203[32:31];
ZF := bool2bv(0bv32 == t_203);

label_0x314b:
if (bv2bool(ZF)) {
  goto label_0x3176;
}

label_0x314d:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3151:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3156:
t_207 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_207)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_207, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)), 2bv32)), (XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)), 2bv32)), (XOR_32((RSHIFT_32(t_207, 4bv32)), t_207)))))[1:0]));
SF := t_207[32:31];
ZF := bool2bv(0bv32 == t_207);

label_0x3158:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3164;
}

label_0x315a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 1bv32);

label_0x3162:
goto label_0x316c;

label_0x3164:
mem := STORE_LE_32(mem, PLUS_64(RSP, 72bv64), 0bv32);

label_0x316c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 72bv64))));

label_0x3171:
goto label_0x3882;

label_0x3176:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x317a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3182:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3186:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x318b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x318f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3197:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x319b:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x31a0:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x31a5:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x31aa:
t_211 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_211)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_211, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))))[1:0]));
SF := t_211[32:31];
ZF := bool2bv(0bv32 == t_211);

label_0x31ac:
if (bv2bool(ZF)) {
  goto label_0x31d8;
}

label_0x31ae:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x31b3:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x31b8:
t_215 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_215)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_215, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_215, 4bv32)), t_215)), 2bv32)), (XOR_32((RSHIFT_32(t_215, 4bv32)), t_215)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_215, 4bv32)), t_215)), 2bv32)), (XOR_32((RSHIFT_32(t_215, 4bv32)), t_215)))))[1:0]));
SF := t_215[32:31];
ZF := bool2bv(0bv32 == t_215);

label_0x31ba:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x31c6;
}

label_0x31bc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 76bv64), 1bv32);

label_0x31c4:
goto label_0x31ce;

label_0x31c6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 76bv64), 0bv32);

label_0x31ce:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 76bv64))));

label_0x31d3:
goto label_0x3882;

label_0x31d8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x31dc:
t_219 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_219[32:31]) == (1bv32[32:31]))), (XOR_1((t_219[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_219)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x31de:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x31e2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x31e6:
t_223 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_223[32:31]) == (1bv32[32:31]))), (XOR_1((t_223[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_223)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x31e8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x31ec:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x31f0:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x31f8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x31fc:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x31ff:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3203:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x320b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x320f:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x3213:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3217:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x321c:
t_227 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_227)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_227, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_227, 4bv32)), t_227)), 2bv32)), (XOR_32((RSHIFT_32(t_227, 4bv32)), t_227)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_227, 4bv32)), t_227)), 2bv32)), (XOR_32((RSHIFT_32(t_227, 4bv32)), t_227)))))[1:0]));
SF := t_227[32:31];
ZF := bool2bv(0bv32 == t_227);

label_0x321e:
if (bv2bool(ZF)) {
  goto label_0x3249;
}

label_0x3220:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3224:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3229:
t_231 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_231)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_231, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_231, 4bv32)), t_231)), 2bv32)), (XOR_32((RSHIFT_32(t_231, 4bv32)), t_231)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_231, 4bv32)), t_231)), 2bv32)), (XOR_32((RSHIFT_32(t_231, 4bv32)), t_231)))))[1:0]));
SF := t_231[32:31];
ZF := bool2bv(0bv32 == t_231);

label_0x322b:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3237;
}

label_0x322d:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), 1bv32);

label_0x3235:
goto label_0x323f;

label_0x3237:
mem := STORE_LE_32(mem, PLUS_64(RSP, 80bv64), 0bv32);

label_0x323f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 80bv64))));

label_0x3244:
goto label_0x3882;

label_0x3249:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x324d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3255:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3259:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x325e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3262:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x326a:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x326e:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x3273:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3278:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x327d:
t_235 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_235)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_235, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)), 2bv32)), (XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)), 2bv32)), (XOR_32((RSHIFT_32(t_235, 4bv32)), t_235)))))[1:0]));
SF := t_235[32:31];
ZF := bool2bv(0bv32 == t_235);

label_0x327f:
if (bv2bool(ZF)) {
  goto label_0x32ab;
}

label_0x3281:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3286:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x328b:
t_239 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_239)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_239, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_239, 4bv32)), t_239)), 2bv32)), (XOR_32((RSHIFT_32(t_239, 4bv32)), t_239)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_239, 4bv32)), t_239)), 2bv32)), (XOR_32((RSHIFT_32(t_239, 4bv32)), t_239)))))[1:0]));
SF := t_239[32:31];
ZF := bool2bv(0bv32 == t_239);

label_0x328d:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3299;
}

label_0x328f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), 1bv32);

label_0x3297:
goto label_0x32a1;

label_0x3299:
mem := STORE_LE_32(mem, PLUS_64(RSP, 84bv64), 0bv32);

label_0x32a1:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 84bv64))));

label_0x32a6:
goto label_0x3882;

label_0x32ab:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x32af:
t_243 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_243[32:31]) == (1bv32[32:31]))), (XOR_1((t_243[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_243)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x32b1:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x32b5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x32b9:
t_247 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_247[32:31]) == (1bv32[32:31]))), (XOR_1((t_247[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_247)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x32bb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x32bf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x32c3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x32cb:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x32cf:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x32d2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x32d6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x32de:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x32e2:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x32e6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x32ea:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x32ef:
t_251 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_251)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_251, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)), 2bv32)), (XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)), 2bv32)), (XOR_32((RSHIFT_32(t_251, 4bv32)), t_251)))))[1:0]));
SF := t_251[32:31];
ZF := bool2bv(0bv32 == t_251);

label_0x32f1:
if (bv2bool(ZF)) {
  goto label_0x331c;
}

label_0x32f3:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x32f7:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x32fc:
t_255 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_255)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_255, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)), 2bv32)), (XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)), 2bv32)), (XOR_32((RSHIFT_32(t_255, 4bv32)), t_255)))))[1:0]));
SF := t_255[32:31];
ZF := bool2bv(0bv32 == t_255);

label_0x32fe:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x330a;
}

label_0x3300:
mem := STORE_LE_32(mem, PLUS_64(RSP, 88bv64), 1bv32);

label_0x3308:
goto label_0x3312;

label_0x330a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 88bv64), 0bv32);

label_0x3312:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 88bv64))));

label_0x3317:
goto label_0x3882;

label_0x331c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3320:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3328:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x332c:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x3331:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3335:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x333d:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3341:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x3346:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x334b:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3350:
t_259 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_259)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_259, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)), 2bv32)), (XOR_32((RSHIFT_32(t_259, 4bv32)), t_259)))))[1:0]));
SF := t_259[32:31];
ZF := bool2bv(0bv32 == t_259);

label_0x3352:
if (bv2bool(ZF)) {
  goto label_0x337e;
}

label_0x3354:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3359:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x335e:
t_263 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_263)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_263, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)), 2bv32)), (XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)), 2bv32)), (XOR_32((RSHIFT_32(t_263, 4bv32)), t_263)))))[1:0]));
SF := t_263[32:31];
ZF := bool2bv(0bv32 == t_263);

label_0x3360:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x336c;
}

label_0x3362:
mem := STORE_LE_32(mem, PLUS_64(RSP, 92bv64), 1bv32);

label_0x336a:
goto label_0x3374;

label_0x336c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 92bv64), 0bv32);

label_0x3374:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 92bv64))));

label_0x3379:
goto label_0x3882;

label_0x337e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3382:
t_267 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_267[32:31]) == (1bv32[32:31]))), (XOR_1((t_267[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_267)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3384:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3388:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x338c:
t_271 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_271[32:31]) == (1bv32[32:31]))), (XOR_1((t_271[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_271)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x338e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x3392:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3396:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x339e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x33a2:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x33a5:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x33a9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x33b1:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x33b5:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x33b9:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x33bd:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x33c2:
t_275 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_275)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_275, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_275, 4bv32)), t_275)), 2bv32)), (XOR_32((RSHIFT_32(t_275, 4bv32)), t_275)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_275, 4bv32)), t_275)), 2bv32)), (XOR_32((RSHIFT_32(t_275, 4bv32)), t_275)))))[1:0]));
SF := t_275[32:31];
ZF := bool2bv(0bv32 == t_275);

label_0x33c4:
if (bv2bool(ZF)) {
  goto label_0x33ef;
}

label_0x33c6:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x33ca:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x33cf:
t_279 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_279)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_279, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)), 2bv32)), (XOR_32((RSHIFT_32(t_279, 4bv32)), t_279)))))[1:0]));
SF := t_279[32:31];
ZF := bool2bv(0bv32 == t_279);

label_0x33d1:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x33dd;
}

label_0x33d3:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 1bv32);

label_0x33db:
goto label_0x33e5;

label_0x33dd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 96bv64), 0bv32);

label_0x33e5:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 96bv64))));

label_0x33ea:
goto label_0x3882;

label_0x33ef:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x33f3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x33fb:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x33ff:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x3404:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3408:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3410:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3414:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x3419:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x341e:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3423:
t_283 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_283)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_283, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)), 2bv32)), (XOR_32((RSHIFT_32(t_283, 4bv32)), t_283)))))[1:0]));
SF := t_283[32:31];
ZF := bool2bv(0bv32 == t_283);

label_0x3425:
if (bv2bool(ZF)) {
  goto label_0x3451;
}

label_0x3427:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x342c:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3431:
t_287 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_287)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_287, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_287, 4bv32)), t_287)), 2bv32)), (XOR_32((RSHIFT_32(t_287, 4bv32)), t_287)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_287, 4bv32)), t_287)), 2bv32)), (XOR_32((RSHIFT_32(t_287, 4bv32)), t_287)))))[1:0]));
SF := t_287[32:31];
ZF := bool2bv(0bv32 == t_287);

label_0x3433:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x343f;
}

label_0x3435:
mem := STORE_LE_32(mem, PLUS_64(RSP, 100bv64), 1bv32);

label_0x343d:
goto label_0x3447;

label_0x343f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 100bv64), 0bv32);

label_0x3447:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 100bv64))));

label_0x344c:
goto label_0x3882;

label_0x3451:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3455:
t_291 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_291[32:31]) == (1bv32[32:31]))), (XOR_1((t_291[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_291)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3457:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x345b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x345f:
t_295 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_295[32:31]) == (1bv32[32:31]))), (XOR_1((t_295[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_295)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3461:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x3465:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3469:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3471:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3475:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x3478:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x347c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3484:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3488:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x348c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3490:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3495:
t_299 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_299)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_299, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_299, 4bv32)), t_299)), 2bv32)), (XOR_32((RSHIFT_32(t_299, 4bv32)), t_299)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_299, 4bv32)), t_299)), 2bv32)), (XOR_32((RSHIFT_32(t_299, 4bv32)), t_299)))))[1:0]));
SF := t_299[32:31];
ZF := bool2bv(0bv32 == t_299);

label_0x3497:
if (bv2bool(ZF)) {
  goto label_0x34c2;
}

label_0x3499:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x349d:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x34a2:
t_303 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_303)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_303, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)), 2bv32)), (XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)), 2bv32)), (XOR_32((RSHIFT_32(t_303, 4bv32)), t_303)))))[1:0]));
SF := t_303[32:31];
ZF := bool2bv(0bv32 == t_303);

label_0x34a4:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x34b0;
}

label_0x34a6:
mem := STORE_LE_32(mem, PLUS_64(RSP, 104bv64), 1bv32);

label_0x34ae:
goto label_0x34b8;

label_0x34b0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 104bv64), 0bv32);

label_0x34b8:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 104bv64))));

label_0x34bd:
goto label_0x3882;

label_0x34c2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x34c6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x34ce:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x34d2:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x34d7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x34db:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x34e3:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x34e7:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x34ec:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x34f1:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x34f6:
t_307 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_307)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_307, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)), 2bv32)), (XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)), 2bv32)), (XOR_32((RSHIFT_32(t_307, 4bv32)), t_307)))))[1:0]));
SF := t_307[32:31];
ZF := bool2bv(0bv32 == t_307);

label_0x34f8:
if (bv2bool(ZF)) {
  goto label_0x3524;
}

label_0x34fa:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x34ff:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3504:
t_311 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_311)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_311, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)), 2bv32)), (XOR_32((RSHIFT_32(t_311, 4bv32)), t_311)))))[1:0]));
SF := t_311[32:31];
ZF := bool2bv(0bv32 == t_311);

label_0x3506:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3512;
}

label_0x3508:
mem := STORE_LE_32(mem, PLUS_64(RSP, 108bv64), 1bv32);

label_0x3510:
goto label_0x351a;

label_0x3512:
mem := STORE_LE_32(mem, PLUS_64(RSP, 108bv64), 0bv32);

label_0x351a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 108bv64))));

label_0x351f:
goto label_0x3882;

label_0x3524:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3528:
t_315 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_315[32:31]) == (1bv32[32:31]))), (XOR_1((t_315[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_315)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x352a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x352e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3532:
t_319 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_319[32:31]) == (1bv32[32:31]))), (XOR_1((t_319[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_319)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3534:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x3538:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x353c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3544:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3548:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x354b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x354f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3557:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x355b:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x355f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3563:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3568:
t_323 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_323)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_323, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_323, 4bv32)), t_323)), 2bv32)), (XOR_32((RSHIFT_32(t_323, 4bv32)), t_323)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_323, 4bv32)), t_323)), 2bv32)), (XOR_32((RSHIFT_32(t_323, 4bv32)), t_323)))))[1:0]));
SF := t_323[32:31];
ZF := bool2bv(0bv32 == t_323);

label_0x356a:
if (bv2bool(ZF)) {
  goto label_0x3595;
}

label_0x356c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3570:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3575:
t_327 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_327)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_327, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)), 2bv32)), (XOR_32((RSHIFT_32(t_327, 4bv32)), t_327)))))[1:0]));
SF := t_327[32:31];
ZF := bool2bv(0bv32 == t_327);

label_0x3577:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3583;
}

label_0x3579:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), 1bv32);

label_0x3581:
goto label_0x358b;

label_0x3583:
mem := STORE_LE_32(mem, PLUS_64(RSP, 112bv64), 0bv32);

label_0x358b:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 112bv64))));

label_0x3590:
goto label_0x3882;

label_0x3595:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3599:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x35a1:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x35a5:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x35aa:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x35ae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x35b6:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x35ba:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x35bf:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x35c4:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x35c9:
t_331 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_331)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_331, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)), 2bv32)), (XOR_32((RSHIFT_32(t_331, 4bv32)), t_331)))))[1:0]));
SF := t_331[32:31];
ZF := bool2bv(0bv32 == t_331);

label_0x35cb:
if (bv2bool(ZF)) {
  goto label_0x35f7;
}

label_0x35cd:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x35d2:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x35d7:
t_335 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_335)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_335, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)), 2bv32)), (XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)), 2bv32)), (XOR_32((RSHIFT_32(t_335, 4bv32)), t_335)))))[1:0]));
SF := t_335[32:31];
ZF := bool2bv(0bv32 == t_335);

label_0x35d9:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x35e5;
}

label_0x35db:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), 1bv32);

label_0x35e3:
goto label_0x35ed;

label_0x35e5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 116bv64), 0bv32);

label_0x35ed:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 116bv64))));

label_0x35f2:
goto label_0x3882;

label_0x35f7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x35fb:
t_339 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_339[32:31]) == (1bv32[32:31]))), (XOR_1((t_339[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_339)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x35fd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x3601:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3605:
t_343 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_343[32:31]) == (1bv32[32:31]))), (XOR_1((t_343[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_343)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3607:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x360b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x360f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3617:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x361b:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x361e:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3622:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x362a:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x362e:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x3632:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3636:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x363b:
t_347 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_347)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_347, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_347, 4bv32)), t_347)), 2bv32)), (XOR_32((RSHIFT_32(t_347, 4bv32)), t_347)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_347, 4bv32)), t_347)), 2bv32)), (XOR_32((RSHIFT_32(t_347, 4bv32)), t_347)))))[1:0]));
SF := t_347[32:31];
ZF := bool2bv(0bv32 == t_347);

label_0x363d:
if (bv2bool(ZF)) {
  goto label_0x3668;
}

label_0x363f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3643:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x3648:
t_351 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_351)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_351, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_351, 4bv32)), t_351)), 2bv32)), (XOR_32((RSHIFT_32(t_351, 4bv32)), t_351)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_351, 4bv32)), t_351)), 2bv32)), (XOR_32((RSHIFT_32(t_351, 4bv32)), t_351)))))[1:0]));
SF := t_351[32:31];
ZF := bool2bv(0bv32 == t_351);

label_0x364a:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3656;
}

label_0x364c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), 1bv32);

label_0x3654:
goto label_0x365e;

label_0x3656:
mem := STORE_LE_32(mem, PLUS_64(RSP, 120bv64), 0bv32);

label_0x365e:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 120bv64))));

label_0x3663:
goto label_0x3882;

label_0x3668:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x366c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3674:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3678:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x367d:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x3681:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3689:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x368d:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x3692:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3697:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x369c:
t_355 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_355)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_355, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_355, 4bv32)), t_355)), 2bv32)), (XOR_32((RSHIFT_32(t_355, 4bv32)), t_355)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_355, 4bv32)), t_355)), 2bv32)), (XOR_32((RSHIFT_32(t_355, 4bv32)), t_355)))))[1:0]));
SF := t_355[32:31];
ZF := bool2bv(0bv32 == t_355);

label_0x369e:
if (bv2bool(ZF)) {
  goto label_0x36ca;
}

label_0x36a0:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x36a5:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x36aa:
t_359 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_359)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_359, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_359, 4bv32)), t_359)), 2bv32)), (XOR_32((RSHIFT_32(t_359, 4bv32)), t_359)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_359, 4bv32)), t_359)), 2bv32)), (XOR_32((RSHIFT_32(t_359, 4bv32)), t_359)))))[1:0]));
SF := t_359[32:31];
ZF := bool2bv(0bv32 == t_359);

label_0x36ac:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x36b8;
}

label_0x36ae:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), 1bv32);

label_0x36b6:
goto label_0x36c0;

label_0x36b8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 124bv64), 0bv32);

label_0x36c0:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 124bv64))));

label_0x36c5:
goto label_0x3882;

label_0x36ca:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x36ce:
t_363 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_363[32:31]) == (1bv32[32:31]))), (XOR_1((t_363[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_363)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x36d0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x36d4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x36d8:
t_367 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_367[32:31]) == (1bv32[32:31]))), (XOR_1((t_367[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_367)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x36da:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x36de:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x36e2:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x36ea:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x36ee:
mem := STORE_LE_8(mem, RSP, RAX[32:0][8:0]);

label_0x36f1:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x36f5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x36fd:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RCX, RAX))));

label_0x3701:
mem := STORE_LE_8(mem, PLUS_64(RSP, 1bv64), RAX[32:0][8:0]);

label_0x3705:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3709:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x370e:
t_371 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_371)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_371, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)), 2bv32)), (XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)), 2bv32)), (XOR_32((RSHIFT_32(t_371, 4bv32)), t_371)))))[1:0]));
SF := t_371[32:31];
ZF := bool2bv(0bv32 == t_371);

label_0x3710:
if (bv2bool(ZF)) {
  goto label_0x3744;
}

label_0x3712:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, RSP)));

label_0x3716:
RCX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 1bv64))));

label_0x371b:
t_375 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_375)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_375, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_375, 4bv32)), t_375)), 2bv32)), (XOR_32((RSHIFT_32(t_375, 4bv32)), t_375)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_375, 4bv32)), t_375)), 2bv32)), (XOR_32((RSHIFT_32(t_375, 4bv32)), t_375)))))[1:0]));
SF := t_375[32:31];
ZF := bool2bv(0bv32 == t_375);

label_0x371d:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x372c;
}

label_0x371f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), 1bv32);

label_0x372a:
goto label_0x3737;

label_0x372c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 128bv64), 0bv32);

label_0x3737:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 128bv64))));

label_0x373f:
goto label_0x3882;

label_0x3744:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x3748:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3750:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3754:
mem := STORE_LE_16(mem, PLUS_64(RSP, 12bv64), RAX[32:0][16:0]);

label_0x3759:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x375d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 184bv64));

label_0x3765:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 1bv64))))));

label_0x3769:
mem := STORE_LE_16(mem, PLUS_64(RSP, 16bv64), RAX[32:0][16:0]);

label_0x376e:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3773:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3778:
t_379 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_379)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_379, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_379, 4bv32)), t_379)), 2bv32)), (XOR_32((RSHIFT_32(t_379, 4bv32)), t_379)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_379, 4bv32)), t_379)), 2bv32)), (XOR_32((RSHIFT_32(t_379, 4bv32)), t_379)))))[1:0]));
SF := t_379[32:31];
ZF := bool2bv(0bv32 == t_379);

label_0x377a:
if (bv2bool(ZF)) {
  goto label_0x37af;
}

label_0x377c:
RAX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 12bv64))));

label_0x3781:
RCX := (0bv32 ++ (0bv16 ++ LOAD_LE_16(mem, PLUS_64(RSP, 16bv64))));

label_0x3786:
t_383 := MINUS_32((RAX[32:0]), (RCX[32:0]));
CF := bool2bv(LT_32((RAX[32:0]), (RCX[32:0])));
OF := AND_32((XOR_32((RAX[32:0]), (RCX[32:0]))), (XOR_32((RAX[32:0]), t_383)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_383, (RAX[32:0]))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)), 2bv32)), (XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)), 2bv32)), (XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)))))[1:0]));
SF := t_383[32:31];
ZF := bool2bv(0bv32 == t_383);

label_0x3788:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3797;
}

label_0x378a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), 1bv32);

label_0x3795:
goto label_0x37a2;

label_0x3797:
mem := STORE_LE_32(mem, PLUS_64(RSP, 132bv64), 0bv32);

label_0x37a2:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RSP, 132bv64))));

label_0x37aa:
goto label_0x3882;

label_0x37af:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x37b3:
t_387 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_387[32:31]) == (1bv32[32:31]))), (XOR_1((t_387[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_387)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x37b5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x37b9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x37bd:
t_391 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_391[32:31]) == (1bv32[32:31]))), (XOR_1((t_391[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_391)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x37bf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x37c3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x37ca:
t_395 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))), t_395)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_395, (LOAD_LE_32(mem, PLUS_64(RSP, 4bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)), 2bv32)), (XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)), 2bv32)), (XOR_32((RSHIFT_32(t_395, 4bv32)), t_395)))))[1:0]));
SF := t_395[32:31];
ZF := bool2bv(0bv32 == t_395);

label_0x37ce:
if (bv2bool(CF)) {
  goto label_0x37e3;
}

label_0x37d0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x37d7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 4bv64)));

label_0x37db:
t_399 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_399, (RAX[32:0])));
OF := AND_32((XOR_32(t_399, (RAX[32:0]))), (XOR_32(t_399, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_399)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x37dd:
RAX := (0bv32 ++ RCX[32:0]);

label_0x37df:
mem := STORE_LE_32(mem, PLUS_64(RSP, 4bv64), RAX[32:0]);

label_0x37e3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x37ea:
t_403 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))), t_403)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_403, (LOAD_LE_32(mem, PLUS_64(RSP, 8bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)), 2bv32)), (XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)), 2bv32)), (XOR_32((RSHIFT_32(t_403, 4bv32)), t_403)))))[1:0]));
SF := t_403[32:31];
ZF := bool2bv(0bv32 == t_403);

label_0x37ee:
if (bv2bool(CF)) {
  goto label_0x3803;
}

label_0x37f0:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x37f7:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 8bv64)));

label_0x37fb:
t_407 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_407, (RAX[32:0])));
OF := AND_32((XOR_32(t_407, (RAX[32:0]))), (XOR_32(t_407, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_407)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x37fd:
RAX := (0bv32 ++ RCX[32:0]);

label_0x37ff:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RAX[32:0]);

label_0x3803:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 20bv64)));

label_0x3807:
t_411 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 8bv32));
CF := bool2bv(LT_32(t_411, 8bv32));
OF := AND_32((XOR_32(t_411, 8bv32)), (XOR_32(t_411, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_411)), 8bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x380a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 20bv64), RAX[32:0]);

label_0x380e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x3816:
RAX := (0bv32 ++ LOAD_LE_32(mem, RAX));

label_0x3818:
t_415 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_415, 1bv32)), (XOR_32(t_415, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_415)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x381a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 136bv64), RAX[32:0]);

label_0x3821:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x3829:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x382f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3834:
t_421 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)), 2bv64)), (XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)), 2bv64)), (XOR_64((RSHIFT_64(t_421, 4bv64)), t_421)))))[1:0]));
SF := t_421[64:63];
ZF := bool2bv(0bv64 == t_421);

label_0x3837:
if (bv2bool(ZF)) {
  goto label_0x383a;
}

label_0x3839:
assume false;

label_0x383a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x3842:
origDEST_425 := RAX;
origCOUNT_426 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), CF, LSHIFT_64(origDEST_425, (MINUS_64(64bv64, origCOUNT_426)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_426 == 1bv64)), origDEST_425[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_426 == 0bv64)), AF, unconstrained_4);

label_0x3846:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x384d:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3851:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x3859:
origDEST_431 := RCX;
origCOUNT_432 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), CF, LSHIFT_64(origDEST_431, (MINUS_64(64bv64, origCOUNT_432)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_432 == 1bv64)), origDEST_431[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_432 == 0bv64)), AF, unconstrained_6);

label_0x385d:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x3861:
if (bv2bool(CF)) {
  goto label_0x3864;
}

label_0x3863:
assume false;

label_0x3864:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 200bv64));

label_0x386c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 136bv64)));

label_0x3873:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3875:
t_437 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))), t_437)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_437, (LOAD_LE_32(mem, PLUS_64(RSP, 20bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)), 2bv32)), (XOR_32((RSHIFT_32(t_437, 4bv32)), t_437)))))[1:0]));
SF := t_437[32:31];
ZF := bool2bv(0bv32 == t_437);

label_0x387a:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x3119;
}

label_0x3880:
RAX := (RAX[64:8]) ++ 0bv8;
AF := unconstrained_11;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3882:
t1_441 := RSP;
t2_442 := 152bv64;
RSP := PLUS_64(RSP, t2_442);
CF := bool2bv(LT_64(RSP, t1_441));
OF := AND_1((bool2bv((t1_441[64:63]) == (t2_442[64:63]))), (XOR_1((t1_441[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_441)), t2_442)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3889:

ra_447 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_426,origCOUNT_432,origDEST_425,origDEST_431,ra_447,t1_197,t1_441,t2_198,t2_442,t_1,t_101,t_105,t_109,t_113,t_117,t_121,t_125,t_129,t_13,t_133,t_137,t_141,t_145,t_149,t_153,t_157,t_161,t_165,t_169,t_17,t_173,t_177,t_181,t_185,t_189,t_193,t_203,t_207,t_21,t_211,t_215,t_219,t_223,t_227,t_231,t_235,t_239,t_243,t_247,t_25,t_251,t_255,t_259,t_263,t_267,t_271,t_275,t_279,t_283,t_287,t_29,t_291,t_295,t_299,t_303,t_307,t_311,t_315,t_319,t_323,t_327,t_33,t_331,t_335,t_339,t_343,t_347,t_351,t_355,t_359,t_363,t_367,t_37,t_371,t_375,t_379,t_383,t_387,t_391,t_395,t_399,t_403,t_407,t_41,t_411,t_415,t_421,t_437,t_45,t_49,t_5,t_53,t_57,t_61,t_65,t_69,t_73,t_77,t_81,t_85,t_89,t_9,t_93,t_97;

const unconstrained_1: bv1;
const unconstrained_10: bv1;
const unconstrained_11: bv1;
const unconstrained_2: bv1;
const unconstrained_3: bv1;
const unconstrained_4: bv1;
const unconstrained_5: bv1;
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
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
var origCOUNT_426: bv64;
var origCOUNT_432: bv64;
var origDEST_425: bv64;
var origDEST_431: bv64;
var ra_447: bv64;
var t1_197: bv32;
var t1_441: bv64;
var t2_198: bv32;
var t2_442: bv64;
var t_1: bv64;
var t_101: bv32;
var t_105: bv32;
var t_109: bv32;
var t_113: bv32;
var t_117: bv32;
var t_121: bv32;
var t_125: bv32;
var t_129: bv32;
var t_13: bv32;
var t_133: bv32;
var t_137: bv32;
var t_141: bv32;
var t_145: bv32;
var t_149: bv32;
var t_153: bv32;
var t_157: bv32;
var t_161: bv32;
var t_165: bv32;
var t_169: bv32;
var t_17: bv32;
var t_173: bv32;
var t_177: bv32;
var t_181: bv32;
var t_185: bv32;
var t_189: bv32;
var t_193: bv32;
var t_203: bv32;
var t_207: bv32;
var t_21: bv32;
var t_211: bv32;
var t_215: bv32;
var t_219: bv32;
var t_223: bv32;
var t_227: bv32;
var t_231: bv32;
var t_235: bv32;
var t_239: bv32;
var t_243: bv32;
var t_247: bv32;
var t_25: bv32;
var t_251: bv32;
var t_255: bv32;
var t_259: bv32;
var t_263: bv32;
var t_267: bv32;
var t_271: bv32;
var t_275: bv32;
var t_279: bv32;
var t_283: bv32;
var t_287: bv32;
var t_29: bv32;
var t_291: bv32;
var t_295: bv32;
var t_299: bv32;
var t_303: bv32;
var t_307: bv32;
var t_311: bv32;
var t_315: bv32;
var t_319: bv32;
var t_323: bv32;
var t_327: bv32;
var t_33: bv32;
var t_331: bv32;
var t_335: bv32;
var t_339: bv32;
var t_343: bv32;
var t_347: bv32;
var t_351: bv32;
var t_355: bv32;
var t_359: bv32;
var t_363: bv32;
var t_367: bv32;
var t_37: bv32;
var t_371: bv32;
var t_375: bv32;
var t_379: bv32;
var t_383: bv32;
var t_387: bv32;
var t_391: bv32;
var t_395: bv32;
var t_399: bv32;
var t_403: bv32;
var t_407: bv32;
var t_41: bv32;
var t_411: bv32;
var t_415: bv32;
var t_421: bv64;
var t_437: bv32;
var t_45: bv32;
var t_49: bv32;
var t_5: bv32;
var t_53: bv32;
var t_57: bv32;
var t_61: bv32;
var t_65: bv32;
var t_69: bv32;
var t_73: bv32;
var t_77: bv32;
var t_81: bv32;
var t_85: bv32;
var t_89: bv32;
var t_9: bv32;
var t_93: bv32;
var t_97: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(1280bv64);
axiom policy(2064bv64);
axiom policy(6688bv64);
axiom policy(11152bv64);
axiom policy(14480bv64);
axiom policy(16016bv64);
axiom policy(16160bv64);
axiom policy(25760bv64);
