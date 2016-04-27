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
axiom _function_addr_low == 176bv64;
axiom _function_addr_high == 720bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xb0:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xb4:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 186bv64)), 1bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 186bv64)), 1bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 186bv64)), 1bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 186bv64)), 1bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 186bv64)), 1bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0xbb:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xc9;
}

label_0xbd:
RCX := PLUS_64((PLUS_64(0bv64, 196bv64)), 0bv64)[64:0];

label_0xc4:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 201bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xc9"} true;
call arbitrary_func();

label_0xc9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0xd1:
goto label_0xdd;

label_0xd3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xd7:
t_9 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_9[32:31]) == (1bv32[32:31]))), (XOR_1((t_9[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_9)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xd9:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xdd:
t_13 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0xe2:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x2ba;
}

label_0xe8:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0xed:
t_17 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_17[64:0];
OF := bool2bv(t_17 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_17 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_1;
SF := unconstrained_2;
ZF := unconstrained_3;
AF := unconstrained_4;

label_0xf1:
RCX := PLUS_64((PLUS_64(0bv64, 248bv64)), 0bv64)[64:0];

label_0xf8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, RAX)));

label_0xfb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0xff:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x104:
t_19 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_19[64:0];
OF := bool2bv(t_19 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_19 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_5;
SF := unconstrained_6;
ZF := unconstrained_7;
AF := unconstrained_8;

label_0x108:
RCX := PLUS_64((PLUS_64(0bv64, 271bv64)), 0bv64)[64:0];

label_0x10f:
t1_21 := RCX;
t2_22 := RAX;
RCX := PLUS_64(RCX, t2_22);
CF := bool2bv(LT_64(RCX, t1_21));
OF := AND_1((bool2bv((t1_21[64:63]) == (t2_22[64:63]))), (XOR_1((t1_21[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_21)), t2_22)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x112:
RAX := RCX;

label_0x115:
R8 := (0bv32 ++ 24bv32);

label_0x11b:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_9;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x11d:
RCX := RAX;

label_0x120:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 293bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x125"} true;
call arbitrary_func();

label_0x125:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x12a:
t_27 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_27[64:0];
OF := bool2bv(t_27 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_27 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_10;
SF := unconstrained_11;
ZF := unconstrained_12;
AF := unconstrained_13;

label_0x12e:
RCX := PLUS_64((PLUS_64(0bv64, 309bv64)), 0bv64)[64:0];

label_0x135:
t1_29 := RCX;
t2_30 := RAX;
RCX := PLUS_64(RCX, t2_30);
CF := bool2bv(LT_64(RCX, t1_29));
OF := AND_1((bool2bv((t1_29[64:63]) == (t2_30[64:63]))), (XOR_1((t1_29[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_29)), t2_30)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x138:
RAX := RCX;

label_0x13b:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x140:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x145:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_14;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x14b:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x150:
t_37 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_15;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)), 2bv64)), (XOR_64((RSHIFT_64(t_37, 4bv64)), t_37)))))[1:0]));
SF := t_37[64:63];
ZF := bool2bv(0bv64 == t_37);

label_0x153:
if (bv2bool(ZF)) {
  goto label_0x156;
}

label_0x155:
assume false;

label_0x156:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x15b:
origDEST_41 := RAX;
origCOUNT_42 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), CF, LSHIFT_64(origDEST_41, (MINUS_64(64bv64, origCOUNT_42)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_42 == 1bv64)), origDEST_41[64:63], unconstrained_16));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_42 == 0bv64)), AF, unconstrained_17);

label_0x15f:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x166:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x16a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x16f:
origDEST_47 := RCX;
origCOUNT_48 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), CF, LSHIFT_64(origDEST_47, (MINUS_64(64bv64, origCOUNT_48)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_48 == 1bv64)), origDEST_47[64:63], unconstrained_18));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_48 == 0bv64)), AF, unconstrained_19);

label_0x173:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_20;
SF := unconstrained_21;
AF := unconstrained_22;
PF := unconstrained_23;

label_0x177:
if (bv2bool(CF)) {
  goto label_0x17a;
}

label_0x179:
assume false;

label_0x17a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x17f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x183:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x185:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x189:
t1_53 := RAX[32:0];
t2_54 := 1048576bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_54));
CF := bool2bv(LT_32((RAX[32:0]), t1_53));
OF := AND_1((bool2bv((t1_53[32:31]) == (t2_54[32:31]))), (XOR_1((t1_53[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_53)), t2_54)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x18e:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x190:
RCX := RAX;

label_0x193:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 408bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x198"} true;
call arbitrary_func();

label_0x198:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x19d:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x1a2:
t_59 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_59[64:0];
OF := bool2bv(t_59 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_59 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_24;
SF := unconstrained_25;
ZF := unconstrained_26;
AF := unconstrained_27;

label_0x1a6:
RCX := PLUS_64((PLUS_64(0bv64, 429bv64)), 0bv64)[64:0];

label_0x1ad:
t1_61 := RCX;
t2_62 := RAX;
RCX := PLUS_64(RCX, t2_62);
CF := bool2bv(LT_64(RCX, t1_61));
OF := AND_1((bool2bv((t1_61[64:63]) == (t2_62[64:63]))), (XOR_1((t1_61[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_61)), t2_62)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1b0:
RAX := RCX;

label_0x1b3:
t1_67 := RAX;
t2_68 := 16bv64;
RAX := PLUS_64(RAX, t2_68);
CF := bool2bv(LT_64(RAX, t1_67));
OF := AND_1((bool2bv((t1_67[64:63]) == (t2_68[64:63]))), (XOR_1((t1_67[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_67)), t2_68)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1b7:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x1bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1c1:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_28;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1c7:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1cc:
t_75 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))))[1:0]));
SF := t_75[64:63];
ZF := bool2bv(0bv64 == t_75);

label_0x1cf:
if (bv2bool(ZF)) {
  goto label_0x1d2;
}

label_0x1d1:
assume false;

label_0x1d2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1d7:
origDEST_79 := RAX;
origCOUNT_80 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_31);

label_0x1db:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1e2:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1e6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1eb:
origDEST_85 := RCX;
origCOUNT_86 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_33);

label_0x1ef:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_34;
SF := unconstrained_35;
AF := unconstrained_36;
PF := unconstrained_37;

label_0x1f3:
if (bv2bool(CF)) {
  goto label_0x1f6;
}

label_0x1f5:
assume false;

label_0x1f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1fb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x200:
mem := STORE_LE_64(mem, RAX, RCX);

label_0x203:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x208:
t_91 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_91[64:0];
OF := bool2bv(t_91 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_91 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_38;
SF := unconstrained_39;
ZF := unconstrained_40;
AF := unconstrained_41;

label_0x20c:
RCX := PLUS_64((PLUS_64(0bv64, 531bv64)), 0bv64)[64:0];

label_0x213:
t_93 := MINUS_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64))), t_93)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_93, (LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x219:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x22e;
}

label_0x21b:
RCX := PLUS_64((PLUS_64(0bv64, 546bv64)), 0bv64)[64:0];

label_0x222:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 551bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x227"} true;
call arbitrary_func();

label_0x227:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_42;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x229:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 558bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x22e"} true;
call arbitrary_func();

label_0x22e:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x236:
goto label_0x245;

label_0x238:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x23c:
t1_97 := RAX[32:0];
t2_98 := 1024bv32;
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_98));
CF := bool2bv(LT_32((RAX[32:0]), t1_97));
OF := AND_1((bool2bv((t1_97[32:31]) == (t2_98[32:31]))), (XOR_1((t1_97[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_97)), t2_98)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x241:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x245:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x249:
t_103 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_103)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_103, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))))[1:0]));
SF := t_103[32:31];
ZF := bool2bv(0bv32 == t_103);

label_0x24d:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x2b5;
}

label_0x24f:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)))));

label_0x254:
t_107 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_107[64:0];
OF := bool2bv(t_107 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_107 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_43;
SF := unconstrained_44;
ZF := unconstrained_45;
AF := unconstrained_46;

label_0x258:
RCX := PLUS_64((PLUS_64(0bv64, 607bv64)), 0bv64)[64:0];

label_0x25f:
RDX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)))));

label_0x264:
RAX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RCX, RAX)), 16bv64));

label_0x269:
t1_109 := RAX;
t2_110 := RDX;
RAX := PLUS_64(RAX, t2_110);
CF := bool2bv(LT_64(RAX, t1_109));
OF := AND_1((bool2bv((t1_109[64:63]) == (t2_110[64:63]))), (XOR_1((t1_109[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_109)), t2_110)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x26c:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x271:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x276:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x27c:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x281:
t_117 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)), 2bv64)), (XOR_64((RSHIFT_64(t_117, 4bv64)), t_117)))))[1:0]));
SF := t_117[64:63];
ZF := bool2bv(0bv64 == t_117);

label_0x284:
if (bv2bool(ZF)) {
  goto label_0x287;
}

label_0x286:
assume false;

label_0x287:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x28c:
origDEST_121 := RAX;
origCOUNT_122 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), CF, LSHIFT_64(origDEST_121, (MINUS_64(64bv64, origCOUNT_122)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_122 == 1bv64)), origDEST_121[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_122 == 0bv64)), AF, unconstrained_50);

label_0x290:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x297:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x29b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2a0:
origDEST_127 := RCX;
origCOUNT_128 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), CF, LSHIFT_64(origDEST_127, (MINUS_64(64bv64, origCOUNT_128)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_128 == 1bv64)), origDEST_127[64:63], unconstrained_51));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_128 == 0bv64)), AF, unconstrained_52);

label_0x2a4:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_53;
SF := unconstrained_54;
AF := unconstrained_55;
PF := unconstrained_56;

label_0x2a8:
if (bv2bool(CF)) {
  goto label_0x2ab;
}

label_0x2aa:
assume false;

label_0x2ab:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x2b0:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x2b3:
goto label_0x238;

label_0x2b5:
goto label_0xd3;

label_0x2ba:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_57;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x2bc:
t1_133 := RSP;
t2_134 := 88bv64;
RSP := PLUS_64(RSP, t2_134);
CF := bool2bv(LT_64(RSP, t1_133));
OF := AND_1((bool2bv((t1_133[64:63]) == (t2_134[64:63]))), (XOR_1((t1_133[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_133)), t2_134)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x2c0:

ra_139 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_122,origCOUNT_128,origCOUNT_42,origCOUNT_48,origCOUNT_80,origCOUNT_86,origDEST_121,origDEST_127,origDEST_41,origDEST_47,origDEST_79,origDEST_85,ra_139,t1_109,t1_133,t1_21,t1_29,t1_53,t1_61,t1_67,t1_97,t2_110,t2_134,t2_22,t2_30,t2_54,t2_62,t2_68,t2_98,t_1,t_103,t_107,t_117,t_13,t_17,t_19,t_27,t_37,t_5,t_59,t_75,t_9,t_91,t_93;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_122: bv64;
var origCOUNT_128: bv64;
var origCOUNT_42: bv64;
var origCOUNT_48: bv64;
var origCOUNT_80: bv64;
var origCOUNT_86: bv64;
var origDEST_121: bv64;
var origDEST_127: bv64;
var origDEST_41: bv64;
var origDEST_47: bv64;
var origDEST_79: bv64;
var origDEST_85: bv64;
var ra_139: bv64;
var t1_109: bv64;
var t1_133: bv64;
var t1_21: bv64;
var t1_29: bv64;
var t1_53: bv32;
var t1_61: bv64;
var t1_67: bv64;
var t1_97: bv32;
var t2_110: bv64;
var t2_134: bv64;
var t2_22: bv64;
var t2_30: bv64;
var t2_54: bv32;
var t2_62: bv64;
var t2_68: bv64;
var t2_98: bv32;
var t_1: bv64;
var t_103: bv32;
var t_107: bv128;
var t_117: bv64;
var t_13: bv32;
var t_17: bv128;
var t_19: bv128;
var t_27: bv128;
var t_37: bv64;
var t_5: bv32;
var t_59: bv128;
var t_75: bv64;
var t_9: bv32;
var t_91: bv128;
var t_93: bv64;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(48bv64);
axiom policy(112bv64);
axiom policy(176bv64);
axiom policy(720bv64);
axiom policy(1504bv64);
axiom policy(2576bv64);
axiom policy(3104bv64);
axiom policy(3392bv64);
axiom policy(3856bv64);
axiom policy(4240bv64);
axiom policy(4672bv64);
axiom policy(5232bv64);
axiom policy(5728bv64);
axiom policy(5856bv64);
axiom policy(6336bv64);
axiom policy(6352bv64);
axiom policy(6480bv64);
