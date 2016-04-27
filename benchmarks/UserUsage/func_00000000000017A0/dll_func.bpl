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
axiom _function_addr_low == 6048bv64;
axiom _function_addr_high == 6631bv64;
function{:expand false} T(i:bv64) returns (bool) { true }

procedure arbitrary_func();

implementation dll_func()
{

label_0x17a0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), RBX);

label_0x17a5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RSI);

label_0x17aa:
t_1 := RDI;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, t_1);

label_0x17ab:
t_3 := RSP;
RSP := MINUS_64(RSP, 1200bv64);
CF := bool2bv(LT_64(t_3, 1200bv64));
OF := AND_64((XOR_64(t_3, 1200bv64)), (XOR_64(t_3, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_3)), 1200bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x17b2:
RDI := RCX;

label_0x17b5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1224bv64), R14);

label_0x17bd:
R14 := RDX;

label_0x17c0:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x17c5:
RDX := (0bv32 ++ 1000bv32);

label_0x17ca:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6095bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4570"} true;
call arbitrary_func();

label_0x17cf:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, 16bv64));

label_0x17d3:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6104bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1650"} true;
call arbitrary_func();

label_0x17d8:
RBX := RAX;

label_0x17db:
t_7 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_7, 4bv64)), t_7)), 2bv64)), (XOR_64((RSHIFT_64(t_7, 4bv64)), t_7)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_7, 4bv64)), t_7)), 2bv64)), (XOR_64((RSHIFT_64(t_7, 4bv64)), t_7)))))[1:0]));
SF := t_7[64:63];
ZF := bool2bv(0bv64 == t_7);

label_0x17de:
if (bv2bool(ZF)) {
  goto label_0x18a1;
}

label_0x17e4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 1216bv64), RBP);

label_0x17ec:


label_0x17f0:
t_11 := MINUS_64((LOAD_LE_64(mem, RBX)), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RBX)), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RBX)), 0bv64)), (XOR_64((LOAD_LE_64(mem, RBX)), t_11)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_11, (LOAD_LE_64(mem, RBX)))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)), 2bv64)), (XOR_64((RSHIFT_64(t_11, 4bv64)), t_11)))))[1:0]));
SF := t_11[64:63];
ZF := bool2bv(0bv64 == t_11);

label_0x17f4:
if (bv2bool(ZF)) {
  goto label_0x1884;
}

label_0x17fa:
RDX := (0bv32 ++ 0bv32);
AF := unconstrained_2;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x17fc:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x1801:
R8 := (0bv32 ++ 1000bv32);

label_0x1807:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6156bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2db0"} true;
call arbitrary_func();

label_0x180c:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RBX, 8bv64)));

label_0x1810:
R8 := PLUS_64((PLUS_64(14905bv64, 6167bv64)), 0bv64)[64:0];

label_0x1817:
RDX := (0bv32 ++ 1000bv32);

label_0x181c:
RCX := PLUS_64(RSP, 48bv64)[64:0];

label_0x1821:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6182bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2d10"} true;
call arbitrary_func();

label_0x1826:
RCX := (0bv32 ++ 32bv32);

label_0x182b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6192bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2410"} true;
call arbitrary_func();

label_0x1830:
t_15 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)), 2bv64)), (XOR_64((RSHIFT_64(t_15, 4bv64)), t_15)))))[1:0]));
SF := t_15[64:63];
ZF := bool2bv(0bv64 == t_15);

label_0x1833:
if (bv2bool(ZF)) {
  goto label_0x1847;
}

label_0x1835:
RDX := PLUS_64(RSP, 48bv64)[64:0];

label_0x183a:
RCX := RAX;

label_0x183d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6210bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2460"} true;
call arbitrary_func();

label_0x1842:
RBP := RAX;

label_0x1845:
goto label_0x1849;

label_0x1847:
RBP := (0bv32 ++ 0bv32);
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1849:
RCX := (0bv32 ++ 32bv32);

label_0x184e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6227bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2410"} true;
call arbitrary_func();

label_0x1853:
t_19 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_5;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)), 2bv64)), (XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)), 2bv64)), (XOR_64((RSHIFT_64(t_19, 4bv64)), t_19)))))[1:0]));
SF := t_19[64:63];
ZF := bool2bv(0bv64 == t_19);

label_0x1856:
if (bv2bool(ZF)) {
  goto label_0x1868;
}

label_0x1858:
RDX := LOAD_LE_64(mem, RBX);

label_0x185b:
RCX := RAX;

label_0x185e:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6243bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2460"} true;
call arbitrary_func();

label_0x1863:
RSI := RAX;

label_0x1866:
goto label_0x186a;

label_0x1868:
RSI := (0bv32 ++ 0bv32);
AF := unconstrained_6;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x186a:
RAX := LOAD_LE_64(mem, R14);

label_0x186d:
RBX := LOAD_LE_64(mem, PLUS_64(RAX, 8bv64));

label_0x1871:
RCX := RBX;

label_0x1874:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6265bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4520"} true;
call arbitrary_func();

label_0x1879:
R8 := RBP;

label_0x187c:
RDX := RSI;

label_0x187f:
RCX := R14;

label_0x1882:

target_23 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6276bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_23"} true;
call arbitrary_func();

label_0x1884:
RCX := LOAD_LE_64(mem, PLUS_64(RDI, 16bv64));

label_0x1888:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6285bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1d00"} true;
call arbitrary_func();

label_0x188d:
RBX := RAX;

label_0x1890:
t_25 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)), 2bv64)), (XOR_64((RSHIFT_64(t_25, 4bv64)), t_25)))))[1:0]));
SF := t_25[64:63];
ZF := bool2bv(0bv64 == t_25);

label_0x1893:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x17f0;
}

label_0x1899:
RBP := LOAD_LE_64(mem, PLUS_64(RSP, 1216bv64));

label_0x18a1:
RSI := LOAD_LE_64(mem, PLUS_64(RDI, 16bv64));

label_0x18a5:
R14 := LOAD_LE_64(mem, PLUS_64(RSP, 1224bv64));

label_0x18ad:
t_29 := AND_64(RSI, RSI);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)), 2bv64)), (XOR_64((RSHIFT_64(t_29, 4bv64)), t_29)))))[1:0]));
SF := t_29[64:63];
ZF := bool2bv(0bv64 == t_29);

label_0x18b0:
if (bv2bool(ZF)) {
  goto label_0x18ca;
}

label_0x18b2:
RAX := LOAD_LE_64(mem, RSI);

label_0x18b5:
RBX := LOAD_LE_64(mem, RAX);

label_0x18b8:
RCX := RBX;

label_0x18bb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6336bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x4520"} true;
call arbitrary_func();

label_0x18c0:
RDX := (0bv32 ++ 1bv32);

label_0x18c5:
RCX := RSI;

label_0x18c8:

target_33 := RBX;
RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6346bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "target_33"} true;
call arbitrary_func();

label_0x18ca:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x18ce:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_9;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18d4:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x18da:
if (bv2bool(ZF)) {
  goto label_0x18dd;
}

label_0x18dc:
assume false;

label_0x18dd:
RSI := LOAD_LE_64(mem, PLUS_64((PLUS_64(18620bv64, 6372bv64)), 0bv64));

label_0x18e4:
RCX := PLUS_64(RDI, 8bv64)[64:0];

label_0x18e8:
origDEST_39 := RCX;
origCOUNT_40 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), CF, LSHIFT_64(origDEST_39, (MINUS_64(64bv64, origCOUNT_40)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_40 == 1bv64)), origDEST_39[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_40 == 0bv64)), AF, unconstrained_12);

label_0x18ec:
RAX := PLUS_64(RDI, 8bv64)[64:0];

label_0x18f0:
origDEST_45 := RAX;
origCOUNT_46 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), CF, LSHIFT_64(origDEST_45, (MINUS_64(64bv64, origCOUNT_46)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_46 == 1bv64)), origDEST_45[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_46 == 0bv64)), AF, unconstrained_14);

label_0x18f4:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RCX, 3bv64))));

label_0x18f8:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_15;
SF := unconstrained_16;
AF := unconstrained_17;
PF := unconstrained_18;

label_0x18fc:
if (bv2bool(CF)) {
  goto label_0x18ff;
}

label_0x18fe:
assume false;

label_0x18ff:
RCX := (0bv32 ++ 48bv32);

label_0x1904:
mem := STORE_LE_64(mem, PLUS_64(RDI, 8bv64), 0bv64);

label_0x190c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6417bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2410"} true;
call arbitrary_func();

label_0x1911:
RBX := RAX;

label_0x1914:
t_51 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)), 2bv64)), (XOR_64((RSHIFT_64(t_51, 4bv64)), t_51)))))[1:0]));
SF := t_51[64:63];
ZF := bool2bv(0bv64 == t_51);

label_0x1917:
if (bv2bool(ZF)) {
  goto label_0x196a;
}

label_0x1919:
RDX := (0bv32 ++ 5000bv32);

label_0x191e:
RCX := RAX;

label_0x1921:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 6438bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x2650"} true;
call arbitrary_func();

label_0x1926:
RCX := PLUS_64(RBX, 24bv64)[64:0];

label_0x192a:
RCX := AND_64(RCX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1931:
RCX := XOR_64(RCX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1938:
if (bv2bool(ZF)) {
  goto label_0x193b;
}

label_0x193a:
assume false;

label_0x193b:
RAX := PLUS_64(RBX, 24bv64)[64:0];

label_0x193f:
origDEST_59 := RAX;
origCOUNT_60 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), CF, LSHIFT_64(origDEST_59, (MINUS_64(64bv64, origCOUNT_60)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_60 == 1bv64)), origDEST_59[64:63], unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_60 == 0bv64)), AF, unconstrained_23);

label_0x1943:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x1947:
RAX := PLUS_64(RBX, 24bv64)[64:0];

label_0x194b:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_24));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_25);

label_0x194f:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_26;
SF := unconstrained_27;
AF := unconstrained_28;
PF := unconstrained_29;

label_0x1953:
if (bv2bool(CF)) {
  goto label_0x1956;
}

label_0x1955:
assume false;

label_0x1956:
RAX := LOAD_LE_64(mem, PLUS_64(RBX, 8bv64));

label_0x195a:
mem := STORE_LE_64(mem, PLUS_64(RBX, 24bv64), RAX);

label_0x195e:
RAX := PLUS_64((PLUS_64(14547bv64, 6501bv64)), 0bv64)[64:0];

label_0x1965:
mem := STORE_LE_64(mem, RBX, RAX);

label_0x1968:
goto label_0x196c;

label_0x196a:
RBX := (0bv32 ++ 0bv32);
AF := unconstrained_30;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x196c:
RAX := PLUS_64(RDI, 16bv64)[64:0];

label_0x1970:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1976:
RAX := XOR_64(RAX, 536870912bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x197c:
if (bv2bool(ZF)) {
  goto label_0x197f;
}

label_0x197e:
assume false;

label_0x197f:
RAX := PLUS_64(RDI, 16bv64)[64:0];

label_0x1983:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, LSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), origDEST_75[64:63], unconstrained_33));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_34);

label_0x1987:
RCX := LOAD_LE_64(mem, PLUS_64(RSI, (LSHIFT_64(RAX, 3bv64))));

label_0x198b:
RAX := PLUS_64(RDI, 16bv64)[64:0];

label_0x198f:
origDEST_81 := RAX;
origCOUNT_82 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), CF, LSHIFT_64(origDEST_81, (MINUS_64(64bv64, origCOUNT_82)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_82 == 1bv64)), origDEST_81[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_82 == 0bv64)), AF, unconstrained_36);

label_0x1993:
CF := RSHIFT_64(RCX, (AND_64(RAX, 63bv64)))[1:0];
OF := unconstrained_37;
SF := unconstrained_38;
AF := unconstrained_39;
PF := unconstrained_40;

label_0x1997:
if (bv2bool(CF)) {
  goto label_0x199a;
}

label_0x1999:
assume false;

label_0x199a:
mem := STORE_LE_64(mem, PLUS_64(RDI, 16bv64), RBX);

label_0x199e:
R11 := PLUS_64(RSP, 1200bv64)[64:0];

label_0x19a6:
RAX := PLUS_64(RSP, 1056bv64)[64:0];

label_0x19ae:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, LSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), origDEST_87[64:63], unconstrained_41));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_42);

label_0x19b2:
RCX := PLUS_64(RSP, 1056bv64)[64:0];

label_0x19ba:
t1_93 := RSI;
t2_94 := RAX;
RSI := PLUS_64(RSI, t2_94);
CF := bool2bv(LT_64(RSI, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RSI[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSI, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)), 2bv64)), (XOR_64((RSHIFT_64(RSI, 4bv64)), RSI)))))[1:0]));
SF := RSI[64:63];
ZF := bool2bv(0bv64 == RSI);

label_0x19bd:
origDEST_99 := RCX;
origCOUNT_100 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), CF, LSHIFT_64(origDEST_99, (MINUS_64(64bv64, origCOUNT_100)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_100 == 1bv64)), origDEST_99[64:63], unconstrained_43));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_100 == 0bv64)), AF, unconstrained_44);

label_0x19c1:
RAX := (0bv32 ++ 254bv32);

label_0x19c6:
RCX := (0bv32 ++ AND_32((RCX[32:0]), 7bv32));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x19c9:
origDEST_107 := RAX[32:0][8:0];
origCOUNT_108 := AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8)));
RAX := (RAX[64:8]) ++ (LSHIFT_8((RAX[32:0][8:0]), (AND_8((RCX[32:0][8:0]), (MINUS_8(8bv8, 1bv8))))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), CF, RSHIFT_8(origDEST_107, (MINUS_8(8bv8, origCOUNT_108)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_108 == 1bv8)), XOR_1((RAX[32:0][8:0][8:7]), CF), unconstrained_46));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), SF, RAX[32:0][8:0][8:7]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), ZF, bool2bv(0bv8 == (RAX[32:0][8:0])));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), PF, NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))), 2bv8)), (XOR_8((RSHIFT_8((RAX[32:0][8:0]), 4bv8)), (RAX[32:0][8:0]))))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_108 == 0bv8)), AF, unconstrained_47);

label_0x19cb:
mem := STORE_LE_8(mem, RSI, AND_8((LOAD_LE_8(mem, RSI)), (RAX[32:0][8:0])));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_48;
PF := NOT_1((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RSI)), 4bv8)), (LOAD_LE_8(mem, RSI)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RSI)), 4bv8)), (LOAD_LE_8(mem, RSI)))))), 1bv8)), (XOR_8((RSHIFT_8((XOR_8((RSHIFT_8((LOAD_LE_8(mem, RSI)), 4bv8)), (LOAD_LE_8(mem, RSI)))), 2bv8)), (XOR_8((RSHIFT_8((LOAD_LE_8(mem, RSI)), 4bv8)), (LOAD_LE_8(mem, RSI)))))))[1:0]));
SF := LOAD_LE_8(mem, RSI)[8:7];
ZF := bool2bv(0bv8 == (LOAD_LE_8(mem, RSI)));

label_0x19cd:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_49;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x19cf:
mem := STORE_LE_64(mem, PLUS_64(RSI, 4294967295bv32 ++ 4294967279bv32), RAX);

label_0x19d3:
mem := STORE_LE_64(mem, PLUS_64(RSI, 4294967295bv32 ++ 4294967287bv32), RAX);

label_0x19d7:
mem := STORE_LE_8(mem, PLUS_64(RSI, 4294967295bv32 ++ 4294967295bv32), RAX[32:0][8:0]);

label_0x19da:
RBX := LOAD_LE_64(mem, PLUS_64(R11, 32bv64));

label_0x19de:
RSI := LOAD_LE_64(mem, PLUS_64(R11, 40bv64));

label_0x19e2:
RSP := R11;

label_0x19e5:
RDI := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);

label_0x19e6:

ra_115 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R11,R14,R8,R9,RAX,RBP,RBX,RCX,RDI,RDX,RSI,RSP,SF,ZF,mem,origCOUNT_100,origCOUNT_108,origCOUNT_40,origCOUNT_46,origCOUNT_60,origCOUNT_66,origCOUNT_76,origCOUNT_82,origCOUNT_88,origDEST_107,origDEST_39,origDEST_45,origDEST_59,origDEST_65,origDEST_75,origDEST_81,origDEST_87,origDEST_99,ra_115,t1_93,t2_94,t_1,t_11,t_15,t_19,t_25,t_29,t_3,t_51,t_7,target_23,target_33;

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
const unconstrained_6: bv1;
const unconstrained_7: bv1;
const unconstrained_8: bv1;
const unconstrained_9: bv1;
var R10: bv64;
var R12: bv64;
var R13: bv64;
var R15: bv64;
var AF: bv1;
var CF: bv1;
var OF: bv1;
var PF: bv1;
var R11: bv64;
var R14: bv64;
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
var origCOUNT_100: bv64;
var origCOUNT_108: bv8;
var origCOUNT_40: bv64;
var origCOUNT_46: bv64;
var origCOUNT_60: bv64;
var origCOUNT_66: bv64;
var origCOUNT_76: bv64;
var origCOUNT_82: bv64;
var origCOUNT_88: bv64;
var origDEST_107: bv8;
var origDEST_39: bv64;
var origDEST_45: bv64;
var origDEST_59: bv64;
var origDEST_65: bv64;
var origDEST_75: bv64;
var origDEST_81: bv64;
var origDEST_87: bv64;
var origDEST_99: bv64;
var ra_115: bv64;
var t1_93: bv64;
var t2_94: bv64;
var t_1: bv64;
var t_11: bv64;
var t_15: bv64;
var t_19: bv64;
var t_25: bv64;
var t_29: bv64;
var t_3: bv64;
var t_51: bv64;
var t_7: bv64;
var target_23: bv64;
var target_33: bv64;


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
