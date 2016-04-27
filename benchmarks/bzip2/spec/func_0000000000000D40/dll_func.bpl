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
axiom _function_addr_low == 3392bv64;
axiom _function_addr_high == 3856bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0xd40:
mem := STORE_LE_32(mem, PLUS_64(RSP, 24bv64), R8[32:0]);

label_0xd45:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0xd4a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 8bv64), RCX[32:0]);

label_0xd4e:
t_1 := RSP;
RSP := MINUS_64(RSP, 72bv64);
CF := bool2bv(LT_64(t_1, 72bv64));
OF := AND_64((XOR_64(t_1, 72bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 72bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xd52:
t_5 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3416bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3416bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3416bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3416bv64)), 1bv64))), t_5)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_5, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3416bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)), 2bv32)), (XOR_32((RSHIFT_32(t_5, 4bv32)), t_5)))))[1:0]));
SF := t_5[32:31];
ZF := bool2bv(0bv32 == t_5);

label_0xd59:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xd75;
}

label_0xd5b:
R9 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xd60:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xd65:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0xd69:
RCX := PLUS_64((PLUS_64(0bv64, 3440bv64)), 0bv64)[64:0];

label_0xd70:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3445bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd75"} true;
call arbitrary_func();

label_0xd75:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 3bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 3bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), 3bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))))), 3bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0xd7a:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xda1;
}

label_0xd7c:
RCX := (0bv32 ++ 2bv32);

label_0xd81:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3462bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd86"} true;
call arbitrary_func();

label_0xd86:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)));

label_0xd8b:
RDX := PLUS_64((PLUS_64(0bv64, 3474bv64)), 0bv64)[64:0];

label_0xd92:
RCX := RAX;

label_0xd95:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3482bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xd9a"} true;
call arbitrary_func();

label_0xd9a:
RCX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0xd9c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3489bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xda1"} true;
call arbitrary_func();

label_0xda1:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)))));

label_0xda6:
RCX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xdab:
t_13 := TIMES_128(((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RCX := t_13[64:0];
OF := bool2bv(t_13 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
CF := bool2bv(t_13 != ((ITE_128(bv2bool(RCX[64:63]) ,(1bv64 ++ RCX) ,(0bv64 ++ RCX)))));
PF := unconstrained_2;
SF := unconstrained_3;
ZF := unconstrained_4;
AF := unconstrained_5;

label_0xdaf:
RDX := PLUS_64((PLUS_64(0bv64, 3510bv64)), 0bv64)[64:0];

label_0xdb6:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xdbb:
t_15 := TIMES_128(((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
R8 := t_15[64:0];
OF := bool2bv(t_15 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
CF := bool2bv(t_15 != ((ITE_128(bv2bool(R8[64:63]) ,(1bv64 ++ R8) ,(0bv64 ++ R8)))));
PF := unconstrained_6;
SF := unconstrained_7;
ZF := unconstrained_8;
AF := unconstrained_9;

label_0xdbf:
R9 := PLUS_64((PLUS_64(0bv64, 3526bv64)), 0bv64)[64:0];

label_0xdc6:
R8 := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(R9, R8)), 8bv64)))));

label_0xdcb:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(RDX, RCX)), 16bv64));

label_0xdd0:
t1_17 := RCX;
t2_18 := R8;
RCX := PLUS_64(RCX, t2_18);
CF := bool2bv(LT_64(RCX, t1_17));
OF := AND_1((bool2bv((t1_17[64:63]) == (t2_18[64:63]))), (XOR_1((t1_17[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_17)), t2_18)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xdd3:
R8 := RAX;

label_0xdd6:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0xddb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3552bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xde0"} true;
call arbitrary_func();

label_0xde0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xde5:
t_23 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_23[64:0];
OF := bool2bv(t_23 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_23 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_10;
SF := unconstrained_11;
ZF := unconstrained_12;
AF := unconstrained_13;

label_0xde9:
RCX := PLUS_64((PLUS_64(0bv64, 3568bv64)), 0bv64)[64:0];

label_0xdf0:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xdf4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 4bv64)));

label_0xdf8:
t1_25 := RAX[32:0];
t2_26 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_26));
CF := bool2bv(LT_32((RAX[32:0]), t1_25));
OF := AND_1((bool2bv((t1_25[32:31]) == (t2_26[32:31]))), (XOR_1((t1_25[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_25)), t2_26)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xdfa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0xdfe:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xe03:
t_31 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_31[64:0];
OF := bool2bv(t_31 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_31 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_14;
SF := unconstrained_15;
ZF := unconstrained_16;
AF := unconstrained_17;

label_0xe07:
RCX := PLUS_64((PLUS_64(0bv64, 3598bv64)), 0bv64)[64:0];

label_0xe0e:
t1_33 := RCX;
t2_34 := RAX;
RCX := PLUS_64(RCX, t2_34);
CF := bool2bv(LT_64(RCX, t1_33));
OF := AND_1((bool2bv((t1_33[64:63]) == (t2_34[64:63]))), (XOR_1((t1_33[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_33)), t2_34)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe11:
RAX := RCX;

label_0xe14:
t1_39 := RAX;
t2_40 := 4bv64;
RAX := PLUS_64(RAX, t2_40);
CF := bool2bv(LT_64(RAX, t1_39));
OF := AND_1((bool2bv((t1_39[64:63]) == (t2_40[64:63]))), (XOR_1((t1_39[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_39)), t2_40)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe18:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0xe1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xe22:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_18;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe28:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xe2d:
t_47 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)), 2bv64)), (XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)), 2bv64)), (XOR_64((RSHIFT_64(t_47, 4bv64)), t_47)))))[1:0]));
SF := t_47[64:63];
ZF := bool2bv(0bv64 == t_47);

label_0xe30:
if (bv2bool(ZF)) {
  goto label_0xe33;
}

label_0xe32:
assume false;

label_0xe33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xe38:
origDEST_51 := RAX;
origCOUNT_52 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), CF, LSHIFT_64(origDEST_51, (MINUS_64(64bv64, origCOUNT_52)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_52 == 1bv64)), origDEST_51[64:63], unconstrained_20));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_52 == 0bv64)), AF, unconstrained_21);

label_0xe3c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xe43:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xe47:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xe4c:
origDEST_57 := RCX;
origCOUNT_58 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), CF, LSHIFT_64(origDEST_57, (MINUS_64(64bv64, origCOUNT_58)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_58 == 1bv64)), origDEST_57[64:63], unconstrained_22));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_58 == 0bv64)), AF, unconstrained_23);

label_0xe50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_24;
SF := unconstrained_25;
AF := unconstrained_26;
PF := unconstrained_27;

label_0xe54:
if (bv2bool(CF)) {
  goto label_0xe57;
}

label_0xe56:
assume false;

label_0xe57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0xe5c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0xe60:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xe62:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xe67:
t_63 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_63[64:0];
OF := bool2bv(t_63 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_63 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_28;
SF := unconstrained_29;
ZF := unconstrained_30;
AF := unconstrained_31;

label_0xe6b:
RCX := PLUS_64((PLUS_64(0bv64, 3698bv64)), 0bv64)[64:0];

label_0xe72:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xe76:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64((PLUS_64(RCX, RAX)), 8bv64)));

label_0xe7a:
t1_65 := RAX[32:0];
t2_66 := RDX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), t2_66));
CF := bool2bv(LT_32((RAX[32:0]), t1_65));
OF := AND_1((bool2bv((t1_65[32:31]) == (t2_66[32:31]))), (XOR_1((t1_65[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t1_65)), t2_66)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0xe7c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0xe80:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 80bv64)))));

label_0xe85:
t_71 := TIMES_128(((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))), ((ITE_128(bv2bool(24bv64[64:63]) ,(1bv64 ++ 24bv64) ,(0bv64 ++ 24bv64)))));
RAX := t_71[64:0];
OF := bool2bv(t_71 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
CF := bool2bv(t_71 != ((ITE_128(bv2bool(RAX[64:63]) ,(1bv64 ++ RAX) ,(0bv64 ++ RAX)))));
PF := unconstrained_32;
SF := unconstrained_33;
ZF := unconstrained_34;
AF := unconstrained_35;

label_0xe89:
RCX := PLUS_64((PLUS_64(0bv64, 3728bv64)), 0bv64)[64:0];

label_0xe90:
t1_73 := RCX;
t2_74 := RAX;
RCX := PLUS_64(RCX, t2_74);
CF := bool2bv(LT_64(RCX, t1_73));
OF := AND_1((bool2bv((t1_73[64:63]) == (t2_74[64:63]))), (XOR_1((t1_73[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_73)), t2_74)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0xe93:
RAX := RCX;

label_0xe96:
t1_79 := RAX;
t2_80 := 8bv64;
RAX := PLUS_64(RAX, t2_80);
CF := bool2bv(LT_64(RAX, t1_79));
OF := AND_1((bool2bv((t1_79[64:63]) == (t2_80[64:63]))), (XOR_1((t1_79[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_79)), t2_80)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xe9a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0xe9f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xea4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_36;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0xeaa:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0xeaf:
t_87 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_37;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)), 2bv64)), (XOR_64((RSHIFT_64(t_87, 4bv64)), t_87)))))[1:0]));
SF := t_87[64:63];
ZF := bool2bv(0bv64 == t_87);

label_0xeb2:
if (bv2bool(ZF)) {
  goto label_0xeb5;
}

label_0xeb4:
assume false;

label_0xeb5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xeba:
origDEST_91 := RAX;
origCOUNT_92 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), CF, LSHIFT_64(origDEST_91, (MINUS_64(64bv64, origCOUNT_92)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_92 == 1bv64)), origDEST_91[64:63], unconstrained_38));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_92 == 0bv64)), AF, unconstrained_39);

label_0xebe:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0xec5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0xec9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xece:
origDEST_97 := RCX;
origCOUNT_98 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), CF, LSHIFT_64(origDEST_97, (MINUS_64(64bv64, origCOUNT_98)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_98 == 1bv64)), origDEST_97[64:63], unconstrained_40));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_98 == 0bv64)), AF, unconstrained_41);

label_0xed2:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_42;
SF := unconstrained_43;
AF := unconstrained_44;
PF := unconstrained_45;

label_0xed6:
if (bv2bool(CF)) {
  goto label_0xed9;
}

label_0xed8:
assume false;

label_0xed9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0xede:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0xee2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0xee4:
t_103 := MINUS_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3818bv64)), 1bv64))), 4bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3818bv64)), 1bv64))), 4bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3818bv64)), 1bv64))), 4bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3818bv64)), 1bv64))), t_103)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_103, (LOAD_LE_32(mem, PLUS_64((PLUS_64(0bv64, 3818bv64)), 1bv64))))), 4bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)), 2bv32)), (XOR_32((RSHIFT_32(t_103, 4bv32)), t_103)))))[1:0]));
SF := t_103[32:31];
ZF := bool2bv(0bv32 == t_103);

label_0xeeb:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0xefd;
}

label_0xeed:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xef1:
RCX := PLUS_64((PLUS_64(0bv64, 3832bv64)), 0bv64)[64:0];

label_0xef8:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 3837bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0xefd"} true;
call arbitrary_func();

label_0xefd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 96bv64)));

label_0xf01:
t1_107 := RSP;
t2_108 := 72bv64;
RSP := PLUS_64(RSP, t2_108);
CF := bool2bv(LT_64(RSP, t1_107));
OF := AND_1((bool2bv((t1_107[64:63]) == (t2_108[64:63]))), (XOR_1((t1_107[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_107)), t2_108)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0xf05:

ra_113 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_52,origCOUNT_58,origCOUNT_92,origCOUNT_98,origDEST_51,origDEST_57,origDEST_91,origDEST_97,ra_113,t1_107,t1_17,t1_25,t1_33,t1_39,t1_65,t1_73,t1_79,t2_108,t2_18,t2_26,t2_34,t2_40,t2_66,t2_74,t2_80,t_1,t_103,t_13,t_15,t_23,t_31,t_47,t_5,t_63,t_71,t_87,t_9;

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
var origCOUNT_52: bv64;
var origCOUNT_58: bv64;
var origCOUNT_92: bv64;
var origCOUNT_98: bv64;
var origDEST_51: bv64;
var origDEST_57: bv64;
var origDEST_91: bv64;
var origDEST_97: bv64;
var ra_113: bv64;
var t1_107: bv64;
var t1_17: bv64;
var t1_25: bv32;
var t1_33: bv64;
var t1_39: bv64;
var t1_65: bv32;
var t1_73: bv64;
var t1_79: bv64;
var t2_108: bv64;
var t2_18: bv64;
var t2_26: bv32;
var t2_34: bv64;
var t2_40: bv64;
var t2_66: bv32;
var t2_74: bv64;
var t2_80: bv64;
var t_1: bv64;
var t_103: bv32;
var t_13: bv128;
var t_15: bv128;
var t_23: bv128;
var t_31: bv128;
var t_47: bv64;
var t_5: bv32;
var t_63: bv128;
var t_71: bv128;
var t_87: bv64;
var t_9: bv32;


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
