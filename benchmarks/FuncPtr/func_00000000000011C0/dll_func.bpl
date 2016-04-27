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
axiom _function_addr_low == 4544bv64;
axiom _function_addr_high == 4999bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x11c0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x11c5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x11ca:
t_1 := RSP;
RSP := MINUS_64(RSP, 88bv64);
CF := bool2bv(LT_64(t_1, 88bv64));
OF := AND_64((XOR_64(t_1, 88bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 88bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x11ce:
t_5 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_5)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_5, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)), 2bv64)), (XOR_64((RSHIFT_64(t_5, 4bv64)), t_5)))))[1:0]));
SF := t_5[64:63];
ZF := bool2bv(0bv64 == t_5);

label_0x11d4:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x11db;
}

label_0x11d6:
goto label_0x1382;

label_0x11db:
t_9 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 456bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 456bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 456bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_9)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_9, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 456bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)), 2bv64)), (XOR_64((RSHIFT_64(t_9, 4bv64)), t_9)))))[1:0]));
SF := t_9[64:63];
ZF := bool2bv(0bv64 == t_9);

label_0x11e4:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x11fa;
}

label_0x11e6:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x11eb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x11f0:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4597bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c80"} true;
call arbitrary_func();

label_0x11f5:
goto label_0x1382;

label_0x11fa:
t_13 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 912bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 912bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 912bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_13)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_13, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 912bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)), 2bv64)), (XOR_64((RSHIFT_64(t_13, 4bv64)), t_13)))))[1:0]));
SF := t_13[64:63];
ZF := bool2bv(0bv64 == t_13);

label_0x1203:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x124e;
}

label_0x1205:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x120a:
origDEST_17 := RAX;
origCOUNT_18 := AND_64(1bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(1bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), CF, LSHIFT_64(origDEST_17, (MINUS_64(64bv64, origCOUNT_18)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_18 == 1bv64)), origDEST_17[64:63], unconstrained_1));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_18 == 0bv64)), AF, unconstrained_2);

label_0x120d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RAX);

label_0x1212:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1217:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x121c:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4641bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c80"} true;
call arbitrary_func();

label_0x1221:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1226:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x122b:
t_23 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_23, RAX));
OF := AND_64((XOR_64(t_23, RAX)), (XOR_64(t_23, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_23)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x122e:
RAX := RCX;

label_0x1231:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 40bv64));

label_0x1236:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x123b:
t1_27 := RDX;
t2_28 := RCX;
RDX := PLUS_64(RDX, t2_28);
CF := bool2bv(LT_64(RDX, t1_27));
OF := AND_1((bool2bv((t1_27[64:63]) == (t2_28[64:63]))), (XOR_1((t1_27[64:63]), (RDX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RDX, t1_27)), t2_28)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)), 2bv64)), (XOR_64((RSHIFT_64(RDX, 4bv64)), RDX)))))[1:0]));
SF := RDX[64:63];
ZF := bool2bv(0bv64 == RDX);

label_0x123e:
RCX := RDX;

label_0x1241:
RDX := RAX;

label_0x1244:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4681bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c80"} true;
call arbitrary_func();

label_0x1249:
goto label_0x1382;

label_0x124e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1253:
RAX := AND_64(RAX, 511bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_3;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1259:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x125e:
t_35 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_35)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_35, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)), 2bv64)), (XOR_64((RSHIFT_64(t_35, 4bv64)), t_35)))))[1:0]));
SF := t_35[64:63];
ZF := bool2bv(0bv64 == t_35);

label_0x1264:
if (bv2bool(ZF)) {
  goto label_0x12cb;
}

label_0x1266:
RAX := (0bv32 ++ 512bv32);

label_0x126b:
t_39 := RAX;
RAX := MINUS_64(RAX, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))));
CF := bool2bv(LT_64(t_39, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64)))));
OF := AND_64((XOR_64(t_39, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), (XOR_64(t_39, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_39)), (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1270:
mem := STORE_LE_64(mem, PLUS_64(RSP, 32bv64), RAX);

label_0x1275:
t_43 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 512bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 512bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), 512bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))), t_43)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_43, (LOAD_LE_64(mem, PLUS_64(RSP, 48bv64))))), 512bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)), 2bv64)), (XOR_64((RSHIFT_64(t_43, 4bv64)), t_43)))))[1:0]));
SF := t_43[64:63];
ZF := bool2bv(0bv64 == t_43);

label_0x127e:
if (bv2bool(CF)) {
  goto label_0x1283;
}

label_0x1280:
assume false;

label_0x1281:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_4;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x1283:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1288:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x128d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4754bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c80"} true;
call arbitrary_func();

label_0x1292:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x1297:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x129c:
t1_47 := RCX;
t2_48 := RAX;
RCX := PLUS_64(RCX, t2_48);
CF := bool2bv(LT_64(RCX, t1_47));
OF := AND_1((bool2bv((t1_47[64:63]) == (t2_48[64:63]))), (XOR_1((t1_47[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_47)), t2_48)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x129f:
RAX := RCX;

label_0x12a2:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x12a7:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x12ac:
t_53 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), RAX);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), RAX));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), RAX)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_53)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_53, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)), 2bv64)), (XOR_64((RSHIFT_64(t_53, 4bv64)), t_53)))))[1:0]));
SF := t_53[64:63];
ZF := bool2bv(0bv64 == t_53);

label_0x12b1:
if (bv2bool(NOT_1((OR_1(CF, ZF))))) {
  goto label_0x12b6;
}

label_0x12b3:
assume false;

label_0x12b4:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_5;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x12b6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 32bv64));

label_0x12bb:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x12c0:
t_57 := RCX;
RCX := MINUS_64(RCX, RAX);
CF := bool2bv(LT_64(t_57, RAX));
OF := AND_64((XOR_64(t_57, RAX)), (XOR_64(t_57, RCX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t_57)), RAX)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x12c3:
RAX := RCX;

label_0x12c6:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x12cb:
t_61 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 512bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 512bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 512bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_61)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_61, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 512bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)), 2bv64)), (XOR_64((RSHIFT_64(t_61, 4bv64)), t_61)))))[1:0]));
SF := t_61[64:63];
ZF := bool2bv(0bv64 == t_61);

label_0x12d4:
if (bv2bool(CF)) {
  goto label_0x136b;
}

label_0x12da:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x12df:
origDEST_65 := RAX;
origCOUNT_66 := AND_64(6bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(6bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), CF, LSHIFT_64(origDEST_65, (MINUS_64(64bv64, origCOUNT_66)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_66 == 1bv64)), origDEST_65[64:63], unconstrained_6));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_66 == 0bv64)), AF, unconstrained_7);

label_0x12e3:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x12e8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x12ed:
origDEST_71 := RAX;
origCOUNT_72 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), CF, LSHIFT_64(origDEST_71, (MINUS_64(64bv64, origCOUNT_72)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_72 == 1bv64)), origDEST_71[64:63], unconstrained_8));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_72 == 0bv64)), AF, unconstrained_9);

label_0x12f1:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x12f6:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x12fb:
RCX := LOAD_LE_64(mem, PLUS_64((PLUS_64(7486bv64, 4866bv64)), 0bv64));

label_0x1302:
t1_77 := RCX;
t2_78 := RAX;
RCX := PLUS_64(RCX, t2_78);
CF := bool2bv(LT_64(RCX, t1_77));
OF := AND_1((bool2bv((t1_77[64:63]) == (t2_78[64:63]))), (XOR_1((t1_77[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_77)), t2_78)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1305:
RAX := RCX;

label_0x1308:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x130d:
goto label_0x132a;

label_0x130f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x1314:
t_83 := RAX;
RAX := MINUS_64(RAX, 1bv64);
OF := AND_64((XOR_64(t_83, 1bv64)), (XOR_64(t_83, RAX)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t_83)), 1bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1317:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x131c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1321:
t1_87 := RAX;
t2_88 := 8bv64;
RAX := PLUS_64(RAX, t2_88);
CF := bool2bv(LT_64(RAX, t1_87));
OF := AND_1((bool2bv((t1_87[64:63]) == (t2_88[64:63]))), (XOR_1((t1_87[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_87)), t2_88)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1325:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x132a:
t_93 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))), t_93)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_93, (LOAD_LE_64(mem, PLUS_64(RSP, 56bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)), 2bv64)), (XOR_64((RSHIFT_64(t_93, 4bv64)), t_93)))))[1:0]));
SF := t_93[64:63];
ZF := bool2bv(0bv64 == t_93);

label_0x1330:
if (bv2bool(ZF)) {
  goto label_0x1340;
}

label_0x1332:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1337:
t_97 := MINUS_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32);
CF := bool2bv(LT_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32));
OF := AND_64((XOR_64((LOAD_LE_64(mem, RAX)), 4294967295bv32 ++ 4294967295bv32)), (XOR_64((LOAD_LE_64(mem, RAX)), t_97)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_97, (LOAD_LE_64(mem, RAX)))), 4294967295bv32 ++ 4294967295bv32)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)), 2bv64)), (XOR_64((RSHIFT_64(t_97, 4bv64)), t_97)))))[1:0]));
SF := t_97[64:63];
ZF := bool2bv(0bv64 == t_97);

label_0x133b:
if (bv2bool(ZF)) {
  goto label_0x133e;
}

label_0x133d:
assume false;

label_0x133e:
goto label_0x130f;

label_0x1340:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1345:
RAX := AND_64(RAX, 4294967295bv32 ++ 4294966784bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_10;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x134b:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x1350:
t1_103 := RCX;
t2_104 := RAX;
RCX := PLUS_64(RCX, t2_104);
CF := bool2bv(LT_64(RCX, t1_103));
OF := AND_1((bool2bv((t1_103[64:63]) == (t2_104[64:63]))), (XOR_1((t1_103[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_103)), t2_104)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x1353:
RAX := RCX;

label_0x1356:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RAX);

label_0x135b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1360:
RAX := AND_64(RAX, 511bv64);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1366:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RAX);

label_0x136b:
t_111 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))), t_111)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_111, (LOAD_LE_64(mem, PLUS_64(RSP, 104bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)), 2bv64)), (XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)), 2bv64)), (XOR_64((RSHIFT_64(t_111, 4bv64)), t_111)))))[1:0]));
SF := t_111[64:63];
ZF := bool2bv(0bv64 == t_111);

label_0x1371:
if (bv2bool(OR_1(CF, ZF))) {
  goto label_0x1382;
}

label_0x1373:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x1378:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x137d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4994bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1c80"} true;
call arbitrary_func();

label_0x1382:
t1_115 := RSP;
t2_116 := 88bv64;
RSP := PLUS_64(RSP, t2_116);
CF := bool2bv(LT_64(RSP, t1_115));
OF := AND_1((bool2bv((t1_115[64:63]) == (t2_116[64:63]))), (XOR_1((t1_115[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_115)), t2_116)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x1386:

ra_121 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_18,origCOUNT_66,origCOUNT_72,origDEST_17,origDEST_65,origDEST_71,ra_121,t1_103,t1_115,t1_27,t1_47,t1_77,t1_87,t2_104,t2_116,t2_28,t2_48,t2_78,t2_88,t_1,t_111,t_13,t_23,t_35,t_39,t_43,t_5,t_53,t_57,t_61,t_83,t_9,t_93,t_97;

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
var RAX: bv64;
var RCX: bv64;
var RDX: bv64;
var RSP: bv64;
var SF: bv1;
var ZF: bv1;
var mem: [bv64]bv8;
var origCOUNT_18: bv64;
var origCOUNT_66: bv64;
var origCOUNT_72: bv64;
var origDEST_17: bv64;
var origDEST_65: bv64;
var origDEST_71: bv64;
var ra_121: bv64;
var t1_103: bv64;
var t1_115: bv64;
var t1_27: bv64;
var t1_47: bv64;
var t1_77: bv64;
var t1_87: bv64;
var t2_104: bv64;
var t2_116: bv64;
var t2_28: bv64;
var t2_48: bv64;
var t2_78: bv64;
var t2_88: bv64;
var t_1: bv64;
var t_111: bv64;
var t_13: bv64;
var t_23: bv64;
var t_35: bv64;
var t_39: bv64;
var t_43: bv64;
var t_5: bv64;
var t_53: bv64;
var t_57: bv64;
var t_61: bv64;
var t_83: bv64;
var t_9: bv64;
var t_93: bv64;
var t_97: bv64;


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
