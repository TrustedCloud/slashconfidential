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
axiom _function_addr_low == 14480bv64;
axiom _function_addr_high == 16016bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x3890:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), R9[32:0]);

label_0x3895:
mem := STORE_LE_64(mem, PLUS_64(RSP, 24bv64), R8);

label_0x389a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 16bv64), RDX);

label_0x389f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x38a4:
t_1 := RSP;
RSP := MINUS_64(RSP, 152bv64);
CF := bool2bv(LT_64(t_1, 152bv64));
OF := AND_64((XOR_64(t_1, 152bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 152bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x38ab:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x38b2:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x38b9:
t_5 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_5, (RAX[32:0])));
OF := AND_32((XOR_32(t_5, (RAX[32:0]))), (XOR_32(t_5, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_5)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x38bb:
RAX := (0bv32 ++ RCX[32:0]);

label_0x38bd:
t_9 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_9[32:31]) == (1bv32[32:31]))), (XOR_1((t_9[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_9)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x38bf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 68bv64), RAX[32:0]);

label_0x38c3:
t_13 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 2bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 2bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), 2bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))), t_13)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_13, (LOAD_LE_32(mem, PLUS_64(RSP, 68bv64))))), 2bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)), 2bv32)), (XOR_32((RSHIFT_32(t_13, 4bv32)), t_13)))))[1:0]));
SF := t_13[32:31];
ZF := bool2bv(0bv32 == t_13);

label_0x38c8:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x38cf;
}

label_0x38ca:
goto label_0x3e7c;

label_0x38cf:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), 0bv32);

label_0x38d7:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)))));

label_0x38dc:
RCX := PLUS_64((PLUS_64(0bv64, 14563bv64)), 0bv64)[64:0];

label_0x38e3:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 68bv64)));

label_0x38e7:
t_17 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))), (RDX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))), (RDX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))), (RDX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))), t_17)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_17, (LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64))))))), (RDX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)), 2bv32)), (XOR_32((RSHIFT_32(t_17, 4bv32)), t_17)))))[1:0]));
SF := t_17[32:31];
ZF := bool2bv(0bv32 == t_17);

label_0x38ea:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x38f8;
}

label_0x38ec:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)));

label_0x38f0:
t_21 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_21[32:31]) == (1bv32[32:31]))), (XOR_1((t_21[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_21)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x38f2:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x38f6:
goto label_0x38d7;

label_0x38f8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)));

label_0x38fc:
t_25 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_25, 1bv32)), (XOR_32(t_25, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_25)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x38fe:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x3902:
goto label_0x390e;

label_0x3904:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)));

label_0x3908:
t_29 := RAX[32:0];
RAX := (0bv32 ++ MINUS_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32(t_29, 1bv32)), (XOR_32(t_29, (RAX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_29)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x390a:
mem := STORE_LE_32(mem, PLUS_64(RSP, 60bv64), RAX[32:0]);

label_0x390e:
t_33 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), 0bv32)), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))), t_33)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_33, (LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)), 2bv32)), (XOR_32((RSHIFT_32(t_33, 4bv32)), t_33)))))[1:0]));
SF := t_33[32:31];
ZF := bool2bv(0bv32 == t_33);

label_0x3913:
if (bv2bool(XOR_1(SF, OF))) {
  goto label_0x3e7c;
}

label_0x3919:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 60bv64)))));

label_0x391e:
RCX := PLUS_64((PLUS_64(0bv64, 14629bv64)), 0bv64)[64:0];

label_0x3925:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x3928:
mem := STORE_LE_32(mem, PLUS_64(RSP, 56bv64), RAX[32:0]);

label_0x392c:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3930:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x3937:
t1_37 := RCX[32:0];
t2_38 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_38));
CF := bool2bv(LT_32((RCX[32:0]), t1_37));
OF := AND_1((bool2bv((t1_37[32:31]) == (t2_38[32:31]))), (XOR_1((t1_37[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_37)), t2_38)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3939:
RAX := (0bv32 ++ RCX[32:0]);

label_0x393b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x393f:
RAX := (0bv32 ++ 0bv32);
AF := unconstrained_1;
ZF := 1bv1;
PF := 1bv1;
OF := 0bv1;
CF := 0bv1;
SF := 0bv1;

label_0x3941:
t_43 := MINUS_32((RAX[32:0]), 1bv32);
CF := bool2bv(LT_32((RAX[32:0]), 1bv32));
OF := AND_32((XOR_32((RAX[32:0]), 1bv32)), (XOR_32((RAX[32:0]), t_43)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_43, (RAX[32:0]))), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)), 2bv32)), (XOR_32((RSHIFT_32(t_43, 4bv32)), t_43)))))[1:0]));
SF := t_43[32:31];
ZF := bool2bv(0bv32 == t_43);

label_0x3944:
if (bv2bool(ZF)) {
  goto label_0x3e77;
}

label_0x394a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x3951:
t_47 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_47)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_47, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)), 2bv32)), (XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)), 2bv32)), (XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)))))[1:0]));
SF := t_47[32:31];
ZF := bool2bv(0bv32 == t_47);

label_0x3955:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x395c;
}

label_0x3957:
goto label_0x3e77;

label_0x395c:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)))));

label_0x3961:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3969:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x396c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RAX[32:0]);

label_0x3970:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3974:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3978:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x397f:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3983:
t1_51 := RCX[32:0];
t2_52 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_52));
CF := bool2bv(LT_32((RCX[32:0]), t1_51));
OF := AND_1((bool2bv((t1_51[32:31]) == (t2_52[32:31]))), (XOR_1((t1_51[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_51)), t2_52)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3985:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3987:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x398b:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x398f:
t_57 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_57, (RCX[32:0])));
OF := AND_32((XOR_32(t_57, (RCX[32:0]))), (XOR_32(t_57, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_57)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x3991:
RCX := (0bv32 ++ RDX[32:0]);

label_0x3993:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x3996:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x399e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))));

label_0x39a1:
t1_61 := RCX[32:0];
t2_62 := LOAD_LE_32(mem, PLUS_64(RSP, 208bv64));
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_62));
CF := bool2bv(LT_32((RCX[32:0]), t1_61));
OF := AND_1((bool2bv((t1_61[32:31]) == (t2_62[32:31]))), (XOR_1((t1_61[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_61)), t2_62)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x39a8:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x39b0:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RDX);

label_0x39b5:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x39bc:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RDX[32:0]);

label_0x39c0:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x39c8:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x39d0:
RDX := (0bv32 ++ RAX[32:0]);

label_0x39d2:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 14807bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x39d7"} true;
call arbitrary_func();

label_0x39d7:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x39da:
t_67 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)), 2bv32)), (XOR_32((RSHIFT_32(t_67, 4bv32)), t_67)))))[1:0]));
SF := t_67[32:31];
ZF := bool2bv(0bv32 == t_67);

label_0x39dc:
if (bv2bool(ZF)) {
  goto label_0x3a91;
}

label_0x39e2:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x39e6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x39ea:
t_71 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_71, (RAX[32:0])));
OF := AND_32((XOR_32(t_71, (RAX[32:0]))), (XOR_32(t_71, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_71)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x39ec:
RAX := (0bv32 ++ RCX[32:0]);

label_0x39ee:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x39f0:
origDEST_75 := RAX;
origCOUNT_76 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), CF, RSHIFT_64(origDEST_75, (MINUS_64(64bv64, origCOUNT_76)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_76 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_76 == 0bv64)), AF, unconstrained_4);

label_0x39f4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x39fc:
t1_81 := RCX;
t2_82 := RAX;
RCX := PLUS_64(RCX, t2_82);
CF := bool2bv(LT_64(RCX, t1_81));
OF := AND_1((bool2bv((t1_81[64:63]) == (t2_82[64:63]))), (XOR_1((t1_81[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_81)), t2_82)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x39ff:
mem := STORE_LE_64(mem, PLUS_64(RSP, 120bv64), RCX);

label_0x3a04:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3a09:
origDEST_87 := RAX;
origCOUNT_88 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), CF, RSHIFT_64(origDEST_87, (MINUS_64(64bv64, origCOUNT_88)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_88 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_88 == 0bv64)), AF, unconstrained_6);

label_0x3a0d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3a15:
t1_93 := RCX;
t2_94 := RAX;
RCX := PLUS_64(RCX, t2_94);
CF := bool2bv(LT_64(RCX, t1_93));
OF := AND_1((bool2bv((t1_93[64:63]) == (t2_94[64:63]))), (XOR_1((t1_93[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_93)), t2_94)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3a18:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RCX);

label_0x3a1d:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3a22:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_7;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3a28:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3a2d:
t_101 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_8;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)), 2bv64)), (XOR_64((RSHIFT_64(t_101, 4bv64)), t_101)))))[1:0]));
SF := t_101[64:63];
ZF := bool2bv(0bv64 == t_101);

label_0x3a30:
if (bv2bool(ZF)) {
  goto label_0x3a33;
}

label_0x3a32:
assume false;

label_0x3a33:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3a38:
origDEST_105 := RAX;
origCOUNT_106 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), CF, LSHIFT_64(origDEST_105, (MINUS_64(64bv64, origCOUNT_106)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_106 == 1bv64)), origDEST_105[64:63], unconstrained_9));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_106 == 0bv64)), AF, unconstrained_10);

label_0x3a3c:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3a43:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3a47:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3a4c:
origDEST_111 := RCX;
origCOUNT_112 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), CF, LSHIFT_64(origDEST_111, (MINUS_64(64bv64, origCOUNT_112)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_112 == 1bv64)), origDEST_111[64:63], unconstrained_11));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_112 == 0bv64)), AF, unconstrained_12);

label_0x3a50:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_13;
SF := unconstrained_14;
AF := unconstrained_15;
PF := unconstrained_16;

label_0x3a54:
if (bv2bool(CF)) {
  goto label_0x3a57;
}

label_0x3a56:
assume false;

label_0x3a57:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x3a5c:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 120bv64));

label_0x3a61:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x3a63:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3a65:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3a69:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3a6d:
t_117 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_117, (RAX[32:0])));
OF := AND_32((XOR_32(t_117, (RAX[32:0]))), (XOR_32(t_117, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_117)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3a6f:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3a71:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3a75:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x3a7c:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3a80:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[32:0]);

label_0x3a84:
t_121 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_121)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_121, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)), 2bv32)), (XOR_32((RSHIFT_32(t_121, 4bv32)), t_121)))))[1:0]));
SF := t_121[32:31];
ZF := bool2bv(0bv32 == t_121);

label_0x3a88:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x3a8c;
}

label_0x3a8a:
goto label_0x3a91;

label_0x3a8c:
goto label_0x3978;

label_0x3a91:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3a96:
origDEST_125 := RAX;
origCOUNT_126 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), CF, RSHIFT_64(origDEST_125, (MINUS_64(64bv64, origCOUNT_126)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_126 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_17));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_126 == 0bv64)), AF, unconstrained_18);

label_0x3a9a:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3aa2:
t1_131 := RCX;
t2_132 := RAX;
RCX := PLUS_64(RCX, t2_132);
CF := bool2bv(LT_64(RCX, t1_131));
OF := AND_1((bool2bv((t1_131[64:63]) == (t2_132[64:63]))), (XOR_1((t1_131[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_131)), t2_132)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3aa5:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RCX);

label_0x3aaa:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3aaf:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_19;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3ab5:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3aba:
t_139 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_20;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)), 2bv64)), (XOR_64((RSHIFT_64(t_139, 4bv64)), t_139)))))[1:0]));
SF := t_139[64:63];
ZF := bool2bv(0bv64 == t_139);

label_0x3abd:
if (bv2bool(ZF)) {
  goto label_0x3ac0;
}

label_0x3abf:
assume false;

label_0x3ac0:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3ac5:
origDEST_143 := RAX;
origCOUNT_144 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), CF, LSHIFT_64(origDEST_143, (MINUS_64(64bv64, origCOUNT_144)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_144 == 1bv64)), origDEST_143[64:63], unconstrained_21));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_144 == 0bv64)), AF, unconstrained_22);

label_0x3ac9:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3ad0:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3ad4:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3ad9:
origDEST_149 := RCX;
origCOUNT_150 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), CF, LSHIFT_64(origDEST_149, (MINUS_64(64bv64, origCOUNT_150)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_150 == 1bv64)), origDEST_149[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_150 == 0bv64)), AF, unconstrained_24);

label_0x3add:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_25;
SF := unconstrained_26;
AF := unconstrained_27;
PF := unconstrained_28;

label_0x3ae1:
if (bv2bool(CF)) {
  goto label_0x3ae4;
}

label_0x3ae3:
assume false;

label_0x3ae4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x3ae9:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3aed:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3aef:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3af3:
t_155 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_155[32:31]) == (1bv32[32:31]))), (XOR_1((t_155[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_155)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3af5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x3af9:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x3b00:
t_159 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_159)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_159, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)), 2bv32)), (XOR_32((RSHIFT_32(t_159, 4bv32)), t_159)))))[1:0]));
SF := t_159[32:31];
ZF := bool2bv(0bv32 == t_159);

label_0x3b04:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3b0b;
}

label_0x3b06:
goto label_0x3e77;

label_0x3b0b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)))));

label_0x3b10:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3b18:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x3b1b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RAX[32:0]);

label_0x3b1f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3b23:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3b27:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x3b2e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3b32:
t1_163 := RCX[32:0];
t2_164 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_164));
CF := bool2bv(LT_32((RCX[32:0]), t1_163));
OF := AND_1((bool2bv((t1_163[32:31]) == (t2_164[32:31]))), (XOR_1((t1_163[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_163)), t2_164)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3b34:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3b36:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3b3a:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3b3e:
t_169 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_169, (RCX[32:0])));
OF := AND_32((XOR_32(t_169, (RCX[32:0]))), (XOR_32(t_169, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_169)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x3b40:
RCX := (0bv32 ++ RDX[32:0]);

label_0x3b42:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x3b45:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3b4d:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))));

label_0x3b50:
t1_173 := RCX[32:0];
t2_174 := LOAD_LE_32(mem, PLUS_64(RSP, 208bv64));
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_174));
CF := bool2bv(LT_32((RCX[32:0]), t1_173));
OF := AND_1((bool2bv((t1_173[32:31]) == (t2_174[32:31]))), (XOR_1((t1_173[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_173)), t2_174)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3b57:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x3b5f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RDX);

label_0x3b64:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x3b6b:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RDX[32:0]);

label_0x3b6f:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3b77:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x3b7f:
RDX := (0bv32 ++ RAX[32:0]);

label_0x3b81:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 15238bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3b86"} true;
call arbitrary_func();

label_0x3b86:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3b89:
t_179 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_29;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)), 2bv32)), (XOR_32((RSHIFT_32(t_179, 4bv32)), t_179)))))[1:0]));
SF := t_179[32:31];
ZF := bool2bv(0bv32 == t_179);

label_0x3b8b:
if (bv2bool(ZF)) {
  goto label_0x3c46;
}

label_0x3b91:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3b95:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3b99:
t_183 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_183, (RAX[32:0])));
OF := AND_32((XOR_32(t_183, (RAX[32:0]))), (XOR_32(t_183, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_183)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3b9b:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3b9d:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3b9f:
origDEST_187 := RAX;
origCOUNT_188 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, RSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_30));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_31);

label_0x3ba3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3bab:
t1_193 := RCX;
t2_194 := RAX;
RCX := PLUS_64(RCX, t2_194);
CF := bool2bv(LT_64(RCX, t1_193));
OF := AND_1((bool2bv((t1_193[64:63]) == (t2_194[64:63]))), (XOR_1((t1_193[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_193)), t2_194)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3bae:
mem := STORE_LE_64(mem, PLUS_64(RSP, 128bv64), RCX);

label_0x3bb6:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3bbb:
origDEST_199 := RAX;
origCOUNT_200 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), CF, RSHIFT_64(origDEST_199, (MINUS_64(64bv64, origCOUNT_200)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_200 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_32));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_200 == 0bv64)), AF, unconstrained_33);

label_0x3bbf:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3bc7:
t1_205 := RCX;
t2_206 := RAX;
RCX := PLUS_64(RCX, t2_206);
CF := bool2bv(LT_64(RCX, t1_205));
OF := AND_1((bool2bv((t1_205[64:63]) == (t2_206[64:63]))), (XOR_1((t1_205[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_205)), t2_206)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3bca:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RCX);

label_0x3bcf:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3bd4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3bda:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3bdf:
t_213 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_35;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)), 2bv64)), (XOR_64((RSHIFT_64(t_213, 4bv64)), t_213)))))[1:0]));
SF := t_213[64:63];
ZF := bool2bv(0bv64 == t_213);

label_0x3be2:
if (bv2bool(ZF)) {
  goto label_0x3be5;
}

label_0x3be4:
assume false;

label_0x3be5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3bea:
origDEST_217 := RAX;
origCOUNT_218 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), CF, LSHIFT_64(origDEST_217, (MINUS_64(64bv64, origCOUNT_218)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_218 == 1bv64)), origDEST_217[64:63], unconstrained_36));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_218 == 0bv64)), AF, unconstrained_37);

label_0x3bee:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3bf5:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3bf9:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3bfe:
origDEST_223 := RCX;
origCOUNT_224 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), CF, LSHIFT_64(origDEST_223, (MINUS_64(64bv64, origCOUNT_224)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_224 == 1bv64)), origDEST_223[64:63], unconstrained_38));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_224 == 0bv64)), AF, unconstrained_39);

label_0x3c02:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_40;
SF := unconstrained_41;
AF := unconstrained_42;
PF := unconstrained_43;

label_0x3c06:
if (bv2bool(CF)) {
  goto label_0x3c09;
}

label_0x3c08:
assume false;

label_0x3c09:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x3c0e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 128bv64));

label_0x3c16:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x3c18:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3c1a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3c1e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3c22:
t_229 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_229, (RAX[32:0])));
OF := AND_32((XOR_32(t_229, (RAX[32:0]))), (XOR_32(t_229, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_229)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3c24:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3c26:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3c2a:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x3c31:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3c35:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[32:0]);

label_0x3c39:
t_233 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_233)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_233, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_233, 4bv32)), t_233)), 2bv32)), (XOR_32((RSHIFT_32(t_233, 4bv32)), t_233)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_233, 4bv32)), t_233)), 2bv32)), (XOR_32((RSHIFT_32(t_233, 4bv32)), t_233)))))[1:0]));
SF := t_233[32:31];
ZF := bool2bv(0bv32 == t_233);

label_0x3c3d:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x3c41;
}

label_0x3c3f:
goto label_0x3c46;

label_0x3c41:
goto label_0x3b27;

label_0x3c46:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3c4b:
origDEST_237 := RAX;
origCOUNT_238 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), CF, RSHIFT_64(origDEST_237, (MINUS_64(64bv64, origCOUNT_238)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_238 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_44));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_238 == 0bv64)), AF, unconstrained_45);

label_0x3c4f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3c57:
t1_243 := RCX;
t2_244 := RAX;
RCX := PLUS_64(RCX, t2_244);
CF := bool2bv(LT_64(RCX, t1_243));
OF := AND_1((bool2bv((t1_243[64:63]) == (t2_244[64:63]))), (XOR_1((t1_243[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_243)), t2_244)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3c5a:
mem := STORE_LE_64(mem, PLUS_64(RSP, 96bv64), RCX);

label_0x3c5f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3c64:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3c6a:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3c6f:
t_251 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_47;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)), 2bv64)), (XOR_64((RSHIFT_64(t_251, 4bv64)), t_251)))))[1:0]));
SF := t_251[64:63];
ZF := bool2bv(0bv64 == t_251);

label_0x3c72:
if (bv2bool(ZF)) {
  goto label_0x3c75;
}

label_0x3c74:
assume false;

label_0x3c75:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3c7a:
origDEST_255 := RAX;
origCOUNT_256 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), CF, LSHIFT_64(origDEST_255, (MINUS_64(64bv64, origCOUNT_256)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_256 == 1bv64)), origDEST_255[64:63], unconstrained_48));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_256 == 0bv64)), AF, unconstrained_49);

label_0x3c7e:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3c85:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3c89:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3c8e:
origDEST_261 := RCX;
origCOUNT_262 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), CF, LSHIFT_64(origDEST_261, (MINUS_64(64bv64, origCOUNT_262)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_262 == 1bv64)), origDEST_261[64:63], unconstrained_50));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_262 == 0bv64)), AF, unconstrained_51);

label_0x3c92:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_52;
SF := unconstrained_53;
AF := unconstrained_54;
PF := unconstrained_55;

label_0x3c96:
if (bv2bool(CF)) {
  goto label_0x3c99;
}

label_0x3c98:
assume false;

label_0x3c99:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 96bv64));

label_0x3c9e:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3ca2:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3ca4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3ca8:
t_267 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_267[32:31]) == (1bv32[32:31]))), (XOR_1((t_267[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_267)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3caa:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x3cae:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 200bv64)));

label_0x3cb5:
t_271 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))), t_271)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_271, (LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_271, 4bv32)), t_271)), 2bv32)), (XOR_32((RSHIFT_32(t_271, 4bv32)), t_271)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_271, 4bv32)), t_271)), 2bv32)), (XOR_32((RSHIFT_32(t_271, 4bv32)), t_271)))))[1:0]));
SF := t_271[32:31];
ZF := bool2bv(0bv32 == t_271);

label_0x3cb9:
if (bv2bool(OR_1(ZF, (XOR_1(SF, OF))))) {
  goto label_0x3cc0;
}

label_0x3cbb:
goto label_0x3e77;

label_0x3cc0:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)))));

label_0x3cc5:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3ccd:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 2bv64)))));

label_0x3cd0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 64bv64), RAX[32:0]);

label_0x3cd4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3cd8:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3cdc:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 208bv64)));

label_0x3ce3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3ce7:
t1_275 := RCX[32:0];
t2_276 := RAX[32:0];
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_276));
CF := bool2bv(LT_32((RCX[32:0]), t1_275));
OF := AND_1((bool2bv((t1_275[32:31]) == (t2_276[32:31]))), (XOR_1((t1_275[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_275)), t2_276)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3ce9:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3ceb:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3cef:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3cf3:
t_281 := RDX[32:0];
RDX := (0bv32 ++ MINUS_32((RDX[32:0]), (RCX[32:0])));
CF := bool2bv(LT_32(t_281, (RCX[32:0])));
OF := AND_32((XOR_32(t_281, (RCX[32:0]))), (XOR_32(t_281, (RDX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RDX[32:0]), t_281)), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RDX[32:0]), 4bv32)), (RDX[32:0]))))))[1:0]));
SF := RDX[32:0][32:31];
ZF := bool2bv(0bv32 == (RDX[32:0]));

label_0x3cf5:
RCX := (0bv32 ++ RDX[32:0]);

label_0x3cf7:
RCX := (ITE_64(bv2bool(RCX[32:0][32:31]) ,(1bv32 ++ RCX[32:0]) ,(0bv32 ++ RCX[32:0])));

label_0x3cfa:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3d02:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RDX, (LSHIFT_64(RCX, 2bv64)))));

label_0x3d05:
t1_285 := RCX[32:0];
t2_286 := LOAD_LE_32(mem, PLUS_64(RSP, 208bv64));
RCX := (0bv32 ++ PLUS_32((RCX[32:0]), t2_286));
CF := bool2bv(LT_32((RCX[32:0]), t1_285));
OF := AND_1((bool2bv((t1_285[32:31]) == (t2_286[32:31]))), (XOR_1((t1_285[32:31]), (RCX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t1_285)), t2_286)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3d0c:
RDX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x3d14:
mem := STORE_LE_64(mem, PLUS_64(RSP, 40bv64), RDX);

label_0x3d19:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 184bv64)));

label_0x3d20:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RDX[32:0]);

label_0x3d24:
R9 := LOAD_LE_64(mem, PLUS_64(RSP, 176bv64));

label_0x3d2c:
R8 := LOAD_LE_64(mem, PLUS_64(RSP, 168bv64));

label_0x3d34:
RDX := (0bv32 ++ RAX[32:0]);

label_0x3d36:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 15675bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x3d3b"} true;
call arbitrary_func();

label_0x3d3b:
RAX := (0bv32 ++ (0bv24 ++ RAX[32:0][8:0]));

label_0x3d3e:
t_291 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_56;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)), 2bv32)), (XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)), 2bv32)), (XOR_32((RSHIFT_32(t_291, 4bv32)), t_291)))))[1:0]));
SF := t_291[32:31];
ZF := bool2bv(0bv32 == t_291);

label_0x3d40:
if (bv2bool(ZF)) {
  goto label_0x3dfb;
}

label_0x3d46:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3d4a:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3d4e:
t_295 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_295, (RAX[32:0])));
OF := AND_32((XOR_32(t_295, (RAX[32:0]))), (XOR_32(t_295, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_295)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3d50:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3d52:
RAX := (ITE_64(bv2bool(RAX[32:0][32:31]) ,(1bv32 ++ RAX[32:0]) ,(0bv32 ++ RAX[32:0])));

label_0x3d54:
origDEST_299 := RAX;
origCOUNT_300 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), CF, RSHIFT_64(origDEST_299, (MINUS_64(64bv64, origCOUNT_300)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_300 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_57));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_300 == 0bv64)), AF, unconstrained_58);

label_0x3d58:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3d60:
t1_305 := RCX;
t2_306 := RAX;
RCX := PLUS_64(RCX, t2_306);
CF := bool2bv(LT_64(RCX, t1_305));
OF := AND_1((bool2bv((t1_305[64:63]) == (t2_306[64:63]))), (XOR_1((t1_305[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_305)), t2_306)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3d63:
mem := STORE_LE_64(mem, PLUS_64(RSP, 136bv64), RCX);

label_0x3d6b:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3d70:
origDEST_311 := RAX;
origCOUNT_312 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), CF, RSHIFT_64(origDEST_311, (MINUS_64(64bv64, origCOUNT_312)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_312 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_59));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_312 == 0bv64)), AF, unconstrained_60);

label_0x3d74:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3d7c:
t1_317 := RCX;
t2_318 := RAX;
RCX := PLUS_64(RCX, t2_318);
CF := bool2bv(LT_64(RCX, t1_317));
OF := AND_1((bool2bv((t1_317[64:63]) == (t2_318[64:63]))), (XOR_1((t1_317[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_317)), t2_318)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3d7f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 104bv64), RCX);

label_0x3d84:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3d89:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_61;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3d8f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3d94:
t_325 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_62;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)), 2bv64)), (XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)), 2bv64)), (XOR_64((RSHIFT_64(t_325, 4bv64)), t_325)))))[1:0]));
SF := t_325[64:63];
ZF := bool2bv(0bv64 == t_325);

label_0x3d97:
if (bv2bool(ZF)) {
  goto label_0x3d9a;
}

label_0x3d99:
assume false;

label_0x3d9a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3d9f:
origDEST_329 := RAX;
origCOUNT_330 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), CF, LSHIFT_64(origDEST_329, (MINUS_64(64bv64, origCOUNT_330)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_330 == 1bv64)), origDEST_329[64:63], unconstrained_63));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_330 == 0bv64)), AF, unconstrained_64);

label_0x3da3:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3daa:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3dae:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3db3:
origDEST_335 := RCX;
origCOUNT_336 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), CF, LSHIFT_64(origDEST_335, (MINUS_64(64bv64, origCOUNT_336)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_336 == 1bv64)), origDEST_335[64:63], unconstrained_65));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_336 == 0bv64)), AF, unconstrained_66);

label_0x3db7:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_67;
SF := unconstrained_68;
AF := unconstrained_69;
PF := unconstrained_70;

label_0x3dbb:
if (bv2bool(CF)) {
  goto label_0x3dbe;
}

label_0x3dbd:
assume false;

label_0x3dbe:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 104bv64));

label_0x3dc3:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 136bv64));

label_0x3dcb:
RCX := (0bv32 ++ LOAD_LE_32(mem, RCX));

label_0x3dcd:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3dcf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3dd3:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)));

label_0x3dd7:
t_341 := RCX[32:0];
RCX := (0bv32 ++ MINUS_32((RCX[32:0]), (RAX[32:0])));
CF := bool2bv(LT_32(t_341, (RAX[32:0])));
OF := AND_32((XOR_32(t_341, (RAX[32:0]))), (XOR_32(t_341, (RCX[32:0]))))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RCX[32:0]), t_341)), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RCX[32:0]), 4bv32)), (RCX[32:0]))))))[1:0]));
SF := RCX[32:0][32:31];
ZF := bool2bv(0bv32 == (RCX[32:0]));

label_0x3dd9:
RAX := (0bv32 ++ RCX[32:0]);

label_0x3ddb:
mem := STORE_LE_32(mem, PLUS_64(RSP, 48bv64), RAX[32:0]);

label_0x3ddf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 192bv64)));

label_0x3de6:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 56bv64)));

label_0x3dea:
RAX := (0bv32 ++ PLUS_64((PLUS_64(RAX, RCX)), 4294967295bv32 ++ 4294967295bv32)[32:0]);

label_0x3dee:
t_345 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))), t_345)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_345, (LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)), 2bv32)), (XOR_32((RSHIFT_32(t_345, 4bv32)), t_345)))))[1:0]));
SF := t_345[32:31];
ZF := bool2bv(0bv32 == t_345);

label_0x3df2:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x3df6;
}

label_0x3df4:
goto label_0x3dfb;

label_0x3df6:
goto label_0x3cdc;

label_0x3dfb:
RAX := (ITE_64(bv2bool(LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))[32:31]) ,(1bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64))) ,(0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 48bv64)))));

label_0x3e00:
origDEST_349 := RAX;
origCOUNT_350 := AND_64(2bv64, (MINUS_64(64bv64, 1bv64)));
RAX := LSHIFT_64(RAX, (AND_64(2bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), CF, RSHIFT_64(origDEST_349, (MINUS_64(64bv64, origCOUNT_350)))[1:0]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_350 == 1bv64)), XOR_1((RAX[64:63]), CF), unconstrained_71));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_350 == 0bv64)), AF, unconstrained_72);

label_0x3e04:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 160bv64));

label_0x3e0c:
t1_355 := RCX;
t2_356 := RAX;
RCX := PLUS_64(RCX, t2_356);
CF := bool2bv(LT_64(RCX, t1_355));
OF := AND_1((bool2bv((t1_355[64:63]) == (t2_356[64:63]))), (XOR_1((t1_355[64:63]), (RCX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RCX, t1_355)), t2_356)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0]));
SF := RCX[64:63];
ZF := bool2bv(0bv64 == RCX);

label_0x3e0f:
mem := STORE_LE_64(mem, PLUS_64(RSP, 112bv64), RCX);

label_0x3e14:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3e19:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_73;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x3e1f:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x3e24:
t_363 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_74;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)), 2bv64)), (XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)), 2bv64)), (XOR_64((RSHIFT_64(t_363, 4bv64)), t_363)))))[1:0]));
SF := t_363[64:63];
ZF := bool2bv(0bv64 == t_363);

label_0x3e27:
if (bv2bool(ZF)) {
  goto label_0x3e2a;
}

label_0x3e29:
assume false;

label_0x3e2a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3e2f:
origDEST_367 := RAX;
origCOUNT_368 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), CF, LSHIFT_64(origDEST_367, (MINUS_64(64bv64, origCOUNT_368)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_368 == 1bv64)), origDEST_367[64:63], unconstrained_75));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_368 == 0bv64)), AF, unconstrained_76);

label_0x3e33:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x3e3a:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x3e3e:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3e43:
origDEST_373 := RCX;
origCOUNT_374 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), CF, LSHIFT_64(origDEST_373, (MINUS_64(64bv64, origCOUNT_374)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_374 == 1bv64)), origDEST_373[64:63], unconstrained_77));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_374 == 0bv64)), AF, unconstrained_78);

label_0x3e47:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_79;
SF := unconstrained_80;
AF := unconstrained_81;
PF := unconstrained_82;

label_0x3e4b:
if (bv2bool(CF)) {
  goto label_0x3e4e;
}

label_0x3e4d:
assume false;

label_0x3e4e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x3e53:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 64bv64)));

label_0x3e57:
mem := STORE_LE_32(mem, RAX, RCX[32:0]);

label_0x3e59:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 52bv64)));

label_0x3e5d:
t_379 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_379[32:31]) == (1bv32[32:31]))), (XOR_1((t_379[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_379)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x3e5f:
mem := STORE_LE_32(mem, PLUS_64(RSP, 52bv64), RAX[32:0]);

label_0x3e63:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 216bv64));

label_0x3e6b:
t_383 := MINUS_32((LOAD_LE_32(mem, RAX)), 0bv32);
CF := bool2bv(LT_32((LOAD_LE_32(mem, RAX)), 0bv32));
OF := AND_32((XOR_32((LOAD_LE_32(mem, RAX)), 0bv32)), (XOR_32((LOAD_LE_32(mem, RAX)), t_383)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_383, (LOAD_LE_32(mem, RAX)))), 0bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)), 2bv32)), (XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)), 2bv32)), (XOR_32((RSHIFT_32(t_383, 4bv32)), t_383)))))[1:0]));
SF := t_383[32:31];
ZF := bool2bv(0bv32 == t_383);

label_0x3e6e:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x3e72;
}

label_0x3e70:
goto label_0x3e7c;

label_0x3e72:
goto label_0x393f;

label_0x3e77:
goto label_0x3904;

label_0x3e7c:
t1_387 := RSP;
t2_388 := 152bv64;
RSP := PLUS_64(RSP, t2_388);
CF := bool2bv(LT_64(RSP, t1_387));
OF := AND_1((bool2bv((t1_387[64:63]) == (t2_388[64:63]))), (XOR_1((t1_387[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_387)), t2_388)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x3e83:

ra_393 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,R9,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_106,origCOUNT_112,origCOUNT_126,origCOUNT_144,origCOUNT_150,origCOUNT_188,origCOUNT_200,origCOUNT_218,origCOUNT_224,origCOUNT_238,origCOUNT_256,origCOUNT_262,origCOUNT_300,origCOUNT_312,origCOUNT_330,origCOUNT_336,origCOUNT_350,origCOUNT_368,origCOUNT_374,origCOUNT_76,origCOUNT_88,origDEST_105,origDEST_111,origDEST_125,origDEST_143,origDEST_149,origDEST_187,origDEST_199,origDEST_217,origDEST_223,origDEST_237,origDEST_255,origDEST_261,origDEST_299,origDEST_311,origDEST_329,origDEST_335,origDEST_349,origDEST_367,origDEST_373,origDEST_75,origDEST_87,ra_393,t1_131,t1_163,t1_173,t1_193,t1_205,t1_243,t1_275,t1_285,t1_305,t1_317,t1_355,t1_37,t1_387,t1_51,t1_61,t1_81,t1_93,t2_132,t2_164,t2_174,t2_194,t2_206,t2_244,t2_276,t2_286,t2_306,t2_318,t2_356,t2_38,t2_388,t2_52,t2_62,t2_82,t2_94,t_1,t_101,t_117,t_121,t_13,t_139,t_155,t_159,t_169,t_17,t_179,t_183,t_21,t_213,t_229,t_233,t_25,t_251,t_267,t_271,t_281,t_29,t_291,t_295,t_325,t_33,t_341,t_345,t_363,t_379,t_383,t_43,t_47,t_5,t_57,t_67,t_71,t_9;

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
var origCOUNT_106: bv64;
var origCOUNT_112: bv64;
var origCOUNT_126: bv64;
var origCOUNT_144: bv64;
var origCOUNT_150: bv64;
var origCOUNT_188: bv64;
var origCOUNT_200: bv64;
var origCOUNT_218: bv64;
var origCOUNT_224: bv64;
var origCOUNT_238: bv64;
var origCOUNT_256: bv64;
var origCOUNT_262: bv64;
var origCOUNT_300: bv64;
var origCOUNT_312: bv64;
var origCOUNT_330: bv64;
var origCOUNT_336: bv64;
var origCOUNT_350: bv64;
var origCOUNT_368: bv64;
var origCOUNT_374: bv64;
var origCOUNT_76: bv64;
var origCOUNT_88: bv64;
var origDEST_105: bv64;
var origDEST_111: bv64;
var origDEST_125: bv64;
var origDEST_143: bv64;
var origDEST_149: bv64;
var origDEST_187: bv64;
var origDEST_199: bv64;
var origDEST_217: bv64;
var origDEST_223: bv64;
var origDEST_237: bv64;
var origDEST_255: bv64;
var origDEST_261: bv64;
var origDEST_299: bv64;
var origDEST_311: bv64;
var origDEST_329: bv64;
var origDEST_335: bv64;
var origDEST_349: bv64;
var origDEST_367: bv64;
var origDEST_373: bv64;
var origDEST_75: bv64;
var origDEST_87: bv64;
var ra_393: bv64;
var t1_131: bv64;
var t1_163: bv32;
var t1_173: bv32;
var t1_193: bv64;
var t1_205: bv64;
var t1_243: bv64;
var t1_275: bv32;
var t1_285: bv32;
var t1_305: bv64;
var t1_317: bv64;
var t1_355: bv64;
var t1_37: bv32;
var t1_387: bv64;
var t1_51: bv32;
var t1_61: bv32;
var t1_81: bv64;
var t1_93: bv64;
var t2_132: bv64;
var t2_164: bv32;
var t2_174: bv32;
var t2_194: bv64;
var t2_206: bv64;
var t2_244: bv64;
var t2_276: bv32;
var t2_286: bv32;
var t2_306: bv64;
var t2_318: bv64;
var t2_356: bv64;
var t2_38: bv32;
var t2_388: bv64;
var t2_52: bv32;
var t2_62: bv32;
var t2_82: bv64;
var t2_94: bv64;
var t_1: bv64;
var t_101: bv64;
var t_117: bv32;
var t_121: bv32;
var t_13: bv32;
var t_139: bv64;
var t_155: bv32;
var t_159: bv32;
var t_169: bv32;
var t_17: bv32;
var t_179: bv32;
var t_183: bv32;
var t_21: bv32;
var t_213: bv64;
var t_229: bv32;
var t_233: bv32;
var t_25: bv32;
var t_251: bv64;
var t_267: bv32;
var t_271: bv32;
var t_281: bv32;
var t_29: bv32;
var t_291: bv32;
var t_295: bv32;
var t_325: bv64;
var t_33: bv32;
var t_341: bv32;
var t_345: bv32;
var t_363: bv64;
var t_379: bv32;
var t_383: bv32;
var t_43: bv32;
var t_47: bv32;
var t_5: bv32;
var t_57: bv32;
var t_67: bv32;
var t_71: bv32;
var t_9: bv32;


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
