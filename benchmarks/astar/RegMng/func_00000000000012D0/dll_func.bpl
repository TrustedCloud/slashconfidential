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
axiom _function_addr_low == 4816bv64;
axiom _function_addr_high == 5840bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x12d0:
mem := STORE_LE_32(mem, PLUS_64(RSP, 16bv64), RDX[32:0]);

label_0x12d4:
mem := STORE_LE_64(mem, PLUS_64(RSP, 8bv64), RCX);

label_0x12d9:
t_1 := RSP;
RSP := MINUS_64(RSP, 104bv64);
CF := bool2bv(LT_64(t_1, 104bv64));
OF := AND_64((XOR_64(t_1, 104bv64)), (XOR_64(t_1, RSP)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t_1)), 104bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x12dd:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x12e5:
goto label_0x12f1;

label_0x12e7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x12eb:
t_5 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_5[32:31]) == (1bv32[32:31]))), (XOR_1((t_5[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_5)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x12ed:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x12f1:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x12f6:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 400bv64)));

label_0x12fc:
t_9 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_9)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_9, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)), 2bv32)), (XOR_32((RSHIFT_32(t_9, 4bv32)), t_9)))))[1:0]));
SF := t_9[32:31];
ZF := bool2bv(0bv32 == t_9);

label_0x1300:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x136c;
}

label_0x1302:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1307:
t1_13 := RAX;
t2_14 := 344bv64;
RAX := PLUS_64(RAX, t2_14);
CF := bool2bv(LT_64(RAX, t1_13));
OF := AND_1((bool2bv((t1_13[64:63]) == (t2_14[64:63]))), (XOR_1((t1_13[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_13)), t2_14)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x130d:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1311:
RCX := RAX;

label_0x1314:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 4889bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1319"} true;
call arbitrary_func();

label_0x1319:
RAX := LOAD_LE_64(mem, RAX);

label_0x131c:
t1_19 := RAX;
t2_20 := 5bv64;
RAX := PLUS_64(RAX, t2_20);
CF := bool2bv(LT_64(RAX, t1_19));
OF := AND_1((bool2bv((t1_19[64:63]) == (t2_20[64:63]))), (XOR_1((t1_19[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_19)), t2_20)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1320:
mem := STORE_LE_64(mem, PLUS_64(RSP, 48bv64), RAX);

label_0x1325:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x132a:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_1;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1330:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x1335:
t_27 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_2;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)), 2bv64)), (XOR_64((RSHIFT_64(t_27, 4bv64)), t_27)))))[1:0]));
SF := t_27[64:63];
ZF := bool2bv(0bv64 == t_27);

label_0x1338:
if (bv2bool(ZF)) {
  goto label_0x133b;
}

label_0x133a:
assume false;

label_0x133b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1340:
origDEST_31 := RAX;
origCOUNT_32 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), CF, LSHIFT_64(origDEST_31, (MINUS_64(64bv64, origCOUNT_32)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_32 == 1bv64)), origDEST_31[64:63], unconstrained_3));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_32 == 0bv64)), AF, unconstrained_4);

label_0x1344:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x134b:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x134f:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1354:
origDEST_37 := RCX;
origCOUNT_38 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), CF, LSHIFT_64(origDEST_37, (MINUS_64(64bv64, origCOUNT_38)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_38 == 1bv64)), origDEST_37[64:63], unconstrained_5));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_38 == 0bv64)), AF, unconstrained_6);

label_0x1358:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_7;
SF := unconstrained_8;
AF := unconstrained_9;
PF := unconstrained_10;

label_0x135c:
if (bv2bool(CF)) {
  goto label_0x135f;
}

label_0x135e:
assume false;

label_0x135f:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 48bv64));

label_0x1364:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x1367:
goto label_0x12e7;

label_0x136c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x1374:
goto label_0x1380;

label_0x1376:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x137a:
t_43 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_43[32:31]) == (1bv32[32:31]))), (XOR_1((t_43[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_43)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x137c:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x1380:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1385:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 400bv64)));

label_0x138b:
t_47 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_47)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_47, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)), 2bv32)), (XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)), 2bv32)), (XOR_32((RSHIFT_32(t_47, 4bv32)), t_47)))))[1:0]));
SF := t_47[32:31];
ZF := bool2bv(0bv32 == t_47);

label_0x138f:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x14da;
}

label_0x1395:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x139a:
t1_51 := RAX;
t2_52 := 344bv64;
RAX := PLUS_64(RAX, t2_52);
CF := bool2bv(LT_64(RAX, t1_51));
OF := AND_1((bool2bv((t1_51[64:63]) == (t2_52[64:63]))), (XOR_1((t1_51[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_51)), t2_52)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13a0:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x13a4:
RCX := RAX;

label_0x13a7:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5036bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x13ac"} true;
call arbitrary_func();

label_0x13ac:
RAX := LOAD_LE_64(mem, RAX);

label_0x13af:
RCX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 120bv64)));

label_0x13b3:
t_57 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), (RCX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), (RCX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), (RCX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))), t_57)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_57, (LOAD_LE_32(mem, PLUS_64(RAX, 16bv64))))), (RCX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)), 2bv32)), (XOR_32((RSHIFT_32(t_57, 4bv32)), t_57)))))[1:0]));
SF := t_57[32:31];
ZF := bool2bv(0bv32 == t_57);

label_0x13b6:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x14d5;
}

label_0x13bc:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x13c1:
t1_61 := RAX;
t2_62 := 344bv64;
RAX := PLUS_64(RAX, t2_62);
CF := bool2bv(LT_64(RAX, t1_61));
OF := AND_1((bool2bv((t1_61[64:63]) == (t2_62[64:63]))), (XOR_1((t1_61[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_61)), t2_62)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13c7:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x13cb:
RCX := RAX;

label_0x13ce:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5075bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x13d3"} true;
call arbitrary_func();

label_0x13d3:
RAX := LOAD_LE_64(mem, RAX);

label_0x13d6:
t1_67 := RAX;
t2_68 := 4bv64;
RAX := PLUS_64(RAX, t2_68);
CF := bool2bv(LT_64(RAX, t1_67));
OF := AND_1((bool2bv((t1_67[64:63]) == (t2_68[64:63]))), (XOR_1((t1_67[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_67)), t2_68)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13da:
mem := STORE_LE_64(mem, PLUS_64(RSP, 56bv64), RAX);

label_0x13df:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x13e4:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_11;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x13ea:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x13ef:
t_75 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_12;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)), 2bv64)), (XOR_64((RSHIFT_64(t_75, 4bv64)), t_75)))))[1:0]));
SF := t_75[64:63];
ZF := bool2bv(0bv64 == t_75);

label_0x13f2:
if (bv2bool(ZF)) {
  goto label_0x13f5;
}

label_0x13f4:
assume false;

label_0x13f5:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x13fa:
origDEST_79 := RAX;
origCOUNT_80 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), CF, LSHIFT_64(origDEST_79, (MINUS_64(64bv64, origCOUNT_80)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_80 == 1bv64)), origDEST_79[64:63], unconstrained_13));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_80 == 0bv64)), AF, unconstrained_14);

label_0x13fe:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1405:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1409:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x140e:
origDEST_85 := RCX;
origCOUNT_86 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), CF, LSHIFT_64(origDEST_85, (MINUS_64(64bv64, origCOUNT_86)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_86 == 1bv64)), origDEST_85[64:63], unconstrained_15));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_86 == 0bv64)), AF, unconstrained_16);

label_0x1412:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_17;
SF := unconstrained_18;
AF := unconstrained_19;
PF := unconstrained_20;

label_0x1416:
if (bv2bool(CF)) {
  goto label_0x1419;
}

label_0x1418:
assume false;

label_0x1419:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 56bv64));

label_0x141e:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x1421:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), 0bv32);

label_0x1429:
goto label_0x1435;

label_0x142b:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x142f:
t_91 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_91[32:31]) == (1bv32[32:31]))), (XOR_1((t_91[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_91)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x1431:
mem := STORE_LE_32(mem, PLUS_64(RSP, 44bv64), RAX[32:0]);

label_0x1435:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x143a:
t1_95 := RAX;
t2_96 := 344bv64;
RAX := PLUS_64(RAX, t2_96);
CF := bool2bv(LT_64(RAX, t1_95));
OF := AND_1((bool2bv((t1_95[64:63]) == (t2_96[64:63]))), (XOR_1((t1_95[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_95)), t2_96)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1440:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1444:
RCX := RAX;

label_0x1447:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5196bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x144c"} true;
call arbitrary_func();

label_0x144c:
RAX := LOAD_LE_64(mem, RAX);

label_0x144f:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 48bv64)));

label_0x1452:
t_101 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))), t_101)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_101, (LOAD_LE_32(mem, PLUS_64(RSP, 44bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)), 2bv32)), (XOR_32((RSHIFT_32(t_101, 4bv32)), t_101)))))[1:0]));
SF := t_101[32:31];
ZF := bool2bv(0bv32 == t_101);

label_0x1456:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x14d5;
}

label_0x1458:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x145d:
t1_105 := RAX;
t2_106 := 344bv64;
RAX := PLUS_64(RAX, t2_106);
CF := bool2bv(LT_64(RAX, t1_105));
OF := AND_1((bool2bv((t1_105[64:63]) == (t2_106[64:63]))), (XOR_1((t1_105[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_105)), t2_106)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1463:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1467:
RCX := RAX;

label_0x146a:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5231bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x146f"} true;
call arbitrary_func();

label_0x146f:
RAX := LOAD_LE_64(mem, RAX);

label_0x1472:
t1_111 := RAX;
t2_112 := 40bv64;
RAX := PLUS_64(RAX, t2_112);
CF := bool2bv(LT_64(RAX, t1_111));
OF := AND_1((bool2bv((t1_111[64:63]) == (t2_112[64:63]))), (XOR_1((t1_111[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_111)), t2_112)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1476:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 44bv64)));

label_0x147a:
RCX := RAX;

label_0x147d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5250bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1482"} true;
call arbitrary_func();

label_0x1482:
RAX := LOAD_LE_64(mem, RAX);

label_0x1485:
t1_117 := RAX;
t2_118 := 5bv64;
RAX := PLUS_64(RAX, t2_118);
CF := bool2bv(LT_64(RAX, t1_117));
OF := AND_1((bool2bv((t1_117[64:63]) == (t2_118[64:63]))), (XOR_1((t1_117[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_117)), t2_118)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1489:
mem := STORE_LE_64(mem, PLUS_64(RSP, 64bv64), RAX);

label_0x148e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x1493:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_21;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1499:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x149e:
t_125 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_22;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)), 2bv64)), (XOR_64((RSHIFT_64(t_125, 4bv64)), t_125)))))[1:0]));
SF := t_125[64:63];
ZF := bool2bv(0bv64 == t_125);

label_0x14a1:
if (bv2bool(ZF)) {
  goto label_0x14a4;
}

label_0x14a3:
assume false;

label_0x14a4:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14a9:
origDEST_129 := RAX;
origCOUNT_130 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), CF, LSHIFT_64(origDEST_129, (MINUS_64(64bv64, origCOUNT_130)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_130 == 1bv64)), origDEST_129[64:63], unconstrained_23));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_130 == 0bv64)), AF, unconstrained_24);

label_0x14ad:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x14b4:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x14b8:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14bd:
origDEST_135 := RCX;
origCOUNT_136 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), CF, LSHIFT_64(origDEST_135, (MINUS_64(64bv64, origCOUNT_136)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_136 == 1bv64)), origDEST_135[64:63], unconstrained_25));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_136 == 0bv64)), AF, unconstrained_26);

label_0x14c1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_27;
SF := unconstrained_28;
AF := unconstrained_29;
PF := unconstrained_30;

label_0x14c5:
if (bv2bool(CF)) {
  goto label_0x14c8;
}

label_0x14c7:
assume false;

label_0x14c8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 64bv64));

label_0x14cd:
mem := STORE_LE_8(mem, RAX, 1bv8);

label_0x14d0:
goto label_0x142b;

label_0x14d5:
goto label_0x1376;

label_0x14da:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), 0bv32);

label_0x14e2:
goto label_0x14ee;

label_0x14e4:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x14e8:
t_141 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_141[32:31]) == (1bv32[32:31]))), (XOR_1((t_141[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_141)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x14ea:
mem := STORE_LE_32(mem, PLUS_64(RSP, 32bv64), RAX[32:0]);

label_0x14ee:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x14f3:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 400bv64)));

label_0x14f9:
t_145 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))), t_145)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_145, (LOAD_LE_32(mem, PLUS_64(RSP, 32bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)), 2bv32)), (XOR_32((RSHIFT_32(t_145, 4bv32)), t_145)))))[1:0]));
SF := t_145[32:31];
ZF := bool2bv(0bv32 == t_145);

label_0x14fd:
if (bv2bool(NOT_1((XOR_1(SF, OF))))) {
  goto label_0x15b5;
}

label_0x1503:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1508:
t1_149 := RAX;
t2_150 := 344bv64;
RAX := PLUS_64(RAX, t2_150);
CF := bool2bv(LT_64(RAX, t1_149));
OF := AND_1((bool2bv((t1_149[64:63]) == (t2_150[64:63]))), (XOR_1((t1_149[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_149)), t2_150)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x150e:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1512:
RCX := RAX;

label_0x1515:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5402bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x151a"} true;
call arbitrary_func();

label_0x151a:
RAX := LOAD_LE_64(mem, RAX);

label_0x151d:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 5bv64))));

label_0x1521:
t_155 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_31;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)), 2bv32)), (XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)), 2bv32)), (XOR_32((RSHIFT_32(t_155, 4bv32)), t_155)))))[1:0]));
SF := t_155[32:31];
ZF := bool2bv(0bv32 == t_155);

label_0x1523:
if (bv2bool(ZF)) {
  goto label_0x15b0;
}

label_0x1529:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x152e:
t1_159 := RAX;
t2_160 := 344bv64;
RAX := PLUS_64(RAX, t2_160);
CF := bool2bv(LT_64(RAX, t1_159));
OF := AND_1((bool2bv((t1_159[64:63]) == (t2_160[64:63]))), (XOR_1((t1_159[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_159)), t2_160)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1534:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x1538:
RCX := RAX;

label_0x153b:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5440bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1540"} true;
call arbitrary_func();

label_0x1540:
RAX := LOAD_LE_64(mem, RAX);

label_0x1543:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 4bv64))));

label_0x1547:
t_165 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_32;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)), 2bv32)), (XOR_32((RSHIFT_32(t_165, 4bv32)), t_165)))))[1:0]));
SF := t_165[32:31];
ZF := bool2bv(0bv32 == t_165);

label_0x1549:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x15b0;
}

label_0x154b:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1550:
t1_169 := RAX;
t2_170 := 344bv64;
RAX := PLUS_64(RAX, t2_170);
CF := bool2bv(LT_64(RAX, t1_169));
OF := AND_1((bool2bv((t1_169[64:63]) == (t2_170[64:63]))), (XOR_1((t1_169[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_169)), t2_170)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1556:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 32bv64)));

label_0x155a:
RCX := RAX;

label_0x155d:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5474bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1562"} true;
call arbitrary_func();

label_0x1562:
RAX := LOAD_LE_64(mem, RAX);

label_0x1565:
t1_175 := RAX;
t2_176 := 5bv64;
RAX := PLUS_64(RAX, t2_176);
CF := bool2bv(LT_64(RAX, t1_175));
OF := AND_1((bool2bv((t1_175[64:63]) == (t2_176[64:63]))), (XOR_1((t1_175[64:63]), (RAX[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RAX, t1_175)), t2_176)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1569:
mem := STORE_LE_64(mem, PLUS_64(RSP, 72bv64), RAX);

label_0x156e:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1573:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_33;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1579:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x157e:
t_183 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_34;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)), 2bv64)), (XOR_64((RSHIFT_64(t_183, 4bv64)), t_183)))))[1:0]));
SF := t_183[64:63];
ZF := bool2bv(0bv64 == t_183);

label_0x1581:
if (bv2bool(ZF)) {
  goto label_0x1584;
}

label_0x1583:
assume false;

label_0x1584:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x1589:
origDEST_187 := RAX;
origCOUNT_188 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), CF, LSHIFT_64(origDEST_187, (MINUS_64(64bv64, origCOUNT_188)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_188 == 1bv64)), origDEST_187[64:63], unconstrained_35));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_188 == 0bv64)), AF, unconstrained_36);

label_0x158d:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1594:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1598:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x159d:
origDEST_193 := RCX;
origCOUNT_194 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), CF, LSHIFT_64(origDEST_193, (MINUS_64(64bv64, origCOUNT_194)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_194 == 1bv64)), origDEST_193[64:63], unconstrained_37));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_194 == 0bv64)), AF, unconstrained_38);

label_0x15a1:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_39;
SF := unconstrained_40;
AF := unconstrained_41;
PF := unconstrained_42;

label_0x15a5:
if (bv2bool(CF)) {
  goto label_0x15a8;
}

label_0x15a7:
assume false;

label_0x15a8:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 72bv64));

label_0x15ad:
mem := STORE_LE_8(mem, RAX, 0bv8);

label_0x15b0:
goto label_0x14e4;

label_0x15b5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), 0bv32);

label_0x15bd:
goto label_0x15c9;

label_0x15bf:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x15c3:
t_199 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_199[32:31]) == (1bv32[32:31]))), (XOR_1((t_199[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_199)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x15c5:
mem := STORE_LE_32(mem, PLUS_64(RSP, 36bv64), RAX[32:0]);

label_0x15c9:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x15ce:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 320bv64)));

label_0x15d4:
t_203 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))), t_203)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_203, (LOAD_LE_32(mem, PLUS_64(RSP, 36bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)), 2bv32)), (XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)), 2bv32)), (XOR_32((RSHIFT_32(t_203, 4bv32)), t_203)))))[1:0]));
SF := t_203[32:31];
ZF := bool2bv(0bv32 == t_203);

label_0x15d8:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x16ac;
}

label_0x15de:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), 0bv32);

label_0x15e6:
goto label_0x15f2;

label_0x15e8:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x15ec:
t_207 := RAX[32:0];
RAX := (0bv32 ++ PLUS_32((RAX[32:0]), 1bv32));
OF := AND_1((bool2bv((t_207[32:31]) == (1bv32[32:31]))), (XOR_1((t_207[32:31]), (RAX[32:0][32:31]))));
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32((RAX[32:0]), t_207)), 1bv32)))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))), 2bv32)), (XOR_32((RSHIFT_32((RAX[32:0]), 4bv32)), (RAX[32:0]))))))[1:0]));
SF := RAX[32:0][32:31];
ZF := bool2bv(0bv32 == (RAX[32:0]));

label_0x15ee:
mem := STORE_LE_32(mem, PLUS_64(RSP, 40bv64), RAX[32:0]);

label_0x15f2:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x15f7:
RAX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RAX, 316bv64)));

label_0x15fd:
t_211 := MINUS_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]));
CF := bool2bv(LT_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0])));
OF := AND_32((XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), (RAX[32:0]))), (XOR_32((LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))), t_211)))[32:31];
AF := bool2bv(16bv32 == (AND_32(16bv32, (XOR_32((XOR_32(t_211, (LOAD_LE_32(mem, PLUS_64(RSP, 40bv64))))), (RAX[32:0]))))));
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)), 2bv32)), (XOR_32((RSHIFT_32(t_211, 4bv32)), t_211)))))[1:0]));
SF := t_211[32:31];
ZF := bool2bv(0bv32 == t_211);

label_0x1601:
if (bv2bool(NOT_1((OR_1(ZF, (XOR_1(SF, OF))))))) {
  goto label_0x16a7;
}

label_0x1607:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x160c:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x1610:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1615:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5658bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x161a"} true;
call arbitrary_func();

label_0x161a:
RAX := LOAD_LE_64(mem, RAX);

label_0x161d:
mem := STORE_LE_64(mem, PLUS_64(RSP, 88bv64), RAX);

label_0x1622:
t_215 := MINUS_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64);
CF := bool2bv(LT_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64));
OF := AND_64((XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), 0bv64)), (XOR_64((LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))), t_215)))[64:63];
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(t_215, (LOAD_LE_64(mem, PLUS_64(RSP, 88bv64))))), 0bv64)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)), 2bv64)), (XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)), 2bv64)), (XOR_64((RSHIFT_64(t_215, 4bv64)), t_215)))))[1:0]));
SF := t_215[64:63];
ZF := bool2bv(0bv64 == t_215);

label_0x1628:
if (bv2bool(ZF)) {
  goto label_0x16a2;
}

label_0x162a:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x162f:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 5bv64))));

label_0x1633:
t_219 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_43;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_219, 4bv32)), t_219)), 2bv32)), (XOR_32((RSHIFT_32(t_219, 4bv32)), t_219)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_219, 4bv32)), t_219)), 2bv32)), (XOR_32((RSHIFT_32(t_219, 4bv32)), t_219)))))[1:0]));
SF := t_219[32:31];
ZF := bool2bv(0bv32 == t_219);

label_0x1635:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x1644;
}

label_0x1637:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 88bv64));

label_0x163c:
RAX := (0bv32 ++ (0bv24 ++ LOAD_LE_8(mem, PLUS_64(RAX, 4bv64))));

label_0x1640:
t_223 := AND_32((RAX[32:0]), (RAX[32:0]));
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_44;
PF := NOT_1((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_223, 4bv32)), t_223)), 2bv32)), (XOR_32((RSHIFT_32(t_223, 4bv32)), t_223)))), 1bv32)), (XOR_32((RSHIFT_32((XOR_32((RSHIFT_32(t_223, 4bv32)), t_223)), 2bv32)), (XOR_32((RSHIFT_32(t_223, 4bv32)), t_223)))))[1:0]));
SF := t_223[32:31];
ZF := bool2bv(0bv32 == t_223);

label_0x1642:
if (bv2bool(NOT_1(ZF))) {
  goto label_0x16a2;
}

label_0x1644:
R8 := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 36bv64)));

label_0x1649:
RDX := (0bv32 ++ LOAD_LE_32(mem, PLUS_64(RSP, 40bv64)));

label_0x164d:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x1652:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5719bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x1657"} true;
call arbitrary_func();

label_0x1657:
mem := STORE_LE_64(mem, PLUS_64(RSP, 80bv64), RAX);

label_0x165c:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1661:
RAX := AND_64(RAX, 4294967295bv32 ++ 3758096384bv32);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_45;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0]));
SF := RAX[64:63];
ZF := bool2bv(0bv64 == RAX);

label_0x1667:
assert {:SlashVerifyCommandType "btc_rax_1d"} true;

label_0x166c:
t_229 := AND_64(RAX, RAX);
OF := 0bv1;
CF := 0bv1;
AF := unconstrained_46;
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)), 2bv64)), (XOR_64((RSHIFT_64(t_229, 4bv64)), t_229)))))[1:0]));
SF := t_229[64:63];
ZF := bool2bv(0bv64 == t_229);

label_0x166f:
if (bv2bool(ZF)) {
  goto label_0x1672;
}

label_0x1671:
assume false;

label_0x1672:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x1677:
origDEST_233 := RAX;
origCOUNT_234 := AND_64(9bv64, (MINUS_64(64bv64, 1bv64)));
RAX := RSHIFT_64(RAX, (AND_64(9bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), CF, LSHIFT_64(origDEST_233, (MINUS_64(64bv64, origCOUNT_234)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_234 == 1bv64)), origDEST_233[64:63], unconstrained_47));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), SF, RAX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), ZF, bool2bv(0bv64 == RAX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)), 2bv64)), (XOR_64((RSHIFT_64(RAX, 4bv64)), RAX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_234 == 0bv64)), AF, unconstrained_48);

label_0x167b:
RCX := LOAD_LE_64(mem, 29888bv64);

label_0x1682:
RAX := LOAD_LE_64(mem, PLUS_64(RCX, (LSHIFT_64(RAX, 3bv64))));

label_0x1686:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x168b:
origDEST_239 := RCX;
origCOUNT_240 := AND_64(3bv64, (MINUS_64(64bv64, 1bv64)));
RCX := RSHIFT_64(RCX, (AND_64(3bv64, (MINUS_64(64bv64, 1bv64)))));
CF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), CF, LSHIFT_64(origDEST_239, (MINUS_64(64bv64, origCOUNT_240)))[64:63]);
OF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), OF, ITE_1(bv2bool(bool2bv(origCOUNT_240 == 1bv64)), origDEST_239[64:63], unconstrained_49));
SF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), SF, RCX[64:63]);
ZF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), ZF, bool2bv(0bv64 == RCX));
PF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), PF, NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)), 2bv64)), (XOR_64((RSHIFT_64(RCX, 4bv64)), RCX)))))[1:0])));
AF := ITE_1(bv2bool(bool2bv(origCOUNT_240 == 0bv64)), AF, unconstrained_50);

label_0x168f:
CF := RSHIFT_64(RAX, (AND_64(RCX, 63bv64)))[1:0];
OF := unconstrained_51;
SF := unconstrained_52;
AF := unconstrained_53;
PF := unconstrained_54;

label_0x1693:
if (bv2bool(CF)) {
  goto label_0x1696;
}

label_0x1695:
assume false;

label_0x1696:
RAX := LOAD_LE_64(mem, PLUS_64(RSP, 80bv64));

label_0x169b:
mem := STORE_LE_64(mem, RAX, 0bv64);

label_0x16a2:
goto label_0x15e8;

label_0x16a7:
goto label_0x15bf;

label_0x16ac:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x16b1:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5814bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x16b6"} true;
call arbitrary_func();

label_0x16b6:
RCX := LOAD_LE_64(mem, PLUS_64(RSP, 112bv64));

label_0x16bb:

RSP := MINUS_64(RSP, 8bv64);
mem := STORE_LE_64(mem, RSP, 5824bv64);
assert {:SlashVerifyCommandType "call"} {:SlashVerifyCallTarget "0x16c0"} true;
call arbitrary_func();

label_0x16c0:
t1_245 := RSP;
t2_246 := 104bv64;
RSP := PLUS_64(RSP, t2_246);
CF := bool2bv(LT_64(RSP, t1_245));
OF := AND_1((bool2bv((t1_245[64:63]) == (t2_246[64:63]))), (XOR_1((t1_245[64:63]), (RSP[64:63]))));
AF := bool2bv(16bv64 == (AND_64(16bv64, (XOR_64((XOR_64(RSP, t1_245)), t2_246)))));
PF := NOT_1((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))), 1bv64)), (XOR_64((RSHIFT_64((XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)), 2bv64)), (XOR_64((RSHIFT_64(RSP, 4bv64)), RSP)))))[1:0]));
SF := RSP[64:63];
ZF := bool2bv(0bv64 == RSP);

label_0x16c4:

ra_251 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies AF,CF,OF,PF,R8,RAX,RCX,RDX,RSP,SF,ZF,mem,origCOUNT_130,origCOUNT_136,origCOUNT_188,origCOUNT_194,origCOUNT_234,origCOUNT_240,origCOUNT_32,origCOUNT_38,origCOUNT_80,origCOUNT_86,origDEST_129,origDEST_135,origDEST_187,origDEST_193,origDEST_233,origDEST_239,origDEST_31,origDEST_37,origDEST_79,origDEST_85,ra_251,t1_105,t1_111,t1_117,t1_13,t1_149,t1_159,t1_169,t1_175,t1_19,t1_245,t1_51,t1_61,t1_67,t1_95,t2_106,t2_112,t2_118,t2_14,t2_150,t2_160,t2_170,t2_176,t2_20,t2_246,t2_52,t2_62,t2_68,t2_96,t_1,t_101,t_125,t_141,t_145,t_155,t_165,t_183,t_199,t_203,t_207,t_211,t_215,t_219,t_223,t_229,t_27,t_43,t_47,t_5,t_57,t_75,t_9,t_91;

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
var origCOUNT_130: bv64;
var origCOUNT_136: bv64;
var origCOUNT_188: bv64;
var origCOUNT_194: bv64;
var origCOUNT_234: bv64;
var origCOUNT_240: bv64;
var origCOUNT_32: bv64;
var origCOUNT_38: bv64;
var origCOUNT_80: bv64;
var origCOUNT_86: bv64;
var origDEST_129: bv64;
var origDEST_135: bv64;
var origDEST_187: bv64;
var origDEST_193: bv64;
var origDEST_233: bv64;
var origDEST_239: bv64;
var origDEST_31: bv64;
var origDEST_37: bv64;
var origDEST_79: bv64;
var origDEST_85: bv64;
var ra_251: bv64;
var t1_105: bv64;
var t1_111: bv64;
var t1_117: bv64;
var t1_13: bv64;
var t1_149: bv64;
var t1_159: bv64;
var t1_169: bv64;
var t1_175: bv64;
var t1_19: bv64;
var t1_245: bv64;
var t1_51: bv64;
var t1_61: bv64;
var t1_67: bv64;
var t1_95: bv64;
var t2_106: bv64;
var t2_112: bv64;
var t2_118: bv64;
var t2_14: bv64;
var t2_150: bv64;
var t2_160: bv64;
var t2_170: bv64;
var t2_176: bv64;
var t2_20: bv64;
var t2_246: bv64;
var t2_52: bv64;
var t2_62: bv64;
var t2_68: bv64;
var t2_96: bv64;
var t_1: bv64;
var t_101: bv32;
var t_125: bv64;
var t_141: bv32;
var t_145: bv32;
var t_155: bv32;
var t_165: bv32;
var t_183: bv64;
var t_199: bv32;
var t_203: bv32;
var t_207: bv32;
var t_211: bv32;
var t_215: bv64;
var t_219: bv32;
var t_223: bv32;
var t_229: bv64;
var t_27: bv64;
var t_43: bv32;
var t_47: bv32;
var t_5: bv32;
var t_57: bv32;
var t_75: bv64;
var t_9: bv32;
var t_91: bv32;


function policy(x: bv64): bool;
axiom policy(0bv64);
axiom policy(208bv64);
axiom policy(688bv64);
axiom policy(1184bv64);
axiom policy(3040bv64);
axiom policy(3232bv64);
axiom policy(3488bv64);
axiom policy(4240bv64);
axiom policy(4816bv64);
axiom policy(5840bv64);
axiom policy(6768bv64);
axiom policy(7760bv64);
axiom policy(8352bv64);
axiom policy(8720bv64);
axiom policy(10656bv64);
axiom policy(12272bv64);
axiom policy(13488bv64);
axiom policy(13872bv64);
