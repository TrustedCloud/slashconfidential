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
axiom _function_addr_low == 7824bv64;
axiom _function_addr_high == 7828bv64;

procedure arbitrary_func();

implementation dll_func()
{

label_0x1e90:


label_0x1e92:
assume false;

label_0x1e93:

ra_1 := LOAD_LE_64(mem, RSP);
RSP := PLUS_64(RSP, 8bv64);
assert {:SlashVerifyCommandType "ret"} true;
return;

}

procedure dll_func();
  modifies RSP,ra_1;

var mem: [bv64] bv8;
var RAX: bv64;
var CF: bv1;
var RCX: bv64;
var RDI: bv64;
var RSP: bv64;
var ra_1: bv64;


function policy(x: bv64): bool;
axiom policy(4096bv64);
axiom policy(4160bv64);
axiom policy(4240bv64);
axiom policy(4288bv64);
axiom policy(4304bv64);
axiom policy(4704bv64);
axiom policy(4736bv64);
axiom policy(4800bv64);
axiom policy(5200bv64);
axiom policy(5664bv64);
axiom policy(5728bv64);
axiom policy(5776bv64);
axiom policy(5840bv64);
axiom policy(5904bv64);
axiom policy(5968bv64);
axiom policy(6288bv64);
axiom policy(6992bv64);
axiom policy(7088bv64);
axiom policy(7168bv64);
axiom policy(7312bv64);
axiom policy(7520bv64);
axiom policy(7664bv64);
axiom policy(7824bv64);
axiom policy(7840bv64);
axiom policy(7952bv64);
axiom policy(8096bv64);
axiom policy(8240bv64);
axiom policy(8800bv64);
axiom policy(8880bv64);
axiom policy(9040bv64);
axiom policy(9088bv64);
axiom policy(9136bv64);
axiom policy(9216bv64);
axiom policy(9264bv64);
axiom policy(9312bv64);
axiom policy(9360bv64);
axiom policy(9392bv64);
axiom policy(9424bv64);
axiom policy(9472bv64);
axiom policy(9520bv64);
axiom policy(9568bv64);
axiom policy(9600bv64);
axiom policy(9616bv64);
axiom policy(9632bv64);
axiom policy(9648bv64);
axiom policy(9664bv64);
axiom policy(9680bv64);
axiom policy(9696bv64);
axiom policy(9984bv64);
axiom policy(10240bv64);
axiom policy(10528bv64);
axiom policy(10672bv64);
axiom policy(10800bv64);
axiom policy(10944bv64);
