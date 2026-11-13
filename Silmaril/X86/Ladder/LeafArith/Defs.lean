module

public import Silmaril.X86.BlockCert.Defs
public import Silmaril.X86.Ladder.LeafArith.Transcript
public import Silmaril.X86.Ladder.LeafArith.Bir.bswap32_manual
public import Silmaril.X86.Ladder.LeafArith.Bir.sat_add_u32
public import Silmaril.Machine.SystemV.Defs
/-!
# Ladder rung 01 (`leaf-arith`, gcc -O2): function certificates

Subjects: `bswap32_manual`, `sat_add_u32`, `clamp_i32` and `gcd_u32` of
`examples/elf-ladder/01-leaf-arith/arith.c`, as linked into the pinned `-O2` executable
(sha256 `d9cf1e5d…`, see `Ladder/LeafArith/Transcript.lean`).

* **C semantics** (`bswap32Spec`, `satAddSpec`, `clampSpec`, `gcdSpec`): the source functions
  transcribed over `BitVec 32` (unsigned `u32` is `BitVec 32` with unsigned order, `int` is
  `BitVec 32` with signed order). `gcdSpec` is `Nat.gcd`; Euclid's loop is the binary's
  business.
* **Code**: `code` is the 181-byte transcribed region `[0x401370, 0x401425)`
  (`Transcript.bytes`) at `base`; block offsets are relative to it. The `bswap32_manual` and
  `sat_add_u32` listings are WP2's generated Bir modules; `clamp_i32` and `gcd_u32` are
  listed here by hand from `Transcript.listing`, because the generator's Bir pass rejects
  `cmovle` (the Bir lifter handles CMOV as its extension form `LInstr.x (.cmov …)`, which
  `BlockCert.toExt` reads as the `Ext` CMOV) and `div` (which Bir cannot lift; that block is a
  single raw instruction whose VC unfolds `Ext.exec`). Every listing is checked against
  `code` (`FunCert.checked`, `decide +kernel`), so a wrong hand listing is rejected.
* **Contracts** (`*Spec`): System V leaf contracts (`BlockCert.leafSpec`): code loaded and
  entered at the function's offset; no memory written; the result in `rax` (zero-extended:
  the 32-bit forms gcc uses clear bits 63:32).
* **C signatures** (`sigU1`, `sigU2`, `sigI3`, `*Result`, `noWrites`, `loadedAt`): the
  integer System V view of each function for `Silmaril.Machine.SystemV.Realizes`
  (`*_realizes` in `Thms.lean`): no memory written, and the domain is the code loaded with
  the call's entry at the function.
* **Certificates** (`*Cert`): blocks, annotations (`*Ann`, with the System V frame `Frame`) and
  measures. `gcd_u32` has a loop cut at `0x401380` with Euclid's invariant
  `gcd eax edx = gcd a b` and measure `edx`.

Not here: `popcount32` (its `imul r32, r/m32, imm32` is outside `X86.Ext`/`Ext8`, so the open
machine has no step for it) and `ilog2_u32` (gcc -O2 compiles the loop to `bsr`, also outside
`Ext8`); `isqrt_u32` is lifted by WP2 but not certified here.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.LeafArith

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Bir9 (LInstr Block E F Stmt)
open Silmaril.X86.BlockCert

/-! ## C semantics -/

/-- `bswap32_manual`. -/
def bswap32Spec (x : BitVec 32) : BitVec 32 :=
  (x >>> 24) ||| ((x >>> 8) &&& 0xff00#32) ||| ((x <<< 8) &&& 0xff0000#32) ||| (x <<< 24)

/-- `sat_add_u32`: `s = a + b; return s < a ? 0xffffffff : s` (unsigned compare). -/
def satAddSpec (a b : BitVec 32) : BitVec 32 :=
  if (a + b).ult a then 0xffffffff#32 else a + b

/-- `clamp_i32` (signed compares). -/
def clampSpec (x lo hi : BitVec 32) : BitVec 32 :=
  if x.slt lo then lo else if hi.slt x then hi else x

/-- `gcd_u32`: the greatest common divisor (`gcd 0 0 = 0`). -/
def gcdSpec (a b : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)

/-! ## The code -/

/-- The load address of the transcribed region. -/
def base : Word := 0x401370

/-- The transcribed bytes `[0x401370, 0x401425)`. -/
def code : List Byte := Transcript.bytes

/-- The low 32 bits of a register. -/
def r32 (r : Reg) (m : MState) : BitVec 32 := (m.core.read r).setWidth 32

/-! ## Contracts -/

/-- `bswap32_manual` at `0x401420`: `rax = bswap32_manual(edi)`. -/
def bswapSpec : FnContract.Spec MState :=
  leafSpec base code 0xb0 fun m t => t.core.read .rax = (bswap32Spec (r32 .rdi m)).setWidth 64

/-- `sat_add_u32` at `0x401400`: `rax = sat_add_u32(edi, esi)`. -/
def satSpec : FnContract.Spec MState :=
  leafSpec base code 0x90 fun m t =>
    t.core.read .rax = (satAddSpec (r32 .rdi m) (r32 .rsi m)).setWidth 64

/-- `clamp_i32` at `0x4013a0`: `rax = clamp_i32(edi, esi, edx)`. -/
def clampSpec' : FnContract.Spec MState :=
  leafSpec base code 0x30 fun m t =>
    t.core.read .rax = (clampSpec (r32 .rdi m) (r32 .rsi m) (r32 .rdx m)).setWidth 64

/-- `gcd_u32` at `0x401370`: `rax = gcd_u32(edi, esi)`. -/
def gcdSpec' : FnContract.Spec MState :=
  leafSpec base code 0x0 fun m t =>
    t.core.read .rax = (gcdSpec (r32 .rdi m) (r32 .rsi m)).setWidth 64

/-! ## C signatures for `SystemV.Realizes` -/

/-- `u32 f(u32)`. -/
def sigU1 : Silmaril.C.Api.Signature := ⟨[.uint32], some .uint32⟩

/-- `u32 f(u32, u32)`. -/
def sigU2 : Silmaril.C.Api.Signature := ⟨[.uint32, .uint32], some .uint32⟩

/-- `int f(int, int, int)`. -/
def sigI3 : Silmaril.C.Api.Signature := ⟨[.int32, .int32, .int32], some .int32⟩

def bswapResult : Silmaril.C.Api.Arguments sigU1.arguments →
    Silmaril.C.Api.ReturnValue sigU1.result
  | .cons x .nil => bswap32Spec x

def satResult : Silmaril.C.Api.Arguments sigU2.arguments →
    Silmaril.C.Api.ReturnValue sigU2.result
  | .cons a (.cons b .nil) => satAddSpec a b

def gcdResult : Silmaril.C.Api.Arguments sigU2.arguments →
    Silmaril.C.Api.ReturnValue sigU2.result
  | .cons a (.cons b .nil) => gcdSpec a b

def clampResult : Silmaril.C.Api.Arguments sigI3.arguments →
    Silmaril.C.Api.ReturnValue sigI3.result
  | .cons x (.cons lo (.cons hi .nil)) => clampSpec x lo hi

/-- The functions write no memory. -/
def noWrites {kinds : List Silmaril.C.Api.Scalar} (_ : Silmaril.C.Api.Arguments kinds) :
    Silmaril.Machine.SystemV.Footprint :=
  fun _ => False

/-- The domain: the code loaded at `base`, the call entered at offset `off`. -/
def loadedAt {kinds : List Silmaril.C.Api.Scalar} (off : Nat)
    (_ : Silmaril.C.Api.Arguments kinds) (call : Silmaril.Machine.SystemV.Call) : Prop :=
  Silmaril.X86.Ext.Loaded call.initial.memory base code ∧
    call.entry = base + BitVec.ofNat 64 off

/-! ## `bswap32_manual`: one block -/

def bswapAnn : Nat → MState → MState → Prop
  | _, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory

def bswapCert : FunCert where
  code := code
  base := base
  blocks := [⟨0xb0, Bir.bswap32_manual.L_401420⟩]
  ann := bswapAnn
  measure _ _ _ := 0

/-! ## `sat_add_u32`: five blocks, no loop -/

/-- `sat_add_u32` overflows on its entry arguments. -/
def satOvf (m0 : MState) : Bool := (r32 .rdi m0 + r32 .rsi m0).ult (r32 .rdi m0)

def satAnn : Nat → MState → MState → Prop
  | 0x90, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory
  | 0xa6, m0, m => Frame m0 m ∧ r32 .rdi m = r32 .rdi m0 + r32 .rsi m0 ∧ satOvf m0 = true
  | 0x96, m0, m => Frame m0 m ∧ r32 .rdi m = r32 .rdi m0 + r32 .rsi m0 ∧
      m.core.read .rdx = (if satOvf m0 then 1 else 0)
  | 0x9c, m0, m => Frame m0 m ∧ m.core.read .rax = (r32 .rdi m0 + r32 .rsi m0).setWidth 64 ∧
      satOvf m0 = false
  | 0xa0, m0, m => Frame m0 m ∧ satOvf m0 = true
  | _, _, _ => False

def satCert : FunCert where
  code := code
  base := base
  blocks := [⟨0x90, Bir.sat_add_u32.L_401400⟩, ⟨0xa6, Bir.sat_add_u32.L_401416⟩,
    ⟨0x96, Bir.sat_add_u32.L_401406⟩, ⟨0x9c, Bir.sat_add_u32.L_40140c⟩,
    ⟨0xa0, Bir.sat_add_u32.L_401410⟩]
  ann := satAnn
  measure o _ _ := match o with
    | 0x90 => 5
    | 0xa6 => 4
    | 0x96 => 3
    | _ => 1

/-! ## `clamp_i32`: three blocks, one CMOV -/

/-- `0x4013a0`: `cmp %esi,%edi; jl 0x4013b0`. -/
def clampL30 : List (LInstr × Nat) :=
  [(.ext (.alu .d .cmp (.reg .rdi) .rsi), 2), (.ext (.jcc8 .l 0xc), 2)]

/-- `0x4013a4`: `cmp %edx,%edi; mov %edx,%eax; cmovle %edi,%eax; ret`. -/
def clampL34 : List (LInstr × Nat) :=
  [(.ext (.alu .d .cmp (.reg .rdi) .rdx), 2), (.ext (.mov .d (.reg .rax) .rdx), 2),
   (.x (.cmov .d .le .rax (.reg .rdi)), 3), (.ext .ret, 1)]

/-- `0x4013b0`: `mov %esi,%eax; ret`. -/
def clampL40 : List (LInstr × Nat) :=
  [(.ext (.mov .d (.reg .rax) .rsi), 2), (.ext .ret, 1)]

def clampI30 : Block :=
  { stmts := [.cond .l (.alu 32 .cmp (.reg .rdi) (.reg .rsi))],
    regs := [],
    flags := .alu 32 .cmp (.reg .rdi) (.reg .rsi),
    rip := .sel (.v 0) (.add .rip (.imm 0x10)) (.add .rip (.imm 0x4)) }

def clampI34 : Block :=
  { stmts := [.cond .le (.alu 32 .cmp (.reg .rdi) (.reg .rdx)), .pop (.reg .rsp)],
    regs := [(.rax, .sel (.v 0) (.zext 32 (.reg .rdi)) (.zext 32 (.zext 32 (.reg .rdx)))),
      (.rsp, .add (.reg .rsp) (.imm 0x8))],
    flags := .alu 32 .cmp (.reg .rdi) (.reg .rdx),
    rip := .v 1 }

def clampI40 : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .zext 32 (.reg .rsi)), (.rsp, .add (.reg .rsp) (.imm 0x8))],
    flags := .entry,
    rip := .v 0 }

def clampAnn : Nat → MState → MState → Prop
  | 0x30, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory
  | 0x34, m0, m => Frame m0 m ∧ m.core.read .rdi = m0.core.read .rdi ∧
      m.core.read .rdx = m0.core.read .rdx ∧ (r32 .rdi m0).slt (r32 .rsi m0) = false
  | 0x40, m0, m => Frame m0 m ∧ m.core.read .rsi = m0.core.read .rsi ∧
      (r32 .rdi m0).slt (r32 .rsi m0) = true
  | _, _, _ => False

def clampCert : FunCert where
  code := code
  base := base
  blocks := [⟨0x30, clampL30⟩, ⟨0x34, clampL34⟩, ⟨0x40, clampL40⟩]
  ann := clampAnn
  measure o _ _ := match o with
    | 0x30 => 2
    | _ => 1

/-! ## `gcd_u32`: Euclid's loop with a `div` -/

/-- `0x401370`: `mov %edi,%eax; mov %esi,%edx; test %esi,%esi; je 0x401390`. -/
def gcdL00 : List (LInstr × Nat) :=
  [(.ext (.mov .d (.reg .rax) .rdi), 2), (.ext (.mov .d (.reg .rdx) .rsi), 2),
   (.ext (.test .d (.reg .rsi) .rsi), 2), (.ext (.jcc8 .e 0x18), 2)]

/-- `0x401378`: `nopl 0x0(%rax,%rax,1)`. -/
def gcdL08 : List (LInstr × Nat) := [(.ext (.nop 7), 8)]

/-- `0x401380` (the loop cut): `mov %edx,%ecx; xor %edx,%edx`. -/
def gcdL10 : List (LInstr × Nat) :=
  [(.ext (.mov .d (.reg .rcx) .rdx), 2), (.ext (.alu .d .xor (.reg .rdx) .rdx), 2)]

/-- `0x401384`: `div %ecx` (not liftable to Bir; its VC unfolds `Ext.exec`). -/
def gcdL14 : List (LInstr × Nat) := [(.ext (.div .d false (.reg .rcx)), 2)]

/-- `0x401386`: `mov %ecx,%eax; test %edx,%edx; jne 0x401380`. -/
def gcdL16 : List (LInstr × Nat) :=
  [(.ext (.mov .d (.reg .rax) .rcx), 2), (.ext (.test .d (.reg .rdx) .rdx), 2),
   (.ext (.jcc8 .ne 0xf4), 2)]

/-- `0x40138c`: `mov %ecx,%eax; ret`. -/
def gcdL1c : List (LInstr × Nat) := [(.ext (.mov .d (.reg .rax) .rcx), 2), (.ext .ret, 1)]

/-- `0x401390`: `mov %edi,%ecx; mov %ecx,%eax; ret`. -/
def gcdL20 : List (LInstr × Nat) :=
  [(.ext (.mov .d (.reg .rcx) .rdi), 2), (.ext (.mov .d (.reg .rax) .rcx), 2), (.ext .ret, 1)]

def gcdI00 : Block :=
  { stmts := [.cond .e (.test 32 (.reg .rsi) (.reg .rsi))],
    regs := [(.rax, .zext 32 (.reg .rdi)), (.rdx, .zext 32 (.reg .rsi))],
    flags := .test 32 (.reg .rsi) (.reg .rsi),
    rip := .sel (.v 0) (.add .rip (.imm 0x20)) (.add .rip (.imm 0x8)) }

def gcdI08 : Block :=
  { stmts := [], regs := [], flags := .entry, rip := .add .rip (.imm 0x8) }

def gcdI10 : Block :=
  { stmts := [],
    regs := [(.rcx, .zext 32 (.reg .rdx)), (.rdx, .zext 32 (.alu 32 .xor (.reg .rdx) (.reg .rdx)))],
    flags := .alu 32 .xor (.reg .rdx) (.reg .rdx),
    rip := .add .rip (.imm 0x4) }

def gcdI16 : Block :=
  { stmts := [.cond .ne (.test 32 (.reg .rdx) (.reg .rdx))],
    regs := [(.rax, .zext 32 (.reg .rcx))],
    flags := .test 32 (.reg .rdx) (.reg .rdx),
    rip := .sel (.v 0) (.add .rip (.imm 0xfffffffffffffffa)) (.add .rip (.imm 0x6)) }

def gcdI1c : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .zext 32 (.reg .rcx)), (.rsp, .add (.reg .rsp) (.imm 0x8))],
    flags := .entry,
    rip := .v 0 }

def gcdI20 : Block :=
  { stmts := [.pop (.reg .rsp)],
    regs := [(.rax, .zext 32 (.zext 32 (.reg .rdi))), (.rcx, .zext 32 (.reg .rdi)),
      (.rsp, .add (.reg .rsp) (.imm 0x8))],
    flags := .entry,
    rip := .v 0 }

/-- Euclid's invariant: `gcd x y = gcd a b` for the entry arguments `a`, `b`. -/
def gcdInv (m0 : MState) (x y : BitVec 32) : Prop :=
  Nat.gcd x.toNat y.toNat = Nat.gcd (r32 .rdi m0).toNat (r32 .rsi m0).toNat

def gcdAnn : Nat → MState → MState → Prop
  | 0x00, m0, m => m = m0 ∧ FnContract.AbiEntry m.core m.memory
  | 0x08, m0, m => Frame m0 m ∧ gcdInv m0 (r32 .rax m) (r32 .rdx m) ∧ r32 .rdx m ≠ 0
  | 0x10, m0, m => Frame m0 m ∧ gcdInv m0 (r32 .rax m) (r32 .rdx m) ∧ r32 .rdx m ≠ 0
  | 0x14, m0, m => Frame m0 m ∧ gcdInv m0 (r32 .rax m) (r32 .rcx m) ∧ r32 .rcx m ≠ 0 ∧
      r32 .rdx m = 0
  | 0x16, m0, m => Frame m0 m ∧ gcdInv m0 (r32 .rcx m) (r32 .rdx m) ∧
      (r32 .rdx m).toNat < (r32 .rcx m).toNat
  | 0x1c, m0, m => Frame m0 m ∧ gcdInv m0 (r32 .rcx m) 0
  | 0x20, m0, m => Frame m0 m ∧ m.core.read .rdi = m0.core.read .rdi ∧ r32 .rsi m0 = 0
  | _, _, _ => False

/-- The measure: `3·edx + 3` at the cut, decreasing through the body; above `3·2^32` before
the loop; zero at the exits. -/
def gcdMeasure : Nat → MState → MState → Nat
  | 0x00, _, _ => 3 * 2 ^ 32 + 10
  | 0x08, _, _ => 3 * 2 ^ 32 + 9
  | 0x10, _, m => 3 * (r32 .rdx m).toNat + 3
  | 0x14, _, m => 3 * (r32 .rcx m).toNat + 2
  | 0x16, _, m => 3 * (r32 .rcx m).toNat + 1
  | _, _, _ => 0

def gcdCert : FunCert where
  code := code
  base := base
  blocks := [⟨0x00, gcdL00⟩, ⟨0x08, gcdL08⟩, ⟨0x10, gcdL10⟩, ⟨0x14, gcdL14⟩, ⟨0x16, gcdL16⟩,
    ⟨0x1c, gcdL1c⟩, ⟨0x20, gcdL20⟩]
  ann := gcdAnn
  measure := gcdMeasure

end Silmaril.X86.Ladder.LeafArith
