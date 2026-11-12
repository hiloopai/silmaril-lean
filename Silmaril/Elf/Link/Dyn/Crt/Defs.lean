module

public import Silmaril.Elf.Link.Dyn.Proc.Defs

/-! # The C runtime of a gcc/clang PIE executable, once for every binary

Every default PIE executable that gcc or clang links against glibc on x86-64 starts and ends in
the same code: glibc's `Scrt1.o` (`_start`), `crti.o`/`crtn.o` (`_init`, `_fini`) and GCC's
`crtbeginS.o` (`deregister_tm_clones`, `register_tm_clones`, `__do_global_dtors_aux`,
`frame_dummy`), plus the linker's `.plt.got` stub for `__cxa_finalize`. Only the placement of
these functions and of the data they address differs between executables, and with it the
rip-relative displacements in their instructions.

A `Layout` records that placement (offsets from the load base) and the bytes of each function
as linked. Each function's **listing** is given here once, as a function of the layout
(`initL`, `startL`, …): the instruction forms are fixed, the displacements are computed
(`rel`). `Layout.ok` is the one per-binary check (a closed Boolean, `decide +kernel`): each
function's bytes decode as its listing, and the offsets are small enough for the
displacement arithmetic. The proofs about the runtime (`Silmaril.Raw.Elf.Link.Dyn.Crt`)
are over an arbitrary layout with `Layout.ok`, so per executable only `main` and the binding
certificate remain.

`CrtMem L b lsmA cxaA cv mem`: what the loaded image provides to the runtime code at base
`b`: the functions' bytes, the GOT slots (`__libc_start_main` bound to `lsmA`,
`__cxa_finalize` to `cxaA`, the weak `__gmon_start__` and `_ITM_*` unbound, `0`),
`__dso_handle` and the byte `completed.0` (`cv`).

`crtWorld`: the process world of such an executable (`Proc.World`): `DT_INIT` then
`DT_INIT_ARRAY` (`_init`, `frame_dummy`), `DT_FINI_ARRAY` then `DT_FINI`
(`__do_global_dtors_aux`, `_fini`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte Reg AluOp)
open Silmaril.X86.Ext (Mem RM Sz Cond Instr ShiftOp Count)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.Dyn.Proc

/-- The rip-relative displacement from `next` to `target` (offsets from the load base). -/
def rel (next target : Nat) : BitVec 32 := BitVec.ofInt 32 ((target : Int) - next)

/-- **The placement of the C runtime in an executable**: offsets from the load base. -/
structure Layout : Type where
  /-- Extent of the image (end of the last `PT_LOAD`). -/
  size : Nat
  init : Nat
  start : Nat
  dereg : Nat
  reg : Nat
  dtors : Nat
  fdummy : Nat
  fini : Nat
  main : Nat
  /-- The `.plt.got` stub of `__cxa_finalize`, with (`ibt`, gcc) or without (clang) `endbr64`. -/
  plt : Nat
  ibt : Bool
  gotLsm : Nat
  gotDereg : Nat
  gotGmon : Nat
  gotReg : Nat
  gotCxa : Nat
  /-- `__TMC_END__`. -/
  tmc : Nat
  dso : Nat
  /-- `completed.0`, the flag `__do_global_dtors_aux` sets: `__TMC_END__` itself unless other
  `.bss` objects (a copy-relocated `stdout`) come first. -/
  cmpl : Nat := tmc
  /-- The bytes of each function, as linked. -/
  cInit : List Byte
  cStart : List Byte
  cDereg : List Byte
  cReg : List Byte
  cDtors : List Byte
  cFdummy : List Byte
  cFini : List Byte
  cPlt : List Byte
  /-- `main`'s bytes, and a read-only slice (`.rodata`) at `ro`. -/
  cMain : List Byte
  ro : Nat
  cRo : List Byte

/-- A base `Ext` instruction as an `Ext9` one. -/
abbrev b8 (i : Instr) : Silmaril.X86.Ext9.Instr := .ext8 (.base i)

/-- `_init` (`crti.o`): call `__gmon_start__` if bound. -/
def initL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, b8 (.aluI8 .q .sub (.reg .rsp) 0x08#8), 4),
   (8, b8 (.load .q .rax (Mem.ofRip (rel (L.init + 15) L.gotGmon))), 7),
   (15, b8 (.test .q (.reg .rax) .rax), 3), (18, b8 (.jcc8 .e 0x02#8), 2),
   (20, .new (.callInd (.reg .rax)), 2), (22, b8 (.aluI8 .q .add (.reg .rsp) 0x08#8), 4),
   (26, b8 .ret, 1)]

/-- `_start` (`Scrt1.o`). -/
def startL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, b8 (.alu .d .xor (.reg .rbp) .rbp), 2),
   (6, b8 (.mov .q (.reg .r9) .rdx), 3), (9, b8 (.pop .rsi), 1),
   (10, b8 (.mov .q (.reg .rdx) .rsp), 3), (13, b8 (.aluI8 .q .and (.reg .rsp) 0xf0#8), 4),
   (17, b8 (.push .rax), 1), (18, b8 (.push .rsp), 1),
   (19, b8 (.alu .d .xor (.reg .r8) .r8), 3), (22, b8 (.alu .d .xor (.reg .rcx) .rcx), 2),
   (24, b8 (.lea .q .rdi (Mem.ofRip (rel (L.start + 31) L.main))), 7),
   (31, .new (.callInd (.mem (Mem.ofRip (rel (L.start + 37) L.gotLsm)))), 6)]

/-- `deregister_tm_clones` (`crtbeginS.o`). -/
def deregL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 (.lea .q .rdi (Mem.ofRip (rel (L.dereg + 7) L.tmc))), 7),
   (7, b8 (.lea .q .rax (Mem.ofRip (rel (L.dereg + 14) L.tmc))), 7),
   (14, b8 (.alu .q .cmp (.reg .rax) .rdi), 3), (17, b8 (.jcc8 .e 0x15#8), 2),
   (19, b8 (.load .q .rax (Mem.ofRip (rel (L.dereg + 26) L.gotDereg))), 7),
   (26, b8 (.test .q (.reg .rax) .rax), 3), (29, b8 (.jcc8 .e 0x09#8), 2),
   (31, .new (.jmpInd (.reg .rax)), 2), (40, b8 .ret, 1)]

/-- `register_tm_clones` (`crtbeginS.o`). -/
def regL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 (.lea .q .rdi (Mem.ofRip (rel (L.reg + 7) L.tmc))), 7),
   (7, b8 (.lea .q .rsi (Mem.ofRip (rel (L.reg + 14) L.tmc))), 7),
   (14, b8 (.alu .q .sub (.reg .rsi) .rdi), 3), (17, b8 (.mov .q (.reg .rax) .rsi), 3),
   (20, b8 (.shift .q .shr (.reg .rsi) (.imm 0x3f#8)), 4),
   (24, b8 (.shift .q .sar (.reg .rax) (.imm 0x03#8)), 4),
   (28, b8 (.alu .q .add (.reg .rsi) .rax), 3), (31, b8 (.shift .q .sar (.reg .rsi) .one), 3),
   (34, b8 (.jcc8 .e 0x14#8), 2),
   (36, b8 (.load .q .rax (Mem.ofRip (rel (L.reg + 43) L.gotReg))), 7),
   (43, b8 (.test .q (.reg .rax) .rax), 3), (46, b8 (.jcc8 .e 0x08#8), 2),
   (48, .new (.jmpInd (.reg .rax)), 2), (56, b8 .ret, 1)]

/-- `__do_global_dtors_aux` (`crtbeginS.o`). -/
def dtorsL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, b8 (.cmpI8 (.mem (Mem.ofRip (rel (L.dtors + 11) L.cmpl))) 0x00#8), 7),
   (11, b8 (.jcc8 .ne 0x2b#8), 2), (13, b8 (.push .rbp), 1),
   (14, b8 (.aluI8 .q .cmp (.mem (Mem.ofRip (rel (L.dtors + 22) L.gotCxa))) 0x00#8), 8),
   (22, b8 (.mov .q (.reg .rbp) .rsp), 3), (25, b8 (.jcc8 .e 0x0c#8), 2),
   (27, b8 (.load .q .rdi (Mem.ofRip (rel (L.dtors + 34) L.dso))), 7),
   (34, b8 (.call (rel (L.dtors + 39) L.plt)), 5),
   (39, b8 (.call (rel (L.dtors + 44) L.dereg)), 5),
   (44, b8 (.movI8 (.mem (Mem.ofRip (rel (L.dtors + 51) L.cmpl))) 0x01#8), 7),
   (51, b8 (.pop .rbp), 1), (52, b8 .ret, 1), (56, b8 .ret, 1)]

/-- `frame_dummy` (`crtbeginS.o`): a tail call of `register_tm_clones`. -/
def fdummyL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, b8 (.jmp (rel (L.fdummy + 9) L.reg)), 5)]

/-- `_fini` (`crti.o`/`crtn.o`). -/
def finiL : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, b8 (.aluI8 .q .sub (.reg .rsp) 0x08#8), 4),
   (8, b8 (.aluI8 .q .add (.reg .rsp) 0x08#8), 4), (12, b8 .ret, 1)]

/-- The offset of the `jmp` in the `__cxa_finalize` stub. -/
def pltJ (L : Layout) : Nat := if L.ibt then 4 else 0

/-- The `.plt.got` stub of `__cxa_finalize`. -/
def pltL (L : Layout) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  (if L.ibt then [(0, b8 .endbr64, 4)] else []) ++
  [(pltJ L, .new (.jmpInd (.mem (Mem.ofRip (rel (L.plt + pltJ L + 6) L.gotCxa)))), 6)]

/-- **The per-binary check**: every function decodes as its listing; the offsets fit the
displacement arithmetic (`< 2^31`) and the image; `completed.0` lies apart from the code and
the GOT slots. -/
def Layout.ok (L : Layout) : Bool :=
  listingOk L.cInit (initL L) && listingOk L.cStart (startL L) &&
  listingOk L.cDereg (deregL L) && listingOk L.cReg (regL L) &&
  listingOk L.cDtors (dtorsL L) && listingOk L.cFdummy (fdummyL L) &&
  listingOk L.cFini finiL && listingOk L.cPlt (pltL L) &&
  decide (L.size < 2 ^ 31) &&
  decide (L.cInit.length = 27 ∧ L.cStart.length = 37 ∧ L.cDereg.length = 41 ∧
    L.cReg.length = 57 ∧ L.cDtors.length = 57 ∧ L.cFdummy.length = 9 ∧ L.cFini.length = 13 ∧
    L.cPlt.length = pltJ L + 6 ∧ 0 < L.cMain.length ∧ 0 < L.cRo.length) &&
  [L.init + L.cInit.length, L.start + L.cStart.length, L.dereg + L.cDereg.length,
    L.reg + L.cReg.length, L.dtors + L.cDtors.length, L.fdummy + L.cFdummy.length,
    L.fini + L.cFini.length, L.plt + L.cPlt.length, L.main + L.cMain.length, L.ro + L.cRo.length,
    L.gotLsm + 8,
    L.gotDereg + 8, L.gotGmon + 8, L.gotReg + 8, L.gotCxa + 8, L.cmpl + 1,
    L.dso + 8].all (fun e => decide (e ≤ L.size)) &&
  [L.init + L.cInit.length, L.start + L.cStart.length, L.dereg + L.cDereg.length,
    L.reg + L.cReg.length, L.dtors + L.cDtors.length, L.fdummy + L.cFdummy.length,
    L.fini + L.cFini.length, L.plt + L.cPlt.length, L.main + L.cMain.length, L.ro + L.cRo.length,
    L.gotLsm + 8, L.gotDereg + 8,
    L.gotGmon + 8, L.gotReg + 8, L.gotCxa + 8, L.dso + 8].all (fun e => decide (e ≤ L.tmc)) &&
  decide (L.tmc ≤ L.cmpl)

/-- The executable's image at base `b`. -/
def Img (L : Layout) (b : Word) (a : Nat) : Prop := b.toNat ≤ a ∧ a < b.toNat + L.size

/-- **What the loaded image provides to the runtime.** -/
structure CrtMem (L : Layout) (b lsmA cxaA : Word) (cv : Byte) (mem : Memory) : Prop where
  init : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.init) L.cInit
  start : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.start) L.cStart
  dereg : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.dereg) L.cDereg
  reg : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.reg) L.cReg
  dtors : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.dtors) L.cDtors
  fdummy : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.fdummy) L.cFdummy
  fini : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.fini) L.cFini
  plt : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.plt) L.cPlt
  main : Silmaril.X86.Ext.Loaded mem (b + BitVec.ofNat 64 L.main) L.cMain
  rodata : mem.readBytes (b + BitVec.ofNat 64 L.ro).toNat L.cRo.length = some L.cRo
  lsm : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.gotLsm) 8 = some lsmA
  gDereg : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.gotDereg) 8 = some 0#64
  gGmon : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.gotGmon) 8 = some 0#64
  gReg : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.gotReg) 8 = some 0#64
  cxa : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.gotCxa) 8 = some cxaA
  dso : Silmaril.X86.Ext.loadN mem (b + BitVec.ofNat 64 L.dso) 8 = some (b + BitVec.ofNat 64 L.dso)
  done : mem.readBytes (b + BitVec.ofNat 64 L.cmpl).toNat 1 = some [cv]
  wDone : mem.Permitted .write (b + BitVec.ofNat 64 L.cmpl).toNat 1

/-- **Where the library is**: the image does not wrap; the bindings of `__libc_start_main`
and `__cxa_finalize` and the callback gate lie outside the image, are distinct, and are what
the world's library steps are keyed by. -/
structure CrtEnv (L : Layout) (W : World) (b lsmA cxaA : Word) : Prop where
  hW : W.InImage = Img L b
  hb : b.toNat + L.size < 2 ^ 64
  gate_out : ¬ Img L b W.gate.toNat
  cxa_out : ¬ Img L b cxaA.toNat
  cxa_gate : cxaA ≠ W.gate
  cxa_res : ∀ res slots, W.lazy = some (res, slots) → cxaA ≠ res
  cxa_fn : W.fns.find? (·.1 == cxaA) = some (cxaA, .cxaFinalize)
  cxa_ne : cxaA ≠ 0#64
  lsm_out : ¬ Img L b lsmA.toNat
  lsm_gate : lsmA ≠ W.gate
  lsm_res : ∀ res slots, W.lazy = some (res, slots) → lsmA ≠ res
  lsm_fn : W.fns.find? (·.1 == lsmA) = some (lsmA, .libcStartMain)

/-- **The process world** of an executable with this runtime, at base `b`. -/
def crtWorld (L : Layout) (b gate : Word) (lazy : Option (Word × List (Nat × Word)))
    (fns : List (Word × Fn)) (rel : Bool)
    (named : Name → PState → Silmaril.X86.RelIsa.Res PState → Prop := fun _ _ r => r = .stop)
    (tls : Nat → Prop := fun _ => False) : World where
  base := b
  size := L.size
  inits := [b + BitVec.ofNat 64 L.init, b + BitVec.ofNat 64 L.fdummy]
  finis := [b + BitVec.ofNat 64 L.dtors, b + BitVec.ofNat 64 L.fini]
  gate := gate
  lazy := lazy
  fns := fns
  reliable := rel
  named := named
  tls := tls

end Silmaril.Elf.Link.Dyn.Crt
