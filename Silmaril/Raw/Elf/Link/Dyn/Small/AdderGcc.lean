module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangMain

/-! # The adder (gcc): world, certificates, listings, the stack guard

gcc's `main` calls `__isoc99_scanf` and `__printf_chk` through `.plt.sec` stubs (`endbr64;
jmp *GOT`) and checks the stack protector's guard `%fs:0x28` before returning. The guard word
is part of the world's `tls` (kept by every library step, avoided by callback stacks), and
`fsBase` is kept from the process start (`Proc.Enters`/`AtGate`). -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Hello
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

/-- The guard word `[fs + 0x28, fs + 0x30)`. -/
def Guard (fs : Word) (a : Nat) : Prop := fs.toNat + 0x28 ≤ a ∧ a < fs.toNat + 0x30

/-- The process world of `adderGcc`, with the thread pointer `fs`. -/
def adderGccWorld (b lb gate fs : Word) (rel : Bool) : World :=
  crtWorld adderGccLayout b gate none [(lsmAt lb, .libcStartMain), (cxaAt lb, .cxaFinalize),
    (scanfAt lb, .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")),
    (printfChkAt lb, .named (Silmaril.Elf.Link.DynElf.nm "__printf_chk")),
    (stackChkAt lb, .named (Silmaril.Elf.Link.DynElf.nm "__stack_chk_fail"))] rel
    (stdioNamed (Img adderGccLayout b) rel) (Guard fs)

theorem adderGcc_scanf (b lb gate fs : Word) (rel : Bool) (s : PState) (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderGccWorld b lb gate fs rel) (.named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")) s r ↔
      scanfStep (Img adderGccLayout b) s r := by
  simp only [fnStep, adderGccWorld, crtWorld, stdioNamed]
  rw [ite_eq_left trivial]

theorem adderGcc_printfChk (b lb gate fs : Word) (rel : Bool) (s : PState)
    (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderGccWorld b lb gate fs rel) (.named (Silmaril.Elf.Link.DynElf.nm "__printf_chk")) s r ↔
      printfStepWith .rsi .rdx (Img adderGccLayout b) rel s r := by
  simp only [fnStep, adderGccWorld, crtWorld, stdioNamed]
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left trivial]

/-- `__stack_chk_fail@plt`, `__printf_chk@plt`, `__isoc99_scanf@plt` (`.plt.sec`). -/
def adderGccStubs : List (Nat × List Byte) :=
  [(0x1070, [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x46, 0x2f, 0x00, 0x00]),
   (0x1080, [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x3e, 0x2f, 0x00, 0x00]),
   (0x1090, [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x36, 0x2f, 0x00, 0x00])]

/-- Their slots. -/
def adderGccGot : List (Nat × Nat) := [(0x3fc0, 0x138120), (0x3fc8, 0x137bf0), (0x3fd0, 0x5fe10)]

def adderGccGotAt (lb : Word) : List (Nat × Word) := adderGccGot.map fun s => (s.1, lb + BitVec.ofNat 64 s.2)

theorem adderGcc_info : finfo adderGccFile = some adderGccInfo := by decide +kernel
theorem adderGcc_refs : refsHold adderGccFile adderGccInfo adderGccRefs = true := by decide +kernel
theorem adderGcc_slots_K :
    slotsWith (resolveK [exeFacts adderGccRefs, libcFactsS, ldFactsS]) false adderGccFile
      adderGccInfo = some adderGccSlots := by decide +kernel
theorem adderGcc_ok : adderGccLayout.ok = true := by decide +kernel
theorem adderGcc_ok' : adderGccLayout.Facts := Layout.facts adderGcc_ok
theorem adderGcc_img : adderGccLayout.imageOk adderGccFile adderGccInfo adderGccTextPh
    adderGccRoPh adderGccRwPh adderGccSlots 0x2a200 0x472c0 = true := by decide +kernel
theorem adderGcc_extra : extraOk adderGccFile adderGccInfo adderGccTextPh adderGccRwPh
    adderGccSlots adderGccStubs adderGccGot = true := by decide +kernel

theorem adderGcc_slots {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS) (hl : ChunksOf Fl ldChunksS) :
    slots [adderGccFile, Fc, Fl] false adderGccFile adderGccInfo = some adderGccSlots := by
  have := slots_of_known (ks := [⟨adderGccFile, adderGccInfo, exeFacts adderGccRefs⟩,
      ⟨Fc, libcInfo, libcFactsS⟩, ⟨Fl, ldInfo, ldFactsS⟩])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · exact exeKnown_ok adderGcc_info adderGcc_refs
      · exact libcKnownS_ok hc
      · exact ldKnownS_ok hl) adderGcc_slots_K
  simpa using this

/-- `[fs + disp]`. -/
def memFs (d : BitVec 32) : Silmaril.X86.Ext.Mem := ⟨.fs, none, d, fun h => by cases h⟩

@[simp] theorem memFs_addr (d : BitVec 32) (c : State) (next : Word) :
    (memFs d).addr c next = c.fsBase + d.signExtend 64 := by
  simp [memFs, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Base.value]

def adderGccMainL : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4),
   (4, b8 (.aluI8 .q .sub (.reg .rsp) 0x18#8), 4),
   (8, b8 (.lea .q .rdi (Silmaril.X86.Ext.Mem.ofRip 0x00000f55#32)), 7),
   (15, b8 (.load .q .rax (memFs 0x00000028#32)), 9),
   (24, b8 (.mov .q (.mem (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000008#32)) .rax), 5),
   (29, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (31, b8 (.lea .q .rdx (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000004#32)), 5),
   (36, b8 (.mov .q (.reg .rsi) .rsp), 3),
   (39, b8 (.call 0xffffffc4#32), 5),
   (44, b8 (.mov .d (.reg .rdx) .rax), 2),
   (46, b8 (.movI32 .rax 0x00000001#32), 5),
   (51, b8 (.aluI8 .d .cmp (.reg .rdx) 0x02#8), 3),
   (54, b8 (.jcc8 .e 0x15#8), 2),
   (56, b8 (.load .q .rdx (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000008#32)), 5),
   (61, b8 (.aluR .q .sub .rdx (.mem (memFs 0x00000028#32))), 9),
   (70, b8 (.jcc8 .ne 0x23#8), 2),
   (72, b8 (.aluI8 .q .add (.reg .rsp) 0x18#8), 4),
   (76, b8 .ret, 1),
   (77, b8 (.load .d .rdx (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000004#32)), 4),
   (81, b8 (.lea .q .rsi (Silmaril.X86.Ext.Mem.ofRip 0x00000f12#32)), 7),
   (88, b8 (.aluR .d .add .rdx (.mem (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000000#32))), 3),
   (91, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (93, b8 (.movI32 .rdi 0x00000002#32), 5),
   (98, b8 (.call 0xffffff79#32), 5),
   (103, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (105, b8 (.jmp8 0xcd#8), 2)]

theorem adderGcc_mainL : listingOk adderGccLayout.cMain adderGccMainL = true := by decide +kernel

def secStubL (d : BitVec 32) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 .endbr64, 4), (4, .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d))), 6)]

theorem adderGcc_stubChk : listingOk [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x3e, 0x2f, 0x00, 0x00]
    (secStubL 0x2f3e#32) = true := by decide +kernel
theorem adderGcc_stubScanf : listingOk [0xf3, 0x0f, 0x1e, 0xfa, 0xff, 0x25, 0x36, 0x2f, 0x00, 0x00]
    (secStubL 0x2f36#32) = true := by decide +kernel

/-- **The invariant `main` gets**: the stubs and their slots, and the guard word readable at the
current thread pointer, which is `fs`. -/
def GccX (b lb fs : Word) (f : Word) (m : Memory) : Prop :=
  Extra b adderGccStubs (adderGccGotAt lb) m ∧ f = fs ∧ fs.toNat + 0x30 ≤ 2 ^ 64 ∧
    ∃ c : Word, loadN m (fs + 40#64) 8 = some c

/-- A load from kept bytes is kept. -/
theorem loadN_keeps {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') {a : Word} {k : Nat}
    (hP : ∀ i < k, P (a.toNat + i)) : loadN m' a k = loadN m a k := by
  simp only [loadN, Memory.readBytes]
  rw [Keeps.readWith h hP]

end Silmaril.Elf.Link.Dyn.Small
