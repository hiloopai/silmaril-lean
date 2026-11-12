module

public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderCert
public import Silmaril.Raw.Elf.Link.Dyn.Crt.ConstMain
public import Silmaril.Elf.Link.Dyn.Stdio.Contracts

/-! # The adder (clang): `main` -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn retOf)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

/-- The library entry points the adders call, at `libc.so.6`'s base `lb`. -/
abbrev lsmAt (lb : Word) : Word := lb + 0x2a200#64
abbrev cxaAt (lb : Word) : Word := lb + 0x472c0#64
abbrev scanfAt (lb : Word) : Word := lb + 0x5fe10#64
abbrev printfAt (lb : Word) : Word := lb + 0x60100#64
abbrev printfChkAt (lb : Word) : Word := lb + 0x137bf0#64
abbrev stackChkAt (lb : Word) : Word := lb + 0x138120#64

/-- The process world of `adderClang`. -/
def adderClangWorld (b lb gate : Word) (rel : Bool) : World :=
  crtWorld adderClangLayout b gate none [(lsmAt lb, .libcStartMain), (cxaAt lb, .cxaFinalize),
    (scanfAt lb, .named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")),
    (printfAt lb, .named (Silmaril.Elf.Link.DynElf.nm "printf"))] rel
    (stdioNamed (Img adderClangLayout b) rel)

theorem adderClang_scanf (b lb gate : Word) (rel : Bool) (s : PState) (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderClangWorld b lb gate rel) (.named (Silmaril.Elf.Link.DynElf.nm "__isoc99_scanf")) s r ↔
      scanfStep (Img adderClangLayout b) s r := by
  simp only [fnStep, adderClangWorld, crtWorld, stdioNamed]
  rw [ite_eq_left trivial]

theorem adderClang_printf (b lb gate : Word) (rel : Bool) (s : PState) (r : Silmaril.X86.RelIsa.Res PState) :
    fnStep (adderClangWorld b lb gate rel) (.named (Silmaril.Elf.Link.DynElf.nm "printf")) s r ↔
      printfStepWith .rdi .rsi (Img adderClangLayout b) rel s r := by
  simp only [fnStep, adderClangWorld, crtWorld, stdioNamed]
  rw [ite_eq_right (by decide), ite_eq_left trivial]

/-- **What `main` does.** -/
def adderPost (rel : Bool) (g g' : Ghost) (e : BitVec 32) : Prop :=
  match scanDD g.inp with
  | .ok a b rest => e = 0 ∧ g'.inp = rest ∧
      (g'.out = g.out ++ decStr (BitVec.ofInt 32 a + BitVec.ofInt 32 b).toInt ++ [10] ∨
       (rel = false ∧ ∃ p, p <+: decStr (BitVec.ofInt 32 a + BitVec.ofInt 32 b).toInt ++ [10] ∧
         g'.out = g.out ++ p))
  | .fail => e = 1 ∧ g'.out = g.out
  | .ub => True

/-- `printf@plt`/`__isoc99_scanf@plt` slots with their libc addresses. -/
def adderClangGotAt (lb : Word) : List (Nat × Word) := adderClangGot.map fun s => (s.1, lb + BitVec.ofNat 64 s.2)

def adderClangMainL : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, b8 (.push .rax), 1),
   (1, b8 (.lea .q .rdi (Silmaril.X86.Ext.Mem.ofRip 0x00000eac#32)), 7),
   (8, b8 (.lea .q .rsi (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000004#32)), 5),
   (13, b8 (.mov .q (.reg .rdx) .rsp), 3),
   (16, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (18, b8 (.call 0xfffffed9#32), 5),
   (23, b8 (.mov .d (.reg .rcx) .rax), 2),
   (25, b8 (.movI32 .rax 0x00000001#32), 5),
   (30, b8 (.aluI8 .d .cmp (.reg .rcx) 0x02#8), 3),
   (33, b8 (.jcc8 .ne 0x17#8), 2),
   (35, b8 (.load .d .rsi (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000000#32)), 3),
   (38, b8 (.aluR .d .add .rsi (.mem (Silmaril.X86.Ext.Mem.ofReg .rsp none 0x00000004#32))), 4),
   (42, b8 (.lea .q .rdi (Silmaril.X86.Ext.Mem.ofRip 0x00000e89#32)), 7),
   (49, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (51, b8 (.call 0xfffffea8#32), 5),
   (56, b8 (.alu .d .xor (.reg .rax) .rax), 2),
   (58, b8 (.pop .rcx), 1),
   (59, b8 .ret, 1)]

theorem adderClang_mainL : listingOk adderClangLayout.cMain adderClangMainL = true := by decide +kernel

def stubL (d : BitVec 32) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  [(0, .new (.jmpInd (.mem (Silmaril.X86.Ext.Mem.ofRip d))), 6)]

theorem adderClang_stub0 : listingOk [0xff, 0x25, 0xca, 0x2f, 0x00, 0x00] (stubL 0x2fca#32) = true := by
  decide +kernel
theorem adderClang_stub1 : listingOk [0xff, 0x25, 0xc2, 0x2f, 0x00, 0x00] (stubL 0x2fc2#32) = true := by
  decide +kernel

theorem addrK (b : Word) {x y : Nat} {d : BitVec 32}
    (h : BitVec.ofNat 64 x + d.signExtend 64 = BitVec.ofNat 64 y) :
    b + BitVec.ofNat 64 x + d.signExtend 64 = b + BitVec.ofNat 64 y := by
  rw [BitVec.add_assoc, h]

@[simp] theorem ofReg_addr (r : Reg) (d : BitVec 32) (c : State) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofReg r none d).addr c next = c.read r + d.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg]

/-- A sub-span of a read. -/
theorem readBytes_sub' {m : Memory} {a n : Nat} {l : List Byte} (h : m.readBytes a n = some l)
    {k j : Nat} (hj : 0 < j) (hk : k + j ≤ n) : m.readBytes (a + k) j = some ((l.drop k).take j) :=
  Silmaril.X86.Ext.readWith_sub h hj hk

theorem adderClang_ok' : adderClangLayout.Facts := Layout.facts adderClang_ok

/-- **`main` of `adderClang` meets `MainOk`** (proved: `adderClangMain_holds`, in
`AdderClangMain`). Hypotheses: the image does not wrap; `scanf` and `printf` lie outside it and are not the gate. -/
def Task.adderClangMain : Prop :=
  ∀ (b lb gate : Word) (rel : Bool), b.toNat + adderClangLayout.size < 2 ^ 64 →
    ¬ Img adderClangLayout b (scanfAt lb).toNat → ¬ Img adderClangLayout b (printfAt lb).toNat →
    scanfAt lb ≠ gate → printfAt lb ≠ gate →
    MainOk (adderClangWorld b lb gate rel) adderClangLayout b (lsmAt lb) (cxaAt lb)
      (fun _ => Extra b adderClangStubs (adderClangGotAt lb)) (fun g => scanDD g.inp ≠ .ub) (adderPost rel)

/-- Where the loader put things, for `adderClang`. -/
structure AdderPlaced (L : Layout) (b lb gate : Word) : Prop where
  base : Placed L b lb gate 0x2a200 0x472c0
  sc_out : ¬ Img L b (scanfAt lb).toNat
  pf_out : ¬ Img L b (printfAt lb).toNat
  sc_gate : scanfAt lb ≠ gate
  pf_gate : printfAt lb ≠ gate

theorem adderClang_env {b lb gate : Word} {rel : Bool} (P : AdderPlaced adderClangLayout b lb gate) :
    CrtEnv adderClangLayout (adderClangWorld b lb gate rel) b (lsmAt lb) (cxaAt lb) where
  hW := rfl
  hb := P.base.hb
  gate_out := P.base.gate_out
  cxa_out := P.base.cxa_out
  cxa_gate := P.base.cxa_gate
  cxa_res := fun _ _ h => by simp [adderClangWorld, crtWorld] at h
  cxa_fn := by simp [adderClangWorld, crtWorld]
  cxa_ne := P.base.cxa_ne
  lsm_out := P.base.lsm_out
  lsm_gate := P.base.lsm_gate
  lsm_res := fun _ _ h => by simp [adderClangWorld, crtWorld] at h
  lsm_fn := by simp [adderClangWorld, crtWorld]

/-- **The adder (clang), given `Task.adderClangMain`**: under the loader relation (eager
binding, any bases, any glibc agreeing with the chunks), from every documented initial state
whose `stdin` does not overflow `int` in `scanf`, every run ends with `main`'s behaviour
(`adderPost`): on `"a b…"` exit status `0` and `a + b` (as `int`) and a newline on `stdout`;
on input `scanf` cannot convert, exit status `1` and nothing written. -/
theorem adderClang_run (T : Task.adderClangMain) {Fc Fl : Blob} (hc : ChunksOf Fc libcChunksS)
    (hl : ChunksOf Fl ldChunksS) {b lb ldb res gate : Word} {ifn : Word → Option Word}
    {rel : Bool} {s : PState}
    (hload : ExeLoaded [adderClangFile, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : AdderPlaced adderClangLayout b lb gate)
    (hs : AtEntry adderClangLayout (adderClangWorld b lb gate rel) b s)
    (hin : scanDD s.g.inp ≠ .ub) :
    MustQ (adderClangWorld b lb gate rel) (Ends s.g (adderPost rel) rel) s := by
  have F := Layout.facts adderClang_ok
  obtain ⟨argc, hargc⟩ := hs.argc
  have hD := adderClang_slots hc hl
  exact crt_run F (adderClang_env P) rfl rfl
    (X := fun _ => Extra b adderClangStubs (adderClangGotAt lb))
    (fun _ _ _ hk hx => hx.keep (L := adderClangLayout) P.base.hb (by decide)
      (by simp [adderClangGotAt, adderClangGot, adderClangLayout]) (keeps_img rfl hk))
    (T b lb gate rel P.base.hb P.sc_out P.pf_out P.sc_gate P.pf_gate) hs.done
    (extra_of_loaded adderClang_info hD adderClang_extra hload) hs.atexit
    (crtMem_of_loaded adderClang_info hD adderClang_img hload) hs.rip hs.al hs.room hargc hin

end Silmaril.Elf.Link.Dyn.Small
