module

public import Silmaril.Raw.Elf.Link.Dyn.Crt.Run
public import Silmaril.Raw.Elf.Link.Dyn.Crt.Image

/-! # `main` returning a constant

`int main(void) { return K; }` compiles, at `-O2`, to `[endbr64;] xor %eax,%eax; ret` (`K = 0`)
or `[endbr64;] mov $K,%eax; ret`. `constMain_ok`: such a `main` meets `MainOk` with nothing
changed in the library state and `eax = K`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Crt

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.X86.Link (Blob)

/-- The listing of a constant `main`: `endbr64` when `ibt`, then `xor %eax,%eax` (`k = none`)
or `mov $k,%eax`, then `ret`. -/
def constMainL (ibt : Bool) (k : Option (BitVec 32)) : List (Nat × Silmaril.X86.Ext9.Instr × Nat) :=
  let o := if ibt then 4 else 0
  let l := match k with | none => 2 | some _ => 5
  (if ibt then [(0, b8 .endbr64, 4)] else []) ++
  [(o, match k with
      | none => b8 (.alu .d .xor (.reg .rax) .rax)
      | some v => b8 (.movI32 .rax v), l),
   (o + l, b8 .ret, 1)]

/-- The value a constant `main` returns. -/
def constMainV : Option (BitVec 32) → BitVec 32
  | none => 0
  | some v => v

theorem listingOk_bound {code : List Byte} {Ls : List (Nat × Silmaril.X86.Ext9.Instr × Nat)}
    (hL : listingOk code Ls = true) {o l : Nat} {i : Silmaril.X86.Ext9.Instr} (hm : (o, i, l) ∈ Ls) :
    o + l ≤ code.length := by
  have := List.all_eq_true.mp hL _ hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **A constant `main` meets `MainOk`.** -/
theorem constMain_ok {L : Layout} (F : L.Facts) {b lsmA cxaA : Word} {W : World}
    (hW : W.InImage = Img L b) (hb : b.toNat + L.size < 2 ^ 64) {ibt : Bool}
    {k : Option (BitVec 32)} (hL : listingOk L.cMain (constMainL ibt k) = true) :
    MainOk W L b lsmA cxaA (fun _ _ => True) (fun _ => True) (fun g g' e => g' = g ∧ e = constMainV k) := by
  intro Q t hd hrip _ hret _ hm _ _ kk
  have hs := F.size
  have hmn := F.bMain
  have hin : ∀ n, n < L.size → W.InImage (b + BitVec.ofNat 64 n).toNat :=
    fun n hn => hW ▸ img_add hb hn
  cases ibt <;> cases k
  · have := listingOk_bound hL (o := 2) (l := 1) (i := b8 .ret) (by simp [constMainL])
    refine must_listed (o := 0) hL rfl hd (by rw [hrip]; exact hin _ (by omega))
      hm.main (by rw [hrip]; simp) ?_
    xstep [hrip]
    refine must_listed (o := 2) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep [Silmaril.X86.popWord, hret]
    exact kk _ rfl rfl rfl hd hm ⟨rfl, by simp [low32, constMainV, Silmaril.X86.Ext.AluOp.resultN]⟩
  · rename_i v
    have := listingOk_bound hL (o := 5) (l := 1) (i := b8 .ret) (by simp [constMainL])
    refine must_listed (o := 0) hL rfl hd (by rw [hrip]; exact hin _ (by omega))
      hm.main (by rw [hrip]; simp) ?_
    xstep [hrip]
    refine must_listed (o := 5) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep [Silmaril.X86.popWord, hret]
    exact kk _ rfl rfl rfl hd hm ⟨rfl, by simp [low32, constMainV]⟩
  · have := listingOk_bound hL (o := 6) (l := 1) (i := b8 .ret) (by simp [constMainL])
    refine must_listed (o := 0) hL rfl hd (by rw [hrip]; exact hin _ (by omega))
      hm.main (by rw [hrip]; simp) ?_
    xstep [hrip]
    refine must_listed (o := 4) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 6) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep [Silmaril.X86.popWord, hret]
    exact kk _ rfl rfl rfl hd hm ⟨rfl, by simp [low32, constMainV, Silmaril.X86.Ext.AluOp.resultN]⟩
  · rename_i v
    have := listingOk_bound hL (o := 9) (l := 1) (i := b8 .ret) (by simp [constMainL])
    refine must_listed (o := 0) hL rfl hd (by rw [hrip]; exact hin _ (by omega))
      hm.main (by rw [hrip]; simp) ?_
    xstep [hrip]
    refine must_listed (o := 4) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep []
    refine must_listed (o := 9) hL rfl hd (hin _ (by omega)) hm.main
      (by rw [ripadd]) ?_
    xstep [Silmaril.X86.popWord, hret]
    exact kk _ rfl rfl rfl hd hm ⟨rfl, by simp [low32, constMainV]⟩

/-- **Where the loader put things** (an assumption about the loader's placement, not about the
program): the executable's image does not wrap; `__libc_start_main`, `__cxa_finalize` and the
library's callback gate lie outside it and are distinct; `__cxa_finalize` is not at `0`. -/
structure Placed (L : Layout) (b lb gate : Word) (lsmOff cxaOff : Nat) : Prop where
  hb : b.toNat + L.size < 2 ^ 64
  gate_out : ¬ Img L b gate.toNat
  lsm_out : ¬ Img L b (lb + BitVec.ofNat 64 lsmOff).toNat
  cxa_out : ¬ Img L b (lb + BitVec.ofNat 64 cxaOff).toNat
  lsm_gate : lb + BitVec.ofNat 64 lsmOff ≠ gate
  cxa_gate : lb + BitVec.ofNat 64 cxaOff ≠ gate
  lsm_cxa : lb + BitVec.ofNat 64 lsmOff ≠ lb + BitVec.ofNat 64 cxaOff
  cxa_ne : lb + BitVec.ofNat 64 cxaOff ≠ 0#64

/-- The process world of an executable linked with this runtime, bound eagerly. -/
def smallWorld (L : Layout) (b lb gate : Word) (lsmOff cxaOff : Nat) (rel : Bool) : World :=
  crtWorld L b gate none [(lb + BitVec.ofNat 64 lsmOff, .libcStartMain),
    (lb + BitVec.ofNat 64 cxaOff, .cxaFinalize)] rel

/-- **The documented initial state** of the process at the executable's entry (after `ld.so`):
the library state fresh, `rip` at `_start`, `rsp` 16-byte aligned with `argc` at `[rsp]` and a
usable stack. -/
structure AtEntry (L : Layout) (W : World) (b : Word) (s : PState) : Prop where
  done : s.g.done = none
  atexit : s.g.atexit = []
  rip : s.m.core.rip = b + BitVec.ofNat 64 L.start
  al : (s.m.core.read .rsp).toNat % 16 = 0
  room : StackRoom W s.m.memory (s.m.core.read .rsp)
  argc : ∃ argc : Word, s.m.memory.readBytes (s.m.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [argc])

theorem Placed.env {L : Layout} {b lb gate : Word} {lsmOff cxaOff : Nat} {rel : Bool}
    (P : Placed L b lb gate lsmOff cxaOff) :
    CrtEnv L (smallWorld L b lb gate lsmOff cxaOff rel) b (lb + BitVec.ofNat 64 lsmOff)
      (lb + BitVec.ofNat 64 cxaOff) where
  hW := rfl
  hb := P.hb
  gate_out := P.gate_out
  cxa_out := P.cxa_out
  cxa_gate := P.cxa_gate
  cxa_res := fun _ _ h => by simp [smallWorld, crtWorld] at h
  cxa_fn := by simp [smallWorld, crtWorld, P.lsm_cxa]
  cxa_ne := P.cxa_ne
  lsm_out := P.lsm_out
  lsm_gate := P.lsm_gate
  lsm_res := fun _ _ h => by simp [smallWorld, crtWorld] at h
  lsm_fn := by simp [smallWorld, crtWorld]

/-- **An executable whose `main` returns a constant `K`** exits with status `K mod 256`, having
written to `stdout` nothing beyond what was already there, from every documented initial
state of every eager load. -/
theorem exe_const {L : Layout} (hL : L.ok = true) {f Fc Fl : Blob} {i : Elf.DynInfo}
    {D : List (Nat × Val)} (hi : finfo f = some i) (hD : slots [f, Fc, Fl] false f i = some D)
    {tx ro rw : Elf.Phdr} {lsmOff cxaOff : Nat}
    (himg : L.imageOk f i tx ro rw D lsmOff cxaOff = true) {ibt : Bool} {k : Option (BitVec 32)}
    (hmain : listingOk L.cMain (constMainL ibt k) = true)
    {b lb ldb res gate : Word} {ifn : Word → Option Word} {rel : Bool} {s : PState}
    (hload : ExeLoaded [f, Fc, Fl] [b, lb, ldb] ifn false res s.m.memory)
    (P : Placed L b lb gate lsmOff cxaOff)
    (hs : AtEntry L (smallWorld L b lb gate lsmOff cxaOff rel) b s) :
    MustQ (smallWorld L b lb gate lsmOff cxaOff rel)
      (fun u => ∃ w, u.g.done = some ((constMainV k).toNat % 256, w) ∧ w <+: s.g.out ∧
        (rel = true → w = s.g.out)) s := by
  have F := Layout.facts hL
  obtain ⟨argc, hargc⟩ := hs.argc
  have := crt_run F P.env (by rfl) (by rfl) (X := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (constMain_ok (W := smallWorld L b lb gate lsmOff cxaOff rel) F rfl P.hb hmain) hs.done
    trivial hs.atexit (crtMem_of_loaded hi hD himg hload) hs.rip hs.al hs.room hargc trivial
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_ this
  rintro u ⟨g', e, w, ⟨rfl, rfl⟩, hd, hw, hrel⟩
  refine ⟨w, ?_, hw, hrel⟩
  rw [hd]; simp

end Silmaril.Elf.Link.Dyn.Crt
