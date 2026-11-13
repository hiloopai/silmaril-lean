module

public import Silmaril.Machine.X86.BlockCert.Store.Defs
public import Silmaril.Machine.X86.BlockCert.Thms

/-!
# Writing blocks are runs of the open machine; assembly

* `execBlockW_open`: a listing that `listingAtW` accepts at the program counter of a loaded
  image, and that executes, is a run of `Open.step`. Every instruction but the last keeps the
  memory (`BlockCert.exec_mem`), so each is fetched from the loaded entry image; the last one
  is fetched before it writes.
* `from_blockW`, `totalW`: strong induction on the block measure, as `BlockCert.from_block`,
  with the code image's loadedness carried by `NextW`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert.Store

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Lift.Bir (LInstr XState XResult execBlock Block liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.BlockCert

theorem execL_toExt {i : LInstr} {e : Silmaril.X86.Ext.Instr} (h : toExt i = some e)
    (s : XState) (mem : Memory) (len : Nat) :
    i.exec s mem len = liftR s.xmm (Silmaril.X86.Ext.exec e s.core mem len) := by
  unfold toExt at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem open_decode {bytes : List Byte} {e : Silmaril.X86.Ext.Instr} {l : Nat}
    (h : Silmaril.X86.Ext.decode bytes = some (e, l)) :
    Open.decode bytes = some (.base e, l) := by
  simp [Open.decode, Silmaril.X86.Ext8.decode_of_ext h]

/-- **The bridge with a final write.** -/
theorem execBlockW_open {code : List Byte} {base : Word} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Lift.Bir.Xmm)
      (mem : Memory) (s' : XState) (mem' : Memory),
      listingAtW code o L = true → Loaded mem base code → c.rip = base + BitVec.ofNat 64 o →
      execBlock L ⟨c, x⟩ mem = .ok s' mem' →
      Reaches Open.step ⟨c, mem⟩ ⟨s'.core, mem'⟩
  | [], _, c, x, mem, s', mem', _, _, _, h => by
    simp only [execBlock] at h
    cases h
    exact Reaches.refl _ _
  | (i, l) :: rest, o, c, x, mem, s', mem', hok, hl, hrip, h => by
    simp only [listingAtW] at hok
    split at hok
    · cases hok
    rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hdec, hfit⟩, hft⟩, hrest⟩ := hok
    simp only [execBlock] at h
    rw [execL_toExt he] at h
    cases hx : Silmaril.X86.Ext.exec e c mem l with
    | ok c1 m1 =>
      rw [hx] at h
      simp only [liftR] at h
      have hs : Open.step ⟨c, mem⟩ = some ⟨c1, m1⟩ :=
        Open.step_of_listed (m := ⟨c, mem⟩) hl hrip hfit (open_decode hdec) hx
      cases rest with
      | nil =>
        simp only [execBlock] at h
        cases h
        exact Silmaril.X86.SegVC.reaches_head (I := Open.isa) hs
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or, Bool.and_eq_true] at hft
        have hm1 : m1 = mem := exec_mem hft.1 hx
        subst hm1
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec_rip hft.2 hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        have hr := execBlockW_open (nx :: rest') (o + l) c1 x m1 s' mem' hrest hl hrip1 h
        exact Silmaril.X86.SegVC.reaches_cons (I := Open.isa) hs hr
    | dataFault => rw [hx] at h; cases h
    | divideError => rw [hx] at h; cases h
    | undefinedCondition _ => rw [hx] at h; cases h
    | trap => rw [hx] at h; cases h

theorem runLW_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAtW code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    Reaches Open.step m m' := by
  unfold runL ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlockW_open L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

theorem checkedW_mem {F : FunCert} (hc : F.checkedW = true) {b : Blk} (hb : b ∈ F.blocks) :
    listingAtW F.code b.off b.instrs = true :=
  List.all_eq_true.mp hc b hb

theorem from_blockW {F : FunCert} {Q : MState → MState → Prop} (hc : F.checkedW = true)
    (hvc : F.VCW Q) (m0 : MState) :
    ∀ (w : Nat) (b : Blk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code → ∃ t, Reaches Open.step m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    obtain ⟨m', hrun, hnext⟩ := hvc b hb m0 m ha hrip hl
    have hr := runLW_open (checkedW_mem hc hb) hl hrip hrun
    rcases hnext with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · obtain ⟨t, hr', hq⟩ := ih _ (hw ▸ hlt) b' m' rfl hb' ha' hrip' hl'
      exact ⟨t, hr.trans hr', hq⟩

theorem totalW {F : FunCert} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa := by
  intro m _ hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_blockW hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.Machine.X86.BlockCert.Store
