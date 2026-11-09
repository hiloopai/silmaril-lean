module

public import Silmaril.X86.BlockCert.Defs
import Silmaril.X86.Open.Thms
import Silmaril.X86.BlockCert9.Thms

/-!
# Bir9 block certificates are runs of the open machine

* `execL_toExt`: a listed instruction executes as the `Ext` instruction `toExt` gives;
* `execBlock_open`: a listing that `listingAt` accepts at the program counter of a loaded
  image, and that executes, is a run of `Open.step`, with the memory unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM retire)
open Silmaril.X86.Bir9 (LInstr XState XResult execBlock Block liftBlock liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.X86
open Silmaril.X86.BlockCert

/-- A listed instruction executes as the `Ext` instruction it denotes. -/
theorem execL_toExt {i : LInstr} {e : Silmaril.X86.Ext.Instr} (h : toExt i = some e)
    (s : XState) (mem : Memory) (len : Nat) :
    i.exec s mem len = liftR s.xmm (Silmaril.X86.Ext.exec e s.core mem len) := by
  unfold toExt at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem liftR_ok {x : Silmaril.X86.Bir9.Xmm} {r : Silmaril.X86.Ext.Result} {s : XState}
    {mem : Memory} (h : liftR x r = .ok s mem) :
    r = .ok s.core mem ∧ s.xmm = x := by
  cases r <;> cases h
  exact ⟨rfl, rfl⟩

/-- An `Ext` decode of the slice is an open-machine decode. -/
theorem open_decode {bytes : List Byte} {e : Silmaril.X86.Ext.Instr} {l : Nat}
    (h : Silmaril.X86.Ext.decode bytes = some (e, l)) :
    Open.decode bytes = some (.base e, l) := by
  simp [Open.decode, Silmaril.X86.Ext8.decode_of_ext h]

/-- **The bridge.** A listing checked at the program counter of a loaded image that executes
is a run of the open machine; the memory is unchanged. -/
theorem execBlock_open {code : List Byte} {base : Word} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Bir9.Xmm)
      (mem : Memory) (s' : XState) (mem' : Memory),
      listingAt code o L = true → Loaded mem base code → c.rip = base + BitVec.ofNat 64 o →
      execBlock L ⟨c, x⟩ mem = .ok s' mem' →
      Reaches Open.step ⟨c, mem⟩ ⟨s'.core, mem'⟩ ∧ mem' = mem
  | [], _, c, x, mem, s', mem', _, _, _, h => by
    simp only [execBlock] at h
    cases h
    exact ⟨Reaches.refl _ _, rfl⟩
  | (i, l) :: rest, o, c, x, mem, s', mem', hok, hl, hrip, h => by
    simp only [listingAt] at hok
    split at hok
    · cases hok
    rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hdec, hfit⟩, hnw⟩, hft⟩, hrest⟩ := hok
    simp only [execBlock] at h
    rw [execL_toExt he] at h
    cases hx : Silmaril.X86.Ext.exec e c mem l with
    | ok c1 m1 =>
      rw [hx] at h
      simp only [liftR] at h
      have hm1 : m1 = mem := BlockCert9.exec_mem hnw hx
      subst hm1
      have hs : Open.step ⟨c, m1⟩ = some ⟨c1, m1⟩ :=
        Open.step_of_listed (m := ⟨c, m1⟩) hl hrip hfit (open_decode hdec) hx
      cases rest with
      | nil =>
        simp only [execBlock] at h
        cases h
        exact ⟨Silmaril.X86.SegVC.reaches_head (I := Open.isa) hs, rfl⟩
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or] at hft
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [BlockCert9.exec_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        obtain ⟨hr, hm⟩ := execBlock_open (nx :: rest') (o + l) c1 x m1 s' mem' hrest hl hrip1 h
        exact ⟨Silmaril.X86.SegVC.reaches_cons (I := Open.isa) hs hr, hm⟩
    | dataFault => rw [hx] at h; cases h
    | divideError => rw [hx] at h; cases h
    | undefinedCondition _ => rw [hx] at h; cases h
    | trap => rw [hx] at h; cases h

/-- The bridge on machine states: a checked listing whose run succeeds is an open run. -/
theorem runL_open {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    Reaches Open.step m m' ∧ m'.memory = m.memory := by
  unfold runL Silmaril.X86.Bir9.ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlock_open L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

/-- A lifted listing runs as its Bir9 block. -/
theorem runL_eq_runB {L : List (LInstr × Nat)} {b : Block} (h : liftBlock L = some b)
    (m : MState) : runL L m = runB b m := by
  simp only [runL, runB, Silmaril.X86.Bir9.liftBlock_sound h]

end Silmaril.Proofs.X86.BlockCert
