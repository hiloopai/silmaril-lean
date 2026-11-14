module

public import Silmaril.Machine.X86.BlockCert.Defs
import Silmaril.Machine.X86.Open.Thms

/-!
# Bir block certificates are runs of the open machine

* `exec_rip`, `exec_mem`: a retired `X86.Ext` instruction that falls through sets `rip` to
  the next instruction; one that writes no memory leaves the memory unchanged (case analysis
  over `Ext.exec`, once);
* `execL_toExt`: a listed instruction executes as the `Ext` instruction `toExt` gives;
* `execBlock_open`: a listing that `listingAt` accepts at the program counter of a loaded
  image, and that executes, is a run of `Open.step`, with the memory unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded RM retire)
open Silmaril.X86.Lift.Bir (LInstr XState XResult execBlock Block liftBlock liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.BlockCert

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Silmaril.X86.Ext (writeRM writeRM8 writeNarrow aluStep aluStepR readRM)

theorem map_some {α β : Type} {f : α → β} {x : Option α} {p : β}
    (h : Option.map f x = some p) : ∃ a, f a = p := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, Option.some.inj h⟩

theorem retire_ok {next : Word} {o : Option (State × Memory)} {s : State} {m : Memory}
    (h : retire next o = .ok s m) :
    s.rip = next ∧ ∃ t, o = some (t, m) ∧ s = { t with rip := next } := by
  cases o with
  | none => cases h
  | some p => obtain ⟨t, m'⟩ := p; cases h; exact ⟨rfl, t, rfl, rfl⟩

/-- A retired fall-through instruction continues at the next instruction. -/
theorem exec_rip {i : Silmaril.X86.Ext.Instr} (hf : fallsThrough i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') :
    s'.rip = s.rip + BitVec.ofNat 64 len := by
  cases i
  case unary sz op dst =>
    cases op <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))
  case cxe sz =>
    cases sz <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))
  all_goals first | (cases hf; done) | skip
  all_goals simp only [Silmaril.X86.Ext.exec] at h
  all_goals
    (repeat' (first | (cases h; done) | exact (retire_ok h).1 | (cases h; rfl) | split at h))

/-- A retired instruction that writes no memory leaves the memory unchanged. -/
theorem exec_mem {i : Silmaril.X86.Ext.Instr} (hf : noWrite i = true) {s : State}
    {mem : Memory} {len : Nat} {s' : State} {mem' : Memory}
    (h : Silmaril.X86.Ext.exec i s mem len = .ok s' mem') : mem' = mem := by
  cases i
  case unary sz op dst =>
    cases dst with
    | mem => cases hf
    | reg =>
    cases op <;>
      simp only [Silmaril.X86.Ext.exec] at h <;>
      (repeat' (first | (cases h; done) | (cases h; rfl) | split at h)) <;>
      (obtain ⟨_, ho, _⟩ := (retire_ok h).2; simp_all [writeRM])
  case cxe sz =>
    cases sz <;> simp only [Silmaril.X86.Ext.exec] at h <;>
      (obtain ⟨_, ho, _⟩ := (retire_ok h).2; simp_all)
  case' mov sz dst src => cases dst
  case' movI sz dst imm => cases dst
  case' movI16 dst imm => cases dst
  case' movI8 dst imm => cases dst
  case' store n dst src => cases dst
  case' alu sz op dst src => cases dst
  case' aluI sz op dst imm => cases dst
  case' aluI8 sz op dst imm => cases dst
  case' incdec sz dec dst => cases dst
  case' shift sz op dst count => cases dst
  case' setcc c dst => cases dst
  all_goals first | (cases hf; done) | skip
  all_goals simp only [Silmaril.X86.Ext.exec] at h
  all_goals
    (repeat' (first
      | (cases h; done)
      | (cases h; rfl)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         simp_all [writeRM, writeRM8, aluStep, aluStepR]; done)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         obtain ⟨_, hh⟩ := map_some ho
         injection hh with _ hm; exact hm.symm)
      | (obtain ⟨_, ho, _⟩ := (retire_ok h).2
         simp only [aluStep, aluStepR, readRM, writeRM, Option.map_some] at ho
         (repeat' split at ho) <;> simp_all; done)
      | split at h))

/-- A listed instruction executes as the `Ext` instruction it denotes. -/
theorem execL_toExt {i : LInstr} {e : Silmaril.X86.Ext.Instr} (h : toExt i = some e)
    (s : XState) (mem : Memory) (len : Nat) :
    i.exec s mem len = liftR s.xmm (Silmaril.X86.Ext.exec e s.core mem len) := by
  unfold toExt at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem liftR_ok {x : Silmaril.X86.Lift.Bir.Xmm} {r : Silmaril.X86.Ext.Result} {s : XState}
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
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Lift.Bir.Xmm)
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
      have hm1 : m1 = mem := exec_mem hnw hx
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
          rw [exec_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
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
  unfold runL ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlock_open L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

/-- A lifted listing runs as its Bir block. -/
theorem runL_eq_runB {L : List (LInstr × Nat)} {b : Block} (h : liftBlock L = some b)
    (m : MState) : runL L m = runB b m := by
  simp only [runL, runB, Silmaril.X86.Lift.Bir.liftBlock_sound h]

end Silmaril.Proofs.Machine.X86.BlockCert
