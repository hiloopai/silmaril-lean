module

public import Silmaril.Machine.Abi.OpenMachine.Defs
public import Silmaril.X86.BlockCert.Thms
/-!
# Runs inside the code, and first returns

* `runsIn_mono`, `runsIn_trans`, `runsIn_reaches`: basic facts;
* `firstReturn_unique`: the open machine is a function, so a run has at most one first
  return;
* `firstReturn_of_runsIn`: a run inside the code that ends returned is the first return,
  when the return address lies outside the code;
* `execBlock_within`, `runL_within`: A's bridge `BlockCert.execBlock_open`, strengthened to
  say that every step of a checked listing is taken inside the code (the proof follows A's,
  `Silmaril.Proofs.X86.BlockCert.execBlock_open`, using only exported lemmas);
* `from_block_within`, `totalIn_of_funCert`: A's `FunCert.from_block`/`FunCert.total` with
  runs inside the code.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.OpenMachine

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (LInstr XState execBlock liftR)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches run)
open Silmaril.X86
open Silmaril.X86.BlockCert
open Silmaril.Machine.Abi.OpenMachine

/-! ## `RunsIn` -/

theorem runsIn_mono {P Q : MState → Prop} (h : ∀ m, P m → Q m) {s t : MState}
    (r : RunsIn P s t) : RunsIn Q s t := by
  induction r with
  | refl m => exact .refl m
  | step hp hs _ ih => exact .step (h _ hp) hs ih

theorem runsIn_trans {P : MState → Prop} {s t u : MState} (r₁ : RunsIn P s t)
    (r₂ : RunsIn P t u) : RunsIn P s u := by
  induction r₁ with
  | refl _ => exact r₂
  | step hp hs _ ih => exact .step hp hs (ih r₂)

theorem runsIn_reaches {P : MState → Prop} {s t : MState} (r : RunsIn P s t) :
    Reaches Open.step s t := by
  induction r with
  | refl m => exact Reaches.refl _ m
  | step _ hs _ ih => exact (Silmaril.X86.SegVC.reaches_head (I := Open.isa) hs).trans ih

/-- On a deterministic machine, two runs that stop at the first state outside `P` agree. -/
theorem runsIn_unique {P : MState → Prop} {s t t' : MState} (r : RunsIn P s t) (ht : ¬ P t)
    (r' : RunsIn P s t') (ht' : ¬ P t') : t = t' := by
  induction r generalizing t' with
  | refl m =>
    cases r' with
    | refl => rfl
    | step hp _ _ => exact absurd hp ht
  | step hp hs _ ih =>
    cases r' with
    | refl => exact absurd hp ht'
    | step _ hs' r'' =>
      rw [hs] at hs'
      cases hs'
      exact ih ht r'' ht'

theorem firstReturn_unique {s t t' : MState} (h : FirstReturn s t) (h' : FirstReturn s t') :
    t = t' :=
  runsIn_unique h.1 (not_not_intro h.2) h'.1 (not_not_intro h'.2)

/-- A run inside the code that ends returned is the first return, when the return address
is outside the code. -/
theorem firstReturn_of_runsIn {base : Word} {len : Nat} {s t : MState}
    (r : RunsIn (InCode base len) s t) (ret : Returned s t) (outside : RetOutside base len s) :
    FirstReturn s t := by
  refine ⟨runsIn_mono (r := r) fun m ⟨o, ho, hrip⟩ hret => outside o ho ?_, ret⟩
  rw [← hrip]
  exact hret.1.symm

/-! ## The block bridge, inside the code -/

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

theorem decode_nil : Silmaril.X86.Ext.decode [] = none := by decide

/-- A decoded instruction has positive length. -/
theorem decode_len_pos {code : List Byte} {o l : Nat} {e : Silmaril.X86.Ext.Instr}
    (h : Silmaril.X86.Ext.decode ((code.drop o).take l) = some (e, l)) : 0 < l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp [decode_nil] at h
  · exact hl

/-- **A's bridge, inside the code**: a listing checked at the program counter of a loaded
image that executes is a run of the open machine whose every step starts inside the code. -/
theorem execBlock_within {code : List Byte} {base : Word} :
    ∀ (L : List (LInstr × Nat)) (o : Nat) (c : State) (x : Silmaril.X86.Bir9.Xmm)
      (mem : Memory) (s' : XState) (mem' : Memory),
      listingAt code o L = true → Loaded mem base code → c.rip = base + BitVec.ofNat 64 o →
      execBlock L ⟨c, x⟩ mem = .ok s' mem' →
      RunsIn (InCode base code.length) ⟨c, mem⟩ ⟨s'.core, mem'⟩ ∧ mem' = mem
  | [], _, c, x, mem, s', mem', _, _, _, h => by
    simp only [execBlock] at h
    cases h
    exact ⟨.refl _, rfl⟩
  | (i, l) :: rest, o, c, x, mem, s', mem', hok, hl, hrip, h => by
    simp only [listingAt] at hok
    split at hok
    · cases hok
    rename_i e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hdec, hfit⟩, hnw⟩, hft⟩, hrest⟩ := hok
    have hin : InCode base code.length ⟨c, mem⟩ :=
      ⟨o, by have := decode_len_pos hdec; omega, hrip⟩
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
        exact ⟨.step hin hs (.refl _), rfl⟩
      | cons nx rest' =>
        simp only [List.isEmpty_cons, Bool.false_or] at hft
        have hrip1 : c1.rip = base + BitVec.ofNat 64 (o + l) := by
          rw [exec_rip hft hx, hrip, BitVec.ofNat_add, BitVec.add_assoc]
        obtain ⟨hr, hm⟩ := execBlock_within (nx :: rest') (o + l) c1 x m1 s' mem' hrest hl hrip1 h
        exact ⟨.step hin hs hr, hm⟩
    | dataFault => rw [hx] at h; cases h
    | divideError => rw [hx] at h; cases h
    | undefinedCondition _ => rw [hx] at h; cases h
    | trap => rw [hx] at h; cases h

/-- The bridge on machine states, inside the code. -/
theorem runL_within {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : runL L m = some m') :
    RunsIn (InCode base code.length) m m' ∧ m'.memory = m.memory := by
  unfold runL ofX at h
  split at h
  · rename_i s mem' hx
    cases h
    exact execBlock_within L o m.core _ m.memory s mem' hok hl hrip hx
  · cases h

/-! ## Function certificates, inside the code -/

theorem checked_mem {F : FunCert} (hc : F.checked = true) {b : Blk} (hb : b ∈ F.blocks) :
    listingAt F.code b.off b.instrs = true :=
  List.all_eq_true.mp hc b hb

theorem from_block_within {F : FunCert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) (m0 : MState) :
    ∀ (w : Nat) (b : Blk) (m : MState), F.measure b.off m0 m = w → b ∈ F.blocks →
      F.ann b.off m0 m → m.core.rip = F.base + BitVec.ofNat 64 b.off →
      Loaded m.memory F.base F.code →
        ∃ t, RunsIn (InCode F.base F.code.length) m t ∧ Q m0 t := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro b m hw hb ha hrip hl
    obtain ⟨m', hrun, hnext⟩ := hvc b hb m0 m ha hrip hl
    obtain ⟨hr, hmem⟩ := runL_within (checked_mem hc hb) hl hrip hrun
    rcases hnext with hq | ⟨b', hb', hrip', ha', hlt⟩
    · exact ⟨m', hr, hq⟩
    · have hl' : Loaded m'.memory F.base F.code := by rw [hmem]; exact hl
      obtain ⟨t, hr', hq⟩ := ih _ (hw ▸ hlt) b' m' rfl hb' ha' hrip' hl'
      exact ⟨t, runsIn_trans hr hr', hq⟩

/-- **A function certificate gives runs inside the code** (A's `FunCert.total`, same
hypotheses). -/
theorem totalIn_of_funCert {F : FunCert} (S : FnContract.Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, FnContract.AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    TotalIn S fun _ => InCode F.base F.code.length := by
  intro m hab he
  obtain ⟨hl, hrip, ha⟩ := hpre m hab he
  exact from_block_within hc hvc m _ entry m rfl hentry ha hrip hl

end Silmaril.Proofs.Machine.Abi.OpenMachine
