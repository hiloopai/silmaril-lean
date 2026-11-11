module

public import Silmaril.Wasm.SSA.Fragment.Defs

/-! # The fuel interpreter against the big-step semantics

Soundness (`sound`), fuel monotonicity (`succ`, `mono`), completeness
(`complete`, `complete_args`, `complete_seq`) and, from these, determinism. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Fragment

open Silmaril.Wasm.SSA

theorem abrupt_of_ne {α} {o : Out α} (h : ∀ ls a, o = .ok ls a → False) : o.Abrupt := by
  cases o <;> simp_all [Out.Abrupt]

theorem blockExit_of {ty : Option Silmaril.Wasm.IntType} {o o' : Out (Option WVal)}
    (h : evalE.blockExit ty o = some o') : BlockExit ty o o' := by
  unfold evalE.blockExit at h
  split at h
  · split at h
    · cases h
    · cases h; exact .ok (fun hs => by simp_all [Option.isSome_iff_ne_none])
  · split at h
    · cases h
    · cases h; exact .brk0 (fun hs => by simp_all [Option.isSome_iff_ne_none])
  all_goals cases h
  · exact .brk
  · exact .ret
  · exact .trap

theorem loopExit_of {ty : Option Silmaril.Wasm.IntType} {o o' : Out (Option WVal)}
    (h : evalE.loopExit ty o = some o') : LoopExit ty o o' := by
  unfold evalE.loopExit at h
  split at h
  · split at h
    · cases h
    · cases h; exact .ok (fun hs => by simp_all [Option.isSome_iff_ne_none])
  all_goals cases h
  · exact .brk
  · exact .ret
  · exact .trap

/-! ### Soundness, one constructor at a time

Each lemma inverts one step of the interpreter at fuel `n + 1`, given soundness
at fuel `n` for the sub-evaluations it uses. -/

section SoundCases

variable {n : Nat}

private theorem sound_op {ls o args out}
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o)
    (h : evalE (n + 1) ls (.op o args) = some out) : Exec ls (.op o args) out := by
  simp only [evalE] at h
  split at h
  · rename_i ha
    split at h
    · cases h; exact .op (ihA _ _ _ ha) ‹_›
    · cases h; exact .op_trap (ihA _ _ _ ha) ‹_›
    · cases h
  · cases h; exact .op_abrupt (ihA _ _ _ ‹_›) (abrupt_of_ne ‹_›)
  · cases h

private theorem sound_localSet {ls i e out}
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (h : evalE (n + 1) ls (.localSet i e) = some out) : Exec ls (.localSet i e) out := by
  simp only [evalE] at h
  split at h
  · cases h; exact .localSet (ihE _ _ _ ‹_›)
  · cases h
  · exact .localSet_abrupt (ihE _ _ _ h) (abrupt_of_ne fun ls a e => by
      subst e; cases a <;> simp_all)

private theorem sound_localTee {ls i e out}
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (h : evalE (n + 1) ls (.localTee i e) = some out) : Exec ls (.localTee i e) out := by
  simp only [evalE] at h
  split at h
  · cases h; exact .localTee (ihE _ _ _ ‹_›)
  · cases h
  · exact .localTee_abrupt (ihE _ _ _ h) (abrupt_of_ne fun ls a e => by
      subst e; cases a <;> simp_all)

private theorem sound_drop {ls e out}
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (h : evalE (n + 1) ls (.drop e) = some out) : Exec ls (.drop e) out := by
  simp only [evalE] at h
  split at h
  · cases h; exact .drop (ihE _ _ _ ‹_›)
  · exact .drop_abrupt (ihE _ _ _ h) (abrupt_of_ne fun ls a e => by subst e; simp_all)

private theorem sound_block {ls ty body out}
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o)
    (h : evalE (n + 1) ls (.block ty body) = some out) : Exec ls (.block ty body) out := by
  obtain ⟨out', h1, h2⟩ : ∃ out', evalSeq n ls none body = some out' ∧
      evalE.blockExit ty out' = some out := by
    simpa only [evalE, Option.bind_eq_some_iff] using h
  exact .block (ihS _ _ _ _ h1) (blockExit_of h2)

private theorem sound_loop {ls ty body out}
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o)
    (h : evalE (n + 1) ls (.loop ty body) = some out) : Exec ls (.loop ty body) out := by
  simp only [evalE] at h
  split at h
  · exact .loop_back (ihS _ _ _ _ ‹_›) (ihE _ _ _ h)
  · exact .loop (ihS _ _ _ _ ‹_›) (loopExit_of h)
  · cases h

private theorem sound_if {ls ty c t el out}
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o)
    (h : evalE (n + 1) ls (.if_ ty c t el) = some out) : Exec ls (.if_ ty c t el) out := by
  simp only [evalE] at h
  split at h
  · rename_i hc
    split at h
    · rename_i b hb
      obtain ⟨out', h1, h2⟩ := Option.bind_eq_some_iff.mp h
      exact .if_ (ihE _ _ _ hc) hb (ihS _ _ _ _ h1) (blockExit_of h2)
    · cases h
  · cases h
  · exact .if_abrupt (ihE _ _ _ h) (abrupt_of_ne fun ls a e => by
      subst e; cases a <;> simp_all)

private theorem sound_br {ls l args out}
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o)
    (h : evalE (n + 1) ls (.br l args) = some out) : Exec ls (.br l args) out := by
  simp only [evalE] at h
  split at h
  · cases h; exact .br (ihA _ _ _ ‹_›)
  · cases h; exact .br_abrupt (ihA _ _ _ ‹_›) (abrupt_of_ne ‹_›)
  · cases h

private theorem sound_brIf {ls l args out}
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o)
    (h : evalE (n + 1) ls (.brIf l args) = some out) : Exec ls (.brIf l args) out := by
  simp only [evalE] at h
  split at h
  · rename_i ha
    split at h
    · rename_i c hc
      obtain ⟨b, hb, hout⟩ := Option.map_eq_some_iff.mp h
      exact hout ▸ .brIf (ihA _ _ _ ha) hc hb
    · cases h
  · cases h; exact .brIf_abrupt (ihA _ _ _ ‹_›) (abrupt_of_ne ‹_›)
  · cases h

private theorem sound_return {ls args out}
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o)
    (h : evalE (n + 1) ls (.return_ args) = some out) : Exec ls (.return_ args) out := by
  simp only [evalE] at h
  split at h
  · cases h; exact .return_ (ihA _ _ _ ‹_›)
  · cases h; exact .return_abrupt (ihA _ _ _ ‹_›) (abrupt_of_ne ‹_›)
  · cases h

private theorem sound_exec_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o) :
    ∀ ls e o, evalE (n + 1) ls e = some o → Exec ls e o := by
  intro ls e o h
  cases e with
  | op o args => exact sound_op ihA h
  | localGet i =>
    obtain ⟨v, hv, hout⟩ := Option.map_eq_some_iff.mp (by simpa only [evalE] using h)
    exact hout ▸ .localGet hv
  | localSet i e => exact sound_localSet ihE h
  | localTee i e => exact sound_localTee ihE h
  | drop e => exact sound_drop ihE h
  | nop => exact (Option.some.inj h) ▸ .nop
  | unreachable => exact (Option.some.inj h) ▸ .unreachable
  | block ty body => exact sound_block ihS h
  | loop ty body => exact sound_loop ihE ihS h
  | if_ ty c t el => exact sound_if ihE ihS h
  | br l args => exact sound_br ihA h
  | brIf l args => exact sound_brIf ihA h
  | return_ args => exact sound_return ihA h

private theorem sound_args_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (ihA : ∀ ls es o, evalArgs n ls es = some o → Args ls es o) :
    ∀ ls es o, evalArgs (n + 1) ls es = some o → Args ls es o := by
  intro ls es o h
  cases es with
  | nil => exact (Option.some.inj h) ▸ .nil
  | cons e es =>
    simp only [evalArgs] at h
    split at h
    · rename_i he
      split at h
      · cases h; exact .cons (ihE _ _ _ he) (ihA _ _ _ ‹_›)
      · exact .tail_abrupt (ihE _ _ _ he) (ihA _ _ _ h)
          (abrupt_of_ne fun ls a e => by subst e; simp_all)
    · cases h
    · cases h; exact .head_abrupt (ihE _ _ _ ‹_›) (abrupt_of_ne fun ls a e => by
        subst e; cases a <;> simp_all)
    · cases h

private theorem sound_seq_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → Exec ls e o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o) :
    ∀ ls r es o, evalSeq (n + 1) ls r es = some o → Seq ls r es o := by
  intro ls r es o h
  cases es with
  | nil => exact (Option.some.inj h) ▸ .nil
  | cons e es =>
    simp only [evalSeq] at h
    split at h
    · exact .cons (ihE _ _ _ ‹_›) (ihS _ _ _ _ h)
    · exact .abrupt (ihE _ _ _ h) (abrupt_of_ne fun ls a e => by subst e; simp_all)

end SoundCases

theorem sound : ∀ n,
    (∀ ls e o, evalE n ls e = some o → Exec ls e o) ∧
    (∀ ls es o, evalArgs n ls es = some o → Args ls es o) ∧
    (∀ ls r es o, evalSeq n ls r es = some o → Seq ls r es o) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [evalE], by simp [evalArgs], by simp [evalSeq]⟩
  | succ n ih =>
    obtain ⟨ihE, ihA, ihS⟩ := ih
    exact ⟨sound_exec_succ ihE ihA ihS, sound_args_succ ihE ihA, sound_seq_succ ihE ihS⟩

end Silmaril.Proofs.Wasm.SSA.Fragment

namespace Silmaril.Proofs.Wasm.SSA.Fragment
open Silmaril.Wasm.SSA

/-! ### Fuel monotonicity, one constructor at a time

At fuel `n + 1` each interpreter step scrutinises sub-evaluations at fuel `n`.
`opt_step` says a sub-evaluation either got stuck, or gives the same answer with
one more unit of fuel; in the first case the whole step was stuck. -/

private theorem opt_step {α} {x y : Option α} (hxy : ∀ r, x = some r → y = some r) :
    x = none ∨ y = x := by
  cases hx : x with
  | none => exact .inl rfl
  | some r => exact .inr (hxy r hx)

section SuccCases

variable {n : Nat}

private theorem succ_if {ls ty c t el o}
    (ihE : ∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → evalSeq (n + 1) ls r es = some o)
    (h : evalE (n + 1) ls (.if_ ty c t el) = some o) :
    evalE (n + 1 + 1) ls (.if_ ty c t el) = some o := by
  rcases opt_step (ihE ls c) with hc | hc
  · exact absurd h (by simp [evalE, hc])
  rw [evalE, hc]
  simp only [evalE] at h
  generalize evalE n ls c = r at h ⊢
  split at h
  · split at h
    · obtain ⟨out, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      exact Option.bind_eq_some_iff.mpr ⟨out, ihS _ _ _ _ h1, h2⟩
    · cases h
  · cases h
  · exact h

private theorem succ_loop {ls ty body o}
    (ihE : ∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → evalSeq (n + 1) ls r es = some o)
    (h : evalE (n + 1) ls (.loop ty body) = some o) :
    evalE (n + 1 + 1) ls (.loop ty body) = some o := by
  rcases opt_step (ihS ls none body) with hb | hb
  · exact absurd h (by simp [evalE, hb])
  rw [evalE, hb]
  simp only [evalE] at h
  generalize evalSeq n ls none body = r at h ⊢
  split at h
  · exact ihE _ _ _ h
  · exact h
  · cases h

private theorem succ_exec_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o)
    (ihA : ∀ ls es o, evalArgs n ls es = some o → evalArgs (n + 1) ls es = some o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → evalSeq (n + 1) ls r es = some o) :
    ∀ ls e o, evalE (n + 1) ls e = some o → evalE (n + 1 + 1) ls e = some o := by
  intro ls e o h
  cases e with
  | localGet i | nop | unreachable => simpa only [evalE] using h
  | op o args | br l args | brIf l args | return_ args =>
    rcases opt_step (ihA ls args) with ha | ha
    · exact absurd h (by simp [evalE, ha])
    · rw [evalE, ha]
      simpa only [evalE] using h
  | localSet i e | localTee i e | drop e =>
    rcases opt_step (ihE ls e) with he | he
    · exact absurd h (by simp [evalE, he])
    · rw [evalE, he]
      simpa only [evalE] using h
  | block ty body =>
    rcases opt_step (ihS ls none body) with hb | hb
    · exact absurd h (by simp [evalE, hb])
    · rw [evalE, hb]
      simpa only [evalE] using h
  | if_ ty c t el => exact succ_if ihE ihS h
  | loop ty body => exact succ_loop ihE ihS h

private theorem succ_args_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o)
    (ihA : ∀ ls es o, evalArgs n ls es = some o → evalArgs (n + 1) ls es = some o) :
    ∀ ls es o, evalArgs (n + 1) ls es = some o → evalArgs (n + 1 + 1) ls es = some o := by
  intro ls es o h
  cases es with
  | nil => simpa only [evalArgs] using h
  | cons e es =>
    rcases opt_step (ihE ls e) with he | he
    · exact absurd h (by simp [evalArgs, he])
    rw [evalArgs, he]
    simp only [evalArgs] at h
    generalize evalE n ls e = r at h ⊢
    split at h
    · rename_i _ ls₁ _
      rcases opt_step (ihA ls₁ es) with ha | ha
      · exact absurd h (by simp [ha])
      · rw [ha]
        exact h
    all_goals exact h

private theorem succ_seq_succ
    (ihE : ∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o)
    (ihS : ∀ ls r es o, evalSeq n ls r es = some o → evalSeq (n + 1) ls r es = some o) :
    ∀ ls r es o, evalSeq (n + 1) ls r es = some o → evalSeq (n + 1 + 1) ls r es = some o := by
  intro ls r es o h
  cases es with
  | nil => simpa only [evalSeq] using h
  | cons e es =>
    rcases opt_step (ihE ls e) with he | he
    · exact absurd h (by simp [evalSeq, he])
    rw [evalSeq, he]
    simp only [evalSeq] at h
    generalize evalE n ls e = r at h ⊢
    split at h
    · exact ihS _ _ _ _ h
    · exact h

end SuccCases

theorem succ : ∀ n,
    (∀ ls e o, evalE n ls e = some o → evalE (n + 1) ls e = some o) ∧
    (∀ ls es o, evalArgs n ls es = some o → evalArgs (n + 1) ls es = some o) ∧
    (∀ ls r es o, evalSeq n ls r es = some o → evalSeq (n + 1) ls r es = some o) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [evalE], by simp [evalArgs], by simp [evalSeq]⟩
  | succ n ih =>
    obtain ⟨ihE, ihA, ihS⟩ := ih
    exact ⟨succ_exec_succ ihE ihA ihS, succ_args_succ ihE ihA, succ_seq_succ ihE ihS⟩

theorem mono {n m : Nat} (hle : n ≤ m) :
    (∀ {ls e o}, evalE n ls e = some o → evalE m ls e = some o) ∧
    (∀ {ls es o}, evalArgs n ls es = some o → evalArgs m ls es = some o) ∧
    (∀ {ls r es o}, evalSeq n ls r es = some o → evalSeq m ls r es = some o) := by
  induction hle with
  | refl => exact ⟨id, id, id⟩
  | step _ ih =>
    exact ⟨fun h => (succ _).1 _ _ _ (ih.1 h), fun h => (succ _).2.1 _ _ _ (ih.2.1 h),
      fun h => (succ _).2.2 _ _ _ _ (ih.2.2 h)⟩

end Silmaril.Proofs.Wasm.SSA.Fragment

namespace Silmaril.Proofs.Wasm.SSA.Fragment
open Silmaril.Wasm.SSA

theorem blockExit_complete {ty : Option Silmaril.Wasm.IntType} {o o' : Out (Option WVal)}
    (h : BlockExit ty o o') : evalE.blockExit ty o = some o' := by
  cases h with
  | ok h | brk0 h =>
    simp only [evalE.blockExit]
    split
    · rename_i h'; simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h'
      simp_all [BlockOk]
    · rfl
  | brk | ret | trap => rfl

theorem loopExit_complete {ty : Option Silmaril.Wasm.IntType} {o o' : Out (Option WVal)}
    (h : LoopExit ty o o') : evalE.loopExit ty o = some o' := by
  cases h with
  | ok h =>
    simp only [evalE.loopExit]
    split
    · rename_i h'; simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h'
      simp_all [BlockOk]
    · rfl
  | brk | ret | trap => rfl

theorem liftE {n m ls e o} (h : evalE n ls e = some o) (hle : n ≤ m) : evalE m ls e = some o :=
  (mono hle).1 h
theorem liftA {n m ls es o} (h : evalArgs n ls es = some o) (hle : n ≤ m) :
    evalArgs m ls es = some o := (mono hle).2.1 h
theorem liftS {n m ls r es o} (h : evalSeq n ls r es = some o) (hle : n ≤ m) :
    evalSeq m ls r es = some o := (mono hle).2.2 h

theorem complete {ls e o} (h : Exec ls e o) : ∃ n, evalE n ls e = some o := by
  induction h using Exec.rec
    (motive_2 := fun ls es o _ => ∃ n, evalArgs n ls es = some o)
    (motive_3 := fun ls r es o _ => ∃ n, evalSeq n ls r es = some o)
  case op _ hv ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE]; simp [h, hv]⟩
  case op_trap _ hv ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE]; simp [h, hv]⟩
  case op_abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalE, h]
    cases out <;> simp_all [Out.Abrupt]
  case localGet hv => exact ⟨1, by simp [evalE, hv]⟩
  case localSet _ ih | localTee _ ih | drop _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE, h]⟩
  case localSet_abrupt out _ hab ih | localTee_abrupt out _ hab ih | if_abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalE, h]
    cases out with
    | ok => exact (hab : False).elim
    | _ => rfl
  case drop_abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalE, h]
    cases out with
    | ok => exact (hab : False).elim
    | _ => rfl
  case nop => exact ⟨1, rfl⟩
  case unreachable => exact ⟨1, rfl⟩
  case block _ hx ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE]; simp [h, blockExit_complete hx]⟩
  case loop _ hx ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalE, h]
    cases hx <;> simp [evalE.loopExit]
    simp_all [BlockOk, Option.isSome_iff_ne_none]
  case loop_back _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by rw [evalE, liftS (m := n₁ + n₂) h₁ (by omega)]; exact liftE (m := n₁ + n₂) h₂ (by omega)⟩
  case if_ _ hb _ hx ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by
      rw [evalE, liftE (m := n₁ + n₂) h₁ (by omega)]; simp [hb, liftS (m := n₁ + n₂) h₂ (by omega), blockExit_complete hx]⟩
  case br _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE, h]⟩
  case br_abrupt out _ hab ih | brIf_abrupt out _ hab ih | return_abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalE, h]
    cases out <;> simp_all [Out.Abrupt]
  case brIf _ hc hb ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE, h]; simp [hc, hb]⟩
  case return_ _ ih => obtain ⟨n, h⟩ := ih; exact ⟨n + 1, by rw [evalE, h]⟩
  case nil => exact ⟨1, rfl⟩
  case cons _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by rw [evalArgs, liftE (m := n₁ + n₂) h₁ (by omega)]; simp [liftA (m := n₁ + n₂) h₂ (by omega)]⟩
  case head_abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalArgs, h]
    cases out <;> simp_all [Out.Abrupt]
  case tail_abrupt out _ _ hab ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    refine ⟨n₁ + n₂ + 1, ?_⟩
    rw [evalArgs, liftE (m := n₁ + n₂) h₁ (by omega)]; simp only [liftA (m := n₁ + n₂) h₂ (by omega)]
    cases out <;> simp_all [Out.Abrupt]
  case nil => exact ⟨1, rfl⟩
  case cons _ _ ih1 ih2 =>
    obtain ⟨n₁, h₁⟩ := ih1; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by rw [evalSeq, liftE (m := n₁ + n₂) h₁ (by omega)]; exact liftS (m := n₁ + n₂) h₂ (by omega)⟩
  case abrupt out _ hab ih =>
    obtain ⟨n, h⟩ := ih; refine ⟨n + 1, ?_⟩; rw [evalSeq, h]
    cases out with
    | ok => exact (hab : False).elim
    | _ => rfl

end Silmaril.Proofs.Wasm.SSA.Fragment

namespace Silmaril.Proofs.Wasm.SSA.Fragment
open Silmaril.Wasm.SSA

theorem complete_args {ls es o} (h : Args ls es o) : ∃ n, evalArgs n ls es = some o := by
  induction h using Args.rec (motive_1 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  all_goals try (intros; trivial)
  case nil => exact ⟨1, rfl⟩
  case cons he _ _ ih2 =>
    obtain ⟨n₁, h₁⟩ := complete he; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by
      rw [evalArgs, liftE (m := n₁ + n₂) h₁ (by omega)]; simp [liftA (m := n₁ + n₂) h₂ (by omega)]⟩
  case head_abrupt he hab _ =>
    obtain ⟨n, h⟩ := complete he; refine ⟨n + 1, ?_⟩; rw [evalArgs, h]
    rename_i out _; cases out <;> simp_all [Out.Abrupt]
  case tail_abrupt he _ hab _ ih2 =>
    obtain ⟨n₁, h₁⟩ := complete he; obtain ⟨n₂, h₂⟩ := ih2
    refine ⟨n₁ + n₂ + 1, ?_⟩
    rw [evalArgs, liftE (m := n₁ + n₂) h₁ (by omega)]
    simp only [liftA (m := n₁ + n₂) h₂ (by omega)]
    rename_i out _ _; cases out <;> simp_all [Out.Abrupt]

theorem complete_seq {ls r es o} (h : Seq ls r es o) : ∃ n, evalSeq n ls r es = some o := by
  induction h using Silmaril.Wasm.SSA.Seq.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
  all_goals try (intros; trivial)
  case nil => exact ⟨1, rfl⟩
  case cons he _ _ ih2 =>
    obtain ⟨n₁, h₁⟩ := complete he; obtain ⟨n₂, h₂⟩ := ih2
    exact ⟨n₁ + n₂ + 1, by
      rw [evalSeq, liftE (m := n₁ + n₂) h₁ (by omega)]; exact liftS (m := n₁ + n₂) h₂ (by omega)⟩
  case abrupt he hab _ =>
    obtain ⟨n, h⟩ := complete he; refine ⟨n + 1, ?_⟩; rw [evalSeq, h]
    rename_i out _; cases out with
    | ok _ a => simp [Out.Abrupt] at hab
    | _ => rfl

theorem exec_det {ls e o₁ o₂} (h₁ : Exec ls e o₁) (h₂ : Exec ls e o₂) : o₁ = o₂ := by
  obtain ⟨n₁, e₁⟩ := complete h₁; obtain ⟨n₂, e₂⟩ := complete h₂
  have := (liftE (m := n₁ + n₂) e₁ (by omega)).symm.trans (liftE e₂ (by omega))
  exact Option.some.inj this

theorem args_det {ls es o₁ o₂} (h₁ : Args ls es o₁) (h₂ : Args ls es o₂) : o₁ = o₂ := by
  obtain ⟨n₁, e₁⟩ := complete_args h₁; obtain ⟨n₂, e₂⟩ := complete_args h₂
  have := (liftA (m := n₁ + n₂) e₁ (by omega)).symm.trans (liftA e₂ (by omega))
  exact Option.some.inj this

theorem seq_det {ls r es o₁ o₂} (h₁ : Seq ls r es o₁) (h₂ : Seq ls r es o₂) : o₁ = o₂ := by
  obtain ⟨n₁, e₁⟩ := complete_seq h₁; obtain ⟨n₂, e₂⟩ := complete_seq h₂
  have := (liftS (m := n₁ + n₂) e₁ (by omega)).symm.trans (liftS e₂ (by omega))
  exact Option.some.inj this

theorem run_det {f : FragFunc} {args o₁ o₂} (h₁ : f.Run args o₁) (h₂ : f.Run args o₂) :
    o₁ = o₂ := by
  obtain ⟨_, out₁, hs₁, he₁⟩ := h₁
  obtain ⟨_, out₂, hs₂, he₂⟩ := h₂
  cases seq_det hs₁ hs₂
  exact Option.some.inj (he₁.symm.trans he₂)

theorem eval_sound {fuel} {f : FragFunc} {args o} (h : f.eval fuel args = some o) :
    f.Run args o := by
  unfold FragFunc.eval at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨out, h1, h2⟩ := h
    exact ⟨‹_›, out, (sound fuel).2.2 _ _ _ _ h1, h2⟩
  · cases h

theorem eval_complete {f : FragFunc} {args o} (h : f.Run args o) :
    ∃ fuel, f.eval fuel args = some o := by
  obtain ⟨hl, out, hs, he⟩ := h
  obtain ⟨n, hn⟩ := complete_seq hs
  exact ⟨n, by simp [FragFunc.eval, hl, hn, he]⟩

end Silmaril.Proofs.Wasm.SSA.Fragment
