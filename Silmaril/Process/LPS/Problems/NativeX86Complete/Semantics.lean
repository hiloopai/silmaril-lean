module

public import Silmaril.Process.LPS.NativeX86Refusal
public import Silmaril.Process.LPS.NativeX86AllLattice
public import Silmaril.Process.LPS.X86GapSweep
public import Silmaril.Process.LPS.Lattice
public import Silmaril.Process.LPS.Problems.NativeX86

/-!
# Semantics for the x86-64 statements, and transfer along a restriction

A `Semantics` is a syscall table and a refusal reading per reading. `complete` is the hub
`NativeX86.All.system`; `exact` and `gap` are its exact and gap-sweep variants, and
`reviewedDefault` is the former reviewed-default table of `Problems.NativeX86`.
`Semantics.Below S T` (S restricts T, with refusal readings that agree where the tables do)
transfers budget refusal and must-exit (`mustExitInAt_of_restricts`) from `S` to `T`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86Complete

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

/-! ## Semantics: a syscall table and a refusal reading per reading -/

structure Semantics where
  spec : Reading → Sys SyscallEffect
  refused : Reading → RefusalFilter

/-- The complete native system `NativeX86.All.system` (the hub): the default. -/
def complete : Semantics where
  spec r := (NativeX86.All.system r).spec
  refused r := (NativeX86.All.system r).refused

/-- The refusal reading over another native table, with the extensions' families. -/
def refusalsOver (t : List SpecArm) : Reading → RefusalFilter
  | none => noFilter
  | some cfg => NativeX86.All.spuriousRefusalCfgX86Ext (dispatch t) cfg

/-- The families' x86-64 arms without chaos (`NativeX86.All.exactTable`). -/
def exact : Semantics where
  spec _ := dispatch NativeX86.All.exactTable
  refused := refusalsOver NativeX86.All.exactTable

/-- The gap-sweep variant (`NativeX86.GapSweep.gapTable`): five more-defined arms. -/
def gap : Semantics where
  spec _ := dispatch NativeX86.GapSweep.gapTable
  refused := refusalsOver NativeX86.GapSweep.gapTable

/-- The reviewed-default table and filter of `Problems.NativeX86` (the legacy point). -/
def reviewedDefault : Semantics where
  spec _ := NativeX86.extendedSyscallSpec
  refused := Problems.NativeX86.readingFilter

theorem complete_spec (r : Reading) : complete.spec r = dispatch NativeX86.All.nativeTable := rfl

theorem complete_refused (r : Reading) :
    complete.refused r = refusalsOver NativeX86.All.nativeTable r := by
  cases r <;> rfl

/-- `S` restricts `T` at every reading, with refusal readings that agree where the tables do:
statements over `S` imply statements over `T`. -/
def Semantics.Below (S T : Semantics) : Prop :=
  ∀ r, _root_.Silmaril.Process.LPS.Restricts (S.spec r) (T.spec r) ∧
    FiltersAgree (S.spec r) (T.spec r) (S.refused r) (T.refused r)

theorem Semantics.Below.refl (S : Semantics) : S.Below S :=
  fun _ => ⟨fun _ _ => .inl fun _ => Iff.rfl, fun _ _ _ _ _ _ _ => Iff.rfl⟩

theorem filtersAgree_ext (p f : Sys SyscallEffect) (cfg : SpuriousCfg) :
    FiltersAgree p f (NativeX86.All.spuriousRefusalCfgX86Ext p cfg)
      (NativeX86.All.spuriousRefusalCfgX86Ext f cfg) := by
  intro i m same e _ _ _
  simp only [NativeX86.All.spuriousRefusalCfgX86Ext, same]

theorem filtersAgree_refusalsOver (t u : List SpecArm) (r : Reading) :
    FiltersAgree (dispatch t) (dispatch u) (refusalsOver t r) (refusalsOver u r) := by
  cases r with
  | none => exact filtersAgree_noFilter _ _
  | some cfg => exact filtersAgree_ext _ _ cfg

theorem below_of_restricts {t u : List SpecArm} (R : Restricts (dispatch t) (dispatch u)) :
    Semantics.Below ⟨fun _ => dispatch t, refusalsOver t⟩ ⟨fun _ => dispatch u, refusalsOver u⟩ :=
  fun r => ⟨R, filtersAgree_refusalsOver t u r⟩

/-- The complete system (with chaos) is below the families' exact arms. -/
theorem complete_below_exact : complete.Below exact := by
  intro r
  rw [complete_spec, complete_refused]
  exact below_of_restricts NativeX86.All.nativeTable_restricts_exact r

/-- The complete system is below the gap-sweep variant. -/
theorem complete_below_gap : complete.Below gap := by
  intro r
  rw [complete_spec, complete_refused]
  exact below_of_restricts NativeX86.GapSweep.gapTable_restricts r

/-! ## The meet of two semantics

`Semantics.meet S T` declines (`unmodeled`) wherever `S` and `T` disagree, at a call or at the
refusal of an effect they answer with, and is `S` (equally `T`) elsewhere. It is below both
(`meet_below_left`, `meet_below_right`) and above every semantics below both (`below_meet`), so it
is the greatest lower bound for `Semantics.Below`. `meetDefault` is the meet of the complete
system and the reviewed-default table: it declines the calls the reviewed default leaves pending
(`open`, `lseek`, `readv`, `writev`, `unlink`, ...), the `TASK_SIZE_MAX` band the complete system
declines, and every other point where the two differ. -/

/-- `p` and `f` agree at `(i, m)`: the same outcomes, and the same refusals of the effects they
answer with. -/
def AgreeAt (p f : Sys SyscallEffect) (rp rf : RefusalFilter) (i : SyscallInput) (m : Model) :
    Prop :=
  (∀ o, p i m o ↔ f i m o) ∧ ∀ e m' evs, p i m (.ok e m' evs) → (rp i m e ↔ rf i m e)

/-- The table that is `p` where `p` and `f` agree, and declines elsewhere. -/
def meetSys (p f : Sys SyscallEffect) (rp rf : RefusalFilter) : Sys SyscallEffect := fun i m o =>
  (AgreeAt p f rp rf i m ∧ p i m o) ∨ (¬ AgreeAt p f rp rf i m ∧ o = .unmodeled)

theorem meetSys_of_agree {p f : Sys SyscallEffect} {rp rf : RefusalFilter} {i : SyscallInput}
    {m : Model} (h : AgreeAt p f rp rf i m) (o : Outcome SyscallEffect) :
    meetSys p f rp rf i m o ↔ p i m o := by
  simp [meetSys, h]

theorem meetSys_of_not_agree {p f : Sys SyscallEffect} {rp rf : RefusalFilter} {i : SyscallInput}
    {m : Model} (h : ¬ AgreeAt p f rp rf i m) (o : Outcome SyscallEffect) :
    meetSys p f rp rf i m o ↔ o = .unmodeled := by
  simp [meetSys, h]

/-- The meet of two semantics, with the first one's refusal reading. -/
def Semantics.meet (S T : Semantics) : Semantics where
  spec r := meetSys (S.spec r) (T.spec r) (S.refused r) (T.refused r)
  refused := S.refused

theorem meet_below_left (S T : Semantics) : (S.meet T).Below S := by
  intro r
  refine ⟨fun i m => ?_, fun _ _ _ _ _ _ _ => Iff.rfl⟩
  by_cases h : AgreeAt (S.spec r) (T.spec r) (S.refused r) (T.refused r) i m
  · exact .inl (meetSys_of_agree h)
  · exact .inr (meetSys_of_not_agree h)

theorem meet_below_right (S T : Semantics) : (S.meet T).Below T := by
  intro r
  refine ⟨fun i m => ?_, fun i m _ e m' evs ok => ?_⟩
  · by_cases h : AgreeAt (S.spec r) (T.spec r) (S.refused r) (T.refused r) i m
    · exact .inl fun o => (meetSys_of_agree h o).trans (h.1 o)
    · exact .inr (meetSys_of_not_agree h)
  · by_cases h : AgreeAt (S.spec r) (T.spec r) (S.refused r) (T.refused r) i m
    · exact h.2 e m' evs ((meetSys_of_agree h _).1 ok)
    · cases (meetSys_of_not_agree h _).1 ok

/-- A semantics below both is below their meet. -/
theorem below_meet {Q S T : Semantics} (hS : Q.Below S) (hT : Q.Below T) : Q.Below (S.meet T) := by
  intro r
  have key : ∀ i m, (∀ o, Q.spec r i m o ↔ o = .unmodeled) ∨
      ((∀ o, Q.spec r i m o ↔ S.spec r i m o) ∧ (∀ o, Q.spec r i m o ↔ T.spec r i m o)) := by
    intro i m
    by_cases dec : ∀ o, Q.spec r i m o ↔ o = .unmodeled
    · exact .inl dec
    · refine .inr ⟨?_, ?_⟩
      · rcases (hS r).1 i m with h | h
        · exact h
        · exact absurd h dec
      · rcases (hT r).1 i m with h | h
        · exact h
        · exact absurd h dec
  have agree : ∀ i m, (∀ o, Q.spec r i m o ↔ S.spec r i m o) →
      (∀ o, Q.spec r i m o ↔ T.spec r i m o) →
      AgreeAt (S.spec r) (T.spec r) (S.refused r) (T.refused r) i m := by
    intro i m qs qt
    refine ⟨fun o => (qs o).symm.trans (qt o), fun e m' evs ok => ?_⟩
    have okQ := (qs _).2 ok
    exact ((hS r).2 i m qs e m' evs okQ).symm.trans ((hT r).2 i m qt e m' evs okQ)
  refine ⟨fun i m => ?_, fun i m same e m' evs ok => ?_⟩
  · rcases key i m with dec | ⟨qs, qt⟩
    · exact .inr dec
    · exact .inl fun o => (qs o).trans (meetSys_of_agree (agree i m qs qt) o).symm
  · rcases key i m with dec | ⟨qs, qt⟩
    · cases (dec _).1 ok
    · exact (hS r).2 i m qs e m' evs ok

/-- The meet of the complete system and the reviewed-default table. -/
def meetDefault : Semantics := complete.meet reviewedDefault

theorem meetDefault_below_complete : meetDefault.Below complete := meet_below_left _ _

theorem meetDefault_below_reviewedDefault : meetDefault.Below reviewedDefault :=
  meet_below_right _ _

/-! ## Transfer along a restriction -/

section Transfer

variable {isa : UserIsa} {segs : List Segment} {p f : Sys SyscallEffect} {rp rf : RefusalFilter}

theorem budgetRefusedAtUsing_mono (R : Restricts p f) {classify : AllocBudgetClassifier}
    {c : Config isa} (h : BudgetRefusedAtUsing isa classify segs p c) :
    BudgetRefusedAtUsing isa classify segs f c := by
  obtain ⟨hh, h | ⟨x8, hx, ha | ⟨eff, m', evs, ok, hm, mat⟩⟩⟩ := h
  · exact ⟨hh, .inl h⟩
  · exact ⟨hh, .inr ⟨x8, hx, .inl ha⟩⟩
  · exact ⟨hh, .inr ⟨x8, hx, .inr ⟨eff, m', evs, Restricts.ok (R := R) ok, hm, mat⟩⟩⟩

theorem runBudgetRefusedFromUsing_mono (R : Restricts p f) (A : FiltersAgree p f rp rf)
    {classify : AllocBudgetClassifier} {c₀ : Config isa}
    (h : RunBudgetRefusedFromUsing isa classify segs p rp c₀) :
    RunBudgetRefusedFromUsing isa classify segs f rf c₀ := by
  obtain ⟨tr, c, s, b⟩ := h
  exact ⟨tr, c, s.of_restricts R A, budgetRefusedAtUsing_mono R b⟩

theorem mustExitInAt_noError {S : List Word} :
    ∀ {c d : Config isa} {tr : List Event}, Star segs p rp c tr d →
      MustExitInAt segs p rp S c → ∀ evs, ¬ SStep segs p rp d evs .error := by
  intro c d tr st
  induction st with
  | refl c =>
    intro h evs s
    cases h with
    | halted hh _ _ => rw [s.not_halted] at hh; cases hh
    | running _ _ noErr _ => exact noErr evs s
  | step s _ ih =>
    intro h
    cases h with
    | halted hh _ _ => rw [s.not_halted] at hh; cases hh
    | running _ _ _ next => exact ih (next _ _ s)

theorem mustExitInAt_not_reachesError {S : List Word} {c : Config isa}
    (h : MustExitInAt segs p rp S c) : ¬ ReachesError segs p rp c := by
  rintro ⟨tr, d, evs, st, err⟩
  exact mustExitInAt_noError st h evs err

/-- A must-exit proved against a restricting table holds against the restricted one. -/
theorem mustExitInAt_of_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf)
    {S : List Word} {c : Config isa} (h : MustExitInAt segs p rp S c) :
    MustExitInAt segs f rf S c := by
  induction h with
  | halted hh hS hk => exact .halted hh hS hk
  | @running c hh ex noErr next ih =>
    have nre : ¬ ReachesError segs p rp c :=
      mustExitInAt_not_reachesError (MustExitInAt.running hh ex noErr next)
    refine .running hh ?_ ?_ ?_
    · obtain ⟨evs, st, s⟩ := ex
      cases st with
      | next c' => exact ⟨evs, _, s.of_restricts R A⟩
      | error => exact (noErr evs s).elim
    · intro evs s
      exact errorFree_of_restricts R A nre ⟨[], c, evs, .refl c, s⟩
    · intro evs c' s
      exact ih evs c' (s.to_restricts R A nre)

end Transfer

end Silmaril.Process.LPS.Problems.NativeX86Complete
