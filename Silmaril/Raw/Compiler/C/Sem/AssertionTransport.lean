module

public import Silmaril.Compiler.C.Sem.CoreX86.Defs
public import Silmaril.Compiler.C.Sem.ElabC0.Defs
public import Silmaril.Compiler.C.Sem.AssertionExecution.Defs
@[expose] public section

/-!
# Assertion transport across validated compilation and decompilation

Assertions here are predicates on complete observations. Intermediate-state assertions
must first be connected to this boundary by an adequacy theorem for their executable
semantics. `Checked` records both a universal assertion and an actual defined behaviour:
empty behaviour sets cannot certify it. The `defined` parameter must be instantiated
with the source semantics' own safety criterion; nonemptiness alone is not UB freedom.

For decompilation, `Valid` must point from the proposed C/IR specification to the
assembly being checked. Running a decompiler does not provide this certificate.
A read-back plus behaviour coverage gives equivalence, whereas backward simulation
alone gives only assertion preservation. Resource exhaustion is explicitly allowed in
the Core/x86 boundary below, so that theorem does not establish termination.
-/

namespace Silmaril.Compile.C.Sem.AssertionTransport

open Silmaril.Compile.Category CategoryTheory

universe u

/-- A non-vacuous observation contract with an explicit definedness predicate.
This is partial correctness; `defined` may admit divergence. -/
def Checked (L : Language.{u}) (p : L.Prog) (defined assertion : Set L.Obs) : Prop :=
  (L.beh p).Nonempty ∧ L.Sat p (defined ∩ assertion)

/-- A validated compilation transfers any source observation assertion to a target
predicate whenever the observation relation preserves that predicate. -/
theorem transport {L T : Language.{u}} {c : L ⟶ T} {p : L.Prog} {q : T.Prog}
    (hv : Valid c p q) {P : Set L.Obs} {Q : Set T.Obs}
    (hP : L.Sat p P) (hrel : ∀ s t, c.R s t → s ∈ P → t ∈ Q) :
    T.Sat q Q := by
  intro t ht
  obtain ⟨s, hs, hr⟩ := ((valid_iff_beh c p q).1 hv).2 ht
  exact hrel s t hr (hP hs)

/-- Target nonemptiness is a separate obligation: refinement may erase all behaviours.
The relation must preserve definedness as well as the desired assertion. -/
theorem checked_transport {L T : Language.{u}} {c : L ⟶ T} {p : L.Prog} {q : T.Prog}
    (hv : Valid c p q) {D P : Set L.Obs} {E Q : Set T.Obs}
    (hp : Checked L p D P) (hne : (T.beh q).Nonempty)
    (hrel : ∀ s t, c.R s t → s ∈ D ∩ P → t ∈ E ∩ Q) :
    Checked T q E Q :=
  ⟨hne, transport hv hp.2 hrel⟩

/-- Exact read-back coverage supplies the missing reverse direction for assertion
translation. This is an extra semantic certificate, not a consequence of `Valid`. -/
theorem assertion_iff_of_readBack {L T : Language.{u}} {c : L ⟶ T}
    (rb : Convention.ReadBack c) {p : L.Prog} {q : T.Prog}
    (hv : Valid c p q) (coverage : L.beh p ⊆ rb.g '' T.beh q) (P : Set L.Obs) :
    L.Sat p P ↔ T.Sat q (rb.g ⁻¹' P) := by
  constructor
  · intro hp
    rw [← rb.lift_eq]
    exact hv.transport hp
  · intro hq s hs
    obtain ⟨t, ht, he⟩ := coverage hs
    exact he ▸ hq ht

/-- Regression witness: refinement can remove every observation, so `Valid` alone
cannot establish non-vacuous correctness or reverse assertion equivalence. -/
def erasureExample : Language.{0} where
  Iface := Unit
  Prog := Bool
  iface _ := ()
  Obs := Unit
  beh b := if b then Set.univ else ∅

theorem valid_can_erase :
    Valid (𝟙 erasureExample) true false ∧
      ¬ Checked erasureExample false Set.univ Set.univ := by
  constructor
  · apply (valid_iff_beh _ _ _).2
    exact ⟨rfl, fun _ h => False.elim h⟩
  · intro h
    simpa [erasureExample] using h.1

/-- Core assertions reach every loaded x86 execution via the existing validated
backend convention. The conclusion allows resource exhaustion; it asserts neither
termination nor the absence of exhaustion. Signals/divergence must be excluded by `P`
if the client wants to exclude them. -/
theorem core_x86_assertion {M : CoreX86.X86Model} {p : Core.lang.Prog}
    {a : M.Artifact} (hv : Valid (CoreX86.c_CoreX86 M) p a)
    {P : Set Obs} (hp : Core.lang.Sat p P) :
    ∀ ctx, M.loaded a ctx → ∀ x, x ∈ M.beh a ctx →
      M.process x = none ∨ ∃ o ∈ P, M.process x = some o := by
  intro ctx hl x hx
  obtain ⟨o, ho, hr⟩ := hv.transport hp (show x ∈ M.lang.beh a from ⟨ctx, hl, hx⟩)
  exact hr.elim Or.inl (fun he => Or.inr ⟨o, ho, he⟩)

/-- Checked structural elaboration gives exact assertion equivalence, not only
forward preservation. The elaborator's certificate includes exact execution checks. -/
theorem c0_core_assertion_iff {p : Silmaril.Cerberus.Ail.TypedProgram}
    {q : Core.lang.Prog} (helab : ElabC0.elaborate p = some q) (P : Set Obs) :
    C0.lang.Sat p P ↔ Core.lang.Sat q P := by
  change C0.beh p ⊆ P ↔ Core.beh q ⊆ P
  rw [(ElabC0.elaborate_sound helab).2]

/-- A source execution certificate and the generated Lean goal are equivalent to
an assertion about every behaviour of the checked Core translation. -/
theorem c0_process_goal_iff_core {p : Silmaril.Cerberus.Ail.TypedProgram}
    {q : Core.lang.Prog} {fuel : Nat} {o : Obs}
    (run : C0.run fuel p = .done o) (helab : ElabC0.elaborate p = some q)
    (assertion : Silmaril.Cerberus.Assertion.Pure.Formula) :
    AssertionExecution.ProcessGoal assertion o ↔
      Core.lang.Sat q {o | AssertionExecution.ProcessPost assertion o} :=
  (AssertionExecution.process_goal_iff_sat run assertion).trans (c0_core_assertion_iff helab _)

/-- Push a run-certified source goal down to every loaded assembly execution.
Only the existing elaboration and backend certificates are trusted premises. -/
theorem c0_process_goal_x86 {M : CoreX86.X86Model}
    {p : Silmaril.Cerberus.Ail.TypedProgram} {q : Core.lang.Prog}
    {a : M.Artifact} {fuel : Nat} {o : Obs}
    (run : C0.run fuel p = .done o) (helab : ElabC0.elaborate p = some q)
    (backend : Valid (CoreX86.c_CoreX86 M) q a)
    (assertion : Silmaril.Cerberus.Assertion.Pure.Formula)
    (goal : AssertionExecution.ProcessGoal assertion o) :
    ∀ ctx, M.loaded a ctx → ∀ x, x ∈ M.beh a ctx →
      M.process x = none ∨ ∃ result,
        AssertionExecution.ProcessPost assertion result ∧ M.process x = some result :=
  core_x86_assertion backend ((c0_process_goal_iff_core run helab assertion).mp goal)

/-- Explicitly discharging exhaustion gives an ordinary process assertion. -/
theorem core_x86_assertion_no_exhaustion {M : CoreX86.X86Model} {p : Core.lang.Prog}
    {a : M.Artifact} (hv : Valid (CoreX86.c_CoreX86 M) p a)
    {P : Set Obs} (hp : Core.lang.Sat p P)
    (hne : ∀ x ∈ M.lang.beh a, M.process x ≠ none) :
    ∀ x ∈ M.lang.beh a, ∃ o ∈ P, M.process x = some o := by
  intro x hx
  obtain ⟨ctx, hl, hb⟩ := hx
  exact (core_x86_assertion hv hp ctx hl x hb).resolve_left (hne x ⟨ctx, hl, hb⟩)

end Silmaril.Compile.C.Sem.AssertionTransport
