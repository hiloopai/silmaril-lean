module

public import Silmaril.Compiler.Core.Semantics.Defs
public import Silmaril.Compile.Category.Pass
public import Silmaril.Compiler.C.Sem.C0.Defs
@[expose] public section

/-!
# The process boundary of the Core → x86 route

This is the hypothesis-based adapter for core-comp's frozen
`Silmaril/Compile/Core/Spec.lean` at `80c845cafdb5ff5335a31467008e74d89d126415`.
That file cannot be imported unchanged here: its source dynamics has `Outcome.aborted`
and library `exit`/`abort`, absent from csem's frozen dynamics. No equality of those
source semantics is assumed silently, and this file imports no compiler implementation.

`X86Model` bundles the *target* part of that specification. Instantiate its context
with `(Space, exit, E0, saved, init)`, `loaded` with `Spec.Loaded`, and `beh` with
`Spec.MachineBeh`. `process` reads the trusted crt0 observation: exit and stdout,
abort as signal 6, trap as signal 4, fault as the chosen fault signal, and divergence.
Only resource exhaustion maps to `none`. The caller supplies this instance; there is
no claim here that the abstract target is already connected to the x86 model.

The fallback theorem statements live in `TargetsCoreX86.lean`. Applying them to
`Verified.compile_sound` requires an explicit bridge from `Spec.Allowed doc` to
`allows (Core.beh (elaborate doc))`. In particular the enum environment, startup,
library outcomes and fault observations must agree. Trusted C → Core elaboration is
also an explicit local validity premise, or a `Pass (Core.cAC S)`.

Resource exhaustion is allowed by core-comp even for an empty source behaviour set.
Since `Convention.lift` is an existential image, *every* convention sends the empty
set to the empty set. Thus a `Valid` restatement needs a source behaviour whenever
the target can exhaust; a nonempty-source premise is a convenient sufficient condition.
These conventions permit exhaustion through the observation relation and are not
read-back conventions / institution comorphisms in the functional sense.
-/

namespace Silmaril.Compile.C.Sem.CoreX86

open Silmaril.Compile.Category CategoryTheory

/-- The loaded-machine boundary, supplied by the backend specification.
All contexts satisfying `loaded` contribute behaviours, not just one chosen execution. -/
structure X86Model where
  Artifact : Type
  Context : Type
  Observation : Type
  loaded : Artifact → Context → Prop
  beh : Artifact → Context → Set Observation
  /-- Trusted process observation; `none` means resource exhaustion only. -/
  process : Observation → Option Obs

/-- Closed x86 artifacts, observed over every permitted loading and initial machine. -/
def X86Model.lang (M : X86Model) : Language.{0} where
  Iface := PUnit
  Prog := M.Artifact
  iface _ := ⟨⟩
  Obs := M.Observation
  beh a := {o | ∃ ctx, M.loaded a ctx ∧ o ∈ M.beh a ctx}

/-- Matching at crt0: a process agrees, or the target exhausted a resource. -/
def processMatch (M : X86Model) (o : Obs) (x : M.Observation) : Prop :=
  M.process x = none ∨ M.process x = some o

/-- Core → x86, including the backend's permitted resource exhaustion. -/
def c_CoreX86 (M : X86Model) : Core.lang ⟶ M.lang :=
  ⟨fun _ => PUnit.unit, processMatch M⟩

/-- Typed Ail → x86 for any rung of C semantics. Use `S = C0.sem` for C-as-Ail. -/
def c_Cx86 (S : Semantics) (M : X86Model) : cSyntax.lang S ⟶ M.lang :=
  ⟨fun _ => PUnit.unit, processMatch M⟩

/-- A source behaviour set's process contract, with unconditional resource exhaustion.
Unlike a convention's lift, this also permits exhaustion when `B` is empty. -/
def allows (M : X86Model) (B : Set Obs) : Set M.Observation :=
  {x | M.process x = none ∨ ∃ o ∈ B, M.process x = some o}

/-- The shape of core-comp's `SoundSpec`, after an explicit source/observation bridge.
This is a hypothesis on a compiler, not a proved property of an imported compiler. -/
def SoundSpec (M : X86Model) {Document : Type}
    (elaborate : Document → Core.lang.Prog)
    (compile : Document → Option M.Artifact) : Prop :=
  ∀ doc a, compile doc = some a → ∀ ctx, M.loaded a ctx →
    ∀ x, x ∈ M.beh a ctx → x ∈ allows M (Core.beh (elaborate doc))

/-- Exact validity criterion, including the witness needed when the target exhausts. -/
theorem core_x86_valid_iff (M : X86Model) (p : Core.lang.Prog) (a : M.Artifact) :
    Valid (c_CoreX86 M) p a ↔
      M.lang.beh a ⊆ allows M (Core.beh p) ∧
      ((∃ x ∈ M.lang.beh a, M.process x = none) → (Core.beh p).Nonempty) := by
  rw [valid_iff_beh (c_CoreX86 M) p a]
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨o, ho, hm⟩ := h.2 hx
      exact hm.elim Or.inl (fun he => .inr ⟨o, ho, he⟩)
    · rintro ⟨x, hx, _⟩
      obtain ⟨o, ho, _⟩ := h.2 hx
      exact ⟨o, ho⟩
  · intro h
    refine ⟨rfl, ?_⟩
    intro x hx
    rcases h.1 hx with hn | ⟨o, ho, he⟩
    · obtain ⟨o, ho⟩ := h.2 ⟨x, hx, hn⟩
      exact ⟨o, ho, Or.inl hn⟩
    · exact ⟨o, ho, Or.inr he⟩

/-- An accepted program with a source behaviour has exactly the usual validity contract. -/
theorem core_compile_sound_iff_valid (M : X86Model) {Document : Type}
    (elaborate : Document → Core.lang.Prog) (compile : Document → Option M.Artifact)
    (hne : ∀ doc a, compile doc = some a → (Core.beh (elaborate doc)).Nonempty) :
    SoundSpec M elaborate compile ↔
      ∀ doc a, compile doc = some a → Valid (c_CoreX86 M) (elaborate doc) a := by
  constructor
  · intro h doc a hc
    apply (core_x86_valid_iff M (elaborate doc) a).2
    exact ⟨fun _ ⟨ctx, hl, hb⟩ => h doc a hc ctx hl _ hb, fun _ => hne doc a hc⟩
  · intro h doc a hc ctx hl x hb
    exact ((core_x86_valid_iff M (elaborate doc) a).1 (h doc a hc)).1 ⟨ctx, hl, hb⟩

/-- Adapter for the actual backend theorem: its source/observation bridge is a separate premise. -/
theorem core_compile_valid_of_sound (M : X86Model) {Document : Type}
    (elaborate : Document → Core.lang.Prog) (compile : Document → Option M.Artifact)
    (Allowed : Document → M.Observation → Prop)
    (hsound : ∀ doc a, compile doc = some a → ∀ ctx, M.loaded a ctx →
      ∀ x, x ∈ M.beh a ctx → Allowed doc x)
    (hbridge : ∀ doc x, Allowed doc x → x ∈ allows M (Core.beh (elaborate doc)))
    (hne : ∀ doc a, compile doc = some a → (Core.beh (elaborate doc)).Nonempty) :
    ∀ doc a, compile doc = some a → Valid (c_CoreX86 M) (elaborate doc) a :=
  (core_compile_sound_iff_valid M elaborate compile hne).1
    (fun doc a hc ctx hl x hb => hbridge doc x (hsound doc a hc ctx hl x hb))

/-- The process convention is unchanged by the route through Core. -/
theorem c_AC_comp_c_CoreX86 (S : Semantics) (M : X86Model) :
    Core.cAC S ≫ c_CoreX86 M = c_Cx86 S M :=
  Convention.ext rfl Relation.eq_comp

/-- Each route contributes just its local validity lemma. -/
theorem c_x86_of_core {S : Semantics} {M : X86Model} {p : cSyntax.Prog}
    {q : Core.lang.Prog} {a : M.Artifact}
    (helab : Valid (Core.cAC S) p q) (hbackend : Valid (c_CoreX86 M) q a) :
    Valid (c_Cx86 S M) p a := by
  rw [← c_AC_comp_c_CoreX86]
  exact valid_comp_le (Core.cAC S) (c_CoreX86 M) p a ⟨q, helab, hbackend⟩

/-- A C → Core pass followed by the backend, at the direct C → x86 convention.
Specialize to `S = C0.sem` for the first rung. -/
def coreRoute {S : Semantics} {M : X86Model}
    (elaborate : Pass (Core.cAC S)) (backend : Pass (c_CoreX86 M)) : Pass (c_Cx86 S M) :=
  (elaborate ≫ₚ backend).congr (c_AC_comp_c_CoreX86 S M)

end Silmaril.Compile.C.Sem.CoreX86
