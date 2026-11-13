module

public import Silmaril.Wasm.Spec.Component.Defs

@[expose] public section

/-!
# The reference Component Model machine as a model of the specification format

`refSem prof h σ0` reads the copied reference semantics of the Component Model
(`Silmaril.Wasm.Component.Reference`, the machine of `definitions.py` over any core engine `E`,
e.g. `core3P P`: Core 3.0 at an arbitrary profile) as a semantics in the trace-institution
format. Its observations are exactly the ground truth `exportBehaviours`:

* a program `p : RefProg E X` is a reference component `p.comp` with root instantiation
  arguments `p.args`, and the export name `p.names j` of each export `j` of `X`;
* its traces are the prefixes of `[call j a, ret j b]` for every `b ∈ exportBehaviours prof h σ0
  p.comp p.args (p.names j) a`: instantiate from the empty store, then call export `j` once.

So every reference outcome is an event, including `diverges`, `deadlocks` and cancelled returns
(`returns none`), at every type level: strings, lists, handles, streams and futures are values
of the reference machine, and `exportBehaviours` covers async exports (their outcome is the
resolution of the top-level call). What is *not* observed: calls of host functions (the host
`h` implements the imports internally, so the traces have no import events), reads and writes
of streams and futures after they cross the boundary (the stream ends are values; their
traffic is host-internal), and sequences of calls on one instance (each trace is one call on a
fresh instance: the machine's `Calls` relation does return the next configuration, but the
reference `exportBehaviours` interface is per call).

Grounding: `refSem_retPost_iff`, `refSem_contract_iff` (`Silmaril.Wasm.Spec.Component.Ref.Thms`).
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component.Reference

/-- A reference component at the interface `X`: the component, its root instantiation
arguments, and the name of each export. -/
structure RefProg (E : Engine) (X : CIface) where
  /-- The component. -/
  comp : CompAst E.Module
  /-- Root instantiation arguments. -/
  args : Silmaril.Wasm.Component.Instantiate.Exports E
  /-- The export name of each export of `X`. -/
  names : X.Exp → String

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- The traces of a reference component: one export call on a fresh instance. -/
def refTraces (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ) {X : CIface}
    (p : RefProg E X) : Set (List (CEvent X)) :=
  {t | t = [] ∨ (∃ j a, t = [Event.call j a]) ∨
    ∃ j a b, b ∈ exportBehaviours prof h σ0 p.comp p.args (p.names j) a ∧
      t = [Event.call j a, Event.ret j b]}

/-- The prefixes of a two-element list. -/
theorem prefix_pair {α : Type} {s : List α} {x y : α} (h : s <+: [x, y]) :
    s = [] ∨ s = [x] ∨ s = [x, y] := by
  obtain ⟨u, hu⟩ := h
  rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, s⟩⟩⟩
  · exact .inl rfl
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
    exact .inr (.inl (by rw [hu.1]))
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
    exact .inr (.inr (by rw [hu.1, hu.2.1]))
  · simp at hu

/-- The traces of a reference component are good. -/
theorem refTraces_good (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ)
    {X : CIface} (p : RefProg E X) : Good (refTraces prof h σ0 p) where
  nil_mem := .inl rfl
  of_prefix := by
    rintro s t (rfl | ⟨j, a, rfl⟩ | ⟨j, a, b, hb, rfl⟩) hs
    · exact .inl (List.prefix_nil.1 hs)
    · rcases List.prefix_cons_iff.1 hs with rfl | ⟨u, rfl, hu⟩
      · exact .inl rfl
      · exact .inr (.inl ⟨j, a, by rw [List.prefix_nil.1 hu]⟩)
    · rcases prefix_pair hs with rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl ⟨j, a, rfl⟩)
      · exact .inr (.inr ⟨j, a, b, hb, rfl⟩)

/-- **The reference semantics**: reference components, observed one export call at a time,
at component choice profile `prof` with host `h` from host state `σ0`. -/
abbrev refSem (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host E σ) (σ0 : σ) :
    Semantics CFn (List RVal) Outcome where
  Prog := RefProg E
  traces p := refTraces prof h σ0 p
  good p := refTraces_good prof h σ0 p

end Silmaril.Wasm.Spec.Component
