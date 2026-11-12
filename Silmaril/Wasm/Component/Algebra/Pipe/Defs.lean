module

public import Silmaril.Wasm.Component.Algebra.Ops.Defs
public import Silmaril.Wasm.Component.Streams.Spec.Defs

/-!
# Stream pipelines in the component algebra: definitions

Stream transformers (`Silmaril.Wasm.Component.Streams`, `Tr σ α β`) are specified as Mealy machines;
the components that implement them are components of the IR. To state pipeline laws in the
algebra we fix **how a transformer is denoted by a strategy**:

* `StreamSem C`: a semantics of transformers as strategies over `sigU`, on a stream interface of
  `width` functions (the same number of imports and exports), which is **compositional**
  (`den_comp`: the composite transformer `T.comp U` is denoted by the composite strategy),
  **respects equivalence of transformers** (`den_congr`) and denotes the identity transformer by
  copycat on the interface (`den_id`). A concrete `StreamSem` is a game semantics of the stream
  built-ins; none is constructed here, so every theorem that uses one is conditional on it.
* `Realizes S c T`: the component `c` has the stream interface and the strategy `S.den T`.
* `pipe I [c₁, …, cₙ]`: the pipeline `seq c₁ (seq c₂ (… (seq cₙ (ident …))))` on the input
  interface `I` (`ident I` when empty).
* `chain ts`: the composite of a list of transformers on one item type (`Tr.id` when empty).

Theorems in `Silmaril.Wasm.Component.Algebra.Pipe.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams

variable {M : Type}

/-- **A pipeline of components**, plugged positionally. -/
def pipe (I : Iface) : List (Comp M) → Comp M
  | [] => ident I
  | c :: cs => seq c (pipe (exportIface c) cs)

/-- The composite of a chain of transformers on one item type. -/
def chain {α : Type} : List (Σ σ : Type, Tr σ α α) → Σ σ : Type, Tr σ α α
  | [] => ⟨Unit, Tr.id⟩
  | t :: ts => ⟨t.1 × (chain ts).1, t.2.comp (chain ts).2⟩

variable [CoreModule M]

/-- **A compositional semantics of stream transformers** as component strategies. -/
structure StreamSem (C : CoreSem M) where
  /-- The number of functions of the stream interface (imports and exports). -/
  width : Nat
  /-- The strategy of a component implementing a transformer. -/
  den : {σ α β : Type} → Tr σ α β → Strategy sigU sigU
  /-- Composite transformers are denoted by composite strategies. -/
  den_comp : ∀ {σ τ α β γ : Type} (T : Tr σ α β) (U : Tr τ β γ),
    den (T.comp U) = (den T).comp (den U)
  /-- Equivalent transformers have the same strategy. -/
  den_congr : ∀ {σ τ α β : Type} {T : Tr σ α β} {U : Tr τ α β}, T.Equiv U → den T = den U
  /-- The identity transformer is copycat on the stream interface. -/
  den_id : ∀ {α : Type}, den (Tr.id : Tr Unit α α) = Strategy.ofHandler (maskH width)

/-- The component `c` **realises** the transformer `T`. -/
def Realizes {C : CoreSem M} (S : StreamSem C) {σ α β : Type} (c : Comp M) (T : Tr σ α β) :
    Prop :=
  c.imports.length = S.width ∧ c.exports.length = S.width ∧ c.denU C = S.den T

end Silmaril.Wasm.Component.Algebra
