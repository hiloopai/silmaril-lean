module

public import Silmaril.Wasm.Spec.Basic.Defs

@[expose] public section

/-!
# Temporal specification logics: LTL, CTL and a TLA-style action logic

All in the trace-institution format, over the events `Event A R X` of an interface. States are
*histories*: an atomic proposition at a position is a predicate of the history before the
position and the event there (`List α → α → Prop`), so the pending export (`activeExport`) and
every simple property are atoms.

## The action-invariant logic `act`

A formula is a position predicate `A`; a trace satisfies it when `A` holds at every position
(`EveryPos A`). This is the common safety core: every simple logic maps into it, and it maps
into LTL (`□ A`), CTL (`AG`) and TLA (`□[A]`) (`Silmaril.Wasm.Spec.Embed`).

## LTL

`LTL α`: atoms, `⊤`, `¬`, `∧`, `∨`, strong next `X`, until `U`; derived `◇`, `□`, weak next,
implication. Three readings of a trace set `T`:

* `ltlFin`: every finite trace of `T` satisfies the formula (LTL on finite traces, at position
  `0`). Exactly right for safety formulas such as `□ A`; liveness formulas fail on unfinished
  prefixes.
* `ltlInf`: every infinite limit of `T` satisfies it (`limits T`: the words all of whose finite
  prefixes are in `T`; for a game strategy this over-approximates its infinite plays, so proving
  a universal property over limits is sound for the infinite plays).
* `ltlMax`: every *maximal* behaviour satisfies it: infinite limits, and finite traces with no
  extension in `T`. With the divergence-observing Wasm semantics `wasmDivSem`, a call that may
  diverge contributes the maximal trace ending in `ret f .diverges`, so liveness ("every call
  returns") is refuted by divergence on any nondeterministic branch. (Over the plain `wasmSem`
  a divergent branch next to an answering one is invisible; liveness there is only meaningful
  for deterministic profiles.)

## CTL over the play tree

`CTL α`: state formulas over histories, `EX`, `AX`, `EF`, `AG`, `E[φ U ψ]`. The tree is the
prefix tree of `T`: the successors of a history `s ∈ T` are its one-event extensions in `T`.
`ctl` reads a formula at the root `[]`. Branching properties ("export `e` *can* call `log`",
`EF`) are not trace properties.

## TLA-style action logic

`TLA α`: `init p` (the first event), `□[A]` (every step satisfies the action `A`), weak fairness
`WF(A)` over infinite limits (if `A` is eventually always enabled, it is taken infinitely often;
enabledness is read off `T`), and conjunction.
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-! ## Words and limits -/

/-- The first `n` letters of an infinite word. -/
def prefixList {α : Type} (w : ℕ → α) (n : ℕ) : List α := List.ofFn fun i : Fin n => w i

/-- The infinite words all of whose finite prefixes lie in `T`. -/
def limits {α : Type} (T : Set (List α)) : Set (ℕ → α) := {w | ∀ n, prefixList w n ∈ T}

/-- A trace of `T` with no one-event extension in `T`. -/
def Maximal {α : Type} (T : Set (List α)) (t : List α) : Prop := t ∈ T ∧ ∀ e, t ++ [e] ∉ T

/-! ## The action-invariant logic -/

/-- Position predicates: formulas of `act` and atoms of the temporal logics. -/
abbrev PosPred {Ty : Type} (A R : Type) (X : Iface Ty) : Type :=
  List (Event A R X) → Event A R X → Prop

/-- **The action-invariant logic**: a position predicate holding everywhere. -/
abbrev act (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (PosPred A R) fun A t => EveryPos A t

/-! ## LTL -/

/-- LTL formulas with history-aware atoms. -/
inductive LTL (α : Type) : Type where
  /-- An atom: a predicate of the history before the position and the event there. -/
  | atom (p : List α → α → Prop)
  /-- Truth. -/
  | tt
  /-- Negation. -/
  | not (φ : LTL α)
  /-- Conjunction. -/
  | and (φ ψ : LTL α)
  /-- Disjunction. -/
  | or (φ ψ : LTL α)
  /-- Strong next. -/
  | next (φ : LTL α)
  /-- Until (`untl`; `until` is a keyword). -/
  | untl (φ ψ : LTL α)

namespace LTL

variable {α : Type}

/-- Eventually. -/
def ev (φ : LTL α) : LTL α := untl tt φ
/-- Always. -/
def alw (φ : LTL α) : LTL α := not (ev (not φ))
/-- Implication. -/
def imp (φ ψ : LTL α) : LTL α := or (not φ) ψ
/-- Weak next. -/
def wnext (φ : LTL α) : LTL α := not (next (not φ))

/-- Finite-trace semantics at position `k`. -/
def HoldsFin (t : List α) : ℕ → LTL α → Prop
  | k, atom p => ∃ h : k < t.length, p (t.take k) (t.get ⟨k, h⟩)
  | _, tt => True
  | k, not φ => ¬ HoldsFin t k φ
  | k, and φ ψ => HoldsFin t k φ ∧ HoldsFin t k ψ
  | k, or φ ψ => HoldsFin t k φ ∨ HoldsFin t k ψ
  | k, next φ => k + 1 < t.length ∧ HoldsFin t (k + 1) φ
  | k, untl φ ψ => ∃ j, k ≤ j ∧ j < t.length ∧ HoldsFin t j ψ ∧ ∀ i, k ≤ i → i < j → HoldsFin t i φ

/-- Infinite-word semantics at position `k`. -/
def HoldsInf (w : ℕ → α) : ℕ → LTL α → Prop
  | k, atom p => p (prefixList w k) (w k)
  | _, tt => True
  | k, not φ => ¬ HoldsInf w k φ
  | k, and φ ψ => HoldsInf w k φ ∧ HoldsInf w k ψ
  | k, or φ ψ => HoldsInf w k φ ∨ HoldsInf w k ψ
  | k, next φ => HoldsInf w (k + 1) φ
  | k, untl φ ψ => ∃ j, k ≤ j ∧ HoldsInf w j ψ ∧ ∀ i, k ≤ i → i < j → HoldsInf w i φ

end LTL

/-- LTL formulas at an interface. -/
abbrev LTLFm {Ty : Type} (A R : Type) (X : Iface Ty) : Type := LTL (Event A R X)

/-- **LTL on finite traces**: every trace satisfies the formula. -/
abbrev ltlFin (Ty A R : Type) : Logic Ty A R where
  Fm := LTLFm A R
  Sat T φ := ∀ t ∈ T, LTL.HoldsFin t 0 φ

/-- **LTL on infinite limits**. -/
abbrev ltlInf (Ty A R : Type) : Logic Ty A R where
  Fm := LTLFm A R
  Sat T φ := ∀ w ∈ limits T, LTL.HoldsInf w 0 φ

/-- **LTL on maximal behaviours**: infinite limits and maximal finite traces. -/
abbrev ltlMax (Ty A R : Type) : Logic Ty A R where
  Fm := LTLFm A R
  Sat T φ := (∀ w ∈ limits T, LTL.HoldsInf w 0 φ) ∧ ∀ t, Maximal T t → LTL.HoldsFin t 0 φ

/-! ## CTL -/

/-- CTL state formulas over histories. -/
inductive CTL (α : Type) : Type where
  /-- A predicate of the history. -/
  | atom (p : List α → Prop)
  /-- Truth. -/
  | tt
  /-- Negation. -/
  | not (φ : CTL α)
  /-- Conjunction. -/
  | and (φ ψ : CTL α)
  /-- Disjunction. -/
  | or (φ ψ : CTL α)
  /-- Some successor satisfies `φ`. -/
  | ex (φ : CTL α)
  /-- Every successor satisfies `φ`. -/
  | ax (φ : CTL α)
  /-- Some reachable state satisfies `φ`. -/
  | ef (φ : CTL α)
  /-- Every reachable state satisfies `φ`. -/
  | ag (φ : CTL α)
  /-- Along some path, `φ` holds until `ψ` does. -/
  | eu (φ ψ : CTL α)

/-- CTL satisfaction at the history `s` of the prefix tree of `T`. -/
def CTL.Holds {α : Type} (T : Set (List α)) : List α → CTL α → Prop
  | s, atom p => p s
  | _, tt => True
  | s, not φ => ¬ CTL.Holds T s φ
  | s, and φ ψ => CTL.Holds T s φ ∧ CTL.Holds T s ψ
  | s, or φ ψ => CTL.Holds T s φ ∨ CTL.Holds T s ψ
  | s, ex φ => ∃ e, s ++ [e] ∈ T ∧ CTL.Holds T (s ++ [e]) φ
  | s, ax φ => ∀ e, s ++ [e] ∈ T → CTL.Holds T (s ++ [e]) φ
  | s, ef φ => ∃ u, s ++ u ∈ T ∧ CTL.Holds T (s ++ u) φ
  | s, ag φ => ∀ u, s ++ u ∈ T → CTL.Holds T (s ++ u) φ
  | s, eu φ ψ => ∃ u, s ++ u ∈ T ∧ CTL.Holds T (s ++ u) ψ ∧
      ∀ v, v <+: u → v ≠ u → CTL.Holds T (s ++ v) φ

/-- **CTL over the play tree**, read at the root. -/
abbrev ctl (Ty A R : Type) : Logic Ty A R where
  Fm X := CTL (Event A R X)
  Sat T φ := CTL.Holds T [] φ

/-! ## A TLA-style action logic -/

/-- TLA-style formulas over actions (position predicates). -/
inductive TLA (α : Type) : Type where
  /-- The first event, if any, satisfies `p`. -/
  | init (p : α → Prop)
  /-- Every step satisfies the action `A`. -/
  | box (A : List α → α → Prop)
  /-- Weak fairness of the action `A` along infinite limits. -/
  | wf (A : List α → α → Prop)
  /-- Conjunction. -/
  | and (φ ψ : TLA α)

/-- The action `A` is enabled after the history `s` in `T`. -/
def Enabled {α : Type} (T : Set (List α)) (s : List α) (A : List α → α → Prop) : Prop :=
  ∃ e, s ++ [e] ∈ T ∧ A s e

/-- TLA satisfaction by a trace set. -/
def TLA.Sat {α : Type} (T : Set (List α)) : TLA α → Prop
  | init p => ∀ t ∈ T, ∀ e, t.head? = some e → p e
  | box A => ∀ t ∈ T, EveryPos A t
  | wf A => ∀ w ∈ limits T, (∃ n, ∀ m, n ≤ m → Enabled T (prefixList w m) A) →
      ∀ n, ∃ m, n ≤ m ∧ A (prefixList w m) (w m)
  | and φ ψ => TLA.Sat T φ ∧ TLA.Sat T ψ

/-- **The TLA-style action logic.** -/
abbrev tla (Ty A R : Type) : Logic Ty A R where
  Fm X := TLA (Event A R X)
  Sat T φ := TLA.Sat T φ

end Silmaril.Wasm.Spec
