module

public import Silmaril.Wasm.Spec.Component.Defs
public import Silmaril.Wasm.Component.Semantics.Defs

@[expose] public section

/-!
# Components of Silmaril's IR as models of the component specification format

Silmaril's component IR (`Silmaril.Wasm.Component`) denotes a component `c : Comp M` over a core
semantics `C : CoreSem M` by the game strategy `c.den C`
(`Strategy (sigN imports) (sigN exports)`). Its moves carry *dynamically typed* payloads
(`Payload`: component values `vals vs` or flat core values `flat xs`) and answers
`Option Payload` (`none` is a trap). This module reads those plays as component events:

* a call (question) with payload `vals vs` is the event with arguments `vs.map toRefVal`;
* an answer `some (vals ws)` is `returns (some (ws.map toRefVal))`, an answer `none` is `traps`;
* moves with flat payloads (which only arise from ill-formed environments: component-level
  environments pass and return component values) end the readable part of a play: a play is
  observed exactly when all its moves are component-level (`mapAll (moveEv? …)`).

Hence:

* `irTraces σ`: the observed traces of a strategy, a good set (prefix closure is
  `mapAll_prefix`);
* `IRProg M X`: a component whose interface (`cface`, the reference types of its import and
  export function types) is `X`;
* `irSem C : Semantics CFn (List RVal) Outcome`: **the IR semantics over `C`**. With
  `C = Reference.core3Sem P` or `Reference.modSem P` the core instances are Core 3.0 instances
  at an arbitrary profile `P` (`Silmaril.Wasm.Game` strategies built from Core `Step P`).

Divergence, deadlock and cancellation are not observed by the IR's (finite-play) strategies;
the IR never produces those outcomes. Grounding in the reference machine is in
`Silmaril.Wasm.Spec.Component.IR.Thms`.
-/

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Games
open Silmaril.Wasm.Component (Payload sigN Comp CoreSem CoreModule)
open Silmaril.Wasm.Component.Reference (toRefVal)

/-! ## Reading moves as events -/

/-- The arguments of a payload, as reference values (`none` for flat payloads). -/
def argsOf : Payload → Option (List RVal)
  | .vals vs => some (vs.map toRefVal)
  | .flat _ => none

/-- The outcome of an answer (`none` for flat payloads). -/
def outOf : Option Payload → Option Outcome
  | some (.vals ws) => some (.returns (some (ws.map toRefVal)))
  | some (.flat _) => none
  | none => some .traps

/-- An event of the game signature `sigN n` as a side event with `m = n` functions. -/
def sideEv? {n m : ℕ} (h : n = m) : Ev (sigN n) → Option (SideEv (List RVal) Outcome m)
  | .ask q => (argsOf q.2).map fun a => .ask (Fin.cast h q.1) a
  | .ans q r => (outOf r).map fun o => .ans (Fin.cast h q.1) o

/-- A move of the IR game as an event at `X`. -/
def moveEv? {n k : ℕ} {X : CIface} (hi : n = X.imports.length) (he : k = X.exports.length) :
    Move (sigN n) (sigN k) → Option (CEvent X)
  | .inl e => (sideEv? hi e).map Sum.inl
  | .inr e => (sideEv? he e).map Sum.inr

/-- Map every element, failing if one fails. -/
def mapAll {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: l => (f a).bind fun b => (mapAll f l).map (b :: ·)

/-- Prefixes of a mapped list are mapped prefixes. -/
theorem mapAll_prefix {α β : Type} (f : α → Option β) :
    ∀ {s : List α} {t u : List β}, mapAll f s = some t → u <+: t →
      ∃ s', s' <+: s ∧ mapAll f s' = some u
  | [], t, u, h, hu => by
    have ht : t = [] := (Option.some.inj h).symm
    subst ht
    exact ⟨[], List.prefix_refl _, by rw [List.prefix_nil.1 hu]; rfl⟩
  | a :: l, t, u, h, hu => by
    simp only [mapAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, t', ht', rfl⟩ := h
    rcases u with _ | ⟨c, u⟩
    · exact ⟨[], List.nil_prefix, rfl⟩
    · obtain ⟨rfl, hu'⟩ := List.cons_prefix_cons.1 hu
      obtain ⟨s', hs', hm⟩ := mapAll_prefix f ht' hu'
      exact ⟨a :: s', List.cons_prefix_cons.2 ⟨rfl, hs'⟩, by simp [mapAll, hb, hm]⟩

/-- The observed traces of an IR strategy at `X`. -/
def irTraces {n k : ℕ} {X : CIface} (hi : n = X.imports.length) (he : k = X.exports.length)
    (σ : Strategy (sigN n) (sigN k)) : Set (List (CEvent X)) :=
  {t | ∃ s ∈ σ, mapAll (moveEv? hi he) s = some t}

/-- Observed traces are good. -/
theorem irTraces_good {n k : ℕ} {X : CIface} (hi : n = X.imports.length)
    (he : k = X.exports.length) (σ : Strategy (sigN n) (sigN k)) : Good (irTraces hi he σ) where
  nil_mem := ⟨[], σ.nil_mem, rfl⟩
  of_prefix := by
    rintro u t ⟨s, hs, h⟩ hu
    obtain ⟨s', hs', hm⟩ := mapAll_prefix _ h hu
    exact ⟨s', σ.of_prefix hs hs', hm⟩

/-! ## Programs and the semantics -/

/-- A component of the IR at the interface `X`. -/
structure IRProg (M : Type) [CoreModule M] (X : CIface) where
  /-- The component. -/
  comp : Comp M
  /-- Its interface is `X`. -/
  cface_eq : cface comp = X

variable {M : Type} [CoreModule M]

/-- The imports of an IR program are those of its interface. -/
theorem IRProg.hi {X : CIface} (p : IRProg M X) : p.comp.imports.length = X.imports.length := by
  have h := congrArg (fun Y : CIface => Y.imports.length) p.cface_eq
  simpa [cface] using h

/-- The exports of an IR program are those of its interface. -/
theorem IRProg.he {X : CIface} (p : IRProg M X) : p.comp.exports.length = X.exports.length := by
  have h := congrArg (fun Y : CIface => Y.exports.length) p.cface_eq
  simpa [cface] using h

/-- A component as a program at its interface. -/
def IRProg.ofComp (c : Comp M) : IRProg M (cface c) := ⟨c, rfl⟩

/-- **The IR semantics over the core semantics `C`.** -/
abbrev irSem (C : CoreSem M) : Semantics CFn (List RVal) Outcome where
  Prog := IRProg M
  traces p := irTraces p.hi p.he (p.comp.den C)
  good _ := irTraces_good _ _ _

end Silmaril.Wasm.Spec.Component
