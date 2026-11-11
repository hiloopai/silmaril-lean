module

public import Silmaril.Wasm.Spec.Maps.Defs
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms

@[expose] public section

/-!
# Scalar Core 3.0 modules as models of the trace-institution format

The models of the Wasm specification institutions are the game semantics of instantiated Core 3.0
modules from `Silmaril.Wasm.Game`, at an **arbitrary** silmaril profile `P` (any `$ND`, relaxed
choices, NaN policy and grow policy; no determinism is assumed).

* `WIface := Iface FnType`: interfaces typed by scalar function types (numbers, `v128`,
  `(ref null? i31)`, the store-independent fragment of `Silmaril.Wasm.Game.Signature`).
* `WEvent X := Event (List Val) (Behaviour Val) X`: calls carry Core argument lists; returns
  carry Core behaviours (`returns vs`, `traps`, `throws a`; `diverges` only in the
  divergence-observing semantics).
* `WasmProg X`: an instantiated module with interface `X` (export addresses and store), read as
  the `ScalarInstance` `p.inst` whose import and export types are those of `X`. A module `m`
  with `IsInstance m mt I` gives one (`WasmProg.ofInstance`).
* `moveEvent`: a move of `I.E ↠ I.F` as an event (typed arguments forgotten, answers read as
  behaviours, `Answer.toBehaviour`).
* `wasmSem P`: the traces of `p` are the plays of `p.inst.strategy P p.store` read as events.
  These plays are defined by Core reduction: each Proponent move is a host-free run
  `Reach P` of silmaril-lean's single-threaded machine (`InternalP P`, i.e. Core
  `Step P` with the empty host), and each environment answer resumes the thread with
  `resumeResult`. They are receptive, so they cover **every** environment.
* `wasmDivSem P`: as `wasmSem P`, plus, for every play after which the divergence-observing
  strategy `p.inst.dstrategy P p.store` may diverge (an infinite host-free run of the pending
  export call), that play followed by `ret f .diverges`. Under a nondeterministic profile a call
  may both answer and diverge; only this semantics records the divergent branch.

Grounding theorems (closed-world Core behaviours read off traces, via adequacy M2) are in
`Silmaril.Wasm.Spec.Wasm.Thms`.
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- Interfaces typed by scalar Wasm function types. -/
abbrev WIface : Type := Iface FnType

/-- Events of Wasm programs: Core argument lists and Core behaviours. -/
abbrev WEvent (X : WIface) : Type := Event (List Val) (Behaviour Val) X

/-- An instantiated scalar module with interface `X`: export addresses and a store. -/
structure WasmProg (X : WIface) where
  /-- The function address of each export. -/
  addrs : List Nat
  /-- The store after instantiation. -/
  store : Store Nat

/-- The scalar instance of a program. -/
def WasmProg.inst {X : WIface} (p : WasmProg X) : ScalarInstance :=
  ⟨X.imports, X.exports, p.addrs, p.store⟩

/-- The interface of a scalar instance. -/
def ifaceOf (I : ScalarInstance) : WIface := ⟨I.imports, I.exports⟩

/-- A scalar instance as a program at its interface. -/
def WasmProg.ofInstance (I : ScalarInstance) : WasmProg (ifaceOf I) := ⟨I.addrs, I.store⟩

/-- An event at one side of a scalar interface. -/
def evOf {ts : List FnType} : Ev (ifaceSig ts) → SideEv (List Val) (Behaviour Val) ts.length
  | .ask e => .ask e.1 e.2.1
  | .ans e w => .ans e.1 (Answer.toBehaviour (ft := ts.get e.1) w)

/-- A move of a Wasm program as an event. -/
def moveEvent {X : WIface} : Move (ifaceSig X.imports) (ifaceSig X.exports) → WEvent X :=
  Sum.map evOf evOf

/-- The traces of a strategy over a scalar interface. -/
def playTraces {X : WIface} (σ : Strategy (ifaceSig X.imports) (ifaceSig X.exports)) :
    Set (List (WEvent X)) :=
  List.map moveEvent '' (σ : Set (List (Move (ifaceSig X.imports) (ifaceSig X.exports))))

/-- Prefixes of mapped lists are mapped prefixes. -/
theorem prefix_map_exists {α β : Type} (f : α → β) {s : List β} {p : List α}
    (h : s <+: p.map f) : ∃ p', p' <+: p ∧ p'.map f = s := by
  refine ⟨p.take s.length, List.take_prefix _ _, ?_⟩
  rw [List.map_take]
  exact (List.prefix_iff_eq_take.1 h).symm

/-- The traces of a strategy are good. -/
theorem playTraces_good {X : WIface} (σ : Strategy (ifaceSig X.imports) (ifaceSig X.exports)) :
    Good (playTraces σ) where
  nil_mem := ⟨[], σ.nil_mem, rfl⟩
  of_prefix := by
    rintro s t ⟨p, hp, rfl⟩ hs
    obtain ⟨p', hp', rfl⟩ := prefix_map_exists moveEvent hs
    exact ⟨p', σ.of_prefix hp hp', rfl⟩

/-- **The Wasm trace semantics at profile `P`.** -/
noncomputable abbrev wasmSem (P : Profile) : Semantics FnType (List Val) (Behaviour Val) where
  Prog := WasmProg
  traces p := playTraces (p.inst.strategy P p.store)
  good _ := playTraces_good _

/-- The divergence traces of a divergence-observing strategy: a divergent play followed by the
divergence of its pending export call. -/
def divTraces {X : WIface} (δ : DStrategy (ifaceSig X.imports) (ifaceSig X.exports)) :
    Set (List (WEvent X)) :=
  {t | ∃ s ∈ δ.div, ∃ f, Path .idle s (.run f) ∧
    t = s.map moveEvent ++ [Event.ret f.1 .diverges]}

/-- Finite traces together with divergence traces are good. -/
theorem divTraces_good {X : WIface} (δ : DStrategy (ifaceSig X.imports) (ifaceSig X.exports)) :
    Good (playTraces δ.toStrategy ∪ divTraces δ) where
  nil_mem := .inl (playTraces_good _).nil_mem
  of_prefix := by
    rintro s t (ht | ⟨u, hu, f, hf, rfl⟩) hs
    · exact .inl ((playTraces_good _).of_prefix ht hs)
    · rcases List.prefix_concat_iff.1 hs with rfl | hs'
      · exact .inr ⟨u, hu, f, hf, rfl⟩
      · exact .inl ((playTraces_good _).of_prefix ⟨u, δ.div_mem hu, rfl⟩ hs')

/-- **The divergence-observing Wasm trace semantics at profile `P`.** -/
noncomputable abbrev wasmDivSem (P : Profile) : Semantics FnType (List Val) (Behaviour Val) where
  Prog := WasmProg
  traces p := playTraces (p.inst.dstrategy P p.store).toStrategy ∪
    divTraces (p.inst.dstrategy P p.store)
  good _ := divTraces_good _

end Silmaril.Wasm.Spec
