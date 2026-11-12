module

public import Silmaril.Wasm.Institution.Games.Defs
public import Silmaril.Games.Inst.Defs
public import Silmaril.Games.DivLTS.Defs

@[expose] public section

/-!
# Reading Wasm observations off divergence- and instantiation-observing games

The bridge between the divergence-observing games (`Silmaril.Games.Div*`,
`Silmaril.Games.Inst`) and silmaril's Wasm observations, prepared for
comorphisms from the session and entry logics
(`Silmaril.Wasm.Institution.{Session,Entry}`) into a divergence-aware game logic.

* `behOf δ q`: the single-invocation behaviours of the question `q`, read off
  `δ : DStrategy E (exportSig X)`: the finite answers `b ≠ .diverges` of the
  two-move plays `[ask q, ans q b]`, and `.diverges` when `δ` may diverge
  right after `[ask q]`. For the reduction `wasmRed P host w` of an
  instantiated module this is exactly silmaril's `behaviours`, divergence
  included (`behOf_wasmRed` in `Thms`), the observation `instEntry` of the
  entry logics.
* `instObs δ`: the first observation of a session, read off a strategy with
  an instantiation phase: `[.returns []]` when instantiation may succeed,
  `[b]` when it may fail with `b`, `[.diverges]` when it may diverge.
* `wasmInst P host s xas m : InstSystem Sig.empty (exportSig Set.univ)
  (Behaviour Val)`: a Core module with its instantiation phase.
  Instantiation runs silmaril's `Instantiate` followed by Core `Step`s
  (segments and start function); it is ready when the code is empty,
  leaving the store and the module instance as persistent state, and fails
  with `r.toBehaviour` on any other result `r`. Export calls invoke the
  export against the persistent store and update it. For the empty script,
  `instObs` of its strategy is silmaril's `moduleObs` (`instObs_wasmInst`).

What is grounded and what is not is listed in `Thms`.
-/

namespace Silmaril.Wasm.Institution.DivGames

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Games Silmaril.Wasm.Institution.Games

/-- Single-invocation behaviours read off a divergence-observing strategy. -/
def behOf {E : Silmaril.Games.Sig.{0}} {X : Set String} (δ : DStrategy E (exportSig X))
    (q : (exportSig X).Op) :
    Set (Behaviour Val) :=
  {b | (b ≠ .diverges ∧ [.inr (.ask q), .inr (.ans q b)] ∈ δ.toStrategy) ∨
    (b = .diverges ∧ [.inr (.ask q)] ∈ δ.div)}

/-- The instantiation observation read off a strategy with an instantiation
phase. -/
def instObs {E F : Silmaril.Games.Sig.{0}} (δ : DStrategy E (F.withInst (Behaviour Val))) :
    Set (List (Behaviour Val)) :=
  {bs | (bs = [.returns []] ∧ δ.InstReady) ∨ (∃ b, bs = [b] ∧ δ.InstFails b) ∨
    (bs = [.diverges] ∧ δ.InstDiverges)}

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- A Core module with its instantiation phase, instantiated from store `s`
with imports `xas`; see the module documentation. -/
def wasmInst (s : Store H) (xas : List ExternAddr) (m : Module) :
    InstSystem Silmaril.Games.Sig.empty (exportSig Set.univ) (Behaviour Val) where
  IConf := Option (Config H × ModuleInst)
  State := Store H × ModuleInst
  Conf _ := Option (Config H × ModuleInst)
  istart := none
  istep c c' := (c = none ∧ ∃ d, Instantiate P host s m xas d ∧ c' = some (d, d.frame.module)) ∨
    ∃ d d' mi, c = some (d, mi) ∧ c' = some (d', mi) ∧ Step P host d d'
  icall _ e _ := PEmpty.elim e
  iready c st := ∃ d mi, c = some (d, mi) ∧ d.code = [] ∧ st = (d.store, mi)
  ifail c b := ∃ d mi, ∃ r : Result, c = some (d, mi) ∧ d.code = r.toAdmin ∧ r ≠ .values [] ∧
    b = r.toBehaviour
  start q st := (Binaryen.exportFunc? st.2 q.1.1).map fun a => (invoke st.1 a q.1.2, st.2)
  step c c' := ∃ d d' mi, c = some (d, mi) ∧ c' = some (d', mi) ∧ Step P host d d'
  call _ e _ := PEmpty.elim e
  done c b st := ∃ d mi, ∃ r : Result, c = some (d, mi) ∧ d.code = r.toAdmin ∧ b = r.toBehaviour ∧
    st = (d.store, mi)

end Silmaril.Wasm.Institution.DivGames
