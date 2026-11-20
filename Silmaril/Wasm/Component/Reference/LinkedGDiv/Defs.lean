module

public import Silmaril.Wasm.Component.Reference.LinkedGInst.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Defs
public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs

/-!
# Divergence through an abstract exporter: definitions

**Scope.** The exporter interface `ExpSpec` of `LinkedG` with its divergence specification
`ExpSpec.DivStep` (a call from state `s` on question `q` never answers), on the IR side
(`Comp.denUD (impSemD P)`) and on the reference machine (`Machine.Step` over `core3P P` under
`linkHost impl`, the data `ExpSpec.RefData` of `LinkedGRef`).

## The IR law

`ExpSpec.AdeqD P e`: after a session of typed rounds `L` from the initial state, a typed question
`q` is an IR divergence of `e.comp.denUD (impSemD P)` exactly when some session of `L` reaches a
state from which `q` diverges (`DivStep`). The session and the divergence are read **along one
run** (one existential state), so no determinism is needed.

## R7: the exporter's activation diverges

`ExpSpec.RefData.Div` (R7), in the frames of R2/R3 (from `Hold pl s S F`, the core activation
of export `w` on `vs` started by `startCfg`, on a thread of the export's instance, in any
frame):

* **forward**: a `DivStep` from `s` on `(w, vals vs)` makes the machine diverge from `startCfg`
  (`Machine.Diverges`: an infinite run without host events);
* **backward**: if the machine diverges from `startCfg`, then the call diverges (`DivStep`), or
  the run passes, without host events, through a **return** of R2 (`EndsT` with a non-empty
  control chain) for some `Step` of the specification, and the machine diverges from there
  (the divergence is the caller's, after the call returned).

R7 cannot be an iff between `DivStep` and divergence from `startCfg`: the caller's continuation
`K` may diverge after a returning call. The backward half therefore splits a divergence at the
first return of the exporter's activation, as R3 splits a finite run.

`ExpSpec.RefAdeqUXD P e`: data meeting `RefAdeqUX` (R1, R2, R3 as `BwdF`, R4 as `InitUX`, R5,
R6) and R7.

## The reference divergences of a linked component

`LinkedG.RefSessQuiet`, `LinkedG.refDivs`: `Linked2.RefSessQuiet`/`Linked2.refDivs` for
`LinkedG.toRef`: after instantiating `lg.toRef`, the resumable session of `calls` has outcomes
`outs`, and then the call of export `j` of the importer on `vs` diverges on the reference machine
(`SessDiv`). The specification side is `LinkedG.sessDivs` (`LinkedG.Defs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## The IR law -/

/-- A typed question: an export in range, on values of the export's parameter types. -/
def ExpSpec.TypedQ (e : ExpSpec) (q : sigU.Op) : Prop :=
  ∃ (w : Fin e.comp.exports.length) (ws : List IVal), q = (w.val, .vals ws) ∧
    ValTy.checkList e.comp.exports[w].ty.params ws = true

/-- **The IR divergence law of an exporter**: after typed complete rounds `L`, a typed question
`q` is a divergence of `e.comp.denUD (impSemD P)` iff a session of `L` from the initial state
reaches a state from which `q` diverges. -/
def ExpSpec.AdeqD (P : Profile) (e : ExpSpec) : Prop :=
  ∀ (L : List URound) (q : sigU.Op), (∀ r ∈ L, e.Typed r) → e.TypedQ q →
    (uMoves L ++ [.inr (.ask q)] ∈ (e.comp.denUD (impSemD P)).div ↔
      ∃ s, e.Run P e.init L s ∧ e.DivStep P s q)

/-! ## R7 -/

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **R7: the exporter's core activation diverges**, in the frames of R2/R3: forward, a
`DivStep` makes the machine diverge from `startCfg`; backward, a divergence from `startCfg` is a
`DivStep`, or passes without host events through a return of R2 (`EndsT`, non-empty control
chain) for some `Step`, the machine diverging from there. -/
def Div : Prop :=
  ∀ (pl : d.Pl) (s : e.St) (w : Nat) (vs : List IVal) (x : Export),
    e.comp.exports[w]? = some x → ValTy.checkList x.ty.params vs = true →
    ∀ (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
    ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
      (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
      (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P)))
      (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
      M.ref = S → S.lockdown = false → instOfThread? S.toCStore th = some ⟨d.inst pl w⟩ →
      (e.DivStep P s (w, .vals vs) →
        Machine.Diverges prof (linkHost impl).hr (linkHost impl).dispatch
          (d.startCfg pl w x vs M th K segs rest)) ∧
      (Machine.Diverges prof (linkHost impl).hr (linkHost impl).dispatch
          (d.startCfg pl w x vs M th K segs rest) →
        e.DivStep P s (w, .vals vs) ∨
        ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ) (R : Option Payload)
          (s' : e.St),
          Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
            (d.startCfg pl w x vs M th K segs rest) tr m ∧ (∀ ev, Label.host ev ∉ tr) ∧
          e.Step P s ⟨(w, .vals vs), R⟩ s' ∧ d.EndsT pl x S F M th K segs rest R s' m ∧
          m.ctl ≠ [] ∧ Machine.Diverges prof (linkHost impl).hr (linkHost impl).dispatch m)

end ExpSpec.RefData

/-- **The reference interface of an exporter with divergence**: `RefAdeqUX` (R1, R2, R3 as
`BwdF`, R4 as `InitUX`, R5, R6) and R7, for the same data. -/
def ExpSpec.RefAdeqUXD (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdF ∧ d.InitUX ∧ d.Resume ∧ d.Bounded ∧ d.Div

/-! ## The reference divergences of a linked component -/

/-- **Quiescent divergence of a linked session** (`Linked2.RefSessQuiet` for `LinkedG.toRef`):
after instantiating `lg.toRef` under `linkHost impl` from `h₀`, the resumable session of `calls`
has the outcomes `outs`, and then the call of export `j` of the importer on `vs` diverges on the
reference machine. -/
def LinkedG.RefSessQuiet (P : Profile) (prof : ProfileKind) (lg : LinkedG) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) (outs : List (Option (List IVal)))
    (j : Fin lg.imp.exports.length) (vs : List IVal) : Prop :=
  ∃ m₀ inst es fs f,
    InstResult.instance m₀ inst es ∈
      instBehaviours prof (linkHost impl) (initConfig h₀) lg.toRef [] ∧
    (calls.map fun q => (lg.imp.exports[q.1].name, q.2.map toRefVal)).mapM
      (fun q => es.lookup q.1) = some fs ∧
    es.lookup lg.imp.exports[j].name = some f ∧
    SessDiv prof (linkHost impl) m₀ 0 (fs.zip (calls.map fun q => q.2.map toRefVal))
      (refOuts outs) f (vs.map toRefVal)

/-- **The diverging session calls of a linked component on the reference machine**: the outcomes
after which the call of export `j` on `vs` diverges (`LinkedG.RefSessQuiet`). -/
def LinkedG.refDivs (P : Profile) (prof : ProfileKind) (lg : LinkedG) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) (j : Fin lg.imp.exports.length)
    (vs : List IVal) : Set (List (Option (List IVal))) :=
  {outs | LinkedG.RefSessQuiet P prof lg impl h₀ calls outs j vs}

end Silmaril.Wasm.Component.Reference
