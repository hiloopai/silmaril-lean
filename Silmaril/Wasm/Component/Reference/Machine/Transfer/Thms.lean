module

public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Transfer
public meta import Lean

/-!
# The machine over `E.withStore I` is simulated by the machine over `E`

For a store simulation `S : E.StoreSim I` (`Engine.Sim`):

* `step_sim`: a step of the machine over `E.withStore I` from `m'`, with label `l'`, is matched
  by a step of the machine over `E` from any configuration related to `m'`, with any label
  related to `l'`, and the targets are related. The dispatchers must be related
  (`DispatchRel`). The host-frame programs of host events are related to themselves
  (`rel_invokeProg`, `rel_tickProg`, `rel_cancelProg`, `rel_runProg`), so they need no
  hypothesis.
* `steps_sim`: the same for runs with related traces.
* `ProgRel.refl`: every program is related to itself; `ProgRel.bind`: the relation is closed
  under sequencing. `view_φ`: the core-store queries of `S.φ c` are those of `c`.
* For traces without `run` events, `labelOf` gives related labels (`forall₂_labelOf`) with the
  same observations (`traceObs_map_labelOf`).

`step_sim` and `steps_sim` are stated for related dispatchers and a related initial
configuration. For a concrete pair of definitions (a dispatcher or an instantiation program
over `E.withStore I` and over `E`), relatedness is `ProgRel.refl` once the two terms agree up to
unfolding, which holds for every REF program because programs reach the core store only
through the core operations (`Canon.Op`); see `Wasi.Accept.Ref.Transfer`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.Transfer

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
  _root_.Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) {σ : Type}

/-- The queries of a mapped core store are those of the store. -/
theorem view_φ {H : Type} (c : I.Store H) : E.view (S.φ c) = (E.withStore I).view c :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.view_φ S c

/-- **Every program is related to itself** (programs over `E.withStore I` and over `E` have the
same type). -/
theorem ProgRel.refl {α : Type} (p : P E σ α) : ProgRel S p p :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.ProgRel.refl S p

theorem ProgRel.bind {α β : Type} {p' : P (E.withStore I) σ α} {p : P E σ α}
    (h : ProgRel S p' p) {f' : α → P (E.withStore I) σ β} {f : α → P E σ β}
    (hf : ∀ a, ProgRel S (f' a) (f a)) : ProgRel S (p' >>= f') (p >>= f) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.ProgRel.bind S h hf

theorem rel_invokeProg (c : CallId) (f : FuncId) (args : List Val) :
    ProgRel S (invokeProg c f args : P (E.withStore I) σ (Ret (E.withStore I)))
      (invokeProg c f args) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.rel_invokeProg S c f args

theorem rel_tickProg (hr : HostReady σ) :
    ProgRel S (tickProg hr : P (E.withStore I) σ (Ret (E.withStore I))) (tickProg hr) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.rel_tickProg S hr

theorem rel_cancelProg (r : CancelRef) :
    ProgRel S (cancelProg r : P (E.withStore I) σ (Ret (E.withStore I))) (cancelProg r) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.rel_cancelProg S r

theorem rel_runProg {p' : P (E.withStore I) σ (Ret (E.withStore I))} {p : P E σ (Ret E)}
    (h : ProgRel S p' p) : ProgRel S (runProg p') (runProg p) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.rel_runProg S h

theorem forall₂_labelOf {tr : List (Label (E.withStore I) σ)}
    (h : ∀ p, Label.host (.run p) ∉ tr) : List.Forall₂ (LabelRel S) tr (tr.map labelOf) :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.forall₂_labelOf S h

theorem traceObs_map_labelOf (tr : List (Label (E.withStore I) σ)) :
    traceObs (tr.map labelOf : List (Label E σ)) = traceObs tr :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.traceObs_map_labelOf tr

theorem labelOf_host {l : Label (E.withStore I) σ} {ev : HostEvent E σ}
    (h : labelOf l = .host ev) : ∃ ev', l = .host ev' :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.labelOf_host h

variable {S} {prof : ProfileKind} {hr : HostReady σ}
  {d' : Call (E.withStore I) → P (E.withStore I) σ (Ret (E.withStore I))}
  {d : Call E → P E σ (Ret E)}

/-- **A step of `E.withStore I` is matched by a step of `E`** from a related configuration, with
any related label, given related dispatchers. -/
theorem step_sim (hd : DispatchRel S d' d) {m' n' : Config (E.withStore I) σ}
    {l' : Label (E.withStore I) σ} (h : Step prof hr d' m' l' n') {m : Config E σ}
    (hm : CfgRel S m' m) {l : Label E σ} (hl : LabelRel S l' l) :
    ∃ n, Step prof hr d m l n ∧ CfgRel S n' n :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.step_sim hd h hm hl

/-- **Runs of `E.withStore I` are matched by runs of `E`** with related traces. -/
theorem steps_sim (hd : DispatchRel S d' d) {m' n' : Config (E.withStore I) σ}
    {tr' : List (Label (E.withStore I) σ)} (h : Steps prof hr d' m' tr' n') {m : Config E σ}
    (hm : CfgRel S m' m) {tr : List (Label E σ)} (htr : List.Forall₂ (LabelRel S) tr' tr) :
    ∃ n, Steps prof hr d m tr n ∧ CfgRel S n' n :=
  Silmaril.Proofs.Wasm.Component.Reference.Transfer.steps_sim hd h hm htr

end Silmaril.Wasm.Component.Machine.Transfer

open Lean Elab Tactic Meta in
/-- Close `ProgRel S p' p` by `ProgRel.refl S p`, where `p'` is the same program definition as
`p` at the engine `E.withStore I`. The check that the two terms agree up to unfolding is left to
the kernel: the elaborator's unifier does not unfold the two applications of a program
definition at the two engines. -/
elab "prog_rel_refl" : tactic => do
  let g ← getMainGoal
  let ty ← whnfR (← g.getType)
  let args := ty.getAppArgs
  unless ty.isAppOf ``Silmaril.Wasm.Component.Machine.Transfer.ProgRel && args.size = 7 do
    throwError "prog_rel_refl: not a `ProgRel` goal"
  let e ← mkAppOptM ``Silmaril.Wasm.Component.Machine.Transfer.ProgRel.refl
    #[none, none, some args[3]!, none, none, some args[6]!]
  g.assign e
  replaceMainGoal []
