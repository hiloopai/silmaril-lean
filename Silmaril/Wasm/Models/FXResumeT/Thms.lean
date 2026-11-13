module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.KBeh

/-!
# Typed `resume` and an FX typing judgement: statements

`StepFXR` (`Defs`) is `StepFXT` with the `resume` rules typed by `ResumeArity`; `TypedFX` is a
typing judgement for straight-line FX code (Core instructions by a parameter, `cont.new`,
`cont.bind`, `resume`).

* **Relations.** `behavioursFXR_incl`: `StepFXR ⊆ StepFXT` on behaviours;
  `behavioursFXR_noK`: on code without continuations `StepFXR` has the `StepFX` behaviours.
* **Inversion and determinism.** `step_resumeR`: a `StepFXR` step at `ref.cont; resume` takes
  arguments of the typed arity; `stepR_resume_det`: so it is deterministic (no host calls).
  `stepT_resume_ambiguous`: under `StepFXT` it is not (two successors with one operand).
* **Refutation of the untyped reading, restated.** `stepR_resume_untyped_stuck`: in a module
  without types, `resume` does not step under `StepFXR`; under `StepFXT` it does
  (`stepT_resume_untyped`). This is `FXResume.resume_untyped` from the typed side.
* **Typing.** `typedFX_resume_inv`, `typedFX_bind_inv`; the judgement gives the arities
  (`resumeArity_of_contType`, `bindArity_of_contType`); `bind_resume_arity`;
  **`typed_resume_progress`** and **`typed_resume_unique`**: a typed stack at `resume` with a
  live continuation steps, and only by resuming with the typed number of arguments.
* **Typed runs.** `echo_runsR`, `echo_hole_returnsR`, **`bind_resume_runsR`**,
  **`resume_directR`**: the `FXResume` runs hold under `StepFXR` when the arities hold.
* **The simulation that ignores consumed slots.** `sim_behaviours`: a store relation
  `KRel ρ B` (slots in `B` ignored, the others renamed by `ρ`, code avoiding `B`) keeps
  `StepFXR` behaviours. `post_eq`: one extra consumed slot at the end of the store does not
  change behaviours, for natural continuations (`ContNat`) and code over existing slots.
* **Bind-then-resume, behaviour level.** **`bind_resume_eq`**: under `StepFXR` (no host
  calls), binding `vs` then resuming with `ws` has exactly the behaviours of resuming the
  original continuation with `vs ++ ws`; `bind_resume_eq_call` instantiates the hypotheses for a
  `cont.new` continuation and Core arguments.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Proofs.Wasm.Models.FXVRuns (NoKs)
open Silmaril.Proofs.Wasm.Models.FXResumeT (KRel avL rnL img ContNat callCont)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- **Every `StepFXR` behaviour is a `StepFXT` behaviour.** -/
theorem behavioursFXR_incl {host : HostSemantics H} (x : ConfigFX H) :
    behavioursFXR P host fx x ⊆ behavioursFXT P host fx x :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.behavioursFXR_incl x

/-- **On code without continuations `StepFXR` has the `StepFX` behaviours.** -/
theorem behavioursFXR_noK {host : HostSemantics H} {x : ConfigFX H} (hx : NoKs x.code) :
    behavioursFXR P host noFX x = behavioursFX P host noFX x :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.behavioursFXR_noK hx

/-- **Typed `resume` steps deterministically** (no host calls). -/
theorem stepR_resume_det {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {V : List FVal} {n : Nat} {ct : TypeIdx} {hs : List OnClause} {T : List AdminFX}
    {y y' : ConfigFX H}
    (h : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y)
    (h' : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y') :
    y = y' :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.stepR_resume_det h h'

/-- **Untyped `resume` under `StepFXT` is ambiguous**: two different successors. -/
theorem stepT_resume_ambiguous {host : HostSemantics H} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {v : FVal} {n : Nat} {C : ContFX} {ct : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} (hk : K[n]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    StepFXT P host fx ⟨s, K, f, fvals [v] ++ [.contRef n, .fx (.resume ct hs)]⟩
        ⟨s, K.set n none, f, [.handler hs' (C.plug (fvals [v]))]⟩ ∧
      StepFXT P host fx ⟨s, K, f, fvals [v] ++ [.contRef n, .fx (.resume ct hs)]⟩
        ⟨s, K.set n none, f, fvals [v] ++ [.handler hs' (C.plug (fvals []))]⟩ ∧
      (⟨s, K.set n none, f, [.handler hs' (C.plug (fvals [v]))]⟩ : ConfigFX H) ≠
        ⟨s, K.set n none, f, fvals [v] ++ [.handler hs' (C.plug (fvals []))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.stepT_resume_ambiguous hk hr

/-- **Typed `resume` rejects the untyped one**: in a module without types it does not step. -/
theorem stepR_resume_untyped_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {V : List FVal} {n : Nat} {ct : TypeIdx} {hs : List OnClause} {T : List AdminFX}
    (hm : f.module.types = []) (y : ConfigFX H) :
    ¬ StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.stepR_resume_untyped_stuck hm y

/-- **Bind `n`, then resume with `j`, is resume with `n + j`.** -/
theorem bind_resume_arity {m : ModuleInst} {ct ct' : TypeIdx} {n j : Nat}
    (hb : BindArity m ct ct' n) (hr : ResumeArity m ct' j) : ResumeArity m ct (n + j) :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.bind_resume_arity hb hr

/-- The judgement's types give `StepFXR`'s resume arity. -/
theorem resumeArity_of_contType {m : ModuleInst} {ct : TypeIdx} {ps rs : List CValType}
    (h : contType? m ct = some (ps, rs)) : ResumeArity m ct ps.length :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.resumeArity_of_contType h

variable {core : Instr → List CValType → List CValType → Prop}
  {VT : Val → CValType → Prop} {KT : Nat → TypeIdx → Prop}

/-- **Progress of typed `resume`.** -/
theorem typed_resume_progress {host : HostSemantics H} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {t₁ t₂ : List FTy} {V : List FVal}
    (h : TypedFX core f.module [.fx (.resume ct hs)] t₁ t₂)
    (hV : List.Forall₂ (FValTy VT KT) V t₁) (hlive : ∀ k, KT k ct → ∃ C, K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    ∃ V₀ V₂ k, ∃ C : ContFX, V = V₀ ++ V₂ ++ [.cont k] ∧ ResumeArity f.module ct V₂.length ∧
      StepFXR P host fx ⟨s, K, f, fvals V ++ [.fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, fvals V₀ ++ [.handler hs' (C.plug (fvals V₂))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.typed_resume_progress h hV hlive hr

/-- **Typed `resume` has one successor** (no host calls). -/
theorem typed_resume_unique {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {ct : TypeIdx} {hs : List OnClause} {t₁ t₂ : List FTy} {V : List FVal} {y : ConfigFX H}
    (h : TypedFX core f.module [.fx (.resume ct hs)] t₁ t₂)
    (hV : List.Forall₂ (FValTy VT KT) V t₁)
    (hy : StepFXR P noHost fx ⟨s, K, f, fvals V ++ [.fx (.resume ct hs)]⟩ y) :
    ∃ V₀ V₂ k, V = V₀ ++ V₂ ++ [.cont k] ∧
      ((∃ C hs', K[k]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
          y = ⟨s, K.set k none, f, fvals V₀ ++ [.handler hs' (C.plug (fvals V₂))]⟩) ∨
        (K[k]? = some none ∧ y = ⟨s, K, f, fvals V₀ ++ [.core .trap]⟩)) :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.typed_resume_unique h hV hy

/-- **Typed bind, then typed resume, reaches `C` with `vs ++ ws`.** -/
theorem bind_resume_runsR {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {k : Nat} {C : ContFX} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {ws vs : List FVal} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' vs.length)
    (ha : ResumeArity f.module ct' ws.length) :
    StepsFXR P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.bind_resume_runsR hk hr hb ha

/-- **The direct resume is typed under the same arities.** -/
theorem resume_directR {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {k : Nat} {C : ContFX} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {ws vs : List FVal} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' vs.length)
    (ha : ResumeArity f.module ct' ws.length) :
    StepFXR P host fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.resume_directR hk hr hb ha

/-- With an empty context and a typed `resume`, the echo handler returns its payload. -/
theorem echo_hole_returnsR {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {ct : TypeIdx} {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val}
    {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') (ha : ResumeArity f.module ct (liftV W).length) :
    .returns W ∈ behavioursFXR P host fx
      ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.echo_hole_returnsR ht hc hl hr ha

/-- info: 'Silmaril.Wasm.Models.FXResumeT.typed_resume_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typed_resume_unique

/-- info: 'Silmaril.Wasm.Models.FXResumeT.stepR_resume_untyped_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepR_resume_untyped_stuck

/-- **The simulation that ignores consumed slots keeps behaviours.** -/
theorem sim_behaviours {host : HostSemantics H} {ρ : Nat → Nat} {B : Nat → Prop}
    {x : ConfigFX H} {K₂ : List (Option ContFX)} (hK : KRel ρ B x.conts K₂) (hx : avL B x.code) :
    behavioursFXR P host fx x ⊆ behavioursFXR P host fx (img ρ x K₂) :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.sim_behaviours hK hx

/-- **An extra consumed slot at the end of the store does not change behaviours.** -/
theorem post_eq {host : HostSemantics H} {K : List (Option ContFX)} {s : Store H} {f : Frame}
    {c : List AdminFX}
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C)
    (hc : avL (fun i => K.length ≤ i) c) :
    behavioursFXR P host fx ⟨s, K ++ [none], f, c⟩ = behavioursFXR P host fx ⟨s, K, f, c⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.post_eq hK hc

/-- **Bind-then-resume has exactly the behaviours of the direct resume** (`StepFXR`). -/
theorem bind_resume_eq {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat}
    {C : ContFX} {ct ct' : TypeIdx} {hs : List OnClause} {hs' : List HClause}
    {ws vs : List FVal} (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (hb : BindArity f.module ct ct' vs.length) (ha : ResumeArity f.module ct' ws.length)
    (hK : ∀ (i : Nat) (C : ContFX), K[i]? = some (some C) → ContNat K.length C)
    (hV : avL (fun i => K.length ≤ i) (fvals (vs ++ ws))) :
    behavioursFXR P noHost fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩ =
      behavioursFXR P noHost fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.bind_resume_eq hk hr hb ha hK hV

/-- The hypotheses of `bind_resume_eq` hold for a `cont.new` continuation and Core
arguments. -/
theorem bind_resume_eq_call {s : Store H} {f : Frame} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {a : Nat} {t : DefType} {Vs Ws : List Val}
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' (liftV Vs).length)
    (ha : ResumeArity f.module ct' (liftV Ws).length) :
    behavioursFXR P noHost fx
        ⟨s, [some (callCont a t)], f, bindResumeSrc (liftV Ws) (liftV Vs) 0 ct ct' hs⟩ =
      behavioursFXR P noHost fx
        ⟨s, [some (callCont a t)], f,
          fvals (liftV Vs ++ liftV Ws) ++ [.contRef 0, .fx (.resume ct hs)]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResumeT.bind_resume_eq_call hr hb ha

/-- info: 'Silmaril.Wasm.Models.FXResumeT.bind_resume_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_resume_eq

/-- info: 'Silmaril.Wasm.Models.FXResumeT.bind_resume_eq_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bind_resume_eq_call

end Silmaril.Wasm.Models.FXResumeT
