module

public import Silmaril.Proofs.Wasm.Models.FXResume.Runs

/-!
# Untyped `resume` beyond fresh continuations: statements

The lowering of `Silmaril.Wasm.Models.FXLower` resumes a fresh continuation of a Core function
(one-shot, and the body never suspends). Here `resume` runs on continuations that suspension and
partial application produce, under the corrected relation `StepFX'`:

* **`echo_runs`**: the echo handler (an `(on $x 0)` clause whose label code resumes the
  continuation it receives, with the payload) reaches the captured context `E` with the payload
  `vs` at its hole: `suspend $x` behaves as if it had returned its operands, under the handler
  clauses that the `resume` installs. The continuation is consumed (`K ++ [none]`);
* **`consumed_resume_traps`**: resuming a consumed continuation traps (one-shot);
* **`echo_hole_returns`**: with an empty context, the echo handler returns its Core payload `W`;
* **`resume_untyped`**: refutation of a typed reading of `StepFX'`. In a frame whose module has
  no types, no `$ct` has a resume arity (`ResumeArity`), and the echo handler still returns `W`,
  of any length. The typed proposal would reject that `resume`, so `StepFX'` (like `StepFX`) is
  an untyped semantics for `resume`. The restatement that holds is `echo_hole_returns`, for
  every `$ct`;
* **`bind_resume_runs`**, `resume_direct`: `cont.bind` with `vs` then `resume` with `ws` reaches
  the code that resuming the original continuation with `vs ++ ws` reaches; only the
  continuation store differs (both continuations are consumed).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXResume

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **The echo handler reinstates the captured context with the payload at its hole.** -/
theorem echo_runs {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {E : CtxV} {vs : List FVal} {x : TagIdx}
    {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    StepsFX' P host fx ⟨s, K, f, echoSrc (vs.length + 1) ct hs₀ hs E vs x⟩
      ⟨s, K ++ [none], f, [.handler hs' (E.plug (fvals vs))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.echo_runs ht hE hc hl hr

/-- **One-shot**: a consumed continuation traps when resumed again. -/
theorem consumed_resume_traps {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat}
    (hk : k < K.length) {ws : List FVal} {ct : TypeIdx} {hs : List OnClause} :
    StepFX' P host fx ⟨s, K.set k none, f, fvals ws ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.core .trap]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.consumed_resume_traps hk

/-- **With an empty context the echo handler returns its payload**, for every `$ct`. -/
theorem echo_hole_returns {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    .returns W ∈ behavioursFX' P host fx
      ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.echo_hole_returns ht hc hl hr

/-- **`StepFX'` does not type `resume`** (refutation of a typed reading): no `$ct` resolves, so
no resume arity holds, and the echo handler still returns its payload. -/
theorem resume_untyped {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (hm : f.module.types = []) (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    (∀ k, ¬ ResumeArity f.module ct k) ∧
      .returns W ∈ behavioursFX' P host fx
        ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.resume_untyped hm ht hc hl hr

/-- **Bind, then resume, is resume with the concatenated arguments.** -/
theorem bind_resume_runs {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat}
    {C : ContFX} {ct ct' : TypeIdx} {hs : List OnClause} {hs' : List HClause}
    {ws vs : List FVal} (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
    StepsFX' P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.bind_resume_runs hk hr

/-- Resuming the original continuation with `vs ++ ws` reaches the same code. -/
theorem resume_direct {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {ws vs : List FVal}
    (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
    StepFX' P host fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXResume.resume_direct hk hr

/--
info: 'Silmaril.Wasm.Models.FXResume.resume_untyped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms resume_untyped

/--
info: 'Silmaril.Wasm.Models.FXResume.bind_resume_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms bind_resume_runs

end Silmaril.Wasm.Models.FXResume
