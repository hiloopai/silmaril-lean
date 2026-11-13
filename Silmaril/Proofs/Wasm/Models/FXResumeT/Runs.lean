module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.Typing

/-!
# Typed `resume`: the echo handler and bind-then-resume under `StepFXR`

The runs of `Silmaril.Wasm.Models.FXResume`, under the typed relation, when the arities hold:

* **`echo_runsR`**: with `ResumeArity f.module ct |vs|`, the echo handler reaches the captured
  context with the payload at its hole;
* `echo_hole_returnsR`: with an empty context it returns its Core payload;
* **`bind_resume_runsR`**: with `BindArity f.module ct ct' |vs|` and
  `ResumeArity f.module ct' |ws|`, binding `vs` and resuming with `ws` reaches the
  continuation's code with arguments `vs ++ ws`;
* **`resume_directR`**: under the same arities, resuming the original continuation with
  `vs ++ ws` is a typed step (`bind_resume_arity`) and reaches the same code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT
open Silmaril.Proofs.Wasm.Models.FXResume (getElem?_append_length set_append_length bound
  cvals_eq_result)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-! ## The echo handler -/

section Echo

variable {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
  {hs₀ : List OnClause} {hs : List HClause} {E : CtxV} {vs : List FVal} {x : TagIdx}

theorem echo_suspendR {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFXR P host fx ⟨s, K, f, echoSrc (vs.length + 1) ct hs₀ hs E vs x⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, [.label (vs.length + 1) [.fx (.resume ct hs₀)]
        (fvals [] ++ fvals (vs ++ [.cont K.length]) ++ [.core (.plain (.br l))] ++ [])]⟩ := by
  have h := StepFXR.ctxLabel (P := P) (host := host) (fx := fx) (n := vs.length + 1)
    (k := [.fx (.resume ct hs₀)]) (StepFXR.suspend (K := K) (vs := vs) ht hE hc)
  simpa [echoSrc, FVal.toAdmin] using h

theorem echo_branchR {K' : List (Option ContFX)} {j : Nat} {l : LabelIdx} (hl : l.toNat = 0) :
    StepFXR P host fx
      ⟨s, K', f, [.label (vs.length + 1) [.fx (.resume ct hs₀)]
        (fvals [] ++ fvals (vs ++ [.cont j]) ++ [.core (.plain (.br l))] ++ [])]⟩
      ⟨s, K', f, fvals vs ++ [.contRef j, .fx (.resume ct hs₀)]⟩ := by
  have h := StepFXR.brLabelZero (P := P) (host := host) (fx := fx) (s := s) (K := K') (f := f)
    (n := vs.length + 1) (k := [.fx (.resume ct hs₀)]) (vs' := [])
    (vs := vs ++ [.cont j]) (rest := []) hl (by simp)
  simpa [InstrFX.toAdmin, FVal.toAdmin] using h

theorem echo_resumeR {hs' : List HClause} (hr : hs₀.mapM (resolve s f) = some hs')
    (ha : ResumeArity f.module ct vs.length) :
    StepFXR P host fx
      ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .fx (.resume ct hs₀)]⟩
      ⟨s, K ++ [none], f, [.handler hs' (E.plug (fvals vs))]⟩ := by
  have h := StepFXR.resume (P := P) (host := host) (fx := fx) (vs := vs) (ct := ct)
    (getElem?_append_length K (some ⟨E.plug⟩)) hr ha
  rwa [set_append_length] at h

/-- **The echo handler under typed `resume`.** -/
theorem echo_runsR {ta : Nat} {ti : TagInst} {l : LabelIdx} {hs' : List HClause}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') (ha : ResumeArity f.module ct vs.length) :
    StepsFXR P host fx ⟨s, K, f, echoSrc (vs.length + 1) ct hs₀ hs E vs x⟩
      ⟨s, K ++ [none], f, [.handler hs' (E.plug (fvals vs))]⟩ :=
  ((Relation.ReflTransGen.single (echo_suspendR ht hE hc)).tail (echo_branchR hl)).tail
    (echo_resumeR hr ha)

end Echo

/-- With an empty context and a typed `resume`, the echo handler returns its payload. -/
theorem echo_hole_returnsR {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') (ha : ResumeArity f.module ct (liftV W).length) :
    .returns W ∈ behavioursFXR P host fx
      ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ := by
  have hrun := echo_runsR (P := P) (host := host) (fx := fx) (K := K) (E := .hole) ht
    (fun h => h) hc hl hr ha
  have hvals : StepFXR P host fx
      ⟨s, K ++ [none], f, [.handler hs' (CtxV.hole.plug (fvals (liftV W)))]⟩
      ⟨s, K ++ [none], f, fvals (liftV W)⟩ := StepFXR.handlerVals
  have hres : (⟨s, K ++ [none], f, fvals (liftV W)⟩ : ConfigFX H).code =
      (Result.values W).toAdmin.map AdminFX.core := by
    rw [← cvals_eq_result]; exact fvals_liftV W
  exact Or.inl ⟨_, .values W, hrun.tail hvals, hres, rfl⟩

/-! ## Bind, then resume -/

section Bind

variable {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} {C : ContFX}
  {ct ct' : TypeIdx} {hs : List OnClause} {ws vs : List FVal}

theorem bind_resume_bindR (hk : K[k]? = some (some C))
    (hb : BindArity f.module ct ct' vs.length) :
    StepFXR P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [some (bound C vs)], f,
        fvals ws ++ [.contRef K.length, .fx (.resume ct' hs)]⟩ := by
  have hstep : StepFXR P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
      ⟨s, K.set k none ++ [some (bound C vs)], f, [.contRef K.length]⟩ :=
    StepFXR.contBind hk hb
  have h := StepFXR.seq (vs := ws) (rest := [.fx (.resume ct' hs)]) hstep
    (Or.inr (List.cons_ne_nil _ _))
  simpa [bindResumeSrc] using h

theorem bind_resume_resumeR {K' : List (Option ContFX)} {hs' : List HClause}
    (hr : hs.mapM (resolve s f) = some hs') (ha : ResumeArity f.module ct' ws.length) :
    StepFXR P host fx ⟨s, K' ++ [some (bound C vs)], f,
        fvals ws ++ [.contRef K'.length, .fx (.resume ct' hs)]⟩
      ⟨s, K' ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have h := StepFXR.resume (P := P) (host := host) (fx := fx) (vs := ws) (ct := ct')
    (getElem?_append_length K' (some (bound C vs))) hr ha
  have hplug : (bound C vs).plug (fvals ws) = C.plug (fvals (vs ++ ws)) := by
    simp [bound, fvals]
  rw [set_append_length, hplug] at h
  exact h

/-- **Typed bind, then typed resume**: the run reaches `C` with arguments `vs ++ ws`. -/
theorem bind_resume_runsR {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' vs.length)
    (ha : ResumeArity f.module ct' ws.length) :
    StepsFXR P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have hlen : (K.set k none).length = K.length := List.length_set
  have h₂ := bind_resume_resumeR (P := P) (host := host) (fx := fx) (K' := K.set k none)
    (C := C) (vs := vs) (ws := ws) (ct' := ct') hr ha
  rw [hlen] at h₂
  exact (Relation.ReflTransGen.single (bind_resume_bindR hk hb)).tail h₂

/-- **The direct resume is typed under the same arities**, and reaches the same code. -/
theorem resume_directR {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') (hb : BindArity f.module ct ct' vs.length)
    (ha : ResumeArity f.module ct' ws.length) :
    StepFXR P host fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have hA : ResumeArity f.module ct (vs ++ ws).length := by
    rw [List.length_append]
    exact bind_resume_arity hb ha
  exact StepFXR.resume hk hr hA

end Bind

end Silmaril.Proofs.Wasm.Models.FXResumeT
