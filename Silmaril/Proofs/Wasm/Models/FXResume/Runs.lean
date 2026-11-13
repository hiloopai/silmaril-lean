module

public import Silmaril.Wasm.Models.FXResume.Defs
public import Silmaril.Wasm.Models.FXV.Thms

/-!
# Untyped `resume`: runs of the echo handler and of bind-then-resume

* `echo_suspend`, `echo_branch`, `echo_resume`, **`echo_runs`**: the echo handler reaches the
  captured context `E` with the payload at its hole, under the resolved clauses `hs'`, with the
  continuation consumed (`K ++ [none]`);
* `consumed_resume_traps`: a consumed continuation traps when resumed again (one-shot);
* **`echo_hole_returns`**: with an empty context and Core payload `W`, the echo handler returns
  `W`, for every `$ct`;
* `contParams?_nil`, **`resume_untyped`**: when the module has no types, no `$ct` has a resume
  arity, and the echo handler still returns its payload: `StepFX'` does not type `resume`;
* `bind_resume_bind`, `bind_resume_resume`, **`bind_resume_runs`**: binding `vs` then resuming
  with `ws` reaches the continuation's code with arguments `vs ++ ws`, the code that resuming
  the original continuation with `vs ++ ws` reaches (`resume_direct`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResume

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-! ## The continuation store -/

theorem getElem?_append_length (K : List (Option ContFX)) (c : Option ContFX) :
    (K ++ [c])[K.length]? = some c := by
  simp

theorem set_append_length (K : List (Option ContFX)) (c c' : Option ContFX) :
    (K ++ [c]).set K.length c' = K ++ [c'] := by
  simp

theorem getElem?_set_self {K : List (Option ContFX)} {k : Nat} (hk : k < K.length) :
    (K.set k none)[k]? = some none := by
  simp [hk]

/-! ## The echo handler -/

section Echo

variable {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
  {hs₀ : List OnClause} {hs : List HClause} {E : CtxV} {vs : List FVal} {x : TagIdx}

/-- `suspend` branches to the label with the payload and the captured continuation. -/
theorem echo_suspend {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFX' P host fx ⟨s, K, f, echoSrc (vs.length + 1) ct hs₀ hs E vs x⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, [.label (vs.length + 1) [.fx (.resume ct hs₀)]
        (fvals [] ++ fvals (vs ++ [.cont K.length]) ++ [.core (.plain (.br l))] ++ [])]⟩ := by
  have h := StepFX'.ctxLabel (P := P) (host := host) (fx := fx) (n := vs.length + 1)
    (k := [.fx (.resume ct hs₀)]) (StepFX'.suspend (K := K) (vs := vs) ht hE hc)
  simpa [echoSrc, FVal.toAdmin] using h

/-- The branch leaves the payload and the continuation for the label's `resume`. -/
theorem echo_branch {K' : List (Option ContFX)} {j : Nat} {l : LabelIdx} (hl : l.toNat = 0) :
    StepFX' P host fx
      ⟨s, K', f, [.label (vs.length + 1) [.fx (.resume ct hs₀)]
        (fvals [] ++ fvals (vs ++ [.cont j]) ++ [.core (.plain (.br l))] ++ [])]⟩
      ⟨s, K', f, fvals vs ++ [.contRef j, .fx (.resume ct hs₀)]⟩ := by
  have h := StepFX'.brLabelZero (P := P) (host := host) (fx := fx) (s := s) (K := K') (f := f)
    (n := vs.length + 1) (k := [.fx (.resume ct hs₀)]) (vs' := [])
    (vs := vs ++ [.cont j]) (rest := []) hl (by simp)
  simpa [InstrFX.toAdmin, FVal.toAdmin] using h

/-- `resume` reinstates the captured context with the payload at its hole. -/
theorem echo_resume {hs' : List HClause} (hr : hs₀.mapM (resolve s f) = some hs') :
    StepFX' P host fx ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .fx (.resume ct hs₀)]⟩
      ⟨s, K ++ [none], f, [.handler hs' (E.plug (fvals vs))]⟩ := by
  have h := StepFX'.resume (P := P) (host := host) (fx := fx) (vs := vs) (ct := ct)
    (getElem?_append_length K (some ⟨E.plug⟩)) hr
  rwa [set_append_length] at h

/-- **The echo handler, run**: the captured context `E` gets the payload `vs` at its hole, under
the clauses `hs'` that the label's `resume` resolves, and the continuation is consumed. -/
theorem echo_runs {ta : Nat} {ti : TagInst} {l : LabelIdx} {hs' : List HClause}
    (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    StepsFX' P host fx ⟨s, K, f, echoSrc (vs.length + 1) ct hs₀ hs E vs x⟩
      ⟨s, K ++ [none], f, [.handler hs' (E.plug (fvals vs))]⟩ :=
  ((Relation.ReflTransGen.single (echo_suspend ht hE hc)).tail (echo_branch hl)).tail
    (echo_resume hr)

end Echo

/-- **One-shot**: a consumed continuation traps when it is resumed again. -/
theorem consumed_resume_traps {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat}
    (hk : k < K.length) {ws : List FVal} {ct : TypeIdx} {hs : List OnClause} :
    StepFX' P host fx ⟨s, K.set k none, f, fvals ws ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.core .trap]⟩ :=
  StepFX'.resumeUsed (getElem?_set_self hk)

/-- After the echo handler, its continuation is consumed. -/
theorem echo_consumed (K : List (Option ContFX)) : (K ++ [none]).set K.length none = K ++ [none] :=
  set_append_length K none none

/-! ## Behaviours -/

/-- Behaviours of a successor are behaviours. -/
theorem behavioursFX'_of_steps {c d : ConfigFX H} (h : StepsFX' P host fx c d) :
    behavioursFX' P host fx d ⊆ behavioursFX' P host fx c := by
  rintro b (⟨d', r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d', r, h.trans hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.of_steps h hdiv⟩

theorem cvals_eq_result (W : List Val) :
    cvals W = (Result.values W).toAdmin.map AdminFX.core := rfl

/-- **With an empty context the echo handler returns its payload**, whatever `$ct` says. -/
theorem echo_hole_returns {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    .returns W ∈ behavioursFX' P host fx
      ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ := by
  have hrun : StepsFX' P host fx
      ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩
      ⟨s, K ++ [none], f, [.handler hs' (CtxV.hole.plug (fvals (liftV W)))]⟩ :=
    echo_runs (E := .hole) ht (fun h => h) hc hl hr
  have hvals : StepFX' P host fx ⟨s, K ++ [none], f, [.handler hs' (CtxV.hole.plug (fvals (liftV W)))]⟩
      ⟨s, K ++ [none], f, fvals (liftV W)⟩ := StepFX'.handlerVals
  have hres : (⟨s, K ++ [none], f, fvals (liftV W)⟩ : ConfigFX H).code =
      (Result.values W).toAdmin.map AdminFX.core := by
    rw [← cvals_eq_result]; exact fvals_liftV W
  exact Or.inl ⟨_, .values W, hrun.tail hvals, hres, rfl⟩

/-- In a module without types, no continuation type resolves. -/
theorem contParams?_nil {m : ModuleInst} (hm : m.types = []) (ct : TypeIdx) :
    contParams? m ct = none := by
  simp [contParams?, hm]

/-- **`StepFX'` does not type `resume`**: in a frame whose module has no types, no `$ct` has a
resume arity, and the echo handler still returns its payload, of any length. -/
theorem resume_untyped {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx}
    {hs₀ : List OnClause} {hs hs' : List HClause} {W : List Val} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {l : LabelIdx} (hm : f.module.types = []) (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0)
    (hr : hs₀.mapM (resolve s f) = some hs') :
    (∀ k, ¬ ResumeArity f.module ct k) ∧
      .returns W ∈ behavioursFX' P host fx
        ⟨s, K, f, echoSrc ((liftV W).length + 1) ct hs₀ hs .hole (liftV W) x⟩ := by
  have hnone : contParams? f.module ct = none := contParams?_nil hm ct
  have hno : ∀ k, ¬ ResumeArity f.module ct k := by
    rintro k ⟨ps, hps, -⟩
    have hne : contParams? f.module ct ≠ some ps := by rw [hnone]; exact Option.some_ne_none ps ∘ Eq.symm
    exact hne hps
  exact ⟨hno, echo_hole_returns ht hc hl hr⟩

/-! ## Partial application, then resume -/

section Bind

variable {s : Store H} {K : List (Option ContFX)} {f : Frame} {k : Nat} {C : ContFX}
  {ct ct' : TypeIdx} {hs : List OnClause} {ws vs : List FVal}

/-- The continuation that `cont.bind` allocates. -/
def bound (C : ContFX) (vs : List FVal) : ContFX := ⟨fun c => C.plug (fvals vs ++ c)⟩

/-- `cont.bind` takes the values just below the reference. -/
theorem bind_resume_bind (hk : K[k]? = some (some C)) :
    StepFX' P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [some (bound C vs)], f,
        fvals ws ++ [.contRef K.length, .fx (.resume ct' hs)]⟩ := by
  have hb : StepFX' P host fx ⟨s, K, f, fvals vs ++ [.contRef k, .fx (.contBind ct ct')]⟩
      ⟨s, K.set k none ++ [some (bound C vs)], f, [.contRef K.length]⟩ := StepFX'.contBind hk
  by_cases hne : ws ≠ [] ∨ [AdminFX.fx (.resume ct' hs)] ≠ []
  · have h := StepFX'.seq (vs := ws) (rest := [.fx (.resume ct' hs)]) hb hne
    simpa [bindResumeSrc] using h
  · exact absurd (Or.inr (List.cons_ne_nil _ _)) hne

/-- The bound continuation, resumed with `ws`, runs `C` with `vs ++ ws`. -/
theorem bind_resume_resume {K' : List (Option ContFX)} {hs' : List HClause}
    (hr : hs.mapM (resolve s f) = some hs') :
    StepFX' P host fx ⟨s, K' ++ [some (bound C vs)], f,
        fvals ws ++ [.contRef K'.length, .fx (.resume ct' hs)]⟩
      ⟨s, K' ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have h := StepFX'.resume (P := P) (host := host) (fx := fx) (vs := ws) (ct := ct')
    (getElem?_append_length K' (some (bound C vs))) hr
  have hplug : (bound C vs).plug (fvals ws) = C.plug (fvals (vs ++ ws)) := by
    simp [bound, fvals]
  rw [set_append_length, hplug] at h
  exact h

/-- **Bind, then resume**: the run reaches `C` with arguments `vs ++ ws`, with both the original
and the bound continuation consumed. -/
theorem bind_resume_runs {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    StepsFX' P host fx ⟨s, K, f, bindResumeSrc ws vs k ct ct' hs⟩
      ⟨s, K.set k none ++ [none], f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ := by
  have hlen : (K.set k none).length = K.length := List.length_set
  have h₂ := bind_resume_resume (P := P) (host := host) (fx := fx) (K' := K.set k none)
    (C := C) (vs := vs) (ws := ws) (ct' := ct') hr
  rw [hlen] at h₂
  exact (Relation.ReflTransGen.single (bind_resume_bind hk)).tail h₂

/-- Resuming the original continuation with `vs ++ ws` reaches the same code. -/
theorem resume_direct {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    StepFX' P host fx ⟨s, K, f, fvals (vs ++ ws) ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals (vs ++ ws)))]⟩ :=
  StepFX'.resume hk hr

end Bind
