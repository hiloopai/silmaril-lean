module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.Incl

/-!
# Inverting `resume` under `StepFXR` (no host calls)

A step of `fvals V ++ ref.cont n :: resume ct hs :: T` resumes (or traps on a consumed
continuation) with a split `V = V₁ ++ V₂`: `V₂` are the arguments, `V₁` stays on the stack.

* `step_resumeR`: under `StepFXR` the arguments have the typed arity,
  `ResumeArity f.module ct |V₂|`;
* `resumeArity_unique`: the typed arity is unique, so the split is unique
  (`stepR_resume_split`) and the step is deterministic (`stepR_resume_det`);
* **`stepR_resume_untyped_stuck`**: in a frame whose module has no types, `resume` does not
  step under `StepFXR`, while it does under `StepFXT` (`stepT_resume_untyped`): the typed rule
  rejects the untyped `resume` of `FXResume.resume_untyped`;
* **`stepT_resume_ambiguous`**: under `StepFXT` the split is not unique, `resume` with one
  operand has two different successors.

The proofs follow `step_resume'` (`Silmaril.Proofs.Wasm.Models.FXVRuns`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume Silmaril.Wasm.Models.FXResumeT
open Silmaril.Proofs.Wasm.Models.FXVRuns (seq_splitF no_step_fvals' fx_head_stuck suffix_concat
  resume_code_eq resume_inj' invoke_ne_fx)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The outcomes of a step at `ref.cont n; resume`, with the side condition `A` on the number
of arguments. -/
def ResumeResR (A : Nat → Prop) (s : Store H) (K : List (Option ContFX)) (f : Frame)
    (hs : List OnClause) (V : List FVal) (n : Nat) (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ V₁ V₂, V = V₁ ++ V₂ ∧ A V₂.length ∧
    ((∃ C hs', K[n]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
        y = ⟨s, K.set n none, f, fvals V₁ ++ .handler hs' (C.plug (fvals V₂)) :: T⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, fvals V₁ ++ .core .trap :: T⟩))

/-- The conclusion of `step_resumeR`. -/
abbrev ResumeInvR (x y : ConfigFX H) : Prop :=
  ∀ V n ct hs T, x.code = fvals V ++ .contRef n :: .fx (.resume ct hs) :: T →
    ResumeResR (ResumeArity x.frame.module ct) x.store x.conts x.frame hs V n T y

theorem resumeResR_seq {A : Nat → Prop} {s s' : Store H} {K K' : List (Option ContFX)}
    {f f' : Frame} {hs : List OnClause} {V : List FVal} {n : Nat} {T es' : List AdminFX}
    (vs : List FVal) (rest : List AdminFX) (h : ResumeResR A s K f hs V n T ⟨s', K', f', es'⟩) :
    ResumeResR A s K f hs (vs ++ V) n (T ++ rest) ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  obtain ⟨V₁, V₂, rfl, hA, h⟩ := h
  refine ⟨vs ++ V₁, V₂, by simp, hA, ?_⟩
  rcases h with ⟨C, hs', hk, hr, hy⟩ | ⟨hk, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨C, hs', hk, hr, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hk, by simp⟩

/-- The `ctxt-instrs` case of `step_resumeR`. -/
theorem resumeR_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX}
    (h : StepFXR P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : ResumeInvR ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    ResumeInvR ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro V n ct hs T hx
  have h' := stepFXT_incl (stepFXR_incl h)
  have hx' : fvals vs ++ es ++ rest = fvals (V ++ [.cont n]) ++ .fx (.resume ct hs) :: T :=
    hx.trans (resume_code_eq V n ct hs T)
  rcases seq_splitF rfl hx' with ⟨U, hU⟩ | ⟨V₂, T₁, hV, hes, hT⟩
  · exact (no_step_fvals' h' U hU).elim
  · have hne : V₂ ≠ [] := fun h0 => fx_head_stuck h' _ T₁ (by rw [hes, h0]; rfl)
    obtain ⟨L, hV₂, hVL⟩ := suffix_concat hV hne
    have hes' : es = fvals L ++ .contRef n :: .fx (.resume ct hs) :: T₁ := by
      rw [hes, hV₂, resume_code_eq]
    have hres := resumeResR_seq vs rest (ih L n ct hs T₁ hes')
    rw [hVL, hT]
    exact hres

/-- **Inversion at `ref.cont; resume`** (`StepFXR`): the arguments have the typed arity. -/
theorem step_resumeR {x y : ConfigFX H} (h : StepFXR P noHost fx x y) : ResumeInvR x y := by
  induction h with
  | core _ =>
    intro V n ct hs T hc
    have hm : AdminFX.contRef n ∈ _ := hc ▸ List.mem_append_right _ List.mem_cons_self
    simp at hm
  | seq h _ ih => exact resumeR_seq h ih
  | @resume s K f vs k C _ _ hs' hk hr ha =>
    intro V n ct hs T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj' hx
    exact ⟨[], vs, rfl, ha, Or.inl ⟨C, hs', hk, hr, by simp⟩⟩
  | @resumeUsed s K f vs k _ _ hk ha =>
    intro V n ct hs T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj' hx
    exact ⟨[], vs, rfl, ha, Or.inr ⟨hk, by simp⟩⟩
  | invoke hc =>
    exact fun V n ct hs T hx => (invoke_ne_fx hc (hx.trans (resume_code_eq V n ct hs T))).elim
  | _ => intro V n ct hs T hx; rw [resume_code_eq] at hx; fnvF_absurd hx

/-! ## Uniqueness of the typed split -/

/-- **The typed resume arity is unique.** -/
theorem resumeArity_unique {m : Silmaril.Wasm.Execution.Core.ModuleInst} {ct : TypeIdx}
    {n n' : Nat} (h : ResumeArity m ct n) (h' : ResumeArity m ct n') : n = n' := by
  obtain ⟨ps, hps, rfl⟩ := h
  obtain ⟨ps', hps', rfl⟩ := h'
  rw [hps] at hps'
  cases hps'
  rfl

/-- Under `StepFXR`, a `resume` with arity `j` takes exactly the last `j` operands. -/
theorem stepR_resume_split {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {V : List FVal} {n : Nat} {ct : TypeIdx} {hs : List OnClause} {T : List AdminFX}
    {j : Nat} {y : ConfigFX H} (hj : ResumeArity f.module ct j)
    (h : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y) :
    ResumeResR (· = j) s K f hs V n T y := by
  obtain ⟨V₁, V₂, hV, hA, hy⟩ := step_resumeR h V n ct hs T rfl
  exact ⟨V₁, V₂, hV, resumeArity_unique hA hj, hy⟩

/-- Two splits of the same list with suffixes of equal length agree. -/
theorem split_eq {V₁ V₂ W₁ W₂ : List FVal} (h : V₁ ++ V₂ = W₁ ++ W₂)
    (hl : V₂.length = W₂.length) : V₁ = W₁ ∧ V₂ = W₂ :=
  List.append_inj' h hl

/-- Determinism of the outcome for a fixed split. -/
theorem resumeRes_det {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List OnClause} {V₁ V₂ : List FVal} {n : Nat} {T : List AdminFX} {y y' : ConfigFX H}
    (h : (∃ C hs', K[n]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
        y = ⟨s, K.set n none, f, fvals V₁ ++ .handler hs' (C.plug (fvals V₂)) :: T⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, fvals V₁ ++ .core .trap :: T⟩))
    (h' : (∃ C hs', K[n]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
        y' = ⟨s, K.set n none, f, fvals V₁ ++ .handler hs' (C.plug (fvals V₂)) :: T⟩) ∨
      (K[n]? = some none ∧ y' = ⟨s, K, f, fvals V₁ ++ .core .trap :: T⟩)) :
    y = y' := by
  rcases h with ⟨C, hs', hk, hr, rfl⟩ | ⟨hk, rfl⟩ <;>
    rcases h' with ⟨C', hs'', hk', hr', rfl⟩ | ⟨hk', rfl⟩
  · rw [hk] at hk'
    rw [hr] at hr'
    cases hk'
    cases hr'
    rfl
  · rw [hk] at hk'
    cases hk'
  · rw [hk] at hk'
    cases hk'
  · rfl

/-- **Typed `resume` steps deterministically** (no host calls). -/
theorem stepR_resume_det {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {V : List FVal} {n : Nat} {ct : TypeIdx} {hs : List OnClause} {T : List AdminFX}
    {y y' : ConfigFX H}
    (h : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y)
    (h' : StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y') :
    y = y' := by
  obtain ⟨V₁, V₂, hV, hA, hy⟩ := step_resumeR h V n ct hs T rfl
  obtain ⟨W₁, W₂, hW, hA', hy'⟩ := step_resumeR h' V n ct hs T rfl
  have hlen : V₂.length = W₂.length := resumeArity_unique hA hA'
  obtain ⟨rfl, rfl⟩ := split_eq (hV.symm.trans hW) hlen
  exact resumeRes_det hy hy'

/-! ## The untyped `resume` is rejected -/

/-- **In a module without types, typed `resume` does not step.** -/
theorem stepR_resume_untyped_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {V : List FVal} {n : Nat} {ct : TypeIdx} {hs : List OnClause} {T : List AdminFX}
    (hm : f.module.types = []) (y : ConfigFX H) :
    ¬ StepFXR P noHost fx ⟨s, K, f, fvals V ++ .contRef n :: .fx (.resume ct hs) :: T⟩ y := by
  intro h
  obtain ⟨_, V₂, -, hA, -⟩ := step_resumeR h V n ct hs T rfl
  obtain ⟨ps, hps, -⟩ := hA
  rw [Silmaril.Proofs.Wasm.Models.FXResume.contParams?_nil hm] at hps
  cases hps

/-- Under `StepFXT` the same `resume` steps, whatever the module's types. -/
theorem stepT_resume_untyped {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {V : List FVal} {n : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} (hk : K[n]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs') :
    StepFXT P host fx ⟨s, K, f, fvals V ++ [.contRef n, .fx (.resume ct hs)]⟩
      ⟨s, K.set n none, f, [.handler hs' (C.plug (fvals V))]⟩ :=
  StepFXT.resume hk hr

/-- **Under `StepFXT` the split of `resume` is not unique**: with one operand `v`, `resume`
may take it or leave it. -/
theorem stepT_resume_ambiguous {host : HostSemantics H} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {v : FVal} {n : Nat} {C : ContFX} {ct : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} (hk : K[n]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    StepFXT P host fx ⟨s, K, f, fvals [v] ++ [.contRef n, .fx (.resume ct hs)]⟩
        ⟨s, K.set n none, f, [.handler hs' (C.plug (fvals [v]))]⟩ ∧
      StepFXT P host fx ⟨s, K, f, fvals [v] ++ [.contRef n, .fx (.resume ct hs)]⟩
        ⟨s, K.set n none, f, fvals [v] ++ [.handler hs' (C.plug (fvals []))]⟩ ∧
      (⟨s, K.set n none, f, [.handler hs' (C.plug (fvals [v]))]⟩ : ConfigFX H) ≠
        ⟨s, K.set n none, f, fvals [v] ++ [.handler hs' (C.plug (fvals []))]⟩ := by
  have h₀ : StepFXT P host fx ⟨s, K, f, fvals [] ++ [.contRef n, .fx (.resume ct hs)]⟩
      ⟨s, K.set n none, f, [.handler hs' (C.plug (fvals []))]⟩ := StepFXT.resume hk hr
  have h₁ := StepFXT.seq (vs := [v]) (rest := []) h₀ (Or.inl (List.cons_ne_nil _ _))
  refine ⟨StepFXT.resume hk hr, by simpa using h₁, ?_⟩
  intro heq
  have hc := congrArg (fun c : ConfigFX H => c.code.length) heq
  simp [fvals] at hc

end Silmaril.Proofs.Wasm.Models.FXResumeT
