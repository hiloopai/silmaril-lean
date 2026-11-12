module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.NoK
public import Silmaril.Proofs.Wasm.Models.FXVRuns.Stuck
public import Silmaril.Proofs.Wasm.Models.FXVRuns.AbortRuns

/-!
# Lowering `resume (cont.new (ref.func a))` to `call_ref`, under `StepFX'`

An earlier step proved `lower_correct` for `StepFX`. Its source inversions are specific to `StepFX`;
here they are re-proved for `StepFX'` with the FX-value decomposition `fnvF`:

* `fx_head_stuck`: code starting with an FX instruction does not step (no host calls);
* `step_contNew'`, `step_resume'`: inversions at `cont.new` and at `ref.cont; resume`;
* `src_succ₁'`, `src_succ₂'`: the successors of the source, and of its first step: the target
  under a handler frame after any prefix of the arguments (`underHW`);
* **`lower_complete'`**: every `StepFX'` behaviour of the source is a Core behaviour of the
  target; the last configurations have no continuations, so `behavioursFX'_noK` hands them to
  `StepFX` and `behaviours_underHW`;
* **`lower_correct'`**: the source's `StepFX'` behaviours are the target's Core behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FXLower (contOf kAfter plug_contOf underHW withVals
  withVals_tgtCall behaviours_underHW)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- **Code starting with an FX instruction does not step.** -/
theorem fx_head_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ i T, x.code ≠ .fx i :: T := by
  induction h with
  | core _ =>
    intro i T hc
    have hm : AdminFX.fx i ∈ _ := hc ▸ List.mem_cons_self
    simp at hm
  | seq h' _ ih =>
    intro i T hc
    rcases seq_head rfl hc with hes | ⟨es₁, hes⟩
    · exact no_step_nil' h' hes
    · exact ih i es₁ hes
  | invoke _ => exact fun i T => invoke_ne_head rfl
  | _ => intro i T hx; fnvF_absurd hx

/-! ## `cont.new` -/

/-- The outcomes of a step of `fvals V ++ cont.new :: T`. -/
def NewRes' (s : Store H) (K : List (Option ContFX)) (f : Frame) (V : List FVal)
    (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ V₀ r, V = V₀ ++ [.val (.ref r)] ∧
    ((∃ a fi, r = .func a ∧ s.funcs[a]? = some fi ∧
        y = ⟨s, K ++ [some (contOf a fi.type)], f, fvals V₀ ++ .contRef K.length :: T⟩) ∨
      (r = .null ∧ y = ⟨s, K, f, fvals V₀ ++ .core .trap :: T⟩))

theorem newRes'_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {V : List FVal} {T es' : List AdminFX} (vs : List FVal) (rest : List AdminFX)
    (h : NewRes' s K f V T ⟨s', K', f', es'⟩) :
    NewRes' s K f (vs ++ V) (T ++ rest) ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  obtain ⟨V₀, r, rfl, h⟩ := h
  refine ⟨vs ++ V₀, r, by simp, ?_⟩
  rcases h with ⟨a, fi, hr, hf, hy⟩ | ⟨hr, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨a, fi, hr, hf, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hr, by simp⟩

/-- The `cont.new` case of `step_contNew'`. -/
theorem contNew_base {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct₀ : TypeIdx} (hf : s.funcs[a]? = some fi) {V : List FVal}
    {ct : TypeIdx} {T : List AdminFX}
    (hx : [AdminFX.core (.ref (.func a)), .fx (.contNew ct₀)] = fvals V ++ .fx (.contNew ct) :: T) :
    NewRes' s K f V T ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)),
      .core (.callRefType fi.type)]⟩], f, [.contRef K.length]⟩ := by
  obtain ⟨hV, -, hT⟩ :=
    fvals_append_cons_inj (V₁ := [.val (.ref (.func a))]) (T₁ := []) hx rfl rfl
  exact ⟨[], .func a, hV.symm, Or.inl ⟨a, fi, rfl, hf, by rw [← hT]; rfl⟩⟩

/-- The `cont.new` on `ref.null` case of `step_contNew'`. -/
theorem contNewNull_base {s : Store H} {K : List (Option ContFX)} {f : Frame} {ct₀ : TypeIdx}
    {V : List FVal} {ct : TypeIdx} {T : List AdminFX}
    (hx : [AdminFX.core (.ref .null), .fx (.contNew ct₀)] = fvals V ++ .fx (.contNew ct) :: T) :
    NewRes' s K f V T ⟨s, K, f, [.core .trap]⟩ := by
  obtain ⟨hV, -, hT⟩ := fvals_append_cons_inj (V₁ := [.val (.ref .null)]) (T₁ := []) hx rfl rfl
  exact ⟨[], .null, hV.symm, Or.inr ⟨rfl, by rw [← hT]; rfl⟩⟩

/-- An `invoke` left-hand side is not values then an FX instruction. -/
theorem invoke_ne_fx {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) {V : List FVal}
    {i : FXInstr} {T : List AdminFX} :
    cvals vs ++ [.core (.ref (.func a)), .core c] ≠ fvals V ++ .fx i :: T := by
  intro hx
  rw [invoke_eq] at hx
  obtain ⟨-, he, -⟩ := fvals_append_cons_inj hx
    (by simp [Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc]) rfl
  cases he

/-- **Inversion at `cont.new`** (`StepFX'`). -/
theorem step_contNew' {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V ct T, x.code = fvals V ++ .fx (.contNew ct) :: T →
      NewRes' x.store x.conts x.frame V T y := by
  induction h with
  | core _ =>
    intro V ct T hc
    have hm : AdminFX.fx (.contNew ct) ∈ _ := hc ▸ List.mem_append_right _ List.mem_cons_self
    simp at hm
  | seq h _ ih =>
    intro V ct T hx
    rcases seq_splitF rfl hx with ⟨U, hU⟩ | ⟨V₂, T₁, rfl, hes, rfl⟩
    · exact (no_step_fvals' h U hU).elim
    · exact newRes'_seq _ _ (ih V₂ ct T₁ hes)
  | contNew hf => exact fun V ct T hx => contNew_base hf hx
  | contNewNull => exact fun V ct T hx => contNewNull_base hx
  | invoke hc => exact fun V ct T hx => (invoke_ne_fx hc hx).elim
  | _ => intro V ct T hx; fnvF_absurd hx

/-! ## `resume` -/

/-- The outcomes of a step of `fvals V ++ ref.cont n :: resume ct hs :: T`. -/
def ResumeRes' (s : Store H) (K : List (Option ContFX)) (f : Frame) (hs : List OnClause)
    (V : List FVal) (n : Nat) (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ V₁ V₂, V = V₁ ++ V₂ ∧
    ((∃ C hs', K[n]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
        y = ⟨s, K.set n none, f, fvals V₁ ++ .handler hs' (C.plug (fvals V₂)) :: T⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, fvals V₁ ++ .core .trap :: T⟩))

theorem resumeRes'_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {hs : List OnClause} {V : List FVal} {n : Nat} {T es' : List AdminFX} (vs : List FVal)
    (rest : List AdminFX) (h : ResumeRes' s K f hs V n T ⟨s', K', f', es'⟩) :
    ResumeRes' s K f hs (vs ++ V) n (T ++ rest) ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  obtain ⟨V₁, V₂, rfl, h⟩ := h
  refine ⟨vs ++ V₁, V₂, by simp, ?_⟩
  rcases h with ⟨C, hs', hk, hr, hy⟩ | ⟨hk, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨C, hs', hk, hr, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hk, by simp⟩

theorem resume_code_eq (V : List FVal) (n : Nat) (ct : TypeIdx) (hs : List OnClause)
    (T : List AdminFX) :
    fvals V ++ .contRef n :: .fx (.resume ct hs) :: T =
      fvals (V ++ [.cont n]) ++ .fx (.resume ct hs) :: T := by
  simp [FVal.toAdmin]

/-- The `resume` and `resumeUsed` cases: the operands are `V`, nothing follows. -/
theorem resume_inj' {vs V : List FVal} {k n : Nat} {ct ct' : TypeIdx} {hs hs₀ : List OnClause}
    {T : List AdminFX}
    (hx : fvals vs ++ [.contRef k, .fx (.resume ct' hs₀)] =
      fvals V ++ .contRef n :: .fx (.resume ct hs) :: T) :
    vs = V ∧ k = n ∧ ct' = ct ∧ hs₀ = hs ∧ T = [] := by
  have hx' : fvals (vs ++ [.cont k]) ++ AdminFX.fx (.resume ct' hs₀) :: [] =
      fvals (V ++ [.cont n]) ++ .fx (.resume ct hs) :: T := by
    simpa [FVal.toAdmin] using hx
  obtain ⟨hV, he, hT⟩ := fvals_append_cons_inj hx' rfl rfl
  obtain ⟨rfl, hk⟩ := List.append_inj' hV rfl
  simp only [List.cons.injEq, FVal.cont.injEq, and_true] at hk
  simp only [AdminFX.fx.injEq, FXInstr.resume.injEq] at he
  exact ⟨rfl, hk, he.1, he.2, hT.symm⟩

/-- The conclusion of `step_resume'`. -/
abbrev ResumeInv (x y : ConfigFX H) : Prop :=
  ∀ V n ct hs T, x.code = fvals V ++ .contRef n :: .fx (.resume ct hs) :: T →
    ResumeRes' x.store x.conts x.frame hs V n T y

/-- The `ctxt-instrs` case of `step_resume'`. -/
theorem resume_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX}
    (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : ResumeInv ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    ResumeInv ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro V n ct hs T hx
  have hx' : fvals vs ++ es ++ rest = fvals (V ++ [.cont n]) ++ .fx (.resume ct hs) :: T :=
    hx.trans (resume_code_eq V n ct hs T)
  rcases seq_splitF rfl hx' with ⟨U, hU⟩ | ⟨V₂, T₁, hV, hes, hT⟩
  · exact (no_step_fvals' h U hU).elim
  · have hne : V₂ ≠ [] := fun h0 => fx_head_stuck h _ T₁ (by rw [hes, h0]; rfl)
    obtain ⟨L, hV₂, hVL⟩ := suffix_concat hV hne
    have hes' : es = fvals L ++ .contRef n :: .fx (.resume ct hs) :: T₁ := by
      rw [hes, hV₂, resume_code_eq]
    have hres : ResumeRes' s K f hs (vs ++ L) n (T₁ ++ rest)
        ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := resumeRes'_seq _ _ (ih L n ct hs T₁ hes')
    rw [hVL, hT]
    exact hres

/-- **Inversion at `ref.cont; resume`** (`StepFX'`). -/
theorem step_resume' {x y : ConfigFX H} (h : StepFX' P noHost fx x y) : ResumeInv x y := by
  induction h with
  | core _ =>
    intro V n ct hs T hc
    have hm : AdminFX.contRef n ∈ _ := hc ▸ List.mem_append_right _ List.mem_cons_self
    simp at hm
  | seq h _ ih => exact resume_seq h ih
  | @resume s K f vs k C _ _ hs' hk hr =>
    intro V n ct hs T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj' hx
    exact ⟨[], vs, rfl, Or.inl ⟨C, hs', hk, hr, by simp⟩⟩
  | @resumeUsed s K f vs k _ _ hk =>
    intro V n ct hs T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj' hx
    exact ⟨[], vs, rfl, Or.inr ⟨hk, by simp⟩⟩
  | invoke hc =>
    exact fun V n ct hs T hx => (invoke_ne_fx hc (hx.trans (resume_code_eq V n ct hs T))).elim
  | _ => intro V n ct hs T hx; rw [resume_code_eq] at hx; fnvF_absurd hx

/-! ## The source -/

/-- The source after `cont.new`. -/
def src₁' (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat) (d : Validation.DefType)
    (ct : TypeIdx) (hs : List OnClause) (vs : List Val) : ConfigFX H :=
  ⟨s, K ++ [some (contOf a d)], f, fvals (liftV vs) ++ .contRef K.length :: [.fx (.resume ct hs)]⟩

theorem srcResume_eq' (a : Nat) (ct : TypeIdx) (hs : List OnClause) (vs : List Val) :
    srcResume a ct hs vs =
      fvals (liftV vs ++ [.val (.ref (.func a))]) ++ .fx (.contNew ct) :: [.fx (.resume ct hs)] := by
  simp [srcResume, FVal.toAdmin, Val.toAdmin]

/-- **The only successor of the source is `src₁'`.** -/
theorem src_succ₁' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) {y : ConfigFX H}
    (h : StepFX' P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ y) :
    y = src₁' s K f a fi.type ct hs vs := by
  obtain ⟨V₀, r, hV, hy⟩ := step_contNew' h _ ct _ (srcResume_eq' a ct hs vs)
  obtain ⟨rfl, hr⟩ := List.append_inj' hV rfl
  have hr' : r = .func a := by
    simp only [List.cons.injEq, FVal.val.injEq, Val.ref.injEq, and_true] at hr
    exact hr.symm
  rcases hy with ⟨a', fi', ha, hf', rfl⟩ | ⟨hn, -⟩
  · have ha' : a' = a := by rw [hr'] at ha; exact (Ref.func.inj ha).symm
    have hfi : fi' = fi := by rw [ha'] at hf'; exact Option.some.inj (hf'.symm.trans hf)
    rw [ha', hfi]
    rfl
  · exact absurd (hr'.symm.trans hn) (by simp)

/-- **The successors of `src₁'`**: the target under a handler frame, after a prefix of `vs`. -/
theorem src_succ₂' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    {y : ConfigFX H} (h : StepFX' P noHost noFX (src₁' s K f a d ct hs vs) y) :
    ∃ hs' W₁ W₂, vs = W₁ ++ W₂ ∧ y = underHW (kAfter K a d) hs' W₁ ⟨s, f, tgtCall a d W₂⟩ := by
  obtain ⟨V₁, V₂, hV, hy⟩ := step_resume' h (liftV vs) K.length ct hs [] rfl
  obtain ⟨W₁, W₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hV
  rcases hy with ⟨C, hs', hk, -, rfl⟩ | ⟨hk, -⟩
  · have hC : C = contOf a d := by
      have h1 : (K ++ [some (contOf a d)])[K.length]? = some (some C) := hk
      simpa using h1.symm
    subst hC
    refine ⟨hs', W₁, W₂, rfl, ?_⟩
    show _ = (⟨s, kAfter K a d, f, cvals W₁ ++ [.handler hs' ((tgtCall a d W₂).map .core)]⟩ :
      ConfigFX H)
    rw [← plug_contOf, ← fvals_liftV', ← fvals_liftV']
    rfl
  · have h1 : (K ++ [some (contOf a d)])[K.length]? = some none := hk
    simp at h1

/-- The configurations under the handler frame have no continuations. -/
theorem noKs_underHW (K : List (Option ContFX)) (hs : List HClause) (W : List Val)
    (c : Config H) : NoKs (underHW K hs W c).code := by
  show NoKs (cvals W ++ onHandler hs c.code)
  simp only [onHandler, noKs_append, noKs_cons, noK_handler, noKs_nil, and_true]
  exact ⟨noKs_cvals W, noKs_map_core _⟩

/-- **Completeness of the lowering under `StepFX'`** (no host calls, no FX functions). -/
theorem lower_complete' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX' P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ := by
  refine behavioursFX'_sub_of_succ
    (not_result_of_mem (a := .fx (.contNew ct)) (by simp [srcResume])
      (by simp [Silmaril.Proofs.Wasm.Models.FX.isCore])) fun y hy => ?_
  rw [src_succ₁' hf hy]
  refine behavioursFX'_sub_of_succ
    (not_result_of_mem (a := .contRef K.length) (by simp [src₁'])
      (by simp [Silmaril.Proofs.Wasm.Models.FX.isCore])) fun z hz => ?_
  obtain ⟨hs', W₁, W₂, rfl, rfl⟩ := src_succ₂' hz
  rw [behavioursFX'_noK (noKs_underHW _ _ _ _), ← withVals_tgtCall]
  exact behaviours_underHW _ _ _ _

/-- **Correctness of the lowering under `StepFX'`**: the source's `StepFX'` behaviours are the
target's Core behaviours (no host calls, no FX functions). -/
theorem lower_correct' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX' P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ := by
  refine Set.Subset.antisymm (lower_complete' hf) ?_
  rw [← Silmaril.Wasm.Models.FXLower.lower_correct (K := K) (ct := ct) hf hr]
  exact Silmaril.Wasm.Models.FXV.behavioursFX_incl _

end Silmaril.Proofs.Wasm.Models.FXVRuns
