module

public import Silmaril.Proofs.Wasm.Models.FXBindT.Inv
public import Silmaril.Wasm.Models.FXBind.Thms

/-!
# Partial application under `StepFX'` and `StepFXT`: the runs of the source

The source `srcBind a ct ct' hs vs₂ vs₁` and its intermediate configurations `bsrc₁`, `bsrc₂`
are those of `Silmaril.Proofs.Wasm.Models.FXBind` (track fxlower, for `StepFX`). With
`S = vs₂ ++ vs₁`, `d` the type of `a` and no host calls:

* `bsrc_succ₁'`, `bsrc_succ₂'`, `bsrc_succ₃'` (`StepFX'`): the same successors as under
  `StepFX`: `cont.new`; `cont.bind` with every split `S = U₁ ++ U₂`; `resume` with every split
  `U₁ = X₁ ++ X₂`, reaching the call on `U₂ ++ X₂` under a handler frame after the values `X₁`;
* `bsrc_succ₁T`, `bsrc_succ₃T` (`StepFXT`): the same, through `stepFXT_incl`;
* **`bsrc_succ₂T`** (`StepFXT`): `cont.bind` binds a suffix `U₂` with
  `BindArity f.module ct ct' |U₂|` only;
* `bsrc_runsT` (`StepFXT`, any host): with that arity for `vs₁`, the source reaches the call on
  `vs₁ ++ vs₂` under the handler frame.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall onHandler)
open Silmaril.Proofs.Wasm.Models.FXLower (contOf kAfter underH underHW)
open Silmaril.Proofs.Wasm.Models.FXBind (bsrc₁ bsrc₂ kBind kRes kOne_get kBind_get plug_bindK)
open Silmaril.Proofs.Wasm.Models.FXVRuns (step_contNew' step_resume' fvals_liftV')
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

theorem srcBind_eq' (a : Nat) (ct ct' : TypeIdx) (hs : List OnClause) (vs₂ vs₁ : List Val) :
    srcBind a ct ct' hs vs₂ vs₁ = fvals (liftV (vs₂ ++ vs₁) ++ [.val (.ref (.func a))]) ++
      .fx (.contNew ct) :: [.fx (.contBind ct ct'), .fx (.resume ct' hs)] := by
  simp [srcBind, FVal.toAdmin, Val.toAdmin]

theorem liftV_eq_append {S : List Val} {V₁ V₂ : List FVal} (h : liftV S = V₁ ++ V₂) :
    ∃ U₁ U₂, S = U₁ ++ U₂ ∧ V₁ = liftV U₁ ∧ V₂ = liftV U₂ := by
  obtain ⟨U₁, U₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp h
  exact ⟨U₁, U₂, rfl, rfl, rfl⟩

/-- **The only successor of the source is `bsrc₁`** (`StepFX'`). -/
theorem bsrc_succ₁' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ y) :
    y = bsrc₁ s K f a fi.type ct ct' hs (vs₂ ++ vs₁) := by
  obtain ⟨V₀, r, hV, hy⟩ := step_contNew' h _ ct _ (srcBind_eq' a ct ct' hs vs₂ vs₁)
  obtain ⟨rfl, hr⟩ := List.append_inj' hV rfl
  have hr' : r = .func a := by
    simp only [List.cons.injEq, FVal.val.injEq, Val.ref.injEq, and_true] at hr
    exact hr.symm
  rcases hy with ⟨a', fi', ha, hf', rfl⟩ | ⟨hn, -⟩
  · have ha' : a' = a := by rw [hr'] at ha; exact (Ref.func.inj ha).symm
    have hfi : fi' = fi := by rw [ha'] at hf'; exact Option.some.inj (hf'.symm.trans hf)
    rw [ha', hfi]
    simp [bsrc₁]
  · exact absurd (hr'.symm.trans hn) (by simp)

/-- The code of `bsrc₁` with FX values. -/
theorem bsrc₁_code (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat)
    (d : Validation.DefType) (ct ct' : TypeIdx) (hs : List OnClause) (S : List Val) :
    (bsrc₁ s K f a d ct ct' hs S).code =
      fvals (liftV S) ++ .contRef K.length :: .fx (.contBind ct ct') :: [.fx (.resume ct' hs)] := by
  simp [bsrc₁]

/-- The configuration `cont.bind` reaches from `bsrc₁` when it binds `U₂`. -/
theorem bind_result_eq (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat)
    (d : Validation.DefType) (ct' : TypeIdx) (hs : List OnClause) (U₁ U₂ : List Val) :
    (⟨s, (K ++ [some (contOf a d)]).set K.length none ++
        [some ⟨fun c => (contOf a d).plug (fvals (liftV U₂) ++ c)⟩], f,
        fvals (liftV U₁) ++ .contRef (K ++ [some (contOf a d)]).length ::
          [.fx (.resume ct' hs)]⟩ : ConfigFX H) = bsrc₂ s K f a d ct' hs U₁ U₂ := by
  simp [bsrc₂, kBind, kAfter, bindK]

/-- **The successors of `bsrc₁` under `StepFX'`: `cont.bind` with every split.** -/
theorem bsrc_succ₂' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct ct' : TypeIdx} {hs : List OnClause} {S : List Val}
    {y : ConfigFX H} (h : StepFX' P noHost fx (bsrc₁ s K f a d ct ct' hs S) y) :
    ∃ U₁ U₂, S = U₁ ++ U₂ ∧ y = bsrc₂ s K f a d ct' hs U₁ U₂ := by
  obtain ⟨V₁, V₂, hV, -, hy⟩ := step_contBind' h _ _ _ _ _ (bsrc₁_code s K f a d ct ct' hs S)
  obtain ⟨U₁, U₂, rfl, rfl, rfl⟩ := liftV_eq_append hV
  rcases hy with ⟨C, hk, rfl⟩ | ⟨hk, -⟩
  · have hC : C = contOf a d := by
      have h1 := (kOne_get K a d).symm.trans hk
      simpa using h1.symm
    subst hC
    exact ⟨U₁, U₂, rfl, bind_result_eq s K f a d ct' hs U₁ U₂⟩
  · exact absurd ((kOne_get K a d).symm.trans hk) (by simp)

/-- **The successors of `bsrc₁` under `StepFXT`: `cont.bind` binds the typed arity.** -/
theorem bsrc_succ₂T {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct ct' : TypeIdx} {hs : List OnClause} {S : List Val}
    {y : ConfigFX H} (h : StepFXT P noHost fx (bsrc₁ s K f a d ct ct' hs S) y) :
    ∃ U₁ U₂, S = U₁ ++ U₂ ∧ BindArity f.module ct ct' U₂.length ∧
      y = bsrc₂ s K f a d ct' hs U₁ U₂ := by
  obtain ⟨V₁, V₂, hV, hA, hy⟩ := step_contBindT h _ _ _ _ _ (bsrc₁_code s K f a d ct ct' hs S)
  obtain ⟨U₁, U₂, rfl, rfl, rfl⟩ := liftV_eq_append hV
  rcases hy with ⟨C, hk, rfl⟩ | ⟨hk, -⟩
  · have hC : C = contOf a d := by
      have h1 := (kOne_get K a d).symm.trans hk
      simpa using h1.symm
    subst hC
    refine ⟨U₁, U₂, rfl, ?_, bind_result_eq s K f a d ct' hs U₁ U₂⟩
    simpa [liftV, bsrc₁] using hA
  · exact absurd ((kOne_get K a d).symm.trans hk) (by simp)

/-- **The successors of `bsrc₂` under `StepFX'`.** -/
theorem bsrc_succ₃' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct' : TypeIdx} {hs : List OnClause} {U₁ U₂ : List Val}
    {y : ConfigFX H} (h : StepFX' P noHost fx (bsrc₂ s K f a d ct' hs U₁ U₂) y) :
    ∃ hs' X₁ X₂, U₁ = X₁ ++ X₂ ∧
      y = underHW (kRes K a d U₂) hs' X₁ ⟨s, f, tgtCall a d (U₂ ++ X₂)⟩ := by
  obtain ⟨V₁, V₂, hV, hy⟩ := step_resume' h (liftV U₁) (K.length + 1) ct' hs []
    (by simp [bsrc₂])
  obtain ⟨X₁, X₂, rfl, rfl, rfl⟩ := liftV_eq_append hV
  rcases hy with ⟨C, hs', hk, -, rfl⟩ | ⟨hk, -⟩
  · have hC : C = bindK (contOf a d) U₂ := by
      have h1 := (kBind_get K a d U₂).symm.trans hk
      simpa using h1.symm
    subst hC
    refine ⟨hs', X₁, X₂, rfl, ?_⟩
    show _ = (⟨s, kRes K a d U₂, f,
      cvals X₁ ++ [.handler hs' ((tgtCall a d (U₂ ++ X₂)).map .core)]⟩ : ConfigFX H)
    rw [← plug_bindK, ← fvals_liftV', ← fvals_liftV']
    rfl
  · exact absurd ((kBind_get K a d U₂).symm.trans hk) (by simp)

/-- The only successor of the source under `StepFXT`. -/
theorem bsrc_succ₁T {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) {y : ConfigFX H}
    (h : StepFXT P noHost fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ y) :
    y = bsrc₁ s K f a fi.type ct ct' hs (vs₂ ++ vs₁) :=
  bsrc_succ₁' hf (stepFXT_incl h)

/-- The successors of `bsrc₂` under `StepFXT`. -/
theorem bsrc_succ₃T {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct' : TypeIdx} {hs : List OnClause} {U₁ U₂ : List Val}
    {y : ConfigFX H} (h : StepFXT P noHost fx (bsrc₂ s K f a d ct' hs U₁ U₂) y) :
    ∃ hs' X₁ X₂, U₁ = X₁ ++ X₂ ∧
      y = underHW (kRes K a d U₂) hs' X₁ ⟨s, f, tgtCall a d (U₂ ++ X₂)⟩ :=
  bsrc_succ₃' (stepFXT_incl h)

/-- **The typed source reaches the intended call** (any host, any FX table): `cont.bind` binds
`vs₁`, `resume` passes `vs₂`. -/
theorem bsrc_runsT {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {hs' : List HClause}
    {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hA : BindArity f.module ct ct' vs₁.length) :
    StepsFXT P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩
      (underH (kRes K a fi.type vs₁) hs' ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩) := by
  have h1 : StepFXT P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩
      (bsrc₁ s K f a fi.type ct ct' hs (vs₂ ++ vs₁)) := by
    have h := StepFXT.seq (vs := liftV (vs₂ ++ vs₁))
      (rest := [.fx (.contBind ct ct'), .fx (.resume ct' hs)])
      (StepFXT.contNew (P := P) (host := host) (fx := fx) (K := K) (f := f) (ct := ct) hf)
      (Or.inr (by simp))
    simpa [srcBind, bsrc₁, contOf, fvals_liftV'] using h
  have h2 : StepFXT P host fx (bsrc₁ s K f a fi.type ct ct' hs (vs₂ ++ vs₁))
      (bsrc₂ s K f a fi.type ct' hs vs₂ vs₁) := by
    have h := StepFXT.seq (vs := liftV vs₂) (rest := [.fx (.resume ct' hs)])
      (StepFXT.contBind (P := P) (host := host) (fx := fx) (s := s) (f := f) (vs := liftV vs₁)
        (ct := ct) (ct' := ct') (kOne_get K a fi.type) (by simpa [liftV] using hA))
      (Or.inr (by simp))
    simpa [bsrc₁, bsrc₂, kBind, kAfter, bindK, fvals_liftV'] using h
  have h3 : StepFXT P host fx (bsrc₂ s K f a fi.type ct' hs vs₂ vs₁)
      (underH (kRes K a fi.type vs₁) hs' ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩) := by
    have h := StepFXT.resume (P := P) (host := host) (fx := fx) (s := s) (f := f)
      (vs := liftV vs₂) (ct := ct') (kBind_get K a fi.type vs₁) hr
    unfold underH onHandler kRes
    rw [← plug_bindK, ← fvals_liftV']
    simpa [bsrc₂, fvals_liftV'] using h
  exact ((Relation.ReflTransGen.single h1).tail h2).tail h3

end Silmaril.Proofs.Wasm.Models.FXBindT
