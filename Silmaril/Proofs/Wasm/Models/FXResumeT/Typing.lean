module

public import Silmaril.Proofs.Wasm.Models.FXResumeT.Inv

/-!
# The FX typing judgement: arities, progress and determinism of typed `resume`

* `typedFX_nil`: the empty sequence has type `t → t`;
* `typedFX_resume_inv`, `typedFX_bind_inv`: inversion of the judgement at a single `resume` or
  `cont.bind`: the operands are a stack prefix, the parameters of `$ct` and a continuation of
  type `$ct`;
* `resumeArity_of_contType`, `bindArity_of_contType`: the judgement's types give the arities
  of `StepFXR` (`ResumeArity`) and `StepFXT` (`BindArity`);
* **`bind_resume_arity`**: binding `n` values to `$ct` at `$ct'`, then resuming with the `j`
  parameters of `$ct'`, resumes `$ct` with `n + j` values;
* **`typed_resume_split`**: a stack of values typed at the judgement's input splits as
  `V₀ ++ V₂ ++ [cont k]` with `|V₂|` the typed arity;
* **`typed_resume_progress`**: such a stack, with a live continuation in slot `k`, steps under
  `StepFXR` by resuming with exactly `V₂`;
* **`typed_resume_unique`**: and every `StepFXR` step from it (no host calls) is that step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXResumeT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT
open Silmaril.Proofs.Wasm.Models.FXVRuns (resume_code_eq)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}
  {core : Instr → List CValType → List CValType → Prop} {m : ModuleInst}

/-! ## Inversion of the judgement -/

/-- The empty sequence has type `t → t`. -/
theorem typedFX_nil {is : List InstrFX} {t₁ t₂ : List FTy} (h : TypedFX core m is t₁ t₂)
    (his : is = []) : t₁ = t₂ := by
  induction h with
  | nil => rfl
  | core => cases his
  | contNew => cases his
  | contBind => cases his
  | resume => cases his
  | append _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.mp his
    rw [ih₁ h₁, ih₂ h₂]
  | frame ts _ ih => rw [ih his]

/-- The judgement at a single `resume $ct hs`. -/
def ResumeTyped (m : ModuleInst) (ct : TypeIdx) (t₁ t₂ : List FTy) : Prop :=
  ∃ pre ps rs, contType? m ct = some (ps, rs) ∧ t₁ = pre ++ vtys ps ++ [.cont ct] ∧
    t₂ = pre ++ vtys rs

theorem resumeTyped_frame {ct : TypeIdx} {t₁ t₂ : List FTy} (ts : List FTy)
    (h : ResumeTyped m ct t₁ t₂) : ResumeTyped m ct (ts ++ t₁) (ts ++ t₂) := by
  obtain ⟨pre, ps, rs, hc, rfl, rfl⟩ := h
  exact ⟨ts ++ pre, ps, rs, hc, by simp, by simp⟩

/-- A singleton is split as `[] ++ [x]` or `[x] ++ []`. -/
theorem singleton_split {is js : List InstrFX} {x : InstrFX} (h : is ++ js = [x]) :
    (is = [] ∧ js = [x]) ∨ (is = [x] ∧ js = []) :=
  List.append_eq_singleton_iff.mp h

/-- **Inversion at `resume`.** -/
theorem typedFX_resume_inv {is : List InstrFX} {ct : TypeIdx} {hs : List OnClause}
    {t₁ t₂ : List FTy} (h : TypedFX core m is t₁ t₂) (his : is = [.fx (.resume ct hs)]) :
    ResumeTyped m ct t₁ t₂ := by
  induction h with
  | nil => cases his
  | core => cases his
  | contNew => cases his
  | contBind => cases his
  | @resume ct' hs' ps rs hc =>
    simp only [List.cons.injEq, InstrFX.fx.injEq, FXInstr.resume.injEq, and_true] at his
    obtain ⟨rfl, -⟩ := his
    exact ⟨[], ps, rs, hc, rfl, rfl⟩
  | append h₁ h₂ ih₁ ih₂ =>
    rcases singleton_split his with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [typedFX_nil h₁ h0]
      exact ih₂ h1
    · rw [← typedFX_nil h₂ h1]
      exact ih₁ h0
  | frame ts _ ih => exact resumeTyped_frame ts (ih his)

/-- The judgement at a single `cont.bind $ct $ct'`. -/
def BindTyped (m : ModuleInst) (ct ct' : TypeIdx) (t₁ t₂ : List FTy) : Prop :=
  ∃ pre ps₁ ps₂ rs, contType? m ct = some (ps₁ ++ ps₂, rs) ∧ contType? m ct' = some (ps₂, rs) ∧
    t₁ = pre ++ vtys ps₁ ++ [.cont ct] ∧ t₂ = pre ++ [.cont ct']

theorem bindTyped_frame {ct ct' : TypeIdx} {t₁ t₂ : List FTy} (ts : List FTy)
    (h : BindTyped m ct ct' t₁ t₂) : BindTyped m ct ct' (ts ++ t₁) (ts ++ t₂) := by
  obtain ⟨pre, ps₁, ps₂, rs, hc, hc', rfl, rfl⟩ := h
  exact ⟨ts ++ pre, ps₁, ps₂, rs, hc, hc', by simp, by simp⟩

/-- **Inversion at `cont.bind`.** -/
theorem typedFX_bind_inv {is : List InstrFX} {ct ct' : TypeIdx} {t₁ t₂ : List FTy}
    (h : TypedFX core m is t₁ t₂) (his : is = [.fx (.contBind ct ct')]) :
    BindTyped m ct ct' t₁ t₂ := by
  induction h with
  | nil => cases his
  | core => cases his
  | contNew => cases his
  | resume => cases his
  | @contBind c c' ps₁ ps₂ rs hc hc' =>
    simp only [List.cons.injEq, InstrFX.fx.injEq, FXInstr.contBind.injEq, and_true] at his
    obtain ⟨rfl, rfl⟩ := his
    exact ⟨[], ps₁, ps₂, rs, hc, hc', rfl, rfl⟩
  | append h₁ h₂ ih₁ ih₂ =>
    rcases singleton_split his with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [typedFX_nil h₁ h0]
      exact ih₂ h1
    · rw [← typedFX_nil h₂ h1]
      exact ih₁ h0
  | frame ts _ ih => exact bindTyped_frame ts (ih his)

/-! ## Arities -/

theorem contParams?_eq (m : ModuleInst) (ct : TypeIdx) :
    contParams? m ct = (contType? m ct).map Prod.fst := rfl

/-- The judgement's parameters are `StepFXR`'s resume arity. -/
theorem resumeArity_of_contType {ct : TypeIdx} {ps rs : List CValType}
    (h : contType? m ct = some (ps, rs)) : ResumeArity m ct ps.length :=
  ⟨ps, by rw [contParams?_eq, h]; rfl, rfl⟩

/-- The judgement's parameters are `StepFXT`'s bind arity. -/
theorem bindArity_of_contType {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType}
    (h : contType? m ct = some (ps₁ ++ ps₂, rs)) (h' : contType? m ct' = some (ps₂, rs)) :
    BindArity m ct ct' ps₁.length :=
  ⟨ps₁ ++ ps₂, ps₂, by rw [contParams?_eq, h]; rfl, by rw [contParams?_eq, h']; rfl, by simp⟩

/-- **Bind `n`, then resume with `j`, is resume with `n + j`.** -/
theorem bind_resume_arity {ct ct' : TypeIdx} {n j : Nat} (hb : BindArity m ct ct' n)
    (hr : ResumeArity m ct' j) : ResumeArity m ct (n + j) := by
  obtain ⟨ps, ps', hps, hps', hn⟩ := hb
  obtain ⟨qs, hqs, rfl⟩ := hr
  rw [hps'] at hqs
  cases hqs
  exact ⟨ps, hps, hn.symm⟩

/-! ## Typed stacks -/

variable {VT : Val → CValType → Prop} {KT : Nat → TypeIdx → Prop}

/-- Values typed at an appended type list split accordingly. -/
theorem forall₂_append_split {R : FVal → FTy → Prop} {V : List FVal} {A B : List FTy}
    (h : List.Forall₂ R V (A ++ B)) :
    ∃ V₁ V₂, V = V₁ ++ V₂ ∧ List.Forall₂ R V₁ A ∧ List.Forall₂ R V₂ B := by
  induction A generalizing V with
  | nil => exact ⟨[], V, rfl, .nil, h⟩
  | cons a A ih =>
    cases h with
    | cons hv hV =>
      obtain ⟨V₁, V₂, rfl, h₁, h₂⟩ := ih hV
      exact ⟨_ :: V₁, V₂, rfl, .cons hv h₁, h₂⟩

theorem forall₂_singleton_cont {V : List FVal} {ct : TypeIdx}
    (h : List.Forall₂ (FValTy VT KT) V [.cont ct]) : ∃ k, V = [.cont k] ∧ KT k ct := by
  cases h with
  | cons hv hnil =>
    cases hnil
    cases hv with
    | cont hk => exact ⟨_, rfl, hk⟩

/-- **A typed stack at `resume` splits with the typed arity.** -/
theorem typed_resume_split {ct : TypeIdx} {hs : List OnClause} {t₁ t₂ : List FTy}
    {V : List FVal} (h : TypedFX core m [.fx (.resume ct hs)] t₁ t₂)
    (hV : List.Forall₂ (FValTy VT KT) V t₁) :
    ∃ V₀ V₂ k, V = V₀ ++ V₂ ++ [.cont k] ∧ ResumeArity m ct V₂.length ∧ KT k ct := by
  obtain ⟨pre, ps, rs, hc, rfl, -⟩ := typedFX_resume_inv h rfl
  obtain ⟨W, U, rfl, hW, hU⟩ := forall₂_append_split hV
  obtain ⟨V₀, V₂, rfl, -, h₂⟩ := forall₂_append_split hW
  obtain ⟨k, rfl, hk⟩ := forall₂_singleton_cont hU
  have hlen : V₂.length = ps.length := by
    rw [h₂.length_eq]
    simp [vtys]
  exact ⟨V₀, V₂, k, rfl, hlen ▸ resumeArity_of_contType hc, hk⟩

theorem resume_code_split (V₀ V₂ : List FVal) (k : Nat) (ct : TypeIdx) (hs : List OnClause) :
    fvals (V₀ ++ V₂ ++ [.cont k]) ++ [AdminFX.fx (.resume ct hs)] =
      fvals V₀ ++ (fvals V₂ ++ [.contRef k, .fx (.resume ct hs)]) ++ [] := by
  simp [fvals, FVal.toAdmin]

/-- A `resume` on the arguments `V₂` under a stack `V₀`. -/
theorem stepR_resume_under {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {V₀ V₂ : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} (hk : K[k]? = some (some C)) (hr : hs.mapM (resolve s f) = some hs')
    (ha : ResumeArity f.module ct V₂.length) :
    StepFXR P host fx ⟨s, K, f, fvals (V₀ ++ V₂ ++ [.cont k]) ++ [.fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, fvals V₀ ++ [.handler hs' (C.plug (fvals V₂))]⟩ := by
  have h₀ : StepFXR P host fx ⟨s, K, f, fvals V₂ ++ [.contRef k, .fx (.resume ct hs)]⟩
      ⟨s, K.set k none, f, [.handler hs' (C.plug (fvals V₂))]⟩ := StepFXR.resume hk hr ha
  rw [resume_code_split]
  by_cases hne : V₀ = []
  · subst hne
    simpa using h₀
  · simpa using StepFXR.seq (vs := V₀) (rest := []) h₀ (Or.inl hne)

/-- **Progress of typed `resume`**: a typed stack with a live continuation resumes it with
exactly the typed number of arguments. -/
theorem typed_resume_progress {host : HostSemantics H} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {t₁ t₂ : List FTy} {V : List FVal}
    (h : TypedFX core f.module [.fx (.resume ct hs)] t₁ t₂)
    (hV : List.Forall₂ (FValTy VT KT) V t₁) (hlive : ∀ k, KT k ct → ∃ C, K[k]? = some (some C))
    (hr : hs.mapM (resolve s f) = some hs') :
    ∃ V₀ V₂ k, ∃ C : ContFX, V = V₀ ++ V₂ ++ [.cont k] ∧ ResumeArity f.module ct V₂.length ∧
      StepFXR P host fx ⟨s, K, f, fvals V ++ [.fx (.resume ct hs)]⟩
        ⟨s, K.set k none, f, fvals V₀ ++ [.handler hs' (C.plug (fvals V₂))]⟩ := by
  obtain ⟨V₀, V₂, k, rfl, ha, hk⟩ := typed_resume_split h hV
  obtain ⟨C, hC⟩ := hlive k hk
  exact ⟨V₀, V₂, k, C, rfl, ha, stepR_resume_under hC hr ha⟩

/-- **Typed `resume` has one successor**: every `StepFXR` step (no host calls) from a typed
stack is the resume with the typed number of arguments, or the trap on a consumed slot. -/
theorem typed_resume_unique {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {ct : TypeIdx} {hs : List OnClause} {t₁ t₂ : List FTy} {V : List FVal} {y : ConfigFX H}
    (h : TypedFX core f.module [.fx (.resume ct hs)] t₁ t₂)
    (hV : List.Forall₂ (FValTy VT KT) V t₁)
    (hy : StepFXR P noHost fx ⟨s, K, f, fvals V ++ [.fx (.resume ct hs)]⟩ y) :
    ∃ V₀ V₂ k, V = V₀ ++ V₂ ++ [.cont k] ∧
      ((∃ C hs', K[k]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
          y = ⟨s, K.set k none, f, fvals V₀ ++ [.handler hs' (C.plug (fvals V₂))]⟩) ∨
        (K[k]? = some none ∧ y = ⟨s, K, f, fvals V₀ ++ [.core .trap]⟩)) := by
  obtain ⟨V₀, V₂, k, rfl, ha, -⟩ := typed_resume_split h hV
  have hcode : fvals (V₀ ++ V₂ ++ [.cont k]) ++ [AdminFX.fx (.resume ct hs)] =
      fvals (V₀ ++ V₂) ++ .contRef k :: .fx (.resume ct hs) :: [] := by
    simp [fvals, FVal.toAdmin]
  rw [hcode] at hy
  obtain ⟨W₁, W₂, hW, hlen, hres⟩ := stepR_resume_split ha hy
  obtain ⟨rfl, rfl⟩ := split_eq hW.symm hlen
  exact ⟨W₁, W₂, k, rfl, hres⟩

end Silmaril.Proofs.Wasm.Models.FXResumeT
