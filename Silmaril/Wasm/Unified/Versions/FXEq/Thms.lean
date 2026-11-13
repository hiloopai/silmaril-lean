module

public import Silmaril.Wasm.Unified.Versions.FXEq.Defs
public import Silmaril.Wasm.Unified.Versions.Thms
public import Silmaril.Wasm.Models.FXVModel.Thms

/-!
# WasmFX in the unified institution: `fxEmb` as an equation, and `StepFX'`

**`fxEmb` is an equation of observations.** an earlier step proved only a refinement (`fxEmb_refines`),
because `algFX` also interprets `block`, `loop` and `if` by the FX structured forms. Those forms
are attached to opcodes outside `sigFX` (`algFX_shape_dead`), so on 3.0 code the FX meanings are
exactly the embedded Core meanings:

* `fam_head`, `fam_headFX`, `head_ne_headFX`: the 3.0 and stack-switching opcodes are disjoint
  (family numbers below `1000` and from `1000`);
* `algFX_shape_dead`: **no opcode of `sigFX` carries an FX structured form in `algFX`**;
* `fx_evalCode_core` (mutual induction through blocks): every FX meaning of 3.0 code in a reduct
  of `algFX` along a morphism keeping opcodes is the embedding of a Core meaning; with
  `core_mem_evalCode`: `fx_meaning_eq`, the FX meaning **is** the image of the Core
  meaning;
* **`core_obsEq_fx`**: Core 3.0 and the reduct of WasmFX without FX functions have the same
  observations on every call, when FX validation of embedded code is Core validation;
  **`fxEmb_obsEq`**, **`fxEmb_sat_iff`**: at the image point of `fxEmb`, for **every** sentence
  (not only universal ones). The models are not equal (their carriers are sets of Core and of FX
  instructions); the equation is of observations, which is what satisfaction reads.

**`StepFX'`** (`Silmaril.Wasm.Models.FXV`, continuation references as values):

* `core_obsEq_fx'`, **`fxEmb'_obsEq`**, **`fxEmb'_sat_iff`**: the same equation for the corrected
  WasmFX model `fxModelN'` (from `behavioursFX'_ofCore`): `fxEmb'` is presented as an equation;
* **`fxFix_refines`**: the defective model refines the corrected one on every signature-level
  call (`behavioursFX_incl`), the code-level `fxFix`.

**The structured forms** (`algFXs`): `structured_mem_algFXs`: an FX `block` whose body is
`resume` has a meaning in `algFXs`, while `structured_not_mem_algFX`: it has none in `algFX`.
The frozen `Task.fxs_obsEq_core` (Core 3.0 and the reduct of `fxModelNs` have the same
observations) is **refuted as stated** in `Silmaril.Wasm.Unified.Versions.FXsEq`
(`not_fxs_obsEq_core`: its hypothesis does not constrain FX validation of the FX structured
forms), and the repaired statement, with FX validation read off the Core program, is proved
there (`core_obsEq_fxs`, from the CoreFX simulation `Silmaril.Wasm.Unified.Versions.FXSim`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

/-! ## The structured forms of `algFX` are dead -/

/-- The family number of an opcode (its first parameter). -/
def fam : Opcode → Nat
  | .named _ (k :: _) => k
  | _ => 0

theorem fam_head (i : Instr) : fam (head i) < 1000 := by
  cases i <;> simp [head, fam]

theorem fam_headFX (j : FXInstr) : 1000 ≤ fam (headFX j) := by
  cases j <;> simp [headFX, fam]

theorem head_ne_headFX (i : Instr) (j : FXInstr) : head i ≠ headFX j := fun h =>
  absurd (h ▸ fam_head i) (Nat.not_lt.mpr (fam_headFX j))

theorem head_ne_nil (i : Instr) (n : String) : head i ≠ .named n [] := by
  cases i <;> simp [head]

theorem headFX_ne_nil (j : FXInstr) (n : String) : headFX j ≠ .named n [] := by
  cases j <;> simp [headFX]

/-- **No opcode of `sigFX` carries an FX structured form in `algFX`.** -/
theorem algFX_shape_dead (o : sigFX.Op) (x : InstrFX) (imms : List Imm)
    (bs : List (List InstrFX)) : shapeFX x ≠ some (o.1, imms, bs) := by
  intro h
  have hnil : ∃ n, o.1 = .named n [] := by
    cases x <;> simp [shapeFX] at h
    all_goals exact ⟨_, h.1.symm⟩
  obtain ⟨n, hn⟩ := hnil
  rcases o.2 with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact head_ne_nil i n (hi.trans hn)
  · exact headFX_ne_nil j n (hj.trans hn)

/-! ## FX meanings of 3.0 code are embedded Core meanings -/

section Eval

mutual
/-- FX meanings of an instruction are embedded Core meanings. -/
theorem fx_evalInstr_core (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (u : UInstr sig30.Op) → ∀ x ∈ evFXI σ u, ∃ i ∈ evalI30 u, x = InstrFX.core i
  | .op o imms bs hs => by
    intro x hx
    rw [evFXI, Alg.evalInstr] at hx
    rcases hx with ⟨i, rfl, h₁, h₂, h₃, h₄⟩ | ⟨j, -, hj, -⟩ | ⟨bs', hb, -⟩
    · refine ⟨i, ?_, rfl⟩
      rw [evalI30, Alg.evalInstr]
      exact ⟨h₁.trans (hσ o), h₂, h₃, fx_evalBlocks_core σ hσ bs i.bodies h₄⟩
    · obtain ⟨i, hi⟩ := o.2
      exact absurd (hi.trans ((hσ o).symm.trans hj.symm)) (head_ne_headFX i j)
    · exact absurd hb (algFX_shape_dead (σ.f o) x imms bs')
/-- **FX meanings of 3.0 code are embedded Core meanings.** -/
theorem fx_evalCode_core (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (c : sig30.Code) → ∀ l ∈ evFX σ c, ∃ is ∈ evalC30 c, l = is.map InstrFX.core
  | [] => by
    intro l hl
    rw [evFX, Alg.evalCode] at hl
    have hl' : l = [] := hl
    refine ⟨[], ?_, hl'⟩
    rw [evalC30, Alg.evalCode]
    rfl
  | u :: c => by
    intro l hl
    rw [evFX, Alg.evalCode] at hl
    obtain ⟨x, t, rfl, hx, ht⟩ := hl
    obtain ⟨i, hi, rfl⟩ := fx_evalInstr_core σ hσ u x hx
    obtain ⟨is, his, rfl⟩ := fx_evalCode_core σ hσ c t ht
    refine ⟨i :: is, ?_, rfl⟩
    rw [evalC30, Alg.evalCode]
    exact ⟨i, is, rfl, hi, his⟩
/-- FX meanings of blocks are embedded Core meanings. -/
theorem fx_evalBlocks_core (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) :
    (bs : List sig30.Code) → ∀ bodies : List (List Instr),
      List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) bodies (evFXB σ bs) →
      List.Forall₂ (· ∈ ·) bodies (evB30 bs)
  | [] => by
    intro bodies h
    rw [evFXB, Alg.evalBlocks] at h
    rw [evB30, Alg.evalBlocks]
    cases h
    exact .nil
  | b :: bs => by
    intro bodies h
    rw [evFXB, Alg.evalBlocks] at h
    rw [evB30, Alg.evalBlocks]
    cases h with
    | @cons b₀ _ _ _ h₁ h₂ =>
      obtain ⟨is, his, heq⟩ := fx_evalCode_core σ hσ b _ h₁
      have hb : b₀ = is := List.map_injective_iff.mpr (fun _ _ h => InstrFX.core.inj h) heq
      exact .cons (hb ▸ his) (fx_evalBlocks_core σ hσ bs _ h₂)
end

/-- **The FX meaning of 3.0 code is the image of its Core meaning.** -/
theorem fx_meaning_eq (σ : sig30 ⟶ sigFX) (hσ : ∀ o, (σ.f o).1 = o.1) (c : sig30.Code) :
    evFX σ c = List.map InstrFX.core '' evalC30 c := by
  ext l
  constructor
  · intro hl
    obtain ⟨is, his, rfl⟩ := fx_evalCode_core σ hσ c l hl
    exact ⟨is, his, rfl⟩
  · rintro ⟨is, his, rfl⟩
    exact core_mem_evalCode σ hσ c is his

end Eval

/-! ## The equations -/

variable {H : Type}

/-- Two models of one signature with the same observations on every call. -/
def ObsEq {In B : Type} {K : FSig} (M N : Model In B K) : Prop := ∀ x, M.obs x = N.obs x

theorem ObsEq.sat_iff {In B : Type} {K : FSig} {M N : Model In B K} (h : ObsEq M N)
    (φ : Sen In B K) : Sat M φ ↔ Sat N φ :=
  BSen.sat_congr h φ

theorem ObsEq.reduct {In B : Type} {K K' : FSig} {M N : Model In B K'} (σ : K ⟶ K')
    (h : ObsEq M N) : ObsEq (M.reduct σ) (N.reduct σ) := by
  rintro ⟨c, i⟩
  rw [Model.obs_reduct, Model.obs_reduct]
  exact h _

/-- The FX reduction relations of this module: CoreFX is conservative over Core on embedded
Core code. -/
theorem cfg_conservative (beh : ConfigFX H → Set UObs) (P : Profile) (host : HostSemantics H)
    (hbeh : ∀ c, beh (ofCore c) = behavioursOf P host c) (s : Store H) (f : Frame)
    (is : List Instr) (vs : UIn) :
    beh (cfgFX s f (is.map InstrFX.core) vs) = behCode P host s f is vs := by
  rw [cfgFX_core, hbeh]
  rfl

/-- Observations of a model over `algFX` reducted to 3.0, for any FX behaviour function that is
conservative over Core. -/
theorem obsEq_of_conservative (beh : ConfigFX H → Set UObs) (P : Profile)
    (host : HostSemantics H) (hbeh : ∀ c, beh (ofCore c) = behavioursOf P host c)
    (s : Store H) (f : Frame) (okc : List Instr → Prop) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) :
    ObsEq (Model.reduct (FSig.incl sub30FX)
        (⟨algFX, fun (D : Set (List InstrFX)) => ∃ is ∈ D, okcFX is,
          fun (D : Set (List InstrFX)) vs =>
            {b | ∃ is ∈ D, okcFX is ∧ b ∈ beh (cfgFX s f is vs)}⟩ :
          Model UIn UObs sigFX))
      (model30 P host s f okc) := by
  have hσ : ∀ o, ((FSig.incl sub30FX).f o).1 = o.1 := fun _ => rfl
  rintro ⟨c, vs⟩
  ext b
  show ((∃ l ∈ evFX _ c, okcFX l) ∧ ∃ l ∈ evFX _ c, okcFX l ∧ b ∈ beh (cfgFX s f l vs)) ↔
    ((∃ is ∈ evalC30 c, okc is) ∧ ∃ is ∈ evalC30 c, okc is ∧ b ∈ behCode P host s f is vs)
  rw [fx_meaning_eq _ hσ c]
  simp only [Set.mem_image, exists_exists_and_eq_and, hok, cfg_conservative beh P host hbeh]

/-- **Core 3.0 and the reduct of WasmFX without FX functions observe the same.** -/
theorem core_obsEq_fx (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) :
    ObsEq ((fxModelN P host s noFX f okcFX).reduct (FSig.incl sub30FX)) (model30 P host s f okc) :=
  obsEq_of_conservative _ P host (behavioursFX_conservative P host) s f okc okcFX hok

/-- **The same for WasmFX with continuation values.** -/
theorem core_obsEq_fx' (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) :
    ObsEq ((fxModelN' P host s noFX f okcFX).reduct (FSig.incl sub30FX))
      (model30 P host s f okc) :=
  obsEq_of_conservative _ P host (FXVModel.behavioursFX'_ofCore P host) s f okc okcFX hok

variable (f : Frame) (okc : List Instr → Prop)

/-- **`fxEmb` in the unified institution, as an equation of observations.** -/
theorem fxEmb_obsEq (P : Profile) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) (x : Core.Pt H) :
    ObsEq ((fxModelAt P f okcFX ((FX.fxEmb P H).pt x)).reduct (FSig.incl nsub_30_FX))
      (coreSAt v30 P f okc x) :=
  (core_obsEq_fx P x.2 x.1 f okc okcFX hok).reduct (FSig.incl (nsig_sub30 v30))

/-- **Transfer along `fxEmb`: every sentence.** -/
theorem fxEmb_sat_iff (P : Profile) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) (x : Core.Pt H)
    (φ : Sen UIn UObs (nsig v30)) :
    Sat (fxModelAt P f okcFX ((FX.fxEmb P H).pt x)) (φ.map (FSig.incl nsub_30_FX)) ↔
      Sat (coreSAt v30 P f okc x) φ := by
  rw [sat_map_iff]
  exact (fxEmb_obsEq f okc P okcFX hok x).sat_iff φ

/-- **`fxEmb'` (`StepFX'`) in the unified institution, as an equation of observations.** -/
theorem fxEmb'_obsEq (P : Profile) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) (x : Core.Pt H) :
    ObsEq ((fxModelAt' P f okcFX ((FXVModel.fxEmb' P H).pt x)).reduct (FSig.incl nsub_30_FX))
      (coreSAt v30 P f okc x) :=
  (core_obsEq_fx' P x.2 x.1 f okc okcFX hok).reduct (FSig.incl (nsig_sub30 v30))

/-- **Transfer along `fxEmb'`: every sentence.** -/
theorem fxEmb'_sat_iff (P : Profile) (okcFX : List InstrFX → Prop)
    (hok : ∀ is, okcFX (is.map InstrFX.core) ↔ okc is) (x : Core.Pt H)
    (φ : Sen UIn UObs (nsig v30)) :
    Sat (fxModelAt' P f okcFX ((FXVModel.fxEmb' P H).pt x)) (φ.map (FSig.incl nsub_30_FX)) ↔
      Sat (coreSAt v30 P f okc x) φ := by
  rw [sat_map_iff]
  exact (fxEmb'_obsEq f okc P okcFX hok x).sat_iff φ

/-- **The correction `fxFix` at the code level**: the defective WasmFX model refines the
corrected one. -/
theorem fxFix_refines (P : Profile) (okcFX : List InstrFX → Prop) (x : FX.Pt H) :
    Refines (fxModelAt P f okcFX x) (fxModelAt' P f okcFX x) := by
  rintro ⟨c, vs⟩ b ⟨hok, is, hD, hc, hb⟩
  exact ⟨hok, is, hD, hc, behavioursFX_incl _ hb⟩

/-! ## The structured forms -/

/-- An FX `block` around a stack-switching instruction has a meaning in `algFXs`. -/
theorem structured_mem_algFXs (bt : BlockType) (j : FXInstr) (o : sigFX.Op)
    (ho : o.1 = head (.block bt [])) :
    InstrFX.block bt [.fx j] ∈
      @id (Set InstrFX) (algFXs.op o [e bt] [({[.fx j]} : Set (List InstrFX))] []) :=
  Or.inr (Or.inr ⟨[[.fx j]], by rw [ho]; rfl, rfl, .cons rfl .nil⟩)

/-- **It has none in `algFX`.** -/
theorem structured_not_mem_algFX (bt : BlockType) (j : FXInstr) (o : sigFX.Op)
    (imms : List Imm) (Ds : List (Set (List InstrFX))) (hs : List Handler) :
    InstrFX.block bt [.fx j] ∉ @id (Set InstrFX) (algFX.op o imms Ds hs) := by
  rintro (⟨i, hi, -⟩ | ⟨j', hj, -⟩ | ⟨bs, hb, -⟩)
  · cases hi
  · cases hj
  · exact algFX_shape_dead o _ imms bs hb

/-- **Frozen target, refuted as stated** (`FXsEq.not_fxs_obsEq_core`): with reachable
structured forms, Core 3.0 and the reduct of WasmFX without FX functions still observe the same.
The hypothesis constrains `okcFX` only on embedded Core code; the repaired statement is
`FXsEq.core_obsEq_fxs`. -/
def Task.fxs_obsEq_core : Prop :=
  ∀ (H : Type) (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (okcFX : List InstrFX → Prop),
    (∀ is, okcFX (is.map InstrFX.core) ↔ okc is) →
    ObsEq ((fxModelNs P host s noFX f okcFX).reduct (FSig.incl sub30FX)) (model30 P host s f okc)

end Silmaril.Wasm.Unified.Versions
