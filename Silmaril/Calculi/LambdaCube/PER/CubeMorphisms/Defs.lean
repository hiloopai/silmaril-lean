module

public import Silmaril.Calculi.LambdaCube.PER.Cube
public import Silmaril.Calculi.LambdaCube.PER.PTSMorphism
public import Silmaril.Calculi.LambdaCube.PER.ParametricityOmega

@[expose] public section

set_option autoImplicit true

/-! # Institution comorphisms in the λ-cube from parametric PER semantics

The general construction lives in `PER/PTSMorphism.lean`
(`GSemantics.pullback`): a *PTS morphism*
`φ : P → Q` (a map of sorts preserving axioms and rules, Barendregt's PTS
morphisms) translates judgments and preserves derivability (`HasType.mapSorts`).
Any semantics of `Q`, pulled back along `φ`, is a semantics of `P`, and the
pullback is an institution comorphism `P → Q` whose satisfaction condition holds
by construction (sentences translate along `φ`, models are kept). Pullback is
functorial in `φ` (`pullback_id`, `pullback_comp`).

The cube's edges `c ≤ d` are PTS morphisms with identity sort map
(`Corner.ptsMorphism`); `Semantics.restrict` is the cube-level instance, related
to the general one by `Semantics.restrict_toG`, and its comorphism is the
existing `SemanticInclusion.comorphism`.

The semantics fed into the construction are *parametric PER semantics*: a model
is a total combinatory algebra; a judgment holds when its decodings are valid in
the PER model (`PERModel.SystemF.Sat`, `PERModel.SystemFOmega.Sat`) *and* their
realizers are parametric in the relational model (`RelSat`, built from
`Ty.rinterp` / `Con.rinterp`). Soundness of the relational part is the
abstraction theorem (`PER/Parametricity.lean`, `PER/ParametricityOmega.lean`).
Instances: comorphisms λ→ → λ2 (from the System F semantics) and
λ→, λ2, λω̲ → λω (from the Fω semantics).

The two λ2 semantics are related by `SystemF.paramSat_of_omega`: the restriction
of the Fω parametric semantics to λ2 implies the System F one (via
`interp_ofF` and `rinterp_ofF`). No converse or equivalence between the native semantics is proved here.
Satisfaction quantifies over admissible decodings; a judgment with no such
decoding satisfies these clauses vacuously. The direct λ2 → λω comorphism
therefore uses the restricted Fω semantics, rather than identifying the two
native semantics.

Sources: Goguen–Roşu 2002, Definition 4.2 (comorphisms); Reynolds 1983 and
Atkey 2012 for the abstraction theorems.
-/

namespace Silmaril.Calculi.LambdaCube

open CategoryTheory Silmaril.Logic.Institution

/-! ## Parametric PER semantics -/

namespace PERModel

namespace SystemF

/-- Relational validity of a decoded typing in the relational model over `M`. -/
def RelValid (M : CombAlg.{0}) (Γ : Ctx) (t : Tm) (A : Ty) : Prop :=
  ∀ (R : ℕ → M.D → M.D → Prop) (ρ₁ ρ₂ : ℕ → M.D),
    (∀ n (B : Ty), Γ[n]? = some B → B.rinterp M R (ρ₁ n) (ρ₂ n)) →
      A.rinterp M R (t.erase.eval M ρ₁) (t.erase.eval M ρ₂)

/-- Every decoding of a typing is relationally valid. -/
def RelTyping (M : CombAlg.{0}) (Γ : List (Pseudo CubeSort)) (t B : Pseudo CubeSort) : Prop :=
  ∀ (T : Tele) (t' : Tm) (A : Ty), T.WF → T.toPseudo = Γ →
    t'.toPseudo T.layout = t → A.toPseudo T.layout = B →
    (∀ m, t'.TyFreeIn m → m < T.numTy) → RelValid M T.ctx t' A

/-- The parametricity part of satisfaction: both sides of an equation are
parametric. -/
def RelSat (M : CombAlg.{0}) : PTSJudgment → Prop
  | .typing Γ t B => RelTyping M Γ t B
  | .equation Γ t u B => RelTyping M Γ t B ∧ RelTyping M Γ u B

/-- Parametric PER satisfaction: PER validity and parametricity. -/
def ParamSat (M : CombAlg.{0}) (j : PTSJudgment) : Prop := Sat M j ∧ RelSat M j

/-- Soundness of the parametric semantics: `sat_sound` and the abstraction
theorem `Typed.abstraction_rel`, through `typed_of_decode`. -/
theorem paramSat_sound {j : PTSJudgment} (h : j.Derivable Corner.systemF)
    (M : CombAlg.{0}) : ParamSat M j := by
  refine ⟨sat_sound h M, ?_⟩
  have key : ∀ {Γ t B}, HasType Corner.systemF.specification Γ t B → RelTyping M Γ t B := by
    intro Γ t B hd T t' A hT hΓ ht hA hbt R ρ₁ ρ₂ hρ
    subst hΓ ht hA
    exact (typed_of_decode hT hd hbt).abstraction_rel R hρ
  cases j with
  | typing Γ t B => exact key h
  | equation Γ t u B => exact ⟨key h.1, key h.2.1⟩

/-- The parametric PER models of System F as semantics of the λ2 corner. -/
def paramSemantics : SystemFSemantics where
  Model := Discrete CombAlg.{0}
  sat X j := ParamSat X.as j
  sound h X := paramSat_sound h X.as

/-- The comorphism λ→ → λ2 induced by the parametric semantics of λ2. -/
def stlcComorphism :
    Inst.CoHom (paramSemantics.restrict Corner.stlc_le_systemF).inst paramSemantics.inst :=
  paramSemantics.restrictComorphism Corner.stlc_le_systemF

end SystemF

namespace SystemFOmega

/-- Relational validity of a decoded Fω typing. -/
def RelValid (M : CombAlg.{0}) (Δ : KCtx) (Γ : Ctx) (t : Tm) (A : Con) : Prop :=
  ∀ (ξ : ℕ → REntry M.D) (ρ₁ ρ₂ : ℕ → M.D), RFits M Δ ξ → RelCtx M Γ ξ ρ₁ ρ₂ →
    A.rinterp M ξ .star (t.erase.eval M ρ₁) (t.erase.eval M ρ₂)

/-- Every bounded decoding of a typing is relationally valid. -/
def RelTyping (M : CombAlg.{0}) (Γ : List (Pseudo CubeSort)) (t B : Pseudo CubeSort) : Prop :=
  ∀ (T : Tele) (t' : Tm) (A : Con), T.WF → T.toPseudo = Γ →
    t'.toPseudo T.layout = t → A.toPseudo T.layout = B →
    (∀ m, t'.TyFreeIn m → m < T.kctx.length) → RelValid M T.kctx T.ctx t' A

/-- The parametricity part of satisfaction. -/
def RelSat (M : CombAlg.{0}) : PTSJudgment → Prop
  | .typing Γ t B => RelTyping M Γ t B
  | .equation Γ t u B => RelTyping M Γ t B ∧ RelTyping M Γ u B

/-- Parametric PER satisfaction for Fω. -/
def ParamSat (M : CombAlg.{0}) (j : PTSJudgment) : Prop := Sat M j ∧ RelSat M j

/-- A bounded decoding of a derivable λω typing over an encoded telescope is an
Fω typing: the Fω analogue of `SystemF.typed_of_decode`. It follows from
`reflect` (with correctness of types for its sort premise) and injectivity of
the encodings on bounded decodings, the same ingredients as `sat_sound`. -/
theorem typed_of_bounded_decode {T : Tele} (hT : T.WF) {t : Tm} {A : Con}
    (h : HasType Corner.systemFOmega.specification T.toPseudo
      (t.toPseudo T.layout) (A.toPseudo T.layout))
    (ht : ∀ m, t.TyFreeIn m → m < T.kctx.length) : Typed T.kctx T.ctx t A :=
  typed_of_decode hT h ht

/-- Soundness: `sat_sound`, `reflect` and the Fω abstraction theorem. -/
theorem paramSat_sound {j : PTSJudgment} (h : j.Derivable Corner.systemFOmega)
    (M : CombAlg.{0}) : ParamSat M j := by
  refine ⟨sat_sound h M, ?_⟩
  have key : ∀ {Γ t B}, HasType Corner.systemFOmega.specification Γ t B →
      RelTyping M Γ t B := by
    intro Γ t B hd T t' A hT hΓ ht hA hbt ξ ρ₁ ρ₂ hξ hρ
    subst hΓ ht hA
    exact (typed_of_bounded_decode hT hd hbt).abstraction hT.ctx_kinded hξ hρ
  cases j with
  | typing Γ t B => exact key h
  | equation Γ t u B => exact ⟨key h.1, key h.2.1⟩

/-- The parametric PER models of Fω as semantics of the λω corner. -/
def paramSemantics : SystemFOmegaSemantics where
  Model := Discrete CombAlg.{0}
  sat X j := ParamSat X.as j
  sound h X := paramSat_sound h X.as

theorem stlc_le_systemFOmega : Corner.stlc ≤ Corner.systemFOmega :=
  ⟨by simp [Corner.stlc, Corner.systemFOmega], by simp [Corner.systemFOmega],
    by simp [Corner.stlc]⟩

theorem systemF_le_systemFOmega : Corner.systemF ≤ Corner.systemFOmega :=
  ⟨by simp [Corner.systemF, Corner.systemFOmega], by simp [Corner.systemFOmega],
    by simp [Corner.systemF]⟩

theorem omega_le_systemFOmega : Corner.omega ≤ Corner.systemFOmega :=
  ⟨by simp [Corner.omega, Corner.systemFOmega], by simp [Corner.systemFOmega],
    by simp [Corner.omega]⟩

/-- The comorphism λ→ → λω. -/
def stlcComorphism :
    Inst.CoHom (paramSemantics.restrict stlc_le_systemFOmega).inst paramSemantics.inst :=
  paramSemantics.restrictComorphism stlc_le_systemFOmega

/-- The comorphism λ2 → λω. -/
def systemFComorphism :
    Inst.CoHom (paramSemantics.restrict systemF_le_systemFOmega).inst paramSemantics.inst :=
  paramSemantics.restrictComorphism systemF_le_systemFOmega

/-- The comorphism λω̲ → λω. -/
def omegaComorphism :
    Inst.CoHom (paramSemantics.restrict omega_le_systemFOmega).inst paramSemantics.inst :=
  paramSemantics.restrictComorphism omega_le_systemFOmega

/-- The edge λ→ → λω factors through λ2 at the level of semantics. -/
theorem restrict_stlc_factor :
    (paramSemantics.restrict systemF_le_systemFOmega).restrict Corner.stlc_le_systemF =
      paramSemantics.restrict stlc_le_systemFOmega :=
  rfl

end SystemFOmega

/-! ## Relating the two λ2 semantics -/

namespace SystemF

/-- System F telescopes as Fω telescopes (type variables of kind `*`). -/
def Tele.toOmega : Tele → SystemFOmega.Tele
  | [] => []
  | .ty :: T => .ty .star :: Tele.toOmega T
  | .tm A :: T => .tm (SystemFOmega.ofF A) :: Tele.toOmega T

theorem Tele.toOmega_layout (T : Tele) : (Tele.toOmega T).layout = T.layout := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    cases e <;> simp only [Tele.toOmega, Tele.layout, SystemFOmega.Tele.layout, ih]

theorem Ty.toPseudo_ofF (A : Ty) (L : Layout) :
    (SystemFOmega.ofF A).toPseudo L = A.toPseudo L := by
  induction A generalizing L with
  | var n => rfl
  | arr A B ihA ihB =>
    simp only [SystemFOmega.ofF, SystemFOmega.Con.toPseudo, Ty.toPseudo, ihA, ihB]
  | all A ih =>
    simp only [SystemFOmega.ofF, SystemFOmega.Con.toPseudo, Ty.toPseudo, ih,
      SystemFOmega.Kind.toPseudo]

theorem Tm.toPseudo_ofFTm (t : Tm) (L : Layout) :
    (SystemFOmega.ofFTm t).toPseudo L = t.toPseudo L := by
  induction t generalizing L with
  | var n => rfl
  | app t u iht ihu =>
    simp only [SystemFOmega.ofFTm, SystemFOmega.Tm.toPseudo, Tm.toPseudo, iht, ihu]
  | lam A t ih =>
    simp only [SystemFOmega.ofFTm, SystemFOmega.Tm.toPseudo, Tm.toPseudo, ih, Ty.toPseudo_ofF]
  | tapp t A ih =>
    simp only [SystemFOmega.ofFTm, SystemFOmega.Tm.toPseudo, Tm.toPseudo, ih, Ty.toPseudo_ofF]
  | tlam t ih =>
    simp only [SystemFOmega.ofFTm, SystemFOmega.Tm.toPseudo, Tm.toPseudo, ih,
      SystemFOmega.Kind.toPseudo]

theorem Tele.toOmega_toPseudo (T : Tele) : (Tele.toOmega T).toPseudo = T.toPseudo := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    cases e with
    | ty =>
      simp only [Tele.toOmega, Tele.toPseudo, SystemFOmega.Tele.toPseudo, ih,
        SystemFOmega.Kind.toPseudo]
    | tm A =>
      simp only [Tele.toOmega, Tele.toPseudo, SystemFOmega.Tele.toPseudo, ih,
        Tele.toOmega_layout, Ty.toPseudo_ofF]

theorem Tele.toOmega_kctx (T : Tele) :
    (Tele.toOmega T).kctx = List.replicate T.numTy .star := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    cases e with
    | ty => simp only [Tele.toOmega, SystemFOmega.Tele.kctx, Tele.numTy, ih, List.replicate_succ]
    | tm A => simp only [Tele.toOmega, SystemFOmega.Tele.kctx, Tele.numTy, ih]

theorem Tele.toOmega_wf {T : Tele} (h : T.WF) : (Tele.toOmega T).WF := by
  induction T with
  | nil => trivial
  | cons e T ih =>
    cases e with
    | ty => exact ih h
    | tm A =>
      obtain ⟨hA, hT⟩ := h
      refine ⟨?_, ih hT⟩
      rw [Tele.toOmega_kctx]
      exact SystemFOmega.kinded_ofF A _ hA

theorem Tele.toOmega_ctx (T : Tele) :
    (Tele.toOmega T).ctx = T.ctx.map SystemFOmega.ofF := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    cases e with
    | ty =>
      simp only [Tele.toOmega, SystemFOmega.Tele.ctx, Tele.ctx, ih]
      exact SystemFOmega.map_ofF_shift _
    | tm A => simp only [Tele.toOmega, SystemFOmega.Tele.ctx, Tele.ctx, ih, List.map_cons]

theorem Ty.freeIn_of_ofF (A : Ty) : ∀ m, (SystemFOmega.ofF A).FreeIn m → A.FreeIn m := by
  induction A with
  | var n => intro m h; exact h
  | arr A B ihA ihB =>
    intro m h
    rcases h with h | h
    exacts [Or.inl (ihA m h), Or.inr (ihB m h)]
  | all A ih => intro m h; exact ih (m + 1) h

theorem Tm.tyFreeIn_of_ofFTm (t : Tm) :
    ∀ m, (SystemFOmega.ofFTm t).TyFreeIn m → t.TyFreeIn m := by
  induction t with
  | var n => intro m h; exact h
  | app t u iht ihu =>
    intro m h
    rcases h with h | h
    exacts [Or.inl (iht m h), Or.inr (ihu m h)]
  | lam A t ih =>
    intro m h
    rcases h with h | h
    exacts [Or.inl (Ty.freeIn_of_ofF A m h), Or.inr (ih m h)]
  | tapp t A ih =>
    intro m h
    rcases h with h | h
    exacts [Or.inl (ih m h), Or.inr (Ty.freeIn_of_ofF A m h)]
  | tlam t ih => intro m h; exact ih (m + 1) h

theorem Tele.fits_toOmega {M : CombAlg.{0}} (T : Tele) (η : ℕ → PER M.D) :
    SystemFOmega.Fits M (Tele.toOmega T).kctx (fun n => ⟨.star, η n⟩) := by
  intro n k hn
  rw [Tele.toOmega_kctx] at hn
  exact (List.eq_of_mem_replicate (List.mem_of_getElem? hn)).symm

theorem Tele.rfits_toOmega {M : CombAlg.{0}} (T : Tele) (R : ℕ → M.D → M.D → Prop) :
    SystemFOmega.RFits M (Tele.toOmega T).kctx (fun n => ⟨.star, R n⟩) := by
  intro n k hn
  rw [Tele.toOmega_kctx] at hn
  exact (List.eq_of_mem_replicate (List.mem_of_getElem? hn)).symm

/-- An Fω PER judgment about embedded System F data gives the System F one. -/
theorem validEq_of_omega {M : CombAlg.{0}} {T : Tele} {t u : Tm} {A : Ty}
    (h : SystemFOmega.ValidEq M (Tele.toOmega T).kctx (Tele.toOmega T).ctx
      (SystemFOmega.ofFTm t) (SystemFOmega.ofFTm u) (SystemFOmega.ofF A)) :
    ValidEq M T.ctx t u A := by
  intro η ρ ρ' hρ
  have := h (fun n => ⟨.star, η n⟩) ρ ρ' (T.fits_toOmega η) (fun n B hn => by
    rw [Tele.toOmega_ctx, List.getElem?_map] at hn
    obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.mp hn
    rw [SystemFOmega.interp_ofF]
    exact hρ n B' hB')
  rwa [SystemFOmega.interp_ofF, SystemFOmega.erase_ofFTm, SystemFOmega.erase_ofFTm] at this

/-- The relational analogue of `validEq_of_omega`. -/
theorem relValid_of_omega {M : CombAlg.{0}} {T : Tele} {t : Tm} {A : Ty}
    (h : SystemFOmega.RelValid M (Tele.toOmega T).kctx (Tele.toOmega T).ctx
      (SystemFOmega.ofFTm t) (SystemFOmega.ofF A)) :
    RelValid M T.ctx t A := by
  intro R ρ₁ ρ₂ hρ
  have := h (fun n => ⟨.star, R n⟩) ρ₁ ρ₂ (T.rfits_toOmega R) (fun n B hn => by
    rw [Tele.toOmega_ctx, List.getElem?_map] at hn
    obtain ⟨B', hB', rfl⟩ := Option.map_eq_some_iff.mp hn
    rw [rinterp_ofF]
    exact hρ n B' hB')
  rwa [rinterp_ofF, SystemFOmega.erase_ofFTm] at this

end SystemF

end PERModel

end Silmaril.Calculi.LambdaCube
