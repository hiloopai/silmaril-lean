module

public import Silmaril.Calculi.PCF.BigStep
public import Silmaril.Calculi.TypedLambda.Morphism

/-! # Morphisms between PCF and PCF+`por`

`Term.embed` includes PCF into PCF+`por` (an operator translation).
`Term.forget` goes back, replacing parallel or by the left sequential or
`if t then true else u` of Definition 33 (a derived-operator translation). On
the other operators it is the identity. `forget` is a retraction of `embed`
and inverts it on `por`-free terms.

Both translations preserve evaluation of `por`-free terms. Consequently
PCF+`por` is a conservative extension of PCF (`Eval.of_embed`): an embedded
PCF program evaluates in PCF+`por` exactly as it does in PCF. Contextual
equivalence is a different matter: parallel or distinguishes PCF programs
that PCF cannot (§8).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

namespace Op

/-- Include the operators of PCF, or of PCF+`por`, into those of PCF+`por`. -/
def lift {p : Bool} : {as : List Ty} → {τ : Ty} → Op p as τ → Op true as τ
  | _, _, .por => .por
  | _, _, .zero => .zero
  | _, _, .succ => .succ
  | _, _, .pred => .pred
  | _, _, .tt => .tt
  | _, _, .ff => .ff
  | _, _, .isZero => .isZero
  | _, _, .ite τ => .ite τ
  | _, _, .fix τ => .fix τ

/-- Translate an operator into a PCF term over its argument variables:
`por(x, y)` becomes the left sequential or `if x then true else y`, and every
other operator is applied to its variables. -/
def forget {p : Bool} : {as : List Ty} → {τ : Ty} → Op p as τ → TypedLambda.Term (sig false) as τ
  | _, _, .zero => .op .zero (Subst.id _)
  | _, _, .succ => .op .succ (Subst.id _)
  | _, _, .pred => .op .pred (Subst.id _)
  | _, _, .tt => .op .tt (Subst.id _)
  | _, _, .ff => .op .ff (Subst.id _)
  | _, _, .isZero => .op .isZero (Subst.id _)
  | _, _, .ite τ => .op (.ite τ) (Subst.id _)
  | _, _, .fix τ => .op (.fix τ) (Subst.id _)
  | _, _, .por => Term.ite (.var .zero) Term.tt (.var (.succ .zero))

/-- The operators of PCF+`por` other than `por`. -/
def IsPCF {p : Bool} : {as : List Ty} → {τ : Ty} → Op p as τ → Prop
  | _, _, .por => False
  | _, _, _ => True

theorem forget_lift {as : List Ty} {τ : Ty} (o : Op false as τ) :
    (lift o).forget = .op o (Subst.id _) := by
  cases o <;> rfl

theorem isPCF_lift {as : List Ty} {τ : Ty} (o : Op false as τ) : (lift o).IsPCF := by
  cases o <;> trivial

theorem lift_forget {as : List Ty} {τ : Ty} (o : Op true as τ) (h : o.IsPCF) :
    ∃ o' : Op false as τ, lift o' = o ∧ o.forget = .op o' (Subst.id _) := by
  cases o <;> first | exact h.elim | exact ⟨_, rfl, rfl⟩

end Op

namespace Term

variable {p : Bool} {Γ : Ctx Base} {σ τ : Ty}

/-- The inclusion into PCF+`por`; the identity on PCF+`por` itself. -/
abbrev lift : Term p Γ τ → Term true Γ τ := TypedLambda.Term.mapOp Op.lift

/-- The inclusion of PCF into PCF+`por`. -/
abbrev embed : Term false Γ τ → Term true Γ τ := lift

/-- Replace parallel or by sequential or. -/
abbrev forget : Term p Γ τ → Term false Γ τ := TypedLambda.Term.translate Op.forget

/-- A term with no occurrence of `por`. -/
def NoPor : {Γ : Ctx Base} → {τ : Ty} → Term p Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .lam t => NoPor t
  | _, _, .app t u => NoPor t ∧ NoPor u
  | _, _, .op o args => o.IsPCF ∧ ∀ a x, NoPor (args a x)

theorem forget_embed : {Γ : Ctx Base} → {τ : Ty} → (t : Term false Γ τ) → t.embed.forget = t
  | _, _, .var _ => rfl
  | _, _, .lam t => congrArg TypedLambda.Term.lam (forget_embed t)
  | _, _, .app t u => congrArg₂ TypedLambda.Term.app (forget_embed t) (forget_embed u)
  | _, _, .op o args => by
      change (Op.forget (Op.lift o)).subst _ = _
      rw [Op.forget_lift]
      exact congrArg (TypedLambda.Term.op o) (Tuple.ext fun a x => forget_embed (args a x))

theorem noPor_embed : {Γ : Ctx Base} → {τ : Ty} → (t : Term false Γ τ) → NoPor t.embed
  | _, _, .var _ => trivial
  | _, _, .lam t => noPor_embed t
  | _, _, .app t u => ⟨noPor_embed t, noPor_embed u⟩
  | _, _, .op o args => ⟨Op.isPCF_lift o, fun a x => noPor_embed (args a x)⟩

theorem embed_forget : {Γ : Ctx Base} → {τ : Ty} → {t : Term true Γ τ} → NoPor t →
    t.forget.embed = t
  | _, _, .var _, _ => rfl
  | _, _, .lam _, h => congrArg TypedLambda.Term.lam (embed_forget h)
  | _, _, .app _ _, h => congrArg₂ TypedLambda.Term.app (embed_forget h.1) (embed_forget h.2)
  | _, _, .op o args, h => by
      obtain ⟨o', rfl, e⟩ := Op.lift_forget o h.1
      change Term.embed ((Op.forget (Op.lift o')).subst _) = _
      rw [e]
      exact congrArg (TypedLambda.Term.op _) (Tuple.ext fun a x => embed_forget (h.2 a x))

theorem embed_injective : Function.Injective (embed (Γ := Γ) (τ := τ)) := fun t t' h => by
  rw [← forget_embed t, ← forget_embed t', h]

theorem noPor_rename : {Γ Δ : Ctx Base} → {τ : Ty} → (ρ : Ren Γ Δ) → {t : Term p Γ τ} →
    NoPor t → NoPor (t.rename ρ)
  | _, _, _, _, .var _, _ => trivial
  | _, _, _, ρ, .lam _, h => noPor_rename (Ren.lift ρ) h
  | _, _, _, ρ, .app _ _, h => ⟨noPor_rename ρ h.1, noPor_rename ρ h.2⟩
  | _, _, _, ρ, .op _ _, h => ⟨h.1, fun a x => noPor_rename ρ (h.2 a x)⟩

theorem noPor_lift {Γ Δ : Ctx Base} {s : Subst (sig p) Γ Δ} (hs : ∀ a x, NoPor (s a x)) :
    ∀ a x, NoPor (Subst.lift (σ := σ) s a x) := by
  intro a x
  cases x with
  | zero => trivial
  | succ x => exact noPor_rename _ (hs _ x)

theorem noPor_subst : {Γ Δ : Ctx Base} → {τ : Ty} → {s : Subst (sig p) Γ Δ} →
    (∀ a x, NoPor (s a x)) → {t : Term p Γ τ} → NoPor t → NoPor (t.subst s)
  | _, _, _, _, hs, .var x, _ => hs _ x
  | _, _, _, _, hs, .lam _, h => noPor_subst (noPor_lift hs) h
  | _, _, _, _, hs, .app _ _, h => ⟨noPor_subst hs h.1, noPor_subst hs h.2⟩
  | _, _, _, _, hs, .op _ _, h => ⟨h.1, fun a x => noPor_subst hs (h.2 a x)⟩

theorem noPor_subst1 {t : Term p (σ :: Γ) τ} {u : Term p Γ σ} (ht : NoPor t) (hu : NoPor u) :
    NoPor (t.subst1 u) :=
  noPor_subst (fun _ x => by cases x with | zero => exact hu | succ x => trivial) ht

theorem forget_subst1 (t : Term p (σ :: Γ) τ) (u : Term p Γ σ) :
    Term.forget (t.subst1 u) = t.forget.subst1 u.forget :=
  TypedLambda.Term.translate_subst1 t u

theorem lift_subst1 (t : Term p (σ :: Γ) τ) (u : Term p Γ σ) :
    Term.lift (t.subst1 u) = t.lift.subst1 u.lift :=
  TypedLambda.Term.mapOp_subst1 _ t u

section SmartConstructors

variable {Γ : Ctx Base}

@[simp] theorem forget_succ (t : Term p Γ .nat) : (Term.succ t).forget = .succ t.forget :=
  congrArg (TypedLambda.Term.op _) <| Tuple.ext fun _ x => by
    cases x with
    | zero => rfl
    | succ y => exact y.elim

@[simp] theorem forget_zero : (Term.zero : Term p Γ .nat).forget = .zero :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

@[simp] theorem forget_tt : (Term.tt : Term p Γ .bool).forget = .tt :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

@[simp] theorem forget_ff : (Term.ff : Term p Γ .bool).forget = .ff :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

@[simp] theorem lift_succ (t : Term p Γ .nat) : (Term.succ t).lift = .succ t.lift :=
  congrArg (TypedLambda.Term.op _) <| Tuple.ext fun _ x => by
    cases x with
    | zero => rfl
    | succ y => exact y.elim

@[simp] theorem lift_zero : (Term.zero : Term p Γ .nat).lift = .zero :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

@[simp] theorem lift_tt : (Term.tt : Term p Γ .bool).lift = .tt :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

@[simp] theorem lift_ff : (Term.ff : Term p Γ .bool).lift = .ff :=
  congrArg (TypedLambda.Term.op _) (Tuple.ext fun _ x => x.elim)

end SmartConstructors

end Term

namespace Value

variable {p : Bool} {τ : Ty}

theorem forget {v : Closed p τ} (h : Value v) : Value v.forget := by
  induction h with
  | @succ args _ ih =>
      rw [← Tuple.single_head args, Term.forget_succ]
      exact .succ' ih
  | zero => rw [Term.forget_zero]; exact .zero
  | tt => rw [Term.forget_tt]; exact .tt
  | ff => rw [Term.forget_ff]; exact .ff
  | lam t => exact .lam _

theorem lift {v : Closed p τ} (h : Value v) : Value v.lift := by
  induction h with
  | @succ args _ ih =>
      rw [← Tuple.single_head args, Term.lift_succ]
      exact .succ' ih
  | zero => rw [Term.lift_zero]; exact .zero
  | tt => rw [Term.lift_tt]; exact .tt
  | ff => rw [Term.lift_ff]; exact .ff
  | lam t => exact .lam _

theorem embed {v : Closed false τ} (h : Value v) : Value v.embed := h.lift

end Value

namespace Eval

variable {p : Bool} {τ : Ty}

/-- Evaluation of a `por`-free program stays `por`-free, and is preserved by
`forget`. -/
theorem forget {t v : Closed p τ} (h : t ⇓ v) (ht : Term.NoPor t) :
    Term.NoPor v ∧ t.forget ⇓ v.forget := by
  induction h with
  | val hv => exact ⟨ht, .val hv.forget⟩
  | @succ _ args v _ ih =>
      obtain ⟨hv, h⟩ := ih (ht.2 _ .zero)
      refine ⟨⟨trivial, fun _ x => by cases x with | zero => exact hv | succ x => exact x.elim⟩, ?_⟩
      rw [Term.forget_succ]
      exact .succ h
  | pred _ ih =>
      obtain ⟨hv, h⟩ := ih (ht.2 _ .zero)
      refine ⟨hv.2 _ .zero, ?_⟩
      rw [Term.forget_succ] at h
      exact .pred h
  | isZeroZ _ ih =>
      obtain ⟨-, h⟩ := ih (ht.2 _ .zero)
      rw [Term.forget_zero] at h
      rw [Term.forget_tt]
      exact ⟨⟨trivial, fun _ x => x.elim⟩, .isZeroZ h⟩
  | isZeroS _ ih =>
      obtain ⟨-, h⟩ := ih (ht.2 _ .zero)
      rw [Term.forget_succ] at h
      rw [Term.forget_ff]
      exact ⟨⟨trivial, fun _ x => x.elim⟩, .isZeroS h⟩
  | iteT _ _ ihb iht =>
      obtain ⟨-, hb⟩ := ihb (ht.2 _ .zero)
      obtain ⟨hv, h⟩ := iht (ht.2 _ (.succ .zero))
      rw [Term.forget_tt] at hb
      exact ⟨hv, .iteT hb h⟩
  | iteF _ _ ihb iht =>
      obtain ⟨-, hb⟩ := ihb (ht.2 _ .zero)
      obtain ⟨hv, h⟩ := iht (ht.2 _ (.succ (.succ .zero)))
      rw [Term.forget_ff] at hb
      exact ⟨hv, .iteF hb h⟩
  | app _ _ iht ihs =>
      obtain ⟨hl, h₁⟩ := iht ht.1
      obtain ⟨hv, h₂⟩ := ihs (Term.noPor_subst1 hl ht.2)
      rw [Term.forget_subst1] at h₂
      exact ⟨hv, .app h₁ h₂⟩
  | fix _ ih =>
      obtain ⟨hv, h⟩ := ih ⟨ht.2 _ .zero, ht⟩
      exact ⟨hv, .fix h⟩
  | porL | porR | porF => exact ht.1.elim

/-- The inclusion into PCF+`por` preserves evaluation. -/
theorem lift {t v : Closed p τ} (h : t ⇓ v) : t.lift ⇓ v.lift := by
  induction h with
  | val hv => exact .val hv.lift
  | @succ _ args v _ ih => rw [Term.lift_succ]; exact .succ ih
  | pred _ ih => rw [Term.lift_succ] at ih; exact .pred ih
  | isZeroZ _ ih => rw [Term.lift_zero] at ih; rw [Term.lift_tt]; exact .isZeroZ ih
  | isZeroS _ ih => rw [Term.lift_succ] at ih; rw [Term.lift_ff]; exact .isZeroS ih
  | iteT _ _ ihb iht => rw [Term.lift_tt] at ihb; exact .iteT ihb iht
  | iteF _ _ ihb iht => rw [Term.lift_ff] at ihb; exact .iteF ihb iht
  | app _ _ iht ihs => rw [Term.lift_subst1] at ihs; exact .app iht ihs
  | fix _ ih => exact .fix ih
  | porL _ ih => rw [Term.lift_tt] at ih ⊢; exact .porL ih
  | porR _ ih => rw [Term.lift_tt] at ih ⊢; exact .porR ih
  | porF _ _ ih ih' => rw [Term.lift_ff] at ih ih' ⊢; exact .porF ih ih'

/-- The inclusion of PCF into PCF+`por` preserves evaluation. -/
theorem embed {t v : Closed false τ} (h : t ⇓ v) : t.embed ⇓ v.embed := h.lift

/-- Conservativity: an embedded PCF program evaluates in PCF+`por` exactly as
in PCF. -/
theorem of_embed {t : Closed false τ} {w : Closed true τ} (h : t.embed ⇓ w) :
    ∃ v, w = v.embed ∧ t ⇓ v := by
  obtain ⟨hw, h'⟩ := forget h (Term.noPor_embed t)
  rw [Term.forget_embed] at h'
  exact ⟨_, (Term.embed_forget hw).symm, h'⟩

theorem embed_iff {t v : Closed false τ} : t.embed ⇓ v.embed ↔ t ⇓ v := by
  refine ⟨fun h => ?_, embed⟩
  obtain ⟨v', e, h'⟩ := of_embed h
  rwa [Term.embed_injective e]

end Eval

end Silmaril.Calculi.PCF
