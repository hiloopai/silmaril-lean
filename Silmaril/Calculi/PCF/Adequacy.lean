module

public import Silmaril.Calculi.PCF.Soundness
public import Silmaril.Calculi.PCF.Contextual
public import Silmaril.Semantics.Domain.ScottInduction

/-! # Adequacy

§7.1–7.2 of the notes, and Theorem 24 of §6.1, for PCF and for PCF+`por`.

The formal approximation relation `d ⊲τ t` (Definition 27) is a logical
relation between elements of `⟦τ⟧` and closed terms of type `τ`. It is closed
under `⊥`, lubs of chains and evaluation (Lemmas 32–35), and every term
approximates its own denotation (Theorem 30, the fundamental property). At
ground types this is adequacy (Theorem 31): `⟦t⟧ = ⟦v⟧` implies `t ⇓ v`. At
function types adequacy fails (Remark 14, `not_eval_of_denote_eq_arrow`).

The fundamental property is proved as in the notes, by induction on terms.
Each operator gets its own lemma about closed terms (the notes' equations (9)
and (10)); the case of `fix` is Scott induction. The flag `p` is arbitrary, so
the proof also covers `por`, for which the notes give no argument. Parallel or
preserves approximation because each of its defined results is justified by
one of the rules PorL, PorR and PorF.

Soundness, compositionality and adequacy together show that denotational
equality implies contextual equivalence (Theorem 24), for open terms too, and
that the denotational order implies the contextual preorder. That argument does
not depend on PCF: it is `TypedLambda.Observation.ctxEquiv_of_denote_eq` and
`TypedLambda.Observation.ctxLe_of_denote_le`, for any sound and adequate model, and
the PCF theorems instantiate it. The preorder version uses that the denotation
of a context is monotone in its hole (`TypedLambda.Context.denote_mono`).

Statements about closed terms use the element `⟦t⟧ = denote t Tuple.nil` of
`⟦τ⟧` (`Model.denoteClosed`, Remark 12) rather than the constant function on
the empty environment; `Model.denote_eq_iff_denoteClosed_eq` converts.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {p : Bool}

/-- Definition 27: the formal approximation relation `d ⊲τ t` between an
element `d ∈ ⟦τ⟧` and a closed term `t : τ`.

* `d ⊲nat t` iff `d = n` implies `t ⇓ n̄`;
* `d ⊲bool t` iff `d = b` implies `t ⇓ b`;
* `d ⊲τ->τ' t` iff `e ⊲τ u` implies `d(e) ⊲τ' t u`. -/
def Approx : (τ : Ty) → (model p).ty τ → Closed p τ → Prop
  | .base .nat, d, t => ∀ n : ℕ, (d : Part ℕ) = Part.some n → t ⇓ Term.num n
  | .base .bool, d, t => ∀ b : Bool, (d : Part Bool) = Part.some b → t ⇓ Term.bool b
  | .arrow σ τ, d, t => ∀ e u, Approx σ e u → Approx τ (Model.app d e) (.app t u)

/-- Definition 29: the formal approximation `ρ ⊲Γ s` between an environment and
a parallel closed substitution (Definition 28), componentwise. -/
def ApproxEnv {Γ : Ctx Base} (ρ : (model p).Env Γ) (s : Subst (sig p) Γ []) : Prop :=
  ∀ a x, Approx a (ρ a x) (s a x)

namespace Approx

/-- Lemma 32: `⊥` approximates every term. -/
theorem bot : (τ : Ty) → {t : Closed p τ} → Approx τ ⊥ t
  | .base .nat, _ => fun n hn => absurd hn.symm (Part.some_ne_none n)
  | .base .bool, _ => fun b hb => absurd hb.symm (Part.some_ne_none b)
  | .arrow _ τ, _ => fun _ _ _ => bot τ

/-- Lemma 33: `{d ∈ ⟦τ⟧ ∣ d ⊲τ t}` is chain-closed. At ground types every set
is chain-closed, since chains in flat domains are eventually constant. -/
theorem chainClosed : (τ : Ty) → (t : Closed p τ) → ChainClosed {d | Approx τ d t}
  | .base .nat, _ => ChainClosed.of_wellFoundedGT (D := Part ℕ) _
  | .base .bool, _ => ChainClosed.of_wellFoundedGT (D := Part Bool) _
  | .arrow _ τ, t => fun c hc e u he =>
      chainClosed τ (.app t u) (c.map ⟨fun f => Model.app f e, fun _ _ h => h e⟩)
        fun n => hc n e u he

/-- Lemmas 32 and 33: `{d ∈ ⟦τ⟧ ∣ d ⊲τ t}` is admissible, so Scott induction
applies to it. -/
theorem admissible (τ : Ty) (t : Closed p τ) : Admissible {d | Approx τ d t} :=
  ⟨bot τ, chainClosed τ t⟩

/-- Lemma 34: approximation is closed downwards. -/
theorem mono : (τ : Ty) → {d d' : (model p).ty τ} → {t : Closed p τ} → d' ≤ d →
    Approx τ d t → Approx τ d' t
  | .base .nat, _, _, _, hle, h => fun n hn =>
      h n (Flat.eq_of_some_le (by rw [← hn]; exact hle))
  | .base .bool, _, _, _, hle, h => fun b hb =>
      h b (Flat.eq_of_some_le (by rw [← hb]; exact hle))
  | .arrow _ τ, _, _, _, hle, h => fun e u he => mono τ (hle e) (h e u he)

/-- Lemma 35: if every result of `t` is a result of `t'`, then `t'`
approximates whatever `t` approximates. -/
theorem of_eval : (τ : Ty) → {d : (model p).ty τ} → {t t' : Closed p τ} →
    (∀ v, t ⇓ v → t' ⇓ v) → Approx τ d t → Approx τ d t'
  | .base .nat, _, _, _, H, h => fun n hn => H _ (h n hn)
  | .base .bool, _, _, _, H, h => fun b hb => H _ (h b hb)
  | .arrow _ τ, _, _, _, H, h => fun e u he => by
      refine of_eval τ (fun v hv => ?_) (h e u he)
      cases hv with
      | val hv => cases hv
      | app ht hs => exact .app (H _ ht) hs

end Approx

namespace ApproxEnv

variable {Γ : Ctx Base}

/-- The empty environment approximates the empty substitution. -/
theorem nil : ApproxEnv (p := p) (Γ := []) Tuple.nil Tuple.nil := fun _ x => x.elim

/-- Extending both sides: `ρ[x ↦ d] ⊲ σ[x ↦ u]`. -/
theorem cons {σ : Ty} {ρ : (model p).Env Γ} {s : Subst (sig p) Γ []} {d : (model p).ty σ}
    {u : Closed p σ} (hd : Approx σ d u) (h : ApproxEnv ρ s) : ApproxEnv (d ::ₜ ρ) (u ::ₜ s)
  | _, .zero => hd
  | _, .succ x => h _ x

end ApproxEnv

/-! ### The operators preserve approximation

These are the cases of the proof of Theorem 30 for the operators, stated for
closed terms as in equations (9) and (10) of the notes. -/

section Operators

/-- Case Zero. -/
theorem approx_zero (args : Tuple (Closed p) []) :
    Approx .nat (Part.some 0 : Part ℕ) (.op .zero args) := fun n hn => by
  obtain rfl := (Part.some_inj.1 hn).symm
  rw [Tuple.eq_nil args]
  exact .val .zero

/-- Case True. -/
theorem approx_tt (args : Tuple (Closed p) []) :
    Approx .bool (Part.some true : Part Bool) (.op .tt args) := fun b hb => by
  obtain rfl := (Part.some_inj.1 hb).symm
  rw [Tuple.eq_nil args]
  exact .val .tt

/-- Case False. -/
theorem approx_ff (args : Tuple (Closed p) []) :
    Approx .bool (Part.some false : Part Bool) (.op .ff args) := fun b hb => by
  obtain rfl := (Part.some_inj.1 hb).symm
  rw [Tuple.eq_nil args]
  exact .val .ff

/-- Case Succ, equation (9): `d ⊲ t` implies `succ⊥(d) ⊲ succ(t)`. -/
theorem approx_succ {args : Tuple (Closed p) [.nat]} {d : Part ℕ}
    (h : Approx .nat d args.head) : Approx .nat (Flat.map Nat.succ d) (.op .succ args) := by
  intro n hn
  rcases Part.eq_none_or_eq_some d with rfl | ⟨m, rfl⟩
  · exact absurd (hn.symm.trans (Flat.map_none _)) (Part.some_ne_none n)
  · obtain rfl : m + 1 = n := Part.some_inj.1 ((Flat.map_some _ m).symm.trans hn)
    exact .succ (h m rfl)

/-- Case Pred. -/
theorem approx_pred {args : Tuple (Closed p) [.nat]} {d : Part ℕ}
    (h : Approx .nat d args.head) : Approx .nat (Flat.lift predPart d) (.op .pred args) := by
  intro n hn
  rcases Part.eq_none_or_eq_some d with rfl | ⟨m, rfl⟩
  · exact absurd (hn.symm.trans (Flat.lift_none _)) (Part.some_ne_none n)
  · rw [Flat.lift_some] at hn
    cases m with
    | zero => exact absurd hn.symm (Part.some_ne_none n)
    | succ m =>
        obtain rfl : m = n := Part.some_inj.1 hn
        exact .pred (h (m + 1) rfl)

/-- Case IsZ. -/
theorem approx_isZero {args : Tuple (Closed p) [.nat]} {d : Part ℕ}
    (h : Approx .nat d args.head) :
    Approx .bool (Flat.map (fun n : ℕ => n == 0) d) (.op .isZero args) := by
  intro b hb
  rcases Part.eq_none_or_eq_some d with rfl | ⟨m, rfl⟩
  · exact absurd (hb.symm.trans (Flat.map_none _)) (Part.some_ne_none b)
  · obtain rfl : (m == 0) = b := Part.some_inj.1 ((Flat.map_some _ m).symm.trans hb)
    cases m with
    | zero => exact .isZeroZ (h 0 rfl)
    | succ m => exact .isZeroS (h (m + 1) rfl)

/-- Case If, equation (10): if `d₁ ⊲ t₁`, `d₂ ⊲ t₂` and `d₃ ⊲ t₃` then
`if(d₁, d₂, d₃) ⊲ if t₁ then t₂ else t₃`. -/
theorem approx_ite {τ : Ty} {args : Tuple (Closed p) [.bool, τ, τ]} {d₁ : Part Bool}
    {d₂ d₃ : (model p).ty τ} (h₁ : Approx .bool d₁ args.head)
    (h₂ : Approx τ d₂ args.tail.head) (h₃ : Approx τ d₃ args.tail.tail.head) :
    Approx τ (condFun d₁ d₂ d₃) (.op (.ite τ) args) := by
  rcases part_bool_cases d₁ with rfl | rfl | rfl
  · rw [condFun_none]
    exact Approx.bot τ
  · rw [condFun_true]
    exact Approx.of_eval τ (fun v hv => .iteT (h₁ true rfl) hv) h₂
  · rw [condFun_false]
    exact Approx.of_eval τ (fun v hv => .iteF (h₁ false rfl) hv) h₃

/-- Case Fix: `d ⊲ f` implies `fix(d) ⊲ fix(f)`, by Scott induction on
`{e ∈ ⟦τ⟧ ∣ e ⊲τ fix(f)}`. -/
theorem approx_fix {τ : Ty} {args : Tuple (Closed p) [τ ⤳ τ]} {d : (model p).ty (τ ⤳ τ)}
    (h : Approx (τ ⤳ τ) d args.head) : Approx τ (fix (Model.fn d)) (.op (.fix τ) args) :=
  fix_mem (Approx.admissible τ _) fun e he =>
    Approx.of_eval τ (fun _ hv => .fix hv) (h e _ he)

/-- Case Por: parallel or preserves approximation. -/
theorem approx_por {args : Tuple (Closed true) [.bool, .bool]} {d₁ d₂ : Part Bool}
    (h₁ : Approx .bool d₁ args.head) (h₂ : Approx .bool d₂ args.tail.head) :
    Approx .bool (porFun d₁ d₂) (.op .por args) := by
  intro b hb
  have hnone : porFun d₁ d₂ ≠ Part.none := fun h => Part.some_ne_none b (hb.symm.trans h)
  -- Rule PorL: the left argument evaluates to `true`.
  have porL (h : d₁ = Part.some true) : b = true ∧ .op .por args ⇓ .tt := by
    subst h
    exact ⟨Part.some_inj.1 (hb.symm.trans (porFun_true_left _)), .porL (h₁ true rfl)⟩
  -- Rule PorR: the right argument evaluates to `true`.
  have porR (h : d₂ = Part.some true) : b = true ∧ .op .por args ⇓ .tt := by
    subst h
    exact ⟨Part.some_inj.1 (hb.symm.trans (porFun_true_right _)), .porR (h₂ true rfl)⟩
  rcases part_bool_cases d₁ with rfl | rfl | rfl
  · rcases part_bool_cases d₂ with rfl | rfl | rfl
    · exact absurd porFun_none_none hnone
    · obtain ⟨rfl, h⟩ := porR rfl
      exact h
    · exact absurd porFun_none_false hnone
  · obtain ⟨rfl, h⟩ := porL rfl
    exact h
  · rcases part_bool_cases d₂ with rfl | rfl | rfl
    · exact absurd porFun_false_none hnone
    · obtain ⟨rfl, h⟩ := porR rfl
      exact h
    · -- Rule PorF: both arguments evaluate to `false`.
      obtain rfl : b = false := Part.some_inj.1 (hb.symm.trans porFun_false_false)
      exact .porF (h₁ false rfl) (h₂ false rfl)

end Operators

/-- The operator cases of Theorem 30: if the arguments of an operator satisfy
the fundamental property then so does the operator. -/
theorem approx_denote_subst_op {Γ : Ctx Base} {as : List Ty} {τ : Ty} (o : Op p as τ)
    (args : Tuple (Term p Γ) as) {ρ : (model p).Env Γ} {s : Subst (sig p) Γ []}
    (ih : ∀ a x, Approx a (denote (args a x) ρ) ((args a x).subst s)) :
    Approx τ (denote (.op o args) ρ) ((TypedLambda.Term.op o args).subst s) := by
  cases o with
  | zero => exact approx_zero _
  | tt => exact approx_tt _
  | ff => exact approx_ff _
  | succ => exact approx_succ (ih _ .zero)
  | pred => exact approx_pred (ih _ .zero)
  | isZero => exact approx_isZero (ih _ .zero)
  | ite τ =>
      exact approx_ite (ih _ .zero) (ih _ (.succ .zero)) (ih _ (.succ (.succ .zero)))
  | fix τ => exact approx_fix (ih _ .zero)
  | por => exact approx_por (ih _ .zero) (ih _ (.succ .zero))

/-- Theorem 30 (fundamental property of formal approximation): if `ρ ⊲Γ s`
then `⟦t⟧(ρ) ⊲τ t[s]`. -/
theorem approx_denote_subst {Γ : Ctx Base} {τ : Ty} :
    (t : TypedLambda.Term (sig p) Γ τ) → {ρ : (model p).Env Γ} → {s : Subst (sig p) Γ []} →
      ApproxEnv ρ s → Approx τ (denote t ρ) (t.subst s)
  | .var x, _, _, h => h _ x
  | .lam t, _, _, h => fun _ u he => by
      refine Approx.of_eval _ (fun v hv => ?_) (approx_denote_subst t (h.cons he))
      refine .app (.val (.lam _)) ?_
      rw [Term.subst_lift_subst1]
      exact hv
  | .app t u, _, _, h => approx_denote_subst t h _ _ (approx_denote_subst u h)
  | .op o args, _, _, h =>
      approx_denote_subst_op o args fun _ x => approx_denote_subst (args _ x) h

/-- Theorem 30 for closed terms: `⟦t⟧ ⊲τ t`. -/
theorem approx_denote {τ : Ty} (t : Closed p τ) : Approx τ (denote t Tuple.nil) t := by
  have h := approx_denote_subst t ApproxEnv.nil
  rwa [Term.subst_nil] at h

/-! ### Adequacy -/

/-- Theorem 31 (adequacy) at `nat`: if `⟦t⟧ = n` then `t ⇓ n̄`. -/
theorem adequacy_nat {t : Closed p .nat} {n : ℕ}
    (h : denote t Tuple.nil = (Part.some n : Part ℕ)) : t ⇓ Term.num n :=
  approx_denote t n h

/-- Theorem 31 (adequacy) at `bool`: if `⟦t⟧ = b` then `t ⇓ b`. -/
theorem adequacy_bool {t : Closed p .bool} {b : Bool}
    (h : denote t Tuple.nil = (Part.some b : Part Bool)) : t ⇓ Term.bool b :=
  approx_denote t b h

/-- Theorem 31 (adequacy), in the form used for the contextual preorder: at
ground type, if `⟦v⟧ ⊑ ⟦t⟧` for a value `v`, then `t ⇓ v`. Values of ground
type denote maximal elements, so the hypothesis is equivalent to
`⟦t⟧ = ⟦v⟧`. -/
theorem adequacy_le {γ : Ty} (hγ : γ.IsGround) {t v : Closed p γ} (hv : Value v)
    (h : denote v Tuple.nil ≤ denote t Tuple.nil) : t ⇓ v := by
  cases γ with
  | arrow => exact hγ.elim
  | base b =>
      cases b with
      | nat =>
          obtain ⟨n, rfl⟩ := hv.eq_num
          rw [denote_num] at h
          exact adequacy_nat (Flat.eq_of_some_le h)
      | bool =>
          obtain ⟨b, rfl⟩ := hv.eq_bool
          rw [denote_bool] at h
          exact adequacy_bool (Flat.eq_of_some_le h)

/-- Theorem 31 (adequacy): for a closed term `t` and a value `v` of ground type,
`⟦t⟧ = ⟦v⟧` implies `t ⇓ v`.

The restriction to ground types is necessary (Remark 14, see
`not_eval_of_denote_eq_arrow`). -/
theorem adequacy {γ : Ty} (hγ : γ.IsGround) {t v : Closed p γ} (hv : Value v)
    (h : denote t Tuple.nil = denote v Tuple.nil) : t ⇓ v :=
  adequacy_le hγ hv h.ge

/-- Theorem 28 (soundness) for the element denoted by a closed term. -/
theorem Eval.denoteClosed_eq {τ : Ty} {t v : Closed p τ} (h : t ⇓ v) :
    (model p).denoteClosed t = (model p).denoteClosed v :=
  Model.denote_eq_iff_denoteClosed_eq.1 h.denote_eq

/-- Soundness and adequacy: at ground type, `t ⇓ v` iff `⟦t⟧ = ⟦v⟧`. -/
theorem eval_iff_denote_eq {γ : Ty} (hγ : γ.IsGround) {t v : Closed p γ} (hv : Value v) :
    t ⇓ v ↔ denote t Tuple.nil = denote v Tuple.nil :=
  ⟨Eval.denoteClosed_eq, adequacy hγ hv⟩

/-- Remark 14: adequacy fails at function types. `fun x:τ. (fun y:τ. y) x` and
`fun x:τ. x` have the same denotation, but the first is a value distinct from
the second, so it does not evaluate to it. -/
theorem not_eval_of_denote_eq_arrow (τ : Ty) :
    denote (.lam (.app (.lam Term.v0) Term.v0) : Closed p (τ ⤳ τ)) =
        denote (.lam Term.v0 : Closed p (τ ⤳ τ)) ∧
      ¬ (.lam (.app (.lam Term.v0) Term.v0) : Closed p (τ ⤳ τ)) ⇓ .lam Term.v0 := by
  refine ⟨ContinuousHom.ext _ _ fun ρ => Model.denote_lam_ext fun d => rfl, fun h => ?_⟩
  have h' := Eval.of_value (.lam _) h
  injection h' with _ _ _ h'
  cases h'

/-! ### Theorem 24 -/

/-- Soundness and adequacy in the form used by the abstract proof of
Theorem 24 (`TypedLambda.Observation.ctxLe_of_denote_le`). -/
theorem adequacy_of_eval {γ : Ty} (hγ : γ.IsGround) {t t' v : Closed p γ} (h : t' ⇓ v)
    (hle : denote v Tuple.nil ≤ denote t Tuple.nil) : t ⇓ v :=
  adequacy_le hγ h.value hle

/-- The denotational order implies the contextual preorder: if
`⟦t₁⟧ ⊑ ⟦t₂⟧` then `t₁ ≤ctx t₂`. An instance of
`TypedLambda.Observation.ctxLe_of_denote_le`. -/
theorem CtxLe.of_denote_le {Γ : Ctx Base} {τ : Ty} {t₁ t₂ : Term p Γ τ}
    (h : denote t₁ ≤ denote t₂) : t₁ ≤ctx t₂ :=
  Observation.ctxLe_of_denote_le (fun _ => Eval.denoteClosed_eq) adequacy_of_eval h

/-- Theorem 24, generalized to open terms: terms with equal denotations are
contextually equivalent. The proof combines soundness, compositionality and
adequacy (`TypedLambda.Observation.ctxEquiv_of_denote_eq`). -/
theorem CtxEquiv.of_denote_eq {Γ : Ctx Base} {τ : Ty} {t₁ t₂ : Term p Γ τ}
    (h : denote t₁ = denote t₂) : t₁ ≅ctx t₂ :=
  Observation.ctxEquiv_of_denote_eq (fun _ => Eval.denoteClosed_eq) adequacy_of_eval h

/-- Theorem 24 (semantic equality implies contextual equivalence): closed
terms `t₁, t₂ : τ` denoting the same element `⟦t₁⟧ = ⟦t₂⟧ ∈ ⟦τ⟧` are
contextually equivalent. -/
theorem CtxEquiv.of_denoteClosed_eq {τ : Ty} {t₁ t₂ : Closed p τ}
    (h : (model p).denoteClosed t₁ = (model p).denoteClosed t₂) : t₁ ≅ctx t₂ :=
  CtxEquiv.of_denote_eq (Model.denote_eq_iff_denoteClosed_eq.2 h)

/-- For closed terms: if `⟦t₁⟧ ⊑ ⟦t₂⟧` in `⟦τ⟧` then `t₁ ≤ctx t₂`. -/
theorem CtxLe.of_denoteClosed_le {τ : Ty} {t₁ t₂ : Closed p τ}
    (h : (model p).denoteClosed t₁ ≤ (model p).denoteClosed t₂) : t₁ ≤ctx t₂ :=
  CtxLe.of_denote_le (Model.denote_le_iff_denoteClosed_le.2 h)

end Silmaril.Calculi.PCF
