module

public import Mathlib.Data.Set.Basic

/-! # §17 Effect systems (notes pp. 30–31; slides pp. 108–112)

The language (notes p. 30)

  `e ::= x | λx.e | e₁ e₂ | ξ?x.e | ξ!e₁.e₂ | if e₁ then e₂ else e₃`

(plus integer constants), where `ξ?x.e` reads an integer from channel `ξ` and
`ξ!e₁.e₂` writes the value of `e₁` to `ξ`. Effects `F` are sets of `Rξ` and
`Wξ`, and function types carry their *latent* effect, `t →ᶠ t′`. The rules
(VAR), (READ), (WRITE), (LAM), (APP) are those of notes p. 31; (SUB) is the
subeffecting rule of the slides (p. 111), letting an expression with fewer
effects be used where more are allowed.

Safety: the effects of every evaluation are among the inferred effects
(`Derives.sound`). The semantics is call-by-value big-step evaluation of
closed terms by substitution, recording the channel events in order; a read
may receive any integer.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.EffectSystems

/-- Channels. -/
abbrev Chan := String

/-- Atomic effects: `Rξ` and `Wξ`. -/
inductive Eff where
  | read (ξ : Chan)
  | write (ξ : Chan)
  deriving DecidableEq

/-- Types `t ::= int | t →ᶠ t′`. -/
inductive Ty where
  | int
  | arrow (a : Ty) (F : Set Eff) (b : Ty)

/-- Terms. -/
inductive Term where
  | var (x : String)
  | lit (n : ℤ)
  | lam (x : String) (e : Term)
  | app (f a : Term)
  | recv (ξ : Chan) (x : String) (e : Term)
  | send (ξ : Chan) (e₁ e₂ : Term)
  | ite (c t e : Term)

/-- Contexts. -/
abbrev Ctx := String → Option Ty

/-- `Γ ⊢ e : t, F` (notes p. 31; (SUB) from the slides). -/
inductive Derives : Ctx → Term → Ty → Set Eff → Prop where
  | var {Γ x t} : Γ x = some t → Derives Γ (.var x) t ∅
  | lit {Γ n} : Derives Γ (.lit n) .int ∅
  | recv {Γ ξ x e t F} : Derives (Function.update Γ x (some .int)) e t F →
      Derives Γ (.recv ξ x e) t ({.read ξ} ∪ F)
  | send {Γ ξ e₁ e₂ t F F'} : Derives Γ e₁ .int F → Derives Γ e₂ t F' →
      Derives Γ (.send ξ e₁ e₂) t (F ∪ {.write ξ} ∪ F')
  | lam {Γ x e t t' F} : Derives (Function.update Γ x (some t)) e t' F →
      Derives Γ (.lam x e) (.arrow t F t') ∅
  | app {Γ f a t t' F F' F''} : Derives Γ f (.arrow t F'' t') F → Derives Γ a t F' →
      Derives Γ (.app f a) t' (F ∪ F' ∪ F'')
  | ite {Γ c e₁ e₂ t F F₁ F₂} : Derives Γ c .int F → Derives Γ e₁ t F₁ → Derives Γ e₂ t F₂ →
      Derives Γ (.ite c e₁ e₂) t (F ∪ F₁ ∪ F₂)
  | sub {Γ e t F F'} : Derives Γ e t F → F ⊆ F' → Derives Γ e t F'

namespace Term

/-- Substitution of a closed term for a variable (no capture is possible). -/
def subst (x : String) (v : Term) : Term → Term
  | var y => if y = x then v else var y
  | lit n => lit n
  | lam y e => if y = x then lam y e else lam y (subst x v e)
  | app f a => app (subst x v f) (subst x v a)
  | recv ξ y e => if y = x then recv ξ y e else recv ξ y (subst x v e)
  | send ξ e₁ e₂ => send ξ (subst x v e₁) (subst x v e₂)
  | ite c t e => ite (subst x v c) (subst x v t) (subst x v e)

end Term

/-- Call-by-value evaluation `e ⇓ v` with the channel events performed. -/
inductive Eval : Term → List Eff → Term → Prop where
  | lit {n} : Eval (.lit n) [] (.lit n)
  | lam {x e} : Eval (.lam x e) [] (.lam x e)
  -- Substitute the argument value into the function body: `body[x := v]`.
  | app {f a x body v r ef ea eb} : Eval f ef (.lam x body) → Eval a ea v →
      Eval (Term.subst x v body) eb r → Eval (.app f a) (ef ++ ea ++ eb) r
  -- Substitute the received value into the continuation: `e[x := n]`.
  | recv {ξ x e n w r} : Eval (Term.subst x (.lit n) e) w r → Eval (.recv ξ x e) (.read ξ :: w) r
  | send {ξ e₁ e₂ n w₁ w₂ r} : Eval e₁ w₁ (.lit n) → Eval e₂ w₂ r →
      Eval (.send ξ e₁ e₂) (w₁ ++ .write ξ :: w₂) r
  | iteT {c e₁ e₂ n w w₁ r} : Eval c w (.lit n) → n ≠ 0 → Eval e₁ w₁ r →
      Eval (.ite c e₁ e₂) (w ++ w₁) r
  | iteF {c e₁ e₂ w w₂ r} : Eval c w (.lit 0) → Eval e₂ w₂ r → Eval (.ite c e₁ e₂) (w ++ w₂) r

/-- Effect soundness: the events of an evaluation of a closed, well-typed term
are among its inferred effects. -/
theorem update_mono {Γ Γ' : Ctx} (hΓ : ∀ x s, Γ x = some s → Γ' x = some s) (y : String)
    (u : Option Ty) :
    ∀ x s, Function.update Γ y u x = some s → Function.update Γ' y u x = some s := by
  intro x s hs
  by_cases hx : x = y
  · subst hx; simpa using hs
  · rw [Function.update_of_ne hx] at hs ⊢; exact hΓ _ _ hs

namespace Derives

theorem weaken {Γ Γ' : Ctx} {e : Term} {t : Ty} {F : Set Eff} (h : Derives Γ e t F)
    (hΓ : ∀ x s, Γ x = some s → Γ' x = some s) : Derives Γ' e t F := by
  induction h generalizing Γ' with
  | var h => exact .var (hΓ _ _ h)
  | lit => exact .lit
  | recv _ ih => exact .recv (ih (update_mono hΓ _ _))
  | send _ _ ih₁ ih₂ => exact .send (ih₁ hΓ) (ih₂ hΓ)
  | lam _ ih => exact .lam (ih (update_mono hΓ _ _))
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hΓ) (ih₂ hΓ)
  | ite _ _ _ ih₀ ih₁ ih₂ => exact .ite (ih₀ hΓ) (ih₁ hΓ) (ih₂ hΓ)
  | sub _ hF ih => exact .sub (ih hΓ) hF

/-- Substituting a closed value preserves typing and effects. -/
theorem subst_preserves {Γ : Ctx} {x : String} {s : Ty} {v : Term}
    (hv : Derives (fun _ => none) v s ∅) {e : Term} {t : Ty} {F : Set Eff}
    (hd : Derives (Function.update Γ x (some s)) e t F) : Derives Γ (Term.subst x v e) t F := by
  generalize hΔ : Function.update Γ x (some s) = Δ at hd
  induction hd generalizing Γ with
  | @var Δ y t h =>
    subst hΔ
    by_cases hy : y = x
    · subst hy
      simp at h
      subst h
      simp only [Term.subst, ↓reduceIte]
      exact hv.weaken (by intro _ _ h; cases h)
    · rw [Function.update_of_ne hy] at h
      simp only [Term.subst, hy, ↓reduceIte]
      exact .var h
  | lit => exact .lit
  | @recv Δ ξ y e t F hd ih =>
    subst hΔ
    by_cases hy : y = x
    · subst hy
      simp only [Term.subst, ↓reduceIte]
      exact .recv (by rwa [Function.update_idem] at hd)
    · simp only [Term.subst, hy, ↓reduceIte]
      exact .recv (ih (Function.update_comm hy _ _ _))
  | send _ _ ih₁ ih₂ => subst hΔ; exact .send (ih₁ rfl) (ih₂ rfl)
  | @lam Δ y e t t' F hd ih =>
    subst hΔ
    by_cases hy : y = x
    · subst hy
      simp only [Term.subst, ↓reduceIte]
      exact .lam (by rwa [Function.update_idem] at hd)
    · simp only [Term.subst, hy, ↓reduceIte]
      exact .lam (ih (Function.update_comm hy _ _ _))
  | app _ _ ih₁ ih₂ => subst hΔ; exact .app (ih₁ rfl) (ih₂ rfl)
  | ite _ _ _ ih₀ ih₁ ih₂ => subst hΔ; exact .ite (ih₀ rfl) (ih₁ rfl) (ih₂ rfl)
  | sub _ hF ih => subst hΔ; exact .sub (ih rfl) hF

theorem lit_strip {Γ : Ctx} {n : ℤ} {t : Ty} {F : Set Eff} (h : Derives Γ (.lit n) t F) :
    Derives Γ (.lit n) t ∅ := by
  generalize he : Term.lit n = e at h
  induction h with
  | lit => exact .lit
  | sub _ _ ih => exact ih he
  | _ => cases he

theorem lam_strip {Γ : Ctx} {x : String} {b : Term} {t : Ty} {F : Set Eff}
    (h : Derives Γ (.lam x b) t F) : Derives Γ (.lam x b) t ∅ := by
  generalize he : Term.lam x b = e at h
  induction h with
  | lam hd _ => cases he; exact .lam hd
  | sub _ _ ih => exact ih he
  | _ => cases he

theorem lam_inv {Γ : Ctx} {x : String} {b : Term} {t t' : Ty} {F G : Set Eff}
    (h : Derives Γ (.lam x b) (.arrow t F t') G) :
    Derives (Function.update Γ x (some t)) b t' F := by
  generalize he : Term.lam x b = e at h
  generalize ht : Ty.arrow t F t' = ty at h
  induction h with
  | lam hd _ => cases he; cases ht; exact hd
  | sub _ _ ih => exact ih he ht
  | _ => cases he

theorem app_inv {Γ : Ctx} {f a : Term} {t' : Ty} {F : Set Eff} (h : Derives Γ (.app f a) t' F) :
    ∃ t F₁ F₂ F₃, Derives Γ f (.arrow t F₃ t') F₁ ∧ Derives Γ a t F₂ ∧ F₁ ∪ F₂ ∪ F₃ ⊆ F := by
  generalize he : Term.app f a = e at h
  induction h with
  | app h₁ h₂ _ _ => cases he; exact ⟨_, _, _, _, h₁, h₂, Set.Subset.rfl⟩
  | sub _ hF ih =>
    obtain ⟨t, F₁, F₂, F₃, h₁, h₂, hs⟩ := ih he
    exact ⟨t, F₁, F₂, F₃, h₁, h₂, hs.trans hF⟩
  | _ => cases he

theorem recv_inv {Γ : Ctx} {ξ : Chan} {x : String} {e : Term} {t : Ty} {F : Set Eff}
    (h : Derives Γ (.recv ξ x e) t F) :
    ∃ F', Derives (Function.update Γ x (some .int)) e t F' ∧ {.read ξ} ∪ F' ⊆ F := by
  generalize he : Term.recv ξ x e = e' at h
  induction h with
  | recv h _ => cases he; exact ⟨_, h, Set.Subset.rfl⟩
  | sub _ hF ih =>
    obtain ⟨F', h, hs⟩ := ih he
    exact ⟨F', h, hs.trans hF⟩
  | _ => cases he

theorem send_inv {Γ : Ctx} {ξ : Chan} {e₁ e₂ : Term} {t : Ty} {F : Set Eff}
    (h : Derives Γ (.send ξ e₁ e₂) t F) :
    ∃ F₁ F₂, Derives Γ e₁ .int F₁ ∧ Derives Γ e₂ t F₂ ∧ F₁ ∪ {.write ξ} ∪ F₂ ⊆ F := by
  generalize he : Term.send ξ e₁ e₂ = e' at h
  induction h with
  | send h₁ h₂ _ _ => cases he; exact ⟨_, _, h₁, h₂, Set.Subset.rfl⟩
  | sub _ hF ih =>
    obtain ⟨F₁, F₂, h₁, h₂, hs⟩ := ih he
    exact ⟨F₁, F₂, h₁, h₂, hs.trans hF⟩
  | _ => cases he

theorem ite_inv {Γ : Ctx} {c e₁ e₂ : Term} {t : Ty} {F : Set Eff}
    (h : Derives Γ (.ite c e₁ e₂) t F) :
    ∃ F₀ F₁ F₂, Derives Γ c .int F₀ ∧ Derives Γ e₁ t F₁ ∧ Derives Γ e₂ t F₂ ∧
      F₀ ∪ F₁ ∪ F₂ ⊆ F := by
  generalize he : Term.ite c e₁ e₂ = e' at h
  induction h with
  | ite h₀ h₁ h₂ _ _ _ => cases he; exact ⟨_, _, _, h₀, h₁, h₂, Set.Subset.rfl⟩
  | sub _ hF ih =>
    obtain ⟨F₀, F₁, F₂, h₀, h₁, h₂, hs⟩ := ih he
    exact ⟨F₀, F₁, F₂, h₀, h₁, h₂, hs.trans hF⟩
  | _ => cases he

end Derives

/-- Effect soundness together with type preservation. -/
theorem eval_sound {e : Term} {w : List Eff} {v : Term} (he : Eval e w v) :
    ∀ {t : Ty} {F : Set Eff}, Derives (fun _ => none) e t F →
      (∀ ε ∈ w, ε ∈ F) ∧ Derives (fun _ => none) v t ∅ := by
  induction he with
  | lit => intro t F hd; exact ⟨by simp, hd.lit_strip⟩
  | lam => intro t F hd; exact ⟨by simp, hd.lam_strip⟩
  | app _ _ _ ihf iha ihb =>
    intro t F hd
    obtain ⟨t₀, F₁, F₂, F₃, hf, ha, hs⟩ := hd.app_inv
    obtain ⟨wf, vf⟩ := ihf hf
    obtain ⟨wa, va⟩ := iha ha
    obtain ⟨wb, vb⟩ := ihb (Derives.subst_preserves va vf.lam_inv)
    refine ⟨fun ε hε => ?_, vb⟩
    simp only [List.mem_append] at hε
    rcases hε with (hε | hε) | hε
    · exact hs (Set.mem_union_left _ (Set.mem_union_left _ (wf ε hε)))
    · exact hs (Set.mem_union_left _ (Set.mem_union_right _ (wa ε hε)))
    · exact hs (Set.mem_union_right _ (wb ε hε))
  | recv _ ih =>
    intro t F hd
    obtain ⟨F', hd', hs⟩ := hd.recv_inv
    obtain ⟨w', v'⟩ := ih (Derives.subst_preserves .lit hd')
    refine ⟨fun ε hε => ?_, v'⟩
    rcases List.mem_cons.1 hε with rfl | hε
    · exact hs (Set.mem_union_left _ (rfl))
    · exact hs (Set.mem_union_right _ (w' ε hε))
  | send _ _ ih₁ ih₂ =>
    intro t F hd
    obtain ⟨F₁, F₂, h₁, h₂, hs⟩ := hd.send_inv
    obtain ⟨w₁', -⟩ := ih₁ h₁
    obtain ⟨w₂', v₂⟩ := ih₂ h₂
    refine ⟨fun ε hε => ?_, v₂⟩
    simp only [List.mem_append, List.mem_cons] at hε
    rcases hε with hε | rfl | hε
    · exact hs (Set.mem_union_left _ (Set.mem_union_left _ (w₁' ε hε)))
    · exact hs (Set.mem_union_left _ (Set.mem_union_right _ (rfl)))
    · exact hs (Set.mem_union_right _ (w₂' ε hε))
  | iteT _ _ _ ihc ih₁ =>
    intro t F hd
    obtain ⟨F₀, F₁, F₂, h₀, h₁, -, hs⟩ := hd.ite_inv
    obtain ⟨w₀, -⟩ := ihc h₀
    obtain ⟨w₁', v₁⟩ := ih₁ h₁
    refine ⟨fun ε hε => ?_, v₁⟩
    rcases List.mem_append.1 hε with hε | hε
    · exact hs (Set.mem_union_left _ (Set.mem_union_left _ (w₀ ε hε)))
    · exact hs (Set.mem_union_left _ (Set.mem_union_right _ (w₁' ε hε)))
  | iteF _ _ ihc ih₂ =>
    intro t F hd
    obtain ⟨F₀, F₁, F₂, h₀, -, h₂, hs⟩ := hd.ite_inv
    obtain ⟨w₀, -⟩ := ihc h₀
    obtain ⟨w₂', v₂⟩ := ih₂ h₂
    refine ⟨fun ε hε => ?_, v₂⟩
    rcases List.mem_append.1 hε with hε | hε
    · exact hs (Set.mem_union_left _ (Set.mem_union_left _ (w₀ ε hε)))
    · exact hs (Set.mem_union_right _ (w₂' ε hε))

theorem Derives.sound {e : Term} {t : Ty} {F : Set Eff} (hd : Derives (fun _ => none) e t F)
    {w : List Eff} {v : Term} (he : Eval e w v) : ∀ ε ∈ w, ε ∈ F :=
  (eval_sound he hd).1

/-- The notes' example (p. 31): `ξ!1.λx.ζ!2.x` has immediate effect `{Wξ}` and
latent effect `{Wζ}`. -/
theorem notesExample :
    Derives (fun _ => none) (.send "ξ" (.lit 1) (.lam "x" (.send "ζ" (.lit 2) (.var "x"))))
      (.arrow .int {.write "ζ"} .int) {.write "ξ"} := by
  have h₁ : Derives (Function.update (fun _ => none) "x" (some .int))
      (.send "ζ" (.lit 2) (.var "x")) .int {.write "ζ"} :=
    .sub (.send .lit (.var (by simp))) (by simp)
  exact .sub (.send .lit (.lam h₁)) (by simp)

end Silmaril.Courses.Cambridge.OptimisingCompilers.EffectSystems
