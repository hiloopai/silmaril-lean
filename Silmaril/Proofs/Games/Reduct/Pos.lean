module

public import Silmaril.Games.Reduct.Defs
public import Silmaril.Games.Play.Thms

/-!
# The plays of a reduct: positions

* `step_upRel`, `legal_of_upRel`: the preimage of a legal play under `UpRel ρ` is legal (the
  question of every answer is renamed along the function `ρ.op`).
* `redPos_step`, `redPos_path`: related moves from related positions reach related positions.
* `legal_mid`: if `s` and `p` are legal and `s` is related to `t` and `t` to `p`, then `t` is
  legal. The upper half of the position of `t` is read from `p`, the lower half from `s`.
-/

public section

namespace Silmaril.Proofs.Games.Reduct

open Silmaril.Games

universe u

/-! ## Preimages of upper images -/

section Up

variable {X G F : Sig.{u}} (ρ : Sig.Hom G F)

/-- Positions of a restriction as positions of the strategy. -/
def posUp : Pos X G → Pos X F
  | .idle => .idle
  | .run q => .run (ρ.op q)
  | .wait q m => .wait (ρ.op q) m

theorem step_upRel {a : Move X F} {b : Move X G} {x y : Pos X G} (hr : UpRel ρ a b)
    (h : Step x b y) : Step (posUp ρ x) a (posUp ρ y) := by
  cases hr with
  | low e =>
    cases e with
    | ask m => cases h with | call q _ => exact .call _ m
    | ans m n => cases h with | reply q _ _ => exact .reply _ m n
  | ask q => cases h with | ask _ => exact .ask _
  | ans q n => cases h with | ret _ _ => exact .ret _ n

theorem path_upRel {s : List (Move X F)} {p : List (Move X G)}
    (hr : List.Forall₂ (UpRel ρ) s p) :
    ∀ {x y : Pos X G}, Path x p y → Path (posUp ρ x) s (posUp ρ y) := by
  induction hr with
  | nil => intro x y h; cases h; exact .nil _
  | cons hab _ ih =>
    intro x y h
    cases h with
    | cons hs hp => exact .cons (step_upRel ρ hab hs) (ih hp)

/-- The preimage of a legal play under `UpRel ρ` is legal. -/
theorem legal_of_upRel {s : List (Move X F)} {p : List (Move X G)}
    (hr : List.Forall₂ (UpRel ρ) s p) (hp : Legal p) : Legal s := by
  obtain ⟨y, hy⟩ := hp
  exact ⟨_, path_upRel ρ hr hy⟩

end Up

/-! ## Related positions -/

section Pos

variable {E E' F F' : Sig.{u}} {lo : Sig.Hom E' E} {up : Sig.Hom F F'}

/-- Related moves from related positions reach related positions. -/
theorem redPos_step {a : Move E' F'} {b : Move E F} {xs xs' : Pos E' F'} {xp xp' : Pos E F}
    (hx : RedPos lo up xs xp) (hr : RedRel lo up a b) (hs : Step xs a xs') (hp : Step xp b xp') :
    RedPos lo up xs' xp' := by
  cases hr with
  | lask m =>
    cases hs with
    | call q₀ _ => cases hp with | call q _ => cases hx with | run _ => exact .wait q m
  | lans m n =>
    cases hs with
    | reply q₀ _ _ => cases hp with | reply q _ _ => cases hx with | wait _ _ => exact .run q
  | uask q => cases hs with | ask _ => cases hp with | ask _ => exact .run q
  | uans q n => cases hs with | ret _ _ => cases hp with | ret _ _ => exact .idle

/-- Related paths from related positions end in related positions. -/
theorem redPos_path {s : List (Move E' F')} {p : List (Move E F)}
    (hr : List.Forall₂ (RedRel lo up) s p) :
    ∀ {xs xs' : Pos E' F'} {xp xp' : Pos E F}, RedPos lo up xs xp → Path xs s xs' →
      Path xp p xp' → RedPos lo up xs' xp' := by
  induction hr with
  | nil => intro xs xs' xp xp' hx hs hp; cases hs; cases hp; exact hx
  | cons hab _ ih =>
    intro xs xs' xp xp' hx hs hp
    cases hs with
    | cons hs₁ hs₂ =>
      cases hp with
      | cons hp₁ hp₂ => exact ih (redPos_step hx hab hs₁ hp₁) hs₂ hp₂

end Pos

/-! ## The middle of two images -/

section Mid

variable {E E' E'' F F' F'' : Sig.{u}} {lo₁ : Sig.Hom E'' E'} {up₁ : Sig.Hom F' F''}
  {lo₂ : Sig.Hom E' E} {up₂ : Sig.Hom F F'}

/-- **Decomposition of the composite move relation.** -/
theorem redRel_decomp {a : Move E'' F''} {c : Move E F}
    (h : RedRel (lo₁.comp lo₂) (up₂.comp up₁) a c) :
    ∃ b, RedRel lo₁ up₁ a b ∧ RedRel lo₂ up₂ b c := by
  cases h with
  | lask m => exact ⟨_, .lask m, .lask (lo := lo₂) (up := up₂) (lo₁.op m)⟩
  | lans m n =>
    exact ⟨_, .lans (lo := lo₁) (up := up₁) m (lo₂.ar (lo₁.op m) n),
      .lans (lo := lo₂) (up := up₂) (lo₁.op m) n⟩
  | uask q => exact ⟨_, .uask (lo := lo₁) (up := up₁) (up₂.op q), .uask (lo := lo₂) (up := up₂) q⟩
  | uans q n =>
    exact ⟨_, .uans (lo := lo₁) (up := up₁) (up₂.op q) n,
      .uans (lo := lo₂) (up := up₂) q (up₁.ar (up₂.op q) n)⟩

/-- Decomposition of the composite move relation, on plays. -/
theorem forall₂_decomp {s : List (Move E'' F'')} {p : List (Move E F)}
    (h : List.Forall₂ (RedRel (lo₁.comp lo₂) (up₂.comp up₁)) s p) :
    ∃ t, List.Forall₂ (RedRel lo₁ up₁) s t ∧ List.Forall₂ (RedRel lo₂ up₂) t p := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons hac _ ih =>
    obtain ⟨b, hab, hbc⟩ := redRel_decomp hac
    obtain ⟨t, h₁, h₂⟩ := ih
    exact ⟨b :: t, .cons hab h₁, .cons hbc h₂⟩

/-- One move of the middle play: its position is read from the two outer positions. -/
theorem step_mid {a : Move E'' F''} {b : Move E' F'} {c : Move E F} {xs xs' : Pos E'' F''}
    {xt : Pos E' F'} {xp xp' : Pos E F} (h₁ : RedRel lo₁ up₁ a b) (h₂ : RedRel lo₂ up₂ b c)
    (hs : Step xs a xs') (hp : Step xp c xp') (hst : RedPos lo₁ up₁ xs xt)
    (htp : RedPos lo₂ up₂ xt xp) :
    ∃ xt', Step xt b xt' ∧ RedPos lo₁ up₁ xs' xt' ∧ RedPos lo₂ up₂ xt' xp' := by
  cases h₁ with
  | lask m =>
    show ∃ xt', Step _ _ xt' ∧ _
    cases h₂ with
    | lask _ =>
      cases hs with
      | call _ _ =>
        cases hp with
        | call qp _ =>
          cases hst with
          | run _ => cases htp with | run _ => exact ⟨_, .call _ _, .wait _ m, .wait qp _⟩
  | lans m n =>
    show ∃ xt', Step _ _ xt' ∧ _
    cases h₂ with
    | lans _ n' =>
      cases hs with
      | reply _ _ _ =>
        cases hp with
        | reply qp _ _ =>
          cases hst with
          | wait _ _ => cases htp with | wait _ _ => exact ⟨_, .reply _ _ _, .run _, .run qp⟩
  | uask q =>
    show ∃ xt', Step _ _ xt' ∧ _
    cases h₂ with
    | uask q' =>
      cases hs with
      | ask _ =>
        cases hp with
        | ask _ => cases htp with | idle => exact ⟨_, .ask _, .run _, .run q'⟩
  | uans q n =>
    show ∃ xt', Step _ _ xt' ∧ _
    cases h₂ with
    | uans q' _ =>
      cases hs with
      | ret _ _ =>
        cases hp with
        | ret _ _ => cases htp with | run _ => exact ⟨_, .ret _ _, .idle, .idle⟩

/-- Paths of the middle play. -/
theorem path_mid {s : List (Move E'' F'')} {t : List (Move E' F')}
    (h₁ : List.Forall₂ (RedRel lo₁ up₁) s t) :
    ∀ {p : List (Move E F)}, List.Forall₂ (RedRel lo₂ up₂) t p →
      ∀ {xs xs₁ : Pos E'' F''} {xt : Pos E' F'} {xp xp₁ : Pos E F}, Path xs s xs₁ →
        Path xp p xp₁ → RedPos lo₁ up₁ xs xt → RedPos lo₂ up₂ xt xp → ∃ xt₁, Path xt t xt₁ := by
  induction h₁ with
  | nil => intro _ _ _ _ xt _ _ _ _ _ _; exact ⟨xt, .nil _⟩
  | cons hab _ ih =>
    intro p h₂ xs xs₁ xt xp xp₁ hs hp hst htp
    cases h₂ with
    | cons hbc h₂' =>
      cases hs with
      | cons hs₁ hs₂ =>
        cases hp with
        | cons hp₁ hp₂ =>
          obtain ⟨xt', hxt, hst', htp'⟩ := step_mid hab hbc hs₁ hp₁ hst htp
          obtain ⟨xt₁, ht⟩ := ih h₂' hs₂ hp₂ hst' htp'
          exact ⟨xt₁, .cons hxt ht⟩

/-- **The middle of two images of legal plays is legal.** -/
theorem legal_mid {s : List (Move E'' F'')} {t : List (Move E' F')} {p : List (Move E F)}
    (h₁ : List.Forall₂ (RedRel lo₁ up₁) s t) (h₂ : List.Forall₂ (RedRel lo₂ up₂) t p)
    (hs : Legal s) (hp : Legal p) : Legal t := by
  obtain ⟨_, hxs⟩ := hs
  obtain ⟨_, hxp⟩ := hp
  exact path_mid h₁ h₂ hxs hxp .idle .idle

end Mid

/-! ## Images of legal plays along injective upper renamings -/

section Inj

variable {E E' F F' : Sig.{u}} {lo : Sig.Hom E' E} {up : Sig.Hom F F'}

/-- Inversion of a running related position. -/
theorem redPos_run_inv {q' : F'.Op} {xp : Pos E F} (h : RedPos lo up (.run q') xp) :
    ∃ q, q' = up.op q ∧ xp = .run q := by
  cases h with
  | run q => exact ⟨q, rfl, rfl⟩

/-- With an injective upper renaming, a related move from a related position is legal. -/
theorem step_of_inj (hinj : Function.Injective up.op) {a : Move E' F'} {b : Move E F}
    {xs xs' : Pos E' F'} {xp : Pos E F} (hr : RedRel lo up a b) (hs : Step xs a xs')
    (hx : RedPos lo up xs xp) : ∃ xp', Step xp b xp' ∧ RedPos lo up xs' xp' := by
  cases hr with
  | lask m =>
    cases hs with
    | call _ _ => cases hx with | run q => exact ⟨_, .call q _, .wait q m⟩
  | lans m n =>
    cases hs with
    | reply _ _ _ => cases hx with | wait q _ => exact ⟨_, .reply q _ n, .run q⟩
  | uask q => cases hs with | ask _ => cases hx with | idle => exact ⟨_, .ask q, .run q⟩
  | uans q n =>
    cases hs with
    | ret _ _ =>
      obtain ⟨q₁, hq, rfl⟩ := redPos_run_inv hx
      cases hinj hq
      exact ⟨_, .ret q _, .idle⟩

/-- With an injective upper renaming, the image of a legal play is legal. -/
theorem legal_of_inj (hinj : Function.Injective up.op) {s : List (Move E' F')}
    {p : List (Move E F)} (hr : List.Forall₂ (RedRel lo up) s p) (hs : Legal s) : Legal p := by
  obtain ⟨_, hxs⟩ := hs
  suffices h : ∀ {s : List (Move E' F')} {p : List (Move E F)},
      List.Forall₂ (RedRel lo up) s p → ∀ {xs xs₁ : Pos E' F'} {xp : Pos E F},
        Path xs s xs₁ → RedPos lo up xs xp → ∃ xp₁, Path xp p xp₁ from
    h hr hxs .idle
  intro s p hr
  induction hr with
  | nil => intro xs xs₁ xp _ _; exact ⟨xp, .nil _⟩
  | cons hab _ ih =>
    intro xs xs₁ xp hs hx
    cases hs with
    | cons hs₁ hs₂ =>
      obtain ⟨xp', hxp, hx'⟩ := step_of_inj hinj hab hs₁ hx
      obtain ⟨xp₁, hp⟩ := ih hs₂ hx'
      exact ⟨xp₁, .cons hxp hp⟩

end Inj

end Silmaril.Proofs.Games.Reduct
