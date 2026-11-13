module

public import Silmaril.Games.Reduct.Defs
public import Silmaril.Games.Institution.Thms

/-!
# The plays of a reduct: soundness

Every play of `Game.reduct f σ` is a `RedRel`-image of a play of `σ`.

* The upper half (`restrict_sound'`): the invariant of `Silmaril.Proofs.Games.Institution.Upper`
  shows that a question received but not yet forwarded is asked from an idle position, so by
  receptiveness `σ` accepts it too, and the image has no trailing question left over.
* The lower half (`lower_sound`): the run of `(Fwd lo).toLTS.comp τ.toLTS`, with the invariant
  `LInv`. A lower answer received but not yet forwarded is accepted by `τ` (receptiveness).
* `RedRel.comp_id`: an upper image followed by a lower image is a `RedRel`-image.
-/

public section

namespace Silmaril.Proofs.Games.Reduct

open Silmaril.Games Silmaril.Proofs.Games.Institution

universe u

/-! ## Moves -/

/-- An upper image as a `RedRel`-image with identity lower renaming. -/
theorem redRel_of_upRel {X G F : Sig.{u}} {ρ : Sig.Hom G F} {a : Move X F} {b : Move X G}
    (h : UpRel ρ a b) : RedRel (Sig.Hom.id X) ρ a b := by
  cases h with
  | low e =>
    cases e with
    | ask m => exact .lask (lo := Sig.Hom.id X) (up := ρ) m
    | ans m n => exact .lans (lo := Sig.Hom.id X) (up := ρ) m n
  | ask q => exact .uask q
  | ans q n => exact .uans (lo := Sig.Hom.id X) (up := ρ) q n

/-- Upper moves are unchanged by a reduct with identity upper renaming. -/
theorem redRel_up_id {E E' F : Sig.{u}} (lo : Sig.Hom E' E) (g : Ev F) :
    RedRel lo (Sig.Hom.id F) (.inr g) (.inr g) := by
  cases g with
  | ask q => exact .uask (lo := lo) (up := Sig.Hom.id F) q
  | ans q n => exact .uans (lo := lo) (up := Sig.Hom.id F) q n

/-- **Composition of move relations.** -/
theorem RedRel.comp {E E' E'' F F' F'' : Sig.{u}} {lo₁ : Sig.Hom E'' E'} {up₁ : Sig.Hom F' F''}
    {lo₂ : Sig.Hom E' E} {up₂ : Sig.Hom F F'} {a : Move E'' F''} {b : Move E' F'}
    {c : Move E F} (h₁ : RedRel lo₁ up₁ a b) (h₂ : RedRel lo₂ up₂ b c) :
    RedRel (lo₁.comp lo₂) (up₂.comp up₁) a c := by
  cases h₁ with
  | lask m => cases h₂ with | lask _ => exact .lask (lo := lo₁.comp lo₂) (up := up₂.comp up₁) m
  | lans m n =>
    cases h₂ with | lans _ n' => exact .lans (lo := lo₁.comp lo₂) (up := up₂.comp up₁) m n'
  | uask q => cases h₂ with | uask q' => exact .uask (lo := lo₁.comp lo₂) (up := up₂.comp up₁) q'
  | uans q n =>
    cases h₂ with | uans q' _ => exact .uans (lo := lo₁.comp lo₂) (up := up₂.comp up₁) q' n

/-- Lists related by two move relations are related by their composite. -/
theorem forall₂_comp {E E' E'' F F' F'' : Sig.{u}} {lo₁ : Sig.Hom E'' E'}
    {up₁ : Sig.Hom F' F''} {lo₂ : Sig.Hom E' E} {up₂ : Sig.Hom F F'} {s : List (Move E'' F'')}
    {t : List (Move E' F')} {p : List (Move E F)} (h₁ : List.Forall₂ (RedRel lo₁ up₁) s t)
    (h₂ : List.Forall₂ (RedRel lo₂ up₂) t p) :
    List.Forall₂ (RedRel (lo₁.comp lo₂) (up₂.comp up₁)) s p := by
  induction h₁ generalizing p with
  | nil => cases h₂; exact .nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc hr => exact .cons (RedRel.comp hab hbc) (ih hr)

/-- Upper images as `RedRel`-images, on plays. -/
theorem forall₂_upRel {X G F : Sig.{u}} {ρ : Sig.Hom G F} {s : List (Move X F)}
    {p : List (Move X G)} (h : List.Forall₂ (UpRel ρ) s p) :
    List.Forall₂ (RedRel (Sig.Hom.id X) ρ) s p := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (redRel_of_upRel hab) ih

/-- Extending related plays by related moves. -/
theorem forall₂_snoc {α β : Type u} {R : α → β → Prop} {s : List α} {p : List β} {a : α} {b : β}
    (h : List.Forall₂ R s p) (hab : R a b) : List.Forall₂ R (s ++ [a]) (p ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h₁ _ ih => exact .cons h₁ ih

/-! ## The upper half -/

/-- **Soundness of restriction**, without a trailing question: every play of `σ.restrict ρ` is
the `UpRel ρ`-image of a play of `σ`. -/
theorem restrict_sound' {X G F : Sig.{u}} (σ : Strategy X F) (ρ : Sig.Hom G F)
    {p : List (Move X G)} (hp : p ∈ σ.restrict ρ) :
    ∃ s ∈ σ, List.Forall₂ (UpRel ρ) s p := by
  have hd := LTS.Denotes.comp σ.denotes_toLTS (Handler.ofHom ρ).denotes_toLTS
  obtain ⟨y, hy⟩ := (hd p).2 hp
  have hi : Inv σ ρ y ([] ++ p) :=
    inv_run σ ρ hy [] ⟨σ.nil_mem, .nil _, .nil⟩
  rw [List.nil_append] at hi
  match y, hi with
  | (s, .idle), ⟨hs, _, hr⟩ => exact ⟨s, hs, hr⟩
  | (s, .run q _), .inl ⟨_, hs, hpath, p', hp', hr⟩ =>
    refine ⟨s ++ [.inr (.ask (ρ.op q))], σ.receptive hs hpath (Step.ask (ρ.op q)) (by exact trivial), ?_⟩
    rw [hp']
    exact forall₂_snoc hr (.ask q)
  | (_, .run _ _), .inr ⟨_, s₀, _, rfl, hs, hr⟩ =>
    exact ⟨s₀, σ.of_prefix hs (List.prefix_append _ _), hr⟩
  | (s, .wait _ _ _), ⟨_, _, hs, hr⟩ => exact ⟨s, hs, hr⟩

/-! ## The lower half -/

section Lower

variable {E E' F : Sig.{u}} (lo : Sig.Hom E' E) (τ : Strategy E' F)

/-- The reduction semantics of the lower forwarding handler. -/
abbrev FwdL : Reduction E E' := (Handler.ofHom lo).toReduction

/-- The forwarding continuation of the lower question `m`. -/
abbrev kontL (m : E'.Op) : E.Ar (lo.op m) → Prog E (E'.Ar m) := fun n => .pure (lo.ar m n)

/-- The lower relation: `RedRel` with identity upper renaming. -/
abbrev LRel : Move E' F → Move E F → Prop := RedRel lo (Sig.Hom.id F)

/-- The invariant of the lower forwarding run. -/
def LInv : (FwdL lo).State × List (Move E' F) → List (Move E F) → Prop
  | (.idle, t), p => t ∈ τ ∧ List.Forall₂ (LRel lo) t p
  | (.run m c, t), p =>
      (c = Handler.ofHom lo m ∧ t ∈ τ ∧ ∃ t', t = t' ++ [.inl (.ask m)] ∧
        List.Forall₂ (LRel lo) t' p) ∨
      (∃ n p', c = .pure (lo.ar m n) ∧ p = p' ++ [.inl (.ans (lo.op m) n)] ∧ t ∈ τ ∧
        (∃ q, Path .idle t (.wait q m)) ∧ List.Forall₂ (LRel lo) t p')
  | (.wait m m₀ k, t), p =>
      m₀ = lo.op m ∧ HEq k (kontL lo m) ∧ t ∈ τ ∧ (∃ q, Path .idle t (.wait q m)) ∧
        List.Forall₂ (LRel lo) t p

omit lo in
/-- A play whose last move is a lower question ends waiting for its answer. -/
theorem wait_of_ask {t : List (Move E' F)} {m : E'.Op} (h : Legal (t ++ [.inl (.ask m)])) :
    ∃ q, Path .idle (t ++ [.inl (.ask m)]) (.wait q m) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨x, -, hx⟩ := Path.concat_iff.1 hy
  cases hx with
  | call q _ => exact ⟨q, hy⟩

omit lo in
/-- No upper move is legal while waiting for a lower answer. -/
theorem no_up_of_wait {t : List (Move E' F)} {q : F.Op} {m : E'.Op} {g : Ev F}
    (h : Path .idle t (.wait q m)) (hl : Legal (t ++ [.inr g])) : False := by
  obtain ⟨_, hp⟩ := hl
  obtain ⟨x, hx, hxg⟩ := Path.concat_iff.1 hp
  cases Path.det hx h
  cases hxg

/-- A forwarder move at the lower interface keeps the invariant. -/
theorem linv_left {z z' : (FwdL lo).State} {t : List (Move E' F)} {e : Ev E}
    {p : List (Move E F)} (h : (FwdL lo).Step z (some (.inl e)) z') (hi : LInv lo τ (z, t) p) :
    LInv lo τ (z', t) (p ++ [.inl e]) := by
  cases h with
  | @call m c m₀ k hc =>
    rcases hi with ⟨hc', ht, t', rfl, hr⟩ | ⟨n, p', hc', -⟩
    · rw [hc'] at hc
      cases hc
      obtain ⟨q, hq⟩ := wait_of_ask (τ.legal ht)
      exact ⟨rfl, HEq.rfl, ht, ⟨q, hq⟩, forall₂_snoc hr (.lask m)⟩
    · rw [hc'] at hc
      cases hc
  | resume m m₀ k n =>
    obtain ⟨rfl, hk, ht, hw, hr⟩ := hi
    cases hk
    exact .inr ⟨n, p, rfl, rfl, ht, hw, hr⟩

/-- An upper move of `τ` keeps the invariant: it happens only while the forwarder is idle. -/
theorem linv_right {z : (FwdL lo).State} {t : List (Move E' F)} {g : Ev F}
    {p : List (Move E F)} (hm : t ++ [.inr g] ∈ τ) (hi : LInv lo τ (z, t) p) :
    LInv lo τ (z, t ++ [.inr g]) (p ++ [.inr g]) := by
  rcases z with _ | ⟨m, c⟩ | ⟨m, m₀, k⟩
  · exact ⟨hm, forall₂_snoc hi.2 (redRel_up_id lo g)⟩
  · rcases hi with ⟨-, ht, t', rfl, -⟩ | ⟨-, -, -, -, -, ⟨q, hq⟩, -⟩
    · obtain ⟨q, hq⟩ := wait_of_ask (τ.legal ht)
      exact (no_up_of_wait hq (τ.legal hm)).elim
    · exact (no_up_of_wait hq (τ.legal hm)).elim
  · obtain ⟨-, -, -, ⟨q, hq⟩, -⟩ := hi
    exact (no_up_of_wait hq (τ.legal hm)).elim

/-- A hidden synchronisation of the forwarder with `τ` keeps the invariant. -/
theorem linv_sync {z z' : (FwdL lo).State} {t : List (Move E' F)} {f : Ev E'}
    {p : List (Move E F)} (hm : t ++ [.inl f] ∈ τ) (h : (FwdL lo).Step z (some (.inr f)) z')
    (hi : LInv lo τ (z, t) p) : LInv lo τ (z', t ++ [.inl f]) p := by
  cases h with
  | ask m => exact .inl ⟨rfl, hm, t, rfl, hi.2⟩
  | @ret m c r hd =>
    rcases hi with ⟨hc, -⟩ | ⟨n, p', hc, rfl, -, -, hr⟩
    · rw [hc] at hd
      cases hd
    · rw [hc] at hd
      cases hd
      exact ⟨hm, forall₂_snoc hr (.lans m n)⟩

/-- One step of the lower forwarding run keeps the invariant. -/
theorem linv_step {x y : ((FwdL lo).toLTS.comp τ.toLTS).State} {l : Option (Move E F)}
    {p : List (Move E F)} (hst : LTS.CompStep (FwdL lo).toLTS τ.toLTS x l y)
    (hi : LInv lo τ x p) : LInv lo τ y (p ++ l.toList) := by
  cases hst with
  | tau₁ h => cases h with | tau hc => exact (hc : False).elim
  | tau₂ h => cases h
  | left e h => exact linv_left lo τ h hi
  | right g h => cases h with | mk _ hm => exact linv_right lo τ hm hi
  | sync f h₁ h₂ =>
    cases h₂ with
    | mk _ hm =>
      rw [Option.toList_none, List.append_nil]
      exact linv_sync lo τ hm h₁ hi

/-- Runs of the lower forwarding system keep the invariant. -/
theorem linv_run {x y : ((FwdL lo).toLTS.comp τ.toLTS).State} {t : List (Move E F)}
    (h : ((FwdL lo).toLTS.comp τ.toLTS).Run x t y) :
    ∀ p, LInv lo τ x p → LInv lo τ y (p ++ t) := by
  induction h with
  | nil => intro p hp; simpa using hp
  | tau hst _ ih =>
    intro p hp
    exact ih p (by simpa using linv_step lo τ hst hp)
  | @vis _ _ _ o t hst _ ih =>
    intro p hp
    simpa using ih _ (linv_step lo τ hst hp)

/-- **Soundness of the lower forwarding**: every play of `(ofHandler (ofHom lo)).comp τ` is the
image of a play of `τ` along `lo`. -/
theorem lower_sound {p : List (Move E F)}
    (hp : p ∈ (Strategy.ofHandler (Handler.ofHom lo)).comp τ) :
    ∃ t ∈ τ, List.Forall₂ (LRel lo) t p := by
  have hd := LTS.Denotes.comp (Handler.ofHom lo).denotes_toLTS τ.denotes_toLTS
  obtain ⟨y, hy⟩ := (hd p).2 hp
  have hi : LInv lo τ y ([] ++ p) := linv_run lo τ hy [] ⟨τ.nil_mem, .nil⟩
  rw [List.nil_append] at hi
  match y, hi with
  | (.idle, t), ⟨ht, hr⟩ => exact ⟨t, ht, hr⟩
  | (.run _ _, _), .inl ⟨_, ht, t', ht', hr⟩ =>
    exact ⟨t', τ.of_prefix ht (ht' ▸ List.prefix_append _ _), hr⟩
  | (.run m _, t), .inr ⟨n, p', _, hp', ht, ⟨q, hq⟩, hr⟩ =>
    exact ⟨t ++ [.inl (.ans m (lo.ar m n))],
      τ.receptive ht hq (Step.reply q m (lo.ar m n)) (by exact trivial),
      hp' ▸ forall₂_snoc hr (.lans m n)⟩
  | (.wait _ _ _, t), ⟨_, _, ht, _, hr⟩ => exact ⟨t, ht, hr⟩

end Lower

/-! ## The reduct -/

/-- **Soundness of the reduct**: every play of the reduct is a `RedRel`-image of a play. -/
theorem reduct_sound {G G' : Game.{u}} (f : G ⟶ G') (σ : G'.Model) {p : List (Move G.E G.F)}
    (hp : p ∈ Game.reduct f σ) : ∃ s ∈ σ, List.Forall₂ (Game.Rel f) s p := by
  obtain ⟨t, ht, hrt⟩ := lower_sound f.lo (σ.restrict f.up) hp
  obtain ⟨s, hs, hst⟩ := restrict_sound' σ f.up ht
  exact ⟨s, hs, forall₂_comp (forall₂_upRel hst) hrt⟩

end Silmaril.Proofs.Games.Reduct
