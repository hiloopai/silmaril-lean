module

public import Silmaril.Games.Reduct.Defs
public import Silmaril.Games.Handler.Thms

/-!
# The plays of a reduct: completeness

Every legal `RedRel`-image of a play of `σ` is a play of the reduct. The proof runs the
transition system `(Fwd lo).toLTS.comp (σ.toLTS.comp (Fwd up).toLTS)`, which denotes the reduct
(`LTS.Denotes.comp`), move by move along the image. The states of the two forwarders are
determined by the positions of the play of `σ` (`zLo`) and of its image (`zUp`).
-/

public section

namespace Silmaril.Proofs.Games.Reduct

open Silmaril.Games

universe u

variable {E E' F F' : Sig.{u}} (lo : Sig.Hom E' E) (up : Sig.Hom F F') (σ : Strategy E' F')

/-- The lower forwarder. -/
abbrev LoR : Reduction E E' := (Handler.ofHom lo).toReduction

/-- The upper forwarder. -/
abbrev UpR : Reduction F' F := (Handler.ofHom up).toReduction

/-- The transition system of the reduct. -/
abbrev RedLTS : LTS E F := (LoR lo).toLTS.comp (σ.toLTS.comp (UpR up).toLTS)

/-- The state of the lower forwarder, from the position of the play of `σ`. -/
def zLo : Pos E' F' → (LoR lo).State
  | .wait _ m => .wait m (lo.op m) fun n => .pure (lo.ar m n)
  | _ => .idle

/-- The state of the upper forwarder, from the position of the image. -/
def zUp : Pos E F → (UpR up).State
  | .idle => .idle
  | .run q => .wait q (up.op q) fun n => .pure (up.ar q n)
  | .wait q _ => .wait q (up.op q) fun n => .pure (up.ar q n)

/-- **One move of the image** is a run of the reduct's transition system. -/
theorem run_move {a : Move E' F'} {b : Move E F} {xs xs' : Pos E' F'} {xp xp' : Pos E F}
    {s₀ : List (Move E' F')} (hr : RedRel lo up a b) (hs : Step xs a xs') (hp : Step xp b xp')
    (hm : s₀ ++ [a] ∈ σ) :
    (RedLTS lo up σ).Run (zLo lo xs, s₀, zUp up xp) [b] (zLo lo xs', s₀ ++ [a], zUp up xp') := by
  cases hr with
  | lask m =>
    show (RedLTS lo up σ).Run _ _ _
    cases hs with
    | call q₀ _ =>
      cases hp with
      | call q _ =>
        exact .tau (LTS.CompStep.sync (.ask m) (Reduction.Step.ask m)
            (LTS.CompStep.left (.ask m) (Strategy.TStep.mk _ _ hm)))
          (.vis (LTS.CompStep.left (.ask (lo.op m)) (Reduction.Step.call rfl)) (.nil _))
  | lans m n =>
    show (RedLTS lo up σ).Run _ _ _
    cases hs with
    | reply q₀ _ _ =>
      cases hp with
      | reply q _ _ =>
        exact .vis (LTS.CompStep.left (.ans (lo.op m) n) (Reduction.Step.resume _ _ _ n))
          (.tau (LTS.CompStep.sync (.ans m (lo.ar m n)) (Reduction.Step.ret rfl)
            (LTS.CompStep.left (.ans m (lo.ar m n)) (Strategy.TStep.mk _ _ hm))) (.nil _))
  | uask q =>
    show (RedLTS lo up σ).Run _ _ _
    cases hs with
    | ask _ =>
      cases hp with
      | ask _ =>
        exact .vis (LTS.CompStep.right (.ask q) (LTS.CompStep.right (.ask q)
            (Reduction.Step.ask q)))
          (.tau (LTS.CompStep.tau₂ (LTS.CompStep.sync (.ask (up.op q))
            (Strategy.TStep.mk _ _ hm) (Reduction.Step.call rfl))) (.nil _))
  | uans q n =>
    show (RedLTS lo up σ).Run _ _ _
    cases hs with
    | ret _ _ =>
      cases hp with
      | ret _ _ =>
        exact .tau (LTS.CompStep.tau₂ (LTS.CompStep.sync (.ans (up.op q) n)
            (Strategy.TStep.mk _ _ hm) (Reduction.Step.resume _ _ _ n)))
          (.vis (LTS.CompStep.right (.ans q (up.ar q n)) (LTS.CompStep.right
            (.ans q (up.ar q n)) (Reduction.Step.ret rfl))) (.nil _))

/-- **A related pair of paths** is a run of the reduct's transition system. -/
theorem run_rel {s : List (Move E' F')} {p : List (Move E F)}
    (hr : List.Forall₂ (RedRel lo up) s p) :
    ∀ {s₀ : List (Move E' F')} {xs xs₁ : Pos E' F'} {xp xp₁ : Pos E F},
      Path xs s xs₁ → Path xp p xp₁ → s₀ ++ s ∈ σ →
      (RedLTS lo up σ).Run (zLo lo xs, s₀, zUp up xp) p (zLo lo xs₁, s₀ ++ s, zUp up xp₁) := by
  induction hr with
  | nil =>
    intro s₀ xs xs₁ xp xp₁ hs hp _
    cases hs
    cases hp
    rw [List.append_nil]
    exact .nil _
  | @cons a b s p hab _ ih =>
    intro s₀ xs xs₁ xp xp₁ hs hp hm
    cases hs with
    | cons has hs' =>
      cases hp with
      | cons hbp hp' =>
        have hm' : s₀ ++ [a] ++ s ∈ σ := by simpa using hm
        have h₁ := run_move lo up σ hab has hbp (σ.of_prefix hm' (List.prefix_append _ _))
        have h₂ := ih hs' hp' hm'
        have h := LTS.Run.append h₁ h₂
        simpa using h

/-- **Completeness of the reduct**: a legal `RedRel`-image of a play of `σ` is a play of the
reduct. -/
theorem reduct_complete {s : List (Move E' F')} {p : List (Move E F)} (hs : s ∈ σ)
    (hr : List.Forall₂ (RedRel lo up) s p) (hp : Legal p) :
    p ∈ (Strategy.ofHandler (Handler.ofHom lo)).comp
      (σ.comp (Strategy.ofHandler (Handler.ofHom up))) := by
  have hd := LTS.Denotes.comp (Handler.ofHom lo).denotes_toLTS
    (LTS.Denotes.comp σ.denotes_toLTS (Handler.ofHom up).denotes_toLTS)
  obtain ⟨xs, hxs⟩ := σ.legal hs
  obtain ⟨xp, hxp⟩ := hp
  have h := run_rel lo up σ hr (s₀ := []) hxs hxp (by simpa using hs)
  exact (hd p).1 ⟨_, h⟩

end Silmaril.Proofs.Games.Reduct
