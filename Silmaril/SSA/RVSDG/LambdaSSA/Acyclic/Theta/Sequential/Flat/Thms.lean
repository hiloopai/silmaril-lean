module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Region

/-! # The actual flat linked CFG denotes ordered composition -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]
variable {A P Q M E D : τ}

theorem Fragment.classify_denote (op : TwoBlock.Instruction Φ A (Silmaril.coprod E D))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (Fragment.classify op).typing env =
      TwoBlock.TwoExit.callCase (ε := ε) op env.2 >>= fun result =>
        pure (TwoBlock.TwoExit.exitLabel result) :=
  Proofs.flat_classify_denote op coherent env

/-- An arbitrary admitted flat body can return at its first exit or restart
from its second exit. Each restart receives the new payload through the
relocated header, with the effects sequenced by the ambient Elgot monad. -/
theorem Fragment.feedback_denote (p : Fragment Φ A E A)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (p.feedback (D := D)).typing env =
      iter (fun x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) >>=
        fun r => pure ((⟨.first, .consumer⟩ : ExitRouting E A A E D).select r)) env.2 :=
  Proofs.flat_feedback_denote p coherent env

/-- A routed producer exit either returns its typed payload immediately or
starts the relocated consumer. Ordered bind carries the state across the cut. -/
theorem denote_linkBy (p : Fragment Φ A P Q) (q : Fragment Φ M E D) (routing : ExitRouting P Q M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (linkBy p q routing).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Sum.elim pure (fun input => Region.denote (ε := ε) (m := m) q.typing (PUnit.unit,input))
          (routing.select y) :=
  Proofs.flat_linkBy_denote p q routing coherent env

/-- The two original exit labels of the producer converge at the consumer
entry. Both dispatchers are interpreted by the repository's region denotation. -/
theorem denote_link (p : Fragment Φ A M M) (q : Fragment Φ M E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (link p q).typing env =
      Region.denote (ε := ε) (m := m) p.typing env >>= fun y =>
        Region.denote (ε := ε) (m := m) q.typing (PUnit.unit, merge y) :=
  Proofs.flat_link_denote p q coherent env

theorem Fragment.splitReturn_denote (p : Fragment Φ A E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m))
    (env : Env [Silmaril.coprod A E]) :
    Region.denote (ε := ε) (m := m) p.splitReturn.typing env =
      match TypeModel.coprodEquiv A E env.2 with
      | .inl x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x)
      | .inr e => pure (.inl e) :=
  Proofs.flat_splitReturn_denote p coherent env

theorem Fragment.gateCarrier_denote (p : Fragment Φ M E D)
    (gate : TwoBlock.Instruction Φ A (TwoBlock.TwoExit.Carrier M E D))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m) (p.gateCarrier gate).typing env =
      TwoBlock.TwoExit.callCase (ε := ε) gate env.2 >>= fun
        | .inl e => pure (TwoBlock.TwoExit.exitLabel (TypeModel.coprodEquiv E D e))
        | .inr x => Region.denote (ε := ε) (m := m) p.typing (PUnit.unit,x) :=
  Proofs.flat_gateCarrier_denote p gate coherent env

/-- The classifier reads the entry value and routes the independent
binding. Only the first external exit is reachable. -/
theorem Fragment.bindChooseLoop_denote {V W : τ} (value : TwoBlock.Instruction Φ A A)
    (test : TwoBlock.Instruction Φ A (Silmaril.coprod V W))
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Region.denote (ε := ε) (m := m)
        (Fragment.bindChooseLoop (D := D) value test).typing env =
      iter (fun x => TwoBlock.call (ε := ε) value x >>= fun y =>
        TwoBlock.TwoExit.callCase (ε := ε) test x >>= fun tag =>
          pure (tag.elim (fun _ => Sum.inl y) (fun _ => Sum.inr y))) env.2 >>= fun y =>
        pure (.inl y) :=
  Proofs.flat_bindChooseLoop_denote value test coherent env

omit [LawfulMonad m] [LawfulElgotMonad m] in
private theorem denote_congr {r s : Region Φ} {Γ L : List τ} (h : r = s)
    (dr : Region.HasType Γ r L) (ds : Region.HasType Γ s L) :
    Region.denote (ε := ε) (m := m) dr = Region.denote (ε := ε) (m := m) ds := by
  subst s
  rfl

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem Fragment.loop_denote {B K : τ} (s : Loop Φ A B K E D) :
    Region.denote (ε := ε) (m := m) (Fragment.loop s).typing =
      Region.denote (ε := ε) (m := m) (Theta.regionTyping s) :=
  denote_congr (Fragment.loop_region s) _ _

omit [LawfulMonad m] [LawfulElgotMonad m] in
theorem Fragment.guarded_denote {I B K : τ} (s : Conditional.Guarded Φ A I B K E D) :
    Region.denote (ε := ε) (m := m) (Fragment.guarded s).typing =
      Region.denote (ε := ε) (m := m) (Conditional.regionTyping s) :=
  denote_congr (Fragment.guarded_region s) _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
