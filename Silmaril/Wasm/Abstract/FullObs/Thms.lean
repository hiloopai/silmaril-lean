module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.FullFun.Thms
import Silmaril.Proofs.Wasm.Abstract.FullObs.Iter

/-!
# Full observations of interaction-tree bodies: theorems

* `toFull_comp` (**faithfulness for sequencing**): the full observation of a composite body is
  the sequencing of the full observations, `toFull (f >=> g) = FullFun.seq (toFull f) (toFull g)`,
  finite part and productive runs both (from `BodyTrace.toAFun_comp`, `BodyTrace.toInf_comp`);
* `toFull_comp_hostObsInf`: hence against a relational host the productive observations of a
  composite body decompose as `hostObsInf_seq` says;
* `mem_toInf_iter_step`: a productive run of a loop is one of its first iteration, or a
  finished continuing iteration followed by a productive run of the loop (Elgot fixpoint law
  and `toInf_comp`);
* `toInf_iter`, `toFull_iter` (**faithfulness for iteration**): the full observation of a body
  loop is the iteration of the full observation of its body,
  `toFull (iter F) = FullFun.iter (toFull F)`. The finite part is `BodyTrace.toAFun_iter`. For
  the productive part, a run that never settles into one iteration is an infinite chain of
  finished continuing iterations, one log per iteration, of unbounded total length (an
  eventually silent chain would make the loop diverge, `AFun.IterBeh.spin`); conversely such a
  chain is a run, since each finite prefix is pending (determinism given the answers,
  `mem_toInf_iff_streamPrefix`). No productivity or non-empty-log assumption is needed:
  unboundedness is part of `FullFun.iter`;
* `toFull_iter_hostObsInf`: hence against a relational host the productive observations of a
  body loop decompose as `hostObsInf_iter` says.

Productive runs of bodies are coherent: a stream is a run of the tree exactly when all its
finite prefixes are pending (`BodyTrace.infPath_iff_pend`), because bodies are deterministic
given the answers.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.FullObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace

universe u

/-- **Faithfulness for sequencing**: the full observation of a composite body is the
sequencing of the full observations. -/
theorem toFull_comp {E : Sig.{u}} {S T A B C : Type (u + 1)} (f : Hom E S T A B)
    (g : Hom E S T B C) :
    toFull (fun a => f a >>= g) = FullFun.seq (toFull f) (toFull g) :=
  Prod.ext (toAFun_comp f g) (funext fun s => funext fun a => toInf_comp f g s a)

/-- **Productive observations of a composite body** against a relational host. -/
theorem toFull_comp_hostObsInf {E : Sig.{u}} {S T A B C : Type (u + 1)} (f : Hom E S T A B)
    (g : Hom E S T B C) {R : HostRel (liftSig E)} (s : S) (a : A)
    (ω : Nat → Call (liftSig E)) :
    ω ∈ hostObsInf R (toInf (fun a => f a >>= g)) s a ↔
      ω ∈ hostObsInf R (toInf f) s a ∨
        ∃ (c : List (Call (liftSig E))) (b : B) (s₁ : S) (ω' : Nat → Call (liftSig E)),
          (c, End.ret b s₁) ∈ toAFun f s a ∧ R.Consistent c ∧ ω' ∈ hostObsInf R (toInf g) s₁ b ∧
          ω = c ++ₛ ω' := by
  have h := congrArg Prod.snd (toFull_comp f g)
  have e : toInf (fun a => f a >>= g) = (FullFun.seq (toFull f) (toFull g)).2 := h
  rw [e]
  exact hostObsInf_seq (toFull f) (toFull g) s a ω

/-- **One iteration unfolded**, for productive runs of a body loop. -/
theorem mem_toInf_iter_step {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A))
    (s : S) (a : A) (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf (Silmaril.Elgot.iter F) s a ↔ ω ∈ toInf F s a ∨
      ∃ (c : List (Call (liftSig E))) (a' : A) (s' : S) (ω' : Nat → Call (liftSig E)),
        (c, End.ret (.inr a') s') ∈ toAFun F s a ∧ ω' ∈ toInf (Silmaril.Elgot.iter F) s' a' ∧
          ω = c ++ₛ ω' :=
  Silmaril.Proofs.Wasm.Abstract.FullObs.mem_toInf_iter_step F s a ω

/-- **Productive runs of a body loop**: those of `FullFun.iter`. -/
theorem toInf_iter {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A)) (s : S)
    (a : A) : toInf (Silmaril.Elgot.iter F) s a = (FullFun.iter (toFull F)).2 s a :=
  Silmaril.Proofs.Wasm.Abstract.FullObs.toInf_iter F s a

/-- **Faithfulness for iteration**: the full observation of a body loop is the iteration of
the full observation of its body. -/
theorem toFull_iter {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A)) :
    toFull (Silmaril.Elgot.iter F) = FullFun.iter (toFull F) :=
  Prod.ext (toAFun_iter F) (funext fun s => funext fun a => toInf_iter F s a)

/-- **Productive observations of a body loop** against a relational host. -/
theorem toFull_iter_hostObsInf {E : Sig.{u}} {S T A B : Type (u + 1)} (F : Hom E S T A (B ⊕ A))
    {R : HostRel (liftSig E)} (s : S) (a : A) (ω : Nat → Call (liftSig E)) :
    ω ∈ hostObsInf R (toInf (Silmaril.Elgot.iter F)) s a ↔
      (∃ (c : List (Call (liftSig E))) (s' : S) (a' : A) (ω' : Nat → Call (liftSig E)),
          FullFun.ContChain (toAFun F) s a c s' a' ∧ R.Consistent c ∧
          ω' ∈ hostObsInf R (toInf F) s' a' ∧ ω = c ++ₛ ω') ∨
        ∃ (σ : Nat → S × A) (l : Nat → List (Call (liftSig E))), σ 0 = (s, a) ∧
          (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ toAFun F (σ n).1 (σ n).2) ∧
          (∀ n, R.Consistent (l n)) ∧ Shape.StreamConcat l ω := by
  have e : toInf (Silmaril.Elgot.iter F) = (FullFun.iter (toFull F)).2 :=
    congrArg Prod.snd (toFull_iter F)
  rw [e]
  exact hostObsInf_iter (toFull F) s a ω

end Silmaril.Wasm.Abstract.FullObs
