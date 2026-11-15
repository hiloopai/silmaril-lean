module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.FullFun.Thms

/-!
# Full observations of interaction-tree bodies: theorems

* `toFull_comp` (**faithfulness for sequencing**): the full observation of a composite body is
  the sequencing of the full observations, `toFull (f >=> g) = FullFun.seq (toFull f) (toFull g)`,
  finite part and productive runs both (from `BodyTrace.toAFun_comp`, `BodyTrace.toInf_comp`);
* `toFull_comp_hostObsInf`: hence against a relational host the productive observations of a
  composite body decompose as `hostObsInf_seq` says.

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

end Silmaril.Wasm.Abstract.FullObs
