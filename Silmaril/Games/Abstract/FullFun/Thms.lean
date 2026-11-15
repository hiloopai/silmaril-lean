module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic

/-!
# Full observations of functions: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.FullFun`.

* `consistent_append`: consistency of a joined stream `c ++ₛ ω` splits exactly into the
  finished prefix `c` and the tail `ω`;
* `hostObsInf_seq` (**host preservation of sequencing**): the productive observations of
  `FullFun.seq f g` against a relational host are those of `f`, or a finished return of `f`
  with a consistent log followed by a productive observation of `g`;
* `pure_inf`, `pure_seq_inf`: the identity has no productive run, and does not change the
  productive runs of what follows.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- Consistency of a joined stream splits into the prefix and the tail. -/
theorem consistent_append {R : HostRel E} (c : List (Call E)) (ω : Nat → Call E) :
    (∀ n, R ((c ++ₛ ω) n).1 (.answer ((c ++ₛ ω) n).2)) ↔
      R.Consistent c ∧ ∀ n, R (ω n).1 (.answer (ω n).2) :=
  Silmaril.Proofs.Games.Abstract.FullFun.consistent_append c ω

/-- **Host preservation of sequencing** (productive part). -/
theorem hostObsInf_seq {R : HostRel E} (f : FullFun E S A B) (g : FullFun E S B C) (s : S)
    (a : A) (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.seq f g).2 s a ↔
      ω ∈ hostObsInf R f.2 s a ∨
        ∃ (c : List (Call E)) (b : B) (s₁ : S) (ω' : Nat → Call E),
          (c, End.ret b s₁) ∈ f.1 s a ∧ R.Consistent c ∧ ω' ∈ hostObsInf R g.2 s₁ b ∧
          ω = c ++ₛ ω' :=
  Silmaril.Proofs.Games.Abstract.FullFun.hostObsInf_seq f g s a ω

/-- The identity has no productive run. -/
theorem FullFun.pure_inf (s : S) (a : A) : (FullFun.pure : FullFun E S A A).2 s a = ∅ := rfl

/-- Sequencing after the identity keeps the productive runs. -/
theorem FullFun.pure_seq_inf (g : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq FullFun.pure g).2 s a = g.2 s a :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_seq_inf g s a

end Silmaril.Games.Abstract
