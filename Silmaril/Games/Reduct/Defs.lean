module

public import Silmaril.Games.Institution.Defs

/-!
# The plays of a reduct: the move relation

`Game.reduct f σ` (`Silmaril.Games.Institution.Defs`) forwards the lower calls of `σ` along `f.lo`
and offers its upper operations through `f.up`. This module names how each move of `σ` is seen
in the reduct:

* `RedRel lo up a b`: the move `a` of a strategy of `E' ↠ F'` is seen as the move `b` of
  `E ↠ F`, for `lo : Sig.Hom E' E` and `up : Sig.Hom F F'`. A lower question `m` is seen as
  `lo.op m`, and the answer `n` to it is given to `σ` as `lo.ar m n`. An upper question `q` is
  given to `σ` as `up.op q`, and `σ`'s answer `n` is seen as `up.ar q n`.
* `RedPos lo up x y`: the matching relation on positions.

`Silmaril.Games.Reduct.Thms` proves that the plays of the reduct are exactly the legal
`RedRel`-images of the plays of `σ` (`Game.mem_reduct_iff_rel`). This is the play-level
description of `GInst`'s reduct, and the move map of `docs/projects/spectec/README.md` §2.

New definitions.
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- **How a move of a strategy is seen in its reduct** along a lower renaming `lo` and an upper
renaming `up`. -/
inductive RedRel {E E' F F' : Sig.{u}} (lo : Sig.Hom E' E) (up : Sig.Hom F F') :
    Move E' F' → Move E F → Prop
  /-- A lower question `m` is forwarded as `lo.op m`. -/
  | lask (m : E'.Op) : RedRel lo up (.inl (.ask m)) (.inl (.ask (lo.op m)))
  /-- The answer `n` to the forwarded question is given back as `lo.ar m n`. -/
  | lans (m : E'.Op) (n : E.Ar (lo.op m)) :
      RedRel lo up (.inl (.ans m (lo.ar m n))) (.inl (.ans (lo.op m) n))
  /-- An upper question `q` is received as `up.op q`. -/
  | uask (q : F.Op) : RedRel lo up (.inr (.ask (up.op q))) (.inr (.ask q))
  /-- The answer `n` to `up.op q` is returned as `up.ar q n`. -/
  | uans (q : F.Op) (n : F'.Ar (up.op q)) :
      RedRel lo up (.inr (.ans (up.op q) n)) (.inr (.ans q (up.ar q n)))

/-- The positions of a strategy and of its reduct along `lo` and `up` that correspond. -/
inductive RedPos {E E' F F' : Sig.{u}} (lo : Sig.Hom E' E) (up : Sig.Hom F F') :
    Pos E' F' → Pos E F → Prop
  /-- Both are idle. -/
  | idle : RedPos lo up .idle .idle
  /-- Both run the question `q`. -/
  | run (q : F.Op) : RedPos lo up (.run (up.op q)) (.run q)
  /-- Both wait for the answer to the lower question `m`. -/
  | wait (q : F.Op) (m : E'.Op) : RedPos lo up (.wait (up.op q) m) (.wait q (lo.op m))

namespace Game

/-- The move relation of a game morphism. -/
abbrev Rel {G G' : Game.{u}} (f : G ⟶ G') : Move G'.E G'.F → Move G.E G.F → Prop :=
  RedRel f.lo f.up

end Game

end Silmaril.Games
