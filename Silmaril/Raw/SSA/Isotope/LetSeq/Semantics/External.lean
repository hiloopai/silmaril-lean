module

public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Operational

/-! Divergence through an explicitly divergent primitive, independently of typing.
The finite syntax follows successful left-to-right prefixes into that invocation;
a missing finite transition does not establish divergence. -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetSeq.Semantics.External

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

inductive Diverges (instr : Φ → Value α → σ → Value α → σ → Prop)
    (prim : Φ → Value α → σ → Prop) (free : FreeEnv ν α) :
    {n : Nat} → BoundEnv α n → Tm ν Φ n → σ → Prop where
  | op_arg {n} {bound : BoundEnv α n} {f a s}
      (arg : Diverges instr prim free bound a s) : Diverges instr prim free bound (.op f a) s
  | primitive {n} {bound : BoundEnv α n} {f a s mid value}
      (arg : Eval instr free bound a s value mid) (diverges : prim f value mid) :
      Diverges instr prim free bound (.op f a) s
  | let₁_arg {n} {bound : BoundEnv α n} {a b s}
      (arg : Diverges instr prim free bound a s) : Diverges instr prim free bound (.let₁ a b) s
  | let₁_body {n} {bound : BoundEnv α n} {a b s mid value}
      (arg : Eval instr free bound a s value mid)
      (body : Diverges instr prim free (extend bound value) b mid) :
      Diverges instr prim free bound (.let₁ a b) s
  | pair_left {n} {bound : BoundEnv α n} {a b s}
      (left : Diverges instr prim free bound a s) : Diverges instr prim free bound (.pair a b) s
  | pair_right {n} {bound : BoundEnv α n} {a b s mid value}
      (left : Eval instr free bound a s value mid) (right : Diverges instr prim free bound b mid) :
      Diverges instr prim free bound (.pair a b) s
  | let₂_arg {n} {bound : BoundEnv α n} {a b s}
      (arg : Diverges instr prim free bound a s) : Diverges instr prim free bound (.let₂ a b) s
  | let₂_body {n} {bound : BoundEnv α n} {a b s mid left right}
      (arg : Eval instr free bound a s (.pair left right) mid)
      (body : Diverges instr prim free (extend (extend bound left) right) b mid) :
      Diverges instr prim free bound (.let₂ a b) s

theorem Diverges.false {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Diverges instr (fun _ _ _ => False) free bound t s) : False := by
  induction h <;> assumption

end Silmaril.Isotope.LetSeq.Semantics.External

