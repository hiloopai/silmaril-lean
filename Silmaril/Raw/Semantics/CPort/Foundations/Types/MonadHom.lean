module

public import Silmaril.Semantics.CPort.Foundations.Types.Inclusion.Defs
public import Silmaril.Semantics.CPort.Foundations.Types.Comparison.Defs
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Control.Combinators

/-!
# Type-syntax conversions as monad homomorphisms

These certificates give compatibility with the standard functor, applicative,
and monadic operations through CSLib's common interface.
-/

@[expose] public section

universe u

namespace Silmaril

namespace FreeTy

theorem embed_isMonadHom {s t : TypeFeatures} (h : TypeFeatures.Inclusion s t) :
    Cslib.IsMonadHom (FreeTy s : Type u → Type u) (FreeTy t) (embed h) :=
  .mk' (fun _ => rfl) (fun A f => embed_bind h A f)

/-- Signature embeddings commute with monadic multiplication. -/
theorem embed_join {s t : TypeFeatures} {α : Type u} (h : TypeFeatures.Inclusion s t)
    (A : FreeTy s (FreeTy s α)) :
    embed h (joinM A) = joinM (embed h <$> embed h A) := by
  change embed h (bind A id) = bind (map (embed h) (embed h A)) id
  rw [embed_bind, bind_map]
  rfl

theorem toTy_isMonadHom (s : TypeFeatures) :
    Cslib.IsMonadHom (FreeTy s : Type u → Type u) Ty toTy :=
  .mk' (fun _ => rfl) (fun A f => toTy_bind A f)

end FreeTy

namespace Ty

theorem toFree_isMonadHom :
    Cslib.IsMonadHom (Ty : Type u → Type u) (FreeTy TypeFeatures.all) toFree :=
  .mk' (fun _ => rfl) (fun A f => toFree_bind A f)

end Ty
end Silmaril
