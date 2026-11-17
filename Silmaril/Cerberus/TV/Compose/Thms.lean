module

public import Silmaril.Cerberus.TV.Compose.Defs
import Silmaril.Proofs.Cerberus.TV.Compose

/-!
# Composition of whole-program evidence (theorems)

* Vertical: `Refines.trans`, `Refines.refl` (a supported terminating program refines itself),
  `Equivalent.symm`, `Equivalent.trans`.
* Horizontal: `ContextRefines.trans` (successive replacements of one function),
  `ContextRefines.then` (a replacement of `f`, then one of `g` in the contexts where `f` is
  already replaced), `validateContexts_sound` (to `FunctionRefines`: nonempty contexts with a
  substitution witness each), `ContextRefines.nil` (the weak relation is vacuous for no context)
  and `FunctionRefines.not_nil`.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

theorem Refines.trans {impl : Spec.Impl} {A B C : Closed} (h₁ : Refines impl A B)
    (h₂ : Refines impl B C) : Refines impl A C :=
  Proofs.Cerberus.TV.Refines.trans h₁ h₂

theorem Refines.refl {impl : Spec.Impl} {P : Closed} (hs : P.Supported) (ht : ¬ P.Diverges) :
    Refines impl P P :=
  Proofs.Cerberus.TV.Refines.refl hs ht

theorem Equivalent.symm {impl : Spec.Impl} {P Q : Closed} (h : Equivalent impl P Q) :
    Equivalent impl Q P :=
  Proofs.Cerberus.TV.Equivalent.symm h

theorem Equivalent.trans {impl : Spec.Impl} {P Q R : Closed} (h₁ : Equivalent impl P Q)
    (h₂ : Equivalent impl Q R) : Equivalent impl P R :=
  Proofs.Cerberus.TV.Equivalent.trans h₁ h₂

theorem ContextRefines.trans {impl : Spec.Impl} {ctxs : List Codec.FileBindings} {f : Sym}
    {d d' d'' : Core.FunDecl Codec.wireModel Unit Unit} (h₁ : ContextRefines impl ctxs f d d')
    (h₂ : ContextRefines impl ctxs f d' d'') : ContextRefines impl ctxs f d d'' :=
  Proofs.Cerberus.TV.ContextRefines.trans h₁ h₂

/-- **Function by function**: replacing `f` (in a context `b`), and then `g` (in that context with
`f` already replaced, where `e` is `g`'s current definition), refines the original program. -/
theorem ContextRefines.then {impl : Spec.Impl} {b : Codec.FileBindings} {f g : Sym}
    {d d' e e' : Core.FunDecl Codec.wireModel Unit Unit}
    (hf : ContextRefines impl [b] f d d') (hg : ContextRefines impl [b.setFunction f d'] g e e')
    (he : (b.setFunction f d').setFunction g e = b.setFunction f d') :
    Refines impl (Closed.withFunction b f d) (Closed.withFunction (b.setFunction f d') g e') := by
  have h₂ := hg (b.setFunction f d') (by simp)
  unfold Closed.withFunction at h₂ ⊢
  rw [he] at h₂
  exact Refines.trans (hf b (by simp)) h₂

theorem validateContexts_sound (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) (bounds : Bounds)
    (h : validateContexts impl ctxs f d d' bounds = true) : FunctionRefines impl ctxs f d d' :=
  Proofs.Cerberus.TV.validateContexts_sound impl ctxs f d d' bounds h

/-- The weak relation is vacuous for no context (why the standard shape is `FunctionRefines`). -/
theorem ContextRefines.nil (impl : Spec.Impl) (f : Sym) (d d' : Core.FunDecl Codec.wireModel Unit Unit) :
    ContextRefines impl [] f d d' := fun _ h => nomatch h

/-- `FunctionRefines` never holds for no context. -/
theorem FunctionRefines.not_nil {impl : Spec.Impl} {f : Sym} {d d' : Core.FunDecl Codec.wireModel Unit Unit} :
    ¬ FunctionRefines impl [] f d d' := fun h => h.nonempty rfl

/-- **Steps compose**: refinements between consecutive stages give the refinement from stage 0
to stage `n`. -/
theorem refines_chain_upto {impl : Spec.Impl} (P : Nat → Closed) (n : Nat) (hn : 0 < n)
    (h : ∀ i < n, Refines impl (P i) (P (i + 1))) : Refines impl (P 0) (P n) :=
  Proofs.Cerberus.TV.refines_chain_upto P n hn h

/-- **The module validator is sound**: one function at a time, composed by induction. -/
theorem validateModule_sound (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (rs : List Replacement)
    (bounds : Bounds) (h : validateModule impl ctxs rs bounds = true) : ModuleRefines impl ctxs rs :=
  Proofs.Cerberus.TV.validateModule_sound impl ctxs rs bounds h

/-- `ModuleRefines` never holds for no context. -/
theorem ModuleRefines.not_nil {impl : Spec.Impl} {rs : List Replacement} : ¬ ModuleRefines impl [] rs :=
  fun h => h.nonempty rfl

end Silmaril.Cerberus.TV
