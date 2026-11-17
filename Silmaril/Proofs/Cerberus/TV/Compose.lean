module

public import Silmaril.Cerberus.TV.Compose.Defs
public import Silmaril.Cerberus.TV.Validate.Thms

/-! Proofs of `Silmaril.Cerberus.TV.Compose.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Cerberus.TV

open Silmaril.Cerberus
open Silmaril.Cerberus.TV

theorem Refines.trans {impl : Spec.Impl} {A B C : Closed} (h₁ : Refines impl A B)
    (h₂ : Refines impl B C) : Refines impl A C :=
  ⟨fun x hx => h₁.observations x (h₂.observations x hx), h₂.supported, h₂.terminates⟩

theorem Refines.refl {impl : Spec.Impl} {P : Closed} (hs : P.Supported) (ht : ¬ P.Diverges) :
    Refines impl P P :=
  ⟨fun _ hx => hx, hs, ht⟩

theorem Equivalent.symm {impl : Spec.Impl} {P Q : Closed} (h : Equivalent impl P Q) :
    Equivalent impl Q P :=
  ⟨h.2, h.1⟩

theorem Equivalent.trans {impl : Spec.Impl} {P Q R : Closed} (h₁ : Equivalent impl P Q)
    (h₂ : Equivalent impl Q R) : Equivalent impl P R :=
  ⟨Refines.trans h₁.1 h₂.1, Refines.trans h₂.2 h₁.2⟩

theorem ContextRefines.trans {impl : Spec.Impl} {ctxs : List Codec.FileBindings} {f : Sym}
    {d d' d'' : Core.FunDecl Codec.wireModel Unit Unit} (h₁ : ContextRefines impl ctxs f d d')
    (h₂ : ContextRefines impl ctxs f d' d'') : ContextRefines impl ctxs f d d'' :=
  fun b hb => Refines.trans (h₁ b hb) (h₂ b hb)

theorem validateContexts_sound (impl : Spec.Impl) (ctxs : List Codec.FileBindings) (f : Sym)
    (d d' : Core.FunDecl Codec.wireModel Unit Unit) (bounds : Bounds)
    (h : validateContexts impl ctxs f d d' bounds = true) : FunctionRefines impl ctxs f d d' := by
  simp only [validateContexts, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, hs⟩, hv⟩ := h
  refine ⟨hne, fun b hb => of_decide_eq_true (List.all_eq_true.mp hs b hb), ?_⟩
  intro b hb
  have := List.all_eq_true.mp hv b hb
  simp only [beq_iff_eq] at this
  exact validate_sound impl _ _ bounds this

end Silmaril.Proofs.Cerberus.TV
