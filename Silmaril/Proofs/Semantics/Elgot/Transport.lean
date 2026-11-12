module

public import Silmaril.Semantics.Elgot.Defs
public import Silmaril.Proofs.Semantics.Elgot.Basic
import all Silmaril.Proofs.Semantics.Elgot.Basic
import Batteries.Tactic.Alias

/-!
# Transport of Elgot laws: proofs

Proofs for `Silmaril.Semantics.Elgot.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u

variable {m n : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m]
  [Monad n] [LawfulMonad n] [Iterate n]

namespace Embedding

variable (e : Embedding m n)

@[simp] private theorem map_map {A B : Type u} (f : A → B) (x : m A) :
    e.map (f <$> x) = f <$> e.map x := by
  have h := e.map_bind x (pure ∘ f)
  simpa only [bind_pure_comp, Function.comp_def, e.map_pure] using h
alias _root_.Silmaril.Proofs.Semantics.Elgot.Embedding.map_map := Silmaril.Elgot.Embedding.map_map

@[simp] private theorem map_mapReturn {A B C : Type u}
    (f : A → m (B ⊕ A)) (g : B → m C) (a : A) :
    e.map (mapReturn f g a) = mapReturn (fun a => e.map (f a)) (fun b => e.map (g b)) a := by
  simp only [mapReturn, e.map_bind]
  congr 1
  funext s
  cases s <;> simp [Function.comp_def, e.map_pure]
alias _root_.Silmaril.Proofs.Semantics.Elgot.Embedding.map_mapReturn := Silmaril.Elgot.Embedding.map_mapReturn

@[simp] private theorem map_flattenBody {A B : Type u} (f : A → m ((B ⊕ A) ⊕ A)) (a : A) :
    e.map (flattenBody f a) = flattenBody (fun a => e.map (f a)) a := by
  simp [flattenBody, Bind.kleisliRight, liftPure, Function.comp_def]
alias _root_.Silmaril.Proofs.Semantics.Elgot.Embedding.map_flattenBody := Silmaril.Elgot.Embedding.map_flattenBody

include e in
/-- All four Elgot equations descend along a faithful iteration-preserving monad map. -/
private theorem lawful [LawfulElgotMonad n] : LawfulElgotMonad m where
  fixpoint f := by
    funext a
    apply e.injective
    show e.map (iter f a) = e.map (f a >>= Sum.elim pure (iter f))
    rw [e.map_iter, e.map_bind, LawfulElgotMonad.fixpoint]
    apply bind_congr
    intro s
    cases s <;> simp [e.map_pure, e.map_iter]
  naturality f g := by
    funext a
    apply e.injective
    simp only [Bind.kleisliRight, e.map_bind, e.map_iter]
    have h : (iter (fun a => e.map (f a)) >=> fun b => e.map (g b)) a =
        iter (mapReturn (fun a => e.map (f a)) fun b => e.map (g b)) a :=
      congrFun (LawfulElgotMonad.naturality (m := n) _ _) a
    simpa only [Bind.kleisliRight, e.map_mapReturn] using h
  codiagonal f := by
    funext a
    apply e.injective
    show e.map (iter (iter f) a) = e.map (iter (flattenBody f) a)
    simpa only [e.map_iter, e.map_flattenBody] using
      congrFun (LawfulElgotMonad.codiagonal (m := n) (fun a => e.map (f a))) a
  uniformity f g h comm := by
    have square : ((fun a => e.map (f a)) >=> liftPure (Sum.map id h)) =
        (liftPure h >=> fun c => e.map (g c)) := by
      funext a
      have ha : e.map ((f >=> liftPure (Sum.map id h)) a) = e.map ((liftPure h >=> g) a) :=
        congrArg e.map (congrFun comm a)
      simpa only [Bind.kleisliRight, liftPure, Function.comp_def, e.map_bind, e.map_pure,
        pure_bind] using ha
    funext a
    apply e.injective
    simpa only [Bind.kleisliRight, liftPure, Function.comp_def, e.map_bind, e.map_pure, pure_bind,
      e.map_iter] using congrFun (LawfulElgotMonad.uniformity (m := n)
        (fun a => e.map (f a)) (fun c => e.map (g c)) h square) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.Embedding.lawful := Silmaril.Elgot.Embedding.lawful

end Embedding

end Silmaril.Elgot
