module

public import Silmaril.Wasm.Component.Wiring.Defs
public import Silmaril.Games.Handler.Thms

/-!
# Programs and handlers: laws used by the component passes

The monad laws of `Silmaril.Games.Prog` (not yet in `Silmaril.Games`), the
interpretation of a `bind`, and the unit laws of handler composition. These
are general facts about the Games API, stated here in namespace
`Silmaril.Wasm.Component` as candidates for upstreaming into
`Silmaril.Games.Handler`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

universe u

variable {E F G : Sig.{u}} {A B C : Type u}

/-- `pure` is a left unit of `bind`. -/
@[simp] theorem Prog.pure_bind (a : A) (f : A → Prog E B) : (Prog.pure a).bind f = f a := rfl

/-- `bind` of a call. -/
@[simp] theorem Prog.call_bind (m : E.Op) (k : E.Ar m → Prog E A) (f : A → Prog E B) :
    (Prog.call m k).bind f = .call m fun n => (k n).bind f := rfl

/-- `pure` is a right unit of `bind`. -/
@[simp] theorem Prog.bind_pure (p : Prog E A) : p.bind Prog.pure = p := by
  induction p with
  | pure a => rfl
  | call m k ih => simp only [Prog.call_bind, ih]

/-- `bind` is associative. -/
theorem Prog.bind_assoc (p : Prog E A) (f : A → Prog E B) (g : B → Prog E C) :
    (p.bind f).bind g = p.bind fun x => (f x).bind g := by
  induction p with
  | pure a => rfl
  | call m k ih => simp only [Prog.call_bind, ih]

/-- Interpretation of a returned value. -/
@[simp] theorem Prog.interp_pure (h : Handler E F) (a : A) : (Prog.pure a).interp h = .pure a :=
  rfl

/-- Interpretation of a call. -/
theorem Prog.interp_call (h : Handler E F) (m : F.Op) (k : F.Ar m → Prog F A) :
    (Prog.call m k).interp h = (h m).bind fun n => (k n).interp h := rfl

/-- Interpretation commutes with `bind`. -/
theorem Prog.interp_bind (h : Handler E F) (p : Prog F A) (f : A → Prog F B) :
    (p.bind f).interp h = (p.interp h).bind fun x => (f x).interp h := by
  induction p with
  | pure a => rfl
  | call m k ih =>
    simp only [Prog.call_bind, Prog.interp_call, ih, Prog.bind_assoc]

/-- Interpretation by the forwarding handler is the identity. -/
@[simp] theorem Prog.interp_id (p : Prog E A) : p.interp (Handler.id E) = p := by
  induction p with
  | pure a => rfl
  | call m k ih =>
    simp only [Prog.interp_call, Handler.id, Prog.lift, Prog.call_bind, Prog.pure_bind, ih]

/-- Interpretation by a composite handler is iterated interpretation. -/
theorem Prog.interp_comp (h₁ : Handler E F) (h₂ : Handler F G) (p : Prog G A) :
    p.interp (h₁.comp h₂) = (p.interp h₂).interp h₁ := by
  induction p with
  | pure a => rfl
  | call m k ih =>
    simp only [Prog.interp_call, Handler.comp, Prog.interp_bind, ih]

/-- The forwarding handler is a left unit of handler composition. -/
@[simp] theorem Handler.id_comp' (h : Handler E F) : (Handler.id E).comp h = h := by
  funext q
  exact Prog.interp_id (h q)

/-- The forwarding handler is a right unit of handler composition. -/
@[simp] theorem Handler.comp_id' (h : Handler E F) : h.comp (Handler.id F) = h := by
  funext q
  simp only [Handler.comp, Handler.id, Prog.lift, Prog.interp_call, Prog.interp_pure,
    Prog.bind_pure]

/-- Handler composition is associative. -/
theorem Handler.comp_assoc' {H : Sig.{u}} (h₁ : Handler E F) (h₂ : Handler F G)
    (h₃ : Handler G H) : (h₁.comp h₂).comp h₃ = h₁.comp (h₂.comp h₃) := by
  funext q
  simp only [Handler.comp, Prog.interp_comp]

end Silmaril.Wasm.Component
