module

public import Silmaril.Wasm.Spec.Maps.Defs

/-!
# A facade for the trace-institution format

`Spec.inst L S : Inst` (`Silmaril.Wasm.Spec.Format.Defs`) is the institution of `L`-specifications of
`S`-programs. This module gives the unfolding lemmas that let `simp` read its satisfaction,
translation and reduct, and the functoriality of the two comorphism builders of
`Silmaril.Wasm.Spec.Maps.Defs`:

* `inst_sat_iff`, `inst_map_sen`, `inst_map_mod_obj` (`@[simp]`, `rfl`): satisfaction is `Spec.Sat`,
  sentences translate by `Sen.map`, models reduct by `Model.reduct`;
* `LogicMap.coHom_sen`, `LogicMap.coHom_mod_obj`, `SemMap.coHom_sen`, `SemMap.coHom_mod_obj`
  (`@[simp]`);
* `LogicMap.coHom_id`, `LogicMap.coHom_comp`: logic maps act functorially, so the builder
  `LogicMap.coHom` ("a comorphism from a translation of formulas") commutes with `Inst.CoHom.id`
  and `Inst.CoHom.comp`;
* `SemMap.id`, `SemMap.comp` and `SemMap.coHom_id`, `SemMap.coHom_comp` (contravariant);
* `LogicMap.coHom_holds_iff`, `SemMap.coHom_models_iff`: satisfaction transfer in one step.

New definitions and lemmas; the institution is unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.Spec

open CategoryTheory Silmaril.Logic.Institution

variable {Ty A R : Type}

/-! ## Unfolding lemmas -/

/-- Satisfaction in `inst L S` is `Spec.Sat`. -/
@[simp] theorem inst_sat_iff (L : Logic Ty A R) (S : Semantics Ty A R) {X : Iface Ty}
    (M : Model S X) (s : Sen L X) : ((inst L S).I.obj X).Sat M s ↔ Sat L S M s := Iff.rfl

/-- Sentence translation in `inst L S` is `Sen.map`. -/
@[simp] theorem inst_map_sen (L : Logic Ty A R) (S : Semantics Ty A R) {X X' : Iface Ty}
    (f : X ⟶ X') (s : Sen L X) : ((inst L S).I.map f).sen s = s.map f := rfl

/-- The reduct of `inst L S` is `Model.reduct`. -/
@[simp] theorem inst_map_mod_obj (L : Logic Ty A R) (S : Semantics Ty A R) {X X' : Iface Ty}
    (f : X ⟶ X') (M : Model S X') :
    ((inst L S).I.map f).mod.obj M = (Model.reduct S f).obj M := rfl

/-! ## Logic maps -/

@[simp] theorem LogicMap.coHom_Φ {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R) :
    (f.coHom S).Φ = 𝟭 _ := rfl

@[simp] theorem LogicMap.coHom_sen {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R)
    (X : Iface Ty) (s : Sen L X) : ((f.coHom S).ρ.app X).sen s = f.sen s := rfl

@[simp] theorem LogicMap.coHom_mod_obj {L L' : Logic Ty A R} (f : LogicMap L L')
    (S : Semantics Ty A R) (X : Iface Ty) (M : Model S X) :
    ((f.coHom S).ρ.app X).mod.obj M = M := rfl

/-- **Satisfaction transfer along a logic map**: a model satisfies the translated sentence iff it
satisfies the sentence. -/
theorem LogicMap.coHom_holds_iff {L L' : Logic Ty A R} (f : LogicMap L L') (S : Semantics Ty A R)
    {X : Iface Ty} (M : Model S X) (s : Sen L X) : Sat L' S M (f.sen s) ↔ Sat L S M s :=
  (f.coHom S).satisfaction X M s

/-- The identity logic map gives the identity comorphism. -/
theorem LogicMap.coHom_id (L : Logic Ty A R) (S : Semantics Ty A R) :
    (LogicMap.id L).coHom S = Inst.CoHom.id (inst L S) := rfl

/-- **Logic maps compose as comorphisms.** -/
theorem LogicMap.coHom_comp {L L' L'' : Logic Ty A R} (f : LogicMap L L') (g : LogicMap L' L'')
    (S : Semantics Ty A R) : (f.comp g).coHom S = (f.coHom S).comp (g.coHom S) := rfl

/-! ## Semantics maps -/

/-- The identity semantics map. -/
def SemMap.id (S : Semantics Ty A R) : SemMap S S := ⟨fun p => p, fun _ => rfl⟩

/-- Composition of semantics maps. -/
def SemMap.comp {S S' S'' : Semantics Ty A R} (m : SemMap S S') (n : SemMap S' S'') :
    SemMap S S'' :=
  ⟨fun p => n.prog (m.prog p), fun p => (n.traces_prog _).trans (m.traces_prog p)⟩

@[simp] theorem SemMap.coHom_Φ {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R) :
    (m.coHom L).Φ = 𝟭 _ := rfl

@[simp] theorem SemMap.coHom_sen {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R)
    (X : Iface Ty) (s : Sen L X) : ((m.coHom L).ρ.app X).sen s = s := rfl

@[simp] theorem SemMap.coHom_mod_obj {S S' : Semantics Ty A R} (m : SemMap S S')
    (L : Logic Ty A R) (X : Iface Ty) (M : Model S X) :
    ((m.coHom L).ρ.app X).mod.obj M = m.model M := rfl

/-- **Satisfaction transfer along a semantics map**: the translated model satisfies a sentence iff
the model does. -/
theorem SemMap.coHom_models_iff {S S' : Semantics Ty A R} (m : SemMap S S') (L : Logic Ty A R)
    {X : Iface Ty} (M : Model S X) (s : Sen L X) : Sat L S' (m.model M) s ↔ Sat L S M s :=
  ((m.coHom L).satisfaction X M s).symm

/-- The identity semantics map gives the identity comorphism. -/
theorem SemMap.coHom_id (S : Semantics Ty A R) (L : Logic Ty A R) :
    (SemMap.id S).coHom L = Inst.CoHom.id (inst L S) := rfl

/-- **Semantics maps compose contravariantly as comorphisms.** -/
theorem SemMap.coHom_comp {S S' S'' : Semantics Ty A R} (m : SemMap S S') (n : SemMap S' S'')
    (L : Logic Ty A R) : (m.comp n).coHom L = (n.coHom L).comp (m.coHom L) := rfl

end Silmaril.Wasm.Spec
