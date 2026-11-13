module

public import Silmaril.Wasm.Spec.Maps.Thms

@[expose] public section

/-!
# Change of base in the trace-institution format

The trace-institution format (`Silmaril.Wasm.Spec.Format`) is generic in the function types `Ty` of
interfaces and in the payloads `A` (arguments) and `R` (results) of events. This module moves
logics and semantics between two such bases along

* a map of function types `τ : Ty → Ty'` (on interfaces: `Iface.map τ`, a functor
  `Iface.mapF τ`; fully faithful when `τ` is injective, with inverse `Iface.unmapHom`);
* payload maps `α : A → A'`, `β : R → R'` (on events: `Event.mapP τ α β`, which keeps the
  kind and index of every event).

Constructions:

* `Logic.pull L' τ α β : Logic Ty A R`: an `L'`-formula at `X.map τ` read on the translated
  traces (`evImage`);
* `Semantics.push S τ α β : Semantics Ty' A' R'`: `S`-programs, at the image interfaces, with
  translated traces (`PushProg`);
* `Semantics.restrict S τ : Semantics Ty A R`: `S`-programs at the image interfaces `X.map τ`,
  read at `X` (only the indices are recast);
* `Semantics.sum`: programs of either semantics (joint models).

The comorphism `inst (L'.pull τ α β) S → inst L' (S.push τ α β)` is in
`Silmaril.Wasm.Spec.Joint.Defs`; lemmas in `Silmaril.Wasm.Spec.Joint.Base.Thms`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec

open CategoryTheory

variable {Ty Ty' A A' R R' : Type}

/-! ## Good sets under maps -/

/-- The image of a good set under a map of events is good. -/
theorem Good.image_map {α β : Type} (f : α → β) {T : Set (List α)} (hT : Good T) :
    Good (List.map f '' T) where
  nil_mem := ⟨[], hT.nil_mem, rfl⟩
  of_prefix := by
    rintro s t ⟨u, hu, rfl⟩ hs
    refine ⟨u.take s.length, hT.of_prefix hu (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm

/-! ## Side events and interfaces along type maps -/

/-- Map a side event: its index along `f`, its payload along `α` or `β`. -/
def SideEv.mapP {n m : ℕ} (f : Fin n → Fin m) (α : A → A') (β : R → R') :
    SideEv A R n → SideEv A' R' m
  | .ask i a => .ask (f i) (α a)
  | .ans i r => .ans (f i) (β r)

namespace Iface

/-- The interface whose function types are mapped by `τ`. -/
def map (τ : Ty → Ty') (X : Iface Ty) : Iface Ty' := ⟨X.imports.map τ, X.exports.map τ⟩

@[simp] theorem map_imports (τ : Ty → Ty') (X : Iface Ty) : (X.map τ).imports = X.imports.map τ :=
  rfl
@[simp] theorem map_exports (τ : Ty → Ty') (X : Iface Ty) : (X.map τ).exports = X.exports.map τ :=
  rfl

/-- An import of `X` as an import of `X.map τ`. -/
def impTo (τ : Ty → Ty') (X : Iface Ty) (i : X.Imp) : (X.map τ).Imp :=
  Fin.cast (List.length_map τ).symm i
/-- An import of `X.map τ` as an import of `X`. -/
def impFrom (τ : Ty → Ty') (X : Iface Ty) (i : (X.map τ).Imp) : X.Imp :=
  Fin.cast (List.length_map τ) i
/-- An export of `X` as an export of `X.map τ`. -/
def expTo (τ : Ty → Ty') (X : Iface Ty) (j : X.Exp) : (X.map τ).Exp :=
  Fin.cast (List.length_map τ).symm j
/-- An export of `X.map τ` as an export of `X`. -/
def expFrom (τ : Ty → Ty') (X : Iface Ty) (j : (X.map τ).Exp) : X.Exp :=
  Fin.cast (List.length_map τ) j

@[simp] theorem impFrom_impTo (τ : Ty → Ty') (X : Iface Ty) (i : X.Imp) :
    impFrom τ X (impTo τ X i) = i := rfl
@[simp] theorem impTo_impFrom (τ : Ty → Ty') (X : Iface Ty) (i : (X.map τ).Imp) :
    impTo τ X (impFrom τ X i) = i := rfl
@[simp] theorem expFrom_expTo (τ : Ty → Ty') (X : Iface Ty) (j : X.Exp) :
    expFrom τ X (expTo τ X j) = j := rfl
@[simp] theorem expTo_expFrom (τ : Ty → Ty') (X : Iface Ty) (j : (X.map τ).Exp) :
    expTo τ X (expFrom τ X j) = j := rfl

theorem impTo_injective (τ : Ty → Ty') (X : Iface Ty) : Function.Injective (impTo τ X) :=
  fun a b h => by simpa using congrArg (impFrom τ X) h
theorem impFrom_injective (τ : Ty → Ty') (X : Iface Ty) : Function.Injective (impFrom τ X) :=
  fun a b h => by simpa using congrArg (impTo τ X) h
theorem expTo_injective (τ : Ty → Ty') (X : Iface Ty) : Function.Injective (expTo τ X) :=
  fun a b h => by simpa using congrArg (expFrom τ X) h
theorem expFrom_injective (τ : Ty → Ty') (X : Iface Ty) : Function.Injective (expFrom τ X) :=
  fun a b h => by simpa using congrArg (expTo τ X) h

/-- The type of a mapped import. -/
theorem get_imports_map (τ : Ty → Ty') (X : Iface Ty) (i : (X.map τ).Imp) :
    (X.map τ).imports.get i = τ (X.imports.get (impFrom τ X i)) :=
  List.getElem_map ..

/-- The type of a mapped export. -/
theorem get_exports_map (τ : Ty → Ty') (X : Iface Ty) (j : (X.map τ).Exp) :
    (X.map τ).exports.get j = τ (X.exports.get (expFrom τ X j)) :=
  List.getElem_map ..

/-- An interface morphism along `τ`. -/
def mapHom (τ : Ty → Ty') {X Y : Iface Ty} (f : X ⟶ Y) : X.map τ ⟶ Y.map τ where
  exp j := expTo τ Y (f.exp (expFrom τ X j))
  exp_inj := (expTo_injective τ Y).comp (f.exp_inj.comp (expFrom_injective τ X))
  exp_ty j := by rw [get_exports_map, get_exports_map, expFrom_expTo, f.exp_ty]
  imp i := impTo τ Y (f.imp (impFrom τ X i))
  imp_inj := (impTo_injective τ Y).comp (f.imp_inj.comp (impFrom_injective τ X))
  imp_ty i := by rw [get_imports_map, get_imports_map, impFrom_impTo, f.imp_ty]

/-- **Fullness**: for injective `τ`, a morphism between mapped interfaces comes from one between
the interfaces. -/
def unmapHom {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y : Iface Ty}
    (g : X.map τ ⟶ Y.map τ) : X ⟶ Y where
  exp j := expFrom τ Y (g.exp (expTo τ X j))
  exp_inj := (expFrom_injective τ Y).comp (g.exp_inj.comp (expTo_injective τ X))
  exp_ty j := hτ (by
    have h := g.exp_ty (expTo τ X j)
    rw [get_exports_map, get_exports_map, expFrom_expTo] at h
    exact h)
  imp i := impFrom τ Y (g.imp (impTo τ X i))
  imp_inj := (impFrom_injective τ Y).comp (g.imp_inj.comp (impTo_injective τ X))
  imp_ty i := hτ (by
    have h := g.imp_ty (impTo τ X i)
    rw [get_imports_map, get_imports_map, impFrom_impTo] at h
    exact h)

@[simp] theorem mapHom_exp (τ : Ty → Ty') {X Y : Iface Ty} (f : X ⟶ Y) (j : (X.map τ).Exp) :
    (mapHom τ f).exp j = expTo τ Y (f.exp (expFrom τ X j)) := rfl
@[simp] theorem mapHom_imp (τ : Ty → Ty') {X Y : Iface Ty} (f : X ⟶ Y) (i : (X.map τ).Imp) :
    (mapHom τ f).imp i = impTo τ Y (f.imp (impFrom τ X i)) := rfl
@[simp] theorem unmapHom_exp {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y : Iface Ty}
    (g : X.map τ ⟶ Y.map τ) (j : X.Exp) :
    (unmapHom hτ g).exp j = expFrom τ Y (g.exp (expTo τ X j)) := rfl
@[simp] theorem unmapHom_imp {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y : Iface Ty}
    (g : X.map τ ⟶ Y.map τ) (i : X.Imp) :
    (unmapHom hτ g).imp i = impFrom τ Y (g.imp (impTo τ X i)) := rfl

/-- **The interface functor of a type map.** -/
def mapF (τ : Ty → Ty') : Iface Ty ⥤ Iface Ty' where
  obj := map τ
  map := mapHom τ
  map_id _ := Hom.ext rfl rfl
  map_comp _ _ := Hom.ext rfl rfl

@[simp] theorem mapF_obj (τ : Ty → Ty') (X : Iface Ty) : (mapF τ).obj X = X.map τ := rfl
@[simp] theorem mapF_map (τ : Ty → Ty') {X Y : Iface Ty} (f : X ⟶ Y) :
    (mapF τ).map f = mapHom τ f := rfl

/-- `unmapHom` inverts `mapHom`. -/
theorem unmapHom_mapHom {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y : Iface Ty}
    (f : X ⟶ Y) : unmapHom hτ (mapHom τ f) = f := Hom.ext rfl rfl

/-- `mapHom` inverts `unmapHom`. -/
theorem mapHom_unmapHom {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y : Iface Ty}
    (g : X.map τ ⟶ Y.map τ) : mapHom τ (unmapHom hτ g) = g := Hom.ext rfl rfl

/-- Composing a mapped morphism with a morphism between mapped interfaces. -/
theorem mapHom_comp_eq {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y Z : Iface Ty}
    (f : X ⟶ Y) (g : Y.map τ ⟶ Z.map τ) :
    mapHom τ f ≫ g = mapHom τ (f ≫ unmapHom hτ g) := Hom.ext rfl rfl

/-- `unmapHom` of a composite with a mapped morphism. -/
theorem unmapHom_mapHom_comp {τ : Ty → Ty'} (hτ : Function.Injective τ) {X Y Z : Iface Ty}
    (f : X ⟶ Y) (g : Y.map τ ⟶ Z.map τ) :
    unmapHom hτ (mapHom τ f ≫ g) = f ≫ unmapHom hτ g := Hom.ext rfl rfl

end Iface

/-! ## Events along type and payload maps -/

/-- An event at `X` as an event at `X.map τ`, payloads mapped by `α` and `β`. -/
def Event.mapP (τ : Ty → Ty') (α : A → A') (β : R → R') {X : Iface Ty} :
    Event A R X → Event A' R' (X.map τ) :=
  Sum.map (SideEv.mapP (Iface.impTo τ X) α β) (SideEv.mapP (Iface.expTo τ X) α β)

/-- An event at `X.map τ` read at `X` (indices recast, payloads kept). -/
def Event.unmapIdx (τ : Ty → Ty') {X : Iface Ty} : Event A R (X.map τ) → Event A R X :=
  Sum.map (SideEv.mapP (Iface.impFrom τ X) id id) (SideEv.mapP (Iface.expFrom τ X) id id)

/-- The translated traces of a trace set. -/
def evImage (τ : Ty → Ty') (α : A → A') (β : R → R') {X : Iface Ty}
    (T : Set (List (Event A R X))) : Set (List (Event A' R' (X.map τ))) :=
  List.map (Event.mapP τ α β) '' T

/-! ## Pulling logics, pushing and restricting semantics -/

/-- **A logic pulled back along a change of base**: an `L'`-formula at `X.map τ`, satisfied by a
trace set when the translated traces satisfy it. -/
abbrev Logic.pull (L' : Logic Ty' A' R') (τ : Ty → Ty') (α : A → A') (β : R → R') :
    Logic Ty A R where
  Fm X := L'.Fm (X.map τ)
  Sat T φ := L'.Sat (evImage τ α β T) φ

/-- A program of `S` sitting at an image interface `X' = src.map τ`. -/
structure PushProg (S : Semantics Ty A R) (τ : Ty → Ty') (X' : Iface Ty') where
  /-- The source interface. -/
  src : Iface Ty
  /-- The program. -/
  prog : S.Prog src
  /-- The interface is the image of the source interface. -/
  eq : src.map τ = X'

/-- Transport a trace set along an equality of interfaces. -/
def castTraces {X X' : Iface Ty'} (h : X = X') (T : Set (List (Event A' R' X))) :
    Set (List (Event A' R' X')) :=
  Eq.rec (motive := fun Y _ => Set (List (Event A' R' Y))) T h

/-- **A semantics pushed along a change of base**: `S`-programs at the image interfaces, with
translated traces. -/
abbrev Semantics.push (S : Semantics Ty A R) (τ : Ty → Ty') (α : A → A') (β : R → R') :
    Semantics Ty' A' R' where
  Prog := PushProg S τ
  traces p := castTraces p.eq (evImage τ α β (S.traces p.prog))
  good p := by
    obtain ⟨src, prog, rfl⟩ := p
    exact (S.good prog).image_map _

/-- A program at the image of its interface, in the pushed semantics. -/
def PushProg.ofProg {S : Semantics Ty A R} {τ : Ty → Ty'} {X : Iface Ty} (p : S.Prog X) :
    PushProg S τ (X.map τ) :=
  ⟨X, p, rfl⟩

/-- **A semantics restricted along a type map**: the `S`-programs at `X.map τ`, read at `X`. -/
abbrev Semantics.restrict (S : Semantics Ty' A R) (τ : Ty → Ty') : Semantics Ty A R where
  Prog X := S.Prog (X.map τ)
  traces p := List.map (Event.unmapIdx τ) '' S.traces p
  good p := (S.good p).image_map _

/-- **Joint models**: a program of either semantics. -/
abbrev Semantics.sum (S₁ S₂ : Semantics Ty A R) : Semantics Ty A R where
  Prog X := S₁.Prog X ⊕ S₂.Prog X
  traces
    | .inl p => S₁.traces p
    | .inr q => S₂.traces q
  good
    | .inl p => S₁.good p
    | .inr q => S₂.good q

/-- The left injection of joint models. -/
def SemMap.inl (S₁ S₂ : Semantics Ty A R) : SemMap S₁ (S₁.sum S₂) := ⟨fun p => .inl p, fun _ => rfl⟩

/-- The right injection of joint models. -/
def SemMap.inr (S₁ S₂ : Semantics Ty A R) : SemMap S₂ (S₁.sum S₂) := ⟨fun p => .inr p, fun _ => rfl⟩

end Silmaril.Wasm.Spec
