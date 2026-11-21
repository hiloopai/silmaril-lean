module

public import Silmaril.Wasm.Profiles.Syntax.Defs
public import Silmaril.Wasm.Profiles.Thms
public import Silmaril.Wasm.Profiles.Injections.Thms
import Silmaril.Proofs.Wasm.Profiles.Syntax.Erasure

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax

abbrev Family.declaredEquiv (family : Family) : family.Declared ≃ family.SomeChecked := Typing.declaredEquiv

theorem Family.forget_surjective (family : Family) : _root_.Function.Surjective family.forget := by
  rintro ⟨term, index, valid⟩
  exact ⟨⟨index, term, valid⟩, rfl⟩

theorem Family.forget_eq_iff (family : Family) (left right : family.SomeChecked) :
    family.forget left = family.forget right ↔ left.2.val = right.2.val := Subtype.ext_iff

theorem Family.forget_injective {family : Family} (unique : family.UniqueIndex) :
    _root_.Function.Injective family.forget := Silmaril.Proofs.Wasm.Profiles.Syntax.forget_injective unique

/-- Forgetting the index is reversible only with a separate uniqueness proof.
This does not specify an algorithm to recover the index. -/
noncomputable def Family.acceptedEquiv {family : Family} (unique : family.UniqueIndex) :
    family.SomeChecked ≃ family.Accepted :=
  Equiv.ofBijective family.forget ⟨Family.forget_injective unique, family.forget_surjective⟩

namespace Intrinsic

variable {family : Family}

theorem erasureChecked_injective (witness : Intrinsic family) (index : family.Index) :
    _root_.Function.Injective (witness.erasureChecked (index := index)) :=
  Silmaril.Proofs.Wasm.Profiles.Syntax.erasureChecked_injective witness index

theorem erasureChecked_surjective {witness : Intrinsic family} (covers : witness.Lifts) (index : family.Index) :
    _root_.Function.Surjective (witness.erasureChecked (index := index)) := by
  rintro ⟨raw, valid⟩
  obtain ⟨term, eq⟩ := covers valid
  exact ⟨Quot.mk _ term, Subtype.ext eq⟩

theorem someChecked_surjective {witness : Intrinsic family} (covers : witness.Lifts) :
    _root_.Function.Surjective witness.someChecked :=
  Silmaril.Proofs.Wasm.Profiles.Syntax.someChecked_surjective covers

/-- At this index, checked raw syntax is exactly the intrinsic family
modulo equal erasure. The inverse uses the supplied existence proof. -/
noncomputable def erasureEquiv {witness : Intrinsic family} (covers : witness.Lifts) (index : family.Index) :
    witness.Erasure index ≃ family.Checked index :=
  Equiv.ofBijective witness.erasureChecked ⟨witness.erasureChecked_injective index, erasureChecked_surjective covers index⟩

@[simp] theorem erasureEquiv_apply_mk {witness : Intrinsic family} (covers : witness.Lifts) {index}
    (term : witness.Typed index) : erasureEquiv covers index (Quot.mk _ term) = witness.checked term := rfl

end Intrinsic

theorem moduleIntrinsic_lifts (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] :
    (moduleIntrinsic W).Lifts := HasIntrinsic.moduleLift

theorem functionIntrinsic_lifts (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W]
    (context : HasTyping.Context W) : (functionIntrinsic W context).Lifts := HasIntrinsic.functionLift

namespace Family.Map

variable {source middle target final : Family}

@[simp] theorem id_comp (arrow : source.Map target) : (id source).comp arrow = arrow := rfl
@[simp] theorem comp_id (arrow : source.Map target) : arrow.comp (id target) = arrow := rfl

theorem comp_assoc (first : source.Map middle) (second : middle.Map target) (third : target.Map final) :
    (first.comp second).comp third = first.comp (second.comp third) := rfl

@[simp] theorem checked_val (arrow : source.Map target) {index} (term : source.Checked index) :
    (arrow.checked term).val = arrow.raw term.val := rfl

@[simp] theorem checked_comp (first : source.Map middle) (second : middle.Map target) {index}
    (term : source.Checked index) : (first.comp second).checked term = second.checked (first.checked term) := rfl

@[simp] theorem accepted_forget (arrow : source.Map target) (term : source.SomeChecked) :
    arrow.accepted (source.forget term) = target.forget (arrow.someChecked term) := rfl

end Family.Map

namespace Intrinsic.Map

@[simp] theorem checked_natural {source target : Family} {origin : Intrinsic source} {into : Intrinsic target}
    {arrow : source.Map target} (move : origin.Map into arrow) {index} (term : origin.Typed index) :
    into.checked (move.typed term) = arrow.checked (origin.checked term) := Subtype.ext (move.erase_eq term)

theorem erasureChecked_natural {source target : Family} {origin : Intrinsic source} {into : Intrinsic target}
    {arrow : source.Map target} (move : origin.Map into arrow) {index} (term : origin.Erasure index) :
    into.erasureChecked (move.onErasure term) = arrow.checked (origin.erasureChecked term) := by
  induction term using Quot.ind with
  | mk representative => exact move.checked_natural representative

end Intrinsic.Map

namespace Core

theorem moduleIndexUnique : moduleSyntax.UniqueIndex := @Validation.ModuleOk.unique

theorem functionIndexUnique (context : Validation.Context) : (functionSyntax context).UniqueIndex :=
  Silmaril.Proofs.Wasm.Profiles.Syntax.coreFunction_unique context

abbrev moduleLifts : moduleWitness.Lifts := moduleIntrinsic_lifts Wasm3
abbrev functionLifts (context : Validation.Context) : (functionWitness context).Lifts :=
  functionIntrinsic_lifts Wasm3 context

def partsToModule : partsSyntax.Map moduleSyntax := ⟨Wasm.ModuleParts.toCore, id, id⟩

def moduleToParts : moduleSyntax.Map partsSyntax :=
  ⟨Wasm.Module.split, id, fun {term _} valid => term.toCore_split.symm ▸ valid⟩

def checkedPartsEquiv (iface : Validation.CModuleType) : moduleSyntax.Checked iface ≃ partsSyntax.Checked iface where
  toFun := moduleToParts.checked
  invFun := partsToModule.checked
  left_inv term := Subtype.ext term.val.toCore_split
  right_inv term := Subtype.ext term.val.split_toCore

/-- A view of the very same intrinsic witnesses above the section split. -/
def partsWitness : Intrinsic partsSyntax :=
  ⟨moduleWitness.Typed, fun term => (moduleWitness.erase term).split,
    fun term => (moduleToParts.checked (moduleWitness.checked term)).property⟩

def toPartsWitness : moduleWitness.Map partsWitness moduleToParts := ⟨id, fun _ => rfl⟩

theorem partsLifts : partsWitness.Lifts := by
  intro _ parts valid
  obtain ⟨term, eq⟩ := moduleLifts valid
  exact ⟨term, (congrArg Wasm.Module.split eq).trans parts.split_toCore⟩

end Core

namespace Lime

theorem moduleIndexUnique : moduleSyntax.UniqueIndex := fun _ _ => Subsingleton.elim (α := Unit) _ _

theorem functionIndexUnique (context : Lime1.Validation.Context) : (functionSyntax context).UniqueIndex :=
  fun left right => Option.some.inj (left.1.symm.trans right.1)

end Lime

/-- Native Wasm1 to native Lime. Both module judgments have `Unit` index. -/
def wasm1ModuleToLime : (moduleFamily Wasm1).Map Lime.moduleSyntax :=
  ⟨Injections.wasm1ToLime, id, V1.Validation.ModuleValid.toLime⟩

/-- Native function injection at the existing translated validation context. -/
def wasm1FunctionToLime (context : V1.Validation.Context) :
    (functionFamily Wasm1 context).Map (Lime.functionSyntax context.toLime) :=
  ⟨Injections.wasm1ToLimeFunction, id, fun ⟨resolved, _, body⟩ => ⟨resolved, trivial, body.toLime⟩⟩

/-- A feature-guarded source module keeps its actual Core interface index. -/
def functionalToCore (gc : GCMode) (exn : ExceptionMode) :
    (moduleFamily (FunctionalCore gc exn)).Map Core.moduleSyntax :=
  ⟨FunctionalCore.toCore gc exn, id, id⟩

def functionalOfLE {gc nextGC : GCMode} {exn nextExn : ExceptionMode}
    (included : FunctionalCore.features gc exn ≤ FunctionalCore.features nextGC nextExn) :
    (moduleFamily (FunctionalCore gc exn)).Map (moduleFamily (FunctionalCore nextGC nextExn)) :=
  ⟨FunctionalCore.ofLE included, id, id⟩

theorem functional_ofLE_toCore {gc nextGC : GCMode} {exn nextExn : ExceptionMode}
    (included : FunctionalCore.features gc exn ≤ FunctionalCore.features nextGC nextExn) :
    (functionalOfLE included).comp (functionalToCore nextGC nextExn) = functionalToCore gc exn := rfl

end Silmaril.Wasm.Profiles.Syntax
