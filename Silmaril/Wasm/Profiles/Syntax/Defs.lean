module

public import Silmaril.Wasm.Profiles.Defs

/-! Indexed views of the existing profile syntax and typing instances.
There is no second instance registry. Intrinsic soundness and coverage are
separate, so a useful native slice does not claim to represent every term. -/

@[expose] public section

namespace Silmaril.Wasm.Profiles.Syntax

structure Family where
  Raw : Type
  Index : Type
  ok : Raw → Index → Prop

abbrev Family.Untyped (family : Family) := family.Raw
abbrev Family.Checked (family : Family) := Typing.Checked family.ok
abbrev Family.SomeChecked (family : Family) := Typing.SomeChecked family.ok
abbrev Family.Declared (family : Family) := Typing.Declared family.ok
abbrev Family.Accepted (family : Family) := Typing.Accepted family.ok

def Family.forget (family : Family) (term : family.SomeChecked) : family.Accepted :=
  ⟨term.2.val, term.1, term.2.property⟩

def Family.UniqueIndex (family : Family) : Prop :=
  ∀ {term left right}, family.ok term left → family.ok term right → left = right

/-- One function family per ambient context. The index is the actual
function type used by that dialect's typing judgment. -/
def functionFamily (W : Type) [HasSyntax W] [HasTyping W] (context : HasTyping.Context W) : Family :=
  ⟨Function W, HasTyping.FuncType W, HasTyping.funcOk context⟩

/-- The actual interface index when exposed by native validation; for
Wasm1 and Lime the existing module judgment validates without one. -/
def moduleFamily (W : Type) [HasSyntax W] [HasTyping W] : Family :=
  ⟨Module W, HasTyping.Interface W, HasTyping.moduleOk⟩

/-- Change the raw representation without changing the judgment index. -/
def Family.represent (family : Family) (Repr : Type) (toRaw : Repr → family.Untyped) : Family :=
  ⟨Repr, family.Index, fun term index => family.ok (toRaw term) index⟩

structure Intrinsic (family : Family) where
  Typed : family.Index → Type
  erase : ∀ {index}, Typed index → family.Untyped
  sound : ∀ {index} (term : Typed index), family.ok (erase term) index

abbrev Intrinsic.SomeTyped {family : Family} (witness : Intrinsic family) := Σ index, witness.Typed index

/-- Actual lifting at the same index with exact erasure. Soundness alone
does not supply a lift, and this proposition does not require an algorithm. -/
def Intrinsic.Lifts {family : Family} (witness : Intrinsic family) : Prop :=
  ∀ {index raw}, family.ok raw index → ∃ term : witness.Typed index, witness.erase term = raw

def Intrinsic.checked {family : Family} (witness : Intrinsic family) {index} (term : witness.Typed index) :
    family.Checked index := ⟨witness.erase term, witness.sound term⟩

def Intrinsic.someChecked {family : Family} (witness : Intrinsic family) (term : witness.SomeTyped) :
    family.SomeChecked := ⟨term.1, witness.checked term.2⟩

/-- Equality of erased syntax at a *fixed* judgment index, not semantic
equivalence or equality of intrinsic derivation trees. -/
abbrev Intrinsic.Erasure {family : Family} (witness : Intrinsic family) (index : family.Index) :=
  Quot (fun left right : witness.Typed index => witness.erase left = witness.erase right)

def Intrinsic.erasureChecked {family : Family} (witness : Intrinsic family) {index} :
    witness.Erasure index → family.Checked index :=
  Quot.lift witness.checked (fun _ _ eq => Subtype.ext eq)

def functionIntrinsic (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W]
    (context : HasTyping.Context W) : Intrinsic (functionFamily W context) :=
  ⟨TypedFunction W context, HasIntrinsic.eraseFunction, HasIntrinsic.functionSound⟩

def moduleIntrinsic (W : Type) [HasSyntax W] [HasTyping W] [HasIntrinsic W] : Intrinsic (moduleFamily W) :=
  ⟨TypedModule W, HasIntrinsic.eraseModule, HasIntrinsic.moduleSound⟩

/-- The laws associate a change of index with a change of raw syntax.
This is not a semantics, nor necessarily an embedding or reflection. -/
structure Family.Map (source target : Family) where
  raw : source.Untyped → target.Untyped
  index : source.Index → target.Index
  sound : ∀ {term ty}, source.ok term ty → target.ok (raw term) (index ty)

namespace Family.Map

variable {source middle target : Family}

def id (family : Family) : family.Map family := ⟨_root_.id, _root_.id, _root_.id⟩

def comp (first : source.Map middle) (second : middle.Map target) : source.Map target :=
  ⟨second.raw ∘ first.raw, second.index ∘ first.index, fun valid => second.sound (first.sound valid)⟩

def checked (arrow : source.Map target) {index} (term : source.Checked index) :
    target.Checked (arrow.index index) := ⟨arrow.raw term.val, arrow.sound term.property⟩

def someChecked (arrow : source.Map target) (term : source.SomeChecked) : target.SomeChecked :=
  ⟨arrow.index term.1, arrow.checked term.2⟩

def accepted (arrow : source.Map target) (term : source.Accepted) : target.Accepted :=
  ⟨arrow.raw term.val, term.property.elim fun index valid => ⟨arrow.index index, arrow.sound valid⟩⟩

end Family.Map

/-- An explicit map of witnesses above a sound raw/index map. Such a map
is supplied, not inferred from validity preservation. -/
structure Intrinsic.Map {source target : Family} (origin : Intrinsic source) (into : Intrinsic target)
    (arrow : source.Map target) where
  typed : ∀ {index}, origin.Typed index → into.Typed (arrow.index index)
  erase_eq : ∀ {index} (term : origin.Typed index), into.erase (typed term) = arrow.raw (origin.erase term)

namespace Intrinsic.Map

variable {source middle target : Family}
variable {origin : Intrinsic source} {via : Intrinsic middle} {into : Intrinsic target}
variable {first : source.Map middle} {second : middle.Map target}

def id (witness : Intrinsic source) : witness.Map witness (Family.Map.id source) :=
  ⟨_root_.id, fun _ => rfl⟩

def comp (move : origin.Map via first) (next : via.Map into second) : origin.Map into (first.comp second) :=
  ⟨fun term => next.typed (move.typed term), fun term =>
    (next.erase_eq (move.typed term)).trans (congrArg second.raw (move.erase_eq term))⟩

def onErasure (move : origin.Map via first) {index} : origin.Erasure index → via.Erasure (first.index index) :=
  Quot.lift (fun term => Quot.mk _ (move.typed term)) fun left right eq =>
    Quot.sound ((move.erase_eq left).trans ((congrArg first.raw eq).trans (move.erase_eq right).symm))

end Intrinsic.Map

namespace Core

abbrev moduleSyntax := moduleFamily Wasm3
abbrev functionSyntax := functionFamily Wasm3
abbrev moduleWitness := moduleIntrinsic Wasm3
abbrev functionWitness := functionIntrinsic Wasm3

/-- The same modules and judgment, viewed through the existing sections /
definitions decomposition. This does not validate the sections alone. -/
abbrev partsSyntax := moduleSyntax.represent (Wasm.ModuleParts Wasm.Func) Wasm.ModuleParts.toCore

end Core

namespace Lime

abbrev moduleSyntax := moduleFamily Profiles.Lime
abbrev functionSyntax := functionFamily Profiles.Lime

end Lime

end Silmaril.Wasm.Profiles.Syntax
