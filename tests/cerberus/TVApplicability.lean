import Silmaril.Project.Shapes.CTV.Thms
import Silmaril.Project.CTV.Examples.Defs
import Silmaril.Cerberus.Names.Defs

/-! Regression tests for the per-type profile check (`Silmaril.Cerberus.TV.Applicability`), from the
review of #911: the scan covers the runtime functions the program reaches, so a runtime function
with a floating result blocks the x86-64 profile (it did not when only the program part was
scanned). Kernel-checked with `cbv`. -/

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Project.CTV.Examples Silmaril.Project.Shapes.CTV

set_option maxRecDepth 100000

/-- The `return 1 + 2;` file reaches its 3 runtime functions, which name `_Bool`. -/
example : (reachableStdlib foldSourceBindings).length = 3 := by cbv
example : mentions foldSourceBindings = [.scalar .bool, .scalar .int] := by cbv

/-- A synthetic runtime function with a floating result, under `main`'s symbol (so reached). -/
def floatRuntime : Codec.FileBindings :=
  match foldSourceBindings.funInfo with
  | (s, l, _) :: _ => { foldSourceBindings with
      stdlib := foldSourceBindings.stdlib ++ [(s, .builtinDecl l (.object .floating) [])] }
  | [] => foldSourceBindings

set_option maxHeartbeats 4000000 in
example : (mentions floatRuntime).contains (.scalar .float) = true := by cbv

set_option maxHeartbeats 4000000 in
example : ¬ linuxX86_64.AppliesTo floatRuntime := by
  unfold Profile.AppliesTo; rw [show ((mentions floatRuntime).all linuxX86_64.coherentAt) = false by cbv]
  decide

/-- An unreachable runtime function is not scanned: it cannot run. -/
def unreachableFloatRuntime : Codec.FileBindings :=
  { foldSourceBindings with
      stdlib := foldSourceBindings.stdlib ++ [(⟨⟨[]⟩, 999999, .none⟩, .builtinDecl .unknown (.object .floating) [])] }

example : mentions unreachableFloatRuntime = [.scalar .bool, .scalar .int] := by cbv

/-! From the re-review of #911 (72f6a597): implementation constants, `byte`, and failing closed. -/

/-- A call's `Name.impl c` names exactly `c`'s key in the `impl` map. -/
example : implsTree (Codec.name.enc (.impl .charactersPlainCharIsSigned)) =
    (implKey .charactersPlainCharIsSigned).toList := by cbv

/-- A floating-typed implementation constant reached through a reachable runtime function blocks. -/
def implFloat : Codec.FileBindings :=
  match foldSourceBindings.funInfo with
  | (s, _, _) :: _ => { foldSourceBindings with
      stdlib := foldSourceBindings.stdlib ++
        [(s, .function (.object .integer) [] ⟨[], (), .call (.impl .charactersPlainCharIsSigned) []⟩)],
      impl := [(.charactersPlainCharIsSigned, .constant (.object .floating) ⟨[], (), .val (.unit)⟩)] }
  | [] => foldSourceBindings

set_option maxHeartbeats 4000000 in
example : (reachableImpl implFloat).length = 1 := by cbv
set_option maxHeartbeats 4000000 in
example : (mentions implFloat).contains (.scalar .float) = true := by cbv

/-- Cerberus's `byte` type counts as `unsigned char` (it used to name nothing). -/
example : mentionsTree (Codec.ctype.enc (Ctype.mk [] .byte)) = [.scalar .uchar] := by cbv

/-- Every constructor tag of the C type vocabulary in `Names` is one `mentionOf` classifies (a
constructor added to the vocabulary fails here until it is classified). -/
example : ((Silmaril.Cerberus.Names.types.filter fun t => ["Ctype.ctype_", "Ctype.basicType",
    "Ctype.floatingType", "Ctype.realFloatingType", "IntegerType.integerType",
    "IntegerType.integerBaseType"].contains t.cerberus).flatMap fun t => t.renames.map (·.1)).all
      (ctypeVocabulary.contains ·) = true := by decide +kernel

/-- An unknown type constructor cannot silently pass the per-type filter. -/
example : mentionsTree (Silmaril.TaggedCodec.node "Ctype"
    [Silmaril.TaggedCodec.node "$list" [], Silmaril.TaggedCodec.node "FutureType" []]) =
    [.outside "FutureType"] := by cbv
example : (mentionsTree (Silmaril.TaggedCodec.node "Basic"
    [Silmaril.TaggedCodec.node "FutureBasic" []])).all linuxX86_64.coherentAt = false := by cbv
example : (mentionsTree (Silmaril.TaggedCodec.node "Signed"
    [Silmaril.TaggedCodec.node "FutureInt" []])).all linuxX86_64.coherentAt = false := by cbv
example : (mentionsTree (Silmaril.TaggedCodec.node "RealFloating"
    [Silmaril.TaggedCodec.node "FutureFloat" []])).all linuxX86_64.coherentAt = false := by cbv
