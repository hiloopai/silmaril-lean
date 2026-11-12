module

public import Silmaril.Wasm.Component.Conformance.DecodeP3.Defs
public import Silmaril.Wasm.Component.BinaryP3.Thms

/-!
# The `BinaryP3` decoder extends the old verified pipeline

* `toRefP3_ofV0`: on the embedding `BinaryP3.Ast.ofV0` of an old AST, the new map to
  reference syntax is the old one (`toRef`);
* **`decodeP3_of_parse`**: whenever the old grammar parses `b` (`Binary.parse b = .ok a`),
  `decodeP3 b = toRef a`, so `decodeP3` agrees with `decodeRef` on every binary
  `decodeRef` reads (with `BinaryP3.parse_ofV0`, conservativity of the new grammar);
* `decodeP3_asyncBuiltins`: on a binary with async built-ins (which `Binary.parse` rejects,
  `parse_asyncBuiltins_fails`), `decodeP3` gives `asyncBuiltinsRef` (kernel-checked).

An earlier step proved that `decodeP3` and the pass-1 runner decoder `Conformance.decode` (its own
grammar `canonXG`) agree on every binary (`DecodeAgree.decode_iff`, commit history of
`Silmaril/Proofs/Wasm/Component/Conformance/DecodeAgree.lean`) and then retired the pass-1
decoder; `asyncBuiltins` moved here from its tests.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component

theorem canons_ofV0 (xs : List Binary.Canon) :
    ToRefP3.canons (xs.map BinaryP3.Canon.ofV0) = .ok (xs.map fun x => .canon (ToRef.canon x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [ToRefP3.canons, BinaryP3.Canon.ofV0, ToRefP3.canonRef, ToRef.canon, ih] <;>
      rfl

mutual

theorem section_ofV0 : ∀ s : Binary.Section,
    ToRefP3.section_ (BinaryP3.Section.ofV0 s) = ToRef.section_ s
  | .custom _ _ | .coreModule _ | .coreInstances _ | .coreTypes _ | .instances _ | .aliases _
  | .types _ | .start _ | .imports _ | .exports _ | .values _ => rfl
  | .canons xs => by
    simp only [BinaryP3.Section.ofV0, ToRefP3.section_, ToRef.section_, canons_ofV0]
  | .component c => by
    simp only [BinaryP3.Section.ofV0, ToRefP3.section_, ToRef.section_, ast_ofV0 c]

theorem sections_ofV0 : ∀ ss : List Binary.Section,
    ToRefP3.sections (BinaryP3.Section.listOfV0 ss) = ToRef.sections ss
  | [] => rfl
  | s :: ss => by
    simp only [BinaryP3.Section.listOfV0, ToRefP3.sections, ToRef.sections, section_ofV0 s,
      sections_ofV0 ss]

theorem ast_ofV0 : ∀ a : Binary.Ast, ToRefP3.ast (BinaryP3.Ast.ofV0 a) = ToRef.ast a
  | .mk ss => by simp only [BinaryP3.Ast.ofV0, ToRefP3.ast, ToRef.ast, sections_ofV0 ss]

end

theorem toRefP3_ofV0 (a : Binary.Ast) : toRefP3 (BinaryP3.Ast.ofV0 a) = toRef a := ast_ofV0 a

/-- **`decodeP3` extends `decodeRef`**: on every binary the old grammar parses, the new
decoder returns the old pipeline's reference syntax. -/
theorem decodeP3_of_parse {b : ByteArray} {a : Binary.Ast} (h : Binary.parse b = .ok a) :
    decodeP3 b = toRef a := by
  simp only [decodeP3, BinaryP3.parse_ofV0 h, toRefP3_ofV0]

theorem decodeP3_eq_decodeRef {b : ByteArray} {a : Binary.Ast} (h : Binary.parse b = .ok a) :
    decodeP3 b = decodeRef b := by
  simp only [decodeP3_of_parse h, decodeRef, h]

/-- The 57 bytes `wasm-tools parse` 1.262.0 writes for

```wat
(component
  (type $s (stream u8))
  (core func (canon waitable-set.new))
  (core func (canon stream.new $s))
  (core func (canon stream.cancel-read $s async))
  (core func (canon task.return (result u32)))
  (core func (canon thread.yield))
  (core func (canon context.get i32 0))
  (core func (canon backpressure.inc)))
```

(`wasm-tools validate --features all` accepts it; its name section is a custom section,
which the reference AST drops). -/
def asyncBuiltins : ByteArray := ⟨#[
  0x00, 0x61, 0x73, 0x6d, 0x0d, 0x00, 0x01, 0x00, 0x07, 0x04, 0x01, 0x66,
  0x01, 0x7d, 0x08, 0x11, 0x07, 0x1f, 0x0e, 0x00, 0x11, 0x00, 0x01, 0x09,
  0x00, 0x79, 0x00, 0x0c, 0x00, 0x0a, 0x7f, 0x00, 0x24, 0x00, 0x16, 0x0e,
  0x63, 0x6f, 0x6d, 0x70, 0x6f, 0x6e, 0x65, 0x6e, 0x74, 0x2d, 0x6e, 0x61,
  0x6d, 0x65, 0x01, 0x05, 0x03, 0x01, 0x00, 0x01, 0x73]⟩

/-- Its reference syntax. -/
def asyncBuiltinsRef : List (Syntax.Definition Silmaril.Wasm.Module) :=
  [.type (.val (.stream (some (.prim .u8)))),
   .canon (.builtin .waitableSetNew),
   .canon (.builtin (.streamNew 0)),
   .canon (.builtin (.streamCancelRead 0 true)),
   .canon (.builtin (.taskReturn (some (.prim .u32)) [])),
   .canon (.builtin .threadYield),
   .canon (.builtin (.contextGet .i32 0)),
   .canon (.builtin .backpressureInc)]

/-- `decodeP3` gives `asyncBuiltinsRef` on `asyncBuiltins` (core modules erased). -/
theorem decodeP3_asyncBuiltins :
    (match decodeP3 asyncBuiltins with
     | .ok d => decide (Silmaril.Wasm.Component.Syntax.Component.map (fun _ => ()) d =
         Silmaril.Wasm.Component.Syntax.Component.map (fun _ => ()) asyncBuiltinsRef)
     | .error _ => false) = true := by
  decide +kernel

theorem parse_asyncBuiltins_fails : (Binary.parse asyncBuiltins).toBool = false := by
  decide +kernel

end Silmaril.Wasm.Component.Conformance
