module

public import Silmaril.Wasm.Wat

/-! # Core 3 module quotation regressions

These compare ordinary source ASTs, including recursive-group boundaries, name
resolution, abbreviation expansion, and independent segment index spaces. They do
not infer validation from successful parsing.
-/

@[expose] public section
namespace Silmaril.Wasm.Wat.CoreModuleExamples

def recursive := wat3! r#"
(module
  (rec
    (type $"node" (sub (struct (field $"payload" (mut i8))
                              (field (ref null $array)))))
    (type $array (array (mut (ref null $node)))))
  (type $child (sub final $node (struct (field (mut i8))
                                      (field (ref null $array)))))
  (func (param (ref $node)) (result i32)
    local.get 0 struct.get_u $"node" $payload))
"#

example : recursive.types[0] = ⟨[
    ⟨false, [], .struct [⟨.var, .packed .i8⟩,
      ⟨.const, .val (.ref ⟨true, .typeIdx ⟨1⟩⟩)⟩]⟩,
    ⟨true, [], .array ⟨.var, .val (.ref ⟨true, .typeIdx ⟨0⟩⟩)⟩⟩]⟩ := rfl
example : recursive.types[1].types[0].supertypes = [⟨0⟩] := rfl
example : recursive.funcs[0].body = [.localGet ⟨0⟩, .structGet (some .unsigned) ⟨0⟩ ⟨0⟩] := rfl

/-- Equal bodies in different recursive groups are not interchangeable implicit types. -/
def interned := wat3! r#"
(module
  (rec (type $first (func)) (type $second (func)))
  (type $open (sub (func)))
  (func $explicit (type $open))
  (func $implicit)
  (func $reused))
"#

example : interned.types.length = 3 := rfl
example : interned.funcs.map (·.type) = [⟨2⟩, ⟨3⟩, ⟨3⟩] := rfl

/-- Type-declaration parameter names are documentation; type-use names bind locals. -/
def documentedNames := wat3! r#"
(module
  (type $t (func (param $x i32) (param $x i64) (result v128 exnref)))
  (func (type $t) (param $a i32) (param $b i64) (result v128 exnref)
    (local $"scratch" (ref null $t))
    local.get $b local.get $scratch drop drop unreachable))
"#

example : documentedNames.funcs[0].locals = [.ref ⟨true, .typeIdx ⟨0⟩⟩] := rfl
example : documentedNames.funcs[0].body =
    [.localGet ⟨1⟩, .localGet ⟨2⟩, .drop, .drop, .unreachable] := rfl

/-- Imports and definitions share an index space only within their own kind. -/
def declarations := wat3! r#"
(module
  (type $event (func (param i32 externref)))
  (func $host (export "host") (import "env" "f") (result i64))
  (tag $incoming (import "env" "incoming") (type $event))
  (global $g (import "env" "g") (mut i64))
  (memory $m0 (import "env" "mem") i64 1 9)
  (table $t0 (import "env" "tab") i64 0 8 externref)
  (tag $outgoing (export "event") (type $event))
  (global $answer (export "answer") i32 (i32.const 42))
  (memory $m1 (export "memory") i64 2 4)
  (table $t1 (export "table") i64 2 6 (ref extern) (ref.null extern))
  (func $entry (export "entry"))
  (start $entry))
"#

example : declarations.imports.length = 5 := rfl
example : declarations.tags = [⟨0⟩] := rfl
example : declarations.exports = [⟨"host", .func ⟨0⟩⟩, ⟨"event", .tag ⟨1⟩⟩,
    ⟨"answer", .global ⟨1⟩⟩, ⟨"memory", .memory ⟨1⟩⟩,
    ⟨"table", .table ⟨1⟩⟩, ⟨"entry", .func ⟨1⟩⟩] := rfl
example : declarations.start = some ⟨1⟩ := rfl
example : declarations.memories = [⟨.i64, ⟨2, some 4⟩⟩] := rfl
example : declarations.tables[0].type = ⟨.i64, ⟨2, some 6⟩, ⟨false, .abstract .extern⟩⟩ := rfl

/-- Anonymous segments from inline initializers occupy real indices before later names. -/
def segments := wat3! r#"
(module
  (func $f)
  (memory $m (export "memory") i64 (data "\00\ff" "é"))
  (table $t (export "table") i64 funcref (elem $f $f))
  (data $passive "hello")
  (data $active (memory $m) (offset i64.const 7) "world")
  (elem $passive func $f)
  (elem $declared declare funcref (item ref.func $f) (ref.null func))
  (elem $active (table $t) (i64.const 3) func $f)
  (func $use memory.init $m $passive data.drop $active
    table.init $t $passive elem.drop $declared))
"#

example : segments.memories = [⟨.i64, ⟨1, some 1⟩⟩] := rfl
example : segments.tables[0].type = ⟨.i64, ⟨2, some 2⟩, ⟨true, .abstract .func⟩⟩ := rfl
example : segments.data[0].bytes = ⟨#[0, 255, 195, 169]⟩ := rfl
example : segments.data[0].mode = .active ⟨0⟩ [.intConst .i64 0] := rfl
example : segments.data[1].mode = .passive := rfl
example : segments.data[2].mode = .active ⟨0⟩ [.intConst .i64 7] := rfl
example : segments.elems[1].type = ⟨false, .abstract .func⟩ := rfl
example : segments.elems[2].mode = .declarative := rfl
example : segments.elems[3].mode = .active ⟨0⟩ [.intConst .i64 3] := rfl
example : segments.funcs[1].body =
    [.memoryInit ⟨0⟩ ⟨1⟩, .dataDrop ⟨2⟩, .tableInit ⟨0⟩ ⟨1⟩, .elemDrop ⟨2⟩] := rfl

/-- Folded table entries preserve the declared reference type and inferred length. -/
def foldedTable := wat3! r#"
(module (func $f)
  (table funcref (elem (ref.func $f) (ref.null func)))
  (table externref (elem))
  (memory (data)))
"#

example : foldedTable.tables[0].init = [.refNull (.abstract .func)] := rfl
example : foldedTable.elems[0].init = [[.refFunc ⟨0⟩], [.refNull (.abstract .func)]] := rfl
example : foldedTable.tables[1].type.limits = ⟨0, some 0⟩ := rfl
example : foldedTable.memories[0].limits = ⟨0, some 0⟩ := rfl

/-- The normative typed element-list abbreviation preserves its own reference
type, including the non-nullable `func` shorthand, independently of the table. -/
def typedInlineTables := wat3! r#"
(module (func $f)
  (table funcref (elem func $f))
  (table funcref (elem (ref func) (ref.func $f)))
  (table (export "nullable") i64 (ref extern)
    (elem externref (item ref.null extern)))
  (table funcref (elem func)))
"#

example : typedInlineTables.tables[0].type.element = ⟨true, .abstract .func⟩ := rfl
example : typedInlineTables.elems[0].type = ⟨false, .abstract .func⟩ := rfl
example : typedInlineTables.elems[0].init = [[.refFunc ⟨0⟩]] := rfl
example : typedInlineTables.elems[1].type = ⟨false, .abstract .func⟩ := rfl
example : typedInlineTables.elems[1].init = [[.refFunc ⟨0⟩]] := rfl
example : typedInlineTables.tables[2].type = ⟨.i64, ⟨1, some 1⟩, ⟨false, .abstract .extern⟩⟩ := rfl
example : typedInlineTables.elems[2].type = ⟨true, .abstract .extern⟩ := rfl
example : typedInlineTables.elems[2].mode = .active ⟨2⟩ [.intConst .i64 0] := rfl
example : typedInlineTables.exports = [⟨"nullable", .table ⟨2⟩⟩] := rfl
example : typedInlineTables.tables[3].type.limits = ⟨0, some 0⟩ := rfl
example : typedInlineTables.elems[3].type = ⟨false, .abstract .func⟩ := rfl

/-- Syntax expansion retains invalid limits and empty constant expressions for validation. -/
def raw := wat3! "(memory 9 2) (global i32) (data (offset)) (elem (offset) funcref (item))"
example : raw.memories[0].limits = ⟨9, some 2⟩ := rfl
example : raw.globals[0].init = [] := rfl
example : raw.data[0].mode = .active ⟨0⟩ [] := rfl
example : raw.elems[0].init = [[]] := rfl

example : wat3_expr! "f32.const -0 f64.const 0x1.8p+1" =
    [Instr.floatConst .f32 0x80000000, .floatConst .f64 0x4008000000000000] := rfl

end Silmaril.Wasm.Wat.CoreModuleExamples
