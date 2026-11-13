module

public import Silmaril.Wasm.Tools.Gen.Core.Defs

/-!
# Validity in a model, up to the ungated Wasm 1.0 spellings

The Core 3.0 binary grammar decodes two Wasm 1.0 forms into 3.0 syntax that
`Module.InFeat` counts as reference-type features: a table's implicit initialiser becomes
`ref.null` of its element type, and an element segment of function indices becomes a segment
of type `(ref func)` with `ref.func` initialisers. wasmparser gates neither (they are Wasm 1.0),
so a Wasm 1.0 module with a table, read back, is not `ValidIn v10`. `wnorm` erases the two
spellings (the same normalisation as the wasm-tools-core validate track's), and
`ValidInW S m := ModuleValid m ∧ Module.InFeat S (wnorm m)` is validity in `S` up to them.
`smith` generates against it, so that tables and element segments exist at every model with
tables (`v10` included).

`Thms`: `validInWB_iff` (the check decides it), `validIn_validInW` (`ValidIn` implies it),
`checkedGenW_validInW`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd

open Silmaril.Wasm Silmaril.Wasm.Models

/-- Is the expression `[ref.null h]`? -/
def isNullOf (h : HeapType) : Expr → Bool
  | [.refNull h'] => h' == h
  | _ => false

/-- The implicit initialiser of a table: `ref.null` of its (nullable) element type. -/
def implicitInit (t : Table) : Bool :=
  t.type.element.nullable && isNullOf t.type.element.heap t.init

/-- Is an element initialiser a function index (`[ref.func f]`)? -/
def isFuncIdx : Expr → Bool
  | [.refFunc _] => true
  | _ => false

/-- An element segment of function indices, as the 3.0 grammar decodes it. -/
def funcIdxElem (e : Elem) : Bool :=
  e.type == ⟨false, .abstract .func⟩ && e.init.all isFuncIdx

/-- **Erase the ungated Wasm 1.0 spellings.** -/
def wnorm (m : Module) : Module :=
  { m with
    tables := m.tables.map fun t => if implicitInit t then { t with init := [] } else t
    elems := m.elems.map fun e =>
      if funcIdxElem e then { e with type := ⟨true, .abstract .func⟩, init := e.init.map fun _ => [] }
      else e }

/-- **Valid in `S` up to the Wasm 1.0 spellings.** -/
def ValidInW (S : FeatureSet) (m : Module) : Prop :=
  Silmaril.Wasm.Validation.ModuleValid m ∧ Module.InFeat S (wnorm m)

/-- Its check. -/
def validInWB (S : FeatureSet) (m : Module) : Bool :=
  (Silmaril.Wasm.Perf.ValidateR.validateR m).isSome && Module.inFeatB S (wnorm m)

/-- The checked output of a raw generator for `ValidInW`. -/
def checkedGenW (S : FeatureSet) (raw : ByteArray → Module) (seed : ByteArray) : Module :=
  if validInWB S (raw seed) then raw seed else ({} : Module)

end Silmaril.Wasm.Tools.Gen.Cmd
