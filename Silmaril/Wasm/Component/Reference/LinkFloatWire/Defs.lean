module

public import Silmaril.Wasm.Component.Reference.LinkFloat.Defs

/-!
# Floats across the wiring of two linked components: the litmus

`Linked2.sound_floatV` (`Reference.LinkFloat`) assumes `Linked2.ImportsFloatFree`: no floats in
the importer's imports, hence none crossing the wiring. This header defines the litmus that
shows why:

* the exporter `nanRbS`: `g(x: f32) -> u32` over `rbCore3`,
  `(func (param f32) (result i32) local.get 0 i32.reinterpret_f32)`: it returns the bits of
  its argument;
* the importer `nanImpS`: imports `g: func(f32) -> u32`, lowered into `nanCore3`, whose function
  `f` is `f32.const nan:0x200001; call $g` (the non-canonical NaN with bits `0x7fa00001`), lifted
  as `f: func() -> u32`;
* `nanRbL`: the importer's `g` answered by the exporter's `g`.

The reference machine canonicalises the NaN in the trampoline's `lift_flat` before the exporter
sees it; the linked IR `l.toComp.den (impSem P)` passes the raw bits. Results:
`Silmaril.Wasm.Component.Reference.LinkFloatWire.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference

/-- The bits of the non-canonical `f32` NaN `nan:0x200001`. -/
def nanBits : BitVec 32 := 0x7fa00001

/-- The bits of the canonical `f32` NaN `nan:0x400000`. -/
def canonBits : BitVec 32 := 0x7fc00000

/-- `(type (func (param f32) (result i32))) (func (export "f") (type 0) local.get 0
i32.reinterpret_f32)`. -/
def rbCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.f32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .convert (.reinterpretInt .f32)]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The exporter `g(x: f32) -> u32`, the bits of `x`. -/
def nanRbS : Simple :=
  ⟨⟨rbCore3, [("f", ⟨[.float .f32], [.int .i32]⟩)]⟩, [⟨"g", ⟨[.f32], [.u32]⟩, 0⟩]⟩

/-- `(type (func (param f32) (result i32))) (type (func (result i32)))
(import "env" "g" (func (type 0))) (func (export "f") (type 1) f32.const nan:0x200001
call 0)`. -/
def nanCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.f32], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  imports := [⟨"env", "g", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.floatConst .f32 nanBits, .call ⟨0⟩]⟩]
  exports := [⟨"f", .func ⟨1⟩⟩]

/-- The importer's module with its import and export interfaces. -/
def nanMod : ImpModule :=
  ⟨nanCore3, [("g", ⟨[.float .f32], [.int .i32]⟩)], [("f", ⟨[], [.int .i32]⟩)]⟩

/-- The importer: `g: func(f32) -> u32` lowered into `nanCore3`, whose `f` is lifted as
`f: func() -> u32`. -/
def nanImpS : SimpleI := ⟨nanMod, [("g", ⟨[.f32], [.u32]⟩)], [⟨"f", ⟨[], [.u32]⟩, 0⟩]⟩

/-- The importer's `g` answered by the exporter's `g`: `f()` passes a non-canonical NaN across
the wiring and returns the bits the exporter sees. -/
def nanRbL : Linked2 := ⟨nanRbS, nanImpS, [0]⟩

end Silmaril.Wasm.Component.Reference.Litmus
