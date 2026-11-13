module

public import Silmaril.Wasm.Lime1.ToCore.Modules

/-!
# The direct 3.0 → Lime compiler, first fragment: definitions

The **direct translation** rewrites Wasm 3.0 instructions to Lime1 instruction sequences in
place, without an interpreter (compare the container approach). The first fragment is
**Lime1 plus the typed `select`** of the reference-types proposal at number types:

  `select (result t*)` ⟶ `select`        when every `t` is a number type.

In Core 3.0 the two `select` rules (`Step_pure/select-true`, `select-false`) ignore the
annotation, and the untyped `select` validates at number operands, so the rewrite is one
instruction for one instruction (same size, same number of steps).

* `isNumType t`, `selectNum ts`: the annotation is a list of number types;
* `lowerI`, `lowerL`: the rewrite, recursively in every block, loop, `if` and `try_table` body;
* `lowerModule m`: the rewrite of every function body (nothing else changes);
* `funcrefElemsB m`: every element segment of `m` is typed `funcref` (the type
  `Lime1.Elem.toCore` gives; `Lime1.Elem.ofCore?` also accepts `(ref func)`, which would make
  `toCore ∘ ofCore?` change a segment type);
* **`compile m : Option Lime1.Module`**: lower, check the element types, and read the result back
  as a Lime1 module with `Lime1.Module.ofCore?` (which fails on anything outside Lime1).
  Correctness is in `Silmaril.Wasm.LimeCompile.Direct.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.Direct

open Silmaril.Wasm

/-- A number type (`i32`, `i64`, `f32`, `f64`). -/
def isNumType : ValType → Bool
  | .num _ => true
  | _ => false

/-- A `select` annotation whose types are all number types. -/
def selectNum (ts : List ValType) : Bool := ts.all isNumType

set_option linter.unusedTactic false in
mutual
/-- **The direct rewrite of one instruction**: a typed `select` at number types becomes the
untyped `select`; bodies are rewritten recursively; everything else is unchanged. -/
def lowerI : Instr → Instr
  | .select (some ts) => if selectNum ts then .select none else .select (some ts)
  | .block bt b => .block bt (lowerL b)
  | .loop bt b => .loop bt (lowerL b)
  | .if_ bt b₁ b₂ => .if_ bt (lowerL b₁) (lowerL b₂)
  | .tryTable bt cs b => .tryTable bt cs (lowerL b)
  | i => i
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The direct rewrite of an instruction sequence. -/
def lowerL : List Instr → List Instr
  | [] => []
  | i :: is => lowerI i :: lowerL is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The direct rewrite of a function: its body. -/
def lowerFunc (f : Func) : Func := { f with body := lowerL f.body }

/-- **The direct rewrite of a module**: every function body; nothing else changes. -/
def lowerModule (m : Module) : Module := { m with funcs := m.funcs.map lowerFunc }

/-- Every element segment is typed `funcref`. -/
def funcrefElemsB (m : Module) : Bool := m.elems.all fun e => decide (e.type = V1.funcref)

/-- **The direct compiler** from Core 3.0 modules to Lime1 modules: lower, check element types,
and read back as Lime1. (No validator run is needed: the lowering keeps validity,
`Direct.lowerModule_valid`.) -/
def compile (m : Module) : Option Lime1.Module :=
  if funcrefElemsB (lowerModule m) then Lime1.Module.ofCore? (lowerModule m) else none

end Silmaril.Wasm.LimeCompile.Direct
