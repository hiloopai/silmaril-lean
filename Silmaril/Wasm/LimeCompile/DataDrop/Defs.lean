module

public import Silmaril.Wasm.LimeCompile.PassiveData.Defs

/-!
# The container with `data.drop`: definitions

An earlier step of the container track (docs/projects/wasm-wasi.md, "3.0 to Lime compiler"). The pass-2
container (`Silmaril.Wasm.LimeCompile.PassiveData`) rejects `data.drop`. Here the fragment is
**Lime1 plus passive data segments, `memory.init` on memory 0 and `data.drop`**. A dropped
segment behaves as an empty one: `memory.init` then traps unless `n = 0` and `j = 0`.

The emulation keeps one **dropped flag** per segment: a mutable `i32` global, initially `0`,
appended after the module's globals, so existing global indices do not move. Per segment `y`
there are four functions, appended after the module's functions (with `D` the number of
segments and `B = helperBase m`):

| index | function | body |
|---|---|---|
| `B + y` | full helper | `helperBody (effBytes d) (B + y)` |
| `B + D + y` | empty helper | `helperBody [] (B + D + y)` (no bytes) |
| `B + 2D + y` | `$init_y`, the dispatcher | `global.get $flag_y; if (call empty) (call full)`, passing `i j n` |
| `B + 3D + y` | `$drop_y` | `i32.const 1; global.set $flag_y` |

`memory.init 0 y` becomes `call $init_y` and `data.drop y` becomes `call $drop_y`, so the
rewrite keeps the length of every instruction sequence. Both helpers are an earlier, so their
emulation theorem is reused unchanged; the dispatcher only adds a frame, a `global.get` and an
`if`.

* `flagBase m`: the index of the first flag global (after imported and defined globals);
* `wrapBody`, `dropBody`: the bodies of the dispatcher and of `$drop_y`;
* `rwI`, `rwL`, `emuModule`, **`compile`**, `compileP := limePres compile`;
* `exDrop`: an earlier example with `data.drop`, now inside the fragment.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.DataDrop

open Silmaril.Wasm
open Silmaril.Wasm.LimeCompile.PassiveData (idx effBytes emuData helperBody helperType helperBase
  helperFunc)

/-- The number of imported globals. -/
def importedGlobalsLen (m : Module) : Nat :=
  (m.imports.filterMap fun e => match e.type with
    | .global g => some g
    | _ => none).length

/-- The index of the first flag global. -/
def flagBase (m : Module) : Nat := importedGlobalsLen m + m.globals.length

/-- The number of data segments. -/
abbrev nseg (m : Module) : Nat := m.data.length

/-- The index of the empty helper of segment `y`. -/
def emptyIdx (m : Module) (y : Nat) : Nat := helperBase m + nseg m + y

/-- The index of the dispatcher of segment `y`. -/
def wrapIdx (m : Module) (y : Nat) : Nat := helperBase m + 2 * nseg m + y

/-- The index of `$drop_y`. -/
def dropIdx (m : Module) (y : Nat) : Nat := helperBase m + 3 * nseg m + y

/-- The dispatcher: if the flag is set, the empty helper, else the full one, on `i j n`. -/
def wrapBody (full empty flag : Nat) : List Instr :=
  [.globalGet (idx flag), .if_ .empty
    [.localGet (idx 0), .localGet (idx 1), .localGet (idx 2), .call (idx empty)]
    [.localGet (idx 0), .localGet (idx 1), .localGet (idx 2), .call (idx full)]]

/-- `$drop_y`: set the flag. -/
def dropBody (flag : Nat) : List Instr := [.intConst .i32 1, .globalSet (idx flag)]

/-- The type of `$drop_y`, `[] → []`. -/
def dropType : V1.FuncType := ⟨[], []⟩

/-- A dropped flag: a mutable `i32` global, initially `0`. -/
def flagGlobal : Global := ⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩

set_option linter.unusedTactic false in
mutual
/-- The rewrite of one instruction: `memory.init 0 y` calls the dispatcher of `y`, and
`data.drop y` calls `$drop_y`. -/
def rwI (m : Module) : Instr → Instr
  | .memoryInit x y =>
    if x.toNat = 0 then .call (idx (wrapIdx m y.toNat)) else .memoryInit x y
  | .dataDrop y => .call (idx (dropIdx m y.toNat))
  | .block bt b => .block bt (rwL m b)
  | .loop bt b => .loop bt (rwL m b)
  | .if_ bt b₁ b₂ => .if_ bt (rwL m b₁) (rwL m b₂)
  | .tryTable bt cs b => .tryTable bt cs (rwL m b)
  | i => i
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The rewrite of an instruction sequence. -/
def rwL (m : Module) : List Instr → List Instr
  | [] => []
  | i :: is => rwI m i :: rwL m is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The rewrite of a function body. -/
def rwFunc (m : Module) (f : Func) : Func := { f with body := rwL m f.body }

/-- The segments with their indices. -/
def segs (m : Module) : List (Nat × Data) := (List.range m.data.length).zip m.data

/-- The empty helper of segment `y`. -/
def emptyFunc (m : Module) (y : Nat) : Func :=
  { type := idx m.types.length, locals := [], body := helperBody [] (emptyIdx m y) }

/-- The dispatcher of segment `y`. -/
def wrapFunc (m : Module) (y : Nat) : Func :=
  { type := idx m.types.length, locals := [],
    body := wrapBody (helperBase m + y) (emptyIdx m y) (flagBase m + y) }

/-- `$drop_y`. -/
def dropFunc (m : Module) (y : Nat) : Func :=
  { type := idx (m.types.length + 1), locals := [], body := dropBody (flagBase m + y) }

/-- **The container's Core 3.0 module**: two types, one flag global per segment, four functions
per segment, passive segments emptied, and the two rewrites. -/
def emuModule (m : Module) : Module :=
  { m with
    types := m.types ++ [helperType.toCoreRec, dropType.toCoreRec]
    globals := m.globals ++ List.replicate (nseg m) flagGlobal
    funcs := m.funcs.map (rwFunc m) ++ (segs m).map (fun p => helperFunc m p.1 p.2) ++
      (segs m).map (fun p => emptyFunc m p.1) ++ (segs m).map (fun p => wrapFunc m p.1) ++
      (segs m).map (fun p => dropFunc m p.1)
    data := m.data.map emuData }

/-- **The container compiler with `data.drop`.** -/
def compile (m : Module) : Option Lime1.Module :=
  if Preserve.ElemsCanon (emuModule m) then Lime1.Module.ofCore? (emuModule m) else none

/-- The Lime-preserving variant. -/
def compileP : Preserve.Compiler := Preserve.limePres compile

end Silmaril.Wasm.LimeCompile.DataDrop
