module

public import Silmaril.Wasm.Wasmi.Fusion.Defs
public import Silmaril.Wasm.Wasmi.Observed.Defs

/-!
# A loose model for the wider select fusion

`Silmaril.Wasm.Wasmi.Fusion` widens the model of wasmi 2.0.0's issue #2046 from `fuse` (one shape)
to `fuseW` (five shapes), because the harness probes observe the bug on four more shapes.
`LooseAll` (`Silmaril.Wasm.Wasmi.Observed`) admits only `fuse`'s shape in its quirk
`selectEither`. This topic gives the loose model of the wider fusion:

* `FuseShape`: the five source shapes of `fuseW`, each a comparison of a local with `0` feeding a
  `select`: `0 != x` (`ne0`, the reported one), `x != 0` (`neSwap`), `0 == x` (`eq0`),
  `x == 0` (`eqSwap`) and `eqz x` (`eqz`);
* `FuseShape.src g x t`: the source code of a shape; `FuseShape.tgt g x t`: its translation by `fuseW`
  (`fusedSel x t` for the `ne` shapes, `fusedSel1 x t` for the others);
* `Quirk` (`selectEitherW`): at the source code of any shape, read the local, drop it and select
  by a chosen constant `0` or `1`;
* `Step`, `obs`: Core 3.0 plus `selectEitherW` in every evaluation context;
* `AnyQuirkW`, `LooseAllW`: Core 3.0 plus `selectEitherW` and wasmi 0.40.0's `roundNaN`, the
  loose model of every wasmi version and model modelled here.

The source shapes have different lengths (`eqz` has three instructions, the others four), so
the simulation of `fuseW`'s code by the loose model is not lock-step: after a `trap` the source
may have fewer instructions left to discard than the translation. The proofs use a stuttering
simulation (`Silmaril.Proofs.Wasm.Wasmi.LooseW.Stutter`). New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.LooseW

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas

variable {H : Type}

/-- The five source shapes of the wider fusion `fuseW`. -/
inductive FuseShape where
  /-- `i32.const 0; local.get x; i32.ne; select` (issue #2046 as reported). -/
  | ne0
  /-- `local.get x; i32.const 0; i32.ne; select`. -/
  | neSwap
  /-- `i32.const 0; local.get x; i32.eq; select`. -/
  | eq0
  /-- `local.get x; i32.const 0; i32.eq; select`. -/
  | eqSwap
  /-- `local.get x; i32.eqz; select`. -/
  | eqz
  deriving DecidableEq, Repr

/-- The source code of a shape. -/
def FuseShape.src : FuseShape → LocalIdx → Option (List ValType) → List Instr
  | .ne0, x, t => [.intConst .i32 0, .localGet x, .intRelOp .i32 .ne, .select t]
  | .neSwap, x, t => [.localGet x, .intConst .i32 0, .intRelOp .i32 .ne, .select t]
  | .eq0, x, t => [.intConst .i32 0, .localGet x, .intRelOp .i32 .eq, .select t]
  | .eqSwap, x, t => [.localGet x, .intConst .i32 0, .intRelOp .i32 .eq, .select t]
  | .eqz, x, t => [.localGet x, .intTestOp .i32 .eqz, .select t]

/-- The condition `fuseW`'s translation of a shape reads: `0` for `ne`, `1` for `eq`/`eqz`. -/
def FuseShape.cond : FuseShape → BitVec 32
  | .ne0 | .neSwap => 0
  | .eq0 | .eqSwap | .eqz => 1

/-- The translation of a shape by `fuseW`: `local.get x; drop; i32.const c; select t`. -/
def FuseShape.tgt (g : FuseShape) (x : LocalIdx) (t : Option (List ValType)) : List Instr :=
  [.localGet x, .drop, .intConst .i32 g.cond, .select t]

/-- **The quirk `selectEitherW`**: at the source code of any shape, read the local, then drop
it and select by the constant `if b then 1 else 0` instead of by the comparison. -/
inductive Quirk : Config H → Config H → Prop where
  | selectEither {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} {t : Option (List ValType)}
      (g : FuseShape) (b : Bool) (h : f.local? x = some (some v)) :
      Quirk ⟨s, f, expression (g.src x t)⟩
        ⟨s, f, [v.toAdmin, .plain .drop, .plain (.intConst .i32 (if b then 1 else 0)),
          .plain (.select t)]⟩

/-- **The loose step relation of the wider fusion**: Core 3.0 plus `selectEitherW` in every
evaluation context. -/
abbrev Step (P : Numerics.Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Variant.loose (Execution.Core.Step P host) Quirk

/-- Its observations of a call. -/
def obs (P : Numerics.Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

/-- The quirks of every modelled wasmi version, with the wider fusion. -/
inductive AnyQuirkW : Config H → Config H → Prop where
  /-- `selectEitherW` (issue #2046, every probed shape). -/
  | select {c c' : Config H} (h : Quirk c c') : AnyQuirkW c c'
  /-- wasmi 0.40.0's `roundNaN`. -/
  | round {c c' : Config H} (h : Observed.Quirk c c') : AnyQuirkW c c'

namespace LooseAllW

/-- **The loose model of every modelled wasmi version**, with the wider fusion. -/
abbrev Step (P : Numerics.Profile) (host : HostSemantics H) : Config H → Config H → Prop :=
  Variant.loose (Execution.Core.Step P host) AnyQuirkW

/-- Its observations of a call. -/
def obs (P : Numerics.Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Variant.obsR (Step P) x c

end LooseAllW

end Silmaril.Wasm.Wasmi.LooseW
