module

public import Silmaril.Wasm.JcoTool.KCore.Defs
public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Defs

/-!
# The KCore fragment compiled to silmaril-lean's Core 3.0 instructions

`Silmaril.Wasm.JcoTool.KCore` gives the stream modules generated from byte kernels (`gen k N`) a
semantics `exec` over a small fragment of WebAssembly (`E`, `S`), and proves the generated module
implements `Proc.tStep`. Its header lists as not proved that the printed text means, under the
official semantics, what `exec` says. This module starts that link against **silmaril-lean's
Core 3.0 `Step`** (the semantics the component reference machine runs core code with,
`Silmaril.Wasm.Component.Reference.Core3Sem`), for the **expressions** of the fragment:

* `Bin.core`: each `i32` binary operator as the Core instruction `Prog.wat` prints for it
  (`i32.add`, `i32.sub`, `i32.eq`, `i32.ne`, `i32.lt_u`, `i32.ge_u`, `i32.div_u`, `i32.rem_u`,
  `i32.shl`);
* `E.code?`: an expression in folded form as the flat Core instruction sequence the WAT text
  stands for (operands first); `none` for `i32.load8_u`, which this increment does not cover;
* `S.code?`: the straight-line statements (`nop`, `local.set`, `global.set`, sequences) as Core
  instructions; `none` for the others;
* `E.Fits s ls gs e`: the locals and globals `e` reads are held as `i32` in the Core locals `ls`
  and globals `gs`, their values are below `2 ^ 32` (the fragment's values are `Nat`s), and
  every divisor is nonzero (`exec` divides by zero to `0`, Core traps; the generated modules only
  divide by the constant `16`).

`Silmaril.Wasm.JcoTool.KCoreCore.Thms` proves that under `E.Fits` the Core run of `E.code?` pushes
the value `E.eval` gives, and that `local.set` and `global.set` leave the frame and store holding
`exec`'s state. `i32.load8_u`, `i32.store8`, `memory.copy`, sequences, control (`block`, `loop`,
`br`, `if`, `return`), the built-in calls and the callback runtime are not covered yet.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCoreCore

open Silmaril.Wasm
open Silmaril.Wasm.JcoTool.KCore (E Bin St M32)
open Silmaril.Wasm.FX.Asyncify.Tool (W gidx)

/-- A local index from a number. -/
def lidx (i : Nat) : LocalIdx := ⟨Fin.ofNat _ i⟩

/-- The Core instruction of a binary operator. -/
def _root_.Silmaril.Wasm.JcoTool.KCore.Bin.core : Bin → Instr
  | .add => .intBinOp .i32 .add
  | .sub => .intBinOp .i32 .sub
  | .eq => .intRelOp .i32 .eq
  | .ne => .intRelOp .i32 .ne
  | .ltu => .intRelOp .i32 (.lt .unsigned)
  | .geu => .intRelOp .i32 (.ge .unsigned)
  | .divu => .intBinOp .i32 (.div .unsigned)
  | .remu => .intBinOp .i32 (.rem .unsigned)
  | .shl => .intBinOp .i32 .shl

/-- An expression as flat Core instructions (operands first); `none` for `i32.load8_u`. -/
def _root_.Silmaril.Wasm.JcoTool.KCore.E.code? : E → Option (List Instr)
  | .c n => some [.intConst .i32 (BitVec.ofNat 32 n)]
  | .l i => some [.localGet (lidx i)]
  | .g i => some [.globalGet (gidx i)]
  | .bin o a b => do
    let ca ← a.code?
    let cb ← b.code?
    pure (ca ++ cb ++ [o.core])
  | .eqz a => (a.code?).map (· ++ [.intTestOp .i32 .eqz])
  | .ld8 _ => none

/-- A straight-line statement as Core instructions: `nop`, `local.set`, `global.set`, sequences;
`none` for the others (not covered yet). -/
def _root_.Silmaril.Wasm.JcoTool.KCore.S.code? : Silmaril.Wasm.JcoTool.KCore.S → Option (List Instr)
  | .nop => some []
  | .lset i e => (e.code?).map (· ++ [.localSet (lidx i)])
  | .gset i e => (e.code?).map (· ++ [.globalSet (gidx i)])
  | .seq a b => do
    let ca ← a.code?
    let cb ← b.code?
    pure (ca ++ cb)
  | _ => none

/-- The locals and globals `e` reads are held in `ls` and `gs`, below `2 ^ 32`, and its
divisors are nonzero. -/
def _root_.Silmaril.Wasm.JcoTool.KCore.E.Fits (s : St) (ls gs : List W) : E → Prop
  | .c _ => True
  | .l i => i < 2 ^ 32 ∧ ls[i]? = some (BitVec.ofNat 32 (s.l i)) ∧ s.l i < M32
  | .g i => i < 2 ^ 32 ∧ gs[i]? = some (BitVec.ofNat 32 (s.g i)) ∧ s.g i < M32
  | .bin o a b => a.Fits s ls gs ∧ b.Fits s ls gs ∧ ((o = .divu ∨ o = .remu) → b.eval s ≠ 0)
  | .eqz a => a.Fits s ls gs
  | .ld8 _ => False

end Silmaril.Wasm.JcoTool.KCoreCore
