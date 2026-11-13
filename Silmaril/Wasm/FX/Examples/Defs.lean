module

public import Silmaril.Wasm.Models.FXAsyncSus.Thms
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# WasmFX explainer examples: a kit and the generator examples

Examples of the WasmFX explainer (`docs/projects/wasm-wasi.md` pins the revision and lists every example
with its status), written as WasmFX programs of `StepFX'` (`Silmaril.Wasm.Models.FXV`). Each
program is given twice: as a program `W` of the one-shot handler kernel `sstep`
(`Silmaril.Wasm.Models.FXAsync`), and as the FX code `Y f` of each kernel function `f`, its
encoding (`Silmaril.Wasm.Models.FXAsyncFX.EncI`). On the tight fragment the `StepFX'` behaviours
of the encoding are exactly the images of the kernel's (`FXAsyncSus.beh_eq_tight`), and the
kernel run is computed by evaluation, so a behaviour theorem needs only the encoding
derivations and two closed evaluations (`Silmaril.Wasm.FX.Examples.Thms`).

**The kit.** A setting `kitS P host nf Y` for `nf` FX functions with no parameters and one
result, whose bodies are `Y f`; one tag (address `0`, payload one value, no result); the module
types `kitTypes`: `[i32] → [i32]` (`btD`, the `block` around an encoded `resume`) and
`[i32] → [i32 i32]` (`btH`, the `block` reached by the handler clause: payload and
continuation). The continuation type immediate is unused by the untyped `StepFX'`.
`resumeFX Z` is the encoding of a kernel `resume 0 [(on 0 h)]` whose handler `h` has the
encoded body `Z`, inlined after the inner block as in the explainer's
`block $on_yield … resume (tag $yield $on_yield) … end` shape.

**Generators.** The explainer revision pinned in `docs/projects/wasm-wasi.md` names generators among the
motivating features but has no generator code; the generator examples below are the
generator pattern written with the explainer's instructions (`cont.new`, `resume` with a
`(tag $yield $l)` clause, `suspend $yield`):

* `genW`: function `0` is a generator yielding `1`, `2`, `3` and returning `0`; function `1`
  (main) makes a continuation of it and resumes it; functions `2`, `3`, `4` are the handlers
  of the three yields: each resumes the generator under the next handler and adds the yielded
  value to the result (`5` is the handler of a fourth yield, never reached). Intended
  result: the sum `6`.
* `takeW`: the same generator, consumed twice and then abandoned: the second handler drops
  the continuation instead of resuming it. Intended result: `1 + 2 = 3`.

Handlers are unrolled, one kernel function per yield: in the kernel fragment a handler is
inlined code, so a handler cannot resume under itself (`docs/projects/wasm-wasi.md`, "Limits").

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (Ins Prog)

/-! ## The kit -/

/-- `i32`. -/
abbrev ti32 : CValType := .num (.int .i32)

/-- The module types: `[i32] → [i32]` and `[i32] → [i32 i32]`. -/
def kitTypes : List Silmaril.Wasm.Validation.DefType :=
  [Silmaril.Wasm.V2.FuncType.toDefType ⟨[.num (.int .i32)], [.num (.int .i32)]⟩,
    Silmaril.Wasm.V2.FuncType.toDefType
      ⟨[.num (.int .i32)], [.num (.int .i32), .num (.int .i32)]⟩]

/-- The module instance of `nf` functions and one tag, shared by all frames. -/
def kitM (nf : Nat) : ModuleInst := { types := kitTypes, tags := [0], funcs := List.range nf }

/-- `block btD`: `[cont] → [result]`. -/
def btD : BlockType := .typeIdx (ix 0)

/-- `block btH`: `[cont] → [payload, cont]`. -/
def btH : BlockType := .typeIdx (ix 1)

/-- The encoded `resume 0 [(on 0 h)]` with the inlined handler code `Z`. -/
def resumeFX (Z : List InstrFX) : InstrFX :=
  .block btD (.block btH [.fx (.resume (ix 0) [.onLabel (ix 0) (ix 0)]), .core (.br (ix 1))] :: Z)

/-- The FX functions: host code `f < nf` is kernel function `f`, with body `Y f`. -/
def kitFx (nf : Nat) (Y : Nat → List InstrFX) : Nat → Option FuncFX
  | f => if f < nf then some ⟨kitM nf, 0, 1, [], localGets 0 ++ Y f⟩ else none

/-- The store: `nf` FX functions and one tag. -/
def kitStore (nf : Nat) : Store Nat :=
  { funcs := (List.range nf).map fun f => ⟨kitTypes.head!, kitM nf, .host f⟩,
    tags := [⟨kitTypes.head!⟩] }

/-- **The setting** of `nf` FX functions with bodies `Y`, for every profile and host. -/
def kitS (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) (nf : Nat)
    (Y : Nat → List InstrFX) : Setup Nat where
  P := P
  host := host
  fx := kitFx nf Y
  s := kitStore nf
  M := kitM nf
  f0 := ⟨[], kitM nf⟩
  xf := ix
  fa := id
  xt := ix
  ta := id
  ar := fun _ => 1
  ct := ix 0

/-- `i32.add` on kernel operands (top first). -/
def opAdd : List Val → List Val
  | [.num ⟨.int .i32, a⟩, .num ⟨.int .i32, b⟩] => [Val.i32 (b + a)]
  | vs => vs

/-- `i32.const n; nop`, the encoding of `push (i32 n)`. -/
def pushI (n : BitVec 32) : List InstrFX := [.core (.intConst .i32 n), .core .nop]

/-! ## Generators -/

/-- The generator body: yield `1`, `2`, `3`, return `0`. -/
def genBody : List (Ins Val) :=
  [.push (Val.i32 1), .suspend 0 1, .push (Val.i32 2), .suspend 0 1, .push (Val.i32 3),
    .suspend 0 1, .push (Val.i32 0)]

/-- Its encoding. -/
def genY : List InstrFX :=
  pushI 1 ++ [.fx (.suspend (ix 0))] ++ pushI 2 ++ [.fx (.suspend (ix 0))] ++ pushI 3 ++
    [.fx (.suspend (ix 0))] ++ pushI 0

/-- **Sum of a generator** (kernel program). -/
def genW : Prog (Ins Val)
  | 0 => some (0, genBody)
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [.resume 0 [⟨0, 3⟩], .prim 2 opAdd])
  | 3 => some (0, [.resume 0 [⟨0, 4⟩], .prim 2 opAdd])
  | 4 => some (0, [.resume 0 [⟨0, 5⟩], .prim 2 opAdd])
  | 5 => some (0, [])
  | _ => none

/-- The encoded handler of the third yield of `genW` (the fourth handler is empty). -/
def genH4 : List InstrFX := [resumeFX [], .core (.intBinOp .i32 .add)]

/-- The encoded handler of the second yield. -/
def genH3 : List InstrFX := [resumeFX genH4, .core (.intBinOp .i32 .add)]

/-- The encoded handler of the first yield. -/
def genH2 : List InstrFX := [resumeFX genH3, .core (.intBinOp .i32 .add)]

/-- The encoded bodies of `genW`. -/
def genWY : Nat → List InstrFX
  | 0 => genY
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)), resumeFX genH2]
  | 2 => genH2
  | 3 => genH3
  | 4 => genH4
  | _ => []

/-- **Take two from a generator, then drop it** (kernel program). -/
def takeW : Prog (Ins Val)
  | 0 => some (0, genBody)
  | 1 => some (0, [.contNew 0, .resume 0 [⟨0, 2⟩]])
  | 2 => some (0, [.resume 0 [⟨0, 3⟩], .prim 2 opAdd])
  | 3 => some (0, [.drop])
  | _ => none

/-- The encoded bodies of `takeW`. -/
def takeWY : Nat → List InstrFX
  | 0 => genY
  | 1 => [.core (.refFunc (ix 0)), .fx (.contNew (ix 0)),
      resumeFX [resumeFX [.core .drop], .core (.intBinOp .i32 .add)]]
  | 2 => [resumeFX [.core .drop], .core (.intBinOp .i32 .add)]
  | 3 => [.core .drop]
  | _ => []

/-- The WasmFX program: call function `1` (main) of the sum example. -/
def genProg (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) : ConfigFX Nat :=
  fxInit (kitS P host 6 genWY) 1 []

/-- The WasmFX program: call function `1` (main) of the take-two example. -/
def takeProg (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) : ConfigFX Nat :=
  fxInit (kitS P host 4 takeWY) 1 []

end Silmaril.Wasm.FX.Examples
