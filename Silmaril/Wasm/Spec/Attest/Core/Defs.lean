module

public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Wasm.Spec.Wasm.Defs
public import Silmaril.Wasm.Verify.Check.Defs

/-!
# "May attest" for Core 3.0 modules: the Core kit

The Core 3.0 instance of `Silmaril.Wasm.Spec.Attest`. Every profile `P`; no determinism.

## The import

* `unitFn = [] → []`, `Att = ifaceSig [unitFn]`: the single import `attest`, which takes and
  returns nothing (its answers are `Answer unitFn`: no values, a trap or an exception).
* `trapAns`: the trap answer of every Core function (`Answer.trap`).
* `CoreLeaf`: a Core 3.0 program whose only import is `attest`
  (`WasmProg ⟨[unitFn], exports⟩`, a model of `wasmSem P`). `CoreLeaf.toAMod P` is its strategy
  `p.inst.strategy P p.store` (`Silmaril.Wasm.Game.Strategy`): Core `Step P` reduction, the store
  hidden and persisting across export calls.

## The modules (silmaril-lean `Module` syntax)

```wat
(module $true                                        ;; ttMod
  (import "env" "attest" (func $attest))
  (func (export "fire") call $attest))
(module $false                                       ;; ffMod
  (import "env" "attest" (func $attest))
  (func (export "idle")))
(module $gate                                        ;; gateMod
  (import "env" "attest" (func $attest))
  (global $gL (mut i32) (i32.const 0))
  (global $gR (mut i32) (i32.const 0))
  (func (export "attestL")  i32.const 1  global.set $gL
    global.get $gR  (if (then call $attest))  unreachable)
  (func (export "attestR")  i32.const 1  global.set $gR
    global.get $gL  (if (then call $attest))  unreachable))
```

`attestL` records the left conjunct's call in `$gL`, calls the real `attest` if the right one has
called already, and traps. The trap ends the left conjunct's export call (Core traps cannot be
caught), so the environment can go on and call the right conjunct; the globals persist across
export calls. This is the user's gate with `fire` folded into `attestL`/`attestR`: an exported
`fire` would have to be re-exported through the consumer (a copycat on its interface), and
checking at each call already gives "the real `attest` is called only when both are set".

* `gateI`: the gate's scalar instance (instantiated by `instOf`, its imports and exports typed
  `[unitFn]` and `[unitFn, unitFn]`), `ιL`, `ιR`: `attest` as the gate's exports `attestL`
  (export `0`) and `attestR` (export `1`).
* `coreKit P : Kit Att`: the gate strategy `gateI.strategy P gateI.store` and the leaves of
  `ttMod`, `ffMod`.

Proofs and the kit's laws: `Silmaril.Wasm.Spec.Attest.Core.Thms`. New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Spec.Attest.Core

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm
  Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## The import `attest` -/

/-- `[] → []`. -/
def unitFn : FnType := ⟨[], []⟩

/-- The import signature of every module here: one function `attest : [] → []`. -/
abbrev Att : Sig.{0} := ifaceSig [unitFn]

/-- The gate's export signature: `attestL, attestR : [] → []`. -/
abbrev GateSig : Sig.{0} := ifaceSig [unitFn, unitFn]

/-- The trap answer of a scalar function. -/
def trapAns {ts : List FnType} (e : (ifaceSig ts).Op) : (ifaceSig ts).Ar e := .trap

/-- A Core 3.0 program whose only import is `attest`. -/
structure CoreLeaf where
  /-- The exports. -/
  exports : List FnType
  /-- The program: export addresses and the instantiated store. -/
  prog : WasmProg ⟨[unitFn], exports⟩

/-- **A Core program as an attesting module**: its strategy at profile `P`. -/
noncomputable def CoreLeaf.toAMod (P : Profile) (L : CoreLeaf) : AMod Att :=
  ⟨ifaceSig L.exports, trapAns, L.prog.inst.strategy P L.prog.store⟩

/-- The program of a module, with its import typed `attest` (when `instOf` computes it). -/
def leafOf (m : Module) : CoreLeaf := ⟨(instOf m).exports, ⟨(instOf m).addrs, (instOf m).store⟩⟩

/-! ## Modules -/

/-- `[] → []`. -/
def tyVoid : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- The import `env.attest : [] → []`. -/
def attestImport : Import := ⟨"env", "attest", .func ⟨0⟩⟩

/-- **True**: the export `fire` calls `attest`. -/
def ttMod : Module where
  types := [tyVoid]
  imports := [attestImport]
  funcs := [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]
  exports := [⟨"fire", .func ⟨1⟩⟩]

/-- **False**: the export `idle` does nothing; `attest` is imported but never called. -/
def ffMod : Module where
  types := [tyVoid]
  imports := [attestImport]
  funcs := [⟨⟨0⟩, [], []⟩]
  exports := [⟨"idle", .func ⟨1⟩⟩]

/-- The body of `attestL` (`mine = 0`, `other = 1`) and `attestR` (`mine = 1`, `other = 0`). -/
def gateBody (mine other : Fin (2 ^ 32)) : List Instr :=
  [.intConst .i32 1, .globalSet ⟨mine⟩, .globalGet ⟨other⟩, .if_ .empty [.call ⟨0⟩] [], .unreachable]

/-- **The gate**: two flags, `attestL` and `attestR`, the real `attest` called once both are set. -/
def gateMod : Module where
  types := [tyVoid]
  imports := [attestImport]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩, ⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], gateBody 0 1⟩, ⟨⟨0⟩, [], gateBody 1 0⟩]
  exports := [⟨"attestL", .func ⟨1⟩⟩, ⟨"attestR", .func ⟨2⟩⟩]

/-- The gate's scalar instance: import `attest`, exports `attestL`, `attestR`. -/
def gateI : ScalarInstance := ⟨[unitFn], [unitFn, unitFn], (instOf gateMod).addrs, (instOf gateMod).store⟩

/-! ## The relabellings -/

/-- `[unitFn].get e.1 = [unitFn, unitFn].get k` for every `e` and `k`. -/
theorem get_unitFn (i : Fin 1) (k : Fin 2) : [unitFn, unitFn].get k = [unitFn].get i := by
  rcases k with ⟨_ | _ | k, hk⟩ <;> rcases i with ⟨_ | i, hi⟩ <;> first | rfl | omega

/-- The call of export `k` of the gate. -/
def gateOp (k : Fin 2) : GateSig.Op := ⟨k, ⟨[], by rw [get_unitFn 0 k]; exact .nil⟩⟩

/-- `attest` as the gate's export `k`. -/
def ιAt (k : Fin 2) : Relabel Att GateSig where
  op _ := gateOp k
  ar e := Equiv.cast (congrArg Answer
    (show [unitFn, unitFn].get (gateOp k).1 = [unitFn].get e.1 from get_unitFn e.1 k))

/-- The left conjunct's `attest` is `attestL`. -/
def ιL : Relabel Att GateSig := ιAt 0

/-- The right conjunct's `attest` is `attestR`. -/
def ιR : Relabel Att GateSig := ιAt 1

/-! ## The kit -/

/-- **The Core 3.0 kit at profile `P`.** -/
noncomputable def coreKit (P : Profile) : Kit Att where
  G := GateSig
  stopG := trapAns
  gate := gateI.strategy P gateI.store
  ι₁ := ιL
  ι₂ := ιR
  tt := (leafOf ttMod).toAMod P
  ff := (leafOf ffMod).toAMod P

end Silmaril.Wasm.Spec.Attest.Core
