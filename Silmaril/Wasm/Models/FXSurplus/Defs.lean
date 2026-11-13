module

public import Silmaril.Wasm.Models.FXPresI.Defs
public import Silmaril.Wasm.V2.ToCore.Types

/-!
# `suspend` with surplus operands: a typed program and its `StepFX'` runs

The untyped `suspend` rule of `StepFX'` takes **any** suffix of the values in front of the
`suspend` as its payload (`FXAsyncBack.suspend_nondet`). When the frame holds more values than
the tag's parameters (*surplus operands*), a longer payload is possible: the branch to the
handler's label keeps only the label's arity of values, and the captured continuation has lost
the extra ones. This module fixes one typed program in which that happens.

**The setting.** One module instance `surM` with type `0` = `[] → [i32]` (the continuation type
`$ct`) and tag `0` (address `0`) of type `[i32] → []` (`$t`); the store `surS` has that tag.

**The program** `surC` (no continuations yet, empty frame of `surM`):

```
label 2 {resume $ct}            ;; block $on (result i32 (ref $ct)) ... end; resume $ct
  handler (on $t $on)           ;; the handler frame of an earlier resume
    i32.const 7; i32.const 1; suspend $t
  i32.const 0
```

The handler's body leaves `[i32]` (`7`, the `1` is the payload), so its continuation type is
`$ct = [] → [i32]`, and the whole configuration has type `[i32 i32]`
(`FXPresI.envP`, `ConfigOk`). Under the typed relation `StepFXS` the payload is `[1]`, the
continuation keeps `7`, and the run ends with `[1, 7]`. Under `StepFX'` the payload may also be
`[7, 1]` (the continuation is the empty context, `7` is dropped by the branch), and the run ends
with `[1]`; and `resume` may also pass the `1` as an argument of the continuation, giving
`[7, 1]`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXSurplus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV

/-- Index `j`. -/
def ix {k : IndexKind} (j : Nat) : Idx k := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- `i32`. -/
abbrev ti32 : CValType := .num (.int .i32)

/-- The tag type `[i32] → []`. -/
def tagTy : DefType := Silmaril.Wasm.V2.FuncType.toDefType ⟨[.num (.int .i32)], []⟩

/-- The continuation type `$ct = [] → [i32]`. -/
def ctTy : DefType := Silmaril.Wasm.V2.FuncType.toDefType ⟨[], [.num (.int .i32)]⟩

/-- The module instance: type `0` is `$ct`, tag `0` is address `0`. -/
def surM : ModuleInst := { types := [ctTy], tags := [0] }

/-- The store: one tag, `[i32] → []`. -/
def surS (H : Type) : Store H := { tags := [⟨tagTy⟩] }

/-- The frame. -/
def surF : Frame := ⟨[], surM⟩

/-- `$ct`. -/
def ct0 : TypeIdx := ix 0

/-- `$t`. -/
def x0 : TagIdx := ix 0

/-- Label `0`. -/
def l0 : LabelIdx := ix 0

/-- `i32.const n` as FX code. -/
def c32 (n : BitVec 32) : AdminFX := .core (.plain (.intConst .i32 n))

/-- The handler clause `(on $t $on)`, resolved. -/
def surHs : List HClause := [.onLabel 0 l0]

/-- The label's continuation: `resume $ct`. -/
def surK : List InstrFX := [.fx (.resume ct0 [])]

/-- The handler frame. -/
def surH : AdminFX := .handler surHs [c32 7, c32 1, .fx (.suspend x0)]

/-- **The code.** -/
def surCode : List AdminFX := [.label 2 surK [surH, c32 0]]

/-- **The configuration.** -/
def surC (H : Type) : ConfigFX H := ⟨surS H, [], surF, surCode⟩

/-- The configuration with final code `code` and continuation store `K`. -/
def surEnd (H : Type) (K : List (Option ContFX)) (code : List AdminFX) : ConfigFX H :=
  ⟨surS H, K, surF, code⟩

/-- The observable behaviours under the typed relation `StepFXS` (as `behavioursFX'`). -/
def behavioursFXS {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (fx : H → Option FuncFX) (c : ConfigFX H) : Set (Behaviour Val) :=
  {b | ∃ (d : ConfigFX H) (r : Result), Silmaril.Wasm.Models.FXPres.StepsFXS P host fx c d ∧
      d.code = r.toAdmin.map .core ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ Silmaril.InfiniteTrace (Silmaril.Wasm.Models.FXPres.StepFXS P host fx) c}

/-- **Preservation for `StepFX'`** on the environment `FXPresI.envP m₀`: every step of a typed
configuration reaches a typed configuration at the same result types (any slot typing). -/
def PresV {H : Type} (m₀ : ModuleInst) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (fx : H → Option FuncFX) : Prop :=
  ∀ (c c' : ConfigFX H) (Γ : List TypeIdx) (ts : List Silmaril.Wasm.Models.FXResumeT.FTy),
    StepFX' P host fx c c' → Silmaril.Wasm.Models.FXPres.ConfigOk (Silmaril.Wasm.Models.FXPresI.envP m₀) Γ c ts →
      ∃ Γ', Silmaril.Wasm.Models.FXPres.ConfigOk (Silmaril.Wasm.Models.FXPresI.envP m₀) Γ' c' ts

end Silmaril.Wasm.Models.FXSurplus
