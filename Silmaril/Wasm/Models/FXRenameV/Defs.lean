module

public import Silmaril.Wasm.Models.FXRename.Defs
public import Silmaril.Wasm.Models.FXV.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head

/-!
# Exception renaming for the corrected WasmFX semantics `StepFX'`

`Task.exnRenameBisim` (`Silmaril.Wasm.Models.FXRename`, proved as
`FXRenameSim.exnRenameBisim_holds`) is about Core behaviours. This module states its analogue
for `StepFX'`, where code is FX code and the configuration has a continuation store:

* `rnA`, `rnL`: rename the exception addresses of FX administrative code (inside Core code,
  frames' locals, and the bodies of labels, frames and handler frames); continuation
  references, FX instructions and source bodies hold no exception address;
* `ContRn n C₁ C₂`: `C₂` is `C₁` renamed (filling renamed code gives the renamed fill);
  `KRn n K₁ K₂`: slot by slot, consumed slots to consumed slots and live continuations to
  renamed ones;
* **`Task.exnRenameBisimFX'`** (frozen, open): host-free `StepFX'` behaviours (no FX
  functions) of the renamed configuration over an `ExnRen n` target store and a renamed
  continuation store are the renamed behaviours.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXRenameV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

mutual
/-- Rename the exception addresses of FX administrative code. -/
def rnA (n : Nat) : AdminFX → AdminFX
  | .core a => .core (rnAdmin n a)
  | .label m k body => .label m k (rnL n body)
  | .frame m f body => .frame m (rnFrame n f) (rnL n body)
  | .handler hs body => .handler hs (rnL n body)
  | a => a

/-- Rename the exception addresses of an FX code sequence. -/
def rnL (n : Nat) : List AdminFX → List AdminFX
  | [] => []
  | a :: rest => rnA n a :: rnL n rest
end

/-- `C₂` is `C₁` with exception addresses renamed. -/
def ContRn (n : Nat) (C₁ C₂ : ContFX) : Prop := ∀ c, C₂.plug (rnL n c) = rnL n (C₁.plug c)

/-- The continuation store `K₂` is `K₁` renamed. -/
def KRn (n : Nat) (K₁ K₂ : List (Option ContFX)) : Prop :=
  List.Forall₂ (Option.Rel (ContRn n)) K₁ K₂

/-- **Frozen target: exception renaming for `StepFX'`.** Host-free `StepFX'` behaviours (no FX
functions) of the renamed configuration, over an `ExnRen n` target store and a renamed
continuation store, are the renamed behaviours. Expected true for the reasons of
`Task.exnRenameBisim`, plus: `resume_throw` allocates at `s.exns.length` in the source and at
`rnIdx n s.exns.length` in the target, and every continuation built by a step (`cont.new`,
`cont.bind`, `suspend`, `switch`) of the renamed code is the renamed continuation. Not proved;
the instance on Core code is `exnRenameBisimFX'_core`. -/
def Task.exnRenameBisimFX' : Prop :=
  ∀ (H : Type) (P : Profile) (n : Nat) (c : ConfigFX H) (t : Store H)
    (K₂ : List (Option ContFX)), ExnRen n c.store t → KRn n c.conts K₂ →
    behavioursFX' P noHost noFX ⟨t, K₂, rnFrame n c.frame, rnL n c.code⟩ =
      rnBeh n '' behavioursFX' P noHost noFX c

end Silmaril.Wasm.Models.FXRenameV
