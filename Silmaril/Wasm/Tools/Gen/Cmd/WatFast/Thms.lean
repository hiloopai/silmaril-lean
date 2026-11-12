module

public import Silmaril.Wasm.Tools.Gen.Cmd.WatFast.Defs
public import Mathlib.Tactic.CongrExclamation

/-!
# The faster WAT module elaborator: specification

Each fast function is **equal** to silmaril's: the only change is how `IdCtx.Ok` of a
function's context is decided, and `Decidable` is a subsingleton.

* `funcF?_eq`, `WithUses.funcF?_eq`, `fieldF?_eq` (for an `Ok` context);
* `fieldsF?_eq`: a pass is `mapCertified (field? I)`;
* `moduleF?_eq`: `moduleF? = Source.module?`;
* `parseF?_eq`: `parseF? = parseSupported?`, so `parseF?_sound`: the module is one the Core
  text grammar gives the tree (`Text.Core.ModuleT`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WatFast

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text
open Text.Core
open Silmaril.Wasm.Binaryen.Toolkit.Wat
open Silmaril.Wasm.Binaryen.Toolkit.Wat.Source

theorem funcF?_eq (I : IdCtx) (hI : I.Ok) (x : SExp) : funcF? I hI x = func? I x := by
  unfold funcF? func?
  congr!
  dsimp only
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem WithUses.funcF?_eq (I : IdCtx) (hI : I.Ok) (x : SExp) :
    WithUses.funcF? I hI x = Source.WithUses.func? I x := by
  unfold WithUses.funcF? Source.WithUses.func?
  congr!
  dsimp only
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem fieldF?_eq (I : IdCtx) (hI : I.Ok) : fieldF? I hI = field? I := by
  funext x
  unfold fieldF?
  split
  · rename_i tail h
    rw [field?, h]
    simp only [funcF?_eq, WithUses.funcF?_eq]
  · rfl

theorem fieldsF?_eq (I : IdCtx) (fields : List SExp) :
    fieldsF? I fields = mapCertified (field? I) fields := by
  unfold fieldsF?
  split
  · rename_i hI
    rw [fieldF?_eq I hI]
  · rfl

theorem moduleF?_eq : moduleF? = module? := by
  funext x
  unfold moduleF? module?
  simp only [fieldsF?_eq]

theorem parseF?_eq : parseF? = parseSupported? := by
  funext x
  unfold parseF? parseSupported?
  rw [moduleF?_eq]
  cases parseCanonical? x <;> rfl

/-- **The faster elaborator is sound for the Core text grammar.** -/
theorem parseF?_sound {x : SExp} {m : Wasm.Module} (h : parseF? x = some m) :
    Text.Core.ModuleT x m := by
  rw [parseF?_eq] at h
  exact parseSupported?_sound h

end Silmaril.Wasm.Tools.Gen.Cmd.WatFast
