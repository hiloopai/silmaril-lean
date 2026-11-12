module

public import Silmaril.Wasm.JcoTool.LayoutRefX.Defs
public import Silmaril.Proofs.Wasm.JcoTool.LayoutRefX.Spaces
public import Silmaril.Wasm.Perf.CoreDecode.Thms
public import Silmaril.Wasm.Perf.ValidateComp.Thms

/-!
# The reference translation with core module types: theorems

Proofs in `Silmaril.Proofs.Wasm.JcoTool.LayoutRefX.Spaces`.

* `toRefX_of_toRef`: `toRefX` extends `LayoutRef.toRef`;
* **`read_toRefX`**: `Layout.read names x = readRef names c` whenever `toRefX rd x = some c`, so
  components with core module types have the layout reading on the reference syntax too;
* **`refCheckX_valid`**: bytes that `refCheckX` accepts parse to `x`, whose `toRefX` translation
  `c` (core modules decoded by silmaril's verified decoder) is valid in the reference's
  validation relation, and `Layout.read` of `x` is `readRef` of `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.LayoutRefX

open Silmaril.Wasm.JcoTool.LayoutRef
open Silmaril.Wasm.Component (Syntax.Component)

/-- **The layout reading is a reading of the reference syntax, core module types included.** -/
theorem read_toRefX {M : Type} {rd : ByteArray → Option M} {x : XComp} {c : Syntax.Component M}
    (h : toRefX rd x = some c) (names : List (String × String)) :
    Layout.read names x = readRef names c := by
  rw [readRef, spacesRef_toRefX h, readRS_map]

end Silmaril.Wasm.JcoTool.LayoutRefX

namespace Silmaril.Wasm.JcoTool.ToolV

open New (bind_ok)

theorem refCore3X_ok {b : ByteArray} {c : Silmaril.Wasm.Component.Reference.Core3Component}
    (h : refCore3X b = .ok c) :
    ∃ x, xparse b = .ok x ∧ LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c := by
  unfold refCore3X at h
  rw [Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] at h
  split at h
  · cases h
  · rename_i x hx
    split at h
    · rename_i c' hc
      cases h
      exact ⟨x, hx, hc⟩
    · cases h

/-- **The reference validator's verdict is sound, core module types included.** -/
theorem refCheckX_valid {b : ByteArray} {ct : Silmaril.Wasm.Component.Reference.ComponentType}
    (h : refCheckX b = .ok ct) :
    ∃ x c, xparse b = .ok x ∧ LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct ∧
      ∀ names, Layout.read names x = LayoutRef.readRef names c := by
  obtain ⟨c, hc, h₂⟩ := bind_ok h
  obtain ⟨x, hx, ht⟩ := refCore3X_ok hc
  rw [Silmaril.Wasm.Perf.ValidateR.checkCore3R_eq] at h₂
  have hv : Silmaril.Wasm.Component.Reference.check? Silmaril.Wasm.Component.Features.all c = .ok ct := by
    revert h₂
    cases Silmaril.Wasm.Component.Reference.check? Silmaril.Wasm.Component.Features.all c with
    | ok ct' => intro h₂; cases h₂; rfl
    | error e => intro h₂; cases h₂
  exact ⟨x, c, hx, ht, Silmaril.Wasm.Component.Reference.check?_sound hv,
    fun names => LayoutRefX.read_toRefX ht names⟩

/-- `refCore3` results are `refCore3X` results. -/
theorem refCore3X_of {b : ByteArray} {c : Silmaril.Wasm.Component.Reference.Core3Component}
    (h : refCore3 b = .ok c) : refCore3X b = .ok c := by
  obtain ⟨x, hx, ht⟩ := refCore3_ok h
  unfold refCore3X
  rw [hx, Silmaril.Wasm.Perf.CoreDecode.decodeF_eq]
  simp only [LayoutRefX.toRefX_of_toRef ht]

end Silmaril.Wasm.JcoTool.ToolV
