module

public import Silmaril.Wasm.JcoTool.KTeeEmit.Defs
public import Silmaril.Wasm.JcoTool.KTeeNet.Thms
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound
public import Silmaril.Wasm.Binary.Core.Modules
public import Silmaril.Wasm.Text.Core.Modules

/-!
# The bytes and text of `wasm-jco ktee` are the generated tee

* `wasmOfT_encodes`: the bytes `wasm-jco ktee NAME N -o` writes encode `toModuleT N NAME` in the
  Core 3.0 binary grammar (silmaril's `encodeModule?_sound`);
* `watOfT_encodes`: the text it prints denotes `toModuleT N NAME` in the Core 3.0 text grammar;
* `ktee_tool_correct`: the program behind them is `KTee.genT N`, the module whose steps are
  steps of the tee node (`KTee.step_sim`), so a tee network whose tee and branches are generated
  modules is correct (`KTeeNet.gtee_correct`).

Not covered: that `toModuleT N NAME` runs, under Core 3.0, as `KDrop.dexec` says (for `genD`
this is `KCoreRun`; for the tee it is not done, see `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeEmit

open Silmaril.Wasm
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)

/-- Silmaril's verified encoder, for any module. -/
theorem encodes_of {m : Module} {b : ByteArray} (h : wasmOfM m = .ok b) :
    Binary.Core.Encodes b.data.toList m := by
  unfold wasmOfM at h
  cases he : Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | error e => simp [he] at h
  | ok bs =>
    simp only [he, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    simpa using Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound he

/-- Silmaril's checked printer, for any module. -/
theorem text_of {m : Module} {t : String} (h : watOfM m = .ok t) : Text.Core.Encodes t m := by
  unfold watOfM at h
  cases hd : Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax? m with
  | none => simp [hd] at h
  | some x =>
    cases hr : Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument? x with
    | none => simp [hd, hr] at h
    | some t' =>
      simp only [hd, hr, Except.ok.injEq] at h
      subst h
      exact ⟨x, Silmaril.Wasm.Binaryen.Toolkit.renderWatDocument?_sound hr,
        Silmaril.Wasm.Binaryen.Toolkit.Wat.moduleSyntax?_sound hd⟩

/-- **The bytes encode the generated tee.** -/
theorem wasmOfT_encodes {N : Nat} {name : String} {b : ByteArray}
    (h : wasmOfT N name = .ok b) : Binary.Core.Encodes b.data.toList (toModuleT N name) :=
  encodes_of h

/-- **The text denotes the generated tee.** -/
theorem watOfT_encodes {N : Nat} {name : String} {t : String}
    (h : watOfT N name = .ok t) : Text.Core.Encodes t (toModuleT N name) :=
  text_of h

/-- The module's lift and callback are `genT N`'s, printed by `KCoreEmit.sCode`. -/
theorem toModuleT_funcs (N : Nat) (name : String) :
    (toModuleT N name).funcs = (KCoreEmit.toModule (Silmaril.Wasm.JcoTool.KTee.genT N) name).funcs := rfl

/-- **The tool's tee is the proved one**: the bytes encode `toModuleT N`, whose program is
`genT N`, and the fully generated tee network is correct. -/
theorem ktee_tool_correct {N : Nat} {name : String} {b : ByteArray} (h : wasmOfT N name = .ok b)
    (hN : 0 < N ∧ N ≤ 256) :
    Binary.Core.Encodes b.data.toList (toModuleT N name) ∧
      ∀ {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat}, 0 < N₁ ∧ N₁ ≤ 256 → 0 < N₂ ∧ N₂ ≤ 256 →
        ∀ {m : Silmaril.Wasm.JcoTool.KNet.MSys (KTeeNet.gtee xs N k₁ k₂ N₁ N₂).net},
          KTeeNet.GReach _ m →
          (∀ bb, (m.ns (4 : Fin 6)).rd = .gone bb → (m.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
          (∀ bb, (m.ns (5 : Fin 6)).rd = .gone bb → (m.ns (5 : Fin 6)).got = (trV k₂).run xs) :=
  ⟨wasmOfT_encodes h, fun h₁ h₂ _ hm => KTeeNet.gtee_correct hN h₁ h₂ hm⟩

end Silmaril.Wasm.JcoTool.KTeeEmit
