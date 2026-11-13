module

public import Silmaril.Wasm.Wac.PlugCheck.Defs
public import Silmaril.Wasm.Wac.StreamPkg.Thms

/-!
# WAC: `wac plug` of stream packages, restated on a checked shape

* `binSigs_eq`: the interfaces of the packages read by `lowerXf κ` from any binary are
  `stageSigs`, whatever `κ` and the bytes;
* `plugShape_spec`: `plugShape b = true` is the graph equation `hG` of `StreamPkg.plugX_fusion`;
* **`plugX_fusion_checked`**, **`plugX_realizes_checked`**: the two plug theorems with the
  checked `plugShape b = true` in place of `hG`, stated over `stageSigs`;
* **`plugDoc_noImports`**: `wac plug` refuses a socket with no imports. The stream packages that
  `wasm-streams-gen` and `wasm-jco new` build import nothing (`xfShape` asks for no component
  import), so `wasm-wac plug` of two of them fails, and no binary the tool writes from them has
  the plug shape: the plug theorems describe the batch view (`Streams.Alg.stage`, which imports
  `src`), not a composition of these packages. Their composition goes through a driver; its
  reading is `Silmaril.Wasm.Wac.StreamFn`. (Tested by `tools/wac/tests/streams.sh`, case
  `plug-refused`: both `wasm-wac plug` and `wac plug` refuse.)
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.PlugCheck

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamPkg Silmaril.Wasm.Wac.Emit
open Silmaril.Wasm.Component.BinaryAsync Silmaril.Wasm.Component.Streams

theorem sigOf_pkgMeaning (κ : Interp) (o : Option AstX) :
    sigOf (pkgMeaning (lowerXf κ) dflt o) = sigOf (stage .id) := by
  unfold pkgMeaning
  cases h : o.bind (lowerXf κ) with
  | none => rfl
  | some c =>
    obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s, k, -, -, rfl⟩ := lowerXf_some ha
    rfl

/-- The packages read by `lowerXf κ` all have the stage interface. -/
theorem binSigs_eq (κ : Interp) (b : ByteArray) : binSigs κ b = stageSigs := by
  funext k
  unfold binSigs binPkgs
  cases parseX b with
  | ok a => exact sigOf_pkgMeaning κ _
  | error e => rfl

theorem plugShape_spec {b : ByteArray} (h : plugShape b = true) :
    binGraphX stageSigs b = .ok (plugGraph stageSigs) := by
  unfold plugShape at h
  split at h
  · rename_i G hG
    rw [hG, of_decide_eq_true h]
  · cases h

theorem plugShape_hG {κ : Interp} {b : ByteArray} (h : plugShape b = true) :
    binGraphX (binSigs κ b) b = .ok (plugGraph (binSigs κ b)) := by
  rw [binSigs_eq]
  exact plugShape_spec h

/-- **`wac plug` of two stream packages is the fused stage**, on a binary whose plug shape is
checked. -/
theorem plugX_fusion_checked {κ : Interp} {b : ByteArray} {a c : TCode}
    (hc : plugShape b = true)
    (h0 : binPkgs (lowerXf κ) dflt b 0 = stage a) (h1 : binPkgs (lowerXf κ) dflt b 1 = stage c) :
    ∃ X, binCompX stageSigs (lowerXf κ) dflt b = .ok X ∧
      CompEquiv batchSem (select (List.range 1) X) (stage (.comp a c)) := by
  have e := plugX_fusion (plugShape_hG hc) h0 h1
  rwa [binSigs_eq] at e

/-- **`wac plug` of two stream packages realises the composite transformer**, for any
compositional stream semantics, on a binary whose plug shape is checked. -/
theorem plugX_realizes_checked {κ : Interp} {b : ByteArray} {C : CoreSem TCode}
    (Ssem : StreamSem C) {σ τ α β γ : Type} {T : Tr σ α β} {U : Tr τ β γ}
    (hc : plugShape b = true)
    (h0 : Realizes Ssem (binPkgs (lowerXf κ) dflt b 0) T)
    (h1 : Realizes Ssem (binPkgs (lowerXf κ) dflt b 1) U)
    (hnames : names (binPkgs (lowerXf κ) dflt b 1).imports =
      names (exportIface (binPkgs (lowerXf κ) dflt b 0)))
    (hn₀ : (names (binPkgs (lowerXf κ) dflt b 0).imports).Nodup)
    (hne : (names (exportIface (binPkgs (lowerXf κ) dflt b 0))).Nodup)
    (hn₁ : (names (exportIface (binPkgs (lowerXf κ) dflt b 1))).Nodup) :
    ∃ X, binCompX stageSigs (lowerXf κ) dflt b = .ok X ∧
      Realizes Ssem (select (List.range (binPkgs (lowerXf κ) dflt b 1).exports.length) X)
        (T.comp U) := by
  have e := plugX_realizes Ssem (plugShape_hG hc) h0 h1 hnames hn₀ hne hn₁
  rwa [binSigs_eq] at e

theorem usedPlugs_noImports {socket : PkgType} (h : socket.imports = []) (plugs : List PkgType) :
    usedPlugs socket plugs = [] := by
  simp [usedPlugs, matched, h]

/-- **`wac plug` refuses a socket with no imports.** -/
theorem plugDoc_noImports {socket : PkgType} (h : socket.imports = []) (plugs : List PkgType) :
    plugDoc socket plugs = .error "no plug matched an import of the socket" := by
  simp [plugDoc, usedPlugs_noImports h]
  rfl

end Silmaril.Wasm.Wac.PlugCheck
