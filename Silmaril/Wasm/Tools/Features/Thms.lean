module

public import Silmaril.Wasm.Tools.Features.Defs
public import Silmaril.Wasm.Models.Features.Thms
public meta import Silmaril.Wasm.Tools.Features.Defs

/-!
# wasmparser feature flags: theorems

* `toFS_mono`: more wasmparser bits grant more capabilities (`F ⊆ G` as masks, `subset`);
* the groups are the named feature sets of `Silmaril.Wasm.Models`: `toFS_wasm1` (`v10`),
  `toFS_wasm2` (`v20`), `toFS_wasm3` (`v30`), `toFS_lime1` (`lime1`), `toFS_mvp` (`v10`: the
  `mutable-global` flag `mvp` lacks only gates imports and exports, see `Validate`);
* `toFS_dflt`: the default set grants every capability except stack switching and custom page
  sizes (off by default upstream), and `toFS_all` grants every capability;
* the `--features` parser: `applyActions_append` (several `--features` arguments act in order),
  and executable `#guard` checks of `parseFeatures` on upstream's examples.

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Features

open Silmaril.Wasm.Models

namespace WFeatures

/-- Mask inclusion. -/
def Subset (F G : WFeatures) : Prop := F &&& G = F

theorem hasBit_mono {F G : WFeatures} (h : Subset F G) {i : Nat} (hF : F.hasBit i = true) :
    G.hasBit i = true := by
  unfold hasBit at *
  simp only [bne_iff_ne, ne_eq] at *
  intro hG
  apply hF
  rw [← h, Nat.and_assoc, hG, Nat.and_zero]

theorem raw_mono {F G : WFeatures} (h : Subset F G) (c : Cap) (hF : raw F c = true) :
    raw G c = true := by
  cases c <;> first | rfl | exact hasBit_mono h hF

/-- **More bits, more capabilities.** -/
theorem toFS_mono {F G : WFeatures} (h : Subset F G) : toFS F ≤ toFS G := by
  rw [le_iff]
  intro c hc
  simp only [FeatureSet.has, toFS, interior, Bool.and_eq_true, List.all_eq_true] at hc ⊢
  exact ⟨raw_mono h c hc.1, fun d hd => raw_mono h d (hc.2 d hd)⟩

/-- Equality of feature sets, capability by capability. -/
theorem fs_ext {S T : FeatureSet} (h : ∀ c, S.1 c = T.1 c) : S = T :=
  Subtype.ext (funext h)

theorem toFS_wasm1 : toFS wasm1 = v10 := fs_ext fun c => by cases c <;> decide
theorem toFS_wasm2 : toFS wasm2 = v20 := fs_ext fun c => by cases c <;> decide
theorem toFS_wasm3 : toFS wasm3 = v30 := fs_ext fun c => by cases c <;> decide
theorem toFS_lime1 : toFS lime1 = Silmaril.Wasm.Models.lime1 := fs_ext fun c => by cases c <;> decide
theorem toFS_mvp : toFS mvp = v10 := fs_ext fun c => by cases c <;> decide

/-- The default set: everything but stack switching and custom page sizes. -/
theorem toFS_dflt (c : Cap) :
    (toFS dflt).has c = !(c == .stackSwitching || c == .customPageSizes) := by
  cases c <;> decide

/-- `all` grants every capability. -/
theorem toFS_all : toFS all = ⊤ := fs_ext fun c => by cases c <;> decide

end WFeatures

/-! ## The `--features` parser -/

/-! Executable checks of the parser (evaluated by `#guard`; the string functions it uses do not
reduce in the kernel). -/

#guard parseFeatures "all" == .ok [.enable WFeatures.all]
#guard parseFeatures "-all" == .ok [.disable WFeatures.all]
#guard parseFeatures "wasm1" == .ok [.reset WFeatures.wasm1]
#guard parseFeatures "mvp" == .ok [.reset WFeatures.mvp]
#guard parseFeatures "lime1" == .ok [.reset WFeatures.lime1]
#guard parseFeatures "-wasm2" == .error "cannot disable `-wasm2`, it can only be enabled"
#guard parseFeatures "foo" == .error (unknownMsg "foo")
#guard parseFeatures " simd, -gc ,," == .ok [.enable (bitsOf "simd"), .disable (bitsOf "gc")]
#guard parseFeatures "" == .ok []
#guard validNames.length == 50

/-- Several `--features` arguments act in order. -/
theorem applyActions_append (a b : List Action) :
    applyActions (a ++ b) = b.foldl Action.apply (applyActions a) := by
  simp [applyActions, List.foldl_append]

/-- No `--features` argument: the default set. -/
theorem applyActions_nil : applyActions [] = WFeatures.dflt := rfl

/-- `--features=wasm1`: Wasm 1.0. -/
theorem features_wasm1 : (applyActions [.reset WFeatures.wasm1]).toFS = v10 :=
  WFeatures.toFS_wasm1

end Silmaril.Wasm.Tools.Features
