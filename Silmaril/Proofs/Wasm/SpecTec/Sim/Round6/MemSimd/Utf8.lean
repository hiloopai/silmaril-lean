module

public import Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 6: the U7 builtin is inert, so `NoExports` stays

`withUtf8 B` does answer `$utf8` (`withUtf8_call_g`), but `callDef` consults the builtins only
when the clauses of a definition fail definitely (`undef`), and the first clause of `$utf8`
loops to `outOfFuel` on every non-empty list (`Round5.Pos.tryClauses_utf8`). Hence:

* `not_typedV_moduleinst_withUtf8`: with the U7 builtin installed, a module instance exporting a
  one-character name is still not a typed `moduleinst` (this is round 5's
  `not_typedV_moduleinst_of_export`, which holds for every `B`);
* `noMissel_expNopCfg`, `noMissel_expDoneCfg`: round 5's witness (`nop` over a module exporting
  `"g"`) has no `FloatMissel` code;
* `not_forwardSelE`: the forward conjunct over `BoundedSelE` (`BoundedSel` without `NoExports`)
  fails for every `B`;
* `not_wholeStepValidSelE`: **`Round5.Task.wholeStepValidSel` with `NoExports` dropped is
  false**, whatever builtins are chosen.

So the export-free restriction cannot be dropped from any target read in `simEnv B`; removing it
needs a different reading of `$utf8` (an erratum to the script, as erratum 685 did for
wasm-1.0), not a builtin.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- The U7 builtin answers `$utf8("g")` with the byte `0x67`. -/
theorem withUtf8_call_g (B : Builtins) :
    (withUtf8 B).call "utf8"
      [.val (.list [Silmaril.SpecTec.Equiv.RuntimeBridge.charToValue 'g'])] =
      some (.list [Silmaril.SpecTec.Equiv.Execution.pctV 103]) := by
  have h : String.utf8EncodeChar (Char.ofNat 103) = [103] := by decide
  simp [withUtf8, utf8Call, charCode?, Silmaril.SpecTec.Equiv.RuntimeBridge.charToValue,
    utf8CharV, h]

/-- **With the U7 builtin, an exporting module instance is still untyped.** -/
theorem not_typedV_moduleinst_withUtf8 (B : Builtins) (m : ModuleInst) (e : ExportInst)
    (he : e ∈ m.exports) (c : Char) (hc : e.name.toList = [c]) :
    ¬ TypedV (simEnv (withUtf8 B)) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m) :=
  Round5.Pos.not_typedV_moduleinst_of_export (withUtf8 B) m e he c hc

theorem noMissel_expNopCfg : Round5.Target.NoMissel (Round5.Pos.expNopCfg (H := H)) :=
  ⟨by simp [Round5.Target.StoreSel, Round5.Pos.expNopCfg, ConfigOk.exportStore],
    ⟨rfl, trivial⟩⟩

theorem noMissel_expDoneCfg : Round5.Target.NoMissel (Round5.Pos.expDoneCfg (H := H)) :=
  ⟨by simp [Round5.Target.StoreSel, Round5.Pos.expDoneCfg, ConfigOk.exportStore], trivial⟩

/-- **The forward conjunct over `BoundedSelE` fails**, for every `B`, profile, host and
encoding. -/
theorem not_forwardSelE (B : Builtins) (P : Profile) (host : HostSemantics H) (hn : H → String) :
    ¬ ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelE c →
      BoundedSelE c' → Step P host c c' →
      ∃ d', Bwd.ConfigEq c' d' ∧ SStep (simEnv B) (configV hn c) (configV hn d') := fun h => by
  obtain ⟨d', -, hs⟩ := h Round5.Pos.expNopCfg Round5.Pos.expDoneCfg []
    Round5.Pos.configOk_expNopCfg ⟨Round5.Pos.bounded_expNopCfg, noMissel_expNopCfg⟩
    ⟨Round5.Pos.bounded_expDoneCfg, noMissel_expDoneCfg⟩ (Round5.Pos.step_expNopCfg P host)
  exact Round5.Pos.not_sstep_expNopCfg B hn _ hs

/-- **`Round5.Task.wholeStepValidSel` without `NoExports` is false**, for every choice of
builtins (so with the U7 builtin `withUtf8` too). -/
theorem not_wholeStepValidSelE : ¬ WholeStepValidSelE := fun h => by
  obtain ⟨B, hf, -⟩ := h Unit Round5.Pos.hnU Round5.Pos.hnU_injective Round5.Pos.divHost
    Round5.Pos.hostFinite_divHost Round5.Pos.hostOk_divHost false {}
  exact not_forwardSelE B _ Round5.Pos.divHost Round5.Pos.hnU hf

end Silmaril.Wasm.SpecTec.Sim.Round6.MemSimd
