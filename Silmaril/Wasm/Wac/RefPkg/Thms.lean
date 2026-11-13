module

public import Silmaril.Wasm.Wac.RefPkg.Defs
public import Silmaril.Wasm.Wac.EndToEnd.Thms
public import Silmaril.Wasm.JcoTool.RefSimple.Thms

/-!
# WAC packages that the reference machine runs as their algebra meaning: theorems

* **`pkgMeaning_ref`**: under `rdRef`, a package's meaning is the default `dflt` (no package, or
  one that is not a simple component in the fragment), or `s.toComp` for a simple component `s`
  in the soundness fragment whose reference component is what the package is
  (`LayoutRef.toRef` of its sections, core modules by silmaril's verified decoder), so that
  `RefSimple.readSimple_sound`'s conclusion applies to it (`Simple.sound`).
* **`composeText_ref`**: `EndToEnd.composeText_correct` at `rd := rdRef`: the component read
  off the bytes `wasm-wac compose --wasm` writes is the document's algebra term evaluated at
  the packages' meanings, each of which is as in `pkgMeaning_ref`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.RefPkg

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Reference (NumModule Simple funcExportNames)
open Silmaril.Wasm.JcoTool (XComp)
open Silmaril.Wasm.JcoTool.RefSimple (rdRef xcompOfX)
open Silmaril.Wasm.Wac.Emit (pkgMeaning)

/-- A package meaning the reference machine runs as itself: `C = s.toComp` for a simple
component `s` in the fragment whose reference component the package `a` is. -/
def RefRuns (a : BinaryAsync.AstX) (C : Comp NumModule) : Prop :=
  ∃ (x : XComp) (s : Simple), xcompOfX a = some x ∧
    JcoTool.LayoutRef.toRef Silmaril.Wasm.Binary.Core.decode? x = some s.toRef ∧ C = s.toComp ∧
    s.Good ∧ s.FloatFree ∧ s.Arity ∧ funcExportNames s.mod.mod = s.mod.exports.map (·.1)

/-- **Each package meaning under `rdRef`** is the default, or a package the reference machine
runs as that meaning. -/
theorem pkgMeaning_ref (dflt : Comp NumModule) (o : Option BinaryAsync.AstX) :
    pkgMeaning rdRef dflt o = dflt ∨
      ∃ a, o = some a ∧ RefRuns a (pkgMeaning rdRef dflt o) := by
  cases o with
  | none => exact .inl rfl
  | some a =>
    cases h : rdRef a with
    | none => exact .inl (by simp [pkgMeaning, h])
    | some C =>
      have hm : pkgMeaning rdRef dflt (some a) = C := by simp [pkgMeaning, h]
      exact .inr ⟨a, rfl, hm ▸ JcoTool.RefSimple.rdRef_sound h⟩

/-- **`wasm-wac compose --wasm` with packages the reference machine runs as their meaning.** -/
theorem composeText_ref {src : String} {raw : List (String × ByteArray)} {b : ByteArray}
    {tbl : SpliceX.PkgTableX} (h : EndToEnd.composeText src raw = .ok (b, some tbl, true))
    (S : Nat → PkgSig) (dflt : Comp NumModule) :
    ∃ (g : _) (pk : Nat → Option BinaryAsync.AstX),
      refComp S dflt b = .ok (((Bridge.toGraph S g).term S).eval
        fun k => pkgMeaning rdRef dflt (pk k)) ∧
      ∀ k, pkgMeaning rdRef dflt (pk k) = dflt ∨
        ∃ a, pk k = some a ∧ RefRuns a (pkgMeaning rdRef dflt (pk k)) := by
  obtain ⟨_, _, _, _, _, g, c, -, -, -, -, -, -, -, -, -, -, -, hX⟩ :=
    EndToEnd.composeText_correct h
  exact ⟨g, fun k => ((SpliceX.pkgSrcs c)[k]?).bind (SpliceX.PkgSrc.resolve tbl),
    hX S rdRef dflt, fun k => pkgMeaning_ref dflt _⟩

end Silmaril.Wasm.Wac.RefPkg
