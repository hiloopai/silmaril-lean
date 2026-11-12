module

public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkInst

/-!
# The wiring of a linked pair: trampoline indices and the split fragment

* `trampIdxL_wireFid`: under `WireNodup`, the trampoline of import `k` (lowering the exporter's
  function `wireFid l k`) has import index `k`; `trampIdxL_tramp` for every trampoline of
  `trampsL`.
* Litmus: `dblFwdL_wireNodup`, `dblFwdL_splitOk` (both modules are in the split fragment, by
  kernel reduction of the module literals).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime

/-- **The import index of the trampoline of import `k`.** -/
theorem trampIdxL_wireFid {E : Engine} {l : Linked2} (hn : l.WireNodup) {k : Nat}
    (hk : k < l.wire.length) (ft : WIT.FuncType Empty RtId) (o : CanonOpts E) (inst : InstId) :
    l.trampIdxL (E := E) (.lowered (l.wireFid k) ft o inst) = k := by
  simp only [Linked2.trampIdxL, Linked2.wireFid, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.Nodup.idxOf_getElem hn k hk

/-- The trampolines of `trampsL` at the wiring: trampoline `k` has import index `k`. -/
theorem trampIdxL_tramp {P : Silmaril.Wasm.Numerics.Profile} {l : Linked2} (hn : l.WireNodup)
    (hw : l.WireTy) (inst : InstId) {k : Nat} {fi : Silmaril.Wasm.Execution.Core.FuncInst
      (CanonHost (core3P P))}
    (hk : (trampsL P inst l.wireFid l.imp.imports)[k]? = some fi) :
    FuncCode.mapH l.trampIdxL fi.code = .host k := by
  simp only [trampsL, List.getElem?_mapIdx] at hk
  cases hp : l.imp.imports[k]? with
  | none => simp [hp] at hk
  | some p =>
    simp only [hp, Option.map_some, Option.some.injEq] at hk
    subst hk
    have hk' : k < l.wire.length := by
      rw [hw.length]; exact (List.getElem?_eq_some_iff.mp hp).1
    simp only [trampFIL, FuncCode.mapH]
    rw [trampIdxL_wireFid hn hk']

theorem dblFwdL_wireNodup : dblFwdL.WireNodup := List.nodup_singleton 0

theorem dblFwdL_splitOk : dblFwdL.SplitOk :=
  ⟨⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Silmaril.Proofs.Wasm.Component.Reference
