module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkExp

/-!
# Core runs in a store with extra functions (the split fragment)

The engine `fxEV P` instantiates a module's Core part and then allocates its FX functions after
it, so a Core export runs in the store of the Core instance **extended by the FX functions**,
not in the store of the module's `IsInst` instance. `FXRefE`'s argument renames the run to the
`IsInst` store and does not apply. This module replaces the renaming by the store split of
`Silmaril.Wasm.Game.Linking` (`PartRel`, `reach_link_back`), with the Core instance as the only
part (the empty prefix, as for the exporter of `Linked2`):

* `ext π L`: the store `π` with the functions `L` appended;
* `partRel_ext`, `fnPre_ext`: a good store (`StoreGood`, every store of a `ModSplitOk` module,
  `storeGood_inst`) is related to its extension by the identity renaming, owning everything;
* **`core_ext_run`**: a host-free run of a typed call of a core export of `m` in
  `ext I.store L` (`m.IsInst I`, `StoreGood I.store`) never reaches a host-call redex (so never
  calls a function of `L`), and the values it returns have the export's result types. The run
  maps back to a run of the instance (`reach_link_back`), where `run_no_callout_at` and
  `run_typed_at` hold.

The fragment is that of `Linked2.SplitOk`: Core modules without tags, memories, tables or
segments (the instance's module and its frames are then `Own.ModGood`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (decompose? Thread ofFlat toFlat?)
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Component.Reference (NumModule)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)
open Silmaril.Proofs.Wasm.Component.Reference (StoreGood ownOf FnPre reloc_empty exp_invoke
  reach_link_back callout_back values_back map_val_flat run_typed_at run_no_callout_at opAt
  internalP_steps linkMap)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- The store `π` with the functions `L` appended. -/
def ext (π : Store H) (L : List (FuncInst H)) : Store H := { π with funcs := π.funcs ++ L }

theorem ext_funcs_getElem? {π : Store H} {L : List (FuncInst H)} {a : Nat} {fi : FuncInst H}
    (h : π.funcs[a]? = some fi) : (ext π L).funcs[a]? = some fi := by
  simp only [ext]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]

/-- **A good store is related to its extension**, by the identity renaming. -/
theorem partRel_ext {π : Store H} (hg : StoreGood π) (L : List (FuncInst H)) :
    PartRel Ren.id (ownOf π) π (ext π L) where
  fn a ha := by
    obtain ⟨fi, hfi⟩ := Silmaril.Proofs.Wasm.Component.Reference.getElem?_of_lt' ha
    exact ⟨fi, hfi, fi, ext_funcs_getElem? hfi, rfl, fun c hc => ⟨rfl, hg.fn a fi hfi c hc⟩⟩
  gl a ha := by
    obtain ⟨g, hga⟩ := Silmaril.Proofs.Wasm.Component.Reference.getElem?_of_lt' ha
    exact ⟨g, hga, by simpa [ext] using hga, hg.gl a g hga⟩
  st a ha := by
    obtain ⟨si, hsi⟩ := Silmaril.Proofs.Wasm.Component.Reference.getElem?_of_lt' ha
    exact ⟨si, hsi, by simpa [ext] using hsi, hg.st a si hsi⟩
  ar a ha := by
    obtain ⟨ai, hai⟩ := Silmaril.Proofs.Wasm.Component.Reference.getElem?_of_lt' ha
    exact ⟨ai, hai, by simpa [ext] using hai, hg.ar a ai hai⟩
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

/-- The functions of `π` are functions of its extension. -/
theorem fnPre_ext (π : Store H) (L : List (FuncInst H)) : FnPre ({} : Store H) (ext π L) π := by
  intro a fi h
  rw [reloc_empty] at h
  exact ext_funcs_getElem? h

/-- **A typed call of a core export in an extended store**: no reached configuration is at a
host-call redex, and returned flat values have the export's result types. -/
theorem core_ext_run {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    (hg : StoreGood I.store) {k : Nat} (hk : k < m.exports.length) {xs : List Flat}
    (hxs : xs.map (·.type) = m.exports[k].2.params) (L : List (FuncInst Nat))
    {y : Store Nat × Thread}
    (run : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P)
      (ext I.store L, Thread.invokeFlat (I.addrs.getD k 0) xs) y) :
    decompose? y.1 (y.2.config y.1).code = none ∧
      ∀ (cvs : List Val) (zs : List Flat), (y.2.config y.1).code = vals cvs →
        cvs.mapM toFlat? = some zs → zs.map (·.type) = m.exports[k].2.results := by
  have hw : I.WellFormed I.store := hI.1.choose_spec.ok
  obtain ⟨ts, htyped, fi, hfi⟩ :=
    Silmaril.Wasm.Game.ScalarInstance.invoke_typed hw (opAt hI hk hxs)
  have hO : (ownOf I.store).fn (I.addrs.getD k 0) := (List.getElem?_eq_some_iff.mp hfi).1
  have hL₀ := exp_invoke (partRel_ext hg L) (fnPre_ext I.store L) hO xs
  obtain ⟨⟨π', t'⟩, ρ', O', prun, hL, -, -, hs', ht'⟩ :=
    reach_link_back run hL₀ hw.storeOk htyped
  have steps := internalP_steps prun
  have hst : (t'.config π').store = π' := Thread.config_store _ _
  have hn₀ : decompose? (t'.config π').store (t'.config π').code = none :=
    run_no_callout_at hI hw hk hxs steps
  have hn : decompose? π' (t'.config π').code = none := by
    rw [hst] at hn₀
    exact hn₀
  refine ⟨?_, fun cvs zs hc hm => ?_⟩
  · show decompose? y.1 (y.2.config y.1).code = none
    cases hd : decompose? y.1 (y.2.config y.1).code with
    | none => rfl
    | some r =>
      obtain ⟨E₁, a₁, args₁, hdx, -⟩ := callout_back P hL hs' ht' hd
      rw [hdx] at hn
      cases hn
  · obtain ⟨vs', hv', hmap⟩ := values_back P hL hs' ht' hc
    have hvv : vs'.map (linkMap ({} : Store Nat) ρ').val = vs' :=
      map_val_flat _ (show (vs'.map (linkMap ({} : Store Nat) ρ').val).mapM toFlat? = some zs by
        rw [hmap]; exact hm)
    have hcv : vs' = cvs := hvv.symm.trans hmap
    exact run_typed_at hI hw hk hxs steps (hcv ▸ hv') hm

end Silmaril.Proofs.Wasm.Component.FXTyped
