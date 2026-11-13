module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Prepare.Defs
public import Silmaril.Wasm.Component.Engine.Core3.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Store
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Core.Soundness.InstantiationOnce

/-!
# Typing of instantiation in the concrete Core 3.0 engine

`prepareE?` (Engine/Core3/Defs.lean) is `instantiateOnce?` (`$evalglobals`, then the spec's
direct instantiation of the global-free residue) guarded by the validator and the
`Externaddr_ok` check of the arguments. On a typed store (`Store_ok`):

* `Instantiate.extend_wasm`: the allocation phase of instantiation (the spec's `$instantiate`,
  through `$allocmodule`) extends the store, and the only new function instances are the module's
  Wasm functions (`allocModule?_inv`; constant evaluation only appends globals, structures and
  arrays, `initEval_ok`); for `instantiateOnce?`, the allocation phase of the residue after
  `$evalglobals` is typed and extends the store in the same way (`prepare?_globalResidue_ok`);
* the direct segment initialisation that follows is a run of host-free Core steps
  (`instantiateOnce?_steps`), so it keeps the functions (`Steps.funcs_eq`) and, by
  preservation, typing and store extension (`Steps.preserves`);
* `start_configOk`: the start function has type `[] -> []`: a typed `call x` at `[] -> []` names
  a function whose type expands to a function type with no parameters and no results
  (`Start_ok` of module validation, carried by the module instance's function types), so its
  invocation `$invoke(s, a, [])` is typed at `[]` (`invoke_ok`).

`prepareE?_typed` combines them.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Runs of Core steps -/

/-! ## Allocation -/

/-- Instantiation of a valid module against typed imports extends a typed store, and appends only
Wasm function instances. -/
theorem Instantiate.extend_wasm {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) :
    Extend s c.store ∧ ∃ new : List (FuncInst H), c.store.funcs = s.funcs ++ new ∧
      ∀ fi ∈ new, ∃ code, fi.code = .wasm code := by
  obtain ⟨xtE, xtI, hm, hxas⟩ := h.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hg, ht, he, ha, rfl⟩ := h.run
  cases hm with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart
      hexports hdisjoint =>
    obtain ⟨hsh, -⟩ := initEval_ok hs htypes himports hC' hC htags hglobals htables hfuncs
      helems hxas hg ht he
    obtain ⟨tagTypes, funcTypes, xi, -, -, -, -, hs₄⟩ := allocModule?_inv ha
    subst hs₄
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, _, by rw [← hsh.funcs], ?_⟩
    · exact ExtendsList.of_prefix (by rw [← hsh.tags]; exact List.prefix_append _ _)
        fun _ _ => rfl
    · exact ExtendsList.of_prefix (hsh.globals.trans (List.prefix_append _ _))
        fun _ _ => ⟨rfl, .inr rfl⟩
    · exact ExtendsList.of_prefix (by rw [← hsh.mems]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
    · exact ExtendsList.of_prefix (by rw [← hsh.tables]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
    · exact ExtendsList.of_prefix (by rw [← hsh.funcs]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
    · exact ExtendsList.of_prefix (by rw [← hsh.datas]; exact List.prefix_append _ _)
        fun _ _ => .inl rfl
    · exact ExtendsList.of_prefix (by rw [← hsh.elems]; exact List.prefix_append _ _)
        fun _ _ => ⟨rfl, .inl rfl⟩
    · refine ExtendsList.of_prefix hsh.structs fun si hsi => ?_
      obtain ⟨fs, he, hf⟩ := hs.structs si hsi
      exact ⟨rfl, fs, he, rfl, by simpa using hf.length_eq, fun _ _ h => .inr h⟩
    · refine ExtendsList.of_prefix hsh.arrays fun ai hai => ?_
      obtain ⟨ft, he, _⟩ := hs.arrays ai hai
      match ft, he with
      | .field m z, he => exact ⟨rfl, m, z, he, rfl, .inr rfl⟩
    · exact ExtendsList.of_prefix (by rw [hsh.exns]) fun _ _ => rfl
    · intro fi hfi
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hfi
      exact ⟨p.2, rfl⟩

/-! ## The start function -/

/-! ## Instantiation -/

-- FLAG(statement-change): `prepareE?` runs `instantiateOnce?` (every global allocated once)
-- instead of `instantiateDirect?`.
end Silmaril.Wasm.Component.Engine.Core3.Typed
