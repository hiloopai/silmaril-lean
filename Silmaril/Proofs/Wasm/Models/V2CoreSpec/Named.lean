module

public import Silmaril.Wasm.Models.V2CoreSpec.Defs
public import Silmaril.Wasm.Models.V2Core.Defs

/-!
# `GlobalsNamed` and 2.0 store well-formedness

The host-free and blind-host inclusions into the spec's `$instantiate` assume `GlobalsNamed`
on the Core store. An earlier step left open whether it follows from the 2.0 domain (`StoreWF`).

* **`dom_not_globalsNamed`**: it does not. 2.0 `StoreWF` constrains the *function* addresses
  of module instances (`ModWF`), not their global addresses: a store with one host function
  whose module instance names global `0`, and no globals, is in the 2.0 domain (with the closed
  host), and its Core image is not `GlobalsNamed`.
* **`globalsNamed_toCore`**: `GlobalsNamed` of the Core image is exactly `GlobalsNamedV` of the
  2.0 store (the image keeps the globals, the function order, the module instances' global
  addresses and their global exports), so the hypothesis can be stated, and checked, on the
  2.0 store; `dom_globalsNamed_iff`: on the 2.0 domain, for the Core point.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpec

open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec

variable {H : Type}

theorem mapM_mem_iff {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∀ y, y ∈ l' ↔ ∃ x ∈ l, f x = some y
  | [], l', h, y => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | a :: l, l', h, y => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rw [List.mem_cons, mapM_mem_iff hbs y]
    constructor
    · rintro (rfl | ⟨x, hx, hfx⟩)
      · exact ⟨a, List.mem_cons_self, hb⟩
      · exact ⟨x, List.mem_cons_of_mem a hx, hfx⟩
    · rintro ⟨x, hx, hfx⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · rw [hb] at hfx
        exact Or.inl (Option.some.inj hfx).symm
      · exact Or.inr ⟨x, hx', hfx⟩

theorem mapM_some_of_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, -⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact ⟨b, hb⟩
    · exact mapM_some_of_mem hbs x hx'

theorem funcInst_toCore_module {fi : Silmaril.Wasm.V2.Execution.FuncInst H}
    {fc : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : Silmaril.Wasm.V2.Execution.FuncInst.toCore fi = some fc) :
    fc.module = fi.module.toCore := by
  unfold Silmaril.Wasm.V2.Execution.FuncInst.toCore at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h
    rfl

theorem moduleNamed_toCore (m : Silmaril.Wasm.V2.Execution.ModuleInst) (n : Nat) :
    ((∀ a ∈ m.toCore.globals, a < n) ∧
      ∀ e ∈ m.toCore.exports, ∀ a, e.addr = .global a → a < n) ↔
    ((∀ a ∈ m.globals, a < n) ∧ ∀ e ∈ m.exports, ∀ a, e.addr = .global a → a < n) := by
  refine and_congr Iff.rfl ⟨fun h e he a ha => ?_, fun h e he a ha => ?_⟩
  · refine h _ (List.mem_map_of_mem he) a ?_
    simp only [Silmaril.Wasm.V2.Execution.ExportInst.toCore, ha,
      Silmaril.Wasm.V2.Execution.ExternAddr.toCore]
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    refine h e' he' a ?_
    cases hx : e'.addr <;>
      simp_all [Silmaril.Wasm.V2.Execution.ExportInst.toCore,
        Silmaril.Wasm.V2.Execution.ExternAddr.toCore]

/-- **`GlobalsNamed` of the Core image is `GlobalsNamedV` of the 2.0 store.** -/
theorem globalsNamed_toCore {s : VStore H} {S : CStore H}
    (h : Silmaril.Wasm.V2.Execution.Store.toCore s = some S) :
    GlobalsNamed S ↔ GlobalsNamedV s := by
  simp only [Silmaril.Wasm.V2.Execution.Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  have hmem := mapM_mem_iff hfs
  unfold GlobalsNamed GlobalsNamedV
  simp only [List.length_map]
  constructor
  · intro hS fi hfi
    obtain ⟨fc, hfc⟩ := mapM_some_of_mem hfs fi hfi
    have hS' := hS fc ((hmem fc).2 ⟨fi, hfi, hfc⟩)
    rw [funcInst_toCore_module hfc] at hS'
    exact (moduleNamed_toCore fi.module _).1 hS'
  · intro hV fc hfc
    obtain ⟨fi, hfi, hc⟩ := (hmem fc).1 hfc
    rw [funcInst_toCore_module hc]
    exact (moduleNamed_toCore fi.module _).2 (hV fi hfi)

/-- On the 2.0 domain, `GlobalsNamed` of the Core point is `GlobalsNamedV` of the 2.0 store. -/
theorem dom_globalsNamed_iff {p : Pt H} (hp : dom p) :
    GlobalsNamed (ptCore p).1 ↔ GlobalsNamedV p.1 := by
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 hp.2.1
  have hpt : (ptCore p).1 = S := by
    simp only [ptCore, hS, Option.getD_some]
  rw [hpt]
  exact globalsNamed_toCore hS

/-- The witness: one host function whose module instance names global `0`, no globals. -/
def badStore : VStore Nat where
  funcs := [⟨⟨[], []⟩, { globals := [0] }, .host 0⟩]

theorem badStore_modWF {i : Nat} {fi : Silmaril.Wasm.V2.Execution.FuncInst Nat}
    (hfi : badStore.funcs[i]? = some fi) :
    Silmaril.Wasm.V2.Execution.ModWF badStore fi.module := by
  have hi : i = 0 := by
    rcases i with _ | i
    · rfl
    · simp [badStore] at hfi
  subst hi
  have hfi' : fi = ⟨⟨[], []⟩, { globals := [0] }, .host 0⟩ := by
    simpa only [badStore, List.getElem?_cons_zero, Option.some.injEq, eq_comm] using hfi
  subst hfi'
  intro a ha
  simp at ha

/-- The witness store is well formed: its one module instance names no function. -/
theorem badStore_wf : Silmaril.Wasm.V2.Execution.StoreWF badStore :=
  ⟨fun _ _ h => badStore_modWF h, fun _ _ h => by simp [badStore] at h,
    fun _ _ h => by simp [badStore] at h, fun _ _ h => by simp [badStore] at h⟩

/-- The witness point is in the 2.0 domain. -/
theorem badStore_dom : dom (badStore, (closedV : VHost Nat)) :=
  ⟨badStore_wf, rfl, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- The Core image of the witness names global `0` and has no globals. -/
theorem badStore_not_named : ¬ GlobalsNamed (ptCore (badStore, (closedV : VHost Nat))).1 := by
  intro hn
  obtain ⟨fc, hfc⟩ : ∃ fc, (ptCore (badStore, (closedV : VHost Nat))).1.funcs[0]? = some fc :=
    ⟨_, rfl⟩
  have hg : 0 ∈ fc.module.globals := by
    cases hfc
    exact List.mem_singleton_self 0
  have hlt := (hn fc (List.mem_of_getElem? hfc)).1 0 hg
  exact absurd hlt (by decide)

/-- **2.0 `StoreWF` does not give `GlobalsNamed`**: a point of the 2.0 domain (the closed
host) whose Core image is not `GlobalsNamed`. -/
theorem dom_not_globalsNamed : ∃ p : Pt Nat, dom p ∧ ¬ GlobalsNamed (ptCore p).1 :=
  ⟨(badStore, closedV), badStore_dom, badStore_not_named⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpec
