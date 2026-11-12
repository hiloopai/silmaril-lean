module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Typing

/-!
# Round 7: the round-6 domain at stripped configurations

Removing every export maps round 7's domain `BoundedSelE` into round 6's `BoundedSel`
(`boundedSel_strip`): the size bounds and the `FloatMissel` restriction do not read exports, and
`stripConfig c` exports nothing (`noExports_strip`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem moduleBnd_strip {m : ModuleInst} (h : Round4.ModuleBnd m) :
    Round4.ModuleBnd (stripModule m) :=
  ⟨h.1, fun _ he => absurd he List.not_mem_nil⟩

mutual
theorem adminBnd_strip : ∀ a : Admin, Round4.AdminBnd a → Round4.AdminBnd (stripAdmin a)
  | .label _ _ body, h => ⟨h.1, adminsBnd_strip body h.2⟩
  | .handler _ _ body, h => adminsBnd_strip body h
  | .frame _ _ body, h => ⟨moduleBnd_strip h.1, adminsBnd_strip body h.2⟩
  | .plain _, h | .ref _, h | .callRefType _, h | .returnCallRefType _, h | .trap, h => h

theorem adminsBnd_strip : ∀ l : List Admin, Round4.AdminsBnd l → Round4.AdminsBnd (stripAdmins l)
  | [], h => h
  | a :: l, h => ⟨adminBnd_strip a h.1, adminsBnd_strip l h.2⟩
end

mutual
theorem adminSel_strip : ∀ a : Admin, Round5.Target.AdminSel a →
    Round5.Target.AdminSel (stripAdmin a)
  | .label _ _ body, h => ⟨h.1, adminsSel_strip body h.2⟩
  | .handler _ _ body, h => adminsSel_strip body h
  | .frame _ _ body, h => adminsSel_strip body h
  | .plain _, h | .ref _, h | .callRefType _, h | .returnCallRefType _, h | .trap, h => h

theorem adminsSel_strip : ∀ l : List Admin, Round5.Target.AdminsSel l →
    Round5.Target.AdminsSel (stripAdmins l)
  | [], h => h
  | a :: l, h => ⟨adminSel_strip a h.1, adminsSel_strip l h.2⟩
end

mutual
theorem adminNE_strip : ∀ a : Admin, Round5.Pos.AdminNE (stripAdmin a)
  | .label _ _ body => adminsNE_strip body
  | .handler _ _ body => adminsNE_strip body
  | .frame _ _ body => ⟨rfl, adminsNE_strip body⟩
  | .plain _ | .ref _ | .callRefType _ | .returnCallRefType _ | .trap => True.intro

theorem adminsNE_strip : ∀ l : List Admin, Round5.Pos.AdminsNE (stripAdmins l)
  | [] => True.intro
  | a :: l => ⟨adminNE_strip a, adminsNE_strip l⟩
end

/-- `stripConfig c` exports nothing. -/
theorem noExports_strip (c : Config H) : Round5.Pos.NoExports (stripConfig c) where
  store fi hfi := by
    obtain ⟨fi₀, -, rfl⟩ := List.mem_map.mp hfi
    rfl
  frame := rfl
  code := adminsNE_strip c.code

theorem bounded_strip {c : Config H} (h : Round4.Bounded c) : Round4.Bounded (stripConfig c) where
  store := ⟨h.store.tables, ⟨h.store.aggs.arrays, h.store.aggs.elems, h.store.aggs.datas⟩,
    h.store.mems⟩
  storeBnd :=
    { tags := h.storeBnd.tags
      globals := h.storeBnd.globals
      tables := h.storeBnd.tables
      funcs := fun fi hfi => by
        obtain ⟨fi₀, hfi₀, rfl⟩ := List.mem_map.mp hfi
        obtain ⟨ht, hm, hc⟩ := h.storeBnd.funcs fi₀ hfi₀
        exact ⟨ht, moduleBnd_strip hm, hc⟩
      elems := h.storeBnd.elems
      structs := h.storeBnd.structs
      arrays := h.storeBnd.arrays }
  frame := moduleBnd_strip h.frame
  code := adminsBnd_strip c.code h.code

theorem noMissel_strip {c : Config H} (h : Round5.Target.NoMissel c) :
    Round5.Target.NoMissel (stripConfig c) where
  store fi hfi := by
    obtain ⟨fi₀, hfi₀, rfl⟩ := List.mem_map.mp hfi
    exact h.store fi₀ hfi₀
  code := adminsSel_strip c.code h.code

/-- **Round 7's domain, stripped, is in round 6's domain.** -/
theorem boundedSel_strip {c : Config H} (h : BoundedSelE c) :
    Round5.Target.BoundedSel (stripConfig c) :=
  ⟨⟨bounded_strip h.1.1, noExports_strip c⟩, noMissel_strip h.1.2⟩

end Silmaril.Wasm.SpecTec.Sim.Round7
