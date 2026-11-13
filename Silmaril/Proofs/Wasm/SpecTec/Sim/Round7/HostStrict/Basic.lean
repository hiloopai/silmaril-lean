module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.Defs
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# the cloning host (proofs)

The five properties of `Round7.HostStrict.cloneHost`: finite, `HostOk`, invents no module,
export-blind, and not export-parametric.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.HostMods (HostModsSub)

variable {H : Type}

/-! ## Finite, and no new module -/

open Classical in
theorem cloneHost_finite : HostFinite (cloneHost (H := H)) := by
  intro h s vs
  refine ⟨.diverged :: (s.funcs.filter fun fi => decide (Clonable s fi)).map
    fun fi => .returned (cloneStore s fi) .trap, fun o => ?_⟩
  simp only [cloneHost, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (rfl | ⟨fi, hc, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨fi, ⟨hc.1, hc⟩, rfl⟩
  · rintro (rfl | ⟨fi, ⟨_, hc⟩, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨fi, hc, rfl⟩

theorem cloneHost_modsSub : HostModsSub (cloneHost (H := H)) := by
  rintro h s s' vs r (hd | ⟨fi, hc, ho⟩) g hg
  · cases hd
  · cases ho
    simp only [cloneStore, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact List.mem_map_of_mem hg
    · exact List.mem_map_of_mem hc.1

/-! ## `HostOk` -/

theorem immut_clone {s : Store H} {fi : FuncInst H} {a b : FieldVal}
    (h : ImmutReachable (cloneStore s fi) a b) : ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

theorem extend_clone {s : Store H} (hs : StoreOk s) (fi : FuncInst H) :
    Extend s (cloneStore s fi) :=
  let he := Extend.refl hs
  { tags := he.tags, globals := he.globals, mems := he.mems, tables := he.tables
    funcs := ExtendsList.of_prefix (List.prefix_append _ _)
      fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
    datas := he.datas, elems := he.elems, structs := he.structs, arrays := he.arrays
    exns := he.exns }

theorem funcInstOk_clone {s : Store H} (hs : StoreOk s) {fi g : FuncInst H}
    (hfi : fi ∈ s.funcs) (hg : g ∈ (cloneStore s fi).funcs) : FuncInstOk (cloneStore s fi) g := by
  have he := extend_clone hs fi
  have hg' : g ∈ s.funcs := by
    simp only [cloneStore, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hg
    · exact hfi
  cases hs.funcs g hg' with
  | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
  | host hdt he' hcode => exact .host hdt he' hcode

theorem storeOk_clone {s : Store H} (hs : StoreOk s) {fi : FuncInst H} (hfi : fi ∈ s.funcs) :
    StoreOk (cloneStore s fi) :=
  have he := extend_clone hs fi
  { tags := hs.tags
    globals := fun gi h => ⟨(hs.globals gi h).1, (hs.globals gi h).2.extend he⟩
    mems := hs.mems
    tables := fun ti h => ⟨(hs.tables ti h).1, (hs.tables ti h).2.1,
      fun r hr => ((hs.tables ti h).2.2 r hr).extend he⟩
    funcs := fun _ h => funcInstOk_clone hs hfi h
    elems := fun ei h => (hs.elems ei h).extend he ⟨rfl, .inl rfl⟩
    structs := fun si h => by
      obtain ⟨fs, hx, hf⟩ := hs.structs si h
      exact ⟨fs, hx, hf.imp fun _ _ h => h.extend he⟩
    arrays := fun ai h => by
      obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
      exact ⟨ft, hx, fun fv hfv => (hf fv hfv).extend he⟩
    exns := fun e h => by
      obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
      exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => h.extend he⟩
    acyclicStructs := fun a ha hr => hs.acyclicStructs a ha (immut_clone hr)
    acyclicArrays := fun a ha hr => hs.acyclicArrays a ha (immut_clone hr)
    acyclicExns := fun a ha hr => hs.acyclicExns a ha (immut_clone hr)
    structsClosed := hs.structsClosed
    arraysClosed := hs.arraysClosed }

theorem cloneHost_ok : HostOk (cloneHost (H := H)) := by
  intro s _ h vs _ _ hs _ _ _ _
  refine ⟨⟨.diverged, .inl rfl⟩, fun out ho => ?_⟩
  rcases ho with rfl | ⟨fi, hc, rfl⟩
  · trivial
  · exact ⟨storeOk_clone hs hc.1, extend_clone hs fi, trivial⟩

/-! ## Export-blind -/

theorem stripStore_clone (s : Store H) (fi : FuncInst H) :
    stripStore (cloneStore s fi) = cloneStore (stripStore s) (stripFI fi) := by
  simp [stripStore, cloneStore, stripFI]

theorem clonable_strip {s : Store H} {fi : FuncInst H} (hc : Clonable s fi) :
    Clonable (stripStore s) (stripFI fi) :=
  ⟨List.mem_map_of_mem hc.1, .inl rfl⟩

/-- Every clonable instance of the stripped store is the stripped form of a clonable instance. -/
theorem clonable_unstrip {s : Store H} {g : FuncInst H} (hc : Clonable (stripStore s) g) :
    ∃ fi, Clonable s fi ∧ g = stripFI fi := by
  obtain ⟨fi₀, hfi₀, rfl⟩ := List.mem_map.1 hc.1
  by_cases hx : ∃ fi ∈ s.funcs, stripFI fi = stripFI fi₀ ∧ fi.module.exports = []
  · obtain ⟨fi, hfi, he, hx⟩ := hx
    exact ⟨fi, ⟨hfi, .inl hx⟩, he.symm⟩
  · refine ⟨fi₀, ⟨hfi₀, .inr fun fi' hfi' he hx' => hx ⟨fi', hfi', he, hx'⟩⟩, rfl⟩

theorem cloneHost_blind : HostExportBlind (cloneHost (H := H)) := by
  refine ⟨?_, ?_⟩
  · rintro h s vs o (rfl | ⟨fi, hc, rfl⟩)
    · exact .inl rfl
    · refine .inr ⟨stripFI fi, clonable_strip hc, ?_⟩
      simp only [stripOutcome, stripStore_clone]
  · rintro h s vs o' (rfl | ⟨g, hc, rfl⟩)
    · exact ⟨.diverged, .inl rfl, rfl⟩
    · obtain ⟨fi, hc', rfl⟩ := clonable_unstrip hc
      exact ⟨_, .inr ⟨fi, hc', rfl⟩, by simp only [stripOutcome, stripStore_clone]⟩

/-! ## Not export-parametric -/

section Swap

variable (fi : FuncInst H)

/-- The module of `fi` with no exports. -/
def m₀ : ModuleInst := { fi.module with exports := [] }

/-- The same module exporting one name. -/
def m₁ : ModuleInst := { fi.module with exports := [⟨"e", .func 0⟩] }

/-- Swap `m₀` and `m₁`; every other module is fixed. -/
def swapμ (m : ModuleInst) : ModuleInst :=
  if m = m₀ fi then m₁ fi else if m = m₁ fi then m₀ fi else m

/-- A store with two instances that differ only in their module's exports. -/
def swapStore : Store H :=
  { funcs := [{ fi with module := m₀ fi }, { fi with module := m₁ fi }] }

theorem m₁_ne_m₀ : m₁ fi ≠ m₀ fi := fun h => by
  have := congrArg ModuleInst.exports h
  simp [m₀, m₁] at this

theorem exportOnly_swapμ : ExportOnly (swapμ fi) := by
  intro m
  unfold swapμ
  split_ifs with h₀ h₁
  · subst h₀; rfl
  · subst h₁; rfl
  · rfl

theorem not_clonable_swap :
    ¬ Clonable (mapStore (swapμ fi) (swapStore fi)) { fi with module := m₁ fi } := by
  rintro ⟨_, hx | hx⟩
  · simp [m₁] at hx
  · refine hx { fi with module := m₀ fi } ?_ rfl rfl
    simp [mapStore, swapStore, mapFI, swapμ, m₁_ne_m₀]

theorem cloneHost_swap_ret (h : H) :
    cloneHost h (swapStore fi) []
      (.returned (cloneStore (swapStore fi) { fi with module := m₀ fi }) .trap) :=
  .inr ⟨_, ⟨by simp [swapStore], .inl rfl⟩, rfl⟩

theorem not_cloneHost_swap (h : H) :
    ¬ cloneHost h (mapStore (swapμ fi) (swapStore fi)) []
      (mapOutcome (swapμ fi)
        (.returned (cloneStore (swapStore fi) { fi with module := m₀ fi }) .trap)) := by
  rintro (hd | ⟨g, hc, ho⟩)
  · cases hd
  · simp only [mapOutcome, Silmaril.Wasm.Execution.Host.Outcome.returned.injEq, and_true] at ho
    have hf := congrArg Store.funcs ho
    simp only [mapStore, cloneStore, List.map_append, List.map_cons, List.map_nil,
      List.append_cancel_left_eq, List.cons.injEq, and_true] at hf
    subst hf
    exact not_clonable_swap fi (by simpa [mapFI, swapμ] using hc)

end Swap

/-- **`cloneHost` is not export-parametric**, as soon as there is a function instance and a host
function. -/
theorem cloneHost_not_param (fi : FuncInst H) (h : H) : ¬ HostExportParam (cloneHost (H := H)) :=
  fun hp => not_cloneHost_swap fi h (hp _ (exportOnly_swapμ fi) _ _ _ _ (cloneHost_swap_ret fi h))

end Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict
