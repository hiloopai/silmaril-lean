module

public import Silmaril.Wasm.SpecTec.Sim.Round7.REGap.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# REH gaps: the stripped-cloning host (proofs)

`Round7.REGap.stripCloneHost` is finite, `HostOk` and export-blind. It invents modules
(`not_modsSub_stripCloneHost`), and one call at a store whose modules do not collide can return a
store whose modules do (`collides_stripClone`), so `StripInj` fails at every configuration over
it (`not_stripInj_of_collide`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.REGap

open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.HostMods (HostModsSub)
open Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict (cloneStore extend_clone immut_clone stripStore_clone)

variable {H : Type}

/-! ## Typing the stripped copy -/

/-- Removing a module's exports keeps it typed, over the same store. -/
theorem moduleInstOk_stripAt {s : Store H} {m : ModuleInst} {C : Context}
    (h : ModuleInstOk s m C) : ModuleInstOk s (stripModule m) C := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems _ _ _ hk =>
    exact .mk htypes htags hglobals hfuncs hmems htables hdatas helems
      (fun _ h => absurd h List.not_mem_nil) List.nodup_nil
      (fun _ h => absurd h List.not_mem_nil) hk

/-- Removing a function instance's module's exports keeps it typed, over the same store. -/
theorem funcInstOk_stripAt {s : Store H} {fi : FuncInst H} (h : FuncInstOk s fi) :
    FuncInstOk s (stripFI fi) := by
  cases h with
  | wasm hdt hm hcode hf hs => exact .wasm hdt (moduleInstOk_stripAt hm) hcode hf hs
  | host hdt he hcode => exact .host hdt he hcode

theorem funcInstOk_extend {s s' : Store H} (hs : StoreOk s) (he : Extend s s') {g : FuncInst H}
    (h : FuncInstOk s g) : FuncInstOk s' g := by
  cases h with
  | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
  | host hdt he' hcode => exact .host hdt he' hcode

/-- **Appending a typed function instance keeps a store typed.** -/
theorem storeOk_cloneG {s : Store H} (hs : StoreOk s) {fi : FuncInst H} (hfi : FuncInstOk s fi) :
    StoreOk (cloneStore s fi) :=
  have he := extend_clone hs fi
  { tags := hs.tags
    globals := fun gi h => ⟨(hs.globals gi h).1, (hs.globals gi h).2.extend he⟩
    mems := hs.mems
    tables := fun ti h => ⟨(hs.tables ti h).1, (hs.tables ti h).2.1,
      fun r hr => ((hs.tables ti h).2.2 r hr).extend he⟩
    funcs := fun g hg => by
      simp only [cloneStore, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact funcInstOk_extend hs he (hs.funcs g hg)
      · exact funcInstOk_extend hs he hfi
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

/-! ## Finite, `HostOk`, export-blind -/

theorem stripCloneHost_finite : HostFinite (stripCloneHost (H := H)) := by
  intro h s vs
  refine ⟨.diverged :: s.funcs.map fun fi => .returned (cloneStore s (stripFI fi)) .trap,
    fun o => ?_⟩
  simp only [stripCloneHost, List.mem_cons, List.mem_map]
  constructor
  · rintro (rfl | ⟨fi, hfi, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨fi, hfi, rfl⟩
  · rintro (rfl | ⟨fi, hfi, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨fi, hfi, rfl⟩

theorem stripCloneHost_ok : HostOk (stripCloneHost (H := H)) := by
  intro s _ h vs _ _ hs _ _ _ _
  refine ⟨⟨.diverged, .inl rfl⟩, fun out ho => ?_⟩
  rcases ho with rfl | ⟨fi, hfi, rfl⟩
  · trivial
  · exact ⟨storeOk_cloneG hs (funcInstOk_stripAt (hs.funcs fi hfi)), extend_clone hs _, trivial⟩

theorem stripFI_mem_stripStore {s : Store H} {fi : FuncInst H} (h : fi ∈ s.funcs) :
    stripFI fi ∈ (stripStore s).funcs :=
  List.mem_map_of_mem h

theorem stripCloneHost_blind : HostExportBlind (stripCloneHost (H := H)) := by
  refine ⟨?_, ?_⟩
  · rintro h s vs o (rfl | ⟨fi, hfi, rfl⟩)
    · exact .inl rfl
    · exact .inr ⟨stripFI fi, stripFI_mem_stripStore hfi, by
        simp only [stripOutcome, stripStore_clone]⟩
  · rintro h s vs o' (rfl | ⟨g, hg, rfl⟩)
    · exact ⟨.diverged, .inl rfl, rfl⟩
    · obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hg
      exact ⟨_, .inr ⟨fi, hfi, rfl⟩, by simp only [stripOutcome, stripStore_clone]; rfl⟩

/-! ## It invents modules, and breaks `StripInj` -/

theorem stripModule_ne {m : ModuleInst} (hx : m.exports ≠ []) : m ≠ stripModule m := fun h =>
  hx (congrArg ModuleInst.exports h)

/-- **One call returns a store whose modules collide**, from any store holding an instance
whose module exports something. -/
theorem collides_stripClone (h : H) (vs : List Val) {s : Store H} {fi : FuncInst H}
    (hfi : fi ∈ s.funcs) (hx : fi.module.exports ≠ []) :
    stripCloneHost h s vs (.returned (cloneStore s (stripFI fi)) .trap) ∧
      StoreCollides (cloneStore s (stripFI fi)) := by
  refine ⟨.inr ⟨fi, hfi, rfl⟩, fi.module, ?_, stripModule fi.module, ?_, stripModule_ne hx, rfl⟩
  · simp only [cloneStore, List.map_append, List.mem_append]
    exact .inl (List.mem_map_of_mem hfi)
  · simp [cloneStore, stripFI]

/-- A store with one function instance has no collision. -/
theorem not_collides_single (fi : FuncInst H) : ¬ StoreCollides ({ funcs := [fi] } : Store H) := by
  rintro ⟨m₁, h₁, m₂, h₂, hne, -⟩
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at h₁ h₂
  exact hne (h₁.trans h₂.symm)

/-- **A configuration over a store whose modules collide fails `StripInj`.** -/
theorem not_stripInj_of_collide {c : Config H} (h : StoreCollides c.store) : ¬ StripInj c := by
  rintro hi
  obtain ⟨m₁, h₁, m₂, h₂, hne, he⟩ := h
  exact hne (hi m₁ (List.mem_append_left _ h₁) m₂ (List.mem_append_left _ h₂) he)

/-- **`stripCloneHost` invents modules**, as soon as there is a function instance whose module
exports something, and a host function. -/
theorem not_modsSub_stripCloneHost (h : H) (fi : FuncInst H) (hx : fi.module.exports ≠ []) :
    ¬ HostModsSub (stripCloneHost (H := H)) := by
  intro hm
  have hfi : fi ∈ ({ funcs := [fi] } : Store H).funcs := List.mem_singleton_self _
  have ho := (collides_stripClone h [] hfi hx).1
  have := hm h _ _ [] _ ho (stripFI fi) (by simp [cloneStore])
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
  exact stripModule_ne hx this.symm

end Silmaril.Wasm.SpecTec.Sim.Round7.REGap
