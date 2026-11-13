module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostMods.Basic

/-!
# a Core step introduces no module instance, for a host that invents none (unrefined)

`mods_step_sub`: if `c → c'` and the host returns only module instances of the calling store
(`HostModsSub`), every module instance of `c'` is one of `c`. The new frames of `call_ref` and
`return_call_ref` take their module from a function instance of the store, every other rule keeps
or drops frames, and only a host call changes the store's function instances. One case per rule,
closed by the same simplification; kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem modsAdmin_atomic {a : Admin} (h : Atomic a) : modsAdmin a = [] := by
  cases a <;> simp_all [Atomic, modsAdmin]

theorem modsAdmins_append : ∀ l r : List Admin, modsAdmins (l ++ r) = modsAdmins l ++ modsAdmins r
  | [], _ => rfl
  | a :: l, r => by simp only [List.cons_append, modsAdmins, modsAdmins_append l r, List.append_assoc]

theorem modsAdmins_atomic : ∀ {l : List Admin}, AllAtomic l → modsAdmins l = []
  | [], _ => rfl
  | a :: l, h => by
      simp only [modsAdmins, modsAdmin_atomic (h a List.mem_cons_self),
        modsAdmins_atomic (fun b hb => h b (List.mem_cons_of_mem a hb)), List.append_nil]

@[simp] theorem modsAdmins_vals (vs : List Val) : modsAdmins (vals vs) = [] :=
  modsAdmins_atomic (allAtomic_vals vs)

@[simp] theorem modsAdmins_expression (es : List Instr) : modsAdmins (expression es) = [] :=
  modsAdmins_atomic ((allAtomic_expression es).mpr trivial)

@[simp] theorem modsAdmins_resultToAdmin (r : Result) : modsAdmins r.toAdmin = [] :=
  modsAdmins_atomic ((allAtomic_toAdmin r).mpr trivial)

/-- Every module instance of `c'` is one of `c`. -/
def ModsLe (c' c : Config H) : Prop := ∀ m ∈ mods c', m ∈ mods c

/-- An atomic successor with the same function instances and frame module. -/
theorem modsLe_of_atomic {c c' : Config H} (hF : c'.store.funcs = c.store.funcs)
    (hM : c'.frame.module = c.frame.module) (hA : AllAtomic c'.code) : ModsLe c' c := by
  intro m hm
  simp only [mods, modsAdmins_atomic hA, hF, hM, List.mem_append, List.mem_cons] at hm
  simp only [mods, List.mem_append, List.mem_cons]
  rcases hm with hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact absurd hm List.not_mem_nil

theorem mem_map_module_of {s s' : Store H} (h : ∀ fi ∈ s'.funcs, fi.module ∈ s.funcs.map FuncInst.module)
    {m : ModuleInst} (hm : m ∈ s'.funcs.map FuncInst.module) : m ∈ s.funcs.map FuncInst.module := by
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hm
  exact h fi hfi

theorem mem_map_module_get {s : Store H} {a : Nat} {fi : FuncInst H} (hf : s.funcs[a]? = some fi) :
    fi.module ∈ s.funcs.map FuncInst.module :=
  List.mem_map_of_mem (List.mem_of_getElem? hf)

theorem modsAdmin_toAdmin (v : Val) : modsAdmin v.toAdmin = [] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r <;> rfl

theorem mem_mods {s : Store H} {f : Frame} {is : List Admin} {m : ModuleInst} :
    m ∈ mods (⟨s, f, is⟩ : Config H) ↔
      m ∈ s.funcs.map FuncInst.module ∨ m = f.module ∨ m ∈ modsAdmins is := by
  simp only [mods, List.mem_append, List.mem_cons]

/-- A successor with the same function instances and frame module, and no frame in its code. -/
theorem modsLe_nil {c c' : Config H} (hF : c'.store.funcs = c.store.funcs)
    (hM : c'.frame.module = c.frame.module) (hC : modsAdmins c'.code = []) : ModsLe c' c := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  intro m hm
  rcases mem_mods.1 hm with hm | hm | hm
  · exact mem_mods.2 (.inl (hF ▸ hm))
  · exact mem_mods.2 (.inr (.inl (hM ▸ hm)))
  · simp only [hC, List.not_mem_nil] at hm

theorem modsLe_ctx {s s' : Store H} {f f' : Frame} {is is' pre post : List Admin}
    (ih : ModsLe (⟨s', f', is'⟩ : Config H) ⟨s, f, is⟩) :
    ModsLe (⟨s', f', pre ++ is' ++ post⟩ : Config H) ⟨s, f, pre ++ is ++ post⟩ := by
  intro m hm
  rcases mem_mods.1 hm with hm | hm | hm
  · rcases mem_mods.1 (ih m (mem_mods.2 (.inl hm))) with h | h | h
    · exact mem_mods.2 (.inl h)
    · exact mem_mods.2 (.inr (.inl h))
    · exact mem_mods.2 (.inr (.inr (by simp [modsAdmins_append, h])))
  · rcases mem_mods.1 (ih m (mem_mods.2 (.inr (.inl hm)))) with h | h | h
    · exact mem_mods.2 (.inl h)
    · exact mem_mods.2 (.inr (.inl h))
    · exact mem_mods.2 (.inr (.inr (by simp [modsAdmins_append, h])))
  · simp only [modsAdmins_append, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact mem_mods.2 (.inr (.inr (by simp [modsAdmins_append, hm])))
    · rcases mem_mods.1 (ih m (mem_mods.2 (.inr (.inr hm)))) with h | h | h
      · exact mem_mods.2 (.inl h)
      · exact mem_mods.2 (.inr (.inl h))
      · exact mem_mods.2 (.inr (.inr (by simp [modsAdmins_append, h])))
    · exact mem_mods.2 (.inr (.inr (by simp [modsAdmins_append, hm])))

theorem mods_label (s : Store H) (f : Frame) (n : Nat) (cont : List Instr) (is : List Admin) :
    mods (⟨s, f, [.label n cont is]⟩ : Config H) = mods ⟨s, f, is⟩ := by
  simp [mods, modsAdmins, modsAdmin]

theorem mods_handler (s : Store H) (f : Frame) (n : Nat) (cs : List Catch) (is : List Admin) :
    mods (⟨s, f, [.handler n cs is]⟩ : Config H) = mods ⟨s, f, is⟩ := by
  simp [mods, modsAdmins, modsAdmin]

theorem mem_mods_frame {s : Store H} {f fi : Frame} {n : Nat} {is : List Admin}
    {m : ModuleInst} :
    m ∈ mods (⟨s, f, [.frame n fi is]⟩ : Config H) ↔ m = f.module ∨ m ∈ mods ⟨s, fi, is⟩ := by
  simp only [mods, modsAdmins, modsAdmin, List.append_nil, List.mem_append, List.mem_cons]
  tauto

/-- **A Core step introduces no module instance**, for a host that invents none. -/
theorem mods_step_sub {P : Profile} {host : HostSemantics H} (hm : HostModsSub host)
    {c c' : Config H} (h : Step P host c c') : ModsLe c' c := by
  induction h with
  | parametric h => exact modsLe_of_atomic rfl rfl (parametricStep_atomic' h)
  | numeric h => exact modsLe_of_atomic rfl rfl (numericStep_atomic' h)
  | vector h => exact modsLe_of_atomic rfl rfl (vectorStep_atomic' h)
  | «variable» h =>
      exact modsLe_of_atomic (variableStep_funcs h).1 (variableStep_funcs h).2
        (variableStep_atomic' h)
  | table h =>
      exact modsLe_of_atomic (tableStep_funcs h).1 (tableStep_funcs h).2 (tableStep_atomic' h)
  | memory h =>
      exact modsLe_of_atomic (memoryStep_funcs h).1 (memoryStep_funcs h).2 (memoryStep_atomic' h)
  | reference h =>
      exact modsLe_of_atomic (refStep_funcs h).1 (refStep_funcs h).2 (refStep_atomic' h)
  | aggregate h =>
      exact modsLe_of_atomic (aggregateStep_funcs h).1 (aggregateStep_funcs h).2
        (aggregateStep_atomic' h)
  | ctxtInstrs _ _ ih => exact modsLe_ctx ih
  | ctxtLabel _ ih =>
      intro m hm'
      rw [mods_label] at hm' ⊢
      exact ih m hm'
  | ctxtHandler _ ih =>
      intro m hm'
      rw [mods_handler] at hm' ⊢
      exact ih m hm'
  | ctxtFrame _ ih =>
      intro m hm'
      rcases mem_mods_frame.1 hm' with h | h
      · exact mem_mods_frame.2 (.inl h)
      · exact mem_mods_frame.2 (.inr (ih m h))
  | callRefFunc hc hf =>
      intro m hm'
      rcases mem_mods.1 hm' with h | h | h
      · exact mem_mods.2 (.inl h)
      · exact mem_mods.2 (.inr (.inl h))
      · simp only [modsAdmins, modsAdmin, Frame.forCall, modsAdmins_expression, List.append_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h
        exact mem_mods.2 (.inl (h ▸ mem_map_module_get hf))
  | callRefHost hc _ _ _ _ hhost =>
      intro m hm'
      rcases mem_mods.1 hm' with h | h | h
      · exact mem_mods.2 (.inl (mem_map_module_of (hm _ _ _ _ _ hhost) h))
      · exact mem_mods.2 (.inr (.inl h))
      · simp at h
  | returnCallRefFrameAddr hc hf =>
      refine modsLe_nil rfl rfl ?_
      simp [modsAdmins_append, modsAdmins, modsAdmin_atomic (atomic_retToCallIn (atomic_of_isReturnCallRef hc) _), modsAdmin]
  | callRefNull hc =>
      refine modsLe_nil rfl rfl ?_
      simp [modsAdmins, modsAdmin]
  | callRefHostDiv hc =>
      exact modsLe_nil rfl rfl (by simp [modsAdmins_append, modsAdmins, modsAdmin,
        modsAdmin_atomic (atomic_of_isCallRef hc)])
  | returnCallRefLabel hc =>
      exact modsLe_nil rfl rfl (by simp [modsAdmins_append, modsAdmins,
        modsAdmin_atomic (atomic_of_isReturnCallRef hc)])
  | returnCallRefHandler hc =>
      exact modsLe_nil rfl rfl (by simp [modsAdmins_append, modsAdmins,
        modsAdmin_atomic (atomic_of_isReturnCallRef hc)])
  | brOnNonNullAddr =>
      exact modsLe_nil rfl rfl (by simp [modsAdmins, modsAdmin, modsAdmin_toAdmin])
  | brOnNullAddr =>
      exact modsLe_nil rfl rfl (by simp [modsAdmins, modsAdmin_toAdmin])
  | throw => exact modsLe_nil rfl rfl (by simp [modsAdmins, modsAdmin])
  | _ => exact modsLe_nil rfl rfl (by simp [modsAdmins_append, modsAdmins, modsAdmin])

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
