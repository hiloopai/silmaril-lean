module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PBCommon

@[expose] public section

/-! # Step simulation: local and global variable head rules

`local.get`, `local.set`, `global.get`, `global.set` are each one Core
`VariableStep`. Lime1 frame locals are `some (toCore v)` in Core; a Lime1
`global.set` retypes the global, which `Store.erase`/`GlobalInst.erase` absorbs.
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

theorem var_erase_value (g : Silmaril.Wasm.Execution.Core.GlobalInst) :
    (ToCore.GlobalInst.erase g).value = g.value := by
  unfold ToCore.GlobalInst.erase; split <;> rfl

theorem var_erase_mut (g : Silmaril.Wasm.Execution.Core.GlobalInst) :
    (ToCore.GlobalInst.erase g).type.mutability = g.type.mutability := by
  unfold ToCore.GlobalInst.erase; split <;> rfl

theorem var_locals {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    cf.locals = f.locals.map (some ∘ Value.toCore) :=
  congrArg Silmaril.Wasm.Execution.Core.Frame.locals (pb_frameEq hs)

theorem var_globals {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H} {cf : CFrame}
    {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    cf.module.globals = f.module.globals.map Addr.value :=
  congrArg (fun fr => fr.module.globals) (pb_frameEq hs)

theorem var_storeGlobals {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H}
    {cf : CFrame} {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    cs.globals.map ToCore.GlobalInst.erase = s.globals.map GlobalInst.toCore :=
  congrArg Silmaril.Wasm.Execution.Core.Store.globals (pb_storeEq hs)

/-- The Core global behind a Lime1 global lookup. -/
theorem var_global {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {code : List Admin} {cs : CStore H}
    {cf : CFrame} {cl : List CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩)
    {i : GlobalIdx} {a : GlobalAddr} {g : GlobalInst}
    (index : f.module.globals[i.toNat]? = some a) (found : s.globals[a.value]? = some g) :
    ∃ g0, cs.global? cf i = some (a.value, g0) ∧ cs.globals[a.value]? = some g0 ∧
      ToCore.GlobalInst.erase g0 = g.toCore := by
  have hm := congrArg (·[a.value]?) (var_storeGlobals hs)
  simp only [List.getElem?_map, found, Option.map_some] at hm
  obtain ⟨g0, hg0, he⟩ := Option.map_eq_some_iff.mp hm
  refine ⟨g0, ?_, hg0, he⟩
  simp [Silmaril.Wasm.Execution.Core.Store.global?, var_globals hs, index, hg0]

theorem localGet {tgt : ToCore.CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {i : LocalIdx}
    {v : Value} (found : f.locals[i.toNat]? = some v) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [.source (.localGet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value v]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hl := var_locals hs
  refine pb_finish_same hs (by simp) (by simp) ?_
  pb_norm
  exact .variable (.localGet (by simp [Silmaril.Wasm.Execution.Core.Frame.local?, hl, found]))

theorem localSet {tgt : ToCore.CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {i : LocalIdx}
    {v old : Value} (found : f.locals[i.toNat]? = some old) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value v, .source (.localSet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, {f with locals := f.locals.set i.toNat v}, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  have hl := var_locals hs
  have hfr := pb_frameEq hs
  have hb : i.toNat < cf.locals.length := by
    rw [hl, List.length_map]; exact (List.getElem?_eq_some_iff.mp found).1
  refine pb_finish (s' := s) (cf' := cf.setLocal i v.toCore) (after := []) hs (by simp) ?_
    (pb_storeEq hs) ?_ ⟨hs.2.1, hs.2.2.1, by simp⟩
  · pb_norm
    exact .variable (.localSet hb)
  · rw [show ToCore.Frame.erase (cf.setLocal i v.toCore) =
        { ToCore.Frame.erase cf with locals := cf.locals.set i.toNat (some v.toCore) } from rfl,
      hfr, hl]
    simp [Silmaril.Wasm.Execution.Runtime.Frame.toCore, List.map_set]

theorem globalGet {tgt : ToCore.CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {i : GlobalIdx}
    {a : GlobalAddr} {g : GlobalInst} (index : f.module.globals[i.toNat]? = some a)
    (found : s.globals[a.value]? = some g) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [.source (.globalGet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value g.value]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨g0, hget, -, he⟩ := var_global hs index found
  have hv : g0.value = g.value.toCore := by
    rw [← var_erase_value, he]; rfl
  refine pb_finish_same hs (by simp) (by simp) ?_
  pb_norm
  rw [← hv]
  exact .variable (.globalGet hget)

theorem var_setGlobal_erase (cs : CStore H) (n : Nat) (w : CVal) :
    ToCore.Store.erase (cs.setGlobal n w) =
      { ToCore.Store.erase cs with
        globals := (cs.globals.modify n fun g => { g with value := w }).map
          ToCore.GlobalInst.erase } := rfl

theorem var_setGlobal_toCore (s : Silmaril.Wasm.Execution.Runtime.Store H) (a : GlobalAddr) (g : GlobalInst) :
    (setGlobal s a g).toCore =
      { s.toCore with globals := List.map GlobalInst.toCore (s.globals.set a.value g) } := rfl

theorem globalSet {tgt : ToCore.CHostSemantics H} {s : Silmaril.Wasm.Execution.Runtime.Store H} {f : Frame} {i : GlobalIdx}
    {a : GlobalAddr} {g : GlobalInst} {v : Value} (index : f.module.globals[i.toNat]? = some a)
    (found : s.globals[a.value]? = some g) (_mutable : g.mutability = .var)
    {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value v, .source (.globalSet i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨setGlobal s a { g with value := v }, f, []⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨g0, hget, hg0, he⟩ := var_global hs index found
  have hmap := var_storeGlobals hs
  have hst := pb_storeEq hs
  have hmut : g0.type.mutability = g.mutability := by
    rw [← var_erase_mut, he]; rfl
  refine pb_finish (s' := setGlobal s a { g with value := v }) (f' := f)
    (cs' := cs.setGlobal a.value v.toCore) (cf' := cf) (after := []) hs (by simp) ?_ ?_
    (pb_frameEq hs) ⟨hs.2.1, hs.2.2.1, by simp⟩
  · pb_norm
    exact .variable (.globalSet hget)
  · rw [var_setGlobal_erase, hst, var_setGlobal_toCore]
    suffices hG : (cs.globals.modify a.value fun g => { g with value := v.toCore }).map
        ToCore.GlobalInst.erase = (s.globals.set a.value { g with value := v }).map
        GlobalInst.toCore by rw [hG]
    apply List.ext_getElem?
    intro j
    have hj := congrArg (·[j]?) hmap
    simp only [List.getElem?_map] at hj ⊢
    rw [List.getElem?_modify, List.getElem?_set]
    by_cases hjn : a.value = j
    · subst hjn
      simp [hg0, ToCore.GlobalInst.erase, GlobalInst.toCore, Value.toCore, hmut]
      exact (List.getElem?_eq_some_iff.mp found).1
    · simp [hjn, hj]

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
