module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Inv

/-!
# Round 7: export-free configurations, helpers

Facts used by `stripped_step` (`Raw/…/Round7/Strip/Pres.lean`): the families' successors are
atomic, stripping is idempotent, and the successor of a family step from an export-free
configuration is export-free (`stripped_fam`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem allAtomic_map_ref (rs : List Ref) : AllAtomic (rs.map .ref) ↔ True :=
  ⟨fun _ => trivial, fun _ a ha => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    exact True.intro⟩

theorem allAtomic_take {l : List Admin} (h : AllAtomic l) (n : Nat) : AllAtomic (l.take n) :=
  fun a ha => h a (List.mem_of_mem_take ha)

theorem allAtomic_drop {l : List Admin} (h : AllAtomic l) (n : Nat) : AllAtomic (l.drop n) :=
  fun a ha => h a (List.mem_of_mem_drop ha)

theorem allAtomic_expression (es : List Instr) : AllAtomic (expression es) ↔ True :=
  ⟨fun _ => trivial, fun _ a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact True.intro⟩

theorem allAtomic_toAdmin (r : Result) : AllAtomic r.toAdmin ↔ True :=
  ⟨fun _ => trivial, fun _ => by
    cases r with
    | values vs => exact allAtomic_vals vs
    | throw a => exact allAtomic_cons True.intro (allAtomic_cons True.intro allAtomic_nil)
    | trap => exact allAtomic_cons True.intro allAtomic_nil⟩

attribute [local simp] atomic_toAdmin atomic_plain atomic_ref atomic_trap atomic_constI32
  atomic_callRefType atomic_returnCallRefType allAtomic_append_iff allAtomic_cons_iff
  allAtomic_nil_iff allAtomic_vals_iff allAtomic_map_ref allAtomic_expression

/-! ## The families' successors are atomic -/

theorem parametricStep_atomic' {is is' : List Admin} (h : ParametricStep is is') :
    AllAtomic is' := by
  cases h <;> simp

theorem numericStep_atomic' {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    AllAtomic is' := by
  cases h <;> simp

theorem vectorStep_atomic' {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    AllAtomic is' := by
  cases h <;> simp

theorem variableStep_atomic' {c c' : Config H} (h : VariableStep c c') : AllAtomic c'.code := by
  cases h <;> simp

theorem tableStep_atomic' {P : Profile} {c c' : Config H} (h : TableStep P c c') :
    AllAtomic c'.code := by
  cases h <;> simp

theorem memoryStep_atomic' {P : Profile} {c c' : Config H} (h : MemoryStep P c c') :
    AllAtomic c'.code := by
  cases h <;> simp [store8, load8u]

theorem aggregateStep_atomic' {c c' : Config H} (h : AggregateStep c c') : AllAtomic c'.code := by
  cases h <;> simp
  exact allAtomic_take (allAtomic_drop ((allAtomic_map_ref _).mpr trivial) _) _

theorem refStep_atomic' {c c' : Config H} (h : RefStep c c') : AllAtomic c'.code := by
  cases h <;> simp

/-! ## Export-free configurations -/

theorem stripModule_stripModule (m : ModuleInst) : stripModule (stripModule m) = stripModule m :=
  rfl

theorem stripped_iff {s : Store H} {f : Frame} {is : List Admin} :
    Stripped ⟨s, f, is⟩ ↔ stripStore s = s ∧ stripFrame f = f ∧ stripAdmins is = is := by
  simp only [Stripped, stripConfig, Config.mk.injEq]

theorem stripped_mk {s : Store H} {f : Frame} {is : List Admin} (hs : stripStore s = s)
    (hf : stripFrame f = f) (hc : stripAdmins is = is) : Stripped ⟨s, f, is⟩ :=
  stripped_iff.mpr ⟨hs, hf, hc⟩

theorem stripStore_stripStore (s : Store H) : stripStore (stripStore s) = stripStore s := by
  simp only [stripStore_eq, List.map_map]
  rfl

theorem stripFrame_stripFrame (f : Frame) : stripFrame (stripFrame f) = stripFrame f := rfl

mutual
theorem stripAdmin_stripAdmin : ∀ a : Admin, stripAdmin (stripAdmin a) = stripAdmin a
  | .label n cont body => by simp only [stripAdmin, stripAdmins_stripAdmins body]
  | .handler n cs body => by simp only [stripAdmin, stripAdmins_stripAdmins body]
  | .frame n f body => by simp only [stripAdmin, stripFrame_stripFrame, stripAdmins_stripAdmins body]
  | .plain _ | .ref _ | .callRefType _ | .returnCallRefType _ | .trap => rfl

theorem stripAdmins_stripAdmins : ∀ l : List Admin, stripAdmins (stripAdmins l) = stripAdmins l
  | [] => rfl
  | a :: l => by simp only [stripAdmins_cons, stripAdmin_stripAdmin a, stripAdmins_stripAdmins l]
end

theorem stripped_stripConfig (c : Config H) : Stripped (stripConfig c) := by
  simp only [Stripped, stripConfig, stripStore_stripStore, stripFrame_stripFrame,
    stripAdmins_stripAdmins]

theorem exRel_stripConfig (c : Config H) : ExRel c (stripConfig c) := by
  simp only [ExRel, stripConfig, stripStore_stripStore, stripFrame_stripFrame,
    stripAdmins_stripAdmins]

/-- Related export-free configurations are equal. -/
theorem eq_of_exRel_stripped {c d : Config H} (h : ExRel c d) (hc : Stripped c)
    (hd : Stripped d) : c = d := by
  rw [← hc, ← hd]
  exact h

/-- The function instances of an export-free store are export-free. -/
theorem stripFI_of_stripped {s : Store H} (hs : stripStore s = s) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : stripModule fi.module = fi.module := by
  have h' : (stripStore s).funcs[a]? = some fi := by rw [hs]; exact h
  simp only [stripStore_eq, List.getElem?_map, h, Option.map_some, Option.some.injEq] at h'
  rw [← h']
  rfl

/-- A family successor of an export-free configuration is export-free. -/
theorem stripped_fam {c c' : Config H} (hc : Stripped c)
    (hfun : c'.store.funcs = c.store.funcs) (hmod : c'.frame.module = c.frame.module)
    (hat : AllAtomic c'.code) : Stripped c' := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', is'⟩ := c'
  obtain ⟨hs, hf, -⟩ := stripped_iff.mp hc
  refine stripped_mk ?_ ?_ (stripAdmins_atomic hat)
  · have hF : s.funcs.map stripFI = s.funcs := congrArg Store.funcs hs
    simp only at hfun
    rw [stripStore_eq, hfun, hF]
    rw [← hfun]
  · have hm : stripModule f.module = f.module := congrArg Frame.module hf
    simp only at hmod
    simp only [stripFrame, hmod, hm]
    rw [← hmod]

theorem stripAdmins_append_eq {l r : List Admin} (h : stripAdmins (l ++ r) = l ++ r) :
    stripAdmins l = l ∧ stripAdmins r = r := by
  rw [stripAdmins_append] at h
  exact List.append_inj h (stripAdmins_length l)

theorem stripAdmins_label_eq {n : Nat} {cont : List Instr} {body : List Admin}
    (h : stripAdmins [.label n cont body] = [.label n cont body]) : stripAdmins body = body := by
  simpa [stripAdmin] using h

theorem stripAdmins_handler_eq {n : Nat} {cs : List Catch} {body : List Admin}
    (h : stripAdmins [.handler n cs body] = [.handler n cs body]) : stripAdmins body = body := by
  simpa [stripAdmin] using h

theorem stripAdmins_frame_eq {n : Nat} {fi : Frame} {body : List Admin}
    (h : stripAdmins [.frame n fi body] = [.frame n fi body]) :
    stripFrame fi = fi ∧ stripAdmins body = body := by
  simpa [stripAdmin] using h

theorem stripStore_addExn_eq {s : Store H} (hs : stripStore s = s) (e : ExnInst) :
    stripStore (s.addExn e) = s.addExn e := by
  have hF : s.funcs.map stripFI = s.funcs := congrArg Store.funcs hs
  simp only [stripStore_eq, Store.addExn, hF]

theorem stripFrame_forCall_eq {m : ModuleInst} (hm : stripModule m = m) (args : List Val)
    (ls : List ValType) : stripFrame (Frame.forCall m args ls) = Frame.forCall m args ls := by
  simp only [stripFrame, Frame.forCall, hm]

theorem stripAdmins_label_atomic {n : Nat} {cont : List Instr} {body : List Admin}
    (h : AllAtomic body) : stripAdmins [.label n cont body] = [.label n cont body] := by
  simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, stripAdmins_atomic h]

theorem stripAdmins_handler_atomic {n : Nat} {cs : List Catch} {body : List Admin}
    (h : AllAtomic body) : stripAdmins [.handler n cs body] = [.handler n cs body] := by
  simp only [stripAdmins_cons, stripAdmins_nil, stripAdmin, stripAdmins_atomic h]

end Silmaril.Wasm.SpecTec.Sim.Round7
