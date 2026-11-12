module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Strip.Fam

/-!
# Round 7: inverting `ExRel` at the shapes of Core's rules

Helpers for `Round7.exRel_step`: a configuration related to one whose code is a label, handler or
frame around an atomic prefix and an arbitrary rest has the same shape; function instances
related by `stripFI` agree on type and code; a call frame and `retToCallIn` depend on a module
only up to exports.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem allAtomic_append_iff {l r : List Admin} : AllAtomic (l ++ r) ↔ AllAtomic l ∧ AllAtomic r :=
  ⟨fun h => ⟨fun a ha => h a (List.mem_append_left _ ha), fun a ha => h a (List.mem_append_right _ ha)⟩,
    fun h => allAtomic_append h.1 h.2⟩

theorem allAtomic_cons_iff {a : Admin} {l : List Admin} :
    AllAtomic (a :: l) ↔ Atomic a ∧ AllAtomic l :=
  ⟨fun h => ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem _ hb)⟩,
    fun h => allAtomic_cons h.1 h.2⟩

theorem allAtomic_nil_iff : AllAtomic [] ↔ True := ⟨fun _ => trivial, fun _ => allAtomic_nil⟩

theorem allAtomic_vals_iff (vs : List Val) : AllAtomic (vals vs) ↔ True :=
  ⟨fun _ => trivial, fun _ => allAtomic_vals vs⟩

theorem atomic_of_isCallRef {c : Admin} (h : c.IsCallRef) : Atomic c := by
  cases c <;> simp_all [Admin.IsCallRef, Atomic]

theorem atomic_of_isReturnCallRef {c : Admin} (h : c.IsReturnCallRef) : Atomic c := by
  cases c <;> simp_all [Admin.IsReturnCallRef, Atomic]

theorem atomic_retToCallIn {c : Admin} (h : Atomic c) (m : ModuleInst) :
    Atomic (c.retToCallIn m) := by
  unfold Admin.retToCallIn
  split
  · split <;> exact True.intro
  · exact True.intro
  · exact h

theorem stripAdmins_length (l : List Admin) : (stripAdmins l).length = l.length := by
  simp [stripAdmins_eq_map]

theorem ne_nil_of_strip {l r : List Admin} (h : stripAdmins l = stripAdmins r) :
    l ≠ [] ↔ r ≠ [] := by
  have hl : l.length = r.length := by
    simpa only [stripAdmins_length] using congrArg List.length h
  rw [Ne, Ne, ← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hl]

theorem stripAdmins_eq_nil {l : List Admin} (h : stripAdmins l = stripAdmins []) : l = [] := by
  cases l <;> simp_all

/-- Split a related sequence along an append. -/
theorem stripAdmins_eq_append {js l r : List Admin} (h : stripAdmins js = stripAdmins (l ++ r)) :
    ∃ jl jr, js = jl ++ jr ∧ stripAdmins jl = stripAdmins l ∧ stripAdmins jr = stripAdmins r := by
  rw [stripAdmins_append, stripAdmins_eq_map, stripAdmins_eq_map, stripAdmins_eq_map] at h
  obtain ⟨jl, jr, rfl, hl, hr⟩ := List.map_eq_append_iff.mp h
  exact ⟨jl, jr, rfl, by rw [stripAdmins_eq_map, hl, stripAdmins_eq_map],
    by rw [stripAdmins_eq_map, hr, stripAdmins_eq_map]⟩

/-- A related label around an atomic prefix. -/
theorem inv_label {js l r : List Admin} {n : Nat} {cont : List Instr} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.label n cont (l ++ r)]) :
    ∃ r', js = [.label n cont (l ++ r')] ∧ stripAdmins r' = stripAdmins r := by
  obtain ⟨b, rfl, hb⟩ := stripAdmins_eq_singleton h
  obtain ⟨body, rfl, hbody⟩ := stripAdmin_eq_label hb
  obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append r hl hbody
  exact ⟨r', rfl, hr'⟩

/-- A related handler around an atomic prefix. -/
theorem inv_handler {js l r : List Admin} {n : Nat} {cs : List Catch} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.handler n cs (l ++ r)]) :
    ∃ r', js = [.handler n cs (l ++ r')] ∧ stripAdmins r' = stripAdmins r := by
  obtain ⟨b, rfl, hb⟩ := stripAdmins_eq_singleton h
  obtain ⟨body, rfl, hbody⟩ := stripAdmin_eq_handler hb
  obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append r hl hbody
  exact ⟨r', rfl, hr'⟩

/-- A related frame around an atomic prefix. -/
theorem inv_frame {js l r : List Admin} {n : Nat} {fi : Frame} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.frame n fi (l ++ r)]) :
    ∃ fi' r', js = [.frame n fi' (l ++ r')] ∧ stripFrame fi' = stripFrame fi ∧
      stripAdmins r' = stripAdmins r := by
  obtain ⟨b, rfl, hb⟩ := stripAdmins_eq_singleton h
  obtain ⟨fi', body, rfl, hfi, hbody⟩ := stripAdmin_eq_frame hb
  obtain ⟨r', rfl, hr'⟩ := stripAdmins_eq_atomic_append r hl hbody
  exact ⟨fi', r', rfl, hfi, hr'⟩

theorem inv_label0 {js l : List Admin} {n : Nat} {cont : List Instr} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.label n cont l]) : js = [.label n cont l] := by
  obtain ⟨r', h₁, h₂⟩ := inv_label (r := []) hl (by simpa using h)
  rw [h₁, stripAdmins_eq_nil h₂, List.append_nil]

theorem inv_handler0 {js l : List Admin} {n : Nat} {cs : List Catch} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.handler n cs l]) : js = [.handler n cs l] := by
  obtain ⟨r', h₁, h₂⟩ := inv_handler (r := []) hl (by simpa using h)
  rw [h₁, stripAdmins_eq_nil h₂, List.append_nil]

theorem inv_frame0 {js l : List Admin} {n : Nat} {fi : Frame} (hl : AllAtomic l)
    (h : stripAdmins js = stripAdmins [.frame n fi l]) :
    ∃ fi', js = [.frame n fi' l] ∧ stripFrame fi' = stripFrame fi := by
  obtain ⟨fi', r', h₁, hfi, h₂⟩ := inv_frame (r := []) hl (by simpa using h)
  exact ⟨fi', by rw [h₁, stripAdmins_eq_nil h₂, List.append_nil], hfi⟩

/-- A function instance at a related store: same type, same code, same module up to exports. -/
theorem stripFI_get {F G : List (FuncInst H)} (h : F.map stripFI = G.map stripFI) {a : Nat}
    {fi : FuncInst H} (hfi : G[a]? = some fi) :
    ∃ fi', F[a]? = some fi' ∧ fi'.type = fi.type ∧ fi'.code = fi.code ∧
      stripModule fi'.module = stripModule fi.module := by
  have h' := congrArg (fun l => l[a]?) h
  simp only [List.getElem?_map, hfi, Option.map_some] at h'
  obtain ⟨fi', hfi', he⟩ := Option.map_eq_some_iff.mp h'
  refine ⟨fi', hfi', ?_, ?_, ?_⟩
  · have ht : (stripFI fi').type = (stripFI fi).type := by rw [he]
    exact ht
  · have hc : (stripFI fi').code = (stripFI fi).code := by rw [he]
    exact hc
  · have hm : (stripFI fi').module = (stripFI fi).module := by rw [he]
    exact hm

theorem types_of_stripModule {m m' : ModuleInst} (h : stripModule m = stripModule m') :
    m.types = m'.types := by
  have ht : (stripModule m).types = (stripModule m').types := by rw [h]
  exact ht

theorem stripFrame_forCall {m m' : ModuleInst} (h : stripModule m = stripModule m')
    (args : List Val) (ls : List ValType) :
    stripFrame (Frame.forCall m args ls) = stripFrame (Frame.forCall m' args ls) := by
  simp only [stripFrame, Frame.forCall, types_of_stripModule h, h]

theorem retToCallIn_strip {m m' : ModuleInst} (h : stripModule m = stripModule m') (c : Admin) :
    c.retToCallIn m = c.retToCallIn m' := by
  unfold Admin.retToCallIn
  rw [types_of_stripModule h]

theorem stripModule_frame {f f' : Frame} (h : stripFrame f = stripFrame f') :
    stripModule f.module = stripModule f'.module := congrArg (fun g : Frame => g.module) h

theorem stripStore_addExn {s : Store H} {F : List (FuncInst H)}
    (hF : F.map stripFI = s.funcs.map stripFI) (e : ExnInst) :
    stripStore (s.addExn e) = stripStore ({ s with funcs := F }.addExn e) := by
  simp only [stripStore_eq, Store.addExn, hF]

/-- `ExRel` with the normal form's store and frame. -/
theorem exRel_nfc {s : Store H} {f : Frame} {F : List (FuncInst H)}
    (hF : F.map stripFI = s.funcs.map stripFI) (E : List ExportInst) {l l' : List Admin}
    (hc : stripAdmins l = stripAdmins l') :
    ExRel ⟨s, f, l⟩ ⟨{ s with funcs := F }, { f with module := { f.module with exports := E } }, l'⟩ :=
  exRel_mk (stripStore_withFuncs s hF).symm (stripFrame_withEx f E).symm hc

/-- The components of `ExRel`. -/
theorem exRel_parts {c d : Config H} (h : ExRel c d) :
    stripStore c.store = stripStore d.store ∧ stripFrame c.frame = stripFrame d.frame ∧
      stripAdmins c.code = stripAdmins d.code := by
  simp only [ExRel, stripConfig, Config.mk.injEq] at h
  exact h

end Silmaril.Wasm.SpecTec.Sim.Round7
