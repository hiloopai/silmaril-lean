module

public import Silmaril.Proofs.Wasm.LimeCompile.Select.Inv

/-!
# Erasing `select` annotations: the reduction families

The state families of Core 3.0 (`VariableStep`, `TableStep`, `MemoryStep`, `RefStep`,
`AggregateStep`) neither change nor read the code of function instances: a step stays a step
when the store's functions are replaced by others of the same types, and the functions are
unchanged by the step. Their redexes, like those of the pure families other than `select`, are
rigid.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Select

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.LimeCompile.Select

variable {H : Type} {P : Profile}

theorem variableStep_funcs {c c' : Config H} (h : VariableStep c c') (Fs : List (FuncInst H)) :
    VariableStep (H := H) ⟨{c.store with funcs := Fs}, c.frame, c.code⟩
        ⟨{c'.store with funcs := Fs}, c'.frame, c'.code⟩ ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> exact ⟨by constructor <;> assumption, rfl⟩

theorem tableStep_funcs {c c' : Config H} (h : TableStep P c c') (Fs : List (FuncInst H)) :
    TableStep P ⟨{c.store with funcs := Fs}, c.frame, c.code⟩
        ⟨{c'.store with funcs := Fs}, c'.frame, c'.code⟩ ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> exact ⟨by constructor <;> assumption, rfl⟩

theorem memoryStep_funcs {c c' : Config H} (h : MemoryStep P c c') (Fs : List (FuncInst H)) :
    MemoryStep P ⟨{c.store with funcs := Fs}, c.frame, c.code⟩
        ⟨{c'.store with funcs := Fs}, c'.frame, c'.code⟩ ∧ c'.store.funcs = c.store.funcs := by
  cases h <;> exact ⟨by constructor <;> assumption, rfl⟩

theorem aggregateStep_funcs {c c' : Config H} (h : AggregateStep c c') (Fs : List (FuncInst H)) :
    AggregateStep (H := H) ⟨{c.store with funcs := Fs}, c.frame, c.code⟩
        ⟨{c'.store with funcs := Fs}, c'.frame, c'.code⟩ ∧ c'.store.funcs = c.store.funcs := by
  cases h with
  | arrayCopyOob₂ ha h => exact ⟨.arrayCopyOob₂ ha h, rfl⟩
  | arrayInitElemOob₂ he h => exact ⟨.arrayInitElemOob₂ he h, rfl⟩
  | arrayInitDataOob₂ hd he hdat hz h => exact ⟨.arrayInitDataOob₂ hd he hdat hz h, rfl⟩
  | _ => exact ⟨by constructor! <;> assumption, rfl⟩


/-! ## Stores -/

theorem selFI_type (fi : FuncInst H) : (selFI fi).type = fi.type := rfl

theorem selS_eq {s t : Store H} (h : selS s = selS t) :
    t = { s with funcs := t.funcs } ∧ t.funcs.map selFI = s.funcs.map selFI := by
  rcases s with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases t with ⟨_, _, _, _, _, _, _, _, _, _⟩
  simp only [selS, Store.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, hf, rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, hf.symm⟩

theorem selS_with {s t s' : Store H} (h : selS s = selS t) (hs' : s'.funcs = s.funcs) :
    selS s' = selS { s' with funcs := t.funcs } := by
  have hf : t.funcs.map selFI = s.funcs.map selFI := (selS_eq h).2
  simp only [selS, hf, hs']

theorem types_eq_of_selS {s t : Store H} (h : selS s = selS t) :
    t.funcs.map FuncInst.type = s.funcs.map FuncInst.type := by
  have hf : t.funcs.map selFI = s.funcs.map selFI := (selS_eq h).2
  have h' := congrArg (List.map FuncInst.type) hf
  simpa only [List.map_map, Function.comp_def, selFI_type] using h'

theorem funcs_get_of_selS {s t : Store H} (h : selS s = selS t) {a : Nat} {fi : FuncInst H}
    (hf : s.funcs[a]? = some fi) : ∃ fi', t.funcs[a]? = some fi' ∧ selFI fi' = selFI fi := by
  have hm : t.funcs.map selFI = s.funcs.map selFI := (selS_eq h).2
  have h' : (t.funcs.map selFI)[a]? = some (selFI fi) := by
    rw [hm, List.getElem?_map, hf]; rfl
  rw [List.getElem?_map] at h'
  cases ht : t.funcs[a]? with
  | none => rw [ht] at h'; cases h'
  | some fi' => rw [ht] at h'; exact ⟨fi', rfl, Option.some.inj h'⟩

theorem selFI_eq {fi fi' : FuncInst H} (h : selFI fi' = selFI fi) :
    fi'.type = fi.type ∧ fi'.module = fi.module ∧
      (∀ code, fi.code = .wasm code → ∃ code', fi'.code = .wasm code' ∧
        code'.locals = code.locals ∧ selL code'.body = selL code.body) ∧
      (∀ hh, fi.code = .host hh → fi'.code = .host hh) := by
  rcases fi with ⟨ty, m, code | hh⟩ <;> rcases fi' with ⟨ty', m', code' | hh'⟩ <;>
    simp only [selFI, selFn, FuncInst.mk.injEq, FuncCode.wasm.injEq, FuncCode.host.injEq,
      reduceCtorEq, and_false] at h
  · obtain ⟨rfl, rfl, h⟩ := h
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro c hc
      cases hc
      exact ⟨code', rfl, (Declaration.Func.mk.inj h).2.1, (Declaration.Func.mk.inj h).2.2⟩
    · intro _ hc
      cases hc
  · obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro _ hc
      cases hc
    · intro _ hc
      exact hc

theorem refOk_funcs {s : Store H} {Fs : List (FuncInst H)}
    (hF : Fs.map FuncInst.type = s.funcs.map FuncInst.type) {r : Ref} {rt : CRefType}
    (h : RefOk s r rt) : RefOk { s with funcs := Fs } r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct ha => exact .struct ha
  | array ha => exact .array ha
  | exn ha => exact .exn ha
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs
  | @func a fi ha =>
    have h' : (Fs.map FuncInst.type)[a]? = some fi.type := by
      rw [hF, List.getElem?_map, ha]; rfl
    rw [List.getElem?_map] at h'
    cases hFa : Fs[a]? with
    | none => rw [hFa] at h'; cases h'
    | some fi' =>
      rw [hFa] at h'
      rw [← Option.some.inj h']
      exact .func hFa

theorem refOk_funcs_iff {s : Store H} {Fs : List (FuncInst H)}
    (hF : Fs.map FuncInst.type = s.funcs.map FuncInst.type) {r : Ref} {rt : CRefType} :
    RefOk { s with funcs := Fs } r rt ↔ RefOk s r rt :=
  ⟨fun h => refOk_funcs (s := { s with funcs := Fs }) (Fs := s.funcs) hF.symm h,
    refOk_funcs hF⟩

theorem refStep_funcs {c c' : Config H} (h : RefStep c c') {Fs : List (FuncInst H)}
    (hF : Fs.map FuncInst.type = c.store.funcs.map FuncInst.type) :
    RefStep (H := H) ⟨{c.store with funcs := Fs}, c.frame, c.code⟩
        ⟨{c'.store with funcs := Fs}, c'.frame, c'.code⟩ ∧ c'.store.funcs = c.store.funcs := by
  cases h with
  | testTrue h => exact ⟨.testTrue ((refOk_funcs_iff hF).mpr h), rfl⟩
  | testFalse h => exact ⟨.testFalse (fun h' => h ((refOk_funcs_iff hF).mp h')), rfl⟩
  | castSucceed h => exact ⟨.castSucceed ((refOk_funcs_iff hF).mpr h), rfl⟩
  | castFail h => exact ⟨.castFail (fun h' => h ((refOk_funcs_iff hF).mp h')), rfl⟩
  | refFunc h => exact ⟨.refFunc h, rfl⟩
  | isNullFalse h => exact ⟨.isNullFalse h, rfl⟩
  | asNonNullAddr h => exact ⟨.asNonNullAddr h, rfl⟩
  | eqTrue h => exact ⟨.eqTrue h, rfl⟩
  | eqFalse h => exact ⟨.eqFalse h, rfl⟩
  | externConvertAddr h => exact ⟨.externConvertAddr h, rfl⟩
  | _ => exact ⟨by constructor!, rfl⟩

/-! ## Rigid redexes -/

/-- Every instruction of a list is rigid. -/
def AllRig (L : List Admin) : Prop := ∀ a ∈ L, Rig a

theorem allRig_nil : AllRig [] := fun _ h => nomatch h

theorem allRig_cons {a : Admin} {L : List Admin} (ha : Rig a) (hL : AllRig L) :
    AllRig (a :: L) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  · exact hL x hx

theorem allRig_append {L L' : List Admin} (hL : AllRig L) (hL' : AllRig L') :
    AllRig (L ++ L') := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · exact hL' x hx

theorem allRig_vals (vs : List Val) : AllRig (vals vs) := rig_vals vs

theorem rig_frame {n : Nat} {f : Frame} {B : List Admin} (hB : AllRig B) :
    Rig (.frame n f B) := by
  intro b hb
  obtain ⟨B', rfl, hB'⟩ := selA_eq_frame hb
  rw [eq_of_selAs_rig hB hB']

theorem rig_handler {n : Nat} {cs : List Catch} {B : List Admin} (hB : AllRig B) :
    Rig (.handler n cs B) := by
  intro b hb
  obtain ⟨B', rfl, hB'⟩ := selA_eq_handler hb
  rw [eq_of_selAs_rig hB hB']

theorem rig_isCallRef {c : Admin} (hc : c.IsCallRef) : Rig c := by
  cases c with
  | plain i =>
    cases i <;> first | exact hc.elim | exact rig_plain (flat_mk rfl fun _ h => nomatch h)
  | callRefType d => exact rig_callRefType d
  | _ => exact hc.elim

theorem rig_isReturnCallRef {c : Admin} (hc : c.IsReturnCallRef) : Rig c := by
  cases c with
  | plain i =>
    cases i <;> first | exact hc.elim | exact rig_plain (flat_mk rfl fun _ h => nomatch h)
  | returnCallRefType d => exact rig_returnCallRefType d
  | _ => exact hc.elim

theorem rig_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    selA (c.retToCallIn m) = c.retToCallIn m := by
  cases c with
  | plain i =>
    cases i <;> first | exact hc.elim | (simp only [Admin.retToCallIn]; split <;> rfl)
  | returnCallRefType d => rfl
  | _ => exact hc.elim

end Silmaril.Proofs.Wasm.LimeCompile.Select
