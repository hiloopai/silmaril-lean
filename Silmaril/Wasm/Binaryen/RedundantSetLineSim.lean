module

public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.CodeSimClosed
public import Silmaril.Wasm.Binaryen.Pass.RedundantSetLine

@[expose] public section

namespace Silmaril.Wasm.Binaryen.RedundantSetLine

open Execution.Core Execution.Core.Sim Validation Numerics
variable {H : Type} {P : Profile}

/-- Rewritten and original instruction segments. -/
inductive rsBI : List Instr → List Instr → Prop where
  | set (x : LocalIdx) : rsBI [.localGet x, .drop] [.localGet x, .localSet x]
  | tee (x : LocalIdx) : rsBI [.localGet x] [.localGet x, .localTee x]

/-- The extra drop pair is the intermediate state after reading a self store. -/
inductive rsB : List Admin → List Admin → Prop where
  | set (x : LocalIdx) : rsB [.plain (.localGet x), .plain .drop]
      [.plain (.localGet x), .plain (.localSet x)]
  | tee (x : LocalIdx) : rsB [.plain (.localGet x)]
      [.plain (.localGet x), .plain (.localTee x)]
  | drop (v : Val) : rsB [v.toAdmin, .plain .drop] []

/-- Storing the current value leaves the entire frame unchanged. -/
theorem setLocal_self {f : Frame} {x : LocalIdx} {v : Val}
    (h : f.local? x = some (some v)) : f.setLocal x v = f := by
  obtain ⟨hx, hv⟩ := List.getElem?_eq_some_iff.mp h
  have he : f.locals.set x.toNat (some v) = f.locals := by
    rw [← hv, List.set_getElem_self]
  cases f
  simp_all [Frame.setLocal]

/-- Invert a local read at the active head. -/
theorem get_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {x : LocalIdx}
    {rest es' : List Admin}
    (h : Step P closedHost ⟨s, f, vals vs ++ .plain (.localGet x) :: rest⟩ ⟨s', f', es'⟩) :
    ∃ v, f.local? x = some (some v) ∧ s' = s ∧ f' = f ∧
      es' = vals vs ++ v.toAdmin :: rest := by
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨rfl, v, hv, rfl⟩ := GuardSim.head_localGet hh
  simp only [List.append_nil] at hW
  subst hW
  simp only [Config.mk.injEq] at hc
  exact ⟨v, hv, by simpa using hc⟩

/-- A read followed by a self store executes without changing the frame. -/
theorem run_self_set {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.local? x = some (some v)) (vs : List Val) (rest : List Admin) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, vals vs ++ [.plain (.localGet x), .plain (.localSet x)] ++ rest⟩
      ⟨s, f, vals vs ++ rest⟩ := by
  have hx := (List.getElem?_eq_some_iff.mp hv).1
  have h1 := Step.append_right (Step.vals_left
    (Step.variable (P := P) (host := closedHost) (VariableStep.localGet (s := s) hv)) vs)
    (.plain (.localSet x) :: rest)
  have h2 := Step.append_right (Step.vals_left
    (Step.variable (P := P) (host := closedHost)
      (VariableStep.localSet (s := s) (v := v) hx)) vs) rest
  rw [setLocal_self hv] at h2
  exact .tail (.single (by simpa using h1)) (by simpa using h2)

/-- A self tee also leaves the value on the stack. -/
theorem run_self_tee {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hv : f.local? x = some (some v)) (vs : List Val) (rest : List Admin) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, vals vs ++ [.plain (.localGet x), .plain (.localTee x)] ++ rest⟩
      ⟨s, f, vals vs ++ [v.toAdmin] ++ rest⟩ := by
  have hx := (List.getElem?_eq_some_iff.mp hv).1
  have h1 := Step.append_right (Step.vals_left
    (Step.variable (P := P) (host := closedHost) (VariableStep.localGet (s := s) hv)) vs)
    (.plain (.localTee x) :: rest)
  have h2 := Step.append_right (Step.vals_left
    (Step.variable (P := P) (host := closedHost)
      (VariableStep.localTee (s := s) (f := f) (x := x) (v := v))) vs) rest
  have h3 := Step.append_right (Step.vals_left
    (Step.variable (P := P) (host := closedHost)
      (VariableStep.localSet (s := s) (v := v) hx)) (vs ++ [v])) rest
  rw [setLocal_self hv] at h3
  exact .tail (.tail (.single (by simpa using h1)) (by simpa using h2))
    (by simpa [vals, List.append_assoc] using h3)

/-- A drop consumes exactly one operand. -/
theorem head_drop {s : Store H} {f : Frame} {args : List Val} {c : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain .drop) c) :
    ∃ v, args = [v] ∧ c = ⟨s, f, []⟩ := by
  have hv := h.fam_inv (by simp [SingleThreaded.Det.famOf])
  simp only [SingleThreaded.Det.famOf, SingleThreaded.Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize he : vals args ++ [Admin.plain .drop] = code at hv
  cases hv with
  | drop v =>
    obtain ⟨h1, _⟩ := (SingleThreaded.Det.append_singleton_inj (l₂ := [v.toAdmin])).mp he
    exact ⟨v, SingleThreaded.Det.vals_inj.mp h1, rfl⟩
  | _ => have := congrArg List.getLast? he; simp at this

/-- The rewritten code simulates the original using frame-preserving self stores. -/
theorem rsBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F rsBI rsB where
  src := by
    intro x y h
    cases h with
    | set x => exact .set x
    | tee x => exact .tee x
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | set x =>
      obtain ⟨v, hv, rfl, rfl, hcode⟩ := get_step_inv (by simpa using hstep)
      subst es'
      refine ⟨t, vals vs ++ rest', Or.inl (run_self_set hv vs rest'), hst, ?_⟩
      simpa using ((AdminsRel.refl (vals vs)).append (AdminsRel.base (rsB.drop v))).append hrest
    | tee x =>
      obtain ⟨v, hv, rfl, rfl, hcode⟩ := get_step_inv (by simpa using hstep)
      subst es'
      refine ⟨t, vals vs ++ [v.toAdmin] ++ rest', Or.inl (run_self_tee hv vs rest'), hst, ?_⟩
      simpa using (AdminsRel.refl (vals vs ++ [v.toAdmin])).append hrest
    | drop v =>
      have hstep' : Step P closedHost
          ⟨s, f, vals (vs ++ [v]) ++ .plain .drop :: rest⟩ ⟨s', f', es'⟩ := by
        simpa [vals, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hW, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep'
      obtain ⟨w, rfl, rfl⟩ := head_drop hh
      obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
      simp only [Config.mk.injEq, List.append_nil] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      refine ⟨t, vals vs ++ rest', Or.inr ⟨rfl, rfl, by simp, ?_⟩, hst,
        (AdminsRel.refl _).append hrest⟩
      exact codeSize_lt_of_infix (vals vs) [v.toAdmin, .plain .drop] rest (by simp)
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | set x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localGet x))
        (x' := [.plain .drop]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
    | tee x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localGet x))
        (x' := []) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
    | drop v =>
      exact GuardSim.not_exit (W := vs ++ [v]) (e₀ := .plain .drop)
        (x' := []) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa [vals, List.append_assoc] using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | set x => exact hall (.plain (.localGet x)) (by simp) rfl
    | tee x => exact hall (.plain (.localGet x)) (by simp) rfl
    | drop v => exact hall (.plain .drop) (by simp) rfl

/-- The simulated heads cannot be host calls. -/
theorem rs_noRedex : CodeSimClosed.NoRedexB H rsB := by
  intro x y hxy s vs rest
  cases hxy with
  | set x =>
    simpa using SingleThreaded.decompose?_vals_cons_none (s := s) (vs := vs)
      (d := Admin.plain (.localGet x)) (r := .plain .drop :: rest) rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | tee x =>
    simpa using SingleThreaded.decompose?_vals_cons_none (s := s) (vs := vs)
      (d := Admin.plain (.localGet x)) (r := rest) rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | drop v =>
    have h := SingleThreaded.decompose?_vals_cons_none (s := s) (vs := vs ++ [v])
      (d := Admin.plain .drop) (r := rest) rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
    simpa [vals, List.append_assoc] using h

end Silmaril.Wasm.Binaryen.RedundantSetLine
