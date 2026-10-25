module

public import Silmaril.Wasm.Binaryen.ConstBranchSim
public import Silmaril.Wasm.Binaryen.Pass.ConstSelect

@[expose] public section

/-! Constant select and branch-table folding as a code simulation. -/

namespace Silmaril.Wasm.Binaryen.ConstSelect

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

/-- Original and rewritten flat segments. -/
inductive csBI : List Instr → List Instr → Prop where
  | selectTrue (ts : Option (List ValType)) (c : BitVec 32) (hc : c ≠ 0) :
      csBI [.intConst .i32 c, .select ts] [.drop]
  | selectFalse (ts : Option (List ValType)) (b : BitVec 32) :
      csBI [.intConst .i32 b, .intConst .i32 0, .select ts] [.drop, .intConst .i32 b, .nop]
  | table (ls : List LabelIdx) (d : LabelIdx) (c : BitVec 32) :
      csBI [.intConst .i32 c, .brTable ls d] [.br (ls[c.toNat]?.getD d)]

/-- The same segments as administrative code. -/
inductive csB : List Admin → List Admin → Prop where
  | selectTrue (ts : Option (List ValType)) (c : BitVec 32) (hc : c ≠ 0) :
      csB [constI32 c, .plain (.select ts)] [.plain .drop]
  | selectFalse (ts : Option (List ValType)) (b : BitVec 32) :
      csB [constI32 b, constI32 0, .plain (.select ts)] [.plain .drop, constI32 b, .plain .nop]
  | table (ls : List LabelIdx) (d : LabelIdx) (c : BitVec 32) :
      csB [constI32 c, .plain (.brTable ls d)] [.plain (.br (ls[c.toNat]?.getD d))]

/-- The head rule of select exposes its two operands and its i32 condition. -/
theorem head_select {s : Store H} {f : Frame} {args : List Val} {ts : Option (List ValType)}
    {c₀ : Config H} (h : SingleThreaded.Det.Head P s f args (.plain (.select ts)) c₀) :
    ∃ (a b : Val) (c : BitVec 32), args = [a, b, .num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [(if c = 0 then b else a).toAdmin]⟩ := by
  have hv := h.fam_inv (by simp [SingleThreaded.Det.famOf])
  simp only [SingleThreaded.Det.famOf, SingleThreaded.Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize he : vals args ++ [Admin.plain (.select ts)] = code at hv
  cases hv with
  | @selectTrue a b c ts' hc =>
    obtain ⟨h1, _⟩ := (SingleThreaded.Det.append_singleton_inj (l₂ := [_, _, _])).mp he
    refine ⟨a, b, c, ?_, ?_⟩
    · exact SingleThreaded.Det.vals_inj.mp h1
    · rw [ite_eq_right hc]
  | selectFalse a b =>
    obtain ⟨h1, _⟩ := (SingleThreaded.Det.append_singleton_inj (l₂ := [_, _, _])).mp he
    exact ⟨a, b, 0, SingleThreaded.Det.vals_inj.mp h1, by simp⟩
  | _ => have := congrArg List.getLast? he; simp at this

/-- The table head selects an in-range label or its default. -/
theorem head_table {s : Store H} {f : Frame} {args : List Val} {ls : List LabelIdx}
    {d : LabelIdx} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain (.brTable ls d)) c₀) :
    ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [.plain (.br (ls[c.toNat]?.getD d))]⟩ := by
  cases h with
  | brTableLt hi => exact ⟨_, rfl, by simp [hi]⟩
  | brTableGe hi => exact ⟨_, rfl, by simp [List.getElem?_eq_none_iff.mpr hi]⟩
  | _ => first
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2
        (by simp [SingleThreaded.Det.famOf])
    | (exfalso; simp_all [Admin.IsCallRef])

/-- Invert a select with a known condition under an arbitrary value prefix. -/
theorem select_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {c : BitVec 32} {ts : Option (List ValType)} {rest es' : List Admin}
    (h : Step P closedHost ⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩
      ⟨s', f', es'⟩) :
    ∃ (pre : List Val) (a b : Val), vs = pre ++ [a, b] ∧ s' = s ∧ f' = f ∧
      es' = vals pre ++ [(if c = 0 then b else a).toAdmin] ++ rest := by
  have hcode : vals vs ++ [constI32 c, .plain (.select ts)] ++ rest =
      vals (vs ++ [.num ⟨.int .i32, c⟩]) ++ .plain (.select ts) :: rest := by
    simp [vals, List.append_assoc, constI32, Val.i32]
  rw [hcode] at h
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨a, b, k, rfl, rfl⟩ := head_select hh
  have hW' : vs ++ [.num ⟨.int .i32, c⟩] =
      (pre ++ [a, b]) ++ [.num ⟨.int .i32, k⟩] := by simpa [List.append_assoc] using hW
  obtain ⟨hvs, hck⟩ := SingleThreaded.Det.append_singleton_inj.mp hW'
  have hk : c = k := by cases hck; rfl
  subst k
  simp only [Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨pre, a, b, hvs, rfl, rfl, rfl⟩

/-- Invert a branch table with a known index. -/
theorem table_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {c : BitVec 32} {ls : List LabelIdx} {d : LabelIdx} {rest es' : List Admin}
    (h : Step P closedHost ⟨s, f, vals vs ++ [constI32 c, .plain (.brTable ls d)] ++ rest⟩
      ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs ++ [.plain (.br (ls[c.toNat]?.getD d))] ++ rest := by
  have hcode : vals vs ++ [constI32 c, .plain (.brTable ls d)] ++ rest =
      vals (vs ++ [.num ⟨.int .i32, c⟩]) ++ .plain (.brTable ls d) :: rest := by
    simp [vals, List.append_assoc, constI32, Val.i32]
  rw [hcode] at h
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h
  obtain ⟨k, rfl, rfl⟩ := head_table hh
  obtain ⟨rfl, hck⟩ := SingleThreaded.Det.append_singleton_inj.mp hW
  have hk : c = k := by cases hck; rfl
  subst k
  simp only [Config.mk.injEq] at hc
  exact hc

/-- The original code simulates the folded code. -/
theorem csBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F csBI csB where
  src := by
    intro x y h
    cases h with
    | selectTrue ts c hc => exact .selectTrue ts c hc
    | selectFalse ts b => exact .selectFalse ts b
    | table ls d c => exact .table ls d c
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | selectTrue ts c hc =>
      obtain ⟨pre, a, b, rfl, rfl, rfl, hcode⟩ := select_step_inv hstep
      rw [ite_eq_right hc] at hcode
      subst es'
      refine ⟨t, vals pre ++ [a.toAdmin] ++ rest', Or.inl ?_, hst, ?_⟩
      · apply Relation.TransGen.single
        simpa [vals, List.append_assoc] using
          Step.append_right (Step.vals_left (Step.parametric (.drop b)) (pre ++ [a])) rest'
      · exact (AdminsRel.refl _).append hrest
    | selectFalse ts b =>
      have hstep' : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 b]) ++ [constI32 0, .plain (.select ts)] ++ rest⟩
          ⟨s', f', es'⟩ := by
        simpa [vals, constI32, Val.i32, List.append_assoc] using hstep
      obtain ⟨pre, a, v, hvs, rfl, rfl, hcode⟩ := select_step_inv hstep'
      have hvs' : vs ++ [Val.i32 b] = (pre ++ [a]) ++ [v] := by
        simpa [List.append_assoc] using hvs
      obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hvs'
      simp only [ite_true] at hcode
      subst es'
      refine ⟨t, vals pre ++ [constI32 b] ++ rest', Or.inl ?_, hst, ?_⟩
      · have h1 := Step.append_right
          (Step.vals_left (Step.parametric (P := P) (host := closedHost) (s := t) (f := f')
            (.drop a)) pre) ([constI32 b, .plain .nop] ++ rest')
        have h2 := Step.append_right
          (Step.vals_left (Step.parametric (P := P) (host := closedHost) (s := t) (f := f')
            .nop) (pre ++ [Val.i32 b])) rest'
        exact .tail (.single (by simpa [vals, List.append_assoc] using h1))
          (by simpa [vals, constI32, List.append_assoc] using h2)
      · exact (AdminsRel.refl _).append hrest
    | table ls d c =>
      obtain ⟨rfl, rfl, rfl⟩ := table_step_inv hstep
      refine ⟨t, vals vs ++ [.plain (.br (ls[c.toNat]?.getD d))] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, (AdminsRel.refl _).append hrest⟩
      have hl : sizeOf (ls[c.toNat]?.getD d) ≤ sizeOf ls + sizeOf d := by
        cases hi : ls[c.toNat]? with
        | none => simp only [Option.getD_none]; omega
        | some l =>
          have hm := List.sizeOf_lt_of_mem (List.mem_of_getElem? hi)
          simp only [Option.getD_some]
          omega
      rw [List.append_assoc, List.append_assoc]
      have hs := codeSize_append (vals vs) ([constI32 c, .plain (.brTable ls d)] ++ rest)
      have ht := codeSize_append (vals vs) ([Admin.plain (.br (ls[c.toNat]?.getD d))] ++ rest)
      simp only [codeSize, List.cons_append, List.nil_append, List.cons.sizeOf_spec,
        Admin.plain.sizeOf_spec, Instr.br.sizeOf_spec, Instr.brTable.sizeOf_spec] at hs ht ⊢
      omega

  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | selectTrue ts c hc =>
      apply GuardSim.not_exit (W := vs ++ [Val.i32 c])
        (e₀ := .plain (.select ts)) (x' := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, constI32, List.append_assoc] using he
    | selectFalse ts b =>
      apply GuardSim.not_exit (W := vs ++ [Val.i32 b, Val.i32 0])
        (e₀ := .plain (.select ts)) (x' := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, constI32, List.append_assoc] using he
    | table ls d c =>
      apply GuardSim.not_exit (W := vs ++ [Val.i32 c])
        (e₀ := .plain (.brTable ls d)) (x' := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, constI32, List.append_assoc] using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | selectTrue ts c hc => exact hall (.plain (.select ts)) (by simp) rfl
    | selectFalse ts b => exact hall (.plain (.select ts)) (by simp) rfl
    | table ls d c => exact hall (.plain (.brTable ls d)) (by simp) rfl

/-- No source base pair contains a host-call redex. -/
theorem cs_noRedex : CodeSimClosed.NoRedexB H csB := by
  intro x y hxy s vs rest
  cases hxy with
  | selectTrue ts c hc =>
    rw [show vals vs ++ [constI32 c, Admin.plain (.select ts)] ++ rest =
      vals (vs ++ [Val.i32 c]) ++ .plain (.select ts) :: rest by
        simp [vals, constI32, List.append_assoc]]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | selectFalse ts b =>
    rw [show vals vs ++ [constI32 b, constI32 0, Admin.plain (.select ts)] ++ rest =
      vals (vs ++ [Val.i32 b, Val.i32 0]) ++ .plain (.select ts) :: rest by
        simp [vals, constI32, List.append_assoc]]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | table ls d c =>
    rw [show vals vs ++ [constI32 c, Admin.plain (.brTable ls d)] ++ rest =
      vals (vs ++ [Val.i32 c]) ++ .plain (.brTable ls d) :: rest by
        simp [vals, constI32, List.append_assoc]]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)

end Silmaril.Wasm.Binaryen.ConstSelect
