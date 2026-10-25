module

public import Silmaril.Wasm.Binaryen.ConstSelectStack
public import Silmaril.Wasm.Binaryen.ConstSelectRel
public import Silmaril.Wasm.Binaryen.CodeSimTyped
public import Silmaril.Wasm.Execution.Core.Sim.TypedFragment
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Constant-select/table folding at every numerical profile

The reverse simulation retains typing of the original runtime configuration in
its ambient context. That invariant supplies both select operands without
changing the pass or excluding any valid input accepted by its existing guards.
-/

namespace Silmaril.Wasm.Binaryen.ConstSelect

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

theorem select_operands_of_contextTyped {s : Store H} {f : Frame} {vs : List Val}
    {c : BitVec 32} {ts : Option (List ValType)} {rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [constI32 c, .plain (.select ts)] ++ rest⟩) :
    ∃ (pre : List Val) (a b : Val), vs = pre ++ [a, b] := by
  have h' : FragmentTyped
      ⟨s, f, vals (vs ++ [Val.i32 c]) ++ .plain (.select ts) :: rest⟩ := by
    simpa [vals, Val.i32, constI32, List.append_assoc] using h.fragment
  have hlen : 3 ≤ (vs ++ [Val.i32 c]).length := h'.active_arity (by
    intro C it ha
    have hi := ha.plain_inv_ne
    cases hi <;> rename_i hi <;> cases hi <;> simp)
  have hlen' : 2 ≤ vs.length := by simpa using hlen
  cases vs using List.reverseRecOn with
  | nil => simp at hlen'
  | append_singleton pre b =>
    cases pre using List.reverseRecOn with
    | nil => simp at hlen'
    | append_singleton pre a => exact ⟨pre, a, b, by simp⟩

/-- Folded-to-original runtime phases. The zero-select phase remembers the
remaining administrative nop after the folded drop has consumed its operand. -/
inductive csReverseB : List Admin → List Admin → Prop where
  | selectTrue (ts : Option (List ValType)) (c : BitVec 32) (hc : c ≠ 0) :
      csReverseB [.plain .drop] [constI32 c, .plain (.select ts)]
  | selectFalse (ts : Option (List ValType)) (b : BitVec 32) :
      csReverseB [.plain .drop, constI32 b, .plain .nop]
        [constI32 b, constI32 0, .plain (.select ts)]
  | falseNop (b : BitVec 32) : csReverseB [constI32 b, .plain .nop] [constI32 b]
  | table (ls : List LabelIdx) (d : LabelIdx) (c : BitVec 32) :
      csReverseB [.plain (.br (ls[c.toNat]?.getD d))] [constI32 c, .plain (.brTable ls d)]

private theorem table_step {s : Store H} {f : Frame} (ls : List LabelIdx) (d : LabelIdx)
    (c : BitVec 32) : Step P closedHost
      ⟨s, f, [constI32 c, .plain (.brTable ls d)]⟩
      ⟨s, f, [.plain (.br (ls[c.toNat]?.getD d))]⟩ := by
  by_cases hi : c.toNat < ls.length
  · simpa [hi] using Step.brTableLt (P := P) (host := closedHost) (s := s) (f := f)
      (l' := d) (i := c) (ls := ls) (l := ls[c.toNat]) (by simp)
  · simpa [List.getElem?_eq_none_iff.mpr (by omega : ls.length ≤ c.toNat)] using
      Step.brTableGe (P := P) (host := closedHost) (s := s) (f := f) (l' := d)
        (i := c) (ls := ls) (by omega)

theorem csReverseFacts {F : FuncInst H → FuncInst H → Prop} :
    BaseFacts P closedHost F (fun a b => csBI b a) csReverseB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | selectTrue ts c hc => exact .selectTrue ts c hc
    | selectFalse ts b => exact .selectFalse ts b
    | table ls d c => exact .table ls d c
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    cases hxy with
    | selectTrue ts c hc =>
      exact (GuardSim.not_exit (W := vs) (e₀ := .plain .drop) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk (by simpa using he)).elim
    | selectFalse ts b =>
      exact (GuardSim.not_exit (W := vs) (e₀ := .plain .drop) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk (by simpa using he)).elim
    | falseNop b =>
      exact (GuardSim.not_exit (W := vs ++ [Val.i32 b]) (e₀ := .plain .nop) rfl (by simp)
        (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, constI32, Val.i32, List.append_assoc] using he)).elim
    | table ls d c =>
      obtain ⟨rfl, rfl, rfl⟩ := ConstBranch.exit_br hk he
      exact ⟨t, [], .single (by simpa using Step.vals_left (table_step ls d c) us), hst⟩
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact Det.mem_vals ha
    cases hxy with
    | selectTrue => exact hall (.plain .drop) (by simp) rfl
    | selectFalse => exact hall (.plain .drop) (by simp) rfl
    | falseNop => exact hall (.plain .nop) (by simp) rfl
    | table ls d c => exact hall (.plain (.br (ls[c.toNat]?.getD d))) (by simp) rfl

theorem csReverseTypedBaseSim {F : FuncInst H → FuncInst H → Prop} :
    TypedBaseSim P F (fun a b => csBI b a) csReverseB teeCodeRank where
  facts := csReverseFacts
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest htyped hstep
    cases hxy with
    | selectTrue ts c hc =>
      obtain ⟨pre, a, b, rfl⟩ := select_operands_of_contextTyped htyped
      have he := SimplifyLocalsLite.drop_step_unique (vs := pre ++ [a]) (v := b)
        (by simpa [vals, List.append_assoc] using hstep)
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals pre ++ [a.toAdmin] ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · simpa [vals, List.append_assoc] using Step.append_right (Step.vals_left
          (Step.parametric (P := P) (host := (fun _ _ _ _ => False)) (s := t)
            (ParametricStep.selectTrue (v₁ := a) (v₂ := b) (ts := ts) hc)) pre) rest'
      · simpa [vals, List.append_assoc] using (AdminsRel.refl (vals (pre ++ [a]))).append hrest
    | selectFalse ts b =>
      have hs : Step P (fun _ _ _ _ => False) ⟨s, f, vals vs ++ .plain .drop ::
          ([constI32 b, .plain .nop] ++ rest)⟩ ⟨s', f', es'⟩ := by simpa using hstep
      obtain ⟨pre, args, cfg, hV, hh, he⟩ := SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl hs
      obtain ⟨a, rfl, rfl⟩ := RedundantSetLine.head_drop hh
      subst vs
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals pre ++ [constI32 b] ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · simpa [vals, Val.i32, constI32, List.append_assoc] using Step.append_right
          (Step.vals_left (Step.parametric (P := P) (host := (fun _ _ _ _ => False)) (s := t)
            (ParametricStep.selectFalse a (Val.i32 b) ts)) pre) rest'
      · simpa [List.append_assoc] using
          ((AdminsRel.vals pre).append (.base (.falseNop b))).append hrest
    | falseNop b =>
      have hs : Step P (fun _ _ _ _ => False)
          ⟨s, f, vals (vs ++ [Val.i32 b]) ++ .plain .nop :: rest⟩ ⟨s', f', es'⟩ := by
        simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hV, hh, he⟩ := SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl hs
      obtain ⟨rfl, rfl⟩ := ConstBranch.head_nop hh
      simp only [List.append_nil] at hV
      subst pre
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [constI32 b] ++ rest', Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · simpa [vals, Val.i32, constI32, List.append_assoc] using
          (LawfulCodeRank.context_lt (rank := teeCodeRank) (vals vs)
            rest (show teeCodeRank [constI32 b] <
              teeCodeRank [constI32 b, .plain .nop] by simp [teeAdminRank, constI32]))
      · simpa [vals, Val.i32, constI32, List.append_assoc] using
          (AdminsRel.vals (vs ++ [Val.i32 b])).append hrest
    | table ls d c =>
      exfalso
      have hs : Step P (fun _ _ _ _ => False) ⟨s, f, vals vs ++ .plain (.br (ls[c.toNat]?.getD d)) :: rest⟩ ⟨s', f', es'⟩ := by
        simpa using hstep
      obtain ⟨pre, args, cfg, _, hh, _⟩ := SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl hs
      exact ConstBranch.head_br hh

/-- The entire recursive raw pass has exact export equivalence at the same
arbitrary profile, retaining its existing input-and-output-validity premises. -/
theorem constSelect_sound_any {m : BModule} (hm : m.Ok) (hm' : (constSelect m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (constSelect m).lower m.lower :=
  ⟨exportRefines_of_typedBodiesRel csReverseTypedBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (constSelect_bodiesRel m).flip hm' hm,
    (exportRefines_of_bodiesRel csBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (constSelect_bodiesRel m) hm hm').mono (fun _ _ h => h.symm)⟩

/-- The actual checked executable keeps both existing guards and needs only
input validity, at every numerical profile. -/
theorem constSelectChecked_sound_any {m : BModule} (hm : m.Ok) :
    (constSelectChecked m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (constSelectChecked m).lower m.lower := by
  unfold constSelectChecked
  split
  · next h =>
    have hok := Exe.validOk_sound (Bool.and_eq_true_iff.mp h).2
    exact ⟨hok, constSelect_sound_any hm hok⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Wasm.Binaryen.ConstSelect
