module

public import Silmaril.Wasm.Binaryen.ConstBranchSim
public import Silmaril.Wasm.Binaryen.PrecomputeAnchorCheck
public import Silmaril.Wasm.Binaryen.Pass.AddChain

@[expose] public section

/-! Wrapping constant-addition chains as a simulation, with the shorter code
on the left. A step of that code is matched by two additions in the original. -/

namespace Silmaril.Wasm.Binaryen.AddChain

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

inductive acBI : List Instr → List Instr → Prop where
  | add (t : IntType) (a b : BitVec t.width) :
      acBI [.intConst t a, .intBinOp t .add, .intConst t b, .intBinOp t .add]
        [.intConst t (a + b), .intBinOp t .add]

inductive acB : List Admin → List Admin → Prop where
  | add (t : IntType) (a b : BitVec t.width) :
      acB [.plain (.intConst t a), .plain (.intBinOp t .add),
        .plain (.intConst t b), .plain (.intBinOp t .add)]
        [.plain (.intConst t (a + b)), .plain (.intBinOp t .add)]

/-- Invert addition by a known constant, leaving the rest of the stack alone. -/
theorem add_const_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {t : IntType} {c : BitVec t.width} {rest es' : List Admin}
    (h : Step P closedHost
      ⟨s, f, vals vs ++ [.plain (.intConst t c), .plain (.intBinOp t .add)] ++ rest⟩
      ⟨s', f', es'⟩) :
    ∃ (pre : List Val) (v : BitVec t.width), vs = pre ++ [.num ⟨.int t, v⟩] ∧
      s' = s ∧ f' = f ∧
      es' = vals pre ++ [.plain (.intConst t (v + c))] ++ rest := by
  have heq : vals vs ++ [.plain (.intConst t c), .plain (.intBinOp t .add)] ++ rest =
      vals (vs ++ [.num ⟨.int t, c⟩]) ++ .plain (.intBinOp t .add) :: rest := by
    simp [vals, Val.toAdmin]
  rw [heq] at h
  rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨pre, a, b, hus, h1, h2, h3⟩ := PrecomputeAnchorCheck.step_add_inv hs1 t us rfl
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    rw [hus] at hV
    have hV' : vs ++ [.num ⟨.int t, c⟩] =
        ((ws ++ pre) ++ [.num ⟨.int t, a⟩]) ++ [.num ⟨.int t, b⟩] := by
      simpa [List.append_assoc] using hV
    obtain ⟨hvs, hb⟩ := SingleThreaded.Det.append_singleton_inj.mp hV'
    have hcb : c = b := by cases hb; rfl
    subst b
    exact ⟨ws ++ pre, a, hvs, rfl, rfl, by simp⟩
  · cases h
  · cases h

/-- The original two additions run to the same wrapping sum. -/
theorem original_run {s : Store H} {f : Frame} (vs : List Val) (rest : List Admin)
    (t : IntType) (v a b : BitVec t.width) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, vals (vs ++ [.num ⟨.int t, v⟩]) ++
        [.plain (.intConst t a), .plain (.intBinOp t .add),
          .plain (.intConst t b), .plain (.intBinOp t .add)] ++ rest⟩
      ⟨s, f, vals vs ++ [.plain (.intConst t (v + (a + b)))] ++ rest⟩ := by
  have h1 := Step.append_right
    (Step.vals_left (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
      (NumericStep.intBinOp (t := t) (op := .add) (x := v) (y := a) rfl)) vs)
    ([.plain (.intConst t b), .plain (.intBinOp t .add)] ++ rest)
  have h2 := Step.append_right
    (Step.vals_left (Step.numeric (P := P) (host := closedHost) (s := s) (f := f)
      (NumericStep.intBinOp (t := t) (op := .add) (x := v + a) (y := b) rfl)) vs) rest
  refine Relation.TransGen.tail (b := ⟨s, f, vals vs ++
    [.plain (.intConst t (v + a)), .plain (.intConst t b),
      .plain (.intBinOp t .add)] ++ rest⟩) (Relation.TransGen.single ?_) ?_
  · simpa [vals, Val.toAdmin, List.append_assoc] using h1
  · simpa [BitVec.add_assoc] using h2

/-- A combined addition simulates the two original additions. -/
theorem acBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => acBI b a) (fun a b => acB b a) where
  src := by
    intro x y h
    cases h with
    | add t a b => exact .add t a b
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | add ty a b =>
      obtain ⟨pre, v, rfl, rfl, rfl, rfl⟩ := add_const_step_inv hstep
      exact ⟨t, vals pre ++ [.plain (.intConst ty (v + (a + b)))] ++ rest',
        Or.inl (original_run pre rest' ty v a b), hst,
        (AdminsRel.refl _).append hrest⟩
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | add ty a b =>
      apply GuardSim.not_exit (W := vs ++ [.num ⟨.int ty, a + b⟩])
        (e₀ := .plain (.intBinOp ty .add)) (x' := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, Val.toAdmin, List.append_assoc] using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | add ty a b => exact hall (.plain (.intBinOp ty .add)) (by simp) rfl

/-- The shorter side contains no host call redex. -/
theorem ac_noRedex : CodeSimClosed.NoRedexB H (fun a b => acB b a) := by
  intro x y hxy s vs rest
  cases hxy with
  | add ty a b =>
    rw [show vals vs ++ [Admin.plain (.intConst ty (a + b)), .plain (.intBinOp ty .add)] ++ rest =
      vals (vs ++ [.num ⟨.int ty, a + b⟩]) ++ .plain (.intBinOp ty .add) :: rest by
        simp [vals, Val.toAdmin, List.append_assoc]]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)

end Silmaril.Wasm.Binaryen.AddChain
