module

public import Silmaril.Wasm.Binaryen.AddChainRel
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Exact constant-addition-chain folding for every numerical profile

The original first addition stutters into an explicit runtime phase; the second
matches the combined addition using wrapping integer associativity. A
payload-independent contextual rank decreases at the stutter. The recursive
module pass therefore has two genuine simulations at the same arbitrary
profile, including all subsequent numerical and host choices allowed by the
existing closed-host contract. The checked executable retains all its guards.
-/

namespace Silmaril.Wasm.Binaryen.AddChain

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

/-- The original addition chain and its intermediate runtime phase. -/
inductive acSourceB : List Admin → List Admin → Prop where
  | add (t : IntType) (a b : BitVec t.width) :
      acSourceB [.plain (.intConst t a), .plain (.intBinOp t .add),
        .plain (.intConst t b), .plain (.intBinOp t .add)]
        [.plain (.intConst t (a + b)), .plain (.intBinOp t .add)]
  | phase (t : IntType) (v a b : BitVec t.width) :
      acSourceB [.plain (.intConst t (v + a)), .plain (.intConst t b), .plain (.intBinOp t .add)]
        [.plain (.intConst t v), .plain (.intConst t (a + b)), .plain (.intBinOp t .add)]

/-- The original chain simulates the combined addition without numerical determinism. -/
theorem acSourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F acBI acSourceB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | add t a b => exact .add t a b
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | add ty a b =>
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ [.plain (.intConst ty a), .plain (.intBinOp ty .add)] ++
            ([.plain (.intConst ty b), .plain (.intBinOp ty .add)] ++ rest)⟩
          ⟨s', f', es'⟩ := by simpa [List.append_assoc] using hstep
      obtain ⟨pre, v, rfl, rfl, rfl, rfl⟩ := add_const_step_inv hs
      refine ⟨t, vals (pre ++ [.num ⟨.int ty, v⟩]) ++
          [.plain (.intConst ty (a + b)), .plain (.intBinOp ty .add)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · have hr : teeCodeRank [.plain (.intConst ty (v + a)), .plain (.intConst ty b),
            .plain (.intBinOp ty .add)] <
          teeCodeRank [.plain (.intConst ty v), .plain (.intConst ty a),
            .plain (.intBinOp ty .add), .plain (.intConst ty b), .plain (.intBinOp ty .add)] := by
          simp [teeAdminRank]
        have := LawfulCodeRank.context_lt (rank := teeCodeRank) (vals pre) rest hr
        simpa [vals, Val.toAdmin, List.append_assoc] using this
      · simpa [vals, Val.toAdmin, List.append_assoc] using
          ((AdminsRel.refl (vals pre)).append (AdminsRel.base (.phase ty v a b))).append hrest
    | phase ty v a b =>
      have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [.num ⟨.int ty, v + a⟩]) ++
            [.plain (.intConst ty b), .plain (.intBinOp ty .add)] ++ rest⟩
          ⟨s', f', es'⟩ := by simpa [vals, Val.toAdmin, List.append_assoc] using hstep
      obtain ⟨pre, w, hvs, rfl, rfl, rfl⟩ := add_const_step_inv hs
      obtain ⟨hpre, hw⟩ := SingleThreaded.Det.append_singleton_inj.mp hvs
      subst pre
      have hw' : v + a = w := by cases hw; rfl
      subst w
      refine ⟨t, vals vs ++ [.plain (.intConst ty ((v + a) + b))] ++ rest',
        Or.inl (.single ?_), hst, (AdminsRel.refl _).append hrest⟩
      have h := Step.append_right (Step.vals_left
        (Step.numeric (P := P) (host := closedHost) (s := t) (f := f')
          (NumericStep.intBinOp (t := ty) (op := .add) (x := v) (y := a + b) rfl)) vs) rest'
      simpa [BitVec.add_assoc] using h
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | add ty a b =>
      apply GuardSim.not_exit (W := vs ++ [.num ⟨.int ty, a⟩])
        (e₀ := .plain (.intBinOp ty .add)) (x' := [.plain (.intConst ty b), .plain (.intBinOp ty .add)])
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, Val.toAdmin, List.append_assoc] using he
    | phase ty v a b =>
      apply GuardSim.not_exit (W := vs ++ [.num ⟨.int ty, v + a⟩, .num ⟨.int ty, b⟩])
        (e₀ := .plain (.intBinOp ty .add)) (x' := [])
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
      simpa [vals, Val.toAdmin, List.append_assoc] using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall := congrArg (fun es => es.all Admin.isVal) hx
    cases hxy <;> simp [Admin.isVal, Admin.val?] at hall

/-- Raw recursive addition-chain folding preserves exact exports for any profile,
provided both the input and output are valid, as in the existing deterministic API. -/
theorem addChain_sound_any {m : BModule} (hm : m.Ok) (hm' : (addChain m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (addChain m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel acBaseSim (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (addChain_bodiesRel m).flip hm' hm,
    (exportRefines_of_bodiesRel acSourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (addChain_bodiesRel m) hm hm').mono fun _ _ h => h.symm⟩

/-- The actual checked executable is valid and exactly export-equivalent at every
profile. Its validity, export, encoding and size guards are retained unchanged. -/
theorem addChainChecked_sound_any {m : BModule} (hm : m.Ok) :
    (addChainChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (addChainChecked m).lower m.lower := by
  have hrefl : ExportEquiv (· = ·) P (closedHost (H := H)) m.lower m.lower :=
    ⟨ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩
  unfold addChainChecked
  dsimp only
  split
  · next h =>
    have hok := Exe.validOk_sound (Bool.and_eq_true_iff.mp h).2
    split
    · split
      · exact ⟨hok, addChain_sound_any hm hok⟩
      · exact ⟨hm, hrefl⟩
    · exact ⟨hm, hrefl⟩
  · exact ⟨hm, hrefl⟩

end Silmaril.Wasm.Binaryen.AddChain
