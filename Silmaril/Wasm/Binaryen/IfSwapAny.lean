module

public import Silmaril.Wasm.Binaryen.IfSwapSim
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Arm swapping at every numerical profile

The direct converse records the intermediate result of the original `eqz`.
That step stutters with a payload-independent rank decrease; the following
`if` matches the swapped `if`. Neither direction needs numerical determinism.
-/

namespace Silmaril.Wasm.Binaryen.IfSwap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

/-- The original arm swap and its intermediate `eqz` runtime phase. -/
inductive swapSourceB : List Admin → List Admin → Prop where
  | swap (bt : BlockType) (A A' B B' : List Instr)
      (hA : InstrsRel swapBI A A') (hB : InstrsRel swapBI B B') :
      swapSourceB [.plain (.intTestOp .i32 .eqz), .plain (.if_ bt A B)]
        [.plain (.if_ bt B' A')]
  | phase (c : BitVec 32) (bt : BlockType) (A A' B B' : List Instr)
      (hA : InstrsRel swapBI A A') (hB : InstrsRel swapBI B B') :
      swapSourceB [constI32 (intTestOp .i32 .eqz c), .plain (.if_ bt A B)]
        [constI32 c, .plain (.if_ bt B' A')]

/-- The original `eqz; if` simulates its swapped form for every profile. -/
theorem swapSourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F swapBI swapSourceB teeCodeRank where
  src := by
    intro x y h
    obtain ⟨bt, A, A', B, B', hA, hB, hx, hy⟩ :=
      (swapBaseSim (P := P) (F := F)).src (x := y) (y := x) h
    rw [hx, hy]
    exact .swap bt A A' B B' hA hB
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | swap bt A A' B B' hA hB =>
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ .plain (.intTestOp .i32 .eqz) :: .plain (.if_ bt A B) :: rest⟩
          ⟨s', f', es'⟩ := by simpa using hstep
      obtain ⟨pre, args, cfg, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hs
      obtain ⟨c, rfl, rfl⟩ := GuardSim.head_eqz hh
      subst vs
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals (pre ++ [Val.i32 c]) ++ [.plain (.if_ bt B' A')] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · have hr : teeCodeRank [constI32 (intTestOp .i32 .eqz c), .plain (.if_ bt A B)] <
            teeCodeRank [constI32 c, .plain (.intTestOp .i32 .eqz), .plain (.if_ bt A B)] := by
          simp [teeAdminRank, constI32]
        have := LawfulCodeRank.context_lt (rank := teeCodeRank) (vals pre) rest hr
        simpa [vals, Val.i32, constI32, List.append_assoc] using this
      · simpa [vals, Val.i32, constI32, List.append_assoc] using
          ((AdminsRel.refl (vals pre)).append
            (AdminsRel.base (.phase c bt A A' B B' hA hB))).append hrest
    | phase c bt A A' B B' hA hB =>
      have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 (intTestOp .i32 .eqz c)]) ++
            .plain (.if_ bt A B) :: rest⟩
          ⟨s', f', es'⟩ := by simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hs
      obtain ⟨k, rfl, rfl⟩ := GuardSim.head_if hh
      obtain ⟨hpre, hk⟩ := Det.append_singleton_inj.mp hW
      subst pre
      have hk' : intTestOp .i32 .eqz c = k := by cases hk; rfl
      subst k
      have hsel : (if intTestOp .i32 .eqz c = 0 then B else A) =
          (if c = 0 then A else B) := by
        by_cases hc : c = 0
        · have hz : intTestOp .i32 .eqz c ≠ 0 := fun h => (GuardSim.eqz_eq_zero c).mp h hc
          rw [ite_eq_right hz, ite_eq_left hc]
        · have hz := (GuardSim.eqz_eq_zero c).mpr hc
          rw [ite_eq_left hz, ite_eq_right hc]
      simp only [hsel, Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [.plain (.block bt (if c = 0 then A' else B'))] ++ rest',
        Or.inl (.single ?_), hst, ?_⟩
      · apply Step.append_right
        apply Step.vals_left
        by_cases hc : c = 0
        · subst c
          simpa only [↓reduceIte] using Step.ifFalse (P := P) (host := closedHost)
            (s := t) (f := f') (bt := bt) (b₁ := B') (b₂ := A')
        · simpa only [hc, ↓reduceIte] using Step.ifTrue (P := P) (host := closedHost)
            (s := t) (f := f') (bt := bt) (b₁ := B') (b₂ := A') hc
      · have hbody : InstrsRel swapBI (if c = 0 then A else B) (if c = 0 then A' else B') := by
          split
          · exact hA
          · exact hB
        exact ((AdminsRel.refl (vals vs)).append
          (.cons (.plain (.block bt hbody)) .nil)).append hrest
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | swap bt A A' B B' hA hB =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.intTestOp .i32 .eqz))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | phase c bt A A' B B' hA hB =>
      exact GuardSim.not_exit (W := vs ++ [Val.i32 (intTestOp .i32 .eqz c)])
        (e₀ := .plain (.if_ bt A B))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall := congrArg (fun es => es.all Admin.isVal) hx
    cases hxy <;> simp [Admin.isVal, Admin.val?, constI32] at hall

/-- Raw arm swapping is exactly export-equivalent for every profile, retaining
the original input-and-output-validity premises and closed-host contract. -/
theorem ifSwap_sound_any {m : BModule} (hm : m.Ok) (hm' : (ifSwap m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (ifSwap m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel swapBaseSim (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (ifSwap_bodiesRel m) hm' hm,
    (exportRefines_of_bodiesRel swapSourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (ifSwap_bodiesRel m).flip hm hm').mono fun _ _ h => h.symm⟩

/-- The actual checked arm swap needs only input validity and retains its validator fallback. -/
theorem ifSwapChecked_sound_any {m : BModule} (hm : m.Ok) :
    (ifSwapChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (ifSwapChecked m).lower m.lower := by
  unfold ifSwapChecked
  split
  · next h => exact ⟨Exe.validOk_sound h, ifSwap_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Wasm.Binaryen.IfSwap
