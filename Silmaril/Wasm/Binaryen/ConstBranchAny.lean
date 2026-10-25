module

public import Silmaril.Wasm.Binaryen.ConstBranchSim
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Constant-condition folding at every numerical profile

The original constant `if` stutters to its selected block, already related to
the folded block through the recursive body relation. A taken constant `br_if`
stutters to its branch; an untaken one matches the folded nop. The contextual
payload-independent rank justifies both stutters. Neither direction needs
global numerical determinism, and the checked executable retains its guards.
-/

namespace Silmaril.Wasm.Binaryen.ConstBranch

open Execution.Core Execution.Core.Sim Validation Numerics
open SingleThreaded

variable {H : Type} {P : Profile}

/-- A conditional branch consumes exactly its i32 condition. -/
private theorem head_brIf {s : Store H} {f : Frame} {args : List Val}
    {l : LabelIdx} {cfg : Config H} (h : Det.Head P s f args (.plain (.brIf l)) cfg) :
    ∃ c : BitVec 32, args = [Val.i32 c] ∧
      cfg = ⟨s, f, if c = 0 then [] else [.plain (.br l)]⟩ := by
  cases h with
  | brIfTrue hc => exact ⟨_, rfl, ite_eq_right hc ▸ rfl⟩
  | brIfFalse hc => exact ⟨_, rfl, ite_eq_left hc ▸ rfl⟩
  | _ => first
    | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
    | (exfalso; simp_all [Admin.IsCallRef])

/-- The original constant-condition redex simulates its folded form for every profile. -/
theorem cbSourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F cbBI cbB teeCodeRank where
  src := by
    intro x y h
    exact (cbBaseSim (P := P) (F := F)).src (x := y) (y := x) h
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    rcases hxy with ⟨bt, c, A, B, X', hX, rfl, rfl⟩ |
      ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
    · have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 c]) ++ .plain (.if_ bt A B) :: rest⟩
          ⟨s', f', es'⟩ := by simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hs
      obtain ⟨k, rfl, rfl⟩ := GuardSim.head_if hh
      obtain ⟨hpre, hk⟩ := Det.append_singleton_inj.mp hW
      subst pre
      have hk' : c = k := by cases hk; rfl
      subst k
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [.plain (.block bt X')] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, ?_⟩
      · apply LawfulCodeRank.context_lt
        simp [teeAdminRank, constI32]
      · exact ((AdminsRel.refl (vals vs)).append
          (.cons (.plain (.block bt hX)) .nil)).append hrest
    · have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 c]) ++ .plain (.brIf l) :: rest⟩
          ⟨s', f', es'⟩ := by simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hs
      obtain ⟨k, rfl, rfl⟩ := head_brIf hh
      obtain ⟨hpre, hk⟩ := Det.append_singleton_inj.mp hW
      subst pre
      have hk' : c = k := by cases hk; rfl
      subst k
      simp only [hc, ↓reduceIte, Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ [.plain (.br l)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst, (AdminsRel.refl _).append hrest⟩
      apply LawfulCodeRank.context_lt
      simp [teeAdminRank, constI32]
    · have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 0]) ++ .plain (.brIf l) :: rest⟩
          ⟨s', f', es'⟩ := by simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, args, cfg, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hs
      obtain ⟨k, rfl, rfl⟩ := head_brIf hh
      obtain ⟨hpre, hk⟩ := Det.append_singleton_inj.mp hW
      subst pre
      have hk' : (0 : BitVec 32) = k := by cases hk; rfl
      subst k
      simp only [↓reduceIte, Config.mk.injEq, List.append_nil] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨t, vals vs ++ rest', Or.inl (.single ?_), hst,
        (AdminsRel.refl _).append hrest⟩
      simpa using Step.append_right (Step.vals_left
        (Step.parametric (P := P) (host := closedHost) ParametricStep.nop) vs) rest'
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    rcases hxy with ⟨bt, c, A, B, X', -, rfl, rfl⟩ |
      ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
    · exact GuardSim.not_exit (W := vs ++ [Val.i32 c]) (e₀ := .plain (.if_ bt A B))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
    · exact GuardSim.not_exit (W := vs ++ [Val.i32 c]) (e₀ := .plain (.brIf l))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
    · exact GuardSim.not_exit (W := vs ++ [Val.i32 0]) (e₀ := .plain (.brIf l))
        rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall := congrArg (fun es => es.all Admin.isVal) hx
    rcases hxy with ⟨bt, c, A, B, X', -, rfl, rfl⟩ |
      ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩ <;>
      simp [Admin.isVal, Admin.val?, constI32] at hall

/-- The full raw fold is exactly export-equivalent at every profile, retaining the
original input-and-output-validity premises and closed-host contract. -/
theorem constBranch_sound_any {m : BModule} (hm : m.Ok) (hm' : (constBranch m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (constBranch m).lower m.lower :=
  ⟨exportRefines_of_bodiesRel cbBaseSim (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (constBranch_bodiesRel m) hm' hm,
    (exportRefines_of_bodiesRel cbSourceBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (constBranch_bodiesRel m).flip hm hm').mono fun _ _ h => h.symm⟩

/-- The actual checked fold needs only input validity, retaining both existing guards. -/
theorem constBranchChecked_sound_any {m : BModule} (hm : m.Ok) :
    (constBranchChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (constBranchChecked m).lower m.lower := by
  unfold constBranchChecked
  split
  · next h =>
    have hok := Exe.validOk_sound (Bool.and_eq_true_iff.mp h).2
    exact ⟨hok, constBranch_sound_any hm hok⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Wasm.Binaryen.ConstBranch
