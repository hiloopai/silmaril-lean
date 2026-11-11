module

public import Silmaril.Wasm.Binaryen.DropGet.Defs
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim

@[expose] public section

/-! # Dropped local reads: the forward simulation and the body relation

`dgBaseSim` has the **original** on the left, at every numerical profile: its
`local.get x` step is matched by the result's `nop` step, leaving the runtime pair
`v; drop` ⟷ (nothing), whose `drop` step stutters with a `codeSize` decrease.
`elimL_rel` relates every original body to its rewrite. The typed reverse simulation
and the export equivalence at every numerical profile are in `Reverse.lean`.
-/
namespace Silmaril.Proofs.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Runtime base pairs, with the state after the read. -/
inductive dgB : List Admin → List Admin → Prop where
  | start (x : LocalIdx) : dgB [.plain (.localGet x), .plain .drop] [.plain .nop]
  | phase (v : Val) : dgB [v.toAdmin, .plain .drop] []

/-- A `drop` after a value pops it, leaving store and frame unchanged. -/
private theorem drop_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {v : Val}
    {rest es' : List Admin}
    (hstep : Step P closedHost ⟨s, f, vals (vs ++ [v]) ++ .plain .drop :: rest⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs ++ rest := by
  obtain ⟨pre, args, cfg, hW, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
  obtain ⟨w, hargs, hcfg⟩ : ∃ w, args = [w] ∧ cfg = ⟨s, f, []⟩ :=
    RedundantSetLine.head_drop hh
  have hW' : vs ++ [v] = pre ++ [w] := by rw [← hargs]; exact hW
  have hpre : pre = vs := (SingleThreaded.Det.append_singleton_inj.mp hW').1.symm
  have hc' : (⟨s', f', es'⟩ : Config H) = ⟨s, f, vals pre ++ rest⟩ := by
    simpa only [hcfg, List.append_nil] using hc
  have hparts : s' = s ∧ f' = f ∧ es' = vals pre ++ rest := by
    simpa only [Config.mk.injEq] using hc'
  rw [← hpre]
  exact hparts

theorem dgBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F dgBI dgB where
  src := by
    intro x y h
    cases h with
    | mk x => exact .start x
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | start x =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨t, f, vals vs ++ [.plain .nop] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = t ∧ f' = f ∧ es'' = vals vs ++ [.plain .nop] ++ rest' ∧
            codeSize es' < codeSize (vals vs ++ [.plain (.localGet x), .plain .drop] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel dgBI dgB es' es''
      obtain ⟨v, -, hs, hf, hes⟩ : ∃ v, f.local? x = some (some v) ∧ s' = s ∧ f' = f ∧
          es' = vals vs ++ v.toAdmin :: .plain .drop :: rest :=
        RedundantSetLine.get_step_inv (by simpa using hstep)
      rw [hs, hf, hes]
      refine ⟨t, vals vs ++ [] ++ rest', Or.inl (.single ?_), hst, ?_⟩
      · exact Step.append_right (Step.vals_left
          (Step.parametric (P := P) (host := closedHost) (s := t)
            ParametricStep.nop) vs) rest'
      · simpa [List.append_assoc] using
          ((AdminsRel.refl (vals vs)).append (AdminsRel.base (dgB.phase v))).append hrest
    | phase v =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨t, f, vals vs ++ [] ++ rest'⟩ ⟨t', f', es''⟩ ∨
          (t' = t ∧ f' = f ∧ es'' = vals vs ++ [] ++ rest' ∧
            codeSize es' < codeSize (vals vs ++ [v.toAdmin, .plain .drop] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel dgBI dgB es' es''
      have hstep' : Step P closedHost
          ⟨s, f, vals (vs ++ [v]) ++ .plain .drop :: rest⟩ ⟨s', f', es'⟩ := by
        simpa [vals, List.append_assoc] using hstep
      obtain ⟨hs, hf, hes⟩ : s' = s ∧ f' = f ∧ es' = vals vs ++ rest := drop_step_inv hstep'
      have hrank : codeSize (vals vs ++ rest) <
          codeSize (vals vs ++ [v.toAdmin, .plain .drop] ++ rest) :=
        codeSize_lt_of_infix (vals vs) [v.toAdmin, .plain .drop] rest (by simp)
      rw [hs, hf, hes]
      refine ⟨t, vals vs ++ [] ++ rest', Or.inr ⟨rfl, rfl, rfl, ?_⟩, hst,
        by simpa using (AdminsRel.refl (vals vs)).append hrest⟩
      simpa using hrank
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | start x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localGet x))
        (x' := [.plain .drop]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa using he)
    | phase v =>
      exact GuardSim.not_exit (W := vs ++ [v]) (e₀ := .plain .drop)
        (x' := []) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa [vals, List.append_assoc] using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | start x => exact hall (.plain (.localGet x)) (by simp) rfl
    | phase v => exact hall (.plain .drop) (by simp) rfl

mutual
theorem elimE_rel : ∀ x : BExpr, InstrsRel dgBI x.lower (elimE x).lower
  | e₀ => by
    unfold elimE
    split
    · rename_i x
      simpa [BExpr.lower] using (InstrsRel.base (dgBI.mk x) : InstrsRel dgBI _ _)
    · rename_i i args _
      simpa [BExpr.lower] using (elimL_rel args).append (InstrsRel.refl [i])
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.block bt (elimL_rel b)) .nil
    · rename_i bt b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (elimL_rel b)) .nil
    · rename_i bt c t e
      simpa [BExpr.lower] using (elimL_rel c).append
        (InstrsRel.cons (InstrRel.if_ bt (elimL_rel t) (elimL_rel e)) .nil)
    · rename_i bt cs b
      simpa [BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (elimL_rel b)) .nil
termination_by x => sizeOf x

theorem elimL_rel : ∀ es : List BExpr,
    InstrsRel dgBI (BExpr.lowerList es) (BExpr.lowerList (elimL es))
  | es => by
    unfold elimL
    split
    · rename_i x ys
      simpa [BExpr.lower, List.append_assoc] using
        (InstrsRel.base (dgBI.mk x) : InstrsRel dgBI _ _).append (elimL_rel ys)
    · exact .nil
    · rename_i e ys _
      simpa using (elimE_rel e).append (elimL_rel ys)
termination_by es => sizeOf es
end

theorem dropGet_bodiesRel (m : BModule) : ModuleBodiesRel dgBI m.lower (dropGet m).lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, dropGet, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, elimL_rel f.body⟩ ih

end Silmaril.Proofs.Wasm.Binaryen.DropGet
