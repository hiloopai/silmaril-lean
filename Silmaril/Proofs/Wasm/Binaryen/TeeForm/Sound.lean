module

public import Silmaril.Wasm.Binaryen.TeeForm.Defs
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Execution.Core.Sim.TeeRank

@[expose] public section

/-! # Tee formation: the forward simulation and the body relation

`tfBaseSim` has the **result** on the left, at every numerical profile. Its
`local.tee x` step (to `v; v; local.set x`) stutters, measured by `teeCodeRank`; its
`local.set x` step is matched by the original's `local.set x; local.get x`, which
reads back the value it just stored. `elimL_rel` relates every rewritten body to its
original. The reverse simulation, in which the original's intermediate state after
`local.set x` is related to the result only through the frame, and the export
equivalence at every numerical profile are in `Reverse.lean`.
-/
namespace Silmaril.Proofs.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.TeeForm

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Runtime base pairs, with the state after the tee's expansion. -/
inductive tfB : List Admin → List Admin → Prop where
  | start (x : LocalIdx) : tfB [.plain (.localTee x)] [.plain (.localSet x), .plain (.localGet x)]
  | phase (x : LocalIdx) (v : Val) :
      tfB [v.toAdmin, v.toAdmin, .plain (.localSet x)]
        [v.toAdmin, .plain (.localSet x), .plain (.localGet x)]

theorem local?_setLocal {f : Frame} {x : LocalIdx} {v : Val} (hx : x.toNat < f.locals.length) :
    (f.setLocal x v).local? x = some (some v) := by
  simp [Frame.setLocal, Frame.local?, hx]

/-- A `local.tee` after a value expands to `v; v; local.set x`. -/
private theorem tee_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {x : LocalIdx}
    {rest es' : List Admin}
    (hstep : Step P closedHost ⟨s, f, vals vs ++ .plain (.localTee x) :: rest⟩ ⟨s', f', es'⟩) :
    ∃ pre v, vs = pre ++ [v] ∧ s' = s ∧ f' = f ∧
      es' = vals pre ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
  obtain ⟨v, hargs, hc₀⟩ : ∃ v, args = [v] ∧
      c₀ = ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ :=
    SimplifyLocalsLite.head_localTee hh
  have hvs : vs = pre ++ [v] := by rw [hW, hargs]
  have hparts : s' = s ∧ f' = f ∧
      es' = vals pre ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest := by
    simpa only [hc₀, Config.mk.injEq] using he
  exact ⟨pre, v, hvs, hparts⟩

/-- A `local.set x` after a value writes it to the frame. -/
private theorem set_step_inv {s s' : Store H} {f f' : Frame} {ws : List Val} {v : Val}
    {x : LocalIdx} {rest es' : List Admin}
    (hstep : Step P closedHost
      ⟨s, f, vals (ws ++ [v]) ++ .plain (.localSet x) :: rest⟩ ⟨s', f', es'⟩) :
    x.toNat < f.locals.length ∧ s' = s ∧ f' = f.setLocal x v ∧ es' = vals ws ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
  obtain ⟨w, hargs, hx, hc₀⟩ : ∃ w, args = [w] ∧ x.toNat < f.locals.length ∧
      c₀ = ⟨s, f.setLocal x w, []⟩ :=
    SimplifyLocalsLite.head_localSet hh
  have hW' : ws ++ [v] = pre ++ [w] := by rw [← hargs]; exact hW
  obtain ⟨hpre, hw⟩ : ws = pre ∧ v = w := SingleThreaded.Det.append_singleton_inj.mp hW'
  have hparts : s' = s ∧ f' = f.setLocal x w ∧ es' = vals pre ++ rest := by
    simpa only [hc₀, Config.mk.injEq, List.append_nil] using he
  rw [hpre, hw]
  exact ⟨hx, hparts⟩

/-- The tee's expansion strictly decreases `teeCodeRank`. -/
private theorem tee_rank_lt (pre : List Val) (v : Val) (x : LocalIdx) (rest : List Admin) :
    teeCodeRank (vals pre ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest) <
      teeCodeRank (vals (pre ++ [v]) ++ [.plain (.localTee x)] ++ rest) := by
  have hv : teeAdminRank v.toAdmin = 1 := by
    cases v with
    | num n => cases n with | mk t b => cases t <;> rfl
    | vec => rfl
    | ref => rfl
  have hr : teeCodeRank [v.toAdmin, v.toAdmin, .plain (.localSet x)] <
      teeCodeRank [v.toAdmin, .plain (.localTee x)] := by
    simp only [teeCodeRank_cons, teeCodeRank_nil, hv]
    simp [teeAdminRank]
  have hctx := LawfulCodeRank.context_lt (rank := teeCodeRank) (vals pre) rest hr
  simpa [vals, List.append_assoc] using hctx

/-- The original's `local.set x; local.get x` stores the value and reads it back. -/
private theorem set_get_steps {t : Store H} {f : Frame} {vs : List Val} {v : Val}
    {x : LocalIdx} {rest' : List Admin} (hx : x.toNat < f.locals.length) :
    Relation.TransGen (Step P closedHost)
      ⟨t, f, vals vs ++ [v.toAdmin, .plain (.localSet x), .plain (.localGet x)] ++ rest'⟩
      ⟨t, f.setLocal x v, vals (vs ++ [v]) ++ rest'⟩ := by
  have h₁ : Step P closedHost
      ⟨t, f, vals vs ++ [v.toAdmin, .plain (.localSet x)] ++ (.plain (.localGet x) :: rest')⟩
      ⟨t, f.setLocal x v, vals vs ++ [] ++ (.plain (.localGet x) :: rest')⟩ :=
    Step.append_right (Step.vals_left
      (Step.variable (P := P) (host := closedHost)
        (VariableStep.localSet (s := t) (f := f) (x := x) (v := v) hx)) vs)
      (.plain (.localGet x) :: rest')
  have h₂ : Step P closedHost
      ⟨t, f.setLocal x v, vals vs ++ [.plain (.localGet x)] ++ rest'⟩
      ⟨t, f.setLocal x v, vals vs ++ [v.toAdmin] ++ rest'⟩ :=
    Step.append_right (Step.vals_left
      (Step.variable (P := P) (host := closedHost)
        (VariableStep.localGet (s := t) (x := x) (v := v) (local?_setLocal hx))) vs) rest'
  exact .tail (.single (by simpa [vals, List.append_assoc] using h₁))
    (by simpa [vals, List.append_assoc] using h₂)

theorem tfBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F tfBI tfB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | mk x => exact .start x
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | start x =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost)
            ⟨t, f, vals vs ++ [.plain (.localSet x), .plain (.localGet x)] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = t ∧ f' = f ∧
            es'' = vals vs ++ [.plain (.localSet x), .plain (.localGet x)] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++ [.plain (.localTee x)] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel tfBI tfB es' es''
      have hs : Step P closedHost ⟨s, f, vals vs ++ .plain (.localTee x) :: rest⟩ ⟨s', f', es'⟩ := by
        simpa using hstep
      obtain ⟨pre, v, hvs, hs₁, hf₁, he₁⟩ := tee_step_inv hs
      rw [hvs, hs₁, hf₁, he₁]
      refine ⟨t, vals (pre ++ [v]) ++ [.plain (.localSet x), .plain (.localGet x)] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, tee_rank_lt pre v x rest⟩, hst, ?_⟩
      simpa [vals, List.append_assoc] using
        ((AdminsRel.refl (BI := tfBI) (B := tfB) (vals pre)).append
          (AdminsRel.base (tfB.phase x v))).append hrest
    | phase x v =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost)
            ⟨t, f, vals vs ++ [v.toAdmin, .plain (.localSet x), .plain (.localGet x)] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = t ∧ f' = f ∧
            es'' = vals vs ++ [v.toAdmin, .plain (.localSet x), .plain (.localGet x)] ++ rest' ∧
            teeCodeRank es' <
              teeCodeRank (vals vs ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel tfBI tfB es' es''
      have hs : Step P closedHost
          ⟨s, f, vals ((vs ++ [v]) ++ [v]) ++ .plain (.localSet x) :: rest⟩ ⟨s', f', es'⟩ := by
        simpa [vals, List.append_assoc] using hstep
      obtain ⟨hx, hs₁, hf₁, he₁⟩ : x.toNat < f.locals.length ∧ s' = s ∧
          f' = f.setLocal x v ∧ es' = vals (vs ++ [v]) ++ rest :=
        set_step_inv hs
      rw [hs₁, hf₁, he₁]
      refine ⟨t, vals (vs ++ [v]) ++ rest', Or.inl (set_get_steps hx), hst, ?_⟩
      simpa [vals, List.append_assoc] using
        (AdminsRel.refl (BI := tfBI) (B := tfB) (vals (vs ++ [v]))).append hrest
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | start x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.localTee x)) (x' := []) rfl (by simp)
        (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk (by simpa using he)
    | phase x v =>
      exact GuardSim.not_exit (W := vs ++ [v, v]) (e₀ := .plain (.localSet x)) (x' := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa [vals, List.append_assoc] using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | start x => exact hall (.plain (.localTee x)) (by simp) rfl
    | phase x v => exact hall (.plain (.localSet x)) (by simp) rfl

/-- The leftmost-leaf replacement splits the lowering. -/
theorem headGet?_lower {x : LocalIdx} {r : BExpr} :
    ∀ {e e' : BExpr}, headGet? x r e = some e' →
      ∃ T, e.lower = [.localGet x] ++ T ∧ e'.lower = r.lower ++ T
  | e, e', h => by
    unfold headGet? at h
    split at h
    · rename_i y
      split at h
      · next hy =>
        have := beq_iff_eq.mp hy
        subst this
        cases h
        exact ⟨[], by simp [BExpr.lower], by simp⟩
      · cases h
    · rename_i i a args
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨T, h₁, h₂⟩ := headGet?_lower ha
      exact ⟨T ++ BExpr.lowerList args ++ [i], by simp [BExpr.lower, h₁],
        by simp [BExpr.lower, h₂]⟩
    · rename_i bt c cs t e
      obtain ⟨c', hc, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨T, h₁, h₂⟩ := headGet?_lower hc
      exact ⟨T ++ BExpr.lowerList cs ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)],
        by simp [BExpr.lower, h₁], by simp [BExpr.lower, h₂]⟩
    · cases h
termination_by e => sizeOf e

mutual
theorem elimE_rel : ∀ x : BExpr, InstrsRel tfBI (elimE x).lower x.lower
  | .op i args => by
    simpa [elimE, BExpr.lower] using (elimL_rel args).append (InstrsRel.refl [i])
  | .block bt b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.block bt (elimL_rel b)) .nil
  | .loop bt b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.loop bt (elimL_rel b)) .nil
  | .if_ bt c t e => by
    simpa [elimE, BExpr.lower] using (elimL_rel c).append
      (InstrsRel.cons (InstrRel.if_ bt (elimL_rel t) (elimL_rel e)) .nil)
  | .tryTable bt cs b => by
    simpa [elimE, BExpr.lower] using InstrsRel.cons (InstrRel.tryTable bt cs (elimL_rel b)) .nil
termination_by x => sizeOf x

theorem elimL_rel : ∀ es : List BExpr,
    InstrsRel tfBI (BExpr.lowerList (elimL es)) (BExpr.lowerList es)
  | es => by
    unfold elimL
    split
    · rename_i x args e ys
      split
      · next e' he =>
        obtain ⟨T, h₁, h₂⟩ := headGet?_lower he
        have := (elimL_rel args).append ((InstrsRel.base (tfBI.mk x) : InstrsRel tfBI _ _).append
          ((InstrsRel.refl T).append (elimL_rel ys)))
        simpa [BExpr.lower, h₁, h₂, List.append_assoc] using this
      · simpa [BExpr.lower, List.append_assoc] using
          ((elimL_rel args).append (InstrsRel.refl [Instr.localSet x])).append (elimL_rel (e :: ys))
    · exact .nil
    · rename_i e ys _
      simpa using (elimE_rel e).append (elimL_rel ys)
termination_by es => sizeOf es
end

theorem teeForm_bodiesRel (m : BModule) : ModuleBodiesRel tfBI (teeForm m).lower m.lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, teeForm, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, elimL_rel f.body⟩ ih

end Silmaril.Proofs.Wasm.Binaryen.TeeForm
