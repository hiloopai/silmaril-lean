module

public import Silmaril.Wasm.FnInst.Ground.Typed.Defs
public import Silmaril.Proofs.Wasm.FnInst.Ground.Sim
public import Silmaril.Wasm.Execution.Core.Sim.TypedClosure
public import Silmaril.Wasm.Execution.Core.Sim.TypedLocalBounds

@[expose] public section

/-! # The typed frame-free bridge

`gTypedSim : TypedBaseSim P F GTI GT gCodeRank` at every numerical profile and function
relation. The left side is stack-only: each of its steps is matched by stuttering
(`pairRefT_step`, as in `gBaseSim`). When it has become values, the right side runs its whole
code. That run needs the leading reads of the right side to hold values, which the typing of
the right configuration supplies (`leadRd_of_typed`): a typed active `local.get` reads a value
of the actual frame, and the configuration stays typed after the read.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-! ## Typing gives the leading reads -/

/-- A typed active `local.get x` reads a value of the actual frame. -/
theorem readable_of_typed {t : Store H} {f : Frame} {vs : List Val} {x : LocalIdx}
    {rest : List Admin} (h : ContextTyped ⟨t, f, vals vs ++ .plain (.localGet x) :: rest⟩) :
    ∃ v, f.local? x = some (some v) := by
  obtain ⟨C, it, _, _, hc, ha⟩ := h.active_admin_typed
  obtain ⟨ty, hx, _⟩ := ha.plain_inv_ne.localGet_invVar
  exact hc.set _ _ hx

theorem run_get {f : Frame} {x : LocalIdx} {v : Val} (hv : f.local? x = some (some v))
    (X : List Val) : run [.localGet x] f X = some (f, v :: X) := by
  simp only [run, step1, hv, Option.bind_some, Option.map_some]

/-- **Typing gives the leading reads**: in a typed configuration, every leading `local.get` of
the code after the values holds a value. -/
theorem leadRd_of_typed (P : Profile) :
    ∀ (b : List GInstr) {t : Store H} {f : Frame} {vs : List Val} {rest : List Admin},
      ContextTyped ⟨t, f, vals vs ++ expression (lower b) ++ rest⟩ → LeadRd b f
  | [], _, _, _, _, _ => trivial
  | .localGet x :: L, t, f, vs, rest, h => by
    have e : vals vs ++ expression (lower (.localGet x :: L)) ++ rest =
        vals vs ++ .plain (.localGet x) :: (expression (lower L) ++ rest) := by
      simp [lower, expression, GInstr.lower]
    have h₁ : ContextTyped ⟨t, f, vals vs ++ .plain (.localGet x) :: (expression (lower L) ++
        rest)⟩ := e ▸ h
    obtain ⟨v, hv⟩ := readable_of_typed h₁
    have hs : Steps P (fun _ _ _ _ => False)
        ⟨t, f, vals vs.reverse.reverse ++ expression (lower [.localGet x]) ++
          (expression (lower L) ++ rest)⟩
        ⟨t, f, vals (v :: vs.reverse).reverse ++ (expression (lower L) ++ rest)⟩ :=
      run_steps (run_get hv vs.reverse) _
    have e₂ : vals vs.reverse.reverse ++ expression (lower [.localGet x]) ++
        (expression (lower L) ++ rest) = vals vs ++ expression (lower (.localGet x :: L)) ++
          rest := by
      simp [lower, expression]
    have e₃ : vals (v :: vs.reverse).reverse ++ (expression (lower L) ++ rest) =
        vals (vs ++ [v]) ++ expression (lower L) ++ rest := by simp
    have h₂ : ContextTyped ⟨t, f, vals (vs ++ [v]) ++ expression (lower L) ++ rest⟩ :=
      e₃ ▸ h.steps (e₂ ▸ hs)
    exact ⟨⟨v, hv⟩, leadRd_of_typed P L h₂⟩
  | .const _ :: _, _, _, _, _, _ | .bin _ :: _, _, _, _, _, _ | .eqz :: _, _, _, _, _, _
  | .localSet _ :: _, _, _, _, _, _ | .localTee _ :: _, _, _, _, _, _ | .drop :: _, _, _, _, _, _
  | .nop :: _, _, _, _, _, _ => trivial

/-! ## The step law -/

/-- The conclusion of `TypedBaseSim.step`, with the typed bridge's relations and rank. -/
def StepGoalT (P : Profile) (F : FuncInst H → FuncInst H → Prop) (t s' : Store H)
    (f f' : Frame) (vs : List Val) (x y rest rest' es' : List Admin) : Prop :=
  ∃ (t' : Store H) (es'' : List Admin),
    (Relation.TransGen (Step P closedHost) ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t', f', es''⟩ ∨
      (t' = t ∧ f' = f ∧ es'' = vals vs ++ y ++ rest' ∧
        gCodeRank es' < gCodeRank (vals vs ++ x ++ rest))) ∧
    StoreRel F s' t' ∧ AdminsRel GTI GT es' es''

/-- The right side moves (or stays) to code related to the left's. -/
theorem advanceT {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs : List Val} {x y rest rest' X Z : List Admin} (hst : StoreRel F s t)
    (hXZ : AdminsRel GTI GT X Z)
    (hrun : Steps P closedHost ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t, f, Z ++ rest'⟩)
    (hrank : gCodeRank (X ++ rest) < gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel GTI GT rest rest') :
    StepGoalT P F t s f f vs x y rest rest' (X ++ rest) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hrun with he | ht
  · have hz : Z ++ rest' = vals vs ++ y ++ rest' := (Config.mk.inj he).2.2
    exact ⟨t, vals vs ++ y ++ rest', Or.inr ⟨rfl, rfl, rfl, hrank⟩, hst, hz ▸ hXZ.append hrest⟩
  · exact ⟨t, Z ++ rest', Or.inl ht, hst, hXZ.append hrest⟩

/-- A stack-only step keeps the typed pair condition. -/
theorem pairRefT_step {q r Y : List Val} {vs : List Val} {ks : List (BitVec 32)} {i : GInstr}
    {a₁ b : List GInstr} {f : Frame} (hi : i.stk = true)
    (hp : PairRefT q (ks.map GInstr.const ++ i :: a₁) r b)
    (hY : step1 i f (vs ++ q ++ kvals ks).reverse = some (f, Y)) :
    PairRefT Y.reverse a₁ (vs ++ r) b := by
  intro f₀ S res hrd h
  have hs : step1 i f₀ ((vs ++ q ++ kvals ks).reverse ++ S) = some (f₀, Y ++ S) :=
    (step1_stk hi hY).2 f₀ S
  have hrun : run (ks.map GInstr.const ++ i :: a₁) f₀ (q.reverse ++ (vs.reverse ++ S)) =
      some res := by
    rw [run_consts, run_cons]
    have e : (kvals ks).reverse ++ (q.reverse ++ (vs.reverse ++ S)) =
        (vs ++ q ++ kvals ks).reverse ++ S := by simp
    rw [e, hs]
    simpa using h
  simpa using hp f₀ (vs.reverse ++ S) res hrd hrun

/-- The left side becomes values: the right side, whose leading reads hold values, runs to
them. -/
theorem stkT_finish {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {vs r Y : List Val} {a₁ b : List GInstr} {x rest rest' : List Admin}
    (hst : StoreRel F s t) (hp' : PairRefT Y.reverse a₁ (vs ++ r) b) (hrd : LeadRd b f)
    (hop : ¬ ∃ j ∈ a₁, j.isConst = false)
    (hrank : gCodeRank (vals Y.reverse ++ (expression (lower a₁) ++ rest)) <
      gCodeRank (vals vs ++ x ++ rest))
    (hrest : AdminsRel GTI GT rest rest') :
    StepGoalT P F t s f f vs x (vals r ++ expression (lower b)) rest rest'
      (vals Y.reverse ++ expression (lower a₁) ++ rest) := by
  obtain ⟨ks₂, rfl⟩ := all_consts hop
  have hb : run b f ((vs ++ r).reverse) = some (f, (kvals ks₂).reverse ++ Y) := by
    simpa using hp' f [] _ hrd (by simpa using run_consts_only ks₂ f Y)
  have hrun := run_steps (P := P) (host := closedHost) (s := t) hb rest'
  have e : vals Y.reverse ++ expression (lower (ks₂.map GInstr.const)) =
      vals ((kvals ks₂).reverse ++ Y).reverse := by
    simp [expression_consts]
  rw [e]
  refine advanceT hst (.refl _) (by simpa using hrun) ?_ hrest
  rw [← e]
  simpa [List.append_assoc] using hrank

/-- **The step law of the typed bridge.** -/
theorem stkT_step {F : FuncInst H → FuncInst H → Prop} {s t s' : Store H} {f f' : Frame}
    {vs q r : List Val} {a b : List GInstr} {rest rest' es' : List Admin}
    (hst : StoreRel F s t) (ha : StkOp a) (hp : PairRefT q a r b)
    (hrest : AdminsRel GTI GT rest rest')
    (htyped : ContextTyped ⟨t, f, vals vs ++ (vals r ++ expression (lower b)) ++ rest'⟩)
    (hstep : Step P closedHost ⟨s, f, vals vs ++ (vals q ++ expression (lower a)) ++ rest⟩
      ⟨s', f', es'⟩) :
    StepGoalT P F t s' f f' vs (vals q ++ expression (lower a))
      (vals r ++ expression (lower b)) rest rest' es' := by
  obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
  have hiS : i.stk = true := ha.1 i (by simp)
  rw [code_split] at hstep
  obtain ⟨Y, hY, hc⟩ := step_inv ⟨Or.inl hiS, hi⟩ hstep
  obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj hc
  have hp' : PairRefT Y.reverse a₁ (vs ++ r) b := pairRefT_step hiS hp hY
  have hrank := stk_rank (a₁ := a₁) (rest := rest) hiS hi hY
  have e : vals Y.reverse ++ (expression (lower a₁) ++ rest) =
      vals Y.reverse ++ expression (lower a₁) ++ rest := (List.append_assoc _ _ _).symm
  rw [e]
  by_cases hop : ∃ j ∈ a₁, j.isConst = false
  · have hB : GT (vals Y.reverse ++ expression (lower a₁)) (vals vs ++ (vals r ++
        expression (lower b))) :=
      ⟨Y.reverse, a₁, vs ++ r, b, rfl, by simp,
        ⟨fun j hj => ha.1 j (by simp [hj]), hop⟩, hp'⟩
    exact advanceT hst (.base hB) .refl (by simpa using hrank) hrest
  · have ht' : ContextTyped ⟨t, f', vals (vs ++ r) ++ expression (lower b) ++ rest'⟩ := by
      simpa only [vals_append, List.append_assoc] using htyped
    exact stkT_finish hst hp' (leadRd_of_typed P b ht') hop hrank hrest

/-- Every left side has a non-value head that the bridge can invert. -/
theorem gt_head {x y : List Admin} (h : GT x y) (vs : List Val) :
    ∃ W i R, Inv i ∧ vals vs ++ x = vals W ++ .plain i.lower :: R := by
  obtain ⟨q, a, r, b, rfl, -, ha, -⟩ := h
  obtain ⟨ks, i, a₁, rfl, hi⟩ := split_op ha.2
  refine ⟨vs ++ q ++ kvals ks, i, expression (lower a₁), ⟨Or.inl (ha.1 i (by simp)), hi⟩, ?_⟩
  simpa using code_split vs q ks i a₁ []

/-- **The typed bridge**: typed pairs satisfy silmaril's typed base obligations, at every
numerical profile, for every function relation. -/
theorem gTypedSim {F : FuncInst H → FuncInst H → Prop} :
    TypedBaseSim P F GTI GT gCodeRank where
  facts := {
    src := by
      rintro x y ⟨a, b, ⟨ha, href⟩, rfl, rfl⟩
      exact ⟨[], a, [], b, rfl, rfl, ha, fun f S res hrd h => href f S res hrd h⟩
    exit := by
      intro s t f vs us x y k j hst hxy hk he
      obtain ⟨W, i, R, hi, hW⟩ := gt_head hxy vs
      exact absurd (hW.symm.trans he) (fun h => not_exit_lower hi.2 hk h)
    values := by
      intro s t f vs us x y hst hxy hx
      exfalso
      obtain ⟨W, i, R, hi, hW⟩ := gt_head hxy vs
      have hm : Admin.plain i.lower ∈ vals (vs ++ us) := by
        rw [vals_append, ← hx, hW]
        simp
      exact SingleThreaded.Det.mem_vals hm (lower_val hi.2) }
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest htyped hstep
    obtain ⟨q, a, r, b, rfl, rfl, ha, hp⟩ := hxy
    exact stkT_step hst ha hp hrest htyped hstep

end Silmaril.Wasm.FnInst.Ground
