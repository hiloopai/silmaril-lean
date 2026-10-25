module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.DetLift
public import Silmaril.Wasm.Binaryen.Pass.SimplifyLocalsLite

@[expose] public section

/-! # SimplifyLocals-lite: tee-drop as a one-way code simulation and the determinism lift

`SimplifyLocalsLite.teeDrop` (`Pass/SimplifyLocalsLite.lean`) rewrites
`drop (local.tee x v)` into `local.set x v` in functions with scalar/SIMD locals;
reference-local bodies are preserved. The traversal lemmas cover both kinds of locals.
The base pairs put the **set on the left** (the rewritten module):

* source `tdBI`: `[local.set x]` ~ `[local.tee x, drop]`;
* runtime `tdB`: the same over administrative instructions.

`tdBaseSim` is a `BaseSim` for every profile, host and store relation: when the left side
runs `v; local.set x`, the right side runs `v; local.tee x` to `v; v; local.set x`, the
set (to the same frame) and `v; drop`. The other direction has no frame-equal `BaseSim`
(the tee expansion keeps the frame and grows the code,
`no_baseSim_teeDrop`); it comes from the determinism lift
`DetLift.exportRefines_symm_of_hosts`, which needs the one-way refinement under
`closedHost`, `divHost` and `trapHost` (all three respect every function relation).
-/

namespace Silmaril.Wasm.Binaryen.SimplifyLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Base relations -/

/-- Source base pairs: `local.set x` (rewritten) against `local.tee x; drop` (original). -/
def tdBI (a b : List Instr) : Prop := ∃ x, a = [.localSet x] ∧ b = [.localTee x, .drop]

/-- Runtime base pairs. -/
def tdB (a b : List Admin) : Prop :=
  ∃ x, a = [.plain (.localSet x)] ∧ b = [.plain (.localTee x), .plain .drop]

/-! ## Inverting the step of `local.set` -/

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `val* v local.set x` steps only to `val*`, with the local set (in bounds). (The
inversion of the local-store simulation lemma `step_set_inv`, also returning the bound.) -/
theorem step_set_inv {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (x : LocalIdx), c.code = vals us ++ [.plain (.localSet x)] →
      ∃ (us₀ : List Val) (v : Val), us = us₀ ++ [v] ∧ c'.store = c.store ∧
        c'.frame = c.frame.setLocal x v ∧ c'.code = vals us₀ ∧
        x.toNat < c.frame.locals.length := by
  induction h with
  | parametric hp =>
    intro us x hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | numeric hp | vector hp =>
    intro us x hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | «variable» hp =>
    intro us x hc
    cases hp with
    | @localSet s f y v hx =>
      have hl := congrArg List.getLast? hc
      simp at hl
      subst hl
      have h₁ : [v.toAdmin] = vals us := by
        have := congrArg List.dropLast hc
        simpa using this
      obtain ⟨w, rfl⟩ : ∃ w, us = [w] := by
        have hl := congrArg List.length h₁
        simp only [List.length_singleton, vals_length] at hl
        match us, hl with
        | [w], _ => exact ⟨w, rfl⟩
      have : v = w := by
        have h₂ : v.toAdmin = w.toAdmin := by simpa [vals] using h₁
        have := congrArg Admin.val? h₂
        simpa using this
      subst this
      exact ⟨[], v, rfl, rfl, rfl, rfl, hx⟩
    | _ =>
      have hl := congrArg List.getLast? hc
      simp [constI32] at hl
  | table hp | memory hp | reference hp | aggregate hp =>
    intro us x hc
    have hl := congrArg List.getLast? hc
    cases hp <;> simp [constI32] at hl
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro us x hc
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    dsimp only at hc ⊢
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) =
        vals us ++ Admin.plain (.localSet x) :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨us₀, v, rfl, h1, h2, h3, h4⟩ := ih vs₁ x (by simp)
    dsimp only at h1 h2 h3 h4
    refine ⟨vs₀ ++ us₀, v, by simp, h1, h2, ?_, h4⟩
    rw [h3]
    simp
  | @trapInstrs s f vs₀ rest hne =>
    intro us x hc
    have hc' : vals vs₀ ++ Admin.trap :: rest =
        vals us ++ Admin.plain (.localSet x) :: [] := by rw [← hc]; simp
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us x hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain (.localSet x) :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨-, h, -⟩ := vals_append_cons_inj rfl rfl hc'
    cases h
  | _ =>
    intro us x hc
    have hl := congrArg List.getLast? hc
    simp [constI32] at hl
    all_goals (subst hl; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef])

/-- An exit kernel holds no `local.set`. -/
theorem exit_not_set {k : List Admin} (hk : Exit k) (x : LocalIdx) :
    ∀ a ∈ k, a ≠ .plain (.localSet x) := by
  cases hk with
  | @returnCallRef c hc =>
    intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    rintro rfl
    simp [Admin.IsReturnCallRef] at hc
  | _ => simp [throwing]

/-! ## The simulation: the set on the left -/

/-- **One-way simulation**: the left side holds the set, the right side the tee and
the drop. -/
theorem tdBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F tdBI tdB where
  src := by
    rintro _ _ ⟨x, rfl, rfl⟩
    exact ⟨x, rfl, rfl⟩
  step := by
    intro s t s' f f' vs a b rest rest' es' hst hab hrest hstep
    obtain ⟨x, rfl, rfl⟩ := hab
    have heq : vals vs ++ [Admin.plain (.localSet x)] ++ rest =
        vals vs ++ Admin.plain (.localSet x) :: rest := by simp
    rw [heq] at hstep
    rcases Step.split_head rfl hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨us₀, v, rfl, h1, h2, h3, hx⟩ := step_set_inv hs1 us x rfl
      dsimp only at h1 h2 h3 hx
      subst h1 h2 h3 hV
      have s1 : Step P host
          ⟨t, f, vals (ws ++ us₀) ++ [v.toAdmin, .plain (.localTee x)] ++ (.plain .drop :: rest')⟩
          ⟨t, f, vals (ws ++ us₀) ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++
            (.plain .drop :: rest')⟩ :=
        Step.ctxtInstrs (Step.variable VariableStep.localTee) (Or.inr (by simp))
      have s2 : Steps P host
          ⟨t, f, vals (ws ++ us₀ ++ [v]) ++ [v.toAdmin, .plain (.localSet x)] ++
            (.plain .drop :: rest')⟩
          ⟨t, f.setLocal x v, vals (ws ++ us₀ ++ [v]) ++ [] ++ (.plain .drop :: rest')⟩ :=
        Steps.ctxtInstrs (Relation.ReflTransGen.single (Step.variable (VariableStep.localSet hx)))
      have s3 : Steps P host
          ⟨t, f.setLocal x v, vals (ws ++ us₀) ++ [v.toAdmin, .plain .drop] ++ rest'⟩
          ⟨t, f.setLocal x v, vals (ws ++ us₀) ++ [] ++ rest'⟩ :=
        Steps.ctxtInstrs (Relation.ReflTransGen.single (Step.parametric (ParametricStep.drop v)))
      refine ⟨t, vals (ws ++ us₀) ++ rest', Or.inl ?_, hst, ?_⟩
      · have e2 : vals (ws ++ us₀) ++ [v.toAdmin, v.toAdmin, .plain (.localSet x)] ++
            (.plain .drop :: rest') =
            vals (ws ++ us₀ ++ [v]) ++ [v.toAdmin, .plain (.localSet x)] ++
              (.plain .drop :: rest') := by simp [vals]
        have e3 : vals (ws ++ us₀ ++ [v]) ++ [] ++ (.plain .drop :: rest') =
            vals (ws ++ us₀) ++ [v.toAdmin, .plain .drop] ++ rest' := by simp [vals]
        have hrun := Relation.TransGen.head' s1
          ((Closure.steps_congr s2 e2.symm e3).trans s3)
        exact Closure.transGen_congr hrun (by simp [vals]) (by simp)
      · have e : vals ws ++ vals us₀ ++ rest = vals (ws ++ us₀) ++ rest := by simp
        rw [e]
        exact AdminsRel.append (AdminsRel.refl _) hrest
    · cases h
    · cases h
  exit := by
    intro s t f vs us a b k j hst hab hk he
    exfalso
    obtain ⟨x, rfl, rfl⟩ := hab
    obtain ⟨pre, e, hen, rfl⟩ := hk.eq_vals_append
    have h1 : vals vs ++ Admin.plain (.localSet x) :: [] = vals (us ++ pre) ++ e :: j := by
      simpa using he
    obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h1
    exact exit_not_set hk x _ (by simp) rfl
  values := by
    intro s t f vs us a b hst hab ha
    exfalso
    obtain ⟨x, rfl, -⟩ := hab
    have hmem : Admin.plain (.localSet x) ∈ vals us := by rw [← ha]; simp
    obtain ⟨v, -, hv⟩ := List.mem_map.mp hmem
    have := congrArg Admin.val? hv
    rw [Admin.val?_toAdmin] at this
    cases this

/-! ## The three hosts respect every function relation -/

theorem closedHost_respects (F : FuncInst H → FuncInst H → Prop) :
    HostRespects F (closedHost (H := H)) :=
  fun _ _ _ _ _ _ h => h.elim

theorem divHost_respects (F : FuncInst H → FuncInst H → Prop) :
    HostRespects F (SingleThreaded.divHost (H := H)) := by
  intro h s t vs out hst hout
  subst hout
  exact ⟨.diverged, rfl, trivial⟩

theorem trapHost_respects (F : FuncInst H → FuncInst H → Prop) :
    HostRespects F (DetLift.trapHost (H := H)) := by
  intro h s t vs out hst hout
  subst hout
  exact ⟨.returned t .trap, rfl, hst, rfl⟩

/-! ## The pass relates every body to its original -/

mutual
theorem tdE_rel : ∀ e : BExpr, InstrsRel tdBI (tdE e).lower e.lower
  | .op i args => by
    unfold tdE
    split
    · next x v =>
      have h := InstrsRel.append (tdE_rel v) (InstrsRel.base (BI := tdBI) ⟨x, rfl, rfl⟩)
      simpa [BExpr.lower] using h
    · simpa [BExpr.lower] using InstrsRel.append (tdL_rel args) (InstrsRel.refl [i])
  | .block bt b => by
    simpa [tdE, BExpr.lower] using InstrsRel.cons (.block bt (tdL_rel b)) InstrsRel.nil
  | .loop bt b => by
    simpa [tdE, BExpr.lower] using InstrsRel.cons (.loop bt (tdL_rel b)) InstrsRel.nil
  | .tryTable bt cs b => by
    simpa [tdE, BExpr.lower] using InstrsRel.cons (.tryTable bt cs (tdL_rel b)) InstrsRel.nil
  | .if_ bt c t e => by
    simpa [tdE, BExpr.lower] using
      InstrsRel.append (tdL_rel c) (InstrsRel.cons (.if_ bt (tdL_rel t) (tdL_rel e)) InstrsRel.nil)
termination_by e => sizeOf e
theorem tdL_rel : ∀ es : List BExpr,
    InstrsRel tdBI (BExpr.lowerList (tdL es)) (BExpr.lowerList es)
  | [] => InstrsRel.nil
  | e :: es => by simpa [tdL] using InstrsRel.append (tdE_rel e) (tdL_rel es)
termination_by es => sizeOf es
end

/-! ## Typing -/

/-- `local.set x` may replace `local.tee x; drop` (in every typing). -/
theorem tyRepl_teeDrop (x : LocalIdx) : TyRepl [.localTee x, .drop] [.localSet x] := by
  intro C it hC hX
  obtain ⟨m, xs₁, xs₂, h₁, h₂, hL⟩ :=
    InstrsOk.split (is₁ := [.localTee x]) (is₂ := [.drop]) hC hX rfl
  have hreg := InstrsOk.regular hC hX
  have r₁ := InstrsOk.regular hC h₁
  obtain ⟨ts₁, it₁, hts₁, hi₁, hs₁⟩ := single_inv' hC h₁
  obtain ⟨ts₂, it₂, hts₂, hi₂, hs₂⟩ := single_inv' (hC.initLocals _) h₂
  simp only [Context.initLocals_toTypeCtx] at hts₂
  cases hi₁ with
  | «variable» hv =>
    cases hv with
    | @localTee _ i t hloc =>
      cases hi₂ with
      | parametric hp =>
        cases hp with
        | drop hu =>
          rename_i u
          have hset : InstrsOk C [.localSet x] ⟨ts₁ ++ [t], [x.toNat], ts₁ ++ []⟩ :=
            .frame (.instr (.variable (.localSet hloc))) hts₁
          refine .sub hset ⟨hs₁.1, ?_, ?_⟩ hreg
          · have hm : ResultSub C.toTypeCtx (ts₁ ++ [t]) (ts₂ ++ [u]) :=
              ResultSub.trans hC.types r₁.2.1 hs₁.2.1 (by simpa using hs₂.1)
            have hl := resultSub_length hm
            simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
            have h12 := (resultSub_append_inv hm hl).1
            simpa using ResultSub.trans hC.types hts₂ h12 (by simpa using hs₂.2.1)
          · intro y hy hn
            obtain ⟨lt, hlt⟩ := hreg.2.2 y hy
            have h2 := hL.set (Context.initLocals_set_of_mem hy hlt)
            rcases Context.initLocals_set h2 with hm | hm
            · rcases List.mem_append.mp hm with hm | hm
              · exact hs₁.2.2 y hm hn
              · obtain ⟨t', ht'⟩ := hs₂.2.2 y hm (by simp)
                rcases Context.initLocals_set ht' with hm' | hm'
                · exact hs₁.2.2 y hm' hn
                · exact ⟨_, hm'⟩
            · exact ⟨_, hm⟩
      | _ => rename_i h; cases h
  | _ => rename_i h; cases h

mutual
theorem tdE_typed : ∀ e : BExpr, TyRepl e.lower (tdE e).lower
  | .op i args => by
    unfold tdE
    split
    · next x v =>
      have h := TyRepl.append (tdE_typed v) (tyRepl_teeDrop x)
      simpa [BExpr.lower] using h
    · simpa using TyRepl.append_right (tdL_typed args) [i]
  | .block bt b => by simpa [tdE, BExpr.lower] using TyRepl.block (tdL_typed b) bt
  | .loop bt b => by simpa [tdE, BExpr.lower] using TyRepl.loop (tdL_typed b) bt
  | .tryTable bt cs b => by simpa [tdE, BExpr.lower] using TyRepl.tryTable (tdL_typed b) bt cs
  | .if_ bt c t e => by
    simpa [tdE, BExpr.lower] using
      TyRepl.append (tdL_typed c) (TyRepl.if_ (tdL_typed t) (tdL_typed e) bt)
termination_by e => sizeOf e
theorem tdL_typed : ∀ es : List BExpr,
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (tdL es))
  | [] => TyRepl.refl _
  | e :: es => by simpa [tdL] using TyRepl.append (tdE_typed e) (tdL_typed es)
termination_by es => sizeOf es
end

/-! ## Modules -/

theorem teeDrop_ok {m : BModule} (hm : m.Ok) : (teeDrop m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [teeDrop]) fun i _ _ => by
    simp only [teeDrop, List.getElem_map]
    refine ⟨rfl, rfl, fun C ts hC hb => ?_⟩
    dsimp only
    split
    · exact tdL_typed _ C _ hC hb
    · exact hb

theorem teeDrop_bodiesRel (m : BModule) :
    ModuleBodiesRel tdBI (teeDrop m).lower m.lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, teeDrop, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih =>
    refine .cons ⟨rfl, rfl, ?_⟩ ih
    change InstrsRel tdBI (BExpr.lowerList
      (if f.locals.all profileLocalType then tdL f.body else f.body)) (BExpr.lowerList f.body)
    split
    · exact tdL_rel f.body
    · exact InstrsRel.refl _

/-- The one-way refinement, for every host respecting the function relation. -/
theorem teeDrop_refines {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostRespects (FuncRel tdBI) host) :
    ExportRefines (· = ·) P host (teeDrop m).lower m.lower :=
  exportRefines_of_bodiesRel tdBaseSim hhost (teeDrop_bodiesRel m) (teeDrop_ok hm) hm

/-- **Tee-drop is export equivalent** under the deterministic profile and the closed
host: the one-way simulation and the determinism lift. -/
theorem teeDrop_sound {o : GrowKind → Nat → Nat → Nat → Bool} {m : BModule} (hm : m.Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (teeDrop m).lower
      m.lower :=
  ⟨teeDrop_refines hm _ (closedHost_respects _),
    (DetLift.exportRefines_symm_of_hosts (teeDrop_refines hm _ (closedHost_respects _))
      (teeDrop_refines hm _ (divHost_respects _)) (teeDrop_refines hm _ (trapHost_respects _))
      (fun _ _ _ _ hI =>
        let ⟨c', hc', _⟩ := instantiate_bodiesRel (teeDrop_bodiesRel m) hm hI
        ⟨c', hc'⟩)).mono fun _ _ h => h.symm⟩

end Silmaril.Wasm.Binaryen.SimplifyLocalsLite
