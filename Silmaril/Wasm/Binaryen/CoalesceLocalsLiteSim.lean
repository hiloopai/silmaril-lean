module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.DetLift
public import Silmaril.Wasm.Binaryen.VacuumLiteSim
public import Silmaril.Wasm.Binaryen.Pass.CoalesceLocalsLite

@[expose] public section

/-! # CoalesceLocals-lite: a one-way code simulation and the determinism lift

`CoalesceLocalsLite.deadSetLite` (`Pass/CoalesceLocalsLite.lean`) rewrites
`local.set x v; local.set x (const c)` into `drop v; local.set x (const c)`. The base
pairs put the **rewritten code on the left**:

* source `dsBI`: `[drop, k, local.set x]` ~ `[local.set x, k, local.set x]` (`k` a constant);
* runtime `dsB`: the same over administrative instructions, and the state after the
  left side dropped the value, `[w, local.set x]` ~ `[u, local.set x, w, local.set x]`.

`dsBaseSim` is a `BaseSim` for every profile, host and store relation: the left `drop`
is matched by a stutter of the right side (frame and store do not change), and the left
store of `w` by both stores of the right side, which reach the same frame
(`Frame.setLocal_setLocal`). The other direction has no frame-equal `BaseSim` (the dead
store changes the frame of the original side alone); it comes from the determinism
lift `DetLift.exportRefines_symm_of_hosts`, as for tee-drop.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics
open VacuumLite (constInstr constInstr_val step_drop_inv exit_not_unit)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Base relations -/

/-- Source base pairs: `drop; k; local.set x` (rewritten) against
`local.set x; k; local.set x` (original), `k` a constant. -/
def dsBI (a b : List Instr) : Prop :=
  ∃ x k, constInstr k = true ∧ a = [.drop, k, .localSet x] ∧ b = [.localSet x, k, .localSet x]

/-- Runtime base pairs: the lowered source pairs, and the state after the drop. -/
def dsB (a b : List Admin) : Prop :=
  ∃ (x : LocalIdx) (w : Val),
    (a = [.plain .drop, w.toAdmin, .plain (.localSet x)] ∧
      b = [.plain (.localSet x), w.toAdmin, .plain (.localSet x)]) ∨
    (∃ u : Val, a = [w.toAdmin, .plain (.localSet x)] ∧
      b = [u.toAdmin, .plain (.localSet x), w.toAdmin, .plain (.localSet x)])

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

theorem Frame.setLocal_setLocal (f : Frame) (x : LocalIdx) (u w : Val) :
    (f.setLocal x u).setLocal x w = f.setLocal x w := by
  simp [Frame.setLocal, List.set_set]

/-! ## The simulation: the rewritten code on the left -/

/-- The right side runs both stores: `u; set x; w; set x` reaches the frame of `w; set x`. -/
theorem run_both {t : Store H} {f : Frame} {x : LocalIdx} (hx : x.toNat < f.locals.length)
    (u w : Val) (vs : List Val) (rest : List Admin) :
    Relation.TransGen (Step P host)
      ⟨t, f, vals vs ++ [u.toAdmin, .plain (.localSet x), w.toAdmin, .plain (.localSet x)] ++ rest⟩
      ⟨t, f.setLocal x w, vals vs ++ rest⟩ := by
  have hx' : x.toNat < (f.setLocal x u).locals.length := by simpa [Frame.setLocal] using hx
  have s1 : Step P host
      ⟨t, f, vals vs ++ [u.toAdmin, .plain (.localSet x)] ++
        ([w.toAdmin, .plain (.localSet x)] ++ rest)⟩
      ⟨t, f.setLocal x u, vals vs ++ [] ++ ([w.toAdmin, .plain (.localSet x)] ++ rest)⟩ :=
    Step.ctxtInstrs (Step.variable (VariableStep.localSet hx)) (Or.inr (by simp))
  have s2 : Steps P host
      ⟨t, f.setLocal x u, vals vs ++ [w.toAdmin, .plain (.localSet x)] ++ rest⟩
      ⟨t, (f.setLocal x u).setLocal x w, vals vs ++ [] ++ rest⟩ :=
    Steps.ctxtInstrs (Relation.ReflTransGen.single (Step.variable (VariableStep.localSet hx')))
  rw [Frame.setLocal_setLocal] at s2
  have s2' : Steps P host
      ⟨t, f.setLocal x u, vals vs ++ [] ++ ([w.toAdmin, .plain (.localSet x)] ++ rest)⟩
      ⟨t, f.setLocal x w, vals vs ++ rest⟩ := Closure.steps_congr s2 (by simp) (by simp)
  exact Closure.transGen_congr (Relation.TransGen.head' s1 s2') (by simp) rfl

/-- **One-way simulation**: the left side holds the drop, the right side the dead store. -/
theorem dsBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F dsBI dsB where
  src := by
    rintro _ _ ⟨x, k, hk, rfl, rfl⟩
    obtain ⟨w, hw⟩ := constInstr_val hk
    exact ⟨x, w, Or.inl ⟨by simp [Execution.Core.expression, hw],
      by simp [Execution.Core.expression, hw]⟩⟩
  step := by
    intro s t s' f f' vs a b rest rest' es' hst hab hrest hstep
    obtain ⟨x, w, ⟨rfl, rfl⟩ | ⟨u, rfl, rfl⟩⟩ := hab
    · -- the left side drops the value: the right side stutters
      have heq : vals vs ++ [Admin.plain .drop, w.toAdmin, .plain (.localSet x)] ++ rest =
          vals vs ++ Admin.plain .drop :: (w.toAdmin :: .plain (.localSet x) :: rest) := by simp
      rw [heq] at hstep
      rcases Step.split_head rfl hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · obtain ⟨us₀, v, rfl, h1, h2, h3⟩ := step_drop_inv hs1 us rfl
        dsimp only at h1 h2 h3
        subst h1 h2 h3 hV
        refine ⟨t, vals (ws ++ us₀ ++ [v]) ++
            [.plain (.localSet x), w.toAdmin, .plain (.localSet x)] ++ rest',
          Or.inr ⟨rfl, rfl, by simp, ?_⟩, hst, ?_⟩
        · have := codeSize_lt_of_infix (vals (ws ++ us₀))
            [v.toAdmin, Admin.plain .drop] (w.toAdmin :: .plain (.localSet x) :: rest) (by simp)
          simpa [vals] using this
        · have e1 : vals ws ++ vals us₀ ++ (w.toAdmin :: Admin.plain (.localSet x) :: rest) =
              vals (ws ++ us₀) ++ [w.toAdmin, .plain (.localSet x)] ++ rest := by simp
          have e2 : vals (ws ++ us₀ ++ [v]) ++
              [Admin.plain (.localSet x), w.toAdmin, .plain (.localSet x)] ++ rest' =
              vals (ws ++ us₀) ++
                [v.toAdmin, .plain (.localSet x), w.toAdmin, .plain (.localSet x)] ++ rest' := by
            simp [vals]
          rw [e1, e2]
          exact AdminsRel.append (AdminsRel.append (.refl _) (.base ⟨x, w, Or.inr ⟨v, rfl, rfl⟩⟩))
            hrest
      · cases h
      · cases h
    · -- the left side stores `w`: the right side runs both stores
      have heq : vals vs ++ [w.toAdmin, Admin.plain (.localSet x)] ++ rest =
          vals (vs ++ [w]) ++ Admin.plain (.localSet x) :: rest := by simp [vals]
      rw [heq] at hstep
      rcases Step.split_head rfl hstep with ⟨ws, us, is', hV, hs1, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · obtain ⟨us₀, w', rfl, h1, h2, h3, hx⟩ := step_set_inv hs1 us x rfl
        dsimp only at h1 h2 h3 hx
        subst h1 h2 h3
        obtain ⟨rfl, rfl⟩ : vs = ws ++ us₀ ∧ w = w' := by
          have := hV
          rw [← List.append_assoc] at this
          exact List.append_inj' this rfl |>.imp id (fun h => by simpa using h)
        refine ⟨t, vals (ws ++ us₀) ++ rest', Or.inl ?_, hst, ?_⟩
        · exact run_both hx u w (ws ++ us₀) rest'
        · have e : vals ws ++ vals us₀ ++ rest = vals (ws ++ us₀) ++ rest := by simp
          rw [e]
          exact AdminsRel.append (AdminsRel.refl _) hrest
      · cases h
      · cases h
  exit := by
    intro s t f vs us a b k j hst hab hk he
    exfalso
    obtain ⟨pre, e, hen, rfl⟩ := hk.eq_vals_append
    have hmem : e ∈ vals pre ++ [e] := by simp
    obtain ⟨x, w, ⟨rfl, -⟩ | ⟨u, rfl, -⟩⟩ := hab
    · have h1 : vals vs ++ Admin.plain .drop :: [w.toAdmin, .plain (.localSet x)] =
          vals (us ++ pre) ++ e :: j := by simpa using he
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h1
      exact (exit_not_unit hk _ hmem).2 rfl
    · have h1 : vals (vs ++ [w]) ++ Admin.plain (.localSet x) :: [] =
          vals (us ++ pre) ++ e :: j := by simpa [vals] using he
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj rfl hen h1
      exact exit_not_set hk x _ hmem rfl
  values := by
    intro s t f vs us a b hst hab ha
    exfalso
    obtain ⟨x, w, ⟨rfl, -⟩ | ⟨u, rfl, -⟩⟩ := hab
    all_goals
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

theorem overwrites_eq {x : LocalIdx} {e : BExpr} (h : overwrites x e = true) :
    ∃ k, constInstr k = true ∧ e = .op (.localSet x) [.op k []] := by
  unfold overwrites at h
  split at h
  · next y k =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hk⟩ := h
    exact ⟨k, hk, rfl⟩
  · cases h

mutual
theorem dsE_rel : ∀ e : BExpr, InstrsRel dsBI (dsE e).lower e.lower
  | .op i args => by
    simpa [dsE, BExpr.lower] using InstrsRel.append (dsL_rel args) (InstrsRel.refl [i])
  | .block bt b => by
    simpa [dsE, BExpr.lower] using InstrsRel.cons (.block bt (dsL_rel b)) InstrsRel.nil
  | .loop bt b => by
    simpa [dsE, BExpr.lower] using InstrsRel.cons (.loop bt (dsL_rel b)) InstrsRel.nil
  | .tryTable bt cs b => by
    simpa [dsE, BExpr.lower] using InstrsRel.cons (.tryTable bt cs (dsL_rel b)) InstrsRel.nil
  | .if_ bt c t e => by
    simpa [dsE, BExpr.lower] using
      InstrsRel.append (dsL_rel c) (InstrsRel.cons (.if_ bt (dsL_rel t) (dsL_rel e)) InstrsRel.nil)
termination_by e => sizeOf e
theorem dsL_rel : ∀ es : List BExpr,
    InstrsRel dsBI (BExpr.lowerList (dsL es)) (BExpr.lowerList es)
  | [] => InstrsRel.nil
  | [e] => by simpa [dsL] using dsE_rel e
  | e :: e₂ :: es => by
    have ht := dsL_rel (e₂ :: es)
    unfold dsL
    split
    · next x v =>
      split
      · next hw =>
        obtain ⟨k, hk, rfl⟩ := overwrites_eq hw
        have h := InstrsRel.append (InstrsRel.append (dsE_rel v)
          (InstrsRel.base (BI := dsBI) ⟨x, k, hk, rfl, rfl⟩)) (dsL_rel es)
        simpa [BExpr.lower] using h
      · have h := InstrsRel.append (InstrsRel.append (dsE_rel v) (InstrsRel.refl [.localSet x])) ht
        simpa [BExpr.lower] using h
    · simpa using InstrsRel.append (dsE_rel e) ht
termination_by es => sizeOf es
end

/-! ## Typing -/

/-- A constant has one typing, in every context. -/
theorem const_ok {k : Instr} (hk : constInstr k = true) {C : Context} {it : InstrType}
    (h : InstrOk C k it) : ∃ t, it = .plain [] [t] ∧ ∀ C' : Context, InstrOk C' k (.plain [] [t]) := by
  cases k <;> simp [constInstr] at hk
  · cases h with
    | numeric h => cases h; exact ⟨_, rfl, fun _ => .numeric (.intConst _ _)⟩
    | _ => rename_i h; cases h
  · cases h with
    | numeric h => cases h; exact ⟨_, rfl, fun _ => .numeric (.floatConst _ _)⟩
    | _ => rename_i h; cases h
  · cases h with
    | vector h => cases h; exact ⟨_, rfl, fun _ => .vector (.vecConst _)⟩
    | _ => rename_i h; cases h

/-- A local that a typed sequence claims to initialise is in one of its split parts, or
already set. -/
theorem inits_split {C : Context} {it : InstrType} {a b : List Nat} (hreg : InstrTypeOk C it)
    (hL : LocalsLe (C.initLocals it.inits).locals (C.initLocals (a ++ b)).locals) {y : Nat}
    (hy : y ∈ it.inits) : y ∈ a ∨ y ∈ b ∨ ∃ t, C.locals[y]? = some ⟨.set, t⟩ := by
  obtain ⟨lt, hlt⟩ := hreg.2.2 y hy
  rcases Context.initLocals_set (hL.set (Context.initLocals_set_of_mem hy hlt)) with h | h
  · rcases List.mem_append.mp h with h | h
    exacts [.inl h, .inr (.inl h)]
  · exact .inr (.inr ⟨_, h⟩)

/-- Set after `initLocals xs`, where the members of `xs` are already set: set. -/
theorem set_of_initLocals {C : Context} {xs : List Nat} {y : Nat}
    (h : ∃ t, (C.initLocals xs).locals[y]? = some ⟨.set, t⟩)
    (hxs : y ∈ xs → ∃ t, C.locals[y]? = some ⟨.set, t⟩) : ∃ t, C.locals[y]? = some ⟨.set, t⟩ := by
  obtain ⟨t, h⟩ := h
  rcases Context.initLocals_set h with h | h
  exacts [hxs h, ⟨t, h⟩]

theorem initLocals_type {C : Context} {xs : List Nat} {y : Nat} {i : Init} {t : CValType}
    (h : (C.initLocals xs).locals[y]? = some ⟨i, t⟩) : ∃ i', C.locals[y]? = some ⟨i', t⟩ := by
  rw [Context.initLocals_locals] at h
  split at h
  · cases hc : C.locals[y]? with
    | none => simp [hc] at h
    | some lt =>
      simp only [hc, Option.map_some, Option.some.injEq, LocalType.mk.injEq] at h
      exact ⟨lt.init, by rw [← h.2]⟩
  · exact ⟨i, h⟩

/-- The typing of `local.set x`. -/
theorem set_ok {C : Context} {x : LocalIdx} {it : InstrType} (h : InstrOk C (.localSet x) it) :
    ∃ i t, C.locals[x.toNat]? = some ⟨i, t⟩ ∧ it = ⟨[t], [x.toNat], []⟩ := by
  cases h with
  | «variable» h => cases h with | localSet h => exact ⟨_, _, h, rfl⟩
  | _ => rename_i h; cases h

set_option maxHeartbeats 1000000 in
/-- `drop` may replace a `local.set x` that the next constant store to `x` overwrites. -/
theorem tyRepl_deadSet (x : LocalIdx) {k : Instr} (hk : constInstr k = true) :
    TyRepl [.localSet x, k, .localSet x] [.drop, k, .localSet x] := by
  intro C it hC hX
  have hreg := InstrsOk.regular hC hX
  obtain ⟨m, xs₁, xs₂, h₁, h₂, hL⟩ :=
    InstrsOk.split (is₁ := [.localSet x]) (is₂ := [k, .localSet x]) hC hX rfl
  have hC₁ := hC.initLocals xs₁
  obtain ⟨m', ys₁, ys₂, h₂₁, h₂₂, hL₂⟩ :=
    InstrsOk.split (is₁ := [k]) (is₂ := [.localSet x]) hC₁ h₂ rfl
  have hC₂ := hC₁.initLocals ys₁
  have r₁ := InstrsOk.regular hC h₁
  have r₂ := InstrsOk.regular hC₁ h₂
  have r₂₁ := InstrsOk.regular hC₁ h₂₁
  have r₂₂ := InstrsOk.regular hC₂ h₂₂
  obtain ⟨ts₁, it₁, hts₁, hi₁, hs₁⟩ := single_inv' hC h₁
  obtain ⟨ts₂, it₂, hts₂, hi₂, hs₂⟩ := single_inv' hC₁ h₂₁
  obtain ⟨ts₃, it₃, hts₃, hi₃, hs₃⟩ := single_inv' hC₂ h₂₂
  simp only [Context.initLocals_toTypeCtx] at hts₂ hts₃
  have ri₁ := InstrOk.regular hC hi₁
  obtain ⟨tk, rfl, hkC⟩ := const_ok hk hi₂
  obtain ⟨i, t, hloc, rfl⟩ := set_ok hi₁
  obtain ⟨i₃, t₃, hloc₃, rfl⟩ := set_ok hi₃
  obtain ⟨i₃'', hloc₃''⟩ := initLocals_type hloc₃
  obtain ⟨i₃', hloc₃'⟩ := initLocals_type hloc₃''
  rw [hloc] at hloc₃'
  obtain ⟨-, rfl⟩ := LocalType.mk.inj (Option.some.inj hloc₃')
  obtain ⟨hs₁p, hs₁r, hs₁i⟩ := hs₁
  obtain ⟨hs₂p, hs₂r, hs₂i⟩ := hs₂
  obtain ⟨hs₃p, hs₃r, hs₃i⟩ := hs₃
  obtain ⟨r₁p, r₁r, -⟩ := r₁
  obtain ⟨r₂₁p, r₂₁r, -⟩ := r₂₁
  obtain ⟨r₂₂p, r₂₂r, -⟩ := r₂₂
  obtain ⟨ri₁p, -, -⟩ := ri₁
  -- the three pieces, in `C`
  have dD : InstrsOk C [.drop] ⟨it.params, [], m⟩ :=
    .sub (.frame (.instr (.parametric (.drop (ri₁p t (by simp))))) hts₁)
      ⟨hs₁p, hs₁r, fun _ h => by simp at h⟩ ⟨r₁p, r₁r, by simp⟩
  have dK : InstrsOk C [k] ⟨m, [], m'⟩ :=
    .sub (.frame (.instr (hkC C)) (by simpa using hts₂))
      ⟨by simpa using hs₂p, by simpa using hs₂r, fun _ h => by simp at h⟩
      ⟨by simpa using r₂₁p, by simpa using r₂₁r, by simp⟩
  have dS : InstrsOk C [.localSet x] ⟨m', [x.toNat], it.results⟩ :=
    .sub (.frame (.instr (.variable (.localSet hloc))) (by simpa using hts₃))
      ⟨by simpa using hs₃p, by simpa using hs₃r, fun _ _ h => absurd ‹_› h⟩
      ⟨by simpa using r₂₂p, by simpa using r₂₂r, by simp [hloc]⟩
  have dKS := InstrsOk.seq dK (by simp) dS
  have dAll := InstrsOk.seq dD (by simp) dKS
  simp only [List.nil_append, List.singleton_append] at dAll
  refine .sub dAll ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun y hy hn => ?_⟩ hreg
  have hyx : y ≠ x.toNat := fun h => hn (by simp [h])
  -- every claimed local other than `x` is already set
  have in₂ : y ∈ xs₂ → ∃ t, (C.initLocals xs₁).locals[y]? = some ⟨.set, t⟩ := fun hy₂ => by
    rcases inits_split r₂ hL₂ hy₂ with h | h | h
    · exact hs₂i y h (by simp)
    · exact set_of_initLocals (hs₃i y h (by simpa using hyx)) (fun h => hs₂i y h (by simp))
    · exact h
  have in₁ : y ∈ xs₁ → ∃ t, C.locals[y]? = some ⟨.set, t⟩ := fun h =>
    hs₁i y h (by simpa using hyx)
  rcases inits_split hreg hL hy with h | h | h
  · exact in₁ h
  · exact set_of_initLocals (in₂ h) in₁
  · exact h

mutual
theorem dsE_typed : ∀ e : BExpr, TyRepl e.lower (dsE e).lower
  | .op i args => by simpa [dsE] using TyRepl.append_right (dsL_typed args) [i]
  | .block bt b => by simpa [dsE, BExpr.lower] using TyRepl.block (dsL_typed b) bt
  | .loop bt b => by simpa [dsE, BExpr.lower] using TyRepl.loop (dsL_typed b) bt
  | .tryTable bt cs b => by simpa [dsE, BExpr.lower] using TyRepl.tryTable (dsL_typed b) bt cs
  | .if_ bt c t e => by
    simpa [dsE, BExpr.lower] using
      TyRepl.append (dsL_typed c) (TyRepl.if_ (dsL_typed t) (dsL_typed e) bt)
termination_by e => sizeOf e
theorem dsL_typed : ∀ es : List BExpr,
    TyRepl (BExpr.lowerList es) (BExpr.lowerList (dsL es))
  | [] => TyRepl.refl _
  | [e] => by simpa [dsL] using dsE_typed e
  | e :: e₂ :: es => by
    have ht := dsL_typed (e₂ :: es)
    unfold dsL
    split
    · next x v =>
      split
      · next hw =>
        obtain ⟨k, hk, rfl⟩ := overwrites_eq hw
        have h := TyRepl.append (TyRepl.append (dsE_typed v) (tyRepl_deadSet x hk))
          (dsL_typed es)
        simpa [BExpr.lower] using h
      · have h := TyRepl.append (TyRepl.append (dsE_typed v) (TyRepl.refl [.localSet x])) ht
        simpa [BExpr.lower] using h
    · simpa using TyRepl.append (dsE_typed e) ht
termination_by es => sizeOf es
end

/-! ## Modules -/

theorem deadSetLite_ok {m : BModule} (hm : m.Ok) : (deadSetLite m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [deadSetLite]) fun i _ _ => by
    simp only [deadSetLite, List.getElem_map]
    exact ⟨rfl, rfl, fun C ts hC hb => dsL_typed _ C _ hC hb⟩

theorem deadSetLite_bodiesRel (m : BModule) :
    ModuleBodiesRel dsBI (deadSetLite m).lower m.lower := by
  refine ⟨rfl, ?_⟩
  simp only [BModule.lower, deadSetLite, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, dsL_rel f.body⟩ ih

/-- The one-way refinement, for every host respecting the function relation. -/
theorem deadSetLite_refines {m : BModule} (hm : m.Ok) (host : HostSemantics H)
    (hhost : HostRespects (FuncRel dsBI) host) :
    ExportRefines (· = ·) P host (deadSetLite m).lower m.lower :=
  exportRefines_of_bodiesRel dsBaseSim hhost (deadSetLite_bodiesRel m) (deadSetLite_ok hm) hm

/-- **Dropping overwritten stores is export equivalent** under the deterministic profile
and the closed host: the one-way simulation and the determinism lift. -/
theorem deadSetLite_sound {o : GrowKind → Nat → Nat → Nat → Bool} {m : BModule} (hm : m.Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (deadSetLite m).lower
      m.lower :=
  ⟨deadSetLite_refines hm _ (closedHost_respects _),
    (DetLift.exportRefines_symm_of_hosts (deadSetLite_refines hm _ (closedHost_respects _))
      (deadSetLite_refines hm _ (divHost_respects _))
      (deadSetLite_refines hm _ (trapHost_respects _))
      (fun _ _ _ _ hI =>
        let ⟨c', hc', _⟩ := instantiate_bodiesRel (deadSetLite_bodiesRel m) hm hI
        ⟨c', hc'⟩)).mono fun _ _ h => h.symm⟩

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
