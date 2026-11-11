module

public import Silmaril.Wasm.Binaryen.NeutralOps.Defs
public import Silmaril.Wasm.Binaryen.IfSwapAny
public import Silmaril.Wasm.Binaryen.AddChainAny

@[expose] public section

/-! # Neutral-operand elimination: simulations in both directions

Base pairs relate `t.const k; t.op; X` (the original) to `X` (the result), where
`op` with `k` is neutral and the consumer `X` is an integer numeric instruction
of type `t`.

* **Original on the left** (`sourceBaseSim`): the neutral `t.op` step leaves the
  operand unchanged and stutters, with a payload-independent rank decrease;
  the configurations then coincide up to the related continuation.
* **Result on the left** (`resultBaseSim`): the consumer's own step forces its top
  operand to be a `t` value `v`; the original side runs `t.op` on `v` (giving `v`)
  and then replays the very same consumer step.

Neither direction reads the frame or the store, and neither needs numerical
determinism: both hold at every numerical profile under the closed host.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Profile}

/-! ## Arithmetic and instruction facts -/

theorem neutral_sound {t : IntType} {op : IntBinOp} {k : BitVec t.width}
    (h : neutral op k = true) (x : BitVec t.width) : intBinOp t op x k = .ok x := by
  cases op with
  | shr sg =>
    simp only [neutral, beq_iff_eq] at h
    subst h
    cases sg <;> simp [intBinOp, BitVec.ushiftRight_zero]
  | div sg | rem sg => simp [neutral] at h
  | rotl =>
    simp only [neutral, beq_iff_eq] at h
    subst h
    simp [intBinOp, BitVec.rotateLeft, BitVec.rotateLeftAux, BitVec.ushiftRight_eq_zero]
  | rotr =>
    simp only [neutral, beq_iff_eq] at h
    subst h
    simp [intBinOp, BitVec.rotateRight, BitVec.rotateRightAux]
  | _ =>
    simp only [neutral, beq_iff_eq] at h
    subst h
    simp [intBinOp, BitVec.shiftLeft_zero]

theorem fits_spec {X : Instr} {t : IntType} {op : IntBinOp} {t' : IntType}
    {k : BitVec t'.width} (h : fits X t op t' k = true) :
    ∃ e : t' = t, topIntType? X = some t ∧ neutral op (e ▸ k) = true := by
  unfold fits at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hX, hn⟩ := h
  split at hn
  · next e => exact ⟨e, hX, hn⟩
  · cases hn

/-- The consumers are integer unary, binary, test and comparison instructions. -/
theorem topIntType_cases {X : Instr} {t : IntType} (h : topIntType? X = some t) :
    (∃ op, X = .intUnOp t op) ∨ (∃ op, X = .intBinOp t op) ∨ (∃ op, X = .intTestOp t op) ∨
      (∃ op, X = .intRelOp t op) := by
  cases X <;> simp only [topIntType?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

/-- A consumer is no control instruction. -/
theorem topIntType_not_control {X : Instr} {t : IntType} (h : topIntType? X = some t) :
    (∀ l, Admin.plain X ≠ .plain (.br l)) ∧ Admin.plain X ≠ .plain .return_ ∧
      ¬ (Admin.plain X).IsReturnCallRef ∧ Admin.plain X ≠ .plain .throwRef := by
  rcases topIntType_cases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    simp [Admin.IsReturnCallRef]

theorem topIntType_val {X : Instr} {t : IntType} (h : topIntType? X = some t) :
    (Admin.plain X).val? = none := by
  rcases topIntType_cases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem topIntType_famOf {X : Instr} {t : IntType} (h : topIntType? X = some t) :
    Det.famOf (.plain X) = .numeric := by
  rcases topIntType_cases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- A value list ending in an integer constant ends in that integer value. -/
theorem vals_eq_snoc_intConst {args : List Val} {l : List Admin} {t : IntType}
    {x : BitVec t.width} (h : vals args = l ++ [.plain (.intConst t x)]) :
    ∃ pre, args = pre ++ [.num ⟨.int t, x⟩] := by
  unfold vals at h
  obtain ⟨L₁, L₂, rfl, -, h₂⟩ := List.map_eq_append_iff.mp h
  obtain ⟨w, rfl, hw⟩ := List.map_eq_singleton_iff.mp h₂
  have := Det.toAdmin_eq_iff.mp hw
  simp only [Admin.val?, Option.some.injEq] at this
  exact ⟨L₁, by rw [this]⟩

/-- A consumer whose last two operands end in an integer constant of type `t'` has a
`t` value on top. -/
private theorem top_of_int_arm {X Y : Instr} {t t' : IntType} (hX : topIntType? X = some t)
    (hY : topIntType? Y = some t') {args : List Val} {l : List Admin} {y : BitVec t'.width}
    (hl : vals args ++ [.plain X] = (l ++ [.plain (.intConst t' y)]) ++ [.plain Y]) :
    ∃ pre v, args = pre ++ [.num ⟨.int t, v⟩] := by
  obtain ⟨h1, h2⟩ : vals args = l ++ [.plain (.intConst t' y)] ∧ Admin.plain X = .plain Y :=
    Det.append_singleton_inj.mp hl
  have hXY : X = Y := by cases h2; rfl
  have htt : some t' = some t := by rw [← hY, ← hXY, hX]
  obtain ⟨pre, hp⟩ : ∃ pre, args = pre ++ [.num ⟨.int t', y⟩] := vals_eq_snoc_intConst h1
  cases htt
  exact ⟨pre, y, hp⟩

/-- A consumer is no floating-point or conversion instruction. -/
private theorem not_other_arm {X Y : Instr} {t : IntType} (hX : topIntType? X = some t)
    (hY : topIntType? Y = none) {args : List Val} {l : List Admin}
    (hl : vals args ++ [.plain X] = l ++ [.plain Y]) : False := by
  obtain ⟨-, h2⟩ : vals args = l ∧ Admin.plain X = .plain Y := Det.append_singleton_inj.mp hl
  have hXY : X = Y := by cases h2; rfl
  have hnone : (none : Option IntType) = some t := by rw [← hY, ← hXY, hX]
  cases hnone

/-- `numeric_top`, with the step's code abstracted for case analysis. -/
private theorem numeric_top_of_eq {X : Instr} {t : IntType} (hX : topIntType? X = some t)
    {args : List Val} {l is' : List Admin} (hl : vals args ++ [.plain X] = l)
    (h : NumericStep P l is') :
    ∃ pre v, args = pre ++ [.num ⟨.int t, v⟩] := by
  cases h with
  | @intUnOp t' op x => exact top_of_int_arm (l := []) (Y := .intUnOp t' op) hX rfl hl
  | @intBinOp t' op x y z _ =>
    exact top_of_int_arm (l := [.plain (.intConst t' x)]) (Y := .intBinOp t' op) hX rfl hl
  | @intBinOpTrap t' op x y e _ =>
    exact top_of_int_arm (l := [.plain (.intConst t' x)]) (Y := .intBinOp t' op) hX rfl hl
  | @intTestOp t' op x => exact top_of_int_arm (l := []) (Y := .intTestOp t' op) hX rfl hl
  | @intRelOp t' op x y =>
    exact top_of_int_arm (l := [.plain (.intConst t' x)]) (Y := .intRelOp t' op) hX rfl hl
  | @floatUnOp t' op x z _ =>
    exact (not_other_arm (l := [.plain (.floatConst t' x)]) (Y := .floatUnOp t' op)
      hX rfl hl).elim
  | @floatBinOp t' op x y z _ =>
    exact (not_other_arm (l := [.plain (.floatConst t' x), .plain (.floatConst t' y)])
      (Y := .floatBinOp t' op) hX rfl hl).elim
  | @floatRelOp t' op x y =>
    exact (not_other_arm (l := [.plain (.floatConst t' x), .plain (.floatConst t' y)])
      (Y := .floatRelOp t' op) hX rfl hl).elim
  | @convert op x z _ =>
    exact (not_other_arm (l := [(Val.num ⟨op.source, x⟩).toAdmin]) hX (by rfl) hl).elim
  | @convertTrap op x e _ =>
    exact (not_other_arm (l := [(Val.num ⟨op.source, x⟩).toAdmin]) hX (by rfl) hl).elim

/-- A numeric step at a consumer of type `t` has a `t` value on top of its operands. -/
theorem numeric_top {X : Instr} {t : IntType} (hX : topIntType? X = some t)
    {args : List Val} {is' : List Admin} (h : NumericStep P (vals args ++ [.plain X]) is') :
    ∃ pre v, args = pre ++ [.num ⟨.int t, v⟩] :=
  numeric_top_of_eq hX rfl h

/-- A head step at a numeric instruction is a `NumericStep`. -/
private theorem numeric_head_inv {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hfam : Det.famOf e = .numeric) (h : Det.Head P s f args e c₀) :
    ∃ is', NumericStep P (vals args ++ [e]) is' ∧ c₀ = ⟨s, f, is'⟩ := by
  have hrel : Det.FamRel P (Det.famOf e) s f (vals args ++ [e]) c₀ :=
    h.fam_inv (by rw [hfam]; simp)
  simpa only [hfam, Det.FamRel] using hrel

/-- The head step of an integer binary operation. -/
theorem head_binop {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntBinOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intBinOp t op)) c₀) :
    ∃ a b : BitVec t.width, args = [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩] ∧
      ((∃ z, intBinOp t op a b = .ok z ∧ c₀ = ⟨s, f, [.plain (.intConst t z)]⟩) ∨
        (∃ e, intBinOp t op a b = .error e ∧ c₀ = ⟨s, f, [.trap]⟩)) := by
  obtain ⟨is', hv, hc₀⟩ := numeric_head_inv (P := P) rfl h
  rw [hc₀]
  generalize hl : vals args ++ [Admin.plain (.intBinOp t op)] = l at hv
  cases hv with
  | @intBinOp t' op' x y z hz =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj
      (l₂ := [Admin.plain (.intConst t' x), .plain (.intConst t' y)])).mp hl
    cases h2
    have ha : args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] :=
      Det.vals_inj.mp (by simpa [vals, Val.toAdmin] using h1)
    exact ⟨x, y, ha, Or.inl ⟨z, hz, rfl⟩⟩
  | @intBinOpTrap t' op' x y e he =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj
      (l₂ := [Admin.plain (.intConst t' x), .plain (.intConst t' y)])).mp hl
    cases h2
    have ha : args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] :=
      Det.vals_inj.mp (by simpa [vals, Val.toAdmin] using h1)
    exact ⟨x, y, ha, Or.inr ⟨e, he, rfl⟩⟩
  | _ =>
    have hlast : (vals args ++ [Admin.plain (.intBinOp t op)]).getLast? = _ :=
      congrArg List.getLast? hl
    simp at hlast

/-- The neutral operation leaves its other operand on the stack. -/
private theorem neutral_step_inv {t : IntType} {op : IntBinOp} {k : BitVec t.width}
    (hn : neutral op k = true) {s s' : Store H} {f f' : Frame} {vs : List Val}
    {rest es' : List Admin}
    (hstep : Step P closedHost
      ⟨s, f, vals (vs ++ [.num ⟨.int t, k⟩]) ++ .plain (.intBinOp t op) :: rest⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
  obtain ⟨a, b, hargs, hres⟩ := head_binop hh
  have hW' : vs ++ [.num ⟨.int t, k⟩] =
      (pre ++ [.num ⟨.int t, a⟩]) ++ [.num ⟨.int t, b⟩] := by rw [hW, hargs]; simp
  obtain ⟨hvs, hb⟩ := Det.append_singleton_inj.mp hW'
  have hbk : b = k := by cases hb; rfl
  rcases hres with ⟨z, hz, hc₀⟩ | ⟨e, he', -⟩
  · have hz' : intBinOp t op a k = .ok z := by rw [← hbk]; exact hz
    have hza : a = z := Except.ok.inj ((neutral_sound hn a).symm.trans hz')
    have hparts : s' = s ∧ f' = f ∧ es' = vals pre ++ [.plain (.intConst t z)] ++ rest := by
      simpa only [hc₀, Config.mk.injEq] using he
    rw [hvs, hza]
    simpa [vals, Val.toAdmin, List.append_assoc] using hparts
  · have he'' : intBinOp t op a k = .error e := by rw [← hbk]; exact he'
    cases (neutral_sound hn a).symm.trans he''

/-- Inverting a consumer's step: it is a numeric step with a `t` value on top. -/
private theorem consumer_step_inv {X : Instr} {t : IntType} (hX : topIntType? X = some t)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {rest es' : List Admin}
    (hstep : Step P closedHost ⟨s, f, vals vs ++ .plain X :: rest⟩ ⟨s', f', es'⟩) :
    ∃ pre args₀ v is', vs = pre ++ (args₀ ++ [.num ⟨.int t, v⟩]) ∧ s' = s ∧ f' = f ∧
      es' = vals pre ++ is' ++ rest ∧
      NumericStep P (vals (args₀ ++ [.num ⟨.int t, v⟩]) ++ [.plain X]) is' := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv (topIntType_val hX) (by simp)
    (topIntType_not_control hX).2.2.2 hstep
  obtain ⟨is', hns, hc₀⟩ := numeric_head_inv (topIntType_famOf hX) hh
  obtain ⟨args₀, v, hargs⟩ := numeric_top hX hns
  have hparts : s' = s ∧ f' = f ∧ es' = vals pre ++ is' ++ rest := by
    simpa only [hc₀, Config.mk.injEq] using he
  exact ⟨pre, args₀, v, is', by rw [hW, hargs], hparts.1, hparts.2.1, hparts.2.2,
    by rw [← hargs]; exact hns⟩

/-- The original runs the neutral operation on `v`, then the consumer's step. -/
private theorem neutral_consumer_steps {t : IntType} {op : IntBinOp} {k : BitVec t.width}
    {X : Instr} (hn : neutral op k = true) {u : Store H} {f : Frame}
    {pre args₀ : List Val} {v : BitVec t.width} {is' rest' : List Admin}
    (hns : NumericStep P (vals (args₀ ++ [.num ⟨.int t, v⟩]) ++ [.plain X]) is') :
    Relation.TransGen (Step P closedHost)
      ⟨u, f, vals (pre ++ (args₀ ++ [.num ⟨.int t, v⟩])) ++
        [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] ++ rest'⟩
      ⟨u, f, vals pre ++ is' ++ rest'⟩ := by
  have h1 : Step P closedHost
      ⟨u, f, vals (pre ++ (args₀ ++ [.num ⟨.int t, v⟩])) ++
        [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] ++ rest'⟩
      ⟨u, f, vals (pre ++ (args₀ ++ [.num ⟨.int t, v⟩])) ++ [.plain X] ++ rest'⟩ := by
    simpa [vals, Val.toAdmin, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.numeric (P := P) (host := closedHost)
        (s := u) (f := f) (NumericStep.intBinOp (t := t) (op := op) (x := v) (y := k)
          (neutral_sound hn v))) (pre ++ args₀)) (.plain X :: rest')
  have h2 : Step P closedHost
      ⟨u, f, vals (pre ++ (args₀ ++ [.num ⟨.int t, v⟩])) ++ [.plain X] ++ rest'⟩
      ⟨u, f, vals pre ++ is' ++ rest'⟩ := by
    simpa [vals, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.numeric (P := P) (host := closedHost)
        (s := u) (f := f) hns) pre) rest'
  exact .tail (.single h1) h2

/-! ## Base relations -/

/-- Runtime base pairs: the lowered source pairs. -/
inductive nB : List Admin → List Admin → Prop where
  | mk (t : IntType) (op : IntBinOp) (k : BitVec t.width) (X : Instr)
      (hn : neutral op k = true) (hX : topIntType? X = some t) :
      nB [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] [.plain X]

/-! ## The original simulates the result -/

theorem sourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F nBI nB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | mk t op k X hn hX => exact .mk t op k X hn hX
  step := by
    intro s u s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | mk t op k X hn hX =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨u, f, vals vs ++ [.plain X] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++ [.plain X] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++
              [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel nBI nB es' es''
      have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [.num ⟨.int t, k⟩]) ++
            .plain (.intBinOp t op) :: (.plain X :: rest)⟩ ⟨s', f', es'⟩ := by
        simpa [vals, Val.toAdmin, List.append_assoc] using hstep
      obtain ⟨hs₁, hf₁, he₁⟩ : s' = s ∧ f' = f ∧ es' = vals vs ++ (.plain X :: rest) :=
        neutral_step_inv hn hs
      have hr : teeCodeRank (vals vs ++ ([.plain X] ++ rest)) <
          teeCodeRank (vals vs ++ [.plain (.intConst t k), .plain (.intBinOp t op)] ++
            ([.plain X] ++ rest)) :=
        LawfulCodeRank.infix_lt (vals vs) _ _ (by simp)
      rw [hs₁, hf₁, he₁]
      refine ⟨u, vals vs ++ [.plain X] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, by simpa [List.append_assoc] using hr⟩, hst, ?_⟩
      show AdminsRel nBI nB (vals vs ++ ([.plain X] ++ rest)) (vals vs ++ [.plain X] ++ rest')
      rw [← List.append_assoc]
      exact (AdminsRel.refl (BI := nBI) (B := nB) (vals vs ++ [.plain X])).append hrest
  exit := by
    intro s u f vs us x y kk j hst hxy hk he
    exfalso
    cases hxy with
    | mk t op k X hn hX =>
      exact GuardSim.not_exit (W := vs ++ [.num ⟨.int t, k⟩]) (e₀ := .plain (.intBinOp t op))
        (x' := [.plain X]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) hk (by simpa [vals, Val.toAdmin, List.append_assoc] using he)
  values := by
    intro s u f vs us x y hst hxy hx
    exfalso
    have hall : x.all Admin.isVal = (vals us).all Admin.isVal :=
      congrArg (fun es => es.all Admin.isVal) hx
    cases hxy
    exact absurd hall (by simp [Admin.isVal, Admin.val?])

/-! ## The result simulates the original -/

theorem resultBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => nBI b a) (fun a b => nB b a) teeCodeRank where
  src := by
    intro x y h
    cases h with
    | mk t op k X hn hX => exact .mk t op k X hn hX
  step := by
    intro s u s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | mk t op k X hn hX =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨u, f, vals vs ++
            [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++
              [.plain (.intConst t k), .plain (.intBinOp t op), .plain X] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++ [.plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel (fun a b => nBI b a) (fun a b => nB b a) es' es''
      have hs : Step P closedHost ⟨s, f, vals vs ++ .plain X :: rest⟩ ⟨s', f', es'⟩ := by
        simpa using hstep
      obtain ⟨pre, args₀, v, is', hvs, hs₁, hf₁, he₁, hns⟩ := consumer_step_inv hX hs
      rw [hvs, hs₁, hf₁, he₁]
      exact ⟨u, vals pre ++ is' ++ rest', Or.inl (neutral_consumer_steps hn hns), hst,
        (AdminsRel.refl _).append hrest⟩
  exit := by
    intro s u f vs us x y kk j hst hxy hk he
    exfalso
    cases hxy with
    | mk t op k X hn hX =>
      obtain ⟨hbr, hret, hrc, hth⟩ := topIntType_not_control hX
      exact GuardSim.not_exit (W := vs) (e₀ := .plain X) (x' := []) (topIntType_val hX) hbr hret
        hrc (by simp) hth hk (by simpa using he)
  values := by
    intro s u f vs us x y hst hxy hx
    exfalso
    have hall : x.all Admin.isVal = (vals us).all Admin.isVal :=
      congrArg (fun es => es.all Admin.isVal) hx
    cases hxy with
    | mk t op k X hn hX =>
      have hv : (Admin.plain X).val? = none := topIntType_val hX
      exact absurd hall (by simp [Admin.isVal, hv])

end Silmaril.Proofs.Wasm.Binaryen.NeutralOps
