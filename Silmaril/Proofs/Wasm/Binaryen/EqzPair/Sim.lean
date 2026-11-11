module

public import Silmaril.Wasm.Binaryen.EqzPair.Defs
public import Silmaril.Wasm.Binaryen.IfSwapAny
public import Silmaril.Wasm.Binaryen.ConstSelectSim

@[expose] public section

/-! # Double `i32.eqz` before a boolean consumer: simulations in both directions

Base pairs relate `i32.eqz; i32.eqz; X` (the original) to `X` (the result) for a
boolean consumer `X` (`br_if`, `select`, `i32.eqz`). The single fact used about
`X` is `bool_head`: a head step of `X` exposes an `i32` top operand `c`, leaves
store and frame unchanged, and the same successor code is reached from any top
operand `b` with `b = 0 ↔ c = 0`, at any store.

* **Original on the left** (`sourceBaseSim`): each `eqz` stutters with a rank
  decrease through two runtime phases; the final `X` step on `eqz (eqz c)` is
  matched by the result's `X` step on `c`.
* **Result on the left** (`resultBaseSim`): the result's `X` step on `c` is matched
  by the original's two `eqz` steps and its `X` step on `eqz (eqz c)`.

Both hold at every numerical profile under the closed host.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Profile}

/-! ## Facts about `eqz` and the consumers -/

theorem eqz_eqz_eq_zero (c : BitVec 32) :
    intTestOp .i32 .eqz (intTestOp .i32 .eqz c) = 0 ↔ c = 0 := by
  rw [GuardSim.eqz_eq_zero, not_iff_comm, GuardSim.eqz_eq_zero]

theorem eqz_congr {b c : BitVec 32} (h : b = 0 ↔ c = 0) :
    intTestOp .i32 .eqz b = intTestOp .i32 .eqz c := by
  by_cases hc : c = 0
  · rw [hc, h.mpr hc]
  · have hb : b ≠ 0 := fun hb => hc (h.mp hb)
    rw [(GuardSim.eqz_eq_zero b).mpr hb, (GuardSim.eqz_eq_zero c).mpr hc]

theorem boolConsumer_cases {X : Instr} (h : boolConsumer X = true) :
    (∃ l, X = .brIf l) ∨ (∃ ts, X = .select ts) ∨ X = .intTestOp .i32 .eqz := by
  cases X <;> simp only [boolConsumer, reduceCtorEq] at h <;>
    first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr (Or.inl ⟨_, rfl⟩)
    | (rename_i t op
       cases t <;> simp only [reduceCtorEq] at h
       cases op
       exact Or.inr (Or.inr rfl))

/-- A boolean consumer is no value, branch, return, tail call, trap or `throw_ref`. -/
theorem boolConsumer_inert {X : Instr} (h : boolConsumer X = true) :
    (Admin.plain X).val? = none ∧ (∀ l, Admin.plain X ≠ .plain (.br l)) ∧
      Admin.plain X ≠ .plain .return_ ∧ ¬ (Admin.plain X).IsReturnCallRef ∧
      Admin.plain X ≠ .plain .throwRef := by
  rcases boolConsumer_cases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | rfl <;>
    simp [Admin.val?, Admin.IsReturnCallRef]

private theorem head_brIf {s : Store H} {f : Frame} {args : List Val}
    {l : LabelIdx} {cfg : Config H} (h : Det.Head P s f args (.plain (.brIf l)) cfg) :
    ∃ c : BitVec 32, args = [Val.i32 c] ∧
      cfg = ⟨s, f, if c = 0 then [] else [.plain (.br l)]⟩ := by
  cases h with
  | brIfTrue hc => exact ⟨_, rfl, ite_eq_right hc ▸ rfl⟩
  | brIfFalse hc => exact ⟨_, rfl, ite_eq_left hc ▸ rfl⟩
  | _ =>
    first
    | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
    | (exfalso; simp_all [Admin.IsCallRef])

private theorem bool_head_brIf {l : LabelIdx} {s : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (h : Det.Head P s f args (.plain (.brIf l)) c₀) :
    ∃ pre c, args = pre ++ [Val.i32 c] ∧ c₀.store = s ∧ c₀.frame = f ∧
      ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
        Step P closedHost ⟨u, f, vals (pre ++ [Val.i32 b]) ++ [.plain (.brIf l)]⟩
          ⟨u, f, c₀.code⟩ := by
  obtain ⟨c, hargs, hc₀⟩ : ∃ c : BitVec 32, args = [Val.i32 c] ∧
      c₀ = ⟨s, f, if c = 0 then [] else [.plain (.br l)]⟩ := head_brIf h
  rw [hc₀]
  refine ⟨[], c, hargs, rfl, rfl, fun u b hb => ?_⟩
  by_cases hc : c = 0
  · have hb0 : b = 0 := hb.mpr hc
    rw [hb0]
    simpa [hc, vals, Val.i32, constI32] using
      Step.brIfFalse (P := P) (host := closedHost) (s := u) (f := f) (l := l)
  · have hb0 : b ≠ 0 := fun e => hc (hb.mp e)
    rw [ite_eq_right hc]
    simpa [vals, Val.i32, constI32] using
      Step.brIfTrue (P := P) (host := closedHost) (s := u) (f := f) (l := l) hb0

private theorem bool_head_select {ts : Option (List ValType)} {s : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (h : Det.Head P s f args (.plain (.select ts)) c₀) :
    ∃ pre c, args = pre ++ [Val.i32 c] ∧ c₀.store = s ∧ c₀.frame = f ∧
      ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
        Step P closedHost ⟨u, f, vals (pre ++ [Val.i32 b]) ++ [.plain (.select ts)]⟩
          ⟨u, f, c₀.code⟩ := by
  obtain ⟨a, a', c, hargs, hc₀⟩ : ∃ (a a' : Val) (c : BitVec 32),
      args = [a, a', .num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [(if c = 0 then a' else a).toAdmin]⟩ := ConstSelect.head_select h
  rw [hc₀]
  refine ⟨[a, a'], c, hargs, rfl, rfl, fun u b hb => ?_⟩
  by_cases hc : c = 0
  · have hb0 : b = 0 := hb.mpr hc
    rw [hb0]
    simpa [hc, vals, Val.i32, constI32] using
      Step.parametric (P := P) (host := closedHost) (s := u) (f := f)
        (ParametricStep.selectFalse a a' ts)
  · have hb0 : b ≠ 0 := fun e => hc (hb.mp e)
    rw [ite_eq_right hc]
    simpa [vals, Val.i32, constI32] using
      Step.parametric (P := P) (host := closedHost) (s := u) (f := f)
        (ParametricStep.selectTrue (v₁ := a) (v₂ := a') (ts := ts) hb0)

private theorem bool_head_eqz {s : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (h : Det.Head P s f args (.plain eqz) c₀) :
    ∃ pre c, args = pre ++ [Val.i32 c] ∧ c₀.store = s ∧ c₀.frame = f ∧
      ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
        Step P closedHost ⟨u, f, vals (pre ++ [Val.i32 b]) ++ [.plain eqz]⟩
          ⟨u, f, c₀.code⟩ := by
  obtain ⟨c, hargs, hc₀⟩ : ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [constI32 (intTestOp .i32 .eqz c)]⟩ := GuardSim.head_eqz h
  rw [hc₀]
  refine ⟨[], c, hargs, rfl, rfl, fun u b hb => ?_⟩
  have hb' : Step P closedHost ⟨u, f, [constI32 b, .plain eqz]⟩
      ⟨u, f, [constI32 (intTestOp .i32 .eqz b)]⟩ :=
    Step.numeric (P := P) (host := closedHost) (s := u) (f := f)
      (NumericStep.intTestOp (t := .i32) (op := .eqz) (x := b))
  simpa [eqz_congr hb, vals, Val.i32, constI32, Val.toAdmin] using hb'

/-- **The consumer fact.** -/
theorem bool_head {X : Instr} (hX : boolConsumer X = true) {s : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (h : Det.Head P s f args (.plain X) c₀) :
    ∃ pre c, args = pre ++ [Val.i32 c] ∧ c₀.store = s ∧ c₀.frame = f ∧
      ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
        Step P closedHost ⟨u, f, vals (pre ++ [Val.i32 b]) ++ [.plain X]⟩ ⟨u, f, c₀.code⟩ := by
  rcases boolConsumer_cases hX with ⟨l, rfl⟩ | ⟨ts, rfl⟩ | rfl
  exacts [bool_head_brIf h, bool_head_select h, bool_head_eqz h]

/-- One `i32.eqz` step on top of a value stack. -/
theorem eqz_step (u : Store H) (f : Frame) (vs : List Val) (c : BitVec 32) (rest : List Admin) :
    Step P closedHost ⟨u, f, vals (vs ++ [Val.i32 c]) ++ .plain eqz :: rest⟩
      ⟨u, f, vals (vs ++ [Val.i32 (intTestOp .i32 .eqz c)]) ++ rest⟩ := by
  have := Step.append_right (Step.vals_left (Step.numeric (P := P) (host := closedHost) (s := u)
    (f := f) (NumericStep.intTestOp (t := .i32) (op := .eqz) (x := c))) vs) rest
  simpa [vals, Val.i32, constI32, Val.toAdmin, List.append_assoc] using this

/-- Inverting an `i32.eqz` step: it pops an `i32` and pushes its test. -/
private theorem eqz_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val}
    {rest es' : List Admin}
    (hstep : Step P closedHost ⟨s, f, vals vs ++ .plain eqz :: rest⟩ ⟨s', f', es'⟩) :
    ∃ pre c, vs = pre ++ [Val.i32 c] ∧ s' = s ∧ f' = f ∧
      es' = vals pre ++ [constI32 (intTestOp .i32 .eqz c)] ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
  obtain ⟨c, hargs, hc₀⟩ : ∃ c : BitVec 32, args = [.num ⟨.int .i32, c⟩] ∧
      c₀ = ⟨s, f, [constI32 (intTestOp .i32 .eqz c)]⟩ := GuardSim.head_eqz hh
  have hvs : vs = pre ++ [Val.i32 c] := by rw [hW, hargs]; rfl
  have hparts : s' = s ∧ f' = f ∧
      es' = vals pre ++ [constI32 (intTestOp .i32 .eqz c)] ++ rest := by
    simpa only [hc₀, Config.mk.injEq] using he
  exact ⟨pre, c, hvs, hparts⟩

/-- An `i32.eqz` step on a known top operand. -/
private theorem eqz_step_inv_top {s s' : Store H} {f f' : Frame} {vs : List Val}
    {c : BitVec 32} {rest es' : List Admin}
    (hstep : Step P closedHost
      ⟨s, f, vals (vs ++ [Val.i32 c]) ++ .plain eqz :: rest⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs ++ [constI32 (intTestOp .i32 .eqz c)] ++ rest := by
  obtain ⟨pre, c', hvs, hs₁, hf₁, he₁⟩ := eqz_step_inv hstep
  obtain ⟨hpre, hc⟩ : vs = pre ∧ Val.i32 c = Val.i32 c' :=
    Det.append_singleton_inj.mp hvs
  have hcc : c = c' := by cases hc; rfl
  rw [hpre, hcc]
  exact ⟨hs₁, hf₁, he₁⟩

/-- Inverting a boolean consumer's step: it reads an `i32` operand `c`, and its
successor code is reached from any operand with the same truth value. -/
private theorem consumer_step_inv {X : Instr} (hX : boolConsumer X = true)
    {s s' : Store H} {f f' : Frame} {vs : List Val} {rest es' : List Admin}
    (hstep : Step P closedHost ⟨s, f, vals vs ++ .plain X :: rest⟩ ⟨s', f', es'⟩) :
    ∃ pre pre' c code, vs = pre ++ pre' ++ [Val.i32 c] ∧ s' = s ∧ f' = f ∧
      es' = vals pre ++ code ++ rest ∧
      ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
        Step P closedHost ⟨u, f, vals (pre' ++ [Val.i32 b]) ++ [.plain X]⟩ ⟨u, f, code⟩ := by
  obtain ⟨hv, -, -, -, hth⟩ := boolConsumer_inert hX
  obtain ⟨pre, args, c₀, hW, hh, he⟩ := GuardSim.head_inv hv (by simp) hth hstep
  obtain ⟨pre', c, hargs, hcs, hcf, hrun⟩ := bool_head hX hh
  have hparts : s' = c₀.store ∧ f' = c₀.frame ∧ es' = vals pre ++ c₀.code ++ rest := by
    simpa only [Config.mk.injEq] using he
  refine ⟨pre, pre', c, c₀.code, by rw [hW, hargs, List.append_assoc],
    hparts.1.trans hcs, hparts.2.1.trans hcf, hparts.2.2, hrun⟩

/-- The original runs `eqz; eqz; X` on `c` to where the result's `X` goes on `c`. -/
private theorem eqz_eqz_consumer_steps {X : Instr} {u : Store H} {f : Frame}
    {pre pre' : List Val} {c : BitVec 32} {code rest' : List Admin}
    (hrun : ∀ (u : Store H) (b : BitVec 32), (b = 0 ↔ c = 0) →
      Step P closedHost ⟨u, f, vals (pre' ++ [Val.i32 b]) ++ [.plain X]⟩ ⟨u, f, code⟩) :
    Relation.TransGen (Step P closedHost)
      ⟨u, f, vals (pre ++ pre' ++ [Val.i32 c]) ++ [.plain eqz, .plain eqz, .plain X] ++ rest'⟩
      ⟨u, f, vals pre ++ code ++ rest'⟩ := by
  have h₁ := eqz_step (P := P) u f (pre ++ pre') c (.plain eqz :: .plain X :: rest')
  have h₂ := eqz_step (P := P) u f (pre ++ pre') (intTestOp .i32 .eqz c) (.plain X :: rest')
  have h₃ : Step P closedHost
      ⟨u, f, vals pre ++ (vals (pre' ++ [Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c))]) ++
        [.plain X]) ++ rest'⟩ ⟨u, f, vals pre ++ code ++ rest'⟩ :=
    Step.append_right (Step.vals_left (hrun u _ (eqz_eqz_eq_zero c)) pre) rest'
  refine .tail (.tail (.single ?_) h₂) ?_
  · simpa [vals, List.append_assoc] using h₁
  · simpa [vals, List.append_assoc] using h₃

/-! ## Base relations -/

/-- Runtime pairs with the original on the left, including the two `eqz` phases. -/
inductive srcB : List Admin → List Admin → Prop where
  | start (X : Instr) (hX : boolConsumer X = true) :
      srcB [.plain eqz, .plain eqz, .plain X] [.plain X]
  | phase₁ (X : Instr) (hX : boolConsumer X = true) (c : BitVec 32) :
      srcB [constI32 (intTestOp .i32 .eqz c), .plain eqz, .plain X] [constI32 c, .plain X]
  | phase₂ (X : Instr) (hX : boolConsumer X = true) (c : BitVec 32) :
      srcB [constI32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c)), .plain X] [constI32 c, .plain X]

/-- Runtime pairs with the result on the left. -/
inductive resB : List Admin → List Admin → Prop where
  | mk (X : Instr) (hX : boolConsumer X = true) :
      resB [.plain X] [.plain eqz, .plain eqz, .plain X]

/-! ## The original simulates the result -/

theorem sourceBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F eBI srcB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | mk X hX => exact .start X hX
  step := by
    intro s u s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | start X hX =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨u, f, vals vs ++ [.plain X] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++ [.plain X] ++ rest' ∧
            teeCodeRank es' <
              teeCodeRank (vals vs ++ [.plain eqz, .plain eqz, .plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel eBI srcB es' es''
      have hs : Step P closedHost
          ⟨s, f, vals vs ++ .plain eqz :: (.plain eqz :: .plain X :: rest)⟩ ⟨s', f', es'⟩ := by
        simpa using hstep
      obtain ⟨pre, c, hvs, hs₁, hf₁, he₁⟩ : ∃ pre c, vs = pre ++ [Val.i32 c] ∧ s' = s ∧
          f' = f ∧ es' = vals pre ++ [constI32 (intTestOp .i32 .eqz c)] ++
            (.plain eqz :: .plain X :: rest) :=
        eqz_step_inv hs
      have hr : teeCodeRank (vals pre ++ [constI32 (intTestOp .i32 .eqz c), .plain eqz] ++
            (.plain X :: rest)) <
          teeCodeRank (vals pre ++ [constI32 c, .plain eqz, .plain eqz] ++ (.plain X :: rest)) :=
        LawfulCodeRank.context_lt (vals pre) (.plain X :: rest)
          (by simp [teeAdminRank, constI32])
      rw [hvs, hs₁, hf₁, he₁]
      refine ⟨u, vals (pre ++ [.num ⟨.int .i32, c⟩]) ++ [.plain X] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, by simpa [vals, Val.i32, constI32, List.append_assoc] using hr⟩,
        hst, ?_⟩
      simpa [vals, Val.i32, constI32, List.append_assoc] using
        ((AdminsRel.refl (BI := eBI) (B := srcB) (vals pre)).append
          (AdminsRel.base (.phase₁ X hX c))).append hrest
    | phase₁ X hX c =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨u, f, vals vs ++ [constI32 c, .plain X] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++ [constI32 c, .plain X] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++
              [constI32 (intTestOp .i32 .eqz c), .plain eqz, .plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel eBI srcB es' es''
      have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 (intTestOp .i32 .eqz c)]) ++ .plain eqz :: (.plain X :: rest)⟩
          ⟨s', f', es'⟩ := by
        simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨hs₁, hf₁, he₁⟩ : s' = s ∧ f' = f ∧ es' = vals vs ++
          [constI32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c))] ++ (.plain X :: rest) :=
        eqz_step_inv_top hs
      have hr : teeCodeRank (vals vs ++ [constI32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c))] ++
            (.plain X :: rest)) <
          teeCodeRank (vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain eqz] ++
            (.plain X :: rest)) :=
        LawfulCodeRank.context_lt (vals vs) (.plain X :: rest)
          (by simp [teeAdminRank, constI32])
      rw [hs₁, hf₁, he₁]
      refine ⟨u, vals vs ++ [constI32 c, .plain X] ++ rest',
        Or.inr ⟨rfl, rfl, rfl, by simpa [vals, Val.i32, constI32, List.append_assoc] using hr⟩,
        hst, ?_⟩
      simpa [vals, Val.i32, constI32, List.append_assoc] using
        ((AdminsRel.refl (BI := eBI) (B := srcB) (vals vs)).append
          (AdminsRel.base (.phase₂ X hX c))).append hrest
    | phase₂ X hX c =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost) ⟨u, f, vals vs ++ [constI32 c, .plain X] ++ rest'⟩
            ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++ [constI32 c, .plain X] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++
              [constI32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c)), .plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel eBI srcB es' es''
      have hs : Step P closedHost
          ⟨s, f, vals (vs ++ [Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c))]) ++
            .plain X :: rest⟩ ⟨s', f', es'⟩ := by
        simpa [vals, Val.i32, constI32, List.append_assoc] using hstep
      obtain ⟨pre, pre', d, code, hW, hs₁, hf₁, he₁, hrun⟩ := consumer_step_inv hX hs
      obtain ⟨hvs, hd⟩ : pre ++ pre' = vs ∧
          Val.i32 d = Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c)) :=
        Det.append_singleton_inj.mp hW.symm
      have hd' : d = intTestOp .i32 .eqz (intTestOp .i32 .eqz c) := by cases hd; rfl
      have hcd : c = 0 ↔ d = 0 := by rw [hd']; exact (eqz_eqz_eq_zero c).symm
      have hX' : Step P closedHost
          ⟨u, f, vals pre ++ (vals (pre' ++ [Val.i32 c]) ++ [.plain X]) ++ rest'⟩
          ⟨u, f, vals pre ++ code ++ rest'⟩ :=
        Step.append_right (Step.vals_left (hrun u c hcd) pre) rest'
      rw [hs₁, hf₁, he₁, ← hvs]
      refine ⟨u, vals pre ++ code ++ rest', Or.inl (.single ?_), hst,
        (AdminsRel.refl _).append hrest⟩
      simpa [vals, Val.i32, constI32, List.append_assoc] using hX'
  exit := by
    intro s u f vs us x y kk j hst hxy hk he
    exfalso
    cases hxy with
    | start X hX =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain eqz) (x' := [.plain eqz, .plain X]) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk
        (by simpa using he)
    | phase₁ X hX c =>
      exact GuardSim.not_exit (W := vs ++ [Val.i32 (intTestOp .i32 .eqz c)]) (e₀ := .plain eqz)
        (x' := [.plain X]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp)
        (by simp) hk (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
    | phase₂ X hX c =>
      obtain ⟨hv, hbr, hret, hrc, hth⟩ := boolConsumer_inert hX
      exact GuardSim.not_exit (W := vs ++ [Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c))])
        (e₀ := .plain X) (x' := []) hv hbr hret hrc (by simp) hth hk
        (by simpa [vals, Val.i32, constI32, List.append_assoc] using he)
  values := by
    intro s u f vs us x y hst hxy hx
    exfalso
    have hall : x.all Admin.isVal = (vals us).all Admin.isVal :=
      congrArg (fun es => es.all Admin.isVal) hx
    cases hxy with
    | start X hX => exact absurd hall (by simp [Admin.isVal, Admin.val?])
    | phase₁ X hX c =>
      exact absurd hall (by simp [Admin.isVal, Admin.val?, constI32, Val.i32, Val.toAdmin])
    | phase₂ X hX c =>
      have hmem : ∀ a ∈ [constI32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz c)), Admin.plain X],
          a.val? ≠ none := by
        rw [hx]; intro a ha; exact Det.mem_vals ha
      exact hmem (.plain X) (by simp) (boolConsumer_inert hX).1

/-! ## The result simulates the original -/

theorem resultBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => eBI b a) resB teeCodeRank where
  src := by
    intro x y h
    cases h with
    | mk X hX => exact .mk X hX
  step := by
    intro s u s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | mk X hX =>
      show ∃ (t' : Store H) (es'' : List Admin),
        (Relation.TransGen (Step P closedHost)
            ⟨u, f, vals vs ++ [.plain eqz, .plain eqz, .plain X] ++ rest'⟩ ⟨t', f', es''⟩ ∨
          (t' = u ∧ f' = f ∧ es'' = vals vs ++ [.plain eqz, .plain eqz, .plain X] ++ rest' ∧
            teeCodeRank es' < teeCodeRank (vals vs ++ [.plain X] ++ rest))) ∧
        StoreRel F s' t' ∧ AdminsRel (fun a b => eBI b a) resB es' es''
      have hs : Step P closedHost ⟨s, f, vals vs ++ .plain X :: rest⟩ ⟨s', f', es'⟩ := by
        simpa using hstep
      obtain ⟨pre, pre', c, code, hvs, hs₁, hf₁, he₁, hrun⟩ := consumer_step_inv hX hs
      rw [hvs, hs₁, hf₁, he₁]
      exact ⟨u, vals pre ++ code ++ rest', Or.inl (eqz_eqz_consumer_steps hrun), hst,
        (AdminsRel.refl _).append hrest⟩
  exit := by
    intro s u f vs us x y kk j hst hxy hk he
    exfalso
    cases hxy with
    | mk X hX =>
      obtain ⟨hv, hbr, hret, hrc, hth⟩ := boolConsumer_inert hX
      exact GuardSim.not_exit (W := vs) (e₀ := .plain X) (x' := []) hv hbr hret hrc (by simp)
        hth hk (by simpa using he)
  values := by
    intro s u f vs us x y hst hxy hx
    exfalso
    have hall : x.all Admin.isVal = (vals us).all Admin.isVal :=
      congrArg (fun es => es.all Admin.isVal) hx
    cases hxy with
    | mk X hX =>
      have hv : (Admin.plain X).val? = none := (boolConsumer_inert hX).1
      exact absurd hall (by simp [Admin.isVal, hv])

end Silmaril.Proofs.Wasm.Binaryen.EqzPair
