module

public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.CodeSimClosed
public import Silmaril.Wasm.Binaryen.Pass.ConstBranch
public import Silmaril.Wasm.SingleThreaded.HeadInversion

@[expose] public section

/-! # The constant-condition fold is export equivalent

`ConstBranch.constBranch` (`Pass/ConstBranch.lean`) rewrites three **original** shapes
into their **results**:

* `i32.const c; if bt A B` into `block bt X'`, with `X'` the rewritten arm that `c`
  selects: the result enters the block in one step, the original takes two (`if` and
  the block entry) to the same label;
* `i32.const c; br_if l` (`c ≠ 0`) into `br l`: the result is an exit kernel, which the
  original reaches in one step;
* `i32.const 0; br_if l` into `nop`: both sides step to the empty sequence.

`cbBaseSim` is the `BaseSim` with the result on the left, as for the arm swap
(`IfSwapSim.lean`). No intermediate runtime state is needed, and nothing reads the
frame. The original deterministic theorem obtains the converse from the closed
host (`CodeSimClosed.exportEquiv_of_baseSim`); the result side holds no host-call
redex (`cb_noRedex`). `ConstBranchAny.lean` supplies a direct converse for every
numerical profile. The base pairs are stratified so that a kept arm may hold base pairs.
-/

namespace Silmaril.Wasm.Binaryen.ConstBranch

open Execution.Core Execution.Core.Sim Validation Numerics
open SingleThreaded (decompose? decompHead)

variable {H : Type} {P : Profile}

/-! ## Base relations -/

/-- Source base pairs (original, result), stratified so that the kept arm may itself
hold base pairs. -/
def SBI : Nat → List Instr → List Instr → Prop
  | 0, _, _ => False
  | n + 1, x, y =>
    (∃ (bt : BlockType) (c : BitVec 32) (A B X' : List Instr),
      InstrsRel (SBI n) (if c = 0 then B else A) X' ∧
      x = [.intConst .i32 c, .if_ bt A B] ∧ y = [.block bt X']) ∨
    (∃ (c : BitVec 32) (l : LabelIdx), c ≠ 0 ∧ x = [.intConst .i32 c, .brIf l] ∧ y = [.br l]) ∨
    (∃ l : LabelIdx, x = [.intConst .i32 0, .brIf l] ∧ y = [.nop])

/-- Source base pairs: the original on the left, the folded form on the right. -/
def cbBI (x y : List Instr) : Prop := ∃ n, SBI n x y

/-- Runtime base pairs: the lowered source pairs. -/
def cbB (x y : List Admin) : Prop :=
  (∃ (bt : BlockType) (c : BitVec 32) (A B X' : List Instr),
    InstrsRel cbBI (if c = 0 then B else A) X' ∧
    x = [constI32 c, .plain (.if_ bt A B)] ∧ y = [.plain (.block bt X')]) ∨
  (∃ (c : BitVec 32) (l : LabelIdx), c ≠ 0 ∧ x = [constI32 c, .plain (.brIf l)] ∧
    y = [.plain (.br l)]) ∨
  (∃ l : LabelIdx, x = [constI32 0, .plain (.brIf l)] ∧ y = [.plain .nop])

theorem instrsRel_cb {n : Nat} {x y : List Instr} (h : InstrsRel (SBI n) x y) :
    InstrsRel cbBI x y :=
  GuardSim.InstrsRel.mono (fun _ _ h => ⟨n, h⟩) h

/-! ## Inverting the head steps of the result side -/

set_option hygiene false in
/-- A family rule at a control instruction is impossible. -/
local macro "fam_no" : tactic => `(tactic| first
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | exact absurd (SingleThreaded.Det.famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2
      (by simp [SingleThreaded.Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

/-- `block` enters its label. -/
theorem head_block {s : Store H} {f : Frame} {args : List Val} {bt : BlockType}
    {body : List Instr} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain (.block bt body)) c₀) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ args.length = t₁.length ∧
      c₀ = ⟨s, f, [.label t₂.length [] (vals args ++ expression body)]⟩ :=
  SingleThreaded.head_block h

/-- A bare `br` does not step. -/
theorem head_br {s : Store H} {f : Frame} {args : List Val} {l : LabelIdx} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain (.br l)) c₀) : False := by
  cases h <;> fam_no

/-- `nop` steps to nothing. -/
theorem head_nop {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain .nop) c₀) :
    args = [] ∧ c₀ = ⟨s, f, []⟩ := by
  have hv := h.fam_inv (by simp [SingleThreaded.Det.famOf])
  simp only [SingleThreaded.Det.famOf, SingleThreaded.Det.FamRel] at hv
  obtain ⟨is', hv, rfl⟩ := hv
  generalize hc : vals args ++ [Admin.plain .nop] = l at hv
  cases hv with
  | nop =>
    obtain ⟨h1, -⟩ := (SingleThreaded.Det.append_singleton_inj (l₂ := [])).mp hc
    exact ⟨GuardSim.vals_eq_nil h1, rfl⟩
  | _ =>
    have := congrArg List.getLast? hc
    simp at this

/-- An exit kernel at a lone `br` is that `br`. -/
theorem exit_br {vs us : List Val} {l : LabelIdx} {k j : List Admin} (hk : Exit k)
    (h : vals vs ++ [.plain (.br l)] = vals us ++ k ++ j) :
    us = vs ∧ k = [.plain (.br l)] ∧ j = [] := by
  have key : ∀ (pre : List Val) (e : Admin), e.val? = none → k = vals pre ++ [e] →
      vs = us ++ pre ∧ Admin.plain (.br l) = e ∧ [] = j := by
    intro pre e hen hke
    have h' : vals vs ++ Admin.plain (.br l) :: [] = vals (us ++ pre) ++ e :: j := by
      rw [show vals vs ++ Admin.plain (.br l) :: [] = vals vs ++ [.plain (.br l)] from rfl, h, hke]
      simp
    exact vals_append_cons_inj rfl hen h'
  cases hk with
  | br l' =>
    obtain ⟨h1, h2, h3⟩ := key [] _ rfl rfl
    simp only [List.append_nil] at h1
    simp only [Admin.plain.injEq, Instr.br.injEq] at h2
    exact ⟨h1.symm, by rw [h2], h3.symm⟩
  | return_ => exact absurd (key [] _ rfl rfl).2.1 (by simp)
  | returnCallRef hc =>
    obtain ⟨-, h2, -⟩ := key [] _ (SingleThreaded.Det.IsReturnCallRef.val_none hc) rfl
    rw [← h2] at hc
    simp [Admin.IsReturnCallRef] at hc
  | trap => exact absurd (key [] _ rfl rfl).2.1 (by simp)
  | throw a => exact absurd (key [.ref (.exn a)] _ rfl rfl).2.1 (by simp)

/-! ## The simulation -/

/-- The original runs `if` and the block entry to the label that the folded block
enters. -/
theorem original_run_if {s : Store H} {f : Frame} (vs args : List Val) (rest : List Admin)
    (bt : BlockType) (A B : List Instr) (c : BitVec 32) {t₁ t₂ : List CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : args.length = t₁.length) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, vals (vs ++ args) ++ [constI32 c, .plain (.if_ bt A B)] ++ rest⟩
      ⟨s, f, vals vs ++ [.label t₂.length []
        (vals args ++ expression (if c = 0 then B else A))] ++ rest⟩ := by
  have h1 : Step P closedHost
      ⟨s, f, vals (vs ++ args) ++ [constI32 c, .plain (.if_ bt A B)] ++ rest⟩
      ⟨s, f, vals (vs ++ args) ++ [.plain (.block bt (if c = 0 then B else A))] ++ rest⟩ := by
    refine Step.append_right (Step.vals_left ?_ _) rest
    by_cases hc : c = 0
    · subst hc
      simpa only [↓reduceIte] using Step.ifFalse (P := P) (host := closedHost) (s := s) (f := f)
        (bt := bt) (b₁ := A) (b₂ := B)
    · simpa only [hc, ↓reduceIte] using Step.ifTrue (P := P) (host := closedHost) (s := s)
        (f := f) (bt := bt) (b₁ := A) (b₂ := B) hc
  have h2 : Step P closedHost
      ⟨s, f, vals (vs ++ args) ++ [.plain (.block bt (if c = 0 then B else A))] ++ rest⟩
      ⟨s, f, vals vs ++ [.label t₂.length []
        (vals args ++ expression (if c = 0 then B else A))] ++ rest⟩ := by
    have := Step.append_right (Step.vals_left (Step.block (P := P) (host := closedHost) (s := s)
      (body := if c = 0 then B else A) hbt hm) vs) rest
    simpa only [vals_append, List.append_assoc] using this
  exact .tail (.single h1) h2

/-- **The folded form simulates the original**: `BaseSim` with the result on the left. -/
theorem cbBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => cbBI b a) (fun a b => cbB b a) where
  src := by
    rintro x y ⟨n, h⟩
    cases n with
    | zero => exact h.elim
    | succ n =>
      rcases h with ⟨bt, c, A, B, X', hX, rfl, rfl⟩ | ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
      · exact .inl ⟨bt, c, A, B, X', instrsRel_cb hX, rfl, rfl⟩
      · exact .inr (.inl ⟨c, l, hc, rfl, rfl⟩)
      · exact .inr (.inr ⟨l, rfl, rfl⟩)
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    rcases hxy with ⟨bt, c, A, B, X', hX, rfl, rfl⟩ | ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
    · rw [show vals vs ++ [Admin.plain (.block bt X')] ++ rest =
        vals vs ++ .plain (.block bt X') :: rest by simp] at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
      obtain ⟨t₁, t₂, hbt, hm, rfl⟩ := head_block hh
      subst hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨rfl, rfl, rfl⟩ := hc'
      refine ⟨t, vals vs₀ ++ [.label t₂.length []
        (vals args ++ expression (if c = 0 then B else A))] ++ rest',
        Or.inl (original_run_if vs₀ args rest' bt A B c hbt hm), hst, ?_⟩
      exact ((AdminsRel.refl _).append (AdminsRel.cons (AdminRel.label _ .nil
        ((AdminsRel.refl _).append (AdminsRel.src hX.flip))) .nil)).append hrest
    · exfalso
      rw [show vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals vs ++ .plain (.br l) :: rest by simp] at hstep
      obtain ⟨vs₀, args, c₀, -, hh, -⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
      exact head_br hh
    · rw [show vals vs ++ [Admin.plain .nop] ++ rest = vals vs ++ .plain .nop :: rest by simp]
        at hstep
      obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
      obtain ⟨rfl, rfl⟩ := head_nop hh
      simp only [List.append_nil] at hW
      subst hW
      simp only [Config.mk.injEq] at hc'
      obtain ⟨rfl, rfl, rfl⟩ := hc'
      refine ⟨t, vals vs ++ [] ++ rest',
        Or.inl (.single (Step.append_right (Step.vals_left Step.brIfFalse vs) rest')), hst, ?_⟩
      simpa using (AdminsRel.refl (vals vs)).append hrest
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    rcases hxy with ⟨bt, c, A, B, X', -, rfl, rfl⟩ | ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
    · exfalso
      refine GuardSim.not_exit (us := us) (j := j) (W := vs) (e₀ := .plain (.block bt X'))
        (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
    · obtain ⟨rfl, rfl, rfl⟩ := exit_br hk he
      exact ⟨t, [], .single (by simpa using Step.vals_left (Step.brIfTrue (P := P)
        (host := closedHost) (s := t) (f := f) (l := l) hc) us), hst⟩
    · exfalso
      refine GuardSim.not_exit (us := us) (j := j) (W := vs) (e₀ := .plain .nop)
        (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
      all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    rcases hxy with ⟨bt, c, A, B, X', -, rfl, rfl⟩ | ⟨c, l, hc, rfl, rfl⟩ | ⟨l, rfl, rfl⟩
    · exact hall (.plain (.block bt X')) (by simp) rfl
    · exact hall (.plain (.br l)) (by simp) rfl
    · exact hall (.plain .nop) (by simp) rfl

/-- The result side holds no host-call redex. -/
theorem cb_noRedex : CodeSimClosed.NoRedexB H (fun a b => cbB b a) := by
  intro x y hxy s vs rest
  have key : ∀ i : Instr, (Admin.plain i).val? = none → (Admin.plain i).isCallRef = false →
      x = [.plain i] → decompose? s (vals vs ++ x ++ rest) = none := by
    rintro i hv hi rfl
    rw [show vals vs ++ [Admin.plain i] ++ rest = vals vs ++ .plain i :: rest by simp]
    exact SingleThreaded.decompose?_vals_cons_none hv
      (fun _ _ => SingleThreaded.decompHead_plain hi)
  rcases hxy with ⟨bt, c, A, B, X', -, -, rfl⟩ | ⟨c, l, -, -, rfl⟩ | ⟨l, -, rfl⟩
  all_goals exact key _ rfl rfl rfl

/-! ## The pass relates every body to its result -/

theorem SBI_succ : ∀ {n : Nat} {x y : List Instr}, SBI n x y → SBI (n + 1) x y
  | 0, _, _, h => h.elim
  | _ + 1, _, _, .inl ⟨bt, c, A, B, X', hX, hx, hy⟩ =>
    .inl ⟨bt, c, A, B, X', GuardSim.InstrsRel.mono (fun _ _ h => SBI_succ h) hX, hx, hy⟩
  | _ + 1, _, _, .inr h => .inr h

theorem SBI_mono {n m : Nat} (h : n ≤ m) {x y : List Instr} (hg : SBI n x y) : SBI m x y := by
  induction h with
  | refl => exact hg
  | step _ ih => exact SBI_succ ih

theorem instrsRel_le {n m : Nat} (h : n ≤ m) {x y : List Instr} (hr : InstrsRel (SBI n) x y) :
    InstrsRel (SBI m) x y :=
  GuardSim.InstrsRel.mono (fun _ _ => SBI_mono h) hr

theorem constLeaf?_some {x : BExpr} {c : BitVec 32} (h : constLeaf? x = some c) :
    x = .op (.intConst .i32 c) [] := by
  unfold constLeaf? at h
  split at h
  · cases h; rfl
  · cases h

theorem constCond?_some {cs : List BExpr} {c : BitVec 32} (h : constCond? cs = some c) :
    cs = [.op (.intConst .i32 c) []] := by
  unfold constCond? at h
  split at h
  · rw [constLeaf?_some h]
  · cases h

theorem opNode_default {i : Instr} {args args' : List BExpr} (h : ∀ l, i ≠ .brIf l) :
    opNode i args args' = .op i args' := by
  unfold opNode
  split
  · exact absurd rfl (h _)
  · rfl

/-- The congruence case of an `if`. -/
theorem if_congr {n₁ n₂ n₃ : Nat} {bt : BlockType} {c c' t t' e e' : List Instr}
    (h₁ : InstrsRel (SBI n₁) c c') (h₂ : InstrsRel (SBI n₂) t t') (h₃ : InstrsRel (SBI n₃) e e') :
    InstrsRel (SBI (max n₁ (max n₂ n₃))) (c ++ [.if_ bt t e]) (c' ++ [.if_ bt t' e']) :=
  (instrsRel_le (by omega) h₁).append
    (InstrsRel.cons (InstrRel.if_ bt (instrsRel_le (by omega) h₂) (instrsRel_le (by omega) h₃)) .nil)

/-- The folded `br_if` pair. -/
theorem brIf_base (c : BitVec 32) (l : LabelIdx) :
    SBI 1 [.intConst .i32 c, .brIf l]
      (if c = 0 then BExpr.op .nop [] else BExpr.op (.br l) []).lower := by
  by_cases hc : c = 0
  · subst hc
    simp only [↓reduceIte, BExpr.lower_op, BExpr.lowerList_nil, List.nil_append]
    exact Or.inr (Or.inr ⟨l, rfl, rfl⟩)
  · simp only [hc, ↓reduceIte, BExpr.lower_op, BExpr.lowerList_nil, List.nil_append]
    exact Or.inr (Or.inl ⟨c, l, hc, rfl, rfl⟩)

/-- The folded `if` pair, given the relations of the arms. -/
theorem if_base {n₂ n₃ : Nat} (bt : BlockType) (k : BitVec 32) {t e t' e' : List BExpr}
    (h₂ : InstrsRel (SBI n₂) (BExpr.lowerList t) (BExpr.lowerList t'))
    (h₃ : InstrsRel (SBI n₃) (BExpr.lowerList e) (BExpr.lowerList e')) :
    SBI (max n₂ n₃ + 1) [.intConst .i32 k, .if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
      [.block bt (BExpr.lowerList (if k = 0 then e' else t'))] := by
  refine Or.inl ⟨bt, k, _, _, _, ?_, rfl, rfl⟩
  split
  · exact instrsRel_le (by omega) h₃
  · exact instrsRel_le (by omega) h₂

mutual
theorem foldE_rel : ∀ x : BExpr, ∃ n, InstrsRel (SBI n) x.lower (foldE x).lower
  | .op i args => by
    obtain ⟨n, h⟩ := foldL_rel args
    by_cases hi : ∃ l, i = .brIf l
    · obtain ⟨l, rfl⟩ := hi
      simp only [foldE, opNode, brIfNode]
      cases hc : constCond? args with
      | none => exact ⟨n, by simpa using h.append (InstrsRel.refl [.brIf l])⟩
      | some c =>
        obtain rfl := constCond?_some hc
        exact ⟨1, by simpa using InstrsRel.base (brIf_base c l)⟩
    · refine ⟨n, ?_⟩
      rw [foldE, opNode_default (fun l hl => hi ⟨l, hl⟩)]
      simpa using h.append (InstrsRel.refl [i])
  | .block bt body => by
    obtain ⟨n, h⟩ := foldL_rel body
    exact ⟨n, by simpa [foldE, BExpr.lower] using InstrsRel.cons (InstrRel.block bt h) .nil⟩
  | .loop bt body => by
    obtain ⟨n, h⟩ := foldL_rel body
    exact ⟨n, by simpa [foldE, BExpr.lower] using InstrsRel.cons (InstrRel.loop bt h) .nil⟩
  | .tryTable bt cs body => by
    obtain ⟨n, h⟩ := foldL_rel body
    exact ⟨n, by simpa [foldE, BExpr.lower] using
      InstrsRel.cons (InstrRel.tryTable bt cs h) .nil⟩
  | .if_ bt c t e => by
    obtain ⟨n₁, h₁⟩ := foldL_rel c
    obtain ⟨n₂, h₂⟩ := foldL_rel t
    obtain ⟨n₃, h₃⟩ := foldL_rel e
    cases hk : constCond? c with
    | none =>
      refine ⟨max n₁ (max n₂ n₃), ?_⟩
      simpa [foldE, ifNode, hk, BExpr.lower] using if_congr (bt := bt) h₁ h₂ h₃
    | some k =>
      obtain rfl := constCond?_some hk
      refine ⟨max n₂ n₃ + 1, ?_⟩
      simp only [foldE, ifNode, hk, BExpr.lower, BExpr.lowerList_cons, BExpr.lowerList_nil,
        List.nil_append, List.append_nil, List.singleton_append]
      exact .base (if_base bt k h₂ h₃)
termination_by x => sizeOf x
decreasing_by all_goals simp_wf <;> omega
theorem foldL_rel : ∀ es : List BExpr,
    ∃ n, InstrsRel (SBI n) (BExpr.lowerList es) (BExpr.lowerList (foldL es))
  | [] => ⟨0, by simpa [foldL] using .nil⟩
  | [x] => by
    obtain ⟨n, h⟩ := foldE_rel x
    exact ⟨n, by simpa [foldL] using h⟩
  | x :: y :: es => by
    unfold foldL
    split
    · next _ k bt t e hx =>
      obtain rfl := constLeaf?_some hx
      obtain ⟨n₂, h₂⟩ := foldL_rel t
      obtain ⟨n₃, h₃⟩ := foldL_rel e
      obtain ⟨n₄, h₄⟩ := foldL_rel es
      refine ⟨max (max n₂ n₃ + 1) n₄, ?_⟩
      have := (InstrsRel.base (BI := SBI (max (max n₂ n₃ + 1) n₄))
        (SBI_mono (le_max_left _ _) (if_base bt k h₂ h₃))).append
        (instrsRel_le (le_max_right _ _) h₄)
      simpa [BExpr.lower] using this
    · next _ k l hx =>
      obtain rfl := constLeaf?_some hx
      obtain ⟨n₄, h₄⟩ := foldL_rel es
      refine ⟨max 1 n₄, ?_⟩
      have := (InstrsRel.base (BI := SBI (max 1 n₄))
        (SBI_mono (le_max_left _ _) (brIf_base k l))).append
        (instrsRel_le (le_max_right _ _) h₄)
      simpa using this
    · next y _ _ _ =>
      obtain ⟨n₁, h₁⟩ := foldE_rel x
      obtain ⟨n₂, h₂⟩ := foldL_rel (y :: es)
      refine ⟨max n₁ n₂, ?_⟩
      simpa using (instrsRel_le (le_max_left _ _) h₁).append (instrsRel_le (le_max_right _ _) h₂)
termination_by es => sizeOf es
decreasing_by all_goals (try subst_vars); all_goals simp_wf; all_goals omega
end

/-- **Every body is related to its folded form.** -/
theorem foldL_cbBI (es : List BExpr) :
    InstrsRel cbBI (BExpr.lowerList es) (BExpr.lowerList (foldL es)) :=
  (foldL_rel es).elim fun _ h => instrsRel_cb h

theorem constBranch_bodiesRel (m : BModule) :
    ModuleBodiesRel (fun a b => cbBI b a) (constBranch m).lower m.lower := by
  refine ModuleBodiesRel.flip ⟨rfl, ?_⟩
  simp only [BModule.lower, constBranch, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, foldL_cbBI f.body⟩ ih

/-- **The constant-condition fold is export equivalent** under the closed host, for valid
input and output. -/
theorem constBranch_sound {o : GrowKind → Nat → Nat → Nat → Bool} {m : BModule} (hm : m.Ok)
    (hm' : (constBranch m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (constBranch m).lower
      m.lower :=
  CodeSimClosed.exportEquiv_of_baseSim cbBaseSim cb_noRedex (constBranch_bodiesRel m) hm' hm

end Silmaril.Wasm.Binaryen.ConstBranch
