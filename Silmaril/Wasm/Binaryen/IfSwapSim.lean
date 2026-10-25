module

public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.CodeSimClosed
public import Silmaril.Wasm.Binaryen.Pass.IfSwap

@[expose] public section

/-! # The arm swap is export equivalent

`IfSwap.ifSwap` (`Pass/IfSwap.lean`) turns `i32.eqz; if bt A B` (the **original**)
into `if bt B' A'` (the **result**, with `A'`, `B'` the rewritten arms). With the
operand `c` on the stack:

* the result takes one step, `if`, to `block bt (c = 0 ? A' : B')`;
* the original takes two, `eqz` and `if`, to `block bt (eqz c = 0 ? B : A)`, the same
  arm.

`swapBaseSim` is the `BaseSim` with the result on the left: its `if` step is matched
by the two steps of the original, and the two blocks have related bodies. No
intermediate runtime state is needed, and nothing reads the frame. As for guard
inversion (`RemoveUnusedBrsGuardSim.lean`), the converse comes from the closed host
(`CodeSimClosed.exportEquiv_of_baseSim`); the result side holds no host-call redex
(`swap_noRedex`). The base pairs are stratified so that the arms may hold base pairs.
-/

namespace Silmaril.Wasm.Binaryen.IfSwap

open Execution.Core Execution.Core.Sim Validation Numerics
open SingleThreaded (decompose? decompHead)

variable {H : Type} {P : Profile}

/-! ## Base relations -/

/-- Source base pairs (original, result), stratified so that the arms may themselves
hold base pairs. -/
def SBI : Nat → List Instr → List Instr → Prop
  | 0, _, _ => False
  | n + 1, x, y => ∃ (bt : BlockType) (A A' B B' : List Instr),
      InstrsRel (SBI n) A A' ∧ InstrsRel (SBI n) B B' ∧
      x = [.intTestOp .i32 .eqz, .if_ bt A B] ∧ y = [.if_ bt B' A']

/-- Source base pairs: the original on the left, the swapped `if` on the right. -/
def swapBI (x y : List Instr) : Prop := ∃ n, SBI n x y

/-- Runtime base pairs: the lowered source pairs. -/
def swapB (x y : List Admin) : Prop :=
  ∃ (bt : BlockType) (A A' B B' : List Instr), InstrsRel swapBI A A' ∧ InstrsRel swapBI B B' ∧
    x = [.plain (.intTestOp .i32 .eqz), .plain (.if_ bt A B)] ∧ y = [.plain (.if_ bt B' A')]

theorem instrsRel_swap {n : Nat} {x y : List Instr} (h : InstrsRel (SBI n) x y) :
    InstrsRel swapBI x y :=
  GuardSim.InstrsRel.mono (fun _ _ h => ⟨n, h⟩) h

/-! ## The simulation -/

/-- The original runs `eqz` and `if` to the arm that the swapped `if` selects. -/
theorem original_run {s : Store H} {f : Frame} (vs : List Val) (rest : List Admin)
    (bt : BlockType) (A B : List Instr) (c : BitVec 32) :
    Relation.TransGen (Step P closedHost)
      ⟨s, f, vals (vs ++ [.num ⟨.int .i32, c⟩]) ++ [.plain (.intTestOp .i32 .eqz),
        .plain (.if_ bt A B)] ++ rest⟩
      ⟨s, f, vals vs ++ [.plain (.block bt (if c = 0 then A else B))] ++ rest⟩ := by
  have h1 : Step P closedHost
      ⟨s, f, vals (vs ++ [.num ⟨.int .i32, c⟩]) ++ [.plain (.intTestOp .i32 .eqz),
        .plain (.if_ bt A B)] ++ rest⟩
      ⟨s, f, vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain (.if_ bt A B)] ++ rest⟩ := by
    have := Step.vals_left (Step.append_right (Step.numeric (P := P) (host := closedHost) (s := s)
      (f := f) (NumericStep.intTestOp (t := .i32) (op := .eqz) (x := c))) (.plain (.if_ bt A B) :: rest)) vs
    simpa [vals, constI32, Val.i32, Val.toAdmin] using this
  have h2 : Step P closedHost
      ⟨s, f, vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain (.if_ bt A B)] ++ rest⟩
      ⟨s, f, vals vs ++ [.plain (.block bt (if c = 0 then A else B))] ++ rest⟩ := by
    refine Step.append_right (Step.vals_left ?_ vs) rest
    by_cases hc : c = 0
    · have hz : intTestOp .i32 .eqz c ≠ 0 := fun h => (GuardSim.eqz_eq_zero c).mp h hc
      simpa only [hc, ↓reduceIte] using Step.ifTrue (P := P) (host := closedHost) (s := s) (f := f)
        (bt := bt) (b₁ := A) (b₂ := B) hz
    · have hz : intTestOp .i32 .eqz c = 0 := (GuardSim.eqz_eq_zero c).mpr hc
      rw [hz]
      simpa only [hc, ↓reduceIte] using Step.ifFalse (P := P) (host := closedHost) (s := s) (f := f)
        (bt := bt) (b₁ := A) (b₂ := B)
  exact .tail (.single h1) h2

/-- **The swapped `if` simulates the original**: `BaseSim` with the result on the left. -/
theorem swapBaseSim {F : FuncInst H → FuncInst H → Prop} :
    BaseSim P closedHost F (fun a b => swapBI b a) (fun a b => swapB b a) where
  src := by
    rintro x y ⟨n, h⟩
    cases n with
    | zero => exact h.elim
    | succ n =>
      obtain ⟨bt, A, A', B, B', hA, hB, rfl, rfl⟩ := h
      exact ⟨bt, A, A', B, B', instrsRel_swap hA, instrsRel_swap hB, by simp [expression],
        by simp [expression]⟩
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest hstep
    obtain ⟨bt, A, A', B, B', hA, hB, rfl, rfl⟩ := hxy
    have e : vals vs ++ [Admin.plain (.if_ bt B' A')] ++ rest =
        vals vs ++ .plain (.if_ bt B' A') :: rest := by simp
    rw [e] at hstep
    obtain ⟨vs₀, args, c₀, hW, hh, hc'⟩ := GuardSim.head_inv rfl (by simp) (by simp) hstep
    obtain ⟨c, rfl, rfl⟩ := GuardSim.head_if hh
    subst hW
    simp only [Config.mk.injEq] at hc'
    obtain ⟨h1, h2, h3⟩ := hc'
    subst h3
    have h1 := h1.symm
    have h2 := h2.symm
    subst h1 h2
    refine ⟨t, vals vs₀ ++ [.plain (.block bt (if c = 0 then A else B))] ++ rest',
      Or.inl (original_run vs₀ rest' bt A B c), hst, ?_⟩
    have hsel : InstrsRel (fun a b => swapBI b a) (if c = 0 then A' else B')
        (if c = 0 then A else B) := by
      split
      · exact hA.flip
      · exact hB.flip
    exact ((AdminsRel.refl _).append
      (AdminsRel.cons (AdminRel.plain (InstrRel.block bt hsel)) .nil)).append hrest
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    obtain ⟨bt, A, A', B, B', -, -, rfl, rfl⟩ := hxy
    refine GuardSim.not_exit (us := us) (j := j) (W := vs) (e₀ := .plain (.if_ bt B' A'))
      (x' := []) rfl ?_ ?_ ?_ ?_ ?_ hk ?_
    all_goals first | (simp [Admin.IsReturnCallRef]; done) | simpa using he
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    obtain ⟨bt, A, A', B, B', -, -, rfl, rfl⟩ := hxy
    have hall : ∀ a ∈ [Admin.plain (.if_ bt B' A')], a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    exact hall (.plain (.if_ bt B' A')) (by simp) rfl

/-- The result side holds no host-call redex. -/
theorem swap_noRedex : CodeSimClosed.NoRedexB H (fun a b => swapB b a) := by
  intro x y hxy s vs rest
  obtain ⟨bt, A, A', B, B', -, -, rfl, rfl⟩ := hxy
  rw [show vals vs ++ [Admin.plain (.if_ bt B' A')] ++ rest =
    vals vs ++ .plain (.if_ bt B' A') :: rest by simp]
  exact SingleThreaded.decompose?_vals_cons_none rfl
    (fun _ _ => SingleThreaded.decompHead_plain rfl)

/-! ## The pass relates every body to its result -/

theorem SBI_succ : ∀ {n : Nat} {x y : List Instr}, SBI n x y → SBI (n + 1) x y
  | 0, _, _, h => h.elim
  | _ + 1, _, _, ⟨bt, A, A', B, B', hA, hB, hx, hy⟩ =>
    ⟨bt, A, A', B, B', GuardSim.InstrsRel.mono (fun _ _ h => SBI_succ h) hA,
      GuardSim.InstrsRel.mono (fun _ _ h => SBI_succ h) hB, hx, hy⟩

theorem SBI_mono {n m : Nat} (h : n ≤ m) {x y : List Instr} (hg : SBI n x y) : SBI m x y := by
  induction h with
  | refl => exact hg
  | step _ ih => exact SBI_succ ih

theorem instrsRel_le {n m : Nat} (h : n ≤ m) {x y : List Instr} (hr : InstrsRel (SBI n) x y) :
    InstrsRel (SBI m) x y :=
  GuardSim.InstrsRel.mono (fun _ _ => SBI_mono h) hr

theorem swapIf_ne_op {bt : BlockType} {c t e : List BExpr} {i : Instr} {args : List BExpr} :
    swapIf bt c t e ≠ .op i args := by
  unfold swapIf
  split <;> simp

theorem swapE_op {x : BExpr} {i : Instr} {a : List BExpr} (h : swapE x = .op i a) :
    ∃ args, x = .op i args ∧ swapL args = a := by
  cases x with
  | op j args =>
    simp only [swapE, BExpr.op.injEq] at h
    exact ⟨args, by rw [h.1], h.2⟩
  | if_ bt c t e => exact absurd h swapIf_ne_op
  | _ => simp [swapE] at h

theorem swapL_single {c : List BExpr} {y : BExpr} (h : swapL c = [y]) :
    ∃ x, c = [x] ∧ swapE x = y := by
  cases c with
  | nil => simp [swapL] at h
  | cons x cs =>
    simp only [swapL, List.cons.injEq] at h
    cases cs with
    | nil => exact ⟨x, rfl, h.1⟩
    | cons _ _ => simp [swapL] at h

/-- An `if` whose condition is not an `i32.eqz` tree is rebuilt as it is. -/
theorem swapIf_default {bt : BlockType} {c : List BExpr} {t e : List BExpr}
    (hc : ¬ ∃ args, c = [.op (.intTestOp .i32 .eqz) args]) :
    swapIf bt (swapL c) t e = .if_ bt (swapL c) t e := by
  unfold swapIf
  split
  · obtain ⟨x, rfl, hx⟩ := swapL_single ‹swapL c = _›
    obtain ⟨args, rfl, -⟩ := swapE_op hx
    exact (hc ⟨args, rfl⟩).elim
  · rfl

/-- An `if` with an empty else arm is rebuilt as it is. -/
theorem swapIf_nil {bt : BlockType} {c t : List BExpr} : swapIf bt c t [] = .if_ bt c t [] := by
  unfold swapIf
  split
  · rename_i h
    cases h
  · rfl

/-- The congruence case of an `if`. -/
theorem if_congr {n₁ n₂ n₃ : Nat} {bt : BlockType} {c c' t t' e e' : List Instr}
    (h₁ : InstrsRel (SBI n₁) c c') (h₂ : InstrsRel (SBI n₂) t t') (h₃ : InstrsRel (SBI n₃) e e') :
    InstrsRel (SBI (max n₁ (max n₂ n₃))) (c ++ [.if_ bt t e]) (c' ++ [.if_ bt t' e']) :=
  (instrsRel_le (by omega) h₁).append
    (InstrsRel.cons (InstrRel.if_ bt (instrsRel_le (by omega) h₂) (instrsRel_le (by omega) h₃)) .nil)

mutual
theorem swapE_rel : ∀ x : BExpr, ∃ n, InstrsRel (SBI n) x.lower (swapE x).lower
  | .op i args => by
    obtain ⟨n, h⟩ := swapL_rel args
    exact ⟨n, by simpa [swapE] using h.append (InstrsRel.refl [i])⟩
  | .block bt body => by
    obtain ⟨n, h⟩ := swapL_rel body
    exact ⟨n, by simpa [swapE, BExpr.lower] using InstrsRel.cons (InstrRel.block bt h) .nil⟩
  | .loop bt body => by
    obtain ⟨n, h⟩ := swapL_rel body
    exact ⟨n, by simpa [swapE, BExpr.lower] using InstrsRel.cons (InstrRel.loop bt h) .nil⟩
  | .tryTable bt cs body => by
    obtain ⟨n, h⟩ := swapL_rel body
    exact ⟨n, by simpa [swapE, BExpr.lower] using
      InstrsRel.cons (InstrRel.tryTable bt cs h) .nil⟩
  | .if_ bt c t e => by
    obtain ⟨n₁, h₁⟩ := swapL_rel c
    obtain ⟨n₂, h₂⟩ := swapL_rel t
    obtain ⟨n₃, h₃⟩ := swapL_rel e
    by_cases hc : ∃ args, c = [.op (.intTestOp .i32 .eqz) args]
    · obtain ⟨args, rfl⟩ := hc
      obtain ⟨n₀, h₀⟩ := swapL_rel args
      cases he : swapL e with
      | nil =>
        refine ⟨max n₁ (max n₂ n₃), ?_⟩
        have := if_congr (bt := bt) h₁ h₂ h₃
        rw [he] at this
        simpa [swapE, BExpr.lower, he, swapIf_nil] using this
      | cons y ys =>
        refine ⟨max n₀ (max n₂ n₃) + 1, ?_⟩
        have hs : swapE (.if_ bt [.op (.intTestOp .i32 .eqz) args] t e) =
            .if_ bt (swapL args) (y :: ys) (swapL t) := by
          simp [swapE, swapL, swapIf, he]
        rw [hs]
        have hb : InstrsRel (SBI (max n₀ (max n₂ n₃) + 1))
            [.intTestOp .i32 .eqz, .if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]
            [.if_ bt (BExpr.lowerList (y :: ys)) (BExpr.lowerList (swapL t))] := by
          refine .base ⟨bt, _, _, _, _, instrsRel_le (by omega) h₂, ?_, rfl, rfl⟩
          rw [← he]
          exact instrsRel_le (by omega) h₃
        have := (instrsRel_le (m := max n₀ (max n₂ n₃) + 1) (by omega) h₀).append hb
        simpa [BExpr.lower] using this
    · refine ⟨max n₁ (max n₂ n₃), ?_⟩
      simpa [swapE, BExpr.lower, swapIf_default hc] using if_congr (bt := bt) h₁ h₂ h₃
termination_by x => sizeOf x
theorem swapL_rel : ∀ es : List BExpr,
    ∃ n, InstrsRel (SBI n) (BExpr.lowerList es) (BExpr.lowerList (swapL es))
  | [] => ⟨0, .nil⟩
  | e :: es => by
    obtain ⟨n₁, h₁⟩ := swapE_rel e
    obtain ⟨n₂, h₂⟩ := swapL_rel es
    refine ⟨max n₁ n₂, ?_⟩
    simpa [swapL] using (instrsRel_le (by omega) h₁).append (instrsRel_le (by omega) h₂)
termination_by es => sizeOf es
end

/-- **Every body is related to its swapped form.** -/
theorem swapL_swapBI (es : List BExpr) :
    InstrsRel swapBI (BExpr.lowerList es) (BExpr.lowerList (swapL es)) :=
  (swapL_rel es).elim fun _ h => instrsRel_swap h

theorem ifSwap_bodiesRel (m : BModule) :
    ModuleBodiesRel (fun a b => swapBI b a) (ifSwap m).lower m.lower := by
  refine ModuleBodiesRel.flip ⟨rfl, ?_⟩
  simp only [BModule.lower, ifSwap, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, swapL_swapBI f.body⟩ ih

/-- **The arm swap is export equivalent** under the closed host, for valid input and
output. -/
theorem ifSwap_sound {o : GrowKind → Nat → Nat → Nat → Bool} {m : BModule} (hm : m.Ok)
    (hm' : (ifSwap m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (ifSwap m).lower
      m.lower :=
  CodeSimClosed.exportEquiv_of_baseSim swapBaseSim swap_noRedex (ifSwap_bodiesRel m) hm' hm

end Silmaril.Wasm.Binaryen.IfSwap
