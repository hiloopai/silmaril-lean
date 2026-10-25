module

public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.Pass.RewriteEquiv

@[expose] public section

/-! # P1: Precompute-lite (integer constant folding)

Binaryen's `Precompute` (`src/passes/Precompute.cpp`, version_133) evaluates
expressions whose operands are constants with its interpreter. The lite version
folds integer unary, test, binary and relational operators on constant
operands, bottom-up. A division or remainder that traps folds to
`unreachable`, which traps identically, so the pass is an equivalence (Binaryen
keeps the trapping expression; folding it is equally sound and simpler to
state).

Per-node correctness is a `Joinable` fact (`foldNode_joinable`: both sides step
to the same constant, or both to `trap`); the pass theorem is `.congr` plus
`.trans` via `SeqRefines.everywhere`.

**Scope.** This module does not establish the legacy general results the soundness theorems
`FoldCase.step`, `precRule_step`, `precompute_sound` and `precompute_module_sound`. The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- The constant of type `t` a leaf denotes. -/
def constOf? (t : IntType) : BExpr → Option (BitVec t.width)
  | .op (.intConst t' b) [] => if h : t' = t then some (h ▸ b) else none
  | _ => none

/-- Fold one node whose operands are constants. -/
def foldNode : BExpr → Option BExpr
  | .op (.intBinOp t o) [a, b] => do
      let x ← constOf? t a
      let y ← constOf? t b
      match Numerics.intBinOp t o x y with
      | .ok z => some (.op (.intConst t z) [])
      | .error _ => some (.op .unreachable [])
  | .op (.intUnOp t o) [a] => do
      let x ← constOf? t a
      some (.op (.intConst t (Numerics.intUnOp t o x)) [])
  | .op (.intTestOp t o) [a] => do
      let x ← constOf? t a
      some (.op (.intConst .i32 (Numerics.intTestOp t o x)) [])
  | .op (.intRelOp t o) [a, b] => do
      let x ← constOf? t a
      let y ← constOf? t b
      some (.op (.intConst .i32 (Numerics.intRelOp t o x y)) [])
  | _ => none

mutual
/-- Fold bottom-up. -/
def precE : BExpr → BExpr
  | .op i args =>
      let e := BExpr.op i (precL args)
      (foldNode e).getD e
  | .block bt b => .block bt (precL b)
  | .loop bt b => .loop bt (precL b)
  | .if_ bt c t e => .if_ bt (precL c) (precL t) (precL e)
  | .tryTable bt cs b => .tryTable bt cs (precL b)
/-- `precE` on a list. -/
def precL : List BExpr → List BExpr
  | [] => []
  | e :: es => precE e :: precL es
end

/-- The pass on a module. -/
def precompute (m : BModule) : BModule := m.mapBodies precL

open RTy

/-! ## The shapes of a fold -/

theorem constOf?_eq {t : IntType} {a : BExpr} {x : BitVec t.width} (h : constOf? t a = some x) :
    a = .op (.intConst t x) [] := by
  unfold constOf? at h
  split at h
  · next t' b =>
    split at h
    · next ht =>
      cases ht
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · cases h
  · cases h

/-- The successful folds. -/
inductive FoldCase : BExpr → BExpr → Prop where
  | binOk {t : IntType} {o : IntBinOp} {x y z : BitVec t.width}
      (h : Numerics.intBinOp t o x y = .ok z) :
      FoldCase (.op (.intBinOp t o) [.op (.intConst t x) [], .op (.intConst t y) []])
        (.op (.intConst t z) [])
  | binErr {t : IntType} {o : IntBinOp} {x y : BitVec t.width} {err : IntTrap}
      (h : Numerics.intBinOp t o x y = .error err) :
      FoldCase (.op (.intBinOp t o) [.op (.intConst t x) [], .op (.intConst t y) []])
        (.op .unreachable [])
  | un {t : IntType} {o : IntUnOp} {x : BitVec t.width} :
      FoldCase (.op (.intUnOp t o) [.op (.intConst t x) []])
        (.op (.intConst t (Numerics.intUnOp t o x)) [])
  | test {t : IntType} {o : IntTestOp} {x : BitVec t.width} :
      FoldCase (.op (.intTestOp t o) [.op (.intConst t x) []])
        (.op (.intConst .i32 (Numerics.intTestOp t o x)) [])
  | rel {t : IntType} {o : IntRelOp} {x y : BitVec t.width} :
      FoldCase (.op (.intRelOp t o) [.op (.intConst t x) [], .op (.intConst t y) []])
        (.op (.intConst .i32 (Numerics.intRelOp t o x y)) [])

theorem foldNode_cases {e e' : BExpr} (h : foldNode e = some e') : FoldCase e e' := by
  unfold foldNode at h
  split at h
  · next t o a b =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    rw [constOf?_eq hx, constOf?_eq hy]
    split at h
    · next z hz => cases h; exact FoldCase.binOk hz
    · next err herr => cases h; exact FoldCase.binErr herr
  · next t o a =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    rw [constOf?_eq hx]
    cases h
    exact FoldCase.un
  · next t o a =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    rw [constOf?_eq hx]
    cases h
    exact FoldCase.test
  · next t o a b =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    rw [constOf?_eq hx, constOf?_eq hy]
    cases h
    exact FoldCase.rel
  · cases h

/-! ## Small steps -/

theorem FoldCase.joinable {P : Profile} {C : Context} {it : InstrType} {e e' : BExpr}
    (h : FoldCase e e') : Joinable P C it [e] [e'] := by
  intro H s f vs _
  cases h with
  | binOk hz =>
    exact ⟨_, Relation.ReflTransGen.single
      (step_vals vs (Step.numeric (NumericStep.intBinOp hz))), Relation.ReflTransGen.refl⟩
  | binErr herr =>
    exact ⟨_,
      Relation.ReflTransGen.single (step_vals vs (Step.numeric (NumericStep.intBinOpTrap herr))),
      Relation.ReflTransGen.single (step_vals vs (Step.parametric ParametricStep.unreachable))⟩
  | un =>
    exact ⟨_, Relation.ReflTransGen.single (step_vals vs (Step.numeric NumericStep.intUnOp)),
      Relation.ReflTransGen.refl⟩
  | test =>
    exact ⟨_, Relation.ReflTransGen.single (step_vals vs (Step.numeric NumericStep.intTestOp)),
      Relation.ReflTransGen.refl⟩
  | rel =>
    exact ⟨_, Relation.ReflTransGen.single (step_vals vs (Step.numeric NumericStep.intRelOp)),
      Relation.ReflTransGen.refl⟩

/-- **Per-node correctness.** -/
theorem foldNode_joinable {P : Profile} {C : Context} {it : InstrType} {e e' : BExpr}
    (h : foldNode e = some e') (hok : SeqOk C [e] it) : Joinable P C it [e] [e'] := by
  have _ := hok
  intro H
  exact FoldCase.joinable (P := P) (C := C) (it := it) (foldNode_cases h)

/-! ## Typing -/

theorem FoldCase.pres {e e' : BExpr} (h : FoldCase e e') :
    PresL (BExpr.lowerList [e]) (BExpr.lowerList [e']) := by
  cases h with
  | @binOk t o x y z hz =>
    refine PresL.of_redex (A := [.intConst t x, .intConst t y, .intBinOp t o])
      (B := [.intConst t z]) fun lts => ⟨by simp, ⟨([], [.num (.int t)]), ?_, ?_⟩, ?_⟩
    · simp [effList, ieff, comp]
    · intro C it _ hE
      exact realize_eff hE (fun ts hts => by simpa using instrs_const (t := t) (b := z) ts hts)
        (by simp) (by simp)
    · exact goodOuts_of_noLocal (by simp)
  | @binErr t o x y err herr =>
    refine PresL.of_redex (A := [.intConst t x, .intConst t y, .intBinOp t o])
      (B := [.unreachable]) fun lts => ⟨by simp, ⟨([], [.num (.int t)]), ?_, ?_⟩, ?_⟩
    · simp [effList, ieff, comp]
    · intro C it _ hE
      refine realize_eff hE (fun ts hts => ?_) (by simp) (by simp)
      exact InstrsOk.instr (InstrOk.parametric (ParametricInstrOk.unreachable
        ⟨by simpa using hts, ResultOk.append hts (by simp), by simp⟩))
    · exact goodOuts_of_noLocal (by simp)
  | @un t o x =>
    refine PresL.of_redex (A := [.intConst t x, .intUnOp t o])
      (B := [.intConst t (Numerics.intUnOp t o x)]) fun lts =>
        ⟨by simp, ⟨([], [.num (.int t)]), ?_, ?_⟩, ?_⟩
    · simp [effList, ieff, comp]
    · intro C it _ hE
      exact realize_eff hE (fun ts hts => by
        simpa using instrs_const (t := t) (b := Numerics.intUnOp t o x) ts hts) (by simp) (by simp)
    · exact goodOuts_of_noLocal (by simp)
  | @test t o x =>
    refine PresL.of_redex (A := [.intConst t x, .intTestOp t o])
      (B := [.intConst .i32 (Numerics.intTestOp t o x)]) fun lts =>
        ⟨by simp, ⟨([], [Ty.i32]), ?_, ?_⟩, ?_⟩
    · simp [effList, ieff, comp]
    · intro C it _ hE
      exact realize_eff hE (fun ts hts => by
        simpa [Ty.i32] using instrs_const (t := .i32) (b := Numerics.intTestOp t o x) ts hts)
        (by simp) (by simp [Ty.i32])
    · exact goodOuts_of_noLocal (by simp)
  | @rel t o x y =>
    refine PresL.of_redex (A := [.intConst t x, .intConst t y, .intRelOp t o])
      (B := [.intConst .i32 (Numerics.intRelOp t o x y)]) fun lts =>
        ⟨by simp, ⟨([], [Ty.i32]), ?_, ?_⟩, ?_⟩
    · simp [effList, ieff, comp]
    · intro C it _ hE
      exact realize_eff hE (fun ts hts => by
        simpa [Ty.i32] using instrs_const (t := .i32) (b := Numerics.intRelOp t o x y) ts hts)
        (by simp) (by simp [Ty.i32])
    · exact goodOuts_of_noLocal (by simp)

theorem unOp_valid {C : Context} {t : IntType} {o : IntUnOp} {it : InstrType}
    (h : InstrOk C (.intUnOp t o) it) : o.valid t = true := by
  cases h with
  | numeric h => cases h; assumption
  | parametric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

/-! ## The pass as a rewrite sequence -/

/-- One fold, as a rewrite of a singleton. -/
def precRule (a b : List BExpr) : Prop := ∃ e e', a = [e] ∧ b = [e'] ∧ foldNode e = some e'

theorem precRule_pres : ∀ a b, precRule a b → RTy.PresL (BExpr.lowerList a) (BExpr.lowerList b) := by
  rintro a b ⟨e, e', rfl, rfl, h⟩
  exact (foldNode_cases h).pres

mutual
theorem star_precE : ∀ e : BExpr, SeqRefines.Star precRule [e] [precE e]
  | .op i args => by
    have h₁ := (star_precL args).lift (.op i [] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil] at h₁
    simp only [precE]
    cases hf : foldNode (BExpr.op i (precL args)) with
    | none => simpa using h₁
    | some e'' =>
      simp only [Option.getD_some]
      exact h₁.trans' (SeqRefines.Star.single ⟨_, _, rfl, rfl, hf⟩)
  | .block bt b => by
    have h₁ := (star_precL b).lift (.block bt [] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil] at h₁
    simpa only [precE] using h₁
  | .loop bt b => by
    have h₁ := (star_precL b).lift (.loop bt [] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil] at h₁
    simpa only [precE] using h₁
  | .if_ bt c t e => by
    have h₁ := (star_precL c).lift (.ifCond bt [] .hole [] t e)
    have h₂ := (star_precL t).lift (.ifThen bt (precL c) [] .hole [] e)
    have h₃ := (star_precL e).lift (.ifElse bt (precL c) (precL t) [] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil] at h₁ h₂ h₃
    simpa only [precE] using h₁.trans' (h₂.trans' h₃)
  | .tryTable bt cs b => by
    have h₁ := (star_precL b).lift (.tryTable bt cs [] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil] at h₁
    simpa only [precE] using h₁
theorem star_precL : ∀ es : List BExpr, SeqRefines.Star precRule es (precL es)
  | [] => by simpa only [precL] using SeqRefines.Star.refl (rule := precRule) []
  | e :: es => by
    have h₁ := (star_precE e).lift (.seq [] .hole es)
    have h₂ := (star_precL es).lift (.seq [precE e] .hole [])
    simp only [BCtx.plug, List.nil_append, List.append_nil, List.singleton_append] at h₁ h₂
    simpa only [precL] using h₁.trans' h₂
end

/-- Folding preserves typing (a trap folds to the polymorphic `unreachable`). -/
theorem precL_typed {C : Context} {it : InstrType} {es : List BExpr} (h : SeqOk C es it) :
    SeqOk C (precL es) it :=
  (presL_star precRule_pres (star_precL es)).apply h

end Silmaril.Wasm.Binaryen
