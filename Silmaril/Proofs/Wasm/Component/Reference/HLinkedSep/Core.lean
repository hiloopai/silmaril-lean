module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep.Inst

/-!
# The separating pair: the importer's core plays

For the instance `sepInst c` of `sepCore c` and every store `u` with the instance's functions
and one global holding `v` (`SepSt c u v`), every profile:

* `sep_callout`: the export call `f` runs host-free to the callout of the host import `h`, at the
  store `u` with the global set to `c`;
* `sep_path_trap`: answered by a trap, the call answers a trap at that store;
* `sep_path_ans`: answered with no results, the call sets the global to `0` and answers `v`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HLinkedSep
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR (unitFn i32Fn isHost isHost_code
  trapImport_path)
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {c : BitVec 32}

/-! ## Stores -/

/-- **The stores of the importer in sessions**: the instance's functions, and one global holding
`v`. -/
def SepSt (c : BitVec 32) (u : Store Nat) (v : BitVec 32) : Prop :=
  u.funcs = (sepStore c).funcs ∧ ∃ g : GlobalInst, u.globals = [g] ∧ g.value = Val.i32 v

theorem sepSt_init (hc : sepSummary c = true) : SepSt c (sepStore c) 0 := by
  obtain ⟨-, -, g, hg, hv⟩ := sepFacts hc
  exact ⟨rfl, g, hg, hv⟩

theorem sepSt_set {u : Store Nat} {v : BitVec 32} (h : SepSt c u v) (w : BitVec 32) :
    SepSt c (u.setGlobal 0 (Val.i32 w)) w := by
  obtain ⟨hf, g, hg, -⟩ := h
  refine ⟨hf, { g with value := Val.i32 w }, ?_, rfl⟩
  show (u.globals.modify 0 fun g => { g with value := Val.i32 w }) = _
  rw [hg]
  rfl

/-! ## The body of `f` -/

theorem isSepBody_code {fi : FuncInst Nat} (h : isSepBody c fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x₁ x₂ x₃ : Silmaril.Wasm.GlobalIdx) (y : Silmaril.Wasm.FuncIdx),
      fi.code = .wasm code ∧ code.locals = [] ∧
      code.body = [.globalGet x₁, .intConst .i32 c, .globalSet x₂, .call y, .intConst .i32 0,
        .globalSet x₃] ∧
      x₁.toNat = 0 ∧ x₂.toNat = 0 ∧ x₃.toNat = 0 ∧ y.toNat = 0 ∧ fi.module.globals = [0] ∧
      fi.module.funcs[0]? = some 0 := by
  unfold isSepBody at h
  split at h
  next t x₁ b₁ x₂ y b₂ x₃ hc =>
    have h' : ((((((b₁.toNat = c.toNat ∧ b₂.toNat = 0) ∧ x₁.toNat = 0) ∧ x₂.toNat = 0) ∧
        x₃.toNat = 0) ∧ y.toNat = 0) ∧ fi.module.globals = [0]) ∧ fi.module.funcs[0]? = some 0 := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨⟨⟨⟨⟨⟨⟨hb₁, hb₂⟩, h1⟩, h2⟩, h3⟩, hy⟩, hg⟩, hf⟩ := h'
    have e₁ : b₁ = c := BitVec.eq_of_toNat_eq hb₁
    have e₂ : b₂ = 0 := BitVec.eq_of_toNat_eq (by simpa using hb₂)
    subst e₁ e₂
    exact ⟨_, x₁, x₂, x₃, y, hc, rfl, rfl, h1, h2, h3, hy, hg, hf⟩
  next => cases h

/-! ## Questions and answers -/

/-- The export question `f()`. -/
def fQ (c : BitVec 32) : (sepInst c).F.Op := ⟨⟨0, Nat.zero_lt_one⟩, ⟨[], .nil⟩⟩

/-- The import question `h()`. -/
def hE (c : BitVec 32) : (sepInst c).E.Op := ⟨⟨0, Nat.zero_lt_one⟩, ⟨[], .nil⟩⟩

/-- The answer of `h()` with no results. -/
def hA (c : BitVec 32) : (sepInst c).E.Ar (hE c) := .values ⟨[], .nil⟩

/-- The answer `v` of `f()`. -/
def fA (c v : BitVec 32) : (sepInst c).F.Ar (fQ c) := .values ⟨[Val.i32 v], .cons ⟨v, rfl⟩ .nil⟩

theorem h_importOp : (sepInst c).importOp? 0 [] = some (hE c) := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd (hE c).2.2 ‹_›
  · exact absurd (show 0 < (sepInst c).imports.length from Nat.zero_lt_one) ‹_›

/-! ## The callout -/

/-- The callout context of `f`: below its frame and label, the value read from the global on
the stack, and `i32.const 0; global.set x` after the call. -/
def sepCtx (n : Nat) (F : Frame) (v : BitVec 32) (x : Silmaril.Wasm.GlobalIdx) : Ctx :=
  .frame [] n F
    (.label [] n [] (.top [Val.i32 v] [.plain (.intConst .i32 0), .plain (.globalSet x)]) []) []

/-- **The export call `f` reaches the callout of `h`**: it reads the global (`v`), sets it to
`c`, and calls the host function `0` with no arguments. -/
theorem sep_callout (P : Profile) (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) :
    ∃ (t : Thread) (F : Frame) (x : Silmaril.Wasm.GlobalIdx),
      Reach P (u, (sepInst c).initThread (fQ c)) (u.setGlobal 0 (Val.i32 c), t) ∧
      decompose? (u.setGlobal 0 (Val.i32 c)) (t.config (u.setGlobal 0 (Val.i32 c))).code =
        some (sepCtx (Ty.ofList (i32Fn.results.map ScalarType.toC)).length F v x, 0, 0, []) ∧
      (t.config (u.setGlobal 0 (Val.i32 c))).frame = {} ∧ F.module.globals = [0] ∧
      x.toNat = 0 := by
  obtain ⟨-, ⟨h₀, fb, hfuncs, i₀, ib⟩, -⟩ := sepFacts hc
  simp only [sepInfo, Prod.mk.injEq] at i₀ ib
  obtain ⟨code, x₁, x₂, x₃, y, hcode, -, hbody, hx₁, hx₂, hx₃, hy, hmg, hmf⟩ :=
    isSepBody_code ib.2.2
  obtain ⟨hfu, g, hg, hgv⟩ := hu
  have hf1 : u.funcs[1]? = some fb := by rw [hfu, hfuncs]; rfl
  have he : Expand fb.type i32Fn.toComp := FnType.expand_of_ofDefType? ib.1
  let F := Frame.forCall fb.module [] code.locals
  let n := (Ty.ofList (i32Fn.results.map ScalarType.toC)).length
  have hn : ([] : List Silmaril.Wasm.Execution.Core.Val).length = (Ty.ofList (i32Fn.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList]
    rfl
  have s₁ : Step P Det.noHost (invoke u 1 [])
      ⟨u, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf1 he hn hcode
  have hg₁ : u.global? F x₁ = some (0, g) := by
    show u.global? (Frame.forCall fb.module [] code.locals) x₁ = _
    simp [Store.global?, Frame.forCall, hmg, hx₁, hg]
  have hg₂ : u.global? F x₂ = some (0, g) := by
    show u.global? (Frame.forCall fb.module [] code.locals) x₂ = _
    simp [Store.global?, Frame.forCall, hmg, hx₂, hg]
  have hyF : F.module.funcs[y.toNat]? = some 0 := by
    show (Frame.forCall fb.module [] code.locals).module.funcs[y.toNat]? = _
    rw [hy]
    exact hmf
  have hf0 : (u.setGlobal 0 (Val.i32 c)).funcs[0]? = some h₀ := by
    show u.funcs[0]? = _
    rw [hfu, hfuncs]
    rfl
  have a₁ : Step P Det.noHost
      ⟨u, F, vals [] ++ [.plain (.globalGet x₁)] ++ [.plain (.intConst .i32 c),
        .plain (.globalSet x₂), .plain (.call y), .plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩
      ⟨u, F, vals [] ++ [g.value.toAdmin] ++ [.plain (.intConst .i32 c),
        .plain (.globalSet x₂), .plain (.call y), .plain (.intConst .i32 0),
        .plain (.globalSet x₃)]⟩ :=
    .ctxtInstrs (.variable (.globalGet hg₁)) (.inr (by simp))
  rw [hgv] at a₁
  have a₂ : Step P Det.noHost
      ⟨u, F, vals [Val.i32 v] ++ [(Val.i32 c).toAdmin, .plain (.globalSet x₂)] ++
        [.plain (.call y), .plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩
      ⟨u.setGlobal 0 (Val.i32 c), F, vals [Val.i32 v] ++ [] ++
        [.plain (.call y), .plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩ :=
    .ctxtInstrs (.variable (.globalSet hg₂)) (.inl (by simp))
  have a₃ : Step P Det.noHost
      ⟨u.setGlobal 0 (Val.i32 c), F, vals [Val.i32 v] ++ [.plain (.call y)] ++
        [.plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩
      ⟨u.setGlobal 0 (Val.i32 c), F, vals [Val.i32 v] ++ [.ref (.func 0), .callRefType h₀.type] ++
        [.plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩ :=
    .ctxtInstrs (.call hyF hf0) (.inl (by simp))
  have s₂ : Steps P Det.noHost ⟨u, F, expression code.body⟩
      ⟨u.setGlobal 0 (Val.i32 c), F, vals [Val.i32 v] ++ [.ref (.func 0), .callRefType h₀.type] ++
        [.plain (.intConst .i32 0), .plain (.globalSet x₃)]⟩ := by
    rw [hbody]
    exact ((Relation.ReflTransGen.single a₁).tail a₂).tail a₃
  have run : Steps P Det.noHost ((Thread.pending 1 []).config u)
      ⟨u.setGlobal 0 (Val.i32 c), {},
        (sepCtx n F v x₃).fill (vals [] ++ [.ref (.func 0), .callRefType h₀.type])⟩ :=
    (Relation.ReflTransGen.single s₁).trans (Litmus.steps_frame_label s₂)
  obtain ⟨s', t, hr, hd⟩ := Litmus.reach_of_steps run
  have hs : s' = u.setGlobal 0 (Val.i32 c) := by
    have h₁ : (t.config s').store = s' := by cases t <;> rfl
    rw [← h₁, hd]
  subst hs
  have hn' : ([] : List Silmaril.Wasm.Execution.Core.Val).length = (Ty.ofList (unitFn.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList]
    rfl
  refine ⟨t, F, x₃, hr, ?_, by rw [hd], ?_, hx₃⟩
  · rw [hd]
    exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ trivial hf0
      (FnType.expand_of_ofDefType? i₀.1) hn' (isHost_code i₀.2.1)
  · show (Frame.forCall fb.module [] code.locals).module.globals = [0]
    simp [Frame.forCall, hmg]

/-! ## The two plays of `f` -/

/-- **`f` with its host call refused** answers a trap, at the store with the global set to
`c`. -/
theorem sep_path_trap (P : Profile) (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) :
    (sepInst c).Path P (.idle u)
      ([.inr (.ask (fQ c))] ++
        [.inl (.ask (hE c)), .inl (.ans (hE c) .trap), .inr (.ans (fQ c) .trap)])
      (.idle (u.setGlobal 0 (Val.i32 c))) := by
  obtain ⟨t, F, x, hr, hd, -⟩ := sep_callout P hc hu
  exact trapImport_path (.cons (.call _ _) (.nil _)) hr ⟨_, _, hd⟩ h_importOp

/-- **`f` with its host call answered** sets the global to `0` and answers `v`. -/
theorem sep_path_ans (P : Profile) (hc : sepSummary c = true) {u : Store Nat} {v : BitVec 32}
    (hu : SepSt c u v) :
    (sepInst c).Path P (.idle u)
      (.inr (.ask (fQ c)) :: callMoves [⟨hE c, hA c⟩] ++ [.inr (.ans (fQ c) (fA c v))])
      (.idle ((u.setGlobal 0 (Val.i32 c)).setGlobal 0 (Val.i32 0))) := by
  obtain ⟨t, F, x, hr, hd, hfr, hmg, hx⟩ := sep_callout P hc hu
  obtain ⟨-, g, hg, -⟩ := sepSt_set hu c
  let n := (Ty.ofList (i32Fn.results.map ScalarType.toC)).length
  have hres : resumeResult (u.setGlobal 0 (Val.i32 c)) t (Answer.toResult (hA c)) =
      .active {} [.frame n F [.label n []
        (vals [Val.i32 v] ++ [.plain (.intConst .i32 0), .plain (.globalSet x)])]] := by
    unfold resumeResult
    simp only [hd, hfr]
    rfl
  have hgx : (u.setGlobal 0 (Val.i32 c)).global? F x = some (0, g) := by
    simp [Store.global?, hmg, hx, hg]
  have a₁ : Step P Det.noHost
      ⟨u.setGlobal 0 (Val.i32 c), F, vals [Val.i32 v] ++ [(Val.i32 0).toAdmin,
        .plain (.globalSet x)] ++ []⟩
      ⟨(u.setGlobal 0 (Val.i32 c)).setGlobal 0 (Val.i32 0), F, vals [Val.i32 v] ++ [] ++ []⟩ :=
    .ctxtInstrs (.variable (.globalSet hgx)) (.inl (by simp))
  have hn : [Val.i32 v].length = n := (Ty.length_ofList (i32Fn.results.map ScalarType.toC)).symm
  have run₂ : Steps P Det.noHost
      ((Thread.active {} [.frame n F [.label n []
        (vals [Val.i32 v] ++ [.plain (.intConst .i32 0), .plain (.globalSet x)])]]).config
        (u.setGlobal 0 (Val.i32 c)))
      ⟨(u.setGlobal 0 (Val.i32 c)).setGlobal 0 (Val.i32 0), {}, vals [Val.i32 v]⟩ :=
    (((Litmus.steps_frame_label (f := {}) (n := n) (m := n) (cont := [])
      (Relation.ReflTransGen.single a₁)).tail
      (.ctxtFrame (Step.labelVals (vs := [Val.i32 v])))).tail (.frameVals hn))
  obtain ⟨s₂', t₂, hr₂, hd₂⟩ := Litmus.reach_of_steps run₂
  have hs₂ : s₂' = (u.setGlobal 0 (Val.i32 c)).setGlobal 0 (Val.i32 0) := by
    have h₂ : (t₂.config s₂').store = s₂' := by cases t₂ <;> rfl
    rw [← h₂, hd₂]
  subst hs₂
  have hfin : ResultAt ((u.setGlobal 0 (Val.i32 c)).setGlobal 0 (Val.i32 0)) t₂
      (.values [Val.i32 v]) := by
    show (t₂.config _).code = _
    rw [hd₂]
    rfl
  have hans : Answer.ofResult? ((sepInst c).exports.get (fQ c).1) (.values [Val.i32 v]) =
      some (fA c v) := by
    unfold Answer.ofResult?
    exact dite_eq_left (.cons ⟨v, rfl⟩ .nil)
  refine .cons (.call _ _) (.cons (.ucall hr ⟨_, _, hd⟩ h_importOp)
    (.cons (.uret (hA c)) ?_))
  rw [hres]
  exact .cons (.oret hr₂ hfin hans) (.nil _)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep
