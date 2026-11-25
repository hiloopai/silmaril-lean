module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Fixture
public import Silmaril.Wasm.Component.Reference.HLinkedSep.Defs

/-!
# The separating pair: instances and adequacy

* `sepSummary c`: a Boolean summary of the validation and instantiation of `sepCore c`, checked
  by `decide +kernel` at `c = 0` and `c = 1`; `SepFacts` reads it back.
* `sepInst c`: the instance (`sep_isInst`); `sepL_adequate`: `HLinked2.Adequate (sepL c)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HLinkedSep
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetS)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR (unitFn i32Fn isHost isHost_code
  single_of_map pair_of_map)
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The function instance has the body of `f` with the constant `c`, no locals, and its module's
global `0` and function `0` are at address `0`. -/
def isSepBody (c : BitVec 32) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.globalGet x₁, .intConst .i32 b₁, .globalSet x₂, .call y, .intConst .i32 b₂,
      .globalSet x₃]⟩ =>
    b₁.toNat == c.toNat && b₂.toNat == 0 && x₁.toNat == 0 && x₂.toNat == 0 && x₃.toNat == 0 &&
      y.toNat == 0 && fi.module.globals == [0] && fi.module.funcs[0]? == some 0
  | _ => false

/-- What the summary records of a function instance. -/
def sepInfo (c : BitVec 32) (fi : FuncInst Nat) : Option FnType × Bool × Bool :=
  (FnType.ofDefType? fi.type, isHost 0 fi, isSepBody c fi)

/-- The checks on the instantiated store and frame. -/
def sepBody (c : BitVec 32) (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [1] &&
    s.funcs.map (sepInfo c) == [(some unitFn, true, false), (some i32Fn, false, true)] &&
    s.globals.map (·.value) == [Val.i32 0]

/-- The closed import types of `sepCore c`. -/
def sepImports (c : BitVec 32) : List DefType :=
  match validate? (sepCore c) with
  | some mt => CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `sepCore c` against one host function. -/
def sepStore (c : BitVec 32) : Store Nat :=
  match instantiateOnce? (importStore (sepImports c)) (sepCore c) [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `sepCore c`. -/
def sepInst (c : BitVec 32) : ScalarInstance where
  imports := [unitFn]
  exports := [i32Fn]
  addrs := [1]
  store := sepStore c

/-- The Boolean summary of the validation and instantiation of `sepCore c`. -/
def sepSummary (c : BitVec 32) : Bool :=
  match validate? (sepCore c) with
  | some mt => mt.imports.length == 1 && mt.imports.all Litmus.isFuncImport &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some unitFn] &&
      decide (mt.imports = (sepI c).imports.map fun p =>
        .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩)) &&
      Litmus.runOk (sepBody c) (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        (sepCore c) [.func 0])
  | none => false

theorem sepSummary_zero : sepSummary 0 = true := by decide +kernel

theorem sepSummary_one : sepSummary 1 = true := by decide +kernel

/-- The facts the summary records. -/
structure SepFacts (c : BitVec 32) : Prop where
  valid : ∃ mt, validate? (sepCore c) = some mt ∧ mt.imports.length = 1 ∧
    (∀ xt ∈ mt.imports, ∃ d, xt = .func d) ∧
    List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) (CExternType.funcs mt.imports)
      [unitFn] ∧
    mt.imports = (sepI c).imports.map (fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩)) ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports))
      (sepCore c) [.func 0] = some (sepStore c, f, none) ∧ exportFuncAddrs f.module = [1]
  funcs : ∃ h₀ fb : FuncInst Nat, (sepStore c).funcs = [h₀, fb] ∧
    sepInfo c h₀ = (some unitFn, true, false) ∧ sepInfo c fb = (some i32Fn, false, true)
  globals : ∃ g : GlobalInst, (sepStore c).globals = [g] ∧ g.value = Val.i32 0

theorem sepFacts {c : BitVec 32} (hc : sepSummary c = true) : SepFacts c := by
  obtain ⟨mt, hmt⟩ : ∃ mt, validate? (sepCore c) = some mt := by
    cases hv : validate? (sepCore c) with
    | none => exact absurd hc (by simp [sepSummary, hv])
    | some mt => exact ⟨mt, rfl⟩
  have h' : ((((mt.imports.length = 1 ∧ mt.imports.all Litmus.isFuncImport = true) ∧
      (CExternType.funcs mt.imports).map FnType.ofDefType? = [some unitFn]) ∧
      mt.imports = (sepI c).imports.map (fun p =>
        .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩))) ∧
      Litmus.runOk (sepBody c) (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        (sepCore c) [.func 0]) = true) := by
    simpa only [sepSummary, hmt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hc
  obtain ⟨s, f, hrun, hb⟩ := Litmus.runOk_eq h'.2
  have himp : sepImports c = CExternType.funcs mt.imports := by simp only [sepImports, hmt]
  have hs : sepStore c = s := by simp only [sepStore, himp, hrun]
  have hb' : (exportFuncAddrs f.module = [1] ∧
      s.funcs.map (sepInfo c) = [(some unitFn, true, false), (some i32Fn, false, true)]) ∧
      s.globals.map (·.value) = [Val.i32 0] := by
    simpa only [sepBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨d₀, hd, hd₀⟩ := single_of_map h'.1.1.2
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := fun xt hxt =>
    Litmus.func_of_isFuncImport (List.all_eq_true.mp h'.1.1.1.2 xt hxt)
  obtain ⟨h₀, fb, hfs, i₀, ib⟩ := pair_of_map hb'.1.2
  obtain ⟨g, hg, hgv⟩ := single_of_map hb'.2
  exact ⟨⟨mt, hmt, h'.1.1.1.1, hfun, hd ▸ .cons hd₀ .nil, h'.1.2, f, hs ▸ hrun, hb'.1.1⟩,
    ⟨h₀, fb, hs ▸ hfs, i₀, ib⟩, ⟨g, hs ▸ hg, hgv⟩⟩

/-- `sepInst c` is the instance of the importer's module. -/
theorem sep_isInst {c : BitVec 32} (hc : sepSummary c = true) :
    (sepI c).mod.IsInst (sepInst c) := by
  obtain ⟨⟨mt, hmt, hlen, hfun, hty, -, f, hf, hfa⟩, ⟨h₀, fb, hfuncs, -, ib⟩, -⟩ := sepFacts hc
  simp only [sepInfo, Prod.mk.injEq] at ib
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [.func 0] := by
    rw [hlen]
    rfl
  refine ⟨⟨mt, ⟨hmt, hfun, hty, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fb, ?_, ib.1⟩ .nil
    show (sepStore c).funcs[1]? = some fb
    rw [hfuncs]
    rfl

theorem sepI_exports (c : BitVec 32) :
    (sepI c).exports = [⟨"f", LinkedSession.u32Ty, 0⟩] := rfl

theorem sepI_imports (c : BitVec 32) : (sepI c).imports = [("h", LinkedSession.unitTy)] := rfl

theorem sepCore_imports (c : BitVec 32) :
    (sepCore c).imports = [⟨"env", "h", .func ⟨0⟩⟩] := rfl

theorem sepI_good (c : BitVec 32) : (sepI c).Good :=
  ⟨by rw [sepI_exports]; decide, by
    intro x hx
    simp only [sepI, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ⟨"f", rfl⟩, rfl⟩

theorem sepI_inst {c : BitVec 32} (hc : sepSummary c = true) : (sepI c).Inst := by
  obtain ⟨⟨mt, hmt, -, -, -, himp, -⟩, -, -⟩ := sepFacts hc
  exact ⟨⟨sepInst c, sep_isInst hc⟩, rfl, by rw [sepI_imports]; decide, rfl, ⟨mt, hmt, himp⟩⟩

theorem sepI_arity (c : BitVec 32) : (sepI c).Arity := by
  unfold SimpleI.Arity
  rw [sepI_exports, sepI_imports]
  decide

theorem sepI_floatFree (c : BitVec 32) : (sepI c).FloatFree := by
  unfold SimpleI.FloatFree
  rw [sepI_exports, sepI_imports]
  decide

theorem sepL_wireTy (c : BitVec 32) : (sepL c).WireTy :=
  ⟨⟨rfl, Nat.zero_le _⟩, fun k w hk => by simp [sepL] at hk⟩

theorem sepL_namesOk (c : BitVec 32) : (sepL c).toL2.NamesOk := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · exact LinkedSessionRef.linkedC_namesOk.exp x hx
  · simp only [sepL, sepI, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact LinkedSessionRef.ne_tag_of_length 0 (by decide) (by decide)

theorem sepL_wireNodup (c : BitVec 32) : (sepL c).toL2.WireNodup := List.nodup_nil

theorem sepL_splitOk (c : BitVec 32) : (sepL c).toL2.SplitOk :=
  ⟨LinkedSessionRef.linkedC_splitOk.exp,
    ⟨by show (sepCore c).imports.all _ = true; rw [sepCore_imports]; decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The linked component `sepL c` satisfies the adequacy hypotheses** (at `c = 0` and `c = 1`,
through the summary). -/
theorem sepL_adequate {c : BitVec 32} (hc : sepSummary c = true) : (sepL c).Adequate :=
  ⟨LinkedSessionIR.setGetS_good, LinkedSessionRef.setGetS_inst, sepI_good c, sepI_inst hc,
    sepI_arity c, sepI_floatFree c, sepL_wireTy c, sepL_namesOk c, sepL_wireNodup c,
    sepL_splitOk c⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSep
