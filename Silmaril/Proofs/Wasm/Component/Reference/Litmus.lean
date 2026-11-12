module

public import Silmaril.Wasm.Component.Reference.Litmus.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# Litmus components: proofs

The instance of `binCore3 op` (`op ∈ {add, mul}`) is computed by kernel evaluation of
`validate?` and `instantiateOnce?` (`decide +kernel` on a Boolean summary). The export call is
then a Core 3.0 run built from `Step` rules, for an arbitrary profile and all arguments
(`bin_run`): `call_ref` enters the function, the two `local.get`s read the arguments, the
binary operator computes, and the result leaves the label and the frame.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm (IntBinOp)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- The function instance has the body `local.get 0; local.get 1; i32.<op>` and no locals. -/
def isBin (op : IntBinOp) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet x₀, .localGet x₁, .intBinOp .i32 op']⟩ =>
    x₀.toNat == 0 && x₁.toNat == 1 && decide (op' = op)
  | _ => false

/-- The function type of the export. -/
abbrev binFn : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The checks on the instantiated store and frame. -/
def instBody (op : IntBinOp) (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some binFn] &&
    (s.funcs.map (isBin op)) == [true]

/-- A start-free instantiation result passing `B`. -/
def runOk (B : Store Nat → Frame → Bool) : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx) → Bool
  | some (s, f, none) => B s f
  | _ => false

theorem runOk_eq {B : Store Nat → Frame → Bool} :
    ∀ {o : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx)}, runOk B o = true →
      ∃ s f, o = some (s, f, none) ∧ B s f = true
  | some (s, f, none), h => ⟨s, f, rfl, h⟩
  | some (_, _, some _), h => nomatch h
  | none, h => nomatch h

/-- The Boolean summary of the instantiation of `binCore3 op`. -/
def instSummary (op : IntBinOp) : Bool :=
  ((Silmaril.Wasm.Validation.validate? (binCore3 op)).map (·.imports.length) == some 0) &&
    runOk (instBody op) (instantiateOnce? (importStore []) (binCore3 op) [])

theorem instSummary_add : instSummary .add = true := by decide +kernel
theorem instSummary_mul : instSummary .mul = true := by decide +kernel

/-- Reading `isBin`. -/
theorem isBin_code {op : IntBinOp} {fi : FuncInst Nat} (h : isBin op fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x₀ x₁ : Silmaril.Wasm.LocalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.localGet x₀, .localGet x₁, .intBinOp .i32 op] ∧
      x₀.toNat = 0 ∧ x₁.toNat = 1 := by
  unfold isBin at h
  split at h
  next t x₀ x₁ op' hc =>
    have h' : (x₀.toNat = 0 ∧ x₁.toNat = 1) ∧ op' = op := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h
    obtain ⟨⟨h₀, h₁⟩, rfl⟩ := h'
    exact ⟨_, x₀, x₁, hc, rfl, rfl, h₀, h₁⟩
  next => cases h

/-- The facts the summary records. -/
structure InstFacts (op : IntBinOp) : Prop where
  valid : ∃ mt, Silmaril.Wasm.Validation.validate? (binCore3 op) = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) (binCore3 op) [] =
    some (binStore op, f, none) ∧ exportFuncAddrs f.module = [0]
  func : ∃ fi : FuncInst Nat, (binStore op).funcs = [fi] ∧ FnType.ofDefType? fi.type = some binFn ∧
    isBin op fi = true

theorem instFacts {op : IntBinOp} (h : instSummary op = true) : InstFacts op := by
  have h' : (Silmaril.Wasm.Validation.validate? (binCore3 op)).map (·.imports.length) = some 0 ∧
      runOk (instBody op) (instantiateOnce? (importStore []) (binCore3 op) []) = true := by
    simpa only [instSummary, Bool.and_eq_true, beq_iff_eq] using h
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have hs : binStore op = s := by simp only [binStore, hrun]
  have hb' : (exportFuncAddrs f.module = [0] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some binFn]) ∧
      s.funcs.map (isBin op) = [true] := by
    simpa only [instBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨fi, hfi⟩ : ∃ fi, s.funcs = [fi] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hb'.2)
  have hty : FnType.ofDefType? fi.type = some binFn := by simpa [hfi] using hb'.1.2
  have hbin : isBin op fi = true := by simpa [hfi] using hb'.2
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hb'.1.1⟩,
    ⟨fi, hs ▸ hfi, hty, hbin⟩⟩

/-- `binInst op` is the instance of `binMod op`. -/
theorem isInst {op : IntBinOp} (h : instSummary op = true) : (binMod op).IsInst (binInst op) := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fi, hfuncs, hty, _⟩⟩ := instFacts h
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, ?_, hfa⟩
    rw [himp]
    exact hf
  · refine .cons ⟨fi, ?_, hty⟩ .nil
    show (binStore op).funcs[0]? = some fi
    rw [hfuncs]
    rfl

/-- The body `local.get 0; local.get 1; i32.<op>` in a frame whose first two locals are `x`
and `y` reduces to `i32 z`. -/
theorem body_run {P : Profile} {s : Store Nat} {F : Frame} {op : IntBinOp}
    {x₀ x₁ : Silmaril.Wasm.LocalIdx} {x y z : BitVec 32}
    (h₀ : F.local? x₀ = some (some (Val.i32 x))) (h₁ : F.local? x₁ = some (some (Val.i32 y)))
    (hz : Silmaril.Wasm.Numerics.intBinOp .i32 op x y = Except.ok z) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, expression [.localGet x₀, .localGet x₁, .intBinOp .i32 op]⟩
      ⟨s, F, vals [Val.i32 z]⟩ := by
  have a₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, vals [] ++ [.plain (.localGet x₀)] ++ [.plain (.localGet x₁), .plain (.intBinOp .i32 op)]⟩
      ⟨s, F, vals [] ++ [(Val.i32 x).toAdmin] ++ [.plain (.localGet x₁), .plain (.intBinOp .i32 op)]⟩ :=
    .ctxtInstrs (.variable (.localGet h₀)) (.inr (by simp))
  have a₂ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, vals [Val.i32 x] ++ [.plain (.localGet x₁)] ++ [.plain (.intBinOp .i32 op)]⟩
      ⟨s, F, vals [Val.i32 x] ++ [(Val.i32 y).toAdmin] ++ [.plain (.intBinOp .i32 op)]⟩ :=
    .ctxtInstrs (.variable (.localGet h₁)) (.inl (by simp))
  have a₃ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, [.plain (.intConst .i32 x), .plain (.intConst .i32 y), .plain (.intBinOp .i32 op)]⟩
      ⟨s, F, [.plain (.intConst .i32 z)]⟩ :=
    .numeric (.intBinOp hz)
  exact (Relation.ReflTransGen.single a₁).trans
    ((Relation.ReflTransGen.single a₂).trans (Relation.ReflTransGen.single a₃))

/-- Runs inside a label inside a frame. -/
theorem steps_frame_label {P : Profile} {host : HostSemantics Nat} {f : Frame} {n m : Nat}
    {cont : List Silmaril.Wasm.Instr} {c c' : Config Nat} (h : Steps P host c c') :
    Steps P host ⟨c.store, f, [.frame n c.frame [.label m cont c.code]]⟩
      ⟨c'.store, f, [.frame n c'.frame [.label m cont c'.code]]⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (.ctxtFrame (.ctxtLabel st))

/-- **The export call, for every profile and all arguments.** -/
theorem bin_run {P : Profile} {op : IntBinOp} (h : instSummary op = true) {x y z : BitVec 32}
    (hz : Silmaril.Wasm.Numerics.intBinOp .i32 op x y = Except.ok z) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke (binStore op) 0 [Val.i32 x, Val.i32 y]) ⟨binStore op, {}, vals [Val.i32 z]⟩ := by
  obtain ⟨_, _, ⟨fi, hfuncs, hty, hbin⟩⟩ := instFacts h
  obtain ⟨code, x₀, x₁, hcode, hloc, hbody, h₀, h₁⟩ := isBin_code hbin
  have hf : (binStore op).funcs[0]? = some fi := by rw [hfuncs]; rfl
  have he : Expand fi.type binFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall fi.module [Val.i32 x, Val.i32 y] code.locals
  let n := (Silmaril.Wasm.Validation.Ty.ofList (binFn.results.map ScalarType.toC)).length
  have hn : [Val.i32 z].length = n := (Silmaril.Wasm.Validation.Ty.length_ofList (binFn.results.map ScalarType.toC)).symm
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke (binStore op) 0 [Val.i32 x, Val.i32 y])
      ⟨binStore op, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Silmaril.Wasm.Validation.Ty.length_ofList (binFn.params.map ScalarType.toC)).symm hcode
  have hl₀ : F.local? x₀ = some (some (Val.i32 x)) := by
    simp [F, Frame.local?, Frame.forCall, hloc, h₀]
  have hl₁ : F.local? x₁ = some (some (Val.i32 y)) := by
    simp [F, Frame.local?, Frame.forCall, hloc, h₁]
  have s₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨binStore op, F, expression code.body⟩ ⟨binStore op, F, vals [Val.i32 z]⟩ := by
    rw [hbody]
    exact body_run hl₀ hl₁ hz
  have s₃ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨binStore op, {}, [.frame n F [.label n [] (expression code.body)]]⟩
      ⟨binStore op, {}, [.frame n F [.label n [] (vals [Val.i32 z])]]⟩ :=
    steps_frame_label s₂
  have s₄ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨binStore op, {}, [.frame n F [.label n [] (vals [Val.i32 z])]]⟩
      ⟨binStore op, {}, [.frame n F (vals [Val.i32 z])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨binStore op, {}, [.frame n F (vals [Val.i32 z])]⟩ ⟨binStore op, {}, vals [Val.i32 z]⟩ :=
    .frameVals hn
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-! ## Specification outcomes and IR plays -/

/-- The core outcome of the export call. -/
theorem bin_coreOut {P : Profile} {op : IntBinOp} (h : instSummary op = true) {x y z : BitVec 32}
    (hz : Silmaril.Wasm.Numerics.intBinOp .i32 op x y = Except.ok z) :
    some [Flat.i32 z] ∈ coreOut P (binMod op) 0 [Flat.i32 x, Flat.i32 y] :=
  ⟨binInst op, isInst h, _, .values [Val.i32 z], bin_run h hz, rfl, rfl⟩

theorem adderS_good : adderS.Good :=
  ⟨by decide, by intro x hx; simp only [adderS, List.mem_singleton] at hx; subst hx; exact ⟨"f", rfl⟩⟩

theorem recordS_good : recordS.Good :=
  ⟨by decide, by intro x hx; simp only [recordS, List.mem_singleton] at hx; subst hx; exact ⟨"f", rfl⟩⟩

theorem optionS_good : optionS.Good :=
  ⟨by decide, by intro x hx; simp only [optionS, List.mem_singleton] at hx; subst hx; exact ⟨"f", rfl⟩⟩

/-- `binMod op` is instantiated as the IR assumes. -/
theorem binMod_inst {op : IntBinOp} (h : instSummary op = true) (xs : List SimpleExport) :
    Simple.Inst ⟨binMod op, xs⟩ :=
  ⟨⟨binInst op, isInst h⟩, rfl⟩

theorem adderS_inst : adderS.Inst := binMod_inst instSummary_add _
theorem recordS_inst : recordS.Inst := binMod_inst instSummary_add _
theorem optionS_inst : optionS.Inst := binMod_inst instSummary_mul _

/-- A core outcome of lowered arguments is a specification outcome. -/
theorem mem_exportSpec {P : Profile} {c : Simple} {x : SimpleExport}
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat} (hl : checkLower x.ty.params vs = some xs)
    {r : Option (List Flat)} (hr : r ∈ coreOut P c.mod x.core xs) :
    liftOutcome x.ty r ∈ exportSpec P c x vs := by
  unfold exportSpec
  rw [hl]
  exact .inl ⟨r, hr, rfl⟩

/-- The adder returns `x + y`, for every profile. -/
theorem adder_spec (P : Profile) (x y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (x + y))]) ∈
      exportSpec P adderS adderS.exports[0] [.u32 x, .u32 y] :=
  mem_exportSpec (c := adderS) (x := adderS.exports[0]) (xs := [Flat.i32 x, Flat.i32 y])
    (r := some [Flat.i32 (x + y)]) rfl (bin_coreOut instSummary_add rfl)

/-- The record component returns the sum of its fields, for every profile. -/
theorem record_spec (P : Profile) (x y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (x + y))]) ∈
      exportSpec P recordS recordS.exports[0] [.record [.u32 x, .u32 y]] :=
  mem_exportSpec (c := recordS) (x := recordS.exports[0]) (xs := [Flat.i32 x, Flat.i32 y])
    (r := some [Flat.i32 (x + y)]) rfl (bin_coreOut instSummary_add rfl)

/-- `get-or-zero(some y)` returns `y`, for every profile. -/
theorem option_some_spec (P : Profile) (y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 y)]) ∈
      exportSpec P optionS optionS.exports[0] [.variant 1 (some (.u32 y))] := by
  have hz : Silmaril.Wasm.Numerics.intBinOp .i32 .mul 1 (y.setWidth 32) = Except.ok y := by
    show Except.ok (1 * y.setWidth 32) = _
    simp
  exact mem_exportSpec (c := optionS) (x := optionS.exports[0])
    (xs := [Flat.i32 1, Flat.i32 (y.setWidth 32)]) (r := some [Flat.i32 y]) rfl
    (bin_coreOut instSummary_mul hz)

/-- `get-or-zero(none)` returns `0`, for every profile. -/
theorem option_none_spec (P : Profile) :
    Outcome.returns (some [toRefVal (.u32 0)]) ∈
      exportSpec P optionS optionS.exports[0] [.variant 0 none] :=
  mem_exportSpec (c := optionS) (x := optionS.exports[0]) (xs := [Flat.i32 0, Flat.i32 0])
    (r := some [Flat.i32 0]) rfl (bin_coreOut instSummary_mul rfl)

/-! ## IR plays, for every profile -/

theorem toRefVal_eq_u32 {w : Silmaril.Wasm.Component.Val} {x : BitVec 32}
    (h : toRefVal w = toRefVal (.u32 x)) : w = .u32 x := by
  cases w <;> simp only [toRefVal, reduceCtorEq] at h
  case u32 x' =>
    have hx : x'.toNat = x.toNat := by simpa using h
    rw [BitVec.toNat_inj.mp hx]
  all_goals
    first
    | (have h' := congrArg (fun v => match v with
        | Silmaril.Wasm.Component.Value.Val.int k _ => k
        | _ => .u8) h
       simp at h')

/-- The IR play of a returned specification outcome with one result. -/
theorem ir_of_spec {P : Profile} {c : Simple} (hc : c.Good) (j : Fin c.exports.length)
    {vs : List Silmaril.Wasm.Component.Val} {x : BitVec 32}
    (h : Outcome.returns (some [toRefVal (.u32 x)]) ∈ exportSpec P c c.exports[j] vs) :
    two (E := sigN 0) (F := sigN c.toComp.exports.length)
      (⟨j, by simp [Simple.toComp]⟩, .vals vs) (some (.vals [.u32 x])) ∈
      c.toComp.den (modSem P) := by
  obtain ⟨ws, hws, hp⟩ := Silmaril.Proofs.Wasm.Component.Reference.specToIR P c hc j vs _ h
  rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩
  · cases hws
  · have hw' : w = .u32 x := toRefVal_eq_u32 (List.cons.inj hws).1.symm
    rw [hw'] at hp
    exact hp
  · cases (List.cons.inj hws).2

theorem adder_ir (P : Profile) (x y : BitVec 32) :
    two (E := sigN 0) (F := sigN adderS.toComp.exports.length) (⟨0, by decide⟩, .vals [.u32 x, .u32 y])
      (some (.vals [.u32 (x + y)])) ∈ adderS.toComp.den (modSem P) :=
  ir_of_spec adderS_good ⟨0, by decide⟩ (adder_spec P x y)

theorem record_ir (P : Profile) (x y : BitVec 32) :
    two (E := sigN 0) (F := sigN recordS.toComp.exports.length)
      (⟨0, by decide⟩, .vals [.record [.u32 x, .u32 y]])
      (some (.vals [.u32 (x + y)])) ∈ recordS.toComp.den (modSem P) :=
  ir_of_spec recordS_good ⟨0, by decide⟩ (record_spec P x y)

theorem option_some_ir (P : Profile) (y : BitVec 32) :
    two (E := sigN 0) (F := sigN optionS.toComp.exports.length)
      (⟨0, by decide⟩, .vals [.variant 1 (some (.u32 y))])
      (some (.vals [.u32 y])) ∈ optionS.toComp.den (modSem P) :=
  ir_of_spec optionS_good ⟨0, by decide⟩ (option_some_spec P y)

theorem option_none_ir (P : Profile) :
    two (E := sigN 0) (F := sigN optionS.toComp.exports.length)
      (⟨0, by decide⟩, .vals [.variant 0 none])
      (some (.vals [.u32 0])) ∈ optionS.toComp.den (modSem P) :=
  ir_of_spec optionS_good ⟨0, by decide⟩ (option_none_spec P)

/-! ## Sequences of calls -/

/-- Every host-free Core run from a thread is the configuration of a host-free run of the
machine. -/
theorem reach_of_steps {P : Profile} {s : Store Nat} {t : Silmaril.Wasm.SingleThreaded.Thread}
    {d : Config Nat}
    (h : Steps P (Silmaril.Wasm.SingleThreaded.Det.noHost : HostSemantics Nat) (t.config s) d) :
    ∃ s' t', Reach P (s, t) (s', t') ∧ t'.config s' = d := by
  induction h with
  | refl => exact ⟨s, t, .refl, rfl⟩
  | @tail b e _ hst ih =>
    obtain ⟨s', t', hr, rfl⟩ := ih
    exact ⟨e.store, .active e.frame e.code, hr.tail ⟨e.frame, e.code, rfl, hst⟩, rfl⟩

/-- A call of the adder returns `x + y` and leaves the store unchanged, for every profile. -/
theorem adder_retAt (P : Profile) (x y : BitVec 32) :
    RetAt P adderS (binInst .add) adderS.exports[0] [.u32 x, .u32 y] (binStore .add)
      [.u32 (x + y)] (binStore .add) := by
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 0
        (lowerArgs adderS.exports[0].ty.params [.u32 x, .u32 y])).config (binStore .add))
      ⟨binStore .add, {}, vals [Val.i32 (x + y)]⟩ :=
    bin_run instSummary_add (z := x + y) rfl
  obtain ⟨s', t', hr, hd⟩ := reach_of_steps run
  have hs : (t'.config s').store = s' := by cases t' <;> rfl
  have h₂ : (t'.config s').store = binStore .add := by rw [hd]
  have hs' : s' = binStore .add := hs.symm.trans h₂
  have hres : ResultAt s' t' (.values [Val.i32 (x + y)]) := by
    show (t'.config s').code = _
    rw [hd]
    rfl
  exact ⟨rfl, t', [Val.i32 (x + y)], [Flat.i32 (x + y)], hs' ▸ hr, hs' ▸ hres, rfl, rfl⟩

/-- The adder's last call returns `x + y` at its store, for every profile. -/
theorem adder_specAt (P : Profile) (x y : BitVec 32) :
    Outcome.returns (some [toRefVal (.u32 (x + y))]) ∈
      specAt P adderS (binInst .add) adderS.exports[0] [.u32 x, .u32 y] (binStore .add) :=
  .inl ⟨some [Flat.i32 (x + y)], ⟨_, .values [Val.i32 (x + y)],
    bin_run instSummary_add (z := x + y) rfl, rfl, rfl⟩, rfl⟩

/-- **Two calls of the adder are one play of the IR**, for every profile. -/
theorem adder_seq_ir (P : Profile) (x y x' y' : BitVec 32) :
    seqMoves adderS [(⟨0, by decide⟩, [.u32 x, .u32 y]), (⟨0, by decide⟩, [.u32 x', .u32 y'])]
      [[.u32 (x + y)], [.u32 (x' + y')]] ∈ adderS.toComp.den (modSem P) := by
  have hseq : SeqSpec P adderS (binInst .add) (binInst .add).store
      (specCalls adderS [(⟨0, by decide⟩, [.u32 x, .u32 y])]) [[.u32 (x + y)]] (binStore .add) :=
    .cons (adder_retAt P x y) (.nil _)
  obtain ⟨ws, hws, hp⟩ := seqSpecToIR P adderS adderS_good (binInst .add) (isInst instSummary_add)
    [(⟨0, by decide⟩, [.u32 x, .u32 y])] [[.u32 (x + y)]] (binStore .add) ⟨0, by decide⟩
    [.u32 x', .u32 y'] _ hseq (adder_specAt P x' y')
  have hw : ws = [.u32 (x' + y')] := by
    rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩
    · cases hws
    · rw [toRefVal_eq_u32 (List.cons.inj hws).1.symm]
    · cases (List.cons.inj hws).2
  rw [hw] at hp
  exact hp

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
