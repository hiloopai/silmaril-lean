module

public import Silmaril.Wasm.Component.Reference.LinkFloatWire.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkIR
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLink
public import Silmaril.Proofs.Wasm.Component.Reference.SplitBack
public import Silmaril.Proofs.Wasm.Component.Reference.LinkWire

/-!
# A float across the wiring of two linked litmus components

`nanRbL`: the importer `nanImpS` passes the non-canonical NaN `nan:0x200001` (bits `0x7fa00001`)
to its import `g`, answered by the exporter `nanRbS`, whose `g` returns the bits of its `f32`
argument (`i32.reinterpret_f32`).

* The exporter's instance and call (`rbFacts`, `rb_isInst`, `rb_run`, `rb_retAt`): kernel
  evaluation of a Boolean summary of the instantiation, then a Core 3.0 run built from `Step`
  rules for every profile and all bits.
* The importer's instance and play (`nanFacts`, `nan_isInst`, `nan_path`): the call of `f` enters
  its frame, `call 0` reaches the host function of the import with the raw bits of the constant
  (`decompose?_fill`), and the answer leaves the label and the frame, for every profile.
* `nanRb_ir`: through `linked2_specToIR`, for every profile the linked IR plays `f()` answered
  with the raw bits `0x7fa00001`.
* `nanRb_ref`: over `core3 neverFail` with the deterministic first-alternative oracle, the
  reference machine returns the bits `0x7fc00000` of the canonical NaN (`decide +kernel` on the
  copied drivers): the trampoline's `lift_flat` canonicalises the NaN before the exporter sees it.
* The conditions of `Linked2.sound_floatV` other than `ImportsFloatFree` hold
  (`nanRbS_inst`, `nanImpS_inst`, `nanImpS_arity`, `nanRbL_wireTy`, `nanRbL_namesOk`,
  `nanRbL_wireNodup`, `nanRbL_splitOk`), and `ImportsFloatFree` fails.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- The store of the instance of `rbCore3`. -/
def rbStore : Store Nat :=
  match instantiateOnce? (importStore []) rbCore3 [] with
  | some (s, _, _) => s
  | none => {}

/-- The function type of the exporter's core export. -/
abbrev rbFn : FnType := ⟨[.num (.float .f32)], [.num (.int .i32)]⟩

/-- The instance of `rbCore3`. -/
def rbInst : ScalarInstance where
  imports := []
  exports := [rbFn]
  addrs := [0]
  store := rbStore

/-- The function instance has the body `local.get 0; i32.reinterpret_f32` and no locals. -/
def isRb (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet x₀, .convert (.reinterpretInt .f32)]⟩ => x₀.toNat == 0
  | _ => false

/-- The checks on the instantiated store and frame. -/
def rbBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some rbFn] &&
    (s.funcs.map isRb) == [true]

/-- The Boolean summary of the instantiation of `rbCore3`. -/
def rbSummary : Bool :=
  ((Silmaril.Wasm.Validation.validate? rbCore3).map (·.imports.length) == some 0) &&
    runOk rbBody (instantiateOnce? (importStore []) rbCore3 [])

theorem rbSummary_eq : rbSummary = true := by decide +kernel

theorem isRb_code {fi : FuncInst Nat} (h : isRb fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x₀ : Silmaril.Wasm.LocalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.localGet x₀, .convert (.reinterpretInt .f32)] ∧
      x₀.toNat = 0 := by
  unfold isRb at h
  split at h
  next t x₀ hc => exact ⟨_, x₀, hc, rfl, rfl, by simpa only [beq_iff_eq] using h⟩
  next => cases h

/-- The facts the summary records. -/
structure RbFacts : Prop where
  valid : ∃ mt, Silmaril.Wasm.Validation.validate? rbCore3 = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) rbCore3 [] =
    some (rbStore, f, none) ∧ exportFuncAddrs f.module = [0]
  func : ∃ fi : FuncInst Nat, rbStore.funcs = [fi] ∧ FnType.ofDefType? fi.type = some rbFn ∧
    isRb fi = true

theorem rbFacts : RbFacts := by
  have h' : (Silmaril.Wasm.Validation.validate? rbCore3).map (·.imports.length) = some 0 ∧
      runOk rbBody (instantiateOnce? (importStore []) rbCore3 []) = true := by
    simpa only [rbSummary, Bool.and_eq_true, beq_iff_eq] using rbSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have hs : rbStore = s := by simp only [rbStore, hrun]
  have hb' : (exportFuncAddrs f.module = [0] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some rbFn]) ∧
      s.funcs.map isRb = [true] := by
    simpa only [rbBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨fi, hfi⟩ : ∃ fi, s.funcs = [fi] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hb'.2)
  have hty : FnType.ofDefType? fi.type = some rbFn := by simpa [hfi] using hb'.1.2
  have hd : isRb fi = true := by simpa [hfi] using hb'.2
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hb'.1.1⟩,
    ⟨fi, hs ▸ hfi, hty, hd⟩⟩

/-- `rbInst` is the instance of the exporter's module. -/
theorem rb_isInst : nanRbS.mod.IsInst rbInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fi, hfuncs, hty, _⟩⟩ := rbFacts
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
    show rbStore.funcs[0]? = some fi
    rw [hfuncs]
    rfl

theorem nanRbS_good : nanRbS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [nanRbS, List.mem_singleton] at hx
    subst hx
    exact ⟨"f", rfl⟩⟩

/-- `i32.reinterpret_f32` returns the bits, at every profile. -/
theorem convertP_reinterpret (P : Profile) (x : BitVec 32) :
    Silmaril.Wasm.Numerics.convertP P (.reinterpretInt .f32) x (.ok x) := by
  unfold Silmaril.Wasm.Numerics.convertP
  split <;> rfl

/-- **The exporter's export call, for every profile and all bits**: it returns the bits. -/
theorem rb_run {P : Profile} (x : BitVec 32) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke rbStore 0 [Val.num ⟨.float .f32, x⟩]) ⟨rbStore, {}, vals [Val.i32 x]⟩ := by
  obtain ⟨_, _, ⟨fi, hfuncs, hty, hd⟩⟩ := rbFacts
  obtain ⟨code, x₀, hcode, hloc, hbody, h₀⟩ := isRb_code hd
  have hf : rbStore.funcs[0]? = some fi := by rw [hfuncs]; rfl
  have he : Expand fi.type rbFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall fi.module [Val.num ⟨.float .f32, x⟩] code.locals
  let n := (Ty.ofList (rbFn.results.map ScalarType.toC)).length
  have hn : [Val.i32 x].length = n :=
    (Ty.length_ofList (rbFn.results.map ScalarType.toC)).symm
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke rbStore 0 [Val.num ⟨.float .f32, x⟩])
      ⟨rbStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Ty.length_ofList (rbFn.params.map ScalarType.toC)).symm hcode
  have hl₀ : F.local? x₀ = some (some (Val.num ⟨.float .f32, x⟩)) := by
    simp [F, Frame.local?, Frame.forCall, hloc, h₀]
  have a₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨rbStore, F, vals [] ++ [.plain (.localGet x₀)] ++
        [.plain (.convert (.reinterpretInt .f32))]⟩
      ⟨rbStore, F, vals [] ++ [(Val.num ⟨.float .f32, x⟩).toAdmin] ++
        [.plain (.convert (.reinterpretInt .f32))]⟩ :=
    .ctxtInstrs (.variable (.localGet hl₀)) (.inr (by simp))
  have a₂ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨rbStore, F, [(Val.num ⟨.float .f32, x⟩).toAdmin,
        .plain (.convert (.reinterpretInt .f32))]⟩
      ⟨rbStore, F, vals [Val.i32 x]⟩ :=
    .numeric (.convert (op := .reinterpretInt .f32) (convertP_reinterpret P x))
  have s₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨rbStore, F, expression code.body⟩ ⟨rbStore, F, vals [Val.i32 x]⟩ := by
    rw [hbody]
    exact (Relation.ReflTransGen.single a₁).tail a₂
  have s₃ := steps_frame_label (f := {}) (n := n) (m := n) (cont := []) s₂
  have s₄ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨rbStore, {}, [.frame n F [.label n [] (vals [Val.i32 x])]]⟩
      ⟨rbStore, {}, [.frame n F (vals [Val.i32 x])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨rbStore, {}, [.frame n F (vals [Val.i32 x])]⟩ ⟨rbStore, {}, vals [Val.i32 x]⟩ :=
    .frameVals hn
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-- A call of the exporter returns the bits of its argument and leaves the store unchanged,
for every profile. -/
theorem rb_retAt (P : Profile) (x : BitVec 32) :
    RetAt P nanRbS rbInst nanRbS.exports[0] [.f32 x] rbStore [.u32 x] rbStore := by
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 0
        (lowerArgs nanRbS.exports[0].ty.params [.f32 x])).config rbStore)
      ⟨rbStore, {}, vals [Val.i32 x]⟩ :=
    rb_run x
  obtain ⟨s', t', hr, hd⟩ := reach_of_steps run
  have hs : (t'.config s').store = s' := by cases t' <;> rfl
  have h₂ : (t'.config s').store = rbStore := by rw [hd]
  have hs' : s' = rbStore := hs.symm.trans h₂
  have hres : ResultAt s' t' (.values [Val.i32 x]) := by
    show (t'.config s').code = _
    rw [hd]
    rfl
  exact ⟨rfl, t', [Val.i32 x], [Flat.i32 x], hs' ▸ hr, hs' ▸ hres, rfl, rfl⟩


/-! ## The importer -/

open Silmaril.Wasm.SingleThreaded

/-- The closed import types of `nanCore3`. -/
def nanImports : List Silmaril.Wasm.Validation.DefType :=
  match Silmaril.Wasm.Validation.validate? nanCore3 with
  | some mt => Silmaril.Wasm.Validation.CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `nanCore3` against one host function. -/
def nanStore : Store Nat :=
  match instantiateOnce? (importStore nanImports) nanCore3 [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The import's function type `(f32) -> (i32)`. -/
abbrev gFn : FnType := ⟨[.num (.float .f32)], [.num (.int .i32)]⟩

/-- The export's function type `() -> (i32)`. -/
abbrev fFn : FnType := ⟨[], [.num (.int .i32)]⟩

/-- The instance of `nanCore3`. -/
def nanInst : ScalarInstance where
  imports := [gFn]
  exports := [fFn]
  addrs := [1]
  store := nanStore

/-- The function instance has the body `f32.const nan:0x200001; call 0`, no locals, and its
module's function `0` is the import at address `0`. -/
def isNanF (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.floatConst .f32 b, .call x]⟩ =>
    b.toNat == nanBits.toNat && x.toNat == 0 && fi.module.funcs[0]? == some 0
  | _ => false

/-- The checks on the instantiated store and frame. -/
def nanBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [1] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some gFn, some fFn] &&
    hostArity? s 0 == some (0, 1) && (s.funcs.map isNanF) == [false, true]

/-- The Boolean summary of the instantiation of `nanCore3`. -/
def nanSummary : Bool :=
  match validate? nanCore3 with
  | some mt => mt.imports.length == 1 && mt.imports.all isFuncImport &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some gFn] &&
      runOk nanBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) nanCore3
        [.func 0])
  | none => false

theorem nanSummary_eq : nanSummary = true := by decide +kernel


theorem isNanF_code {fi : FuncInst Nat} (h : isNanF fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.FuncIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.floatConst .f32 nanBits, .call x] ∧ x.toNat = 0 ∧
      fi.module.funcs[0]? = some 0 := by
  unfold isNanF at h
  split at h
  next t b x hc =>
    have h' : (b.toNat = nanBits.toNat ∧ x.toNat = 0) ∧ fi.module.funcs[0]? = some 0 := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨⟨hb, hx⟩, hm⟩ := h'
    have hb' : b = nanBits := BitVec.eq_of_toNat_eq hb
    subst hb'
    exact ⟨_, x, hc, rfl, rfl, hx, hm⟩
  next => cases h

theorem hostArity?_code {s : Store Nat} {a h n : Nat} (hh : hostArity? s a = some (h, n)) :
    ∃ fi : FuncInst Nat, s.funcs[a]? = some fi ∧ fi.code = .host h := by
  unfold hostArity? at hh
  split at hh
  next fi hfi =>
    split at hh
    next h' _ _ hc _ =>
      cases hh
      exact ⟨fi, hfi, hc⟩
    next => cases hh
  next => cases hh

/-- The facts the summary records. -/
structure NanFacts : Prop where
  valid : ∃ mt, validate? nanCore3 = some mt ∧ mt.imports.length = 1 ∧
    (∀ xt ∈ mt.imports, ∃ d, xt = .func d) ∧
    List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) (CExternType.funcs mt.imports)
      [gFn] ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports)) nanCore3
      [.func 0] = some (nanStore, f, none) ∧ exportFuncAddrs f.module = [1]
  funcs : ∃ fh fi : FuncInst Nat, nanStore.funcs = [fh, fi] ∧
    FnType.ofDefType? fh.type = some gFn ∧ FnType.ofDefType? fi.type = some fFn ∧
    isNanF fi = true
  arity : hostArity? nanStore 0 = some (0, 1)

/-- The two function instances of the importer's store, from their summarised images. -/
theorem nanFuncs_of_map : ∀ {fs : List (FuncInst Nat)},
    fs.map (fun fi => FnType.ofDefType? fi.type) = [some gFn, some fFn] →
    fs.map isNanF = [false, true] →
    ∃ fh fi : FuncInst Nat, fs = [fh, fi] ∧ FnType.ofDefType? fh.type = some gFn ∧
      FnType.ofDefType? fi.type = some fFn ∧ isNanF fi = true
  | [fh, fi], hty, hnf => by
    have hty' : FnType.ofDefType? fh.type = some gFn ∧ FnType.ofDefType? fi.type = some fFn := by
      simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true] using hty
    have hnf' : isNanF fh = false ∧ isNanF fi = true := by
      simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true] using hnf
    exact ⟨fh, fi, rfl, hty'.1, hty'.2, hnf'.2⟩
  | [], hty, _ => nomatch hty
  | [_], hty, _ => by simp at hty
  | _ :: _ :: _ :: _, hty, _ => by simp at hty

/-- An import that `isFuncImport` accepts is a function import. -/
theorem func_of_isFuncImport {xt : CExternType} (hx : isFuncImport xt = true) :
    ∃ d, xt = .func d := by
  cases xt <;> first | exact ⟨_, rfl⟩ | cases hx

theorem nanFacts : NanFacts := by
  obtain ⟨mt, hmt⟩ : ∃ mt, validate? nanCore3 = some mt := by
    cases hv : validate? nanCore3 with
    | none => exact absurd nanSummary_eq (by simp [nanSummary, hv])
    | some mt => exact ⟨mt, rfl⟩
  have h' : ((mt.imports.length = 1 ∧ mt.imports.all isFuncImport = true) ∧
      (CExternType.funcs mt.imports).map FnType.ofDefType? = [some gFn]) ∧
      runOk nanBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) nanCore3
        [.func 0]) = true := by
    simpa only [nanSummary, hmt, Bool.and_eq_true, beq_iff_eq] using nanSummary_eq
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have himp : nanImports = CExternType.funcs mt.imports := by simp only [nanImports, hmt]
  have hs : nanStore = s := by simp only [nanStore, himp, hrun]
  have hb' : ((exportFuncAddrs f.module = [1] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
        [some gFn, some fFn]) ∧ hostArity? s 0 = some (0, 1)) ∧
      s.funcs.map isNanF = [false, true] := by
    simpa only [nanBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨d, hd, hdt⟩ := forall₂_of_map_single h'.1.2
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := fun xt hxt =>
    func_of_isFuncImport (List.all_eq_true.mp h'.1.1.2 xt hxt)
  have hfs : ∃ fh fi : FuncInst Nat, s.funcs = [fh, fi] ∧
      FnType.ofDefType? fh.type = some gFn ∧ FnType.ofDefType? fi.type = some fFn ∧
      isNanF fi = true := nanFuncs_of_map hb'.1.1.2 hb'.2
  exact ⟨⟨mt, hmt, h'.1.1.1, hfun, hd ▸ .cons hdt .nil, f, hs ▸ hrun, hb'.1.1.1⟩,
    hs ▸ hfs, hs ▸ hb'.1.2⟩

/-- `nanInst` is the instance of `nanMod`. -/
theorem nan_isInst : nanMod.IsInst nanInst := by
  obtain ⟨⟨mt, hmt, hlen, hfun, hty, f, hf, hfa⟩, ⟨fh, fi, hfuncs, hth, hti, _⟩, _⟩ := nanFacts
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [Silmaril.Wasm.Execution.Core.ExternAddr.func 0] := by
    rw [hlen]
    rfl
  refine ⟨⟨mt, ⟨hmt, hfun, hty, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fi, ?_, hti⟩ .nil
    show nanStore.funcs[1]? = some fi
    rw [hfuncs]
    rfl

theorem nanImpS_good : nanImpS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [nanImpS, List.mem_singleton] at hx
    subst hx
    exact ⟨"f", rfl⟩, rfl⟩


/-! ## The importer's play -/

/-- The `f32` NaN `nan:0x200001` as a Core value. -/
abbrev nanV : Silmaril.Wasm.Execution.Core.Val := .num ⟨.float .f32, nanBits⟩

/-- The export question `f()`. -/
def nanQ : nanInst.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The import question `g(nan:0x200001)`. -/
def nanE : nanInst.E.Op := ⟨⟨0, by decide⟩, ⟨[nanV], .cons ⟨nanBits, rfl⟩ .nil⟩⟩

/-- The answer `y` of the import question. -/
def nanAI (y : BitVec 32) : nanInst.E.Ar nanE := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

/-- The answer `y` of the export question. -/
def nanAO (y : BitVec 32) : nanInst.F.Ar nanQ := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

theorem nan_importOp : nanInst.importOp? 0 [nanV] = some nanE := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd nanE.2.2 ‹_›
  · exact absurd (show 0 < nanInst.imports.length by decide) ‹_›

/-- The callout context of `f`'s activation: its frame and its body's label. -/
def nanCtx (n : Nat) (F : Frame) : Ctx := .frame [] n F (.label [] n [] (.top [] []) []) []

/-- **The importer's play of `f()`**: the import call `g(nan:0x200001)` with the raw bits of
the constant, answered `y`, then the answer `y`, for every profile. -/
theorem nan_path (P : Profile) (y : BitVec 32) :
    nanInst.Path P (.idle nanInst.store)
      (.inr (.ask nanQ) :: callMoves [⟨nanE, nanAI y⟩] ++ [.inr (.ans nanQ (nanAO y))])
      (.idle nanStore) := by
  obtain ⟨_, ⟨fh, fi, hfuncs, hth, hti, hnf⟩, harity⟩ := nanFacts
  obtain ⟨code, x, hcode, hloc, hbody, hx, hm⟩ := isNanF_code hnf
  obtain ⟨fh', hf0', hcode0⟩ := hostArity?_code harity
  have hf0 : nanStore.funcs[0]? = some fh := by rw [hfuncs]; rfl
  have hfh : fh' = fh := Option.some_injective _ (hf0'.symm.trans hf0)
  subst hfh
  have hf1 : nanStore.funcs[1]? = some fi := by rw [hfuncs]; rfl
  have he1 : Expand fi.type fFn.toComp := FnType.expand_of_ofDefType? hti
  have he0 : Expand fh'.type gFn.toComp := FnType.expand_of_ofDefType? hth
  let F := Frame.forCall fi.module [] code.locals
  let n := (Ty.ofList (fFn.results.map ScalarType.toC)).length
  have hn : [Val.i32 y].length = n :=
    (Ty.length_ofList (fFn.results.map ScalarType.toC)).symm
  have s₁ : Step P Det.noHost (invoke nanStore 1 [])
      ⟨nanStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf1 he1 (Ty.length_ofList (fFn.params.map ScalarType.toC)).symm hcode
  have hxF : F.module.funcs[x.toNat]? = some 0 := by rw [hx]; exact hm
  have a₁ : Step P Det.noHost ⟨nanStore, F, vals [nanV] ++ [.plain (.call x)] ++ []⟩
      ⟨nanStore, F, vals [nanV] ++ [.ref (.func 0), .callRefType fh'.type] ++ []⟩ :=
    .ctxtInstrs (.call hxF hf0) (.inl (by simp))
  have s₂ : Steps P Det.noHost ⟨nanStore, F, expression code.body⟩
      ⟨nanStore, F, vals [nanV] ++ [.ref (.func 0), .callRefType fh'.type] ++ []⟩ := by
    rw [hbody]
    exact .single a₁
  have run : Steps P Det.noHost ((nanInst.initThread nanQ).config nanInst.store)
      ⟨nanStore, {}, (nanCtx n F).fill (vals [nanV] ++ [.ref (.func 0), .callRefType fh'.type])⟩ :=
    (Relation.ReflTransGen.single s₁).trans (steps_frame_label s₂)
  obtain ⟨s₁', t₁, hr₁, hd₁⟩ := reach_of_steps run
  have hs₁ : s₁' = nanStore := by
    have h₁ : (t₁.config s₁').store = s₁' := by cases t₁ <;> rfl
    rw [← h₁, hd₁]
  subst hs₁
  have hdec : decompose? nanStore (t₁.config nanStore).code = some (nanCtx n F, 0, 0, [nanV]) := by
    rw [hd₁]
    exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ trivial hf0 he0
      (Ty.length_ofList (gFn.params.map ScalarType.toC)).symm hcode0
  have hco : CalloutAt nanStore t₁ 0 [nanV] := ⟨_, _, hdec⟩
  have hfr : (t₁.config nanStore).frame = {} := by rw [hd₁]
  have hres : resumeResult nanStore t₁ (Answer.toResult (nanAI y)) =
      .active {} [.frame n F [.label n [] (vals [Val.i32 y])]] := by
    unfold resumeResult
    simp only [hdec, hfr]
    rfl
  have run₂ : Steps P Det.noHost
      ((Thread.active {} [.frame n F [.label n [] (vals [Val.i32 y])]]).config nanStore)
      ⟨nanStore, {}, vals [Val.i32 y]⟩ :=
    (Relation.ReflTransGen.single (.ctxtFrame .labelVals)).tail (.frameVals hn)
  obtain ⟨s₂', t₂, hr₂, hd₂⟩ := reach_of_steps run₂
  have hs₂ : s₂' = nanStore := by
    have h₂ : (t₂.config s₂').store = s₂' := by cases t₂ <;> rfl
    rw [← h₂, hd₂]
  subst hs₂
  have hfin : ResultAt nanStore t₂ (.values [Val.i32 y]) := by
    show (t₂.config nanStore).code = _
    rw [hd₂]
    rfl
  have hans : Answer.ofResult? (nanInst.exports.get nanQ.1) (.values [Val.i32 y]) =
      some (nanAO y) := by
    unfold Answer.ofResult?
    exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
  refine .cons (.call _ _) (.cons (.ucall hr₁ hco nan_importOp) (.cons (.uret (nanAI y)) ?_))
  rw [hres]
  exact .cons (.oret hr₂ hfin hans) (.nil _)


/-! ## The linked IR play -/

theorem nan_impRel (y : BitVec 32) :
    Silmaril.Wasm.Component.Reference.ImpRel nanImpS nanInst ⟨nanE, nanAI y⟩
      [⟨(⟨0, by decide⟩, .vals [.f32 nanBits]), some (.vals [.u32 y])⟩] := by
  refine ⟨"g", ⟨[.f32], [.u32]⟩, some (.flat [Flat.i32 y]), rfl, ?_, ?_⟩
  · show payloadAnswer (nanInst.imports.get nanE.1) (some (.flat [Flat.i32 y])) = nanAI y
    have ht : typed? (nanInst.imports.get nanE.1).results ([Flat.i32 y].map ofFlat) =
        some ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩ := by
      unfold typed?
      exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
    unfold payloadAnswer
    dsimp only
    erw [ht]
    rfl
  · exact ⟨show 0 < 1 from Nat.zero_lt_one, _, rfl, rfl⟩

/-- **The linked IR passes the raw bits**: for every profile, the linked component's
denotation plays `f()` answered with the bits `0x7fa00001` of the importer's NaN constant (the
importer's call `g(nan:0x200001)` reaches the exporter's `i32.reinterpret_f32` bit for bit). -/
theorem nanRb_ir (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) (some (.vals [.u32 nanBits])))] :
      List (Move (nanRbL.toComp.imports.sig) (sigN nanRbL.toComp.exports.length))) ∈
      nanRbL.toComp.den (impSem P) := by
  have hrun : Linked2.ExpRun P nanRbL rbInst rbInst.store
      [⟨(⟨0, by decide⟩, .vals [.f32 nanBits]), some (.vals [.u32 nanBits])⟩] :=
    .ret ⟨0, by decide⟩ rfl (rb_retAt P nanBits) (.nil _)
  exact (linked2_specToIR P nanRbL nanRbS_good nanImpS_good rbInst rb_isInst nanInst nan_isInst
    ⟨0, by decide⟩ []).2 [] rfl nanQ rfl rfl [⟨nanE, nanAI nanBits⟩] (nanAO nanBits) _
    (nan_path P nanBits)
    [[⟨(⟨0, by decide⟩, .vals [.f32 nanBits]), some (.vals [.u32 nanBits])⟩]]
    (.cons (nan_impRel nanBits) .nil) hrun

/-! ## The reference machine -/

section Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine

theorem nanRbL_valid : ∃ ct, check? Features.p2 nanRbL.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- **The reference machine canonicalises the NaN**: over `core3 neverFail` with the
deterministic first-alternative oracle, `f()` returns the bits `0x7fc00000` of the canonical
NaN. -/
theorem nanRb_ref : Outcome.returns (some [toRefVal (.u32 canonBits)]) ∈
    exportBehaviours Silmaril.Wasm.Component.Reference.Core3Adder.first.prof
      (Host.ofEmbedder Silmaril.Wasm.Component.Reference.Core3Adder.emb) () nanRbL.toRef [] "f" [] :=
  returns_of_summary (by decide +kernel)

end Ref


/-! ## The conditions of `Linked2.sound_floatV` other than float-free imports -/

theorem nanRbS_inst : nanRbS.Inst := ⟨⟨rbInst, rb_isInst⟩, by decide⟩

/-- The validated import types of `nanCore3`, summarised. -/
def nanImportsSummary : Bool :=
  match Silmaril.Wasm.Validation.validate? nanCore3 with
  | some mt => decide (mt.imports =
      [.func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨[.float .f32], [.int .i32]⟩)])
  | none => false

theorem nanImportsSummary_eq : nanImportsSummary = true := by decide +kernel

theorem nan_importTypes : ∃ mt, Silmaril.Wasm.Validation.validate? nanCore3 = some mt ∧
    mt.imports = nanImpS.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩) := by
  have h : nanImportsSummary = true := nanImportsSummary_eq
  unfold nanImportsSummary at h
  split at h
  next mt hmt => exact ⟨mt, hmt, of_decide_eq_true h⟩
  next => cases h

theorem nanImpS_inst : nanImpS.Inst :=
  ⟨⟨nanInst, nan_isInst⟩, rfl, by decide, rfl, nan_importTypes⟩

theorem nanImpS_arity : nanImpS.Arity := by
  unfold SimpleI.Arity
  decide

theorem nanRbL_wireTy : nanRbL.WireTy := by
  refine ⟨rfl, fun k w hk => ?_⟩
  match k, hk with
  | 0, hk =>
    have hw : w = 0 := (Option.some.inj hk).symm
    subst hw
    exact ⟨_, rfl, rfl⟩

theorem nanRbL_namesOk : nanRbL.NamesOk := by
  refine ⟨fun x hx n => ?_, fun x hx n => ?_⟩
  · have hx' : x = ⟨"g", ⟨[.f32], [.u32]⟩, 0⟩ := List.mem_singleton.1 hx
    rw [hx']
    exact ne_tag_t rfl (by decide) n
  · have hx' : x = ⟨"f", ⟨[], [.u32]⟩, 0⟩ := List.mem_singleton.1 hx
    rw [hx']
    exact ne_tag_t rfl (by decide) n

theorem nanRbL_wireNodup : nanRbL.WireNodup := List.nodup_singleton 0

theorem nanRbL_splitOk : nanRbL.SplitOk :=
  ⟨⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The importer's import `g` carries an `f32`. -/
theorem nanRbL_not_importsFloatFree : ¬ nanRbL.ImportsFloatFree := by
  intro h
  have h' := (h _ (List.mem_singleton_self _)).1
  exact absurd h' (by decide)

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
