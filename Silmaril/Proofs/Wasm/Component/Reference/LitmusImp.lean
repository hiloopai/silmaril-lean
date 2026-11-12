module

public import Silmaril.Proofs.Wasm.Component.Reference.Litmus
public import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef

/-!
# A litmus component with an import: the IR side

`fwdS` imports `g: func(u32) -> u32`, lowers it into `fwdCore3`, which re-exports the import
as `f`, and lifts `f`. The instance of `fwdCore3` is computed by kernel evaluation of a Boolean
summary (`fwdSummary`). An export call of the instance is a callout at once
(`decompose?_top`: the invocation's `call_ref` of the host function), the environment's answer
is plugged into the empty context, and the result is the answer (`fwd_path`, every profile,
all arguments and answers). Through `simpleI_specToIR`, the IR denotation forwards the call to
the component import and returns its answer (`fwd_ir`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The scalar type `(i32) -> (i32)`. -/
abbrev fwdFn : FnType := ⟨[.num (.int .i32)], [.num (.int .i32)]⟩

/-- An import is a function. -/
def isFuncImport : CExternType → Bool
  | .func _ => true
  | _ => false

/-- The checks on the instantiated store and frame. -/
def fwdBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some fwdFn] &&
    hostArity? s 0 == some (0, 1)

/-- The Boolean summary of the instantiation of `fwdCore3`. -/
def fwdSummary : Bool :=
  match validate? fwdCore3 with
  | some mt => mt.imports.length == 1 && mt.imports.all isFuncImport &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some fwdFn] &&
      runOk fwdBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) fwdCore3
        [.func 0])
  | none => false

theorem fwdSummary_eq : fwdSummary = true := by decide +kernel

/-- A list whose image is a singleton is a singleton. -/
theorem forall₂_of_map_single {α β : Type} {g : α → Option β} {b : β} :
    ∀ {l : List α}, l.map g = [some b] → ∃ a, l = [a] ∧ g a = some b
  | [a], h => ⟨a, rfl, by simpa using h⟩
  | [], h => nomatch h
  | _ :: _ :: _, h => by simp at h

/-- The facts the summary records. -/
structure FwdFacts : Prop where
  valid : ∃ mt, validate? fwdCore3 = some mt ∧ mt.imports.length = 1 ∧
    (∀ xt ∈ mt.imports, ∃ d, xt = .func d) ∧
    List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) (CExternType.funcs mt.imports)
      [fwdFn] ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports)) fwdCore3
      [.func 0] = some (fwdStore, f, none) ∧ exportFuncAddrs f.module = [0]
  func : ∃ fi : FuncInst Nat, fwdStore.funcs = [fi] ∧ FnType.ofDefType? fi.type = some fwdFn
  arity : hostArity? fwdStore 0 = some (0, 1)

theorem fwdFacts : FwdFacts := by
  have h : fwdSummary = true := fwdSummary_eq
  unfold fwdSummary at h
  split at h
  next mt hmt =>
    show FwdFacts
    have h' : ((mt.imports.length = 1 ∧ mt.imports.all isFuncImport = true) ∧
        (CExternType.funcs mt.imports).map FnType.ofDefType? = [some fwdFn]) ∧
        runOk fwdBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) fwdCore3
          [.func 0]) = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
    have himp : fwdImports = CExternType.funcs mt.imports := by simp only [fwdImports, hmt]
    have hs : fwdStore = s := by simp only [fwdStore, himp, hrun]
    have hb' : (exportFuncAddrs f.module = [0] ∧
        (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some fwdFn]) ∧
        hostArity? s 0 = some (0, 1) := by
      simpa only [fwdBody, Bool.and_eq_true, beq_iff_eq] using hb
    obtain ⟨d, hd, hdt⟩ := forall₂_of_map_single h'.1.2
    obtain ⟨fi, hfi, hft⟩ := forall₂_of_map_single hb'.1.2
    have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := by
      intro xt hxt
      have hx : isFuncImport xt = true := List.all_eq_true.mp h'.1.1.2 xt hxt
      cases xt <;> first | exact ⟨_, rfl⟩ | cases hx
    exact ⟨⟨mt, hmt, h'.1.1.1, hfun, hd ▸ .cons hdt .nil, f, hs ▸ hrun, hb'.1.1⟩,
      ⟨fi, hs ▸ hfi, hft⟩, hs ▸ hb'.2⟩
  next => cases h

/-- `fwdInst` is the instance of `fwdMod`. -/
theorem fwd_isInst : fwdMod.IsInst fwdInst := by
  obtain ⟨⟨mt, hmt, hlen, hfun, hty, f, hf, hfa⟩, ⟨fi, hfuncs, hft⟩, _⟩ := fwdFacts
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [Silmaril.Wasm.Execution.Core.ExternAddr.func 0] := by
    rw [hlen]
    rfl
  refine ⟨⟨mt, ⟨hmt, hfun, hty, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fi, ?_, hft⟩ .nil
    show fwdStore.funcs[0]? = some fi
    rw [hfuncs]
    rfl

theorem fwdS_good : fwdS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [fwdS, List.mem_singleton] at hx
    subst hx
    exact ⟨"f", rfl⟩, rfl⟩

/-! ## The instance's play -/

/-- The export question `f(x)`. -/
def fwdQ (x : BitVec 32) : fwdInst.F.Op :=
  ⟨⟨0, by decide⟩, ⟨[Val.i32 x], .cons ⟨x, rfl⟩ .nil⟩⟩

/-- The import question `g(x)`. -/
def fwdE (x : BitVec 32) : fwdInst.E.Op :=
  ⟨⟨0, by decide⟩, ⟨[Val.i32 x], .cons ⟨x, rfl⟩ .nil⟩⟩

/-- The answer `y` of the import question `g(x)`. -/
def fwdAI (x y : BitVec 32) : fwdInst.E.Ar (fwdE x) := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

/-- The answer `y` of the export question `f(x)`. -/
def fwdAO (x y : BitVec 32) : fwdInst.F.Ar (fwdQ x) := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

/-- The invocation is a callout of the host function. -/
theorem fwd_decompose (x : BitVec 32) :
    decompose? fwdStore (fwdInst.initThread (fwdQ x) |>.config fwdStore).code =
      some (.top [] [], 0, 0, [Val.i32 x]) := by
  have hc : (fwdInst.initThread (fwdQ x) |>.config fwdStore).code =
      vals ([Val.i32 x] ++ [.ref (.func 0)]) ++
        [.callRefType ((fwdStore.funcs[0]?.map FuncInst.type).getD default)] := by
    show vals [Val.i32 x] ++ _ = _
    rfl
  rw [hc, decompose?_top (pre := [Val.i32 x]) (n := 1) (by rfl) fwdFacts.arity (Nat.le_refl 1)]
  rfl

theorem fwd_importOp (x : BitVec 32) : fwdInst.importOp? 0 [Val.i32 x] = some (fwdE x) := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd (fwdE x).2.2 ‹_›
  · exact absurd (show 0 < fwdInst.imports.length by decide) ‹_›

/-- **The instance's play of `f(x)`**: the import call `g(x)`, answered `y`, then the answer
`y`, for every profile. -/
theorem fwd_path (P : Profile) (x y : BitVec 32) :
    fwdInst.Path P (.idle fwdInst.store)
      (.inr (.ask (fwdQ x)) :: callMoves [⟨fwdE x, fwdAI x y⟩] ++
        [.inr (.ans (fwdQ x) (fwdAO x y))])
      (.idle fwdStore) := by
  have hco : CalloutAt fwdStore (fwdInst.initThread (fwdQ x)) 0 [Val.i32 x] :=
    ⟨_, _, fwd_decompose x⟩
  have hres : resumeResult fwdInst.store (fwdInst.initThread (fwdQ x))
      (Answer.toResult (fwdAI x y)) = .active {} (vals [Val.i32 y]) := by
    have hd : decompose? fwdInst.store
        (fwdInst.initThread (fwdQ x) |>.config fwdInst.store).code =
        some (.top [] [], 0, 0, [Val.i32 x]) := fwd_decompose x
    unfold resumeResult
    simp only [hd]
    rfl
  have hfin : ResultAt fwdStore (.active {} (vals [Val.i32 y])) (.values [Val.i32 y]) := rfl
  have hans : Answer.ofResult? (fwdInst.exports.get (fwdQ x).1) (.values [Val.i32 y]) =
      some (fwdAO x y) := by
    unfold Answer.ofResult?
    exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
  refine .cons (.call _ _) (.cons (.ucall .refl hco (fwd_importOp x)) (.cons (.uret (fwdAI x y)) ?_))
  rw [hres]
  exact .cons (.oret .refl hfin hans) (.nil _)

/-! ## The IR play -/

theorem fwd_impRel (x y : BitVec 32) :
    ImpRel fwdS fwdInst ⟨fwdE x, fwdAI x y⟩
      [⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩] := by
  refine ⟨"g", ⟨[.u32], [.u32]⟩, some (.flat [Flat.i32 y]), rfl, ?_, ?_⟩
  · show payloadAnswer (fwdInst.imports.get (fwdE x).1) (some (.flat [Flat.i32 y])) = fwdAI x y
    have ht : typed? (fwdInst.imports.get (fwdE x).1).results ([Flat.i32 y].map ofFlat) =
        some ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩ := by
      unfold typed?
      exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
    unfold payloadAnswer
    dsimp only
    erw [ht]
    rfl
  · exact ⟨show 0 < 1 from Nat.zero_lt_one, _, rfl, rfl⟩

/-- **The IR forwards `f(x)` to the import `g`** and returns its answer, for every profile and
all `x` and `y`. -/
theorem fwd_ir (P : Profile) (x y : BitVec 32) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inl (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inl (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 y]))),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 y])))] :
      List (Move (sigN fwdS.imports.length) (sigN fwdS.toComp.exports.length))) ∈
      fwdS.toComp.den (impSem P) := by
  have h := (simpleI_specToIR P fwdS fwdS_good fwdInst fwd_isInst ⟨0, by decide⟩
    [.u32 x]).2 [Flat.i32 x] rfl (fwdQ x) rfl rfl [⟨fwdE x, fwdAI x y⟩] (fwdAO x y) _
    (fwd_path P x y)
    [[⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 y])⟩]] (.cons (fwd_impRel x y) .nil)
  exact h

/-! ## The reference machine -/

section Ref

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Reference.Core3Adder (first noReady)

theorem fwdS_valid : ∃ ct, check? Features.p2 fwdS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- Instantiation from the host functions' store, then the call of `name` on `vs`, summarised. -/
def callSummaryI (c : Core3Component) (ims : Iface) (name : String) (vs : List Value.Val) :
    Option (Machine.Outcome × Option (Option (List Value.Val))) :=
  (embI.instantiateRun first 400 c (importArgs ims)
      (Config.init (hostFuncs 0 ims CStore.empty) ())).bind fun (r, _, es) =>
    (es.lookup name).bind fun f =>
      (embI.callTop first 400 ⟨0⟩ f vs r.config).map fun r' => (r'.outcome, r'.config.result? ⟨0⟩)

/-- A resolved summary is a returned behaviour. -/
theorem returns_of_summaryI {c : Core3Component} {ims : Iface} {name : String}
    {vs rs : List Value.Val}
    (h : callSummaryI c ims name vs = some (.resolved, some (some rs))) :
    Outcome.returns (some rs) ∈
      exportBehavioursI first.prof (Host.ofEmbedder embI) () c ims name vs := by
  unfold callSummaryI at h
  obtain ⟨⟨r₁, inst, es⟩, hi, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f, hf, h₂⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨r, hc, h₃⟩ := Option.map_eq_some_iff.mp h₂
  have hr : r.outcome = .resolved ∧ r.config.result? ⟨0⟩ = some (some rs) := by
    simpa only [Prod.mk.injEq] using h₃
  have ho : callOutcome? ⟨0⟩ r = some (.resolved (some rs)) := by
    simp only [callOutcome?, hr.1, hr.2, Option.map_some]
  exact Or.inl ⟨r₁.config, inst, es, f, instantiateRun_mem embI first hi, hf,
    callTop_mem embI first hc ho⟩

/-- **The reference machine forwards `f(3)` to the host's `g`** and returns `g(3) = 4`. -/
theorem fwd_ref : Outcome.returns (some [toRefVal (.u32 4)]) ∈
    exportBehavioursI first.prof (Host.ofEmbedder embI) () fwdS.toRef fwdS.imports "f"
      [toRefVal (.u32 3)] :=
  returns_of_summaryI (by decide +kernel)

end Ref

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
