module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkIR
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusSeqI

/-!
# Two linked litmus components: the IR side

`dblFwdL`: the doubler `dblS` answers the import `g` of `fwdS`. The instance of `dblCore3` is
computed by kernel evaluation of a Boolean summary (`dblSummary`), as for `binCore3`; the
export call `g(x)` is a Core 3.0 run built from `Step` rules for every profile and all `x`
(`dbl_run`: `local.get 0` twice and `i32.add`), a returned call of the specification leaving
the store unchanged (`dbl_retAt`). With the importer's play `fwd_path`, `linked2_specToIR`
gives the linked IR play of `f(x)` answered `x + x` (`dblFwd_ir`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## The doubler's instance -/

/-- The store of the instance of `dblCore3`. -/
def dblStore : Store Nat :=
  match instantiateOnce? (importStore []) dblCore3 [] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `dblCore3`. -/
def dblInst : ScalarInstance where
  imports := []
  exports := [⟨[.num (.int .i32)], [.num (.int .i32)]⟩]
  addrs := [0]
  store := dblStore

/-- The function instance has the body `local.get 0; local.get 0; i32.add` and no locals. -/
def isDbl (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet x₀, .localGet x₁, .intBinOp .i32 .add]⟩ =>
    x₀.toNat == 0 && x₁.toNat == 0
  | _ => false

/-- The function type of the export. -/
abbrev dblFn : FnType := ⟨[.num (.int .i32)], [.num (.int .i32)]⟩

/-- The checks on the instantiated store and frame. -/
def dblBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some dblFn] &&
    (s.funcs.map isDbl) == [true]

/-- The Boolean summary of the instantiation of `dblCore3`. -/
def dblSummary : Bool :=
  ((Silmaril.Wasm.Validation.validate? dblCore3).map (·.imports.length) == some 0) &&
    runOk dblBody (instantiateOnce? (importStore []) dblCore3 [])

theorem dblSummary_eq : dblSummary = true := by decide +kernel

theorem isDbl_code {fi : FuncInst Nat} (h : isDbl fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x₀ x₁ : Silmaril.Wasm.LocalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.localGet x₀, .localGet x₁, .intBinOp .i32 .add] ∧
      x₀.toNat = 0 ∧ x₁.toNat = 0 := by
  unfold isDbl at h
  split at h
  next t x₀ x₁ hc =>
    have h' : x₀.toNat = 0 ∧ x₁.toNat = 0 := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨_, x₀, x₁, hc, rfl, rfl, h'.1, h'.2⟩
  next => cases h

/-- The facts the summary records. -/
structure DblFacts : Prop where
  valid : ∃ mt, Silmaril.Wasm.Validation.validate? dblCore3 = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) dblCore3 [] =
    some (dblStore, f, none) ∧ exportFuncAddrs f.module = [0]
  func : ∃ fi : FuncInst Nat, dblStore.funcs = [fi] ∧ FnType.ofDefType? fi.type = some dblFn ∧
    isDbl fi = true

theorem dblFacts : DblFacts := by
  have h' : (Silmaril.Wasm.Validation.validate? dblCore3).map (·.imports.length) = some 0 ∧
      runOk dblBody (instantiateOnce? (importStore []) dblCore3 []) = true := by
    simpa only [dblSummary, Bool.and_eq_true, beq_iff_eq] using dblSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have hs : dblStore = s := by simp only [dblStore, hrun]
  have hb' : (exportFuncAddrs f.module = [0] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some dblFn]) ∧
      s.funcs.map isDbl = [true] := by
    simpa only [dblBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨fi, hfi⟩ : ∃ fi, s.funcs = [fi] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hb'.2)
  have hty : FnType.ofDefType? fi.type = some dblFn := by simpa [hfi] using hb'.1.2
  have hd : isDbl fi = true := by simpa [hfi] using hb'.2
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hb'.1.1⟩,
    ⟨fi, hs ▸ hfi, hty, hd⟩⟩

/-- `dblInst` is the instance of the doubler's module. -/
theorem dbl_isInst : dblS.mod.IsInst dblInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fi, hfuncs, hty, _⟩⟩ := dblFacts
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
    show dblStore.funcs[0]? = some fi
    rw [hfuncs]
    rfl

theorem dblS_good : dblS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [dblS, List.mem_singleton] at hx
    subst hx
    exact ⟨"f", rfl⟩⟩

/-! ## The doubler's call -/

/-- **The doubler's export call, for every profile and all arguments.** -/
theorem dbl_run {P : Profile} (x : BitVec 32) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke dblStore 0 [Val.i32 x]) ⟨dblStore, {}, vals [Val.i32 (x + x)]⟩ := by
  obtain ⟨_, _, ⟨fi, hfuncs, hty, hd⟩⟩ := dblFacts
  obtain ⟨code, x₀, x₁, hcode, hloc, hbody, h₀, h₁⟩ := isDbl_code hd
  have hf : dblStore.funcs[0]? = some fi := by rw [hfuncs]; rfl
  have he : Expand fi.type dblFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall fi.module [Val.i32 x] code.locals
  let n := (Silmaril.Wasm.Validation.Ty.ofList (dblFn.results.map ScalarType.toC)).length
  have hn : [Val.i32 (x + x)].length = n :=
    (Silmaril.Wasm.Validation.Ty.length_ofList (dblFn.results.map ScalarType.toC)).symm
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke dblStore 0 [Val.i32 x])
      ⟨dblStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Silmaril.Wasm.Validation.Ty.length_ofList (dblFn.params.map ScalarType.toC)).symm hcode
  have hl₀ : F.local? x₀ = some (some (Val.i32 x)) := by
    simp [F, Frame.local?, Frame.forCall, hloc, h₀]
  have hl₁ : F.local? x₁ = some (some (Val.i32 x)) := by
    simp [F, Frame.local?, Frame.forCall, hloc, h₁]
  have s₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨dblStore, F, expression code.body⟩ ⟨dblStore, F, vals [Val.i32 (x + x)]⟩ := by
    rw [hbody]
    exact body_run hl₀ hl₁ rfl
  have s₃ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨dblStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩
      ⟨dblStore, {}, [.frame n F [.label n [] (vals [Val.i32 (x + x)])]]⟩ :=
    steps_frame_label s₂
  have s₄ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨dblStore, {}, [.frame n F [.label n [] (vals [Val.i32 (x + x)])]]⟩
      ⟨dblStore, {}, [.frame n F (vals [Val.i32 (x + x)])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨dblStore, {}, [.frame n F (vals [Val.i32 (x + x)])]⟩ ⟨dblStore, {}, vals [Val.i32 (x + x)]⟩ :=
    .frameVals hn
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-- A call of the doubler returns `x + x` and leaves the store unchanged, for every profile. -/
theorem dbl_retAt (P : Profile) (x : BitVec 32) :
    RetAt P dblS dblInst dblS.exports[0] [.u32 x] dblStore [.u32 (x + x)] dblStore := by
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invokeFlat 0
        (lowerArgs dblS.exports[0].ty.params [.u32 x])).config dblStore)
      ⟨dblStore, {}, vals [Val.i32 (x + x)]⟩ :=
    dbl_run x
  obtain ⟨s', t', hr, hd⟩ := reach_of_steps run
  have hs : (t'.config s').store = s' := by cases t' <;> rfl
  have h₂ : (t'.config s').store = dblStore := by rw [hd]
  have hs' : s' = dblStore := hs.symm.trans h₂
  have hres : ResultAt s' t' (.values [Val.i32 (x + x)]) := by
    show (t'.config s').code = _
    rw [hd]
    rfl
  exact ⟨rfl, t', [Val.i32 (x + x)], [Flat.i32 (x + x)], hs' ▸ hr, hs' ▸ hres, rfl, rfl⟩

/-! ## The linked IR play -/

/-- **The linked IR doubles**: for every profile and all `x`, the linked component's denotation
plays `f(x)` answered `x + x` (the importer forwards to its import `g`, answered by the
doubler's export `g` from the doubler instance's store). -/
theorem dblFwd_ir (P : Profile) (x : BitVec 32) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [.u32 x])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [.u32 x])) (some (.vals [.u32 (x + x)])))] :
      List (Move (dblFwdL.toComp.imports.sig) (sigN dblFwdL.toComp.exports.length))) ∈
      dblFwdL.toComp.den (impSem P) := by
  have hrun : Linked2.ExpRun P dblFwdL dblInst dblInst.store
      [⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 (x + x)])⟩] :=
    .ret ⟨0, by decide⟩ rfl (dbl_retAt P x) (.nil _)
  exact (linked2_specToIR P dblFwdL dblS_good fwdS_good dblInst dbl_isInst fwdInst fwd_isInst
    ⟨0, by decide⟩ [.u32 x]).2 [Flat.i32 x] rfl (fwdQ x) rfl rfl [⟨fwdE x, fwdAI x (x + x)⟩]
    (fwdAO x (x + x)) _ (fwd_path P x (x + x))
    [[⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 (x + x)])⟩]]
    (.cons (fwd_impRel x (x + x)) .nil) hrun

/-- **Two linked calls are one IR play**: for every profile and all `x`, `x'`, the linked IR plays
`f(x)` answered `x + x`, then `f(x')` answered `x' + x'` (through `linked_seq_den`, the importer's
two instance plays and two returned calls of the doubler, its store threaded). -/
theorem dblFwd_seq_ir (P : Profile) (x x' : BitVec 32) :
    cplay ([fwdIRRound x (x + x), fwdIRRound x' (x' + x')].map
      (Linked2.linkRound dblFwdL)) ∈ dblFwdL.toComp.den (impSem P) := by
  have hpath : fwdInst.Path P (.idle fwdInst.store)
      (cplay ([fwdRound x (x + x)] ++ [fwdRound x' (x' + x')])) (.idle fwdStore) := by
    rw [cplay_append]
    exact path_append (fwd_path P x (x + x)) (fwd_path P x' (x' + x'))
  have hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI fwdS fwdInst j vs r u)
      [fwdRound x (x + x), fwdRound x' (x' + x')] [fwdIRRound x (x + x), fwdIRRound x' (x' + x')] :=
    .cons (fwd_irRound x (x + x)) (.cons (fwd_irRound x' (x' + x')) .nil)
  have hrun : Linked2.ExpRun P dblFwdL dblInst dblInst.store
      [⟨(⟨0, by decide⟩, .vals [.u32 x]), some (.vals [.u32 (x + x)])⟩,
        ⟨(⟨0, by decide⟩, .vals [.u32 x']), some (.vals [.u32 (x' + x')])⟩] :=
    .ret ⟨0, by decide⟩ rfl (dbl_retAt P x) (.ret ⟨0, by decide⟩ rfl (dbl_retAt P x') (.nil _))
  exact linked_seq_den (l := dblFwdL) dblS_good fwdS_good dbl_isInst fwd_isInst hrel
    (cplay_mem_strategy hpath) hrun

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
