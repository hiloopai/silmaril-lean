module

public import Silmaril.Wasm.Spec.Component.Litmus.Defs
public import Silmaril.Wasm.Spec.Component.Ground.Thms
public import Silmaril.Wasm.Spec.Component.Async.Thms
public import Silmaril.Wasm.Spec.Joint.Wrap.Thms
public import Silmaril.Wasm.Spec.Basic.Thms
public import Silmaril.Wasm.Component.Reference.Litmus.Thms
public import Silmaril.Wasm.Component.Reference.Example.Thms
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Component litmus tests

On the litmus programs of `Silmaril.Wasm.Spec.Component.Litmus.Defs`.

* **Stages**: `level_*` compute the level of sample types; `adder_level` (IR interfaces are at
  most aggregates) and `Xs_level`, `Xh_level`, `Xa_level`.
* **Scalars, records, variants on real Core 3.0 code (every profile `P`)**: `adder_trace`,
  `record_trace`, `option_trace` (traces of the IR semantics `irSem (modSem P)`, from
  `Reference.Litmus.*_ir`); `adder_not_retPost` (the adder is refuted against the
  postcondition "never returns 7"); `adder_retPost_spec` (a postcondition verified on the IR
  must accept the specification's `x + y`: the grounding theorem `Simple.retPost_spec` at work);
  `adder_refSound` (`RefSound` for the adder, unconditional: the adder is within the flat
  arities, `adderS_arity`) and `adder_contract_ref` (a contract verified on the IR transfers to
  the reference machine over `core3P P`, unconditionally).
* **The reference machine**: `adder_ref_trace` (the reference adder over `core3 neverFail`
  returns `7` on `3, 4`, an `exportBehaviours` run checked by the copied drivers);
  `adder_ref_not_retPost`; `adder_ref_retTyped_trace` (the returned value has the result type).
* **Strings and lists** (loose semantics): `greetRun_contract`, `greetRun_callTyped`
  (the logged string is a valid `string`), `greetRun_retTyped`, `greetRun_not_retTyped_u32`
  (a `list<u8>` is not a `u32`).
* **Handles**: `handleRun_noUseAfterDrop`, `useAfterDrop_not_noUseAfterDrop`,
  `handleRun_borrowScoped`, `leakRun_not_borrowScoped`, `handleRun_droppedEventually`,
  `newOnly_not_droppedEventually`.
* **Streams**: `streamRun_streamSafe`, `doubleClose_not_streamSafe`,
  `streamRun_closedExactlyOnce`, `openRun_not_closedExactlyOnce`,
  `doubleClose_not_closedExactlyOnce`;
  `adder_async_streamSafe` (the IR adder, embedded as an async program, is stream safe).
* **Modules as components**: `wrapFn_add`, `wrapOut_throws` (uncaught exceptions trap at the
  boundary), `wrapSimple_add_iface` (the interface of the wrapping of the Core adder module
  is the image interface), `addModRun_push_retPost` (the comorphism of wrapping on a loose
  module program: a component postcondition of the wrapped program is the pulled postcondition
  of the module), `addModRun_joint` (a Core-level and a component-level postcondition of one
  module in the joint logic `modCompLogic`).
-/

namespace Silmaril.Wasm.Spec.Component.Litmus

open Silmaril.Wasm.Component.Reference (toRefVal Simple exportSpec)
open Silmaril.Wasm.Component.Reference.Litmus (adderS recordS optionS)
open Silmaril.Wasm.Numerics (Profile)

/-- The loose semantics of components. -/
abbrev S : Semantics CFn (List RVal) Outcome := Semantics.ofSets CFn (List RVal) Outcome

/-- The loose program whose traces are the prefixes of `l`. -/
def progOf {X : CIface} (l : List (CEvent X)) : S.Prog X := ⟨prefixesOf l, prefixesOf_good l⟩

/-- The loose semantics of async components. -/
abbrev SA : Semantics CFn AMsg AOut := Semantics.ofSets CFn AMsg AOut

/-- The loose async program whose traces are the prefixes of `l`. -/
def aprogOf {X : CIface} (l : List (AEvent X)) : SA.Prog X := ⟨prefixesOf l, prefixesOf_good l⟩

/-! ## Stages -/

theorem level_u32 : CTy.level tU32 = Level.scalar := rfl
theorem level_record : CTy.level (.record [("a", tU32), ("b", .prim .f64)]) = Level.aggregate :=
  rfl
theorem level_option : CTy.level (.option tU32) = Level.aggregate := rfl
theorem level_string : CTy.level tStr = Level.memory := rfl
theorem level_list : CTy.level (.list tU8) = Level.memory := rfl
theorem level_option_list : CTy.level (.option (.list tU8)) = Level.memory := rfl
theorem level_own : CTy.level (.own 0) = Level.async := rfl
theorem level_stream : CTy.level (.stream (some tU8)) = Level.async := rfl

theorem adder_level : (cface adderS.toComp).level ≤ Level.aggregate := cface_level _
theorem Xs_level : Xs.level = Level.memory := rfl
theorem Xh_level : Xh.level = Level.async := rfl
theorem Xa_level : Xa.level = Level.async := rfl

/-! ## Scalars, records and variants on Core 3.0 code -/

open Silmaril.Wasm.Component.Reference (modSem refHost)

/-- **The IR adder answers `x + y`** (every profile). -/
theorem adder_trace (P : Profile) (x y : BitVec 32) :
    [Event.call addE [toRefVal (.u32 x), toRefVal (.u32 y)],
      Event.ret addE (.returns (some [toRefVal (.u32 (x + y))]))] ∈
      (irSem (modSem P)).traces (Simple.irProg adderS) :=
  irTraces_call_ret _ _ _ _ _ _ (Silmaril.Wasm.Component.Reference.Litmus.adder_ir P x y)

/-- A record crosses the boundary. -/
theorem record_trace (P : Profile) (x y : BitVec 32) :
    [Event.call (Simple.expIdx recordS ⟨0, by decide⟩)
        [.record [toRefVal (.u32 x), toRefVal (.u32 y)]],
      Event.ret (Simple.expIdx recordS ⟨0, by decide⟩)
        (.returns (some [toRefVal (.u32 (x + y))]))] ∈
      (irSem (modSem P)).traces (Simple.irProg recordS) :=
  irTraces_call_ret _ _ _ _ _ _ (Silmaril.Wasm.Component.Reference.Litmus.record_ir P x y)

/-- A variant crosses the boundary: `get-or-zero(some y) = y`. -/
theorem option_trace (P : Profile) (y : BitVec 32) :
    [Event.call (Simple.expIdx optionS ⟨0, by decide⟩) [.variant 1 (some (toRefVal (.u32 y)))],
      Event.ret (Simple.expIdx optionS ⟨0, by decide⟩) (.returns (some [toRefVal (.u32 y)]))] ∈
      (irSem (modSem P)).traces (Simple.irProg optionS) :=
  irTraces_call_ret _ _ _ _ _ _ (Silmaril.Wasm.Component.Reference.Litmus.option_some_ir P y)

/-- **Refutation on real code**: the adder does return `7`. -/
theorem adder_not_retPost (P : Profile) :
    ¬ Models (retPost CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg adderS)
      ⟨addE, fun b => b ≠ .returns (some [u32 7])⟩ := by
  intro hM
  have h := (models_iff _ _ _ _).1 hM _ (adder_trace P 3 4)
    (.returns (some [toRefVal (.u32 (3 + 4))])) (by simp)
  exact h rfl

/-- **Grounding at work**: any return postcondition verified on the IR adder accepts the
canonical-ABI specification's result `x + y` (Core 3.0 runs, every profile). -/
theorem adder_retPost_spec (P : Profile) {Q : Outcome → Prop}
    (hM : Models (retPost CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg adderS)
      ⟨addE, Q⟩) (x y : BitVec 32) : Q (.returns (some [toRefVal (.u32 (x + y))])) :=
  Simple.retPost_spec P adderS Silmaril.Wasm.Component.Reference.Litmus.adderS_good ⟨0, by decide⟩
    hM [.u32 x, .u32 y] _ (Silmaril.Wasm.Component.Reference.Litmus.adder_spec P x y) trivial

/-- The adder is float-free. -/
theorem adderS_float : adderS.FloatFree := by
  intro x hx
  simp only [adderS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- The reference-machine half for the adder (unconditional: it is within the flat arities). -/
theorem adder_refSound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) :
    Simple.RefSound P prof adderS :=
  Simple.refSound_of_arity P prof Silmaril.Wasm.Component.Reference.Litmus.adderS_good adderS_float
    Silmaril.Wasm.Component.Reference.Litmus.adderS_inst
    Silmaril.Wasm.Component.Reference.Litmus.adderS_arity

/-- **Transfer to the reference machine**: a contract verified on the IR adder is a sentence
satisfied by the reference adder over `core3P P` (unconditional). -/
theorem adder_contract_ref (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    {pre : List RVal → Prop} {post : List RVal → Outcome → Prop}
    (hM : Models (contract CFn (List RVal) Outcome) (irSem (modSem P)) (Simple.irProg adderS)
      ⟨addE, pre, post⟩) :
    Models (contract CFn (List RVal) Outcome) (refSem prof (refHost P) ()) (Simple.refProg P adderS)
      ⟨addE, Simple.refPre adderS ⟨0, by decide⟩ pre, fun a b => Terminates b → post a b⟩ :=
  Simple.contract_of_refSound (adder_refSound P prof)
    Silmaril.Wasm.Component.Reference.Litmus.adderS_good ⟨0, by decide⟩ hM

/-! ## The reference machine -/

open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm.Component.Reference (Host)

/-- **The reference adder** (over `core3 neverFail`) returns `7` on `3, 4`. -/
theorem adder_ref_trace :
    [Event.call addE [u32 3, u32 4], Event.ret addE (.returns (some [u32 7]))] ∈
      (refSem first.prof (Host.ofEmbedder emb) ()).traces adderRef :=
  .inr (.inr ⟨addE, _, _, Silmaril.Wasm.Component.Reference.Litmus.adder_ref, rfl⟩)

/-- The reference adder refutes "never returns 7". -/
theorem adder_ref_not_retPost :
    ¬ Models (retPost CFn (List RVal) Outcome) (refSem first.prof (Host.ofEmbedder emb) ())
      adderRef ⟨addE, fun b => b ≠ .returns (some [u32 7])⟩ := by
  rw [refSem_retPost_iff]
  intro h
  exact h _ _ Silmaril.Wasm.Component.Reference.Litmus.adder_ref rfl

/-- The returned value has the declared result type `u32`. -/
theorem adder_ref_retTyped_trace :
    RetTyped.holds addE
      [Event.call addE [u32 3, u32 4], Event.ret addE (.returns (some [u32 7]))] := by
  intro rs hrs
  have hrs' : rs = [u32 7] := by simpa using hrs
  subst hrs'
  exact List.Forall₂.cons (.int rfl (by decide)) .nil

/-! ## Strings and lists (loose semantics) -/

/-- A per-trace action invariant on the prefixes of one trace. -/
theorem everyPos_prefixesOf_iff {α : Type} {P : List α → α → Prop} (l : List α) :
    (∀ t ∈ prefixesOf l, EveryPos P t) ↔ EveryPos P l :=
  ⟨fun h => h l (List.prefix_refl l), fun h _ hs => EveryPos.of_prefix h hs⟩

/-- `greet` returns the bytes of its argument. -/
theorem greetRun_contract :
    Models (contract CFn (List RVal) Outcome) S (progOf greetRun)
      ⟨greetE, fun _ => True, fun _ r => r = .returns (some [.list [u8 104, u8 105]])⟩ := by
  rw [models_iff]
  refine (everyPos_prefixesOf_iff greetRun).2 ?_
  rw [everyPos_iff_get]
  intro k hk r hr a _ _
  have hk' : k < 4 := hk
  interval_cases k <;> simp_all [greetRun, greetE, logI]

/-- The logged string is a valid `string` (import arguments are well typed). -/
theorem greetRun_callTyped : Models callTyped S (progOf greetRun) logI := by
  rw [models_iff]
  intro t ht a ha
  have ha' : a = [str "hi"] := by simpa [greetRun, greetE, logI] using ht.subset ha
  subst ha'
  exact List.Forall₂.cons (.string (by decide)) .nil

/-- The returned list of bytes is a `list<u8>`. -/
theorem greetRun_retTyped : Models retTyped S (progOf greetRun) greetE := by
  rw [models_iff]
  intro t ht rs hrs
  have hrs' : rs = [.list [u8 104, u8 105]] := by
    simpa [greetRun, greetE, logI] using ht.subset hrs
  subst hrs'
  refine List.Forall₂.cons (.list fun x hx => ?_) .nil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact .int rfl (by decide)

/-- A `list<u8>` is not a `u32`: `retTyped` at the wrong type fails. -/
theorem greetRun_not_retTyped_u32 :
    ¬ RetTyped.holds (X := ⟨[], [⟨[tStr], [tU32]⟩]⟩) ⟨0, by decide⟩
      [.ret ⟨0, by decide⟩ (.returns (some [.list [u8 104, u8 105]]))] := by
  intro h
  have ht := h _ (List.mem_singleton_self _)
  cases ht with
  | cons hv _ => cases hv

/-! ## Handles -/

/-- Handle `7` is not used after it is dropped. -/
theorem handleRun_noUseAfterDrop : Models noUseAfterDrop S (progOf handleRun) dropE := by
  rw [models_iff]
  refine (everyPos_prefixesOf_iff handleRun).2 ?_
  simp [handleRun, everyPos_cons, everyPos_nil, NoUseAfterDrop.pos, newE, useE, dropE,
    valsReps, valsHandles, valHandles]

/-- Using handle `7` after dropping it violates the protocol. -/
theorem useAfterDrop_not_noUseAfterDrop :
    ¬ Models noUseAfterDrop S (progOf useAfterDrop) dropE := by
  rw [models_iff]
  intro h
  have hpos := h useAfterDrop (List.prefix_refl _) handleRun (.call useE [.borrow 7]) [] rfl
  exact hpos useE [.borrow 7] rfl [.own 7] (by simp [handleRun, dropE]) 7
    (by simp [valsHandles, valHandles]) (by simp [valsReps, valsHandles, valHandles])

/-- `use` returns no handle it was lent. -/
theorem handleRun_borrowScoped : Models borrowScoped S (progOf handleRun) () := by
  rw [models_iff]
  refine (everyPos_prefixesOf_iff handleRun).2 ?_
  simp [handleRun, everyPos_cons, everyPos_nil, BorrowScoped.pos, newE, useE, dropE,
    pendingCall, callStep, valsReps, valsHandles, valHandles]

/-- Returning a lent handle violates `borrowScoped`. -/
theorem leakRun_not_borrowScoped : ¬ Models borrowScoped S (progOf leakRun) () := by
  rw [models_iff]
  intro h
  have hpos := h leakRun (List.prefix_refl _) [.call useE [.borrow 7]]
    (.ret useE (.returns (some [.own 7]))) [] rfl
  exact hpos useE [.own 7] rfl [.borrow 7] rfl 7 (by simp [valsHandles, valHandles])
    (by simp [valsReps, valsHandles, valHandles])

/-- **Drop after use**: the handle created by `new` is eventually dropped (on the maximal
behaviour). -/
theorem handleRun_droppedEventually :
    Models droppedEventually S (progOf handleRun) (newE, dropE) := by
  rw [models_iff]
  intro t ht k hk rs hrs r hr
  have htl : t = handleRun := maximal_prefixesOf_iff.1 ht
  subst htl
  have hk1 : k = 1 ∧ rs = [.own 7] := by
    have hk' : k < 6 := hk
    interval_cases k <;> simp_all [handleRun, newE, useE, dropE]
  obtain ⟨rfl, rfl⟩ := hk1
  have hr7 : r = 7 := by simpa [valsHandles, valHandles] using hr
  subst hr7
  exact ⟨[.own 7], by simp [handleRun], by simp [valsReps, valsHandles, valHandles]⟩

/-- A handle that is never dropped violates "drop after use". -/
theorem newOnly_not_droppedEventually :
    ¬ Models droppedEventually S (progOf (handleRun.take 2)) (newE, dropE) := by
  rw [models_iff]
  intro h
  obtain ⟨a, ha, -⟩ := h _ (maximal_prefixesOf_iff.2 rfl) 1 (by decide) [.own 7] rfl 7
    (by simp [valsHandles, valHandles])
  simp [handleRun] at ha

/-! ## Streams -/

/-- Stream end `3` is written once and closed once. -/
theorem streamRun_streamSafe : Models streamSafe SA (aprogOf streamRun) () := by
  rw [models_iff]
  refine (everyPos_prefixesOf_iff streamRun).2 ?_
  simp [streamRun, everyPos_cons, everyPos_nil, StreamSafe.pos, AEvent.Closes, AEvent.Writes,
    AEvent.msg?, AMsg.closeEnd?, AMsg.writeEnd?]

/-- Closing stream end `3` twice violates stream safety. -/
theorem doubleClose_not_streamSafe : ¬ Models streamSafe SA (aprogOf doubleClose) () := by
  rw [models_iff]
  intro h
  have hpos := h doubleClose (List.prefix_refl _) streamRun (.inr (.ask prodE (.close 3))) [] rfl
  exact hpos 3 (.inl rfl) (.inr (.ask prodE (.close 3))) (by simp [streamRun]) rfl

/-- **Closed exactly once**, on the maximal behaviour. -/
theorem streamRun_closedExactlyOnce : Models closedExactlyOnce SA (aprogOf streamRun) () := by
  rw [models_iff]
  intro t ht e he
  have htl : t = streamRun := maximal_prefixesOf_iff.1 ht
  subst htl
  have he3 : 3 = e := by
    simpa [streamRun, prodE, AEvent.Writes, AEvent.msg?, AMsg.writeEnd?] using he
  subst he3
  rfl

/-- A written end that is never closed violates "closed exactly once". -/
theorem openRun_not_closedExactlyOnce : ¬ Models closedExactlyOnce SA (aprogOf openRun) () := by
  rw [models_iff]
  intro h
  have hc := h openRun (maximal_prefixesOf_iff.2 rfl) 3
    ⟨.inr (.ask prodE (.write 3 [u8 1])), by simp [openRun, streamRun], rfl⟩
  exact absurd hc (by decide)

/-- A twice-closed end violates "closed exactly once". -/
theorem doubleClose_not_closedExactlyOnce :
    ¬ Models closedExactlyOnce SA (aprogOf doubleClose) () := by
  rw [models_iff]
  intro h
  have hc := h doubleClose (maximal_prefixesOf_iff.2 rfl) 3
    ⟨.inr (.ask prodE (.write 3 [u8 1])), by simp [doubleClose, streamRun], rfl⟩
  exact absurd hc (by decide)

/-- **The IR adder, embedded as an async program, is stream safe** (every profile). -/
theorem adder_async_streamSafe (P : Profile) :
    Models streamSafe (syncToAsync (irSem (modSem P))) (PushProg.ofProg (Simple.irProg adderS))
      () :=
  syncToAsync_streamSafe _ _

/-! ## Modules as components -/

theorem wrapFn_add : wrapFn ⟨[.int .i32, .int .i32], [.int .i32]⟩ = ⟨[tU32, tU32], [tU32]⟩ := rfl

/-- Uncaught exceptions trap at the component boundary. -/
theorem wrapOut_throws : wrapOut (.throws 3) = .traps := rfl

/-- The wrapping of the Core adder module (`local.get 0; local.get 1; i32.add`) is an IR
component at the image interface. -/
theorem wrapSimple_add_iface :
    cface (wrapSimple (Silmaril.Wasm.Component.Reference.Litmus.binMod .add)).toComp =
      (numIface (Silmaril.Wasm.Component.Reference.Litmus.binMod .add)).map wrapFn :=
  cface_wrapSimple _

/-- The loose semantics of numeric modules. -/
abbrev SM : Semantics Silmaril.Wasm.Component.CoreFuncTy (List Silmaril.Wasm.Execution.Core.Val)
    (Silmaril.Wasm.Behaviour Silmaril.Wasm.Execution.Core.Val) :=
  Semantics.ofSets _ _ _

/-- The loose module program of `addModRun`. -/
def addModProg : SM.Prog addNum := ⟨prefixesOf addModRun, prefixesOf_good _⟩

/-- The export `add` at the wrapped interface. -/
def addWE : (addNum.map wrapFn).Exp := Iface.expTo wrapFn addNum addNumE

/-- **The comorphism of wrapping on a module program**: the wrapped program returns `u32 7`. -/
theorem addModRun_push_retPost :
    Models (retPost CFn (List RVal) Outcome) (SM.push wrapFn (List.map wrapVal) wrapOut)
      (PushProg.ofProg addModProg) ⟨addWE, fun b => b = .returns (some [u32 7])⟩ := by
  rw [models_push_iff, models_iff]
  rintro _ ⟨u, hu, rfl⟩ r hr
  obtain ⟨x, hx, hxr⟩ := List.mem_map.1 hr
  have hx' : x ∈ addModRun := hu.subset hx
  simp only [addModRun, List.mem_cons, List.not_mem_nil, or_false] at hx'
  rcases hx' with rfl | rfl
  · cases hxr
  · have h1 := Sum.inr.inj hxr
    have hr' : wrapOut (.returns [.i32 7]) = r := (SideEv.ans.inj h1).2
    rw [← hr']
    rfl

/-- **Joint specification of a module**: a Core-level return postcondition and a pulled
component-level one, side by side in `modCompLogic`. -/
theorem addModRun_joint :
    Models (modCompLogic (retPost _ _ _) (retPost CFn (List RVal) Outcome)) SM addModProg
        (.inl ⟨addNumE, fun b => b = .returns [.i32 7]⟩) ∧
      Models (modCompLogic (retPost _ _ _) (retPost CFn (List RVal) Outcome)) SM addModProg
        (.inr ⟨addWE, fun b => b = .returns (some [u32 7])⟩) := by
  refine ⟨?_, (models_push_iff _ _ _ _ _ _ _).1 addModRun_push_retPost⟩
  apply (models_iff _ _ _ _).2
  intro t ht r hr
  have hr' : Event.ret addNumE r ∈ addModRun := ht.subset hr
  simpa [addModRun, addNumE] using hr'

end Silmaril.Wasm.Spec.Component.Litmus
