module

public import Silmaril.Proofs.Wasm.Component.Reference.StartISound
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusSoundI
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# A litmus component with an import and a start function

`startIS` imports `g: func(u32) -> u32`, lowered into `startICore3`, whose start function stores
`42` in a mutable global; it exports `f` (the import, forwarded) and `get` (reading the global).

* `startIS_instS` (`SimpleI.InstS`, by kernel evaluation of a summary of validation and
  instantiation: the host function at address `0`, the start function at address `1`, `get` at
  address `2`), `startIS_good`, `startIS_floatFree`, `startIS_arity`;
* `startIS_valid` (the validator accepts `startIS.toRef`) and `startI_ref`: over
  `core3 neverFail` with the host `g(n) = n + 1`, the reference machine instantiates
  `startIS.toRef`, running the start function, and `get()` returns `42`; `startI_ref_f`: `f(3)`
  returns `4`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
  Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The scalar type `() -> (i32)`. -/
abbrev getFnI : FnType := ⟨[], [.num (.int .i32)]⟩

/-- The start function's body: `i32.const 42; global.set 0`. -/
def startBodyOk : List Silmaril.Wasm.Instr → Bool
  | [.intConst .i32 n, .globalSet x] => n == 42 && x.toNat == 0
  | _ => false

/-- The start function's code and its global, in the instance store. -/
def startCodeOk (s : Store Nat) : Bool :=
  match s.funcs[1]? with
  | some fi =>
    match fi.code with
    | .wasm code => startBodyOk code.body && code.locals.isEmpty &&
        (s.global? (Frame.forCall fi.module [] []) ⟨0⟩).isSome
    | .host _ => false
  | none => false

/-- The checks on the instantiated store and frame, and the start function. -/
def startIBody : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx) → Bool
  | some (s, f, some x) => exportFuncAddrs f.module == [0, 2] &&
      f.module.funcs[x.toNat]? == some 1 &&
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) ==
        [some fwdFn, some startType, some getFnI] &&
      startCodeOk s
  | _ => false

/-- The Boolean summary of the validation and instantiation of `startICore3`. -/
def startISummary : Bool :=
  match validate? startICore3 with
  | some mt => decide (mt.imports =
        [.func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨[.int .i32], [.int .i32]⟩)]) &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some fwdFn] &&
      startIBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) startICore3
        [.func 0])
  | none => false

theorem startISummary_eq : startISummary = true := by decide +kernel

/-- The closed import types of `startICore3`. -/
def startIImports : List DefType :=
  match validate? startICore3 with
  | some mt => CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `startICore3` before its start function. -/
def startIStore : Store Nat :=
  match instantiateOnce? (importStore startIImports) startICore3 [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `startICore3` before its start function: the host function at `0`, `f` at
`0` and `get` at `2`. -/
def startIInst : ScalarInstance where
  imports := [fwdFn]
  exports := [fwdFn, getFnI]
  addrs := [0, 2]
  store := startIStore

theorem startIBody_eq {o : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx)}
    (h : startIBody o = true) :
    ∃ s f x, o = some (s, f, some x) ∧ exportFuncAddrs f.module = [0, 2] ∧
      f.module.funcs[x.toNat]? = some 1 ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
        [some fwdFn, some startType, some getFnI] ∧ startCodeOk s = true := by
  match o, h with
  | some (s, f, some x), h =>
    have h' : ((exportFuncAddrs f.module = [0, 2] ∧ f.module.funcs[x.toNat]? = some 1) ∧
        (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
          [some fwdFn, some startType, some getFnI]) ∧ startCodeOk s = true := by
      simpa only [startIBody, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨s, f, x, rfl, h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- A list whose image has three elements has three elements. -/
theorem map_three {α β : Type} {g : α → β} {b₀ b₁ b₂ : β} :
    ∀ {l : List α}, l.map g = [b₀, b₁, b₂] →
      ∃ a₀ a₁ a₂, l = [a₀, a₁, a₂] ∧ g a₀ = b₀ ∧ g a₁ = b₁ ∧ g a₂ = b₂
  | [a₀, a₁, a₂], h => by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨a₀, a₁, a₂, rfl, h.1, h.2.1, h.2.2⟩
  | [], h => nomatch h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _, h => by simp at h

/-- The facts the summary records. -/
theorem startIFacts : ∃ mt, validate? startICore3 = some mt ∧
    mt.imports = [.func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨[.int .i32], [.int .i32]⟩)] ∧
    (CExternType.funcs mt.imports).map FnType.ofDefType? = [some fwdFn] ∧
    ∃ f x, instantiateOnce? (importStore (CExternType.funcs mt.imports)) startICore3 [.func 0] =
        some (startIStore, f, some x) ∧ exportFuncAddrs f.module = [0, 2] ∧
      f.module.funcs[x.toNat]? = some 1 ∧
      (startIStore.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
        [some fwdFn, some startType, some getFnI] ∧ startCodeOk startIStore = true := by
  have h : startISummary = true := startISummary_eq
  unfold startISummary at h
  split at h
  next mt hmt =>
    have h' : (mt.imports =
          [.func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨[.int .i32], [.int .i32]⟩)] ∧
        (CExternType.funcs mt.imports).map FnType.ofDefType? = [some fwdFn]) ∧
        startIBody (instantiateOnce? (importStore (CExternType.funcs mt.imports)) startICore3
          [.func 0]) = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h
    obtain ⟨s, f, x, hrun, hfa, hx, hty, hcode⟩ := startIBody_eq h'.2
    have himp : startIImports = CExternType.funcs mt.imports := by simp only [startIImports, hmt]
    have hs : startIStore = s := by simp only [startIStore, himp, hrun]
    exact ⟨mt, hmt, h'.1.1, h'.1.2, f, x, hs ▸ hrun, hfa, hx, hs ▸ hty, hs ▸ hcode⟩
  next => cases h

/-- **`startIInst` is the instance of `startIMod` before its start function, at address `1`.** -/
theorem startIMod_isInstS : startIMod.IsInstS startIInst (some 1) := by
  obtain ⟨mt, hmt, himp, hdt, f, x, hrun, hfa, hx, hty, -⟩ := startIFacts
  obtain ⟨d, hd, hdt'⟩ := forall₂_of_map_single hdt
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [Silmaril.Wasm.Execution.Core.ExternAddr.func 0] := by
    rw [himp]
    rfl
  obtain ⟨fi₀, fi₁, fi₂, hfs, ht₀, -, ht₂⟩ := map_three hty
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := by
    intro xt hxt
    rw [himp] at hxt
    exact ⟨_, List.mem_singleton.mp hxt⟩
  refine ⟨⟨mt, ⟨hmt, hfun, hd ▸ .cons hdt' .nil, ⟨f, some x, ?_, hfa, .some hx⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hrun
  · refine .cons ⟨fi₀, ?_, ht₀⟩ (.cons ⟨fi₂, ?_, ht₂⟩ .nil)
    · show startIStore.funcs[0]? = some fi₀
      rw [hfs]
      rfl
    · show startIStore.funcs[2]? = some fi₂
      rw [hfs]
      rfl

theorem startIS_instS : startIS.InstS :=
  ⟨⟨startIInst, some 1, startIMod_isInstS⟩, rfl, by decide, rfl, by
    obtain ⟨mt, hmt, himp, -⟩ := startIFacts
    exact ⟨mt, hmt, himp⟩⟩

theorem startIS_good : startIS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [startIS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"f", rfl⟩
    · exact ⟨"get", rfl⟩, rfl⟩

theorem startIS_floatFree : startIS.FloatFree := by
  unfold SimpleI.FloatFree
  decide

theorem startIS_arity : startIS.Arity := by
  unfold SimpleI.Arity
  decide

theorem startIS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 startIS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- **The reference machine runs the start function**: over `core3 neverFail` with the host
`g(n) = n + 1`, `get()` after instantiation returns `42`. -/
theorem startI_ref : Outcome.returns (some [toRefVal (.u32 42)]) ∈
    exportBehavioursI Silmaril.Wasm.Component.Reference.Core3Adder.first.prof
      (Silmaril.Wasm.Component.Reference.Host.ofEmbedder embI) () startIS.toRef startIS.imports
      "get" [] :=
  returns_of_summaryI (by decide +kernel)

/-- Over `core3 neverFail` with the host `g(n) = n + 1`, `f(3)` returns `4`. -/
theorem startI_ref_f : Outcome.returns (some [toRefVal (.u32 4)]) ∈
    exportBehavioursI Silmaril.Wasm.Component.Reference.Core3Adder.first.prof
      (Silmaril.Wasm.Component.Reference.Host.ofEmbedder embI) () startIS.toRef startIS.imports
      "f" [toRefVal (.u32 3)] :=
  returns_of_summaryI (by decide +kernel)

/-! ## The start function makes no import call -/

/-- **The instance before the start function is unique**: its store is `startIStore` and the
start function is at address `1`. -/
theorem isInstS_startI {I : ScalarInstance} {st : Option Nat} (h : startIMod.IsInstS I st) :
    I.store = startIStore ∧ st = some 1 := by
  obtain ⟨⟨mt', hIs⟩, -, -⟩ := h
  obtain ⟨mt, hmt, himp, -, f, x, hrun, -, hx, -, -⟩ := startIFacts
  obtain rfl : mt' = mt := Option.some.inj (hIs.valid.symm.trans hmt)
  obtain ⟨f', st', hrun', -, hrel⟩ := hIs.instantiated
  have hr : (List.range mt'.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [Silmaril.Wasm.Execution.Core.ExternAddr.func 0] := by
    rw [himp]
    rfl
  have hrun'' : instantiateOnce? (importStore (CExternType.funcs mt'.imports)) startICore3
      [.func 0] = some (I.store, f', st') := by
    rw [← hr]
    exact hrun'
  have he : startIStore = I.store ∧ f = f' ∧ some x = st' := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hrun.symm.trans hrun''
  obtain ⟨hs, rfl, rfl⟩ := he
  cases hrel with
  | some ha =>
    rw [hx] at ha
    exact ⟨hs.symm, congrArg some (Option.some.inj ha).symm⟩

theorem startBodyOk_eq {b : List Silmaril.Wasm.Instr} (h : startBodyOk b = true) :
    b = [.intConst .i32 42, .globalSet ⟨0⟩] := by
  unfold startBodyOk at h
  split at h
  next n x =>
    have hn : n = 42 ∧ x.toNat = 0 := by simpa only [Bool.and_eq_true, beq_iff_eq] using h
    have hx0 : x = ⟨0⟩ := by
      obtain ⟨⟨v, hv⟩⟩ := x
      have hv0 : v = 0 := hn.2
      subst hv0
      rfl
    rw [hn.1, hx0]
  next => cases h

theorem startCodeOk_eq {s : Store Nat} (h : startCodeOk s = true) :
    ∃ (fi : FuncInst Nat) (code : Silmaril.Wasm.Func), s.funcs[1]? = some fi ∧
      fi.code = .wasm code ∧ startBodyOk code.body = true ∧ code.locals = [] ∧
      ∃ a g, s.global? (Frame.forCall fi.module [] []) ⟨0⟩ = some (a, g) := by
  unfold startCodeOk at h
  split at h
  next fi hfi =>
    split at h
    next code hcode =>
      have h' : (startBodyOk code.body = true ∧ code.locals.isEmpty = true) ∧
          (s.global? (Frame.forCall fi.module [] []) ⟨0⟩).isSome = true := by
        simpa only [Bool.and_eq_true] using h
      obtain ⟨⟨a, g⟩, hg⟩ := Option.isSome_iff_exists.mp h'.2
      exact ⟨fi, code, hfi, hcode, h'.1.1, List.isEmpty_iff.mp h'.1.2, a, g, hg⟩
    next => cases h
  next => cases h

/-- The start function's code. -/
theorem startCode_facts : ∃ (fi : FuncInst Nat) (code : Silmaril.Wasm.Func),
    startIStore.funcs[1]? = some fi ∧ fi.code = .wasm code ∧
    code.body = [.intConst .i32 42, .globalSet ⟨0⟩] ∧ code.locals = [] ∧
    ∃ a g, startIStore.global? (Frame.forCall fi.module [] []) ⟨0⟩ = some (a, g) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hc⟩ := startIFacts
  obtain ⟨fi, code, hfi, hcode, hb, hl, hg⟩ := startCodeOk_eq hc
  exact ⟨fi, code, hfi, hcode, startBodyOk_eq hb, hl, hg⟩

section Spec

open Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.Core

/-- The start function's specification: from `startIStore`, without arguments, every outcome
is a return of no values. -/
def startSpec : FSpec Nat where
  pre s args := s = startIStore ∧ args = []
  post _ _ _ o := o = .normal []

/-- **The start function meets its specification** (every profile, no host functions). -/
theorem startSpec_valid (P : Profile) : FSpecValid P Det.noHost 1 startSpec := by
  obtain ⟨fi, code, hfi, hcode, hbody, hloc, a, g, hg⟩ := startCode_facts
  obtain ⟨fi', hfi', he⟩ := startIMod_isInstS.startTyped 1 rfl
  have hfe : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  have he' : Expand fi.type startType.toComp := hfe ▸ he
  intro n
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    show FSpecAt P Det.noHost (n + 1) 1 startSpec
    refine FSpecAt.of_body (fun s _ h => h.1 ▸ hfi) hcode he' (fun _ _ h => by rw [h.2]; rfl)
      fun s args hpre f vs₀ => ?_
    rw [hpre.1, hpre.2]
    have hg' : startIStore.global? (Frame.forCall fi.module [] code.locals) ⟨0⟩ = some (a, g) := by
      rw [hloc]
      exact hg
    have h₁ : HWP P Det.noHost (startIStore.setGlobal a (.i32 42))
        (Frame.forCall fi.module [] code.locals) (vals [])
        (bodyPostK P Det.noHost _ f vs₀ (callPost f vs₀ (startSpec.post startIStore [])) n) :=
      HWP.of_vals ⟨rfl, rfl, .inl ⟨[], rfl, rfl⟩⟩
    have h₂ : Wp .part P Det.noHost startIStore (Frame.forCall fi.module [] code.locals)
        (vals ([] ++ [.i32 42]) ++ .plain (.globalSet ⟨0⟩) :: [])
        (bodyPostK P Det.noHost _ f vs₀ (callPost f vs₀ (startSpec.post startIStore [])) n) :=
      Wp.globalSet hg' (by simpa using h₁)
    rw [hbody]
    exact h₂ n

end Spec

/-- A configuration that steps without host functions is at no host-call redex. -/
theorem decompose_none_of_step {P : Profile} {c c'' : Config Nat}
    (h : Step P Det.noHost c c'') : decompose? c.store c.code = none := by
  rcases Step.split_host h with h' | ⟨E, a, hh, args, -, hhost⟩
  · exact decompose?_none_of_noRedex (Step.noRedex h')
  · rcases hhost with ⟨s', r, hr, -⟩ | ⟨hr, -⟩
    · exact hr.elim
    · exact hr.elim

/-- An exit of the start function's specification is at no host-call redex. -/
theorem decompose_none_of_exit {c : Config Nat} {o : Silmaril.Wasm.Logic.Core.Outcome}
    (hex : Silmaril.Wasm.Logic.Hoare.Exits o c.code)
    (hpost : Silmaril.Wasm.Logic.Hoare.callPost {} [] (startSpec.post startIStore []) c.store
      c.frame o) : decompose? c.store c.code = none := by
  obtain ⟨-, ⟨res, ho, hres⟩ | ⟨-, h⟩ | ⟨a, -, h⟩⟩ := hpost
  · have hr : res = [] := by
      cases hres
      rfl
    have hc : c.code = vals [] := by
      rw [ho, hr] at hex
      exact hex
    rw [hc]
    exact decompose?_vals_nil
  · cases h
  · cases h

/-- **The start function of `startIMod` makes no import call** (every profile). -/
theorem startIMod_noCall (P : Profile) : startIMod.StartNoCall P := by
  intro I st hI c' hs
  obtain ⟨hstore, hst⟩ := isInstS_startI hI
  have hs₁ : Steps P Det.noHost (startConfig I.store (some 1)) c' := hst ▸ hs
  have hs' : Steps P Det.noHost (invoke startIStore 1 []) c' := by
    rw [← hstore]
    exact hs₁
  rcases (startSpec_valid P).invoke_safe ⟨rfl, rfl⟩ hs' with ⟨c'', hstep⟩ | ⟨o, hex, hpost⟩
  · exact decompose_none_of_step hstep
  · exact decompose_none_of_exit hex hpost

/-! ## Soundness on the litmus -/

/-- The host `g(n) = n + 1` answers `startIS`'s import in the IR's types. -/
theorem startIG_ok : startIS.HostOk fwdG := fwdG_ok

/-- **Soundness with imports and a start function on `startIS`** (every profile and component
choice profile): every reference behaviour of `get()` under the host `g(n) = n + 1`, after the
start function ran during instantiation, is matched by the IR denotation over `impSemS P`. The
hypothesis `StartNoCall` is discharged by `startIMod_noCall`. -/
theorem startI_sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) :
    ∀ b ∈ exportBehavioursI prof (answerHost P fwdG) () startIS.toRef startIS.imports "get" [],
      IRObsI (startIS.toComp.den (impSemS P)) ⟨1, by decide⟩ [] fwdG b :=
  simpleI_sound_start P prof startIS startIS_good startIS_instS (startIMod_noCall P)
    startIS_floatFree startIS_arity fwdG startIG_ok ⟨1, by decide⟩ [] rfl

/-- **Soundness on `startIS` for `f(x)`**, forwarded to the import after the start function. -/
theorem startI_sound_f (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x : BitVec 32) :
    ∀ b ∈ exportBehavioursI prof (answerHost P fwdG) () startIS.toRef startIS.imports "f"
        [toRefVal (.u32 x)],
      IRObsI (startIS.toComp.den (impSemS P)) ⟨0, by decide⟩ [.u32 x] fwdG b :=
  simpleI_sound_start P prof startIS startIS_good startIS_instS (startIMod_noCall P)
    startIS_floatFree startIS_arity fwdG startIG_ok ⟨0, by decide⟩ [.u32 x] rfl

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
