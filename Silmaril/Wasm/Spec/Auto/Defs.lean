module

public import Silmaril.Wasm.Spec.Live.Defs
public import Silmaril.Wasm.Spec.Multi.Defs
public import Silmaril.Wasm.Spec.Harness.Thms
public import Silmaril.Wasm.Spec.Joint.Wrap.Thms
public import Silmaril.Wasm.Spec.Component.Logic.Thms

@[expose] public section

/-!
# Automation: the property registry

The API a verification service exposes: one inductive type of supported sentence shapes per
fragment, one satisfaction predicate, and a soundness-preserving reduction.

* `ModProp X`: shapes for **Core modules** at a scalar interface `X`: `neverCall`,
  `assertNeverFalse`, `callPre`, `neverCallFrom`, `retPost` (safety, over `wasmSem P`),
  `hist` (multi-call export histories, `Multi.exportHist`), `terminates` (liveness over the
  divergence-observing `wasmDivSem P`, `Live.terminates`), and `ltl`, `ctl`, `tla`
  (divergence-aware temporal sentences, over `wasmDivSem P`), closed under `and`.
* `CompProp X`: shapes for **components** at an interface `X : CIface`: `contract`, `retTyped`,
  `callTyped`, `borrowScoped`, `noUseAfterDrop`, `droppedEventually`, `callPre`, `retPost`,
  `ltl`, closed under `and`; read over any component semantics. The **value-type level** of the
  fragment is that of the interface (`CIface.level`: 0 scalars, 1 aggregates, 2 strings and lists,
  3 handles and async); `ShapeInfo` records it.
* `Task`: a fragment, a program and a property. `module P p φ`; `component S p φ` (any
  component semantics: IR, reference machine, joint); `joint P p φ`, a numeric Core module
  specified by a component property of its wrapping (`wrapSem P`); `linked P W p Th i`: the
  linkage of a module with a harness never calls `assert` `i` with `i32 0`.
* `Task.Holds`: the single satisfaction predicate.
* `Reduces t t'` (`t'` suffices for `t`): `neverCallFrom` to `neverCall`, **harness
  reduction** of a return postcondition to `assertNeverFalse` of the linked system
  (`wasm_harness_iff`), and congruence for `and`. `reduce` is the deterministic normaliser.
* `ShapeInfo`: name, fragment, level, whether liveness, and whether the verifier of
  `Silmaril.Wasm.Verify` can discharge it.

The verifier dispatch is in `Silmaril.Wasm.Spec.Auto.Verify`. A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Auto

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Numerics (Profile)

/-- The `wasm_spec` simp set: satisfaction of the simple logics as trace conditions, and
temporal embeddings of simple sentences back to the simple logics. -/
register_simp_attr wasm_spec

/-! ## Module properties -/

/-- Supported sentence shapes for Core modules at the interface `X`. -/
inductive ModProp (X : WIface) : Type where
  /-- Import `i` is never called. -/
  | neverCall (i : X.Imp)
  /-- The assertion import `i` is never called with `i32 0`. -/
  | assertNeverFalse (i : X.Imp)
  /-- Every call of import `i` satisfies `pre`. -/
  | callPre (i : X.Imp) (pre : List Val → Prop)
  /-- Import `i` is never called while export `e` is active. -/
  | neverCallFrom (i : X.Imp) (e : X.Exp)
  /-- Every return of export `e` satisfies `post`. -/
  | retPost (e : X.Exp) (post : Behaviour Val → Prop)
  /-- Every export history (sequence of calls and returns on one instance) satisfies `Φ`. -/
  | hist (Φ : Multi.Hist (List Val) (Behaviour Val) X → Prop)
  /-- Every call of export `e` returns (liveness, divergence-aware). -/
  | terminates (e : X.Exp)
  /-- An LTL sentence over maximal behaviours, divergence-aware. -/
  | ltl (φ : LTLFm (List Val) (Behaviour Val) X)
  /-- A CTL sentence over the play tree, divergence-aware. -/
  | ctl (φ : CTL (WEvent X))
  /-- A TLA sentence, divergence-aware. -/
  | tla (φ : TLA (WEvent X))
  /-- Both. -/
  | and (φ ψ : ModProp X)

/-- **Satisfaction of a module property** at profile `P`. -/
def ModProp.Satisfies (P : Profile) {X : WIface} (p : WasmProg X) : ModProp X → Prop
  | .neverCall i => Models (Spec.neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) p i
  | .assertNeverFalse i => Models (Spec.assertNeverFalse FnType (Behaviour Val)) (wasmSem P) p i
  | .callPre i pre => Models (Spec.callPre FnType (List Val) (Behaviour Val)) (wasmSem P) p ⟨i, pre⟩
  | .neverCallFrom i e =>
    Models (Spec.neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) p (i, e)
  | .retPost e post =>
    Models (Spec.retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p ⟨e, post⟩
  | .hist Φ => Models (Multi.exportHist FnType (List Val) (Behaviour Val)) (wasmSem P) p Φ
  | .terminates e =>
    Models (Spec.ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p (Live.terminates e)
  | .ltl φ => Models (Spec.ltlMax FnType (List Val) (Behaviour Val)) (wasmDivSem P) p φ
  | .ctl φ => Models (Spec.ctl FnType (List Val) (Behaviour Val)) (wasmDivSem P) p φ
  | .tla φ => Models (Spec.tla FnType (List Val) (Behaviour Val)) (wasmDivSem P) p φ
  | .and φ ψ => ModProp.Satisfies P p φ ∧ ModProp.Satisfies P p ψ

/-- The normaliser of module properties: `neverCallFrom i e` becomes `neverCall i` (sound, not
complete), recursively under `and`. -/
def ModProp.reduce {X : WIface} : ModProp X → ModProp X
  | .neverCallFrom i _ => .neverCall i
  | .and φ ψ => .and φ.reduce ψ.reduce
  | φ => φ

/-! ## Component properties -/

/-- Supported sentence shapes for components at the interface `X`. -/
inductive CompProp (X : CIface) : Type where
  /-- A contract of export `e`. -/
  | contract (e : X.Exp) (pre : List RVal → Prop) (post : List RVal → Outcome → Prop)
  /-- Results of export `e` have its declared types. -/
  | retTyped (e : X.Exp)
  /-- Calls of import `i` have its declared types. -/
  | callTyped (i : X.Imp)
  /-- No export returns a handle it was lent. -/
  | borrowScoped
  /-- No call mentions a handle dropped by export `d`. -/
  | noUseAfterDrop (d : X.Exp)
  /-- Every handle returned by `c` is passed to `d` (on maximal traces). -/
  | droppedEventually (c d : X.Exp)
  /-- Every call of import `i` satisfies `pre`. -/
  | callPre (i : X.Imp) (pre : List RVal → Prop)
  /-- Every return of export `e` satisfies `post`. -/
  | retPost (e : X.Exp) (post : Outcome → Prop)
  /-- An LTL sentence over maximal behaviours. -/
  | ltl (φ : LTLFm (List RVal) Outcome X)
  /-- Both. -/
  | and (φ ψ : CompProp X)

/-- **Satisfaction of a component property** in a component semantics `S`. -/
def CompProp.Satisfies (S : Semantics CFn (List RVal) Outcome) {X : CIface} (p : S.Prog X) :
    CompProp X → Prop
  | .contract e pre post => Models (Spec.contract CFn (List RVal) Outcome) S p ⟨e, pre, post⟩
  | .retTyped e => Models Component.retTyped S p e
  | .callTyped i => Models Component.callTyped S p i
  | .borrowScoped => Models Component.borrowScoped S p ()
  | .noUseAfterDrop d => Models Component.noUseAfterDrop S p d
  | .droppedEventually c d => Models Component.droppedEventually S p (c, d)
  | .callPre i pre => Models (Spec.callPre CFn (List RVal) Outcome) S p ⟨i, pre⟩
  | .retPost e post => Models (Spec.retPost CFn (List RVal) Outcome) S p ⟨e, post⟩
  | .ltl φ => Models (Spec.ltlMax CFn (List RVal) Outcome) S p φ
  | .and φ ψ => CompProp.Satisfies S p φ ∧ CompProp.Satisfies S p ψ

/-! ## Tasks -/

/-- A verification task: a fragment, a program and a property. -/
inductive Task : Type 1 where
  /-- A Core module property at profile `P`. -/
  | module {X : WIface} (P : Profile) (p : WasmProg X) (φ : ModProp X)
  /-- A component property in a component semantics. -/
  | component {X : CIface} (S : Semantics CFn (List RVal) Outcome) (p : S.Prog X) (φ : CompProp X)
  /-- A numeric Core module specified by a component property of its wrapping. -/
  | joint {X : NIface} (P : Profile) (p : (numSem P).Prog X) (φ : CompProp (X.map wrapFn))
  /-- The linkage of a module with a harness (traces `Th`) never calls `assert` `i` with
  `i32 0`. -/
  | linked {Xp Xh Xl : WIface} (P : Profile) (W : Wiring Xp Xh Xl) (p : WasmProg Xp)
      (Th : Set (List (WEvent Xh))) (i : Xl.Imp)

/-- **The single satisfaction predicate of tasks.** -/
def Task.Holds : Task → Prop
  | .module P p φ => φ.Satisfies P p
  | .component S p φ => φ.Satisfies S p
  | .joint P p φ => φ.Satisfies (wrapSem P) (PushProg.ofProg p)
  | .linked P W p Th i =>
    (Spec.assertNeverFalse FnType (Behaviour Val)).Sat (linkTraces W ((wasmSem P).traces p) Th) i

/-- The normaliser of tasks. -/
def Task.reduce : Task → Task
  | .module P p φ => .module P p φ.reduce
  | t => t

/-- One-step reductions between module properties at one program (`φ'` suffices for `φ`). -/
inductive ModReduces {X : WIface} : ModProp X → ModProp X → Prop where
  | refl (φ : ModProp X) : ModReduces φ φ
  | ncf (i : X.Imp) (e : X.Exp) : ModReduces (.neverCallFrom i e) (.neverCall i)
  | and {φ φ' ψ ψ' : ModProp X} : ModReduces φ φ' → ModReduces ψ ψ' →
      ModReduces (.and φ ψ) (.and φ' ψ')

/-- **Reductions between tasks** (`t'` suffices for `t`). -/
inductive Reduces : Task → Task → Prop where
  /-- A module-property reduction. -/
  | module {X : WIface} (P : Profile) (p : WasmProg X) {φ φ' : ModProp X} :
      ModReduces φ φ' → Reduces (.module P p φ) (.module P p φ')
  /-- **Harness reduction**: a return postcondition of a module reduces to `assertNeverFalse`
  of its linkage with the most general return harness. -/
  | harness {Xp Xh Xl : WIface} (P : Profile) {W : Wiring Xp Xh Xl} (p : WasmProg Xp)
      (H : RetHarness W (List Val) (Behaviour Val)) {Q : Behaviour Val → Prop}
      (hQ : H.verdict = assertVerdict Q) (hpl : ∀ k, W.pl k ≠ W.ol H.chk)
      (hol : Function.Injective W.ol) (hph : ∀ j k, W.ph j ≠ W.oh k)
      (hinj : Function.Injective W.ph) :
      Reduces (.module P p (.retPost H.e Q)) (.linked P W p H.traces (W.ol H.chk))
  /-- Transitivity. -/
  | trans {t t' t'' : Task} : Reduces t t' → Reduces t' t'' → Reduces t t''

/-! ## The registry -/

/-- Fragments. -/
inductive Fragment where
  | module | component | joint | linked
  deriving DecidableEq, Repr

/-- What the registry records about a shape. -/
structure ShapeInfo where
  /-- The shape's name. -/
  name : String
  /-- The fragment. -/
  fragment : Fragment
  /-- The value-type level of the interface (`0` for Core modules). -/
  level : ℕ
  /-- Whether the shape is a liveness property (read on maximal behaviours). -/
  liveness : Bool
  /-- Whether the verifier of `Silmaril.Wasm.Verify` can discharge it (after `reduce`). -/
  automatic : Bool
  deriving DecidableEq, Repr

/-- The registry entry of a module property. -/
def ModProp.info {X : WIface} : ModProp X → ShapeInfo
  | .neverCall _ => ⟨"neverCall", .module, 0, false, true⟩
  | .assertNeverFalse _ => ⟨"assertNeverFalse", .module, 0, false, true⟩
  | .callPre _ _ => ⟨"callPre", .module, 0, false, false⟩
  | .neverCallFrom _ _ => ⟨"neverCallFrom", .module, 0, false, true⟩
  | .retPost _ _ => ⟨"retPost", .module, 0, false, false⟩
  | .hist _ => ⟨"hist", .module, 0, false, false⟩
  | .terminates _ => ⟨"terminates", .module, 0, true, false⟩
  | .ltl _ => ⟨"ltl", .module, 0, true, false⟩
  | .ctl _ => ⟨"ctl", .module, 0, true, false⟩
  | .tla _ => ⟨"tla", .module, 0, true, false⟩
  | .and φ ψ => ⟨"and", .module, 0, φ.info.liveness || ψ.info.liveness,
      φ.info.automatic && ψ.info.automatic⟩

/-- The registry entry of a component property (the level is the interface's). -/
def CompProp.info {X : CIface} : CompProp X → ShapeInfo
  | .contract _ _ _ => ⟨"contract", .component, X.level, false, false⟩
  | .retTyped _ => ⟨"retTyped", .component, X.level, false, false⟩
  | .callTyped _ => ⟨"callTyped", .component, X.level, false, false⟩
  | .borrowScoped => ⟨"borrowScoped", .component, X.level, false, false⟩
  | .noUseAfterDrop _ => ⟨"noUseAfterDrop", .component, X.level, false, false⟩
  | .droppedEventually _ _ => ⟨"droppedEventually", .component, X.level, true, false⟩
  | .callPre _ _ => ⟨"callPre", .component, X.level, false, false⟩
  | .retPost _ _ => ⟨"retPost", .component, X.level, false, false⟩
  | .ltl _ => ⟨"ltl", .component, X.level, true, false⟩
  | .and φ ψ => ⟨"and", .component, X.level, φ.info.liveness || ψ.info.liveness, false⟩

/-- The registry entry of a task. -/
def Task.info : Task → ShapeInfo
  | .module _ _ φ => φ.info
  | .component _ _ φ => φ.info
  | .joint _ _ φ => { φ.info with fragment := .joint }
  | .linked .. => ⟨"assertNeverFalse", .linked, 0, false, false⟩

end Silmaril.Wasm.Spec.Auto
