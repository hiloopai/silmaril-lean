module

public import Silmaril.Wasm.Spec.Maps.Defs
public import Silmaril.Wasm.Execution.Core.Runtime

@[expose] public section

/-!
# The simple specification logics

Small logics in the trace-institution format (`Silmaril.Wasm.Spec.Format`), each a per-trace
property (`Logic.ofTrace`), generic in the argument and result payloads `A`, `R`:

| logic | formula at `X` | a trace satisfies it when |
|---|---|---|
| `neverCall` | an import `i` | import `i` is never called |
| `callPre` | an import `i` and `P : A → Prop` | every call of `i` has arguments satisfying `P` |
| `neverCallFrom` | an import `i` and an export `e` | `i` is never called while `e` is active |
| `retPost` | an export `j` and `Q : R → Prop` | every return of `j` satisfies `Q` |
| `assertNeverFalse` (Wasm, `A = List Val`) | an import `i` (the assert) | `i` is never called with first argument `i32 0` |

"While `e` is active" is read off the trace: `activeExport h` is the export whose call is
pending after the history `h` (plays are single-threaded and well bracketed, so every import call
belongs to the innermost pending export call). Under the Wasm semantics this is "on a path
reachable from export `e`": the import is called during an activation of `e`.

`basic` is the sum of the four generic logics; `NeverCall.toCallPre` and
`AssertNeverFalse.toCallPre` are logic maps (comorphisms) into `callPre`.

`Semantics.ofSets` is the loose trace semantics: a program is any good trace set. It is used
for litmus tests and is the semantics in which a specification is about *all* possible behaviours.
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-! ## Positions in traces -/

/-- `P` holds at every position of the trace: of each event, given the history before it. -/
def EveryPos {α : Type} (P : List α → α → Prop) (t : List α) : Prop :=
  ∀ h e r, t = h ++ e :: r → P h e

/-- `EveryPos` is inherited by prefixes. -/
theorem EveryPos.of_prefix {α : Type} {P : List α → α → Prop} {s t : List α} (ht : EveryPos P t)
    (hs : s <+: t) : EveryPos P s := by
  obtain ⟨u, rfl⟩ := hs
  intro h e r hr
  exact ht h e (r ++ u) (by rw [hr]; simp)

/-- How an event changes the pending export call. -/
def activeStep {X : Iface Ty} : Option X.Exp → Event A R X → Option X.Exp
  | _, .inr (.ask j _) => some j
  | _, .inr (.ans _ _) => none
  | o, .inl _ => o

/-- The export whose call is pending after a history (single-threaded plays). -/
def activeExport {X : Iface Ty} (h : List (Event A R X)) : Option X.Exp :=
  h.foldl activeStep none

/-! ## The logics -/

/-- "Import `i` is never called." -/
def NeverCall.holds {X : Iface Ty} (i : X.Imp) (t : List (Event A R X)) : Prop :=
  ∀ a, Event.icall i a ∉ t

/-- The logic of `NeverCall`. -/
abbrev neverCall (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (fun X => X.Imp) NeverCall.holds

/-- A call precondition: an import and a predicate on its arguments. -/
structure CallPre.Fm {Ty : Type} (A : Type) (X : Iface Ty) where
  /-- The import. -/
  imp : X.Imp
  /-- The precondition on its arguments. -/
  pre : A → Prop

/-- "Every call of the import has arguments satisfying the precondition." -/
def CallPre.holds {X : Iface Ty} (φ : CallPre.Fm A X) (t : List (Event A R X)) : Prop :=
  ∀ a, Event.icall φ.imp a ∈ t → φ.pre a

/-- The logic of call preconditions. -/
abbrev callPre (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (CallPre.Fm A) CallPre.holds

/-- "Import `i` is never called while export `e` is active." -/
def NeverCallFrom.holds {X : Iface Ty} (φ : X.Imp × X.Exp) (t : List (Event A R X)) : Prop :=
  EveryPos (fun h ev => ∀ a, ev = Event.icall φ.1 a → activeExport h ≠ some φ.2) t

/-- The logic of `NeverCallFrom`. -/
abbrev neverCallFrom (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (fun X => X.Imp × X.Exp) NeverCallFrom.holds

/-- A return postcondition: an export and a predicate on its results. -/
structure RetPost.Fm {Ty : Type} (R : Type) (X : Iface Ty) where
  /-- The export. -/
  exp : X.Exp
  /-- The postcondition on its results. -/
  post : R → Prop

/-- "Every return of the export satisfies the postcondition." -/
def RetPost.holds {X : Iface Ty} (φ : RetPost.Fm R X) (t : List (Event A R X)) : Prop :=
  ∀ r, Event.ret φ.exp r ∈ t → φ.post r

/-- The logic of return postconditions. -/
abbrev retPost (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (RetPost.Fm R) RetPost.holds

/-- The four simple logics, joined. -/
def basic (Ty A R : Type) : Logic Ty A R :=
  (((neverCall Ty A R).sum (callPre Ty A R)).sum (neverCallFrom Ty A R)).sum (retPost Ty A R)

/-! ## Assertions in Wasm -/

open Silmaril.Wasm.Execution.Core in
/-- An `assert` call is allowed unless its first argument is `i32 0`. -/
def assertOk (args : List Val) : Prop := args.head? ≠ some (Val.i32 0)

/-- "The assert import `i` is never called with first argument `i32 0`." -/
def AssertNeverFalse.holds {X : Iface Ty} (i : X.Imp)
    (t : List (Event (List Silmaril.Wasm.Execution.Core.Val) R X)) : Prop :=
  ∀ a, Event.icall i a ∈ t → assertOk a

/-- **The assertion logic**: formulas name the assert import. -/
abbrev assertNeverFalse (Ty R : Type) : Logic Ty (List Silmaril.Wasm.Execution.Core.Val) R :=
  Logic.ofTrace (fun X => X.Imp) AssertNeverFalse.holds

/-! ## Logic maps -/

/-- "Never called" is the call precondition `False`. -/
def NeverCall.toCallPre (Ty A R : Type) : LogicMap (neverCall Ty A R) (callPre Ty A R) :=
  LogicMap.ofTrace (fun i => ⟨i, fun _ => False⟩) fun _ _ => Iff.rfl

/-- "Assert never false" is the call precondition `assertOk`. -/
def AssertNeverFalse.toCallPre (Ty R : Type) :
    LogicMap (assertNeverFalse Ty R) (callPre Ty (List Silmaril.Wasm.Execution.Core.Val) R) :=
  LogicMap.ofTrace (fun i => ⟨i, assertOk⟩) fun _ _ => Iff.rfl

/-! ## The loose trace semantics -/

/-- Programs are arbitrary good trace sets. -/
abbrev Semantics.ofSets (Ty A R : Type) : Semantics Ty A R where
  Prog X := {T : Set (List (Event A R X)) // Good T}
  traces p := p.1
  good p := p.2

/-- The prefixes of a list. -/
def prefixesOf {α : Type} (l : List α) : Set (List α) := {s | s <+: l}

/-- The prefixes of a list form a good set. -/
theorem prefixesOf_good {α : Type} (l : List α) : Good (prefixesOf l) :=
  ⟨List.nil_prefix, fun ht hs => hs.trans ht⟩

end Silmaril.Wasm.Spec
