module

public import Silmaril.Wasm.Spec.Component.Defs
public import Silmaril.Wasm.Spec.Embed.Defs

@[expose] public section

/-!
# Component-specific specification logics

Logics in the trace-institution format that are natural for components. The first is generic in
the payloads; the others are over component events (`CEvent X`, reference values and outcomes).

| logic | formula at `X` | a trace satisfies it when |
|---|---|---|
| `contract` | export `j`, `pre : A → Prop`, `post : A → R → Prop` | every return `r` of `j` whose pending call had arguments `a` with `pre a` has `post a r` |
| `retTyped` | export `j` | every returned value list of `j` has the result types of `j` (in `X`) |
| `callTyped` | import `i` | every call of `i` has arguments of the parameter types of `i` |
| `borrowScoped` | `Unit` | no export returns a handle whose representation it was lent (`borrow`) by its pending call |
| `noUseAfterDrop` | export `d` (the destructor) | after `d` is called with `own r`, no later call passes `r` |
| `droppedEventually` | exports `c`, `d` | on maximal traces, every `own r` returned by `c` is later passed to `d` |

Types live in the signature, so the typing logics need no type annotations in formulas: a
component specification can say "the results are well-typed" by naming an export (contrast
the scalar Core logics, whose payloads are untyped lists of Core values).

The handle protocols read the handles off the reference values (`valHandles`: `(true, r)` for
`own r`, `(false, r)` for `borrow r`, through records, lists and variants). `borrowScoped` and
`noUseAfterDrop` are safety properties and action invariants (`BorrowScoped.toAct`,
`NoUseAfterDrop.toAct`, `Contract.toAct` into the logic `act` of `Silmaril.Wasm.Spec.Temporal`, and
from there into LTL/CTL/TLA via `Silmaril.Wasm.Spec.Embed`). `droppedEventually` is a liveness
property, read on maximal finite traces (`Logic.ofMaximal`); strategies that keep accepting
calls have no maximal finite traces, so it is meaningful for harnessed or closed systems.

`pendingCall h`: the export call pending after history `h`, with its arguments (export calls do
not nest in single-threaded plays: Opponent asks only at idle positions).
-/

namespace Silmaril.Wasm.Spec

variable {Ty A R : Type}

/-! ## The pending export call -/

/-- How an event changes the pending export call. -/
def callStep {X : Iface Ty} : Option (X.Exp × A) → Event A R X → Option (X.Exp × A)
  | _, .inr (.ask j a) => some (j, a)
  | _, .inr (.ans _ _) => none
  | o, .inl _ => o

/-- The pending export call, with its arguments, after a history. -/
def pendingCall {X : Iface Ty} (h : List (Event A R X)) : Option (X.Exp × A) :=
  h.foldl callStep none

/-! ## Contracts -/

/-- A contract of an export: a precondition on arguments and a postcondition relating
arguments and result. -/
structure Contract.Fm {Ty : Type} (A R : Type) (X : Iface Ty) where
  /-- The export. -/
  exp : X.Exp
  /-- The precondition. -/
  pre : A → Prop
  /-- The postcondition. -/
  post : A → R → Prop

/-- The position predicate of a contract. -/
def Contract.pos {X : Iface Ty} (φ : Contract.Fm A R X) : PosPred A R X :=
  fun h e => ∀ r, e = Event.ret φ.exp r → ∀ a, pendingCall h = some (φ.exp, a) → φ.pre a →
    φ.post a r

/-- **The logic of contracts.** -/
abbrev contract (Ty A R : Type) : Logic Ty A R :=
  Logic.ofTrace (Contract.Fm A R) fun φ t => EveryPos (Contract.pos φ) t

/-- A contract as an action invariant. -/
def Contract.toAct (Ty A R : Type) : LogicMap (contract Ty A R) (act Ty A R) :=
  LogicMap.ofTrace Contract.pos fun _ _ => Iff.rfl

/-- Per-trace properties read on the maximal finite traces of a trace set (liveness on finished
behaviours). -/
abbrev Logic.ofMaximal (Fm : Iface Ty → Type)
    (holds : ∀ {X : Iface Ty}, Fm X → List (Event A R X) → Prop) : Logic Ty A R where
  Fm := Fm
  Sat T φ := ∀ t, Maximal T t → holds φ t

end Silmaril.Wasm.Spec

namespace Silmaril.Wasm.Spec.Component

open Silmaril.Wasm.Component.Value (Val)

/-! ## Typing logics -/

/-- "Every returned value list of export `j` has the result types of `j`." -/
def RetTyped.holds {X : CIface} (j : X.Exp) (t : List (CEvent X)) : Prop :=
  ∀ rs, Event.ret j (.returns (some rs)) ∈ t → Typed (X.exports.get j).results rs

/-- **The logic of well-typed results.** -/
abbrev retTyped : Logic CFn (List RVal) Outcome :=
  Logic.ofTrace (fun X => X.Exp) RetTyped.holds

/-- "Every call of import `i` has arguments of the parameter types of `i`." -/
def CallTyped.holds {X : CIface} (i : X.Imp) (t : List (CEvent X)) : Prop :=
  ∀ a, Event.icall i a ∈ t → Typed (X.imports.get i).params a

/-- **The logic of well-typed import calls.** -/
abbrev callTyped : Logic CFn (List RVal) Outcome :=
  Logic.ofTrace (fun X => X.Imp) CallTyped.holds

/-- Well-typed import calls are a call precondition. -/
def CallTyped.toCallPre : LogicMap callTyped (callPre CFn (List RVal) Outcome) where
  fm {X} i := ⟨i, Typed (X.imports.get i).params⟩
  sat_fm _ _ _ := Iff.rfl

/-! ## Handles in values -/

mutual
/-- The handles in a value: `(true, r)` for `own r`, `(false, r)` for `borrow r`. -/
def valHandles : RVal → List (Bool × ℕ)
  | .own r => [(true, r)]
  | .borrow r => [(false, r)]
  | .list vs => valsHandles vs
  | .record vs => valsHandles vs
  | .variant _ p => optHandles p
  | _ => []

/-- The handles in a list of values. -/
def valsHandles : List RVal → List (Bool × ℕ)
  | [] => []
  | v :: vs => valHandles v ++ valsHandles vs

/-- The handles in an optional value. -/
def optHandles : Option RVal → List (Bool × ℕ)
  | none => []
  | some v => valHandles v
end

/-- The representations mentioned by a list of values, owned or borrowed. -/
def valsReps (vs : List RVal) : List ℕ := (valsHandles vs).map Prod.snd

/-! ## Handle protocols -/

/-- The position predicate of `borrowScoped`: a return does not mention a representation that
its pending call lent. -/
def BorrowScoped.pos {X : CIface} : PosPred (List RVal) Outcome X :=
  fun h e => ∀ j rs, e = Event.ret j (.returns (some rs)) → ∀ a, pendingCall h = some (j, a) →
    ∀ r, (false, r) ∈ valsHandles a → r ∉ valsReps rs

/-- **The logic of scoped borrows**: no export returns a handle it was only lent. -/
abbrev borrowScoped : Logic CFn (List RVal) Outcome :=
  Logic.ofTrace (fun _ => Unit) fun _ t => EveryPos BorrowScoped.pos t

/-- Scoped borrows as an action invariant. -/
def BorrowScoped.toAct : LogicMap borrowScoped (act CFn (List RVal) Outcome) :=
  LogicMap.ofTrace (fun _ => BorrowScoped.pos) fun _ _ => Iff.rfl

/-- The position predicate of `noUseAfterDrop d`: a call does not mention a representation
owned by an earlier call of `d`. -/
def NoUseAfterDrop.pos {X : CIface} (d : X.Exp) : PosPred (List RVal) Outcome X :=
  fun h e => ∀ j a, e = Event.call j a → ∀ a₀, Event.call d a₀ ∈ h →
    ∀ r, (true, r) ∈ valsHandles a₀ → r ∉ valsReps a

/-- **The logic of "no use after drop"**: formulas name the destructor export. -/
abbrev noUseAfterDrop : Logic CFn (List RVal) Outcome :=
  Logic.ofTrace (fun X => X.Exp) fun d t => EveryPos (NoUseAfterDrop.pos d) t

/-- "No use after drop" as an action invariant. -/
def NoUseAfterDrop.toAct : LogicMap noUseAfterDrop (act CFn (List RVal) Outcome) :=
  LogicMap.ofTrace NoUseAfterDrop.pos fun _ _ => Iff.rfl


/-- "Every `own r` returned by `c` is later passed to `d`." -/
def DroppedEventually.holds {X : CIface} (φ : X.Exp × X.Exp) (t : List (CEvent X)) : Prop :=
  ∀ k (hk : k < t.length) rs, t[k] = Event.ret φ.1 (.returns (some rs)) →
    ∀ r, (true, r) ∈ valsHandles rs → ∃ a, Event.call φ.2 a ∈ t.drop (k + 1) ∧ r ∈ valsReps a

/-- **The logic of "drop after use"** (liveness, on maximal traces): formulas name a
constructor and a destructor. -/
abbrev droppedEventually : Logic CFn (List RVal) Outcome :=
  Logic.ofMaximal (fun X => X.Exp × X.Exp) DroppedEventually.holds

end Silmaril.Wasm.Spec.Component
