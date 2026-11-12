module

public import Silmaril.Machine.Behaviour.Outcome
public import Mathlib.Logic.Equiv.Defs

/-!
# Observables: an event trace and the way a run ends

`Outcome R T F` (`Silmaril/Machine/Behaviour/Outcome.lean`) is the result of one
run of a *function*: it carries no trace and no process exit. This file adds
the observable of a run in general, without changing `Outcome`:

* `Ending V X T F`: how a run ends. It returns a value in `V`, exits the
  process with a code in `X`, aborts with a payload in `T` (a trap, a signal,
  `abort()`), faults with a payload in `F`, reaches undefined behaviour, runs
  out of a resource the specification does not bound, or diverges;
* `Observable E V X T F`: a finite trace of events in `E` followed by an
  `Ending`. `⟨t, .diverges⟩` is silent divergence after the events `t`;
  `⟨t, .undefined⟩` is undefined behaviour after `t`.

Every behaviour and observation type of the repository embeds in one
instance; the embeddings and the proofs that they lose nothing are in
`Silmaril/Machine/Behaviour/Adapters/`. The
function-level `Outcome R T F` is the trace-free instance with no process exit
(`Ending.outcomeEquiv : Ending R Empty T F ≃ Outcome R T F`).

## Signature morphisms

An observable is functorial in its five parameters. Event maps go to *lists*
of events (`E → List E'`), so that a projection such as "the bytes a system
call wrote" (`Process.Syscall.Event.output`) and a renaming are both trace
maps. `Observable.map` preserves trace prefixes (`map_trace_prefix`), which is
what makes refinement transport along it (`Observable.Refines.map`).

## Not modelled

Infinite traces of events (reactive divergence) are not observables here: a
run that emits infinitely many events is observed through its finite
prefixes followed by `diverges`. Statements that need the infinite trace
itself (liveness of output) are out of scope of this core.
-/

@[expose] public section

open Silmaril.Machine.Behaviour

namespace Silmaril.Machine.Behaviour

universe uE uV uX uT uF uE' uV' uX' uT' uF'

/-- How a run ends. `exited` is a process exit; `returned` is a function
return. `aborted` carries a payload (a trap code, a signal number). -/
inductive Ending (V : Type uV) (X : Type uX) (T : Type uT) (F : Type uF) where
  | returned (v : V)
  | exited (x : X)
  | aborted (t : T)
  | faulted (f : F)
  | undefined
  | exhausted
  | diverges
  deriving DecidableEq, Repr

/-- What one run shows: the events it emitted and how it ended. -/
structure Observable (E : Type uE) (V : Type uV) (X : Type uX) (T : Type uT) (F : Type uF) where
  trace : List E
  ending : Ending V X T F
  deriving DecidableEq, Repr

namespace Ending

variable {V : Type uV} {X : Type uX} {T : Type uT} {F : Type uF}
variable {V' : Type uV'} {X' : Type uX'} {T' : Type uT'} {F' : Type uF'}

/-- Rename the payloads of an ending. -/
def map (fv : V → V') (fx : X → X') (ft : T → T') (ff : F → F') :
    Ending V X T F → Ending V' X' T' F'
  | .returned v => .returned (fv v)
  | .exited x => .exited (fx x)
  | .aborted t => .aborted (ft t)
  | .faulted f => .faulted (ff f)
  | .undefined => .undefined
  | .exhausted => .exhausted
  | .diverges => .diverges

@[simp] theorem map_id (e : Ending V X T F) : e.map id id id id = e := by
  cases e <;> rfl

theorem map_comp {V'' X'' T'' F'' : Type*} (fv : V → V') (fx : X → X') (ft : T → T')
    (ff : F → F') (gv : V' → V'') (gx : X' → X'') (gt : T' → T'') (gf : F' → F'')
    (e : Ending V X T F) :
    (e.map fv fx ft ff).map gv gx gt gf = e.map (gv ∘ fv) (gx ∘ fx) (gt ∘ ft) (gf ∘ ff) := by
  cases e <;> rfl

@[simp] theorem map_eq_undefined {fv : V → V'} {fx : X → X'} {ft : T → T'} {ff : F → F'}
    {e : Ending V X T F} : e.map fv fx ft ff = .undefined ↔ e = .undefined := by
  cases e <;> simp [map]

@[simp] theorem map_eq_exhausted {fv : V → V'} {fx : X → X'} {ft : T → T'} {ff : F → F'}
    {e : Ending V X T F} : e.map fv fx ft ff = .exhausted ↔ e = .exhausted := by
  cases e <;> simp [map]

theorem map_injective {fv : V → V'} {fx : X → X'} {ft : T → T'} {ff : F → F'}
    (hv : Function.Injective fv) (hx : Function.Injective fx) (ht : Function.Injective ft)
    (hf : Function.Injective ff) : Function.Injective (map (X := X) fv fx ft ff) := by
  intro a b h
  cases a <;> cases b <;> simp_all [map, hv.eq_iff, hx.eq_iff, ht.eq_iff, hf.eq_iff]

/-! ## The function-level `Outcome` is the trace-free, exit-free instance -/

/-- A function outcome as an ending. `trapped` becomes `aborted`. -/
def ofOutcome {R : Type uV} {T : Type uT} {F : Type uF} :
    Outcome R T F → Ending R Empty T F
  | .returned r => .returned r
  | .trapped t => .aborted t
  | .faulted f => .faulted f
  | .undefined => .undefined
  | .exhausted => .exhausted
  | .diverges => .diverges

/-- An exit-free ending as a function outcome. -/
def toOutcome {R : Type uV} {T : Type uT} {F : Type uF} :
    Ending R Empty T F → Outcome R T F
  | .returned r => .returned r
  | .exited x => x.elim
  | .aborted t => .trapped t
  | .faulted f => .faulted f
  | .undefined => .undefined
  | .exhausted => .exhausted
  | .diverges => .diverges

/-- `Outcome` is exactly the exit-free `Ending`. -/
def outcomeEquiv {R : Type uV} {T : Type uT} {F : Type uF} :
    Ending R Empty T F ≃ Outcome R T F where
  toFun := toOutcome
  invFun := ofOutcome
  left_inv e := by cases e <;> first | rfl | exact (by assumption : Empty).elim
  right_inv o := by cases o <;> rfl

@[simp] theorem toOutcome_ofOutcome {R : Type uV} {T : Type uT} {F : Type uF}
    (o : Outcome R T F) : toOutcome (ofOutcome o) = o :=
  outcomeEquiv.right_inv o

@[simp] theorem ofOutcome_toOutcome {R : Type uV} {T : Type uT} {F : Type uF}
    (e : Ending R Empty T F) : ofOutcome (toOutcome e) = e :=
  outcomeEquiv.left_inv e

@[simp] theorem toOutcome_eq_diverges {R : Type uV} {T : Type uT} {F : Type uF}
    {e : Ending R Empty T F} : e.toOutcome = .diverges ↔ e = .diverges := by
  cases e <;> first | exact (by assumption : Empty).elim | simp [toOutcome]

@[simp] theorem toOutcome_eq_undefined {R : Type uV} {T : Type uT} {F : Type uF}
    {e : Ending R Empty T F} : e.toOutcome = .undefined ↔ e = .undefined := by
  cases e <;> first | exact (by assumption : Empty).elim | simp [toOutcome]

@[simp] theorem toOutcome_eq_exhausted {R : Type uV} {T : Type uT} {F : Type uF}
    {e : Ending R Empty T F} : e.toOutcome = .exhausted ↔ e = .exhausted := by
  cases e <;> first | exact (by assumption : Empty).elim | simp [toOutcome]

theorem ofOutcome_injective {R : Type uV} {T : Type uT} {F : Type uF} :
    Function.Injective (ofOutcome (R := R) (T := T) (F := F)) :=
  outcomeEquiv.symm.injective

@[simp] theorem ofOutcome_eq_undefined {R : Type uV} {T : Type uT} {F : Type uF}
    {o : Outcome R T F} : ofOutcome o = .undefined ↔ o = .undefined := by
  cases o <;> simp [ofOutcome]

@[simp] theorem ofOutcome_eq_exhausted {R : Type uV} {T : Type uT} {F : Type uF}
    {o : Outcome R T F} : ofOutcome o = .exhausted ↔ o = .exhausted := by
  cases o <;> simp [ofOutcome]

end Ending

namespace Observable

variable {E : Type uE} {V : Type uV} {X : Type uX} {T : Type uT} {F : Type uF}
variable {E' : Type uE'} {V' : Type uV'} {X' : Type uX'} {T' : Type uT'} {F' : Type uF'}

/-- A trace-free observable. -/
def ofEnding (e : Ending V X T F) : Observable E V X T F := ⟨[], e⟩

@[simp] theorem ofEnding_trace (e : Ending V X T F) : (ofEnding e : Observable E V X T F).trace = [] :=
  rfl

@[simp] theorem ofEnding_ending (e : Ending V X T F) :
    (ofEnding e : Observable E V X T F).ending = e := rfl

theorem ofEnding_injective : Function.Injective (ofEnding : Ending V X T F → Observable E V X T F) :=
  fun _ _ h => congrArg Observable.ending h

/-- Undefined behaviour after the events `t`. -/
def undefinedAfter (t : List E) : Observable E V X T F := ⟨t, .undefined⟩

/-- A function outcome as a trace-free observable. -/
def ofOutcome {R : Type uV} {T : Type uT} {F : Type uF} (o : Outcome R T F) :
    Observable E R Empty T F :=
  ofEnding (Ending.ofOutcome o)

theorem ofOutcome_injective {R : Type uV} {T : Type uT} {F : Type uF} :
    Function.Injective (ofOutcome : Outcome R T F → Observable E R Empty T F) :=
  ofEnding_injective.comp Ending.ofOutcome_injective

/-- Map an observable along a signature morphism: each event becomes a list of
events, and the payloads are renamed. -/
def map (fe : E → List E') (fv : V → V') (fx : X → X') (ft : T → T') (ff : F → F')
    (o : Observable E V X T F) : Observable E' V' X' T' F' :=
  ⟨o.trace.flatMap fe, o.ending.map fv fx ft ff⟩

/-- Rename only the events, one for one. -/
def mapEvents (fe : E → E') (o : Observable E V X T F) : Observable E' V X T F :=
  ⟨o.trace.map fe, o.ending⟩

theorem mapEvents_eq_map (fe : E → E') (o : Observable E V X T F) :
    o.mapEvents fe = o.map (fun e => [fe e]) id id id id := by
  obtain ⟨t, e⟩ := o
  simp only [mapEvents, map, Ending.map_id, mk.injEq, and_true]
  induction t with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem map_trace_prefix (fe : E → List E') {t t' : List E} (h : t <+: t') :
    t.flatMap fe <+: t'.flatMap fe := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u.flatMap fe, (List.flatMap_append ..).symm⟩

end Observable

end Silmaril.Machine.Behaviour
