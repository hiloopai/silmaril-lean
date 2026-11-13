module

public import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Effects

/-!
# The entry check of core callouts

In REF (`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>,
"REF"), core code leaves its component instance only through the canon definitions of that
instance, and every such exit checks the current instance:
* `Store.lower`'s `core_func_inst` asserts `inst is current_instance()` (L548) and then calls
  `canon_lower`, which begins with `trap_if(not thread.task.inst.may_leave)` (L2170-2171);
* every built-in except `canon_resource_rep` (L2267), `canon_context_get` / `canon_context_set`
  (L2275, L2285) and `canon_backpressure_inc` / `canon_backpressure_dec` (L2295, L2302) begins
  with `trap_if(not inst.may_leave)` on `current_instance()`.

The machine runs a core callout `callout h args` (rule `Machine.Step.coreCallout`) as the
dispatched program `Canon.hostCalloutProg`, which first evaluates the entry check
`calloutEntry s th h` of this file on the current store `s` and thread `th` and traps with its
answer before any canon code runs (`withCalloutEntry`, which test dispatchers that override a
callout reuse):

| Lean | REF |
| --- | --- |
| `instOfThread? s th` | `current_instance()` of thread `th` (`current_thread().task.inst`) |
| `instMayLeave s i` | `inst.may_leave` (`true` for an unallocated id, the default of L203) |
| `threadMayLeave s th` | `current_instance().may_leave` (`true` on a host frame) |
| `ResolvedBuiltin.checksMayLeave b` | the built-in begins with `trap_if(not inst.may_leave)` |
| `CanonHost.inst? h` | the instance whose canon definition `h` is |
| `calloutEntry s th h` | the checks a callout makes before its canon code runs |
| `confine p` | an embedder import called while the current instance may not leave |

`calloutEntry s th h` is `some r` when the callout traps with `r`, in REF's order:
* `lowered callee ft opts inst`: called from a thread of `inst`, no trap here (`canon_lower`
  itself checks `inst.may_leave`, L2171). Called from a thread of another instance, or from a
  host frame (no current instance), it traps `internal`: `Store.lower`'s assert (L548) comes
  before `canon_lower`'s `may_leave` check, so REF never reads the flag in that case.
* `builtin b bi`: called from a thread of `bi`, no trap. Called from a thread of another
  instance `i`, no trap if `b` checks `may_leave` and `i.may_leave` is clear (the built-in then
  traps `cannotLeave` itself, first, as REF's `trap_if(not inst.may_leave)` on
  `current_instance()` does); otherwise `internal`. This check has no REF counterpart: REF
  built-ins carry no instance and act on `current_instance()`, and a canon built-in is only
  reachable from core code of the component instance that defined it (Explainer.md "Canonical
  Definitions"). Called from a host frame (no current instance), it traps `internal`.
* `embedder name ft`: no trap. An embedder import is a core-level import the host supplies
  (test harnesses only; REF has no such import, and `run_tests.py` writes the corresponding core
  functions in Python). While the current instance may not leave, its host program runs
  `confine`d: it may read the store, the host state and the current thread, write the host
  state, choose, emit free-form test notes (`HostObs.note`) and trap; its first other operation
  (a store update, a call, a core call, a thread operation, or an observation that the machine
  acts on: `started`, `resolved`, `received`) traps `cannotLeave`. This is a restriction of the
  test harness and is stricter than REF's Python core functions, which may update their own
  memory while `may_leave` is clear (run_tests `core_consumer_realloc` copies bytes with
  `Heap.realloc` while `assert(not consumer_inst.may_leave)` holds): such a function ported as
  an embedder import traps.

When the current instance of the calling thread is the defining instance of every lowered
function and built-in that core code calls (`calloutEntry_of_local`), the `internal` answers are
never taken. That every reachable callout of a validated component has this property is not
proved here, and it does not follow from the engine laws: a lawful engine whose core instances
export an address they did not import reaches, from the empty store and for valid components, a
callout to another instance's `canon lower` (`Theorems.Fidelity.Cex.calloutLocal_fails_validated`).
It is a property of the core engine (core instances export only their own functions and their
imports) together with instantiation.

Proved here: invariant preservation and the operation shape of `confine` (`confine_every`,
`Prog.Every.confine`), and the cases of `calloutEntry`. Machine-level consequences are in
`Theorems/MayLeave.lean` and `Theorems/Fidelity.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

variable {E : CoreEngine}

end Silmaril.Wasm.Component.Runtime

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

theorem confine_op {α : Type} (o : Op E σ) (k : (Eff E σ).Resp o → P E σ α) :
    confine (.op (S := Eff E σ) o k) =
      if Op.observes o then .op o fun r => confine (k r) else trap .cannotLeave := rfl

/-- **Confinement keeps program properties**: if every operation of `p` satisfies `Q`, so does
every operation of `confine p`, provided the trap `cannotLeave` does. -/
theorem Prog.Every.confine {α : Type} {Q : Op E σ → Prop} {p : P E σ α}
    (hp : Prog.Every (S := Eff E σ) Q p) (ht : Q (.trap .cannotLeave)) :
    Prog.Every (S := Eff E σ) Q (Canon.confine p) := by
  induction hp with
  | pure a => exact Prog.Every.pure a
  | @op o k ho _ ih =>
    dsimp only [Canon.confine]
    split
    · exact Prog.Every.op ho ih
    · exact Prog.Every.op ht fun e => nomatch e

/-- Confined code records no observation that the machine acts on: it emits only free-form
test notes (in particular no `resolved`, which would record the result of a top-level call). -/
theorem confine_emits_note {α : Type} (p : P E σ α) :
    Prog.Every (S := Eff E σ) (fun o => ∀ x, o = .emit x → ∃ tag vs, x = .note tag vs)
      (confine p) :=
  confine_every (fun o ho x hx => by
    subst hx
    cases x with
    | note tag vs => exact ⟨tag, vs, rfl⟩
    | _ => simp [Op.observes] at ho) p

/-! ## The cases of the entry check -/

theorem calloutEntry_lowered_eq_none {s : CStore E} {th : Option ThreadId} {f : FuncId}
    {ft : WIT.FuncType Empty RtId} {o : CanonOpts E} {i : InstId} :
    calloutEntry s th (.lowered f ft o i) = none ↔ instOfThread? s th = some i := by
  unfold calloutEntry
  cases instOfThread? s th with
  | none => simp
  | some j =>
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]

/-- A lowered callout from a thread of another instance, or from a host frame, traps `internal`
(REF `Store.lower`'s `assert(inst is current_instance())`, L548). -/
theorem calloutEntry_lowered_internal {s : CStore E} {th : Option ThreadId} {f : FuncId}
    {ft : WIT.FuncType Empty RtId} {o : CanonOpts E} {i : InstId}
    (hne : instOfThread? s th ≠ some i) :
    ∃ msg, calloutEntry s th (.lowered f ft o i) = some (.internal msg) := by
  unfold calloutEntry
  cases hj : instOfThread? s th with
  | none => exact ⟨_, rfl⟩
  | some j =>
    have : j ≠ i := fun e => hne (e ▸ hj)
    exact ⟨"Store.lower: inst is not current_instance()", by simp [this]⟩

theorem calloutEntry_builtin_eq_none {s : CStore E} {th : Option ThreadId}
    {b : ResolvedBuiltin E} {bi : InstId} :
    calloutEntry s th (.builtin b bi) = none ↔
      ∃ i, instOfThread? s th = some i ∧
        (i = bi ∨ (b.checksMayLeave = true ∧ instMayLeave s i = false)) := by
  unfold calloutEntry
  cases instOfThread? s th with
  | none => simp
  | some j =>
    by_cases hj : j = bi ∨ (b.checksMayLeave = true ∧ instMayLeave s j = false)
    · simp [hj]
    · simp [hj]

/-- **A passed entry check is local**: a callout to a canon definition of instance `i` that
passes its entry check runs on a thread of `i`, or is a built-in that checks `may_leave` called
from a thread whose instance may not leave (which then traps `cannotLeave`,
`Theorems.builtinProg_traps_cannotLeave`). -/
theorem calloutEntry_none_local {s : CStore E} {th : Option ThreadId} {h : CanonHost E}
    {i : InstId} (he : calloutEntry s th h = none) (hi : CanonHost.inst? h = some i) :
    instOfThread? s th = some i ∨
      ∃ b j, h = .builtin b i ∧ b.checksMayLeave = true ∧ instOfThread? s th = some j ∧
        instMayLeave s j = false := by
  cases h with
  | lowered f ft o inst =>
    cases hi
    exact .inl (calloutEntry_lowered_eq_none.mp he)
  | builtin b bi =>
    cases hi
    obtain ⟨j, hj, hj'⟩ := calloutEntry_builtin_eq_none.mp he
    rcases hj' with rfl | ⟨hb, hml⟩
    · exact .inl hj
    · exact .inr ⟨b, j, rfl, hb, hj, hml⟩
  | embedder n ft => cases hi

/-- **No over-trapping on local callouts**: a callout whose calling thread belongs to the
defining instance of the callee (every callout of an embedder import) passes its entry check. -/
theorem calloutEntry_of_local {s : CStore E} {th : Option ThreadId} {h : CanonHost E}
    (hl : ∀ i, CanonHost.inst? h = some i → instOfThread? s th = some i) :
    calloutEntry s th h = none := by
  cases h with
  | lowered f ft o inst => exact calloutEntry_lowered_eq_none.mpr (hl inst rfl)
  | builtin b bi => exact calloutEntry_builtin_eq_none.mpr ⟨bi, hl bi rfl, .inl rfl⟩
  | embedder n ft => rfl

/-! ## Examples -/

section Examples

/-- A program that updates the store traps `cannotLeave` when confined, before the update. -/
example (f : CStore E → CStore E) :
    confine (modifyStore f : P E σ Unit) = trap .cannotLeave := rfl

/-- A program that only reads the store runs unchanged when confined. -/
example : confine (getStore : P E σ (CStore E)) = getStore := rfl

/-- A confined `resolved` observation traps `cannotLeave`: confined code cannot record the
result of a top-level call. -/
example (c : CallId) (r : Option (List Value.Val)) :
    confine (emit (.resolved c r) : P E σ Unit) = trap .cannotLeave := rfl

/-- An embedder import needs no entry check. -/
example (s : CStore E) (th : Option ThreadId) :
    calloutEntry s th (.embedder "f" ⟨[], []⟩) = none := rfl

end Examples

end Silmaril.Wasm.Component.Canon
