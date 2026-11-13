module

public import Silmaril.Cerberus.Core.Run.Defs
public import Silmaril.Compiler.C.Sem.Basic.Defs
public import Silmaril.Compiler.Mir.Semantics.Defs
public import Silmaril.Compiler.Category.Institution.Defs
@[expose] public section

/-!
# The semantics of Cerberus Core

Cerberus Core (`Silmaril.Cerberus.Core.Syntax`, `docs/projects/cerberus.md`) as a language of the
compiler zoo. A Core program is a decoded Core file (`Cerberus.Core.Dynamics.Program`), closed:
its `main` is run by the startup sequence of Cerberus's driver (`Dynamics.initial`: global
definitions in file order, then `main`'s argument objects (`Core.Startup`), `errno`, and the
body; `driver.lem:1542-1872`). Its dynamics is the labelled transition system
`Dynamics.lts` (`Silmaril/Cerberus/Core/Dynamics.lean`); the certified fuelled runner
`Dynamics.runWith` (`Silmaril/Cerberus/Core/Run.lean`) follows one response index per step.

Observations are those of every C semantics, `C.Sem.Obs` (a process's standard output and how
it ended), so that Core meets typed Ail (`C.Sem.cSyntax`) at the identity of observations, and
Mir/Lir through the read-back of ccomp's runtime (`readBack`, as `Target.observe` does for the
interpreter).

## What `Core.beh` covers

* **Nondeterminism.** The Core LTS keeps every unsequenced interleaving and every `nd`
  choice (`Request.choose`, `Request.scheduled`); `beh` takes all of them: it quantifies over
  all finite executions of the LTS (all fuels and all schedules), not over the single schedule
  that `runWith` follows.
* **Endings.** A run ends in a halted state `⟨.halt o, _, mem⟩` with a Core outcome `o`
  (`Dynamics.Outcome`):
  - `.defined v`: `main` returned `v`, or the program called `exit(v)` or `_Exit(v)`
    (`Dynamics.LibraryCall.exit`). An integer `v` (`Specified(n)` or a bare integer object)
    is the exit status `n mod 256`; an unspecified value (`.loaded (.unspecified _)`) allows
    every status; any other value gives no behaviour. Standard output is the accumulated
    `Mem.Concrete.State.stdout`.
  - `.aborted`: `abort()` was called (`Dynamics.LibraryCall.abort`); the process ends by signal 6
    (`SIGABRT`, as in `C0.beh`) with the accumulated standard output.
  - `.ub _ _`: undefined behaviour; the behaviour set is `Set.univ` (as in `C0.beh`).
  - `.error _` (Core dynamic errors: empty choice, pattern mismatch, a missing `main`, …) and
    `.unsupported _` (forms outside the ported fragment): **no behaviour**.
* **Divergence.** `⟨[], .diverges⟩` is a behaviour when the LTS has an infinite execution from
  the start (`Operational.Diverges`), with empty standard output as in `C0.beh`.

The ported dynamics covers the sequential fragment described in `docs/projects/cerberus.md`
(§ Bounded Core evaluation, § Memory operations and formatted output, § Sequential main
startup): LP64 integers, `_Bool`, arithmetic with exceptional-condition guards, conversions,
constructors and patterns, pure functions and procedure calls (also through function
pointers), saved labels and jumps, non-atomic and sequentially consistent Create/Store/Load/Kill
on the concrete PNVI memory (integers, pointers, arrays, structs), pointer arithmetic, and
`printf` with the pinned conversions (`Core.Formatted`), and the library procedures `exit`,
`_Exit` and `abort` (`Dynamics.libraryCall`). There is **no `putchar`** in the dynamics: output
comes only from the `printf` builtin, and a process ends by `main` returning, by `exit`/`_Exit`, or
by `abort`. Other library calls, unions, atomics other than SC, other `printf` flags and
everything else end in `.unsupported`, hence give no behaviour here: `Core.beh` makes no claim
about them (just as `C0.beh` makes none outside the C0 fragment).

Core's standard output is a `String` whose characters are bytes (`printf` writes
`Char.ofNat (n % 256)` per byte, `Core.Formatted`); `stdoutBytes` reads each character back as
one byte.

## Main definitions

* `Core.beh`, `Core.syntax`, `Core.sem`, `Core.lang`.
* `Core.elabSem`: the C semantics obtained by elaborating typed Ail to Core.
* `Core.readBack`: Lir outcomes read as process observations.
* The conventions of the Ail/Core/Mir triangle `cAC`, `cCM`, `cAM`, the 2-cell
  `cAC_comp_cCM`, and their read-backs (hence comorphisms, `Convention.comorphism`).
-/

namespace Silmaril.Compile.Core

open Silmaril.Machine
open CategoryTheory Silmaril.Compile.Category Silmaril.Logic.Institution
open Silmaril.Compile.C.Sem (Obs Exit)
open Silmaril.Cerberus.Core.Dynamics (Program State Labels Val lts initial)

/-! ## Behaviours -/

/-- The standard output of a Core run as bytes: `Mem.Concrete.State.stdout` holds one character
per output byte (`printf` writes `Char.ofNat (n % 256)`, `Silmaril/Cerberus/Core/Formatted.lean`),
read back as that byte. -/
def stdoutBytes (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

/-- The exit statuses of the value `main` returns (`Outcome.defined v`, `Core/Dynamics.lean`,
`core_run.lem:1540-1542`): an integer `n` (specified, or a bare integer object, as
`Core.Outcome.observation` reads it) is the status `n mod 256`; an unspecified value allows every
status; other values are outside the observed fragment (no status). -/
def exitOf : Val → Set Exit
  | .loaded (.specified (.integer n)) => {.status ((n : Int) % 256).toNat}
  | .object (.integer n) => {.status ((n : Int) % 256).toNat}
  | .loaded (.unspecified _) => {e | ∃ k < 256, e = .status k}
  | _ => ∅

/-- The observations of a final state of the Core LTS: a halted state whose outcome is a value
returned by `main` (or passed to `exit`/`_Exit`) shows the accumulated standard output and the exit
status of that value; an aborted state shows the accumulated standard output and signal 6
(`SIGABRT`). Other states (live, undefined, error, unsupported) show nothing. -/
def finalObs (s : State) : Set Obs :=
  match s.control with
  | .halt (.defined v) => {o | o.stdout = stdoutBytes s.memory.stdout ∧ o.exit ∈ exitOf v}
  | .halt .aborted => {o | o.stdout = stdoutBytes s.memory.stdout ∧ o.exit = .signal 6}
  | _ => ∅

/-- The behaviours of the Core LTS (`Dynamics.lts`, `Core/Dynamics.lean`) from a state, in the
style of `C0.beh` but over **all** executions (every fuel and every schedule of the
nondeterministic LTS): the observations of halted final states, everything if some execution
reaches undefined behaviour, and divergence (empty output) if some execution is infinite. -/
def behFrom (file : Program) (labels : Labels) (s₀ : State) : Set Obs := {o |
  (∃ acts s, (lts file labels).MTr s₀ acts s ∧ o ∈ finalObs s) ∨
    (∃ acts s loc ub, (lts file labels).MTr s₀ acts s ∧
      s.control = .halt (.ub loc ub)) ∨
    (o = ⟨[], .diverges⟩ ∧ Silmaril.Operational.Diverges (lts file labels) s₀)}

/-- **The behaviours of a closed Core program**: `behFrom` the startup state of `main`
(`Dynamics.initial` with Cerberus's default arguments `["cmdname"]`, `Core/Startup.lean`,
`driver.lem:1542-1872`). Outcomes the ported dynamics cannot handle (`.unsupported`) and Core
errors (`.error`) give no behaviour. -/
def beh (file : Program) : Set Obs :=
  match initial file with
  | .ok (s₀, labels) => behFrom file labels s₀
  | .error _ => ∅

/-- Core's syntax: closed Core files observed as processes; interfaces are trivial. -/
def «syntax» : Syntax.{0} := ⟨PUnit, Program, fun _ => ⟨⟩, Obs⟩

/-- Core's semantics: `beh`. -/
def sem : «syntax».Sem := beh

/-- Core as a language of the zoo. -/
def lang : Language.{0} := «syntax».lang sem

theorem behFrom_of_final {file : Program} {labels : Labels} {s₀ s : State} {acts}
    (h : (lts file labels).MTr s₀ acts s) {o : Obs} (ho : o ∈ finalObs s) :
    o ∈ behFrom file labels s₀ :=
  .inl ⟨acts, s, h, ho⟩

/-- Undefined behaviour on some execution allows every behaviour. -/
theorem behFrom_of_ub {file : Program} {labels : Labels} {s₀ s : State} {acts}
    (h : (lts file labels).MTr s₀ acts s) {loc ub} (hs : s.control = .halt (.ub loc ub)) :
    behFrom file labels s₀ = Set.univ :=
  Set.eq_univ_of_forall fun _ => .inr (.inl ⟨acts, s, loc, ub, h, hs⟩)

/-- A run of the certified runner that ends finishes in a halted state with that outcome. -/
theorem runWith_finalState_control (choice : Nat) (file : Program) (labels : Labels) :
    ∀ (fuel : Nat) (start : State) {o : Cerberus.Core.Dynamics.Outcome},
      (Cerberus.Core.Dynamics.runWith choice file labels fuel start).ending = some o →
      (Cerberus.Core.Dynamics.runWith choice file labels fuel start).finalState.control =
        .halt o
  | 0, _, _, h => by simp [Cerberus.Core.Dynamics.runWith] at h
  | fuel + 1, start, o, h => by
    unfold Cerberus.Core.Dynamics.runWith at h ⊢
    split at h
    · rename_i t ht
      exact runWith_finalState_control choice file labels fuel t.after h
    · rename_i o' ho' hs
      cases h
      exact ho'

/-- Every observation of a run of the certified runner (`Core/Run.lean`, any response index and
fuel) that ends with `main`'s value is a behaviour. -/
theorem behFrom_of_runWith {file : Program} {labels : Labels} {s₀ : State} (choice fuel : Nat)
    {v : Val} (h : (Cerberus.Core.Dynamics.runWith choice file labels fuel s₀).ending =
      some (.defined v))
    {o : Obs} (ho : o.stdout = stdoutBytes
        (Cerberus.Core.Dynamics.runWith choice file labels fuel s₀).finalState.memory.stdout ∧
      o.exit ∈ exitOf v) :
    o ∈ behFrom file labels s₀ := by
  refine behFrom_of_final (Cerberus.Core.Dynamics.runWith choice file labels fuel s₀).trace ?_
  unfold finalObs
  rw [runWith_finalState_control choice file labels fuel s₀ h]
  exact ho

/-- A run of the certified runner that ends in undefined behaviour makes every observation a
behaviour. -/
theorem behFrom_of_runWith_ub {file : Program} {labels : Labels} {s₀ : State} (choice fuel : Nat)
    {loc ub} (h : (Cerberus.Core.Dynamics.runWith choice file labels fuel s₀).ending =
      some (.ub loc ub)) :
    behFrom file labels s₀ = Set.univ :=
  behFrom_of_ub (Cerberus.Core.Dynamics.runWith choice file labels fuel s₀).trace
    (runWith_finalState_control choice file labels fuel s₀ h)

/-! ## Elaboration: the top of the C ladder -/

/-- The C semantics obtained by elaborating typed Ail to Core and taking Core's behaviours.
The top of the C semantics ladder `⟦p⟧` (`Silmaril/Compile/C/Sem/C0.lean`) is
`elabSem cerberusElab` once the Ail → Core elaboration exists. The intended
relation with the first rung is `C0.sem ⊑[C0.InFragment] elabSem elaborate`, i.e. every behaviour of a
C0 program (`C0.InFragment`) is a behaviour of its elaboration under Core; it is not stated as a
theorem here. -/
def elabSem (elaborate : Silmaril.Cerberus.Ail.TypedProgram → Program) : C.Sem.Semantics :=
  fun p => beh (elaborate p)

/-! ## Reading Lir outcomes as processes -/

/-- Word `i` (8 bytes, little-endian) of the control block of ccomp's runtime at `ctl`. -/
def ctlWord (ctl : Nat) (m : Lir.Memory) (i : Nat) : Nat :=
  (Lir.readLE m.bytes (ctl + 8 * i) 8).toNat

/-- The output buffer of a final memory, as `Target.outputOf` (`Compile/Target/Interp.lean`)
reads it: `min (word 3) (word 7)` bytes from the address in word 6 of the control block, zero
beyond the memory. -/
def outputOf (ctl : Nat) (m : Lir.Memory) : List UInt8 :=
  (List.range (min (ctlWord ctl m 3) (ctlWord ctl m 7))).map fun i =>
    let a := ctlWord ctl m 6 + i
    if a < m.size then (m.bytes a).toNat.toUInt8 else 0

/-- **The read-back of Lir outcomes as process observations**, as `Target.observe`
(`Silmaril/Compile/Target/Interp.lean`) does for the interpreter, with `ctl` the link's address
of `__ccomp_ctl`:

* returned values: the output buffer and the status `(v.headD 0) mod 256` of the first word;
* trapped: the output buffer, and by the exit kind (word 5 of the control block): `1` → the status
  in the low 4 bytes of word 4, `2` → signal 6 (`abort`), otherwise signal 4 (`SIGILL`);
* diverges: empty output, `Exit.diverges`;
* exhausted (`Target.observe`: a too deep recursion, `SIGILL`): empty output (a Lir outcome
  keeps no memory), signal 4;
* undefined (a stuck Lir run, which has no process counterpart): empty output, signal 4. Mir's
  behaviours are closed under undefined behaviour (`Mir.ubClose`), so this choice only matters
  through `Set.univ`;
* faulted: impossible (`Empty`). -/
def readBack (ctl : Nat) : Mir.LirOutcome → Obs
  | .returned (vs, m) => ⟨outputOf ctl m, .status ((vs.headD 0).toNat % 256)⟩
  | .trapped m => ⟨outputOf ctl m, match ctlWord ctl m 5 with
      | 1 => .status ((Lir.readLE m.bytes (ctl + 32) 4).toNat % 256)
      | 2 => .signal 6
      | _ => .signal 4⟩
  | .faulted f => nomatch f
  | .undefined => ⟨[], .signal 4⟩
  | .exhausted => ⟨[], .signal 4⟩
  | .diverges => ⟨[], .diverges⟩

/-! ## The Ail/Core/Mir triangle -/

variable (S : C.Sem.Semantics) (cfg : Mir.Config) (ctl : Nat)

/-- Typed Ail to Core, at the same observations. -/
def cAC : C.Sem.cSyntax.lang S ⟶ lang :=
  ⟨fun _ => PUnit.unit, fun (o o' : Obs) => o = o'⟩

/-- Core to Mir: a Lir outcome realises the process observation it reads back as. -/
def cCM : lang ⟶ Mir.lang cfg :=
  ⟨fun _ => PUnit.unit, fun (o : Obs) (o' : Mir.LirOutcome) => o = readBack ctl o'⟩

/-- Typed Ail to Mir: a Lir outcome realises the process observation it reads back as. -/
def cAM : C.Sem.cSyntax.lang S ⟶ Mir.lang cfg :=
  ⟨fun _ => PUnit.unit, fun (o : Obs) (o' : Mir.LirOutcome) => o = readBack ctl o'⟩

/-- The triangle commutes: going through Core is going directly to Mir. -/
theorem cAC_comp_cCM : cAC S ≫ cCM cfg ctl = cAM S cfg ctl :=
  Convention.ext rfl Relation.eq_comp

/-- `cAC` reads back by the identity. -/
def cAC_readBack : Convention.ReadBack (cAC S) := ⟨id, fun _ _ => Iff.rfl⟩

/-- `cCM` reads back by `readBack ctl`. -/
def cCM_readBack : Convention.ReadBack (cCM cfg ctl) := ⟨readBack ctl, fun _ _ => Iff.rfl⟩

/-- `cAM` reads back by `readBack ctl`. -/
def cAM_readBack : Convention.ReadBack (cAM S cfg ctl) := ⟨readBack ctl, fun _ _ => Iff.rfl⟩

/-- The institution comorphism `Core.lang.inst → (Mir.lang cfg).inst` of `cCM`. -/
def cCM_comorphism : Inst.CoHom lang.inst (Mir.lang cfg).inst :=
  Convention.comorphism (cCM_readBack cfg ctl)

/-- The institution comorphism `(C.Sem.cSyntax.lang S).inst → (Mir.lang cfg).inst` of `cAM`. -/
def cAM_comorphism : Inst.CoHom (C.Sem.cSyntax.lang S).inst (Mir.lang cfg).inst :=
  Convention.comorphism (cAM_readBack S cfg ctl)

end Silmaril.Compile.Core
