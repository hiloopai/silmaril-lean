module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! # The loose C specification

`Spec.allowed impl file enums args obs` holds when the observed behaviour `obs` of a compiled
program (its termination and its stdout bytes) is one of the outcomes of the **nondeterministic**
Core semantics of the program's Cerberus Core document: some execution of `Core.Dynamics.lts`,
under any unsequenced interleaving and any `nd` choice the relation retains, reaches a halted
state whose outcome admits `obs`.

* A reachable undefined behaviour admits every observation, including output printed before it
  (C11 §3.4.3, §4p2: the standard places no requirement on an execution that contains UB).
* An unspecified exit value admits every exit status; the stdout must still match.
* `abort()` (C11 §7.22.4.1p2) admits an abnormal termination whose stdout is a prefix of the
  output the program produced: whether open streams are flushed is implementation-defined,
  and glibc does not flush them.
* `error` and `unsupported` endings admit nothing: they are gaps of the Lean dynamics, not
  behaviours of C. A program whose executions reach them is outside the decided fragment.

Implementation-defined choices that the observation depends on are the fields of `Impl`; the
default is the LP64 Cerberus implementation the documents are elaborated against
(`gcc_4.9.0_x86_64-apple-darwin10.8.0`, whose layout constants `Mem.Layout` and
`Mem.Concrete.integerBounds` fix) and a POSIX host (an exit status is the low 8 bits).

This file is the frozen statement of the loose C specification: change it only in a
reviewed change of its own. The Core dynamics it quantifies over is kept faithful to Cerberus/Lem and the C standard. -/

@[expose] public section
namespace Silmaril.Cerberus.Spec

open Core.Dynamics

/-- How a run of a compiled program ended. -/
inductive Termination where
  /-- `exit(n)` or a return from `main`: the host's 8-bit exit status. -/
  | exit (status : Nat)
  /-- Abnormal termination by `abort()` (SIGABRT). -/
  | abort
  /-- Termination by any other signal: a trap (SIGILL, SIGSEGV, SIGFPE, ...). -/
  | signal (number : Nat)
  deriving DecidableEq, Repr

def Termination.isExit : Termination → Bool
  | .exit _ => true
  | _ => false

/-- An observed behaviour: the termination and the stdout bytes. -/
structure Obs where
  termination : Termination
  stdout : List Nat
  deriving DecidableEq, Repr

/-- The bytes of the dynamics' stdout: the formatted-output functions append one character per
byte (`Core.Formatted`, the `printf` builtin of `Core.Dynamics`). -/
def bytes (s : String) : List Nat := s.toList.map Char.toNat

/-- Implementation-defined choices that the observation depends on. -/
structure Impl where
  /-- The host exit status of `exit(n)` (C11 §7.22.4.4p5 leaves it implementation-defined;
  POSIX `_exit` keeps `n & 0377`). -/
  status : Int → Nat := fun n => (n % 256).toNat
  /-- Whether `abort()` flushes the output streams (C11 §7.22.4.1p2: implementation-defined). -/
  abortFlushes : Bool := false

/-- LP64 Cerberus implementation on a POSIX host (glibc: `abort` does not flush). -/
def Impl.lp64 : Impl := {}

/-- How a defined result of `main` (or the argument of `exit`) reaches the host. -/
inductive ExitValue where
  | int (n : Int)
  | unspecified
  | other

def exitValue : Val → ExitValue
  | .loaded (.specified (.integer n)) => .int n
  | .object (.integer n) => .int n
  | .loaded (.unspecified _) => .unspecified
  | _ => .other

/-- The observations a halted execution with outcome `o` and stdout `out` admits. -/
def admits (impl : Impl) (o : Outcome) (out : String) (obs : Obs) : Prop :=
  match o with
  | .ub _ _ => True
  | .defined v =>
      match exitValue v with
      | .int n => obs.termination = .exit (impl.status n) ∧ obs.stdout = bytes out
      | .unspecified => obs.termination.isExit = true ∧ obs.stdout = bytes out
      | .other => False
  | .aborted =>
      obs.termination = .abort ∧ obs.stdout <+: bytes out ∧
        (impl.abortFlushes = true → obs.stdout = bytes out)
  | .error _ => False
  | .unsupported _ => False

instance (impl : Impl) (o : Outcome) (out : String) (obs : Obs) : Decidable (admits impl o out obs) := by
  unfold admits
  split
  · exact inferInstance
  · split <;> exact inferInstance
  all_goals exact inferInstance

/-- Reachability in the Core LTS, over every label (memory actions, choices, scheduling). -/
def Reaches (file : Program) (labels : Labels) : State → State → Prop :=
  Relation.ReflTransGen fun s t => ∃ a, (lts file labels).Tr s a t

/-- **The specification.** `obs` is a behaviour of the program `file` (with the enum registry
`enums`) run with the command-line arguments `args`. -/
def allowed (impl : Impl) (file : Program) (enums : Map Sym IntegerType) (args : List String)
    (obs : Obs) : Prop :=
  match initial file enums (Core.Startup.execArguments args) with
  | .error o => admits impl o "" obs
  | .ok (start, labels) =>
      ∃ s o, Reaches file labels start s ∧ s.control = .halt o ∧ admits impl o s.memory.stdout obs

/-- The specification of a decoded Cerberus document. -/
def allowedDocument (impl : Impl) (doc : Codec.Document) (args : List String) (obs : Obs) : Prop :=
  allowed impl doc.file (Map.ofList (doc.enumBindings.getD [])) args obs

end Silmaril.Cerberus.Spec
