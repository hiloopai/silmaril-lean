module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Selective instrumentation: no checks around functions that cannot suspend

The asyncify lowering `FXAsync.comp` puts a check (`chk`) after **every** call. Binaryen's
Asyncify omits the instrumentation of functions that cannot reach an unwind (its
`asyncify-imports` / `asyncify-removelist` analysis): such a function is never on the stack while
the stack unwinds, so neither its body nor its call sites need checks. This module states that
optimization on the asyncify machine `FXAsync.tstep`.

* `safeI S i`: instruction `i` cannot start or propagate an unwind if every function in the set
  `S` cannot: `push`, `prim`, `drop`, `alloc`, `chk`, and calls (`call`, `cond`) of functions in
  `S`. A `startUnwind`, a `startRewind` (which may rewind code that suspends) and an `rchk` are not
  safe.
* `SafeProg S Q`: every function in `S` is defined and its body is safe. This is the certificate
  of the analysis: a set of functions that cannot reach a suspension.
* `opt S skip c`: drop the check right after every call of a function in `S` (`skip` says that
  the code `c` follows such a call, so a leading `chk` is dropped). `optP S Q` optimizes every
  body. Bodies of functions in `S` lose all their checks, since they only call functions in `S`.
* `analyze Q n`: a computable analysis on the functions `< n`: iterate the refinement "defined,
  and calls only functions still in the set" from the full set, then **check** the result; a
  set that fails the check is replaced by the empty set (no optimization). So the result always
  satisfies `SafeProg`, by construction and without a proof about the iteration.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync

variable {V : Type}

/-- An instruction that cannot start or propagate an unwind, given the safe set `S`. -/
def safeI (S : Nat → Bool) : TIns V → Bool
  | .push _ => true
  | .prim _ _ => true
  | .drop => true
  | .alloc _ => true
  | .chk => true
  | .call f => S f
  | .cond f g => S f && S g
  | .startRewind _ => false
  | .startUnwind _ _ => false
  | .rchk _ => false

/-- Safe code: every instruction is safe. -/
def SafeCode (S : Nat → Bool) (c : List (TIns V)) : Prop := ∀ i ∈ c, safeI S i = true

/-- **The certificate**: every function in `S` is defined, with a safe body. -/
def SafeProg (S : Nat → Bool) (Q : Prog (TIns V)) : Prop :=
  ∀ f, S f = true → ∃ np body, Q f = some (np, body) ∧ SafeCode S body

/-- Is the instruction the call-site check? -/
def isChk : TIns V → Bool
  | .chk => true
  | _ => false

/-- Does the code after `i` skip its check: `i` calls only functions in `S`. -/
def after (S : Nat → Bool) : TIns V → Bool
  | .call f => S f
  | .cond f g => S f && S g
  | _ => false

/-- **Drop the checks after calls of functions in `S`.** With `skip`, a leading check is
dropped. -/
def opt (S : Nat → Bool) : Bool → List (TIns V) → List (TIns V)
  | _, [] => []
  | skip, i :: c => if skip && isChk i then opt S false c else i :: opt S (after S i) c

/-- Optimize every body of a function table. -/
def optP (S : Nat → Bool) (Q : Prog (TIns V)) : Prog (TIns V) :=
  fun f => (Q f).map fun x => (x.1, opt S false x.2)

/-- The selectively instrumented lowering of a kernel program. -/
def compSel (S : Nat → Bool) (P : Prog (Ins V)) : Prog (TIns V) := optP S (compP P)

/-- The configuration that calls `f` with arguments `args`, optimized. -/
def selInit (S : Nat → Bool) (f : Nat) (args : List (SV V)) : TCfg V :=
  ⟨[], .normal, [⟨opt S false [.call f, .chk], args⟩]⟩

/-! ## The analysis -/

/-- Is `f` defined with a body that calls only functions in `S`? -/
def okF (Q : Prog (TIns V)) (S : Nat → Bool) (f : Nat) : Bool :=
  match Q f with
  | some (_, body) => body.all (safeI S)
  | none => false

/-- One refinement step on the functions `< n`. -/
def refine (Q : Prog (TIns V)) (n : Nat) (S : Nat → Bool) : Nat → Bool :=
  fun f => decide (f < n) && S f && okF Q S f

/-- Iterate a refinement. -/
def iter (r : (Nat → Bool) → Nat → Bool) : Nat → (Nat → Bool) → Nat → Bool
  | 0, T => T
  | k + 1, T => iter r k (r T)

/-- The candidate: `n + 1` refinements of the full set of functions `< n`. -/
def candidate (Q : Prog (TIns V)) (n : Nat) : Nat → Bool :=
  fun f => decide (f < n) && iter (refine Q n) (n + 1) (fun _ => true) f

/-- The check of a candidate on the functions `< n`. -/
def check (Q : Prog (TIns V)) (n : Nat) (S : Nat → Bool) : Bool :=
  (List.range n).all fun f => !S f || okF Q S f

/-- **The analysis**: the checked candidate, or the empty set. -/
def analyze (Q : Prog (TIns V)) (n : Nat) : Nat → Bool :=
  if check Q n (candidate Q n) then candidate Q n else fun _ => false

end Silmaril.Wasm.FX.Asyncify.Selective
