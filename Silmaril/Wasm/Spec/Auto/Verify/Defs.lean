module

public import Silmaril.Wasm.Spec.Auto.Defs
public import Silmaril.Wasm.Verify.Check.Thms

@[expose] public section

/-!
# Automation: dispatching module properties to the verifier

* `ModProp.toVerify?`, `ModProp.ofVerify?`: the verifier's `Silmaril.Wasm.Verify.Property` is the
  serialisable fragment of `ModProp` (`neverCall`, `assertNeverFalse`, by import index).
* `ModProp.verdict m φ`: runs `Silmaril.Wasm.Verify.check` on the module `m` for each atom
  (`neverCallFrom i e` by the per-export verifier `Silmaril.Wasm.Verify.checkFrom`, falling back to
  `neverCall i`) and combines the verdicts
  (`and`: proved when both are, refuted when one is). Other shapes give `unknown`.
* `ModProp.reports m φ`: the verifier's reports for the atoms (`Report.toJson` renders them).
* `Request`: what a service receives, a Core module and a module property at the interface of
  its instance; `Request.task P` is the task, `Request.verdict` the verdict.

Soundness and the `wasm_spec` tactic are in `Silmaril.Wasm.Spec.Auto.Verify.Thms`.
-/

namespace Silmaril.Wasm.Spec.Auto

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Verify (check checkFrom instance? instOf progOf Report)

/-- The verifier's property of a module property, for the shapes it decides. -/
def ModProp.toVerify? {X : WIface} : ModProp X → Option Silmaril.Wasm.Verify.Property
  | .neverCall i => some (.neverCall i.val)
  | .assertNeverFalse i => some (.assertNeverFalse i.val)
  | _ => none

/-- A module property from the verifier's, if the import is in range. -/
def ModProp.ofVerify? (X : WIface) : Silmaril.Wasm.Verify.Property → Option (ModProp X)
  | .neverCall i => if h : i < X.imports.length then some (.neverCall ⟨i, h⟩) else none
  | .assertNeverFalse i => if h : i < X.imports.length then some (.assertNeverFalse ⟨i, h⟩) else none

/-- The verifier's verdict on a property it decides, given a computed instance. -/
def atomVerdict (m : Silmaril.Wasm.Module) (q : Silmaril.Wasm.Verify.Property) : Verdict :=
  if (instance? m).isSome then (check m q).verdict else .unknown

/-- The per-export verifier's verdict on `neverCallFrom (i, e)`, given a computed instance. -/
def fromVerdict (m : Silmaril.Wasm.Module) (i e : Nat) : Verdict :=
  if (instance? m).isSome then (checkFrom m i e).verdict else .unknown

/-- Combine the verdicts of a conjunction. -/
def andVerdict : Verdict → Verdict → Verdict
  | .proved, .proved => .proved
  | .refuted, _ => .refuted
  | _, .refuted => .refuted
  | _, _ => .unknown

/-- **The verdict of the verifier on a module property** of the module `m`. -/
def ModProp.verdict (m : Silmaril.Wasm.Module) : ModProp (ifaceOf (instOf m)) → Verdict
  | .neverCall i => atomVerdict m (.neverCall i.val)
  | .assertNeverFalse i => atomVerdict m (.assertNeverFalse i.val)
  | .neverCallFrom i e =>
    match fromVerdict m i.val e.val with
    | .proved => .proved
    | .refuted => .refuted
    | .unknown =>
      match atomVerdict m (.neverCall i.val) with
      | .proved => .proved
      | _ => .unknown
  | .and φ ψ => andVerdict (φ.verdict m) (ψ.verdict m)
  | _ => .unknown

/-- The verifier's reports for the atoms of a module property. -/
def ModProp.reports (m : Silmaril.Wasm.Module) : ModProp (ifaceOf (instOf m)) → List Report
  | .neverCall i => [check m (.neverCall i.val)]
  | .assertNeverFalse i => [check m (.assertNeverFalse i.val)]
  | .neverCallFrom i e => [checkFrom m i.val e.val, check m (.neverCall i.val)]
  | .and φ ψ => φ.reports m ++ ψ.reports m
  | _ => []

/-- A service request: a Core module and a module property at the interface of its instance. -/
structure Request where
  /-- The module. -/
  module : Silmaril.Wasm.Module
  /-- The property. -/
  prop : ModProp (ifaceOf (instOf module))

/-- The task of a request at profile `P`. -/
noncomputable def Request.task (r : Request) (P : Silmaril.Wasm.Numerics.Profile) : Task :=
  .module P (progOf r.module) r.prop

/-- The verdict on a request. -/
def Request.verdict (r : Request) : Verdict := r.prop.verdict r.module

end Silmaril.Wasm.Spec.Auto

