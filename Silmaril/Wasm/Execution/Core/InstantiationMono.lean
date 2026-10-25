module

public import Silmaril.Wasm.Execution.Core.Instantiation

@[expose] public section

/-! # Instantiation under inclusion of execution profiles

Instantiating a module evaluates its global, table and element initializers.
An inclusion of finite executions therefore transports the complete
instantiation with exactly the same stores, instance, and initial code.
No determinism or totality of either numerical profile is required.

This generalizes the host-free transfer used by `Accel.Runs`: the host is an
arbitrary fixed parameter, and the premise states the required inclusion.
-/

namespace Silmaril.Wasm.Execution.Core

open Numerics Validation

variable {H : Type} {P Q : Profile} {host : HostSemantics H}
  (hPQ : ∀ {c c' : Config H}, Steps P host c c' → Steps Q host c c')
include hPQ

theorem EvalGlobals.mono {s s' : Store H} {f f' : Frame} {gs : List CGlobalType}
    {es : List Expr} {vs : List Val} (h : EvalGlobals P host s f gs es s' f' vs) :
    EvalGlobals Q host s f gs es s' f' vs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (hPQ he) ih

theorem EvalExprs.mono {s s' : Store H} {f f' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P host s f es s' f' rs) : EvalExprs Q host s f es s' f' rs := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (hPQ he) ih

theorem EvalExprss.mono {s s' : Store H} {f f' : Frame} {ess : List (List Expr)}
    {rss : List (List Ref)} (h : EvalExprss P host s f ess s' f' rss) :
    EvalExprss Q host s f ess s' f' rss := by
  induction h with
  | nil => exact .nil
  | cons he _ ih => exact .cons (he.mono hPQ) ih

/-- Transfer the same instantiation along inclusion of finite executions.
Validation, bounds, allocated values and the entire resulting configuration
are retained, rather than replaced by a merely related witness. -/
theorem Instantiate.mono {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    (h : Instantiate P host s m xas c) : Instantiate Q host s m xas c := by
  obtain ⟨valid, bounded, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi,
    globals, tables, elems, allocated, code⟩ := h
  exact ⟨valid, bounded, s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi,
    globals.mono hPQ, tables.mono hPQ, elems.mono hPQ, allocated, code⟩

end Silmaril.Wasm.Execution.Core
