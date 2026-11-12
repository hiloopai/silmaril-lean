module

public import Silmaril.Wasm.Perf.ValidateF.Defs
import Silmaril.Proofs.Wasm.Perf.ValidateF.Eq

/-!
# The validator with array lookups is silmaril's validator

Under the invariant `fa.toList = C.funcs` (which `withLabel` and `initLocals` keep), with `rs`
a hash set of `C.refs` and the locals in an array `la` (the context the fast functions see has
its list of locals emptied): `directStepF_eq`, `padForF_eq`, by mutual induction on
instructions `checkInstrF_eq`, `checkSeqF_eq`; then `checkExprF_eq`, `exportCheckF_eq`,
`nodupF_eq` and **`validateF_eq : validateF = validate?`**.

The proofs are in `Silmaril.Proofs.Wasm.Perf.ValidateF.Eq`.
-/

@[expose] public section

namespace Silmaril.Wasm.Perf.ValidateF

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Validation.CheckInstrs

/-- The fast step is `directStep` (the arrays and the hash set read what the context holds). -/
theorem directStepF_eq {fa : Array DefType} {rs : Std.HashSet Nat} {la : Array LocalType}
    {C : Context} (h : fa.toList = C.funcs) (hr : ∀ n, rs.contains n = decide (n ∈ C.refs))
    (hl : la.toList = C.locals) (S : List CValType) (i : Instr) :
    directStepF fa rs la { C with locals := [] } S i = directStep atomC tyOkC C S i :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.directStepF_eq h hr hl S i

theorem padForF_eq {fa : Array DefType} {C : Context} (h : fa.toList = C.funcs) (poly : Bool)
    (i : Instr) : padForF fa { C with locals := [] } poly i = padFor C poly i :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.padForF_eq h poly i

theorem checkInstrF_eq (fa : Array DefType) (rs : Std.HashSet Nat) (i : Instr) :
    ∀ (C : Context) (la : Array LocalType), fa.toList = C.funcs →
      (∀ n, rs.contains n = decide (n ∈ C.refs)) → la.toList = C.locals →
      ∀ (S : List CValType),
      checkInstrF fa rs la { C with locals := [] } S i = checkInstr atomC tyOkC C S i :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.checkInstrF_eq fa rs i

theorem checkSeqF_eq (fa : Array DefType) (rs : Std.HashSet Nat) (l : List Instr) :
    ∀ (C : Context) (la : Array LocalType), fa.toList = C.funcs →
      (∀ n, rs.contains n = decide (n ∈ C.refs)) → la.toList = C.locals →
      ∀ (s : List CValType) (poly : Bool) (goal : Option (List CValType)),
      checkSeqF fa rs la { C with locals := [] } s poly goal l =
        checkSeq atomC tyOkC C s poly goal l :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.checkSeqF_eq fa rs l

theorem checkExprF_eq {fa : Array DefType} {rs : Std.HashSet Nat} {C : Context}
    (h : fa.toList = C.funcs) (hr : ∀ n, rs.contains n = decide (n ∈ C.refs)) (e : Expr)
    (ts : List CValType) : checkExprF fa rs C e ts = exprC C e ts :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.checkExprF_eq h hr e ts

theorem exportCheckF_eq {fa : Array DefType} {C : Context} (h : fa.toList = C.funcs)
    (e : Export) : exportCheckF fa C e = exportCheck? C e :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.exportCheckF_eq h e

theorem nodupF_eq (l : List String) : nodupF l = decide l.Nodup :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.nodupF_eq l

/-- **`validateF` is silmaril's `validate?`.** -/
theorem validateF_eq : validateF = validate? :=
  Silmaril.Proofs.Wasm.Perf.ValidateF.validateF_eq

end Silmaril.Wasm.Perf.ValidateF
