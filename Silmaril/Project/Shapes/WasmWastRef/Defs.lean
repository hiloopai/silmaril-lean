module

public import Silmaril.Wasm.Execution.Core.Values
public import Silmaril.Wasm.Execution.MemRep.Defs

/-!
# WAST host references: arguments and result patterns

The WAST script language has literals and result patterns for references that no Wasm module
can write down: **host references**. At WebAssembly/spec `608711107b`
(`interpreter/text/parser.mly` l. 1507–1509, `literal_ref`):

* `(ref.host n)` is `Script.HostRef n` (`interpreter/script/script.ml` l. 3), a reference of type
  `(ref any)` (l. 77–81, `type_of_ref'`);
* `(ref.extern n)` is `Extern.ExternRef (Script.HostRef n)` (`interpreter/runtime/extern.ml`):
  the host reference `n` converted to `extern`, of type `(ref extern)`.

In the specification's runtime syntax (Wasm 3.0 SpecTec, `4.0-execution.configurations.spectec`
l. 42–43) these are `REF.HOST_ADDR n` and `REF.EXTERN (REF.HOST_ADDR n)`, typed by `Ref_ok/host`
(`s ⊢ REF.HOST_ADDR a : REF ANY`) and `Ref_ok/extern` (`4.1-execution.values.spectec` l. 57–63);
in Core they are `Ref.host n` and `Ref.extern (Ref.host n)` (`RefOk.host`, `RefOk.extern`). So an
argument `(ref.extern n)` is the Core value `.ref (.extern (.host n))`, with no new runtime
syntax.

**Arguments.** `interpreter/script/runner.ml` l. 402–417 (`run_action`): an `invoke` checks that
each literal's type (`type_of_lit`: `(ref extern)` for `(ref.extern n)`) matches the parameter
type (`Match.match_valtype`), then calls the function. `argsOkR` accepts a numeric argument of
exactly its parameter type (as `WasmWast.argsOk`) and `(ref.extern n)` for a parameter
`(ref null? extern)`; `invokeOkRB_sound` (`….Thms`) gives the premise `InvokeOk` of `$invoke`.

**Result patterns** (`runner.ml` l. 464–477, `assert_ref_pat`; `parser.mly` l. 1525–1537):

* `RefPat r` (`(ref.extern n)`, `(ref.host n)`, `(ref.null)`) holds when `Value.eq_ref` holds:
  for `ExternRef`, `HostRef` and `NullRef` that is structural equality (`extern.ml`,
  `script.ml` l. 90–94); here it is the exact value, `Pat.exact v`;
* `NullPat` (`(ref.null ht)`) holds for every null reference: Core has one null `Ref.null`, so
  it is `Pat.exact (.ref .null)`;
* `RefTypePat FuncHT` (`(ref.func)`) holds for every function reference (`Instance.FuncRef _`),
  never for null: `Pat.funcRef`, any `.ref (.func a)`.

Other patterns (`(ref.any)`, `(ref.extern)`, `(ref.eq)`, `(ref.struct)`, …, `either`, vector
lanes) do not occur in the linked files of the slice and are not modelled.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWastRef

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- **The WAST argument `(ref.extern n)`**: the host reference `n` converted to `extern`. -/
def externHost (n : Nat) : Val := .ref (.extern (.host n))

/-- An argument of the parameter type `p`: a number of exactly that type, or `(ref.extern n)`
for an `extern` reference parameter (nullable or not). -/
def argOkR : Val → CValType → Bool
  | .num n, p => decide (p = .num n.type)
  | .ref (.extern (.host _)), .refv (.ref _ (.abs .extern)) => true
  | _, _ => false

/-- Arguments of the parameter types `ps`, position by position. -/
def argsOkR : List Val → List CValType → Bool
  | [], [] => true
  | v :: vs, p :: ps => argOkR v p && argsOkR vs ps
  | _, _ => false

/-- The function `a` of `s` has a function type whose parameters `args` match (`argsOkR`). Only
the functions of `s` are read, so it is stated over any memory representation `R`. -/
def invokeOkRB {R : Type} (s : Store Nat R) (a : Nat) (args : List Val) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.type.funcType? with
    | some (ps, _) => argsOkR args ps
    | none => false
  | none => false

/-- **A WAST result pattern**: an exact value (numbers, `(ref.extern n)`, `(ref.null …)`), or
`(ref.func)`: any function reference. -/
inductive Pat where
  | exact (v : Val)
  | funcRef
  deriving DecidableEq, Repr

/-- The value `w` matches the pattern. -/
def Pat.Matches : Pat → Val → Prop
  | .exact v, w => w = v
  | .funcRef, w => ∃ a, w = .ref (.func a)

/-- Decide `Pat.Matches`. -/
def Pat.matches : Pat → Val → Bool
  | .exact v, w => decide (w = v)
  | .funcRef, .ref (.func _) => true
  | .funcRef, _ => false

/-- The values `vs` match the patterns `ps`, position by position. -/
def MatchAll (ps : List Pat) (vs : List Val) : Prop := List.Forall₂ Pat.Matches ps vs

/-- Decide `MatchAll`. -/
def matchAll : List Pat → List Val → Bool
  | [], [] => true
  | p :: ps, v :: vs => p.matches v && matchAll ps vs
  | _, _ => false

end Silmaril.Project.Shapes.WasmWastRef

end
