module

public import Silmaril.Wasm.Auto2.VCBridge.Defs
public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Auto2.VCLib.Defs

/-!
# Equivalence of loops through a shared contract (round 2, summaries, pass 2)

The function summaries of `Silmaril.Wasm.Auto2.Summ` and `Silmaril.Wasm.Auto2.Calls` unroll a loop only
when its trip count is a constant. A loop whose trip count depends on the inputs needs an
invariant, which is the VC generator's form (`Silmaril.Wasm.Auto2.VCGen`, total correctness). This
module turns proved contracts into **equivalences**:

* `EqFun`: a **functional contract**, a reference function `f` that returns values on every
  typed argument list, and contracts (`Silmaril.Wasm.Auto2.VCBridge.VcEntry`, one per program shape:
  each carries its own invariants and proved conditions) whose postconditions determine `f`'s
  result;
* `vcEquivWith e₁ e₂ m₁ m₂ j`: the two contracts have the same parameter types, export `j` of
  `m₁` passes `vcCheck e₁` and export `j` of `m₂` passes `vcCheck e₂`;
* `vcEquiv F m₁ m₂ j`: some pair of `F`'s contracts does.

Soundness (`Silmaril.Wasm.Auto2.VCEquiv.Thms`): `vcEquiv F m₁ m₂ j = true` gives `ModEquiv` at
every profile, for every reflexive relation (`modEquiv_of_vcEquiv`): both exports terminate on
every typed argument list with `f`'s values.

The programs of the library (`sumO3`: Binaryen `version_123` `-O3` of `Silmaril.WasmSpec.SumTo`'s
program, whose loop is a `loop` around an `if` instead of a `block` around a `loop` with `br_if`)
are here; the library itself (`Silmaril.Wasm.Auto2.VCEquiv.eqFuns`, with the proofs of the
conditions) is in the results.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCEquiv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge

/-- **A functional contract**: a reference function that returns values on every typed argument
list, and proved contracts that determine it. -/
structure EqFun where
  /-- A name. -/
  name : String
  /-- The reference function. -/
  f : List Val → Option Result
  /-- The proved contracts (one per program shape). -/
  es : List VcEntry
  pre : ∀ e ∈ es, ∀ ρ : Env, ρ.mem 0 = ByteArray.empty → e.S.preF.den e.F ρ ρ
  ref : ∀ e ∈ es, RefOK e f
  tot : ∀ e ∈ es, ∀ vs, Silmaril.Wasm.Auto.Equiv.TypedVals e.S.params vs →
    ∃ res, f vs = some (.values res)

/-- **Two contracts check two exports**: the same parameter types, and each export passes its
contract's check. -/
def vcEquivWith (e₁ e₂ : VcEntry) (m₁ m₂ : Module) (j : Nat) : Bool :=
  e₁.S.params == e₂.S.params && vcCheck e₁ m₁ j && vcCheck e₂ m₂ j

/-- **Some pair of contracts of `F` checks the two exports.** -/
def vcEquiv (F : EqFun) (m₁ m₂ : Module) (j : Nat) : Bool :=
  F.es.any fun e₁ => F.es.any fun e₂ => vcEquivWith e₁ e₂ m₁ m₂ j

/-- Some functional contract of `L` checks the two exports. -/
def vcEquivAny (L : List EqFun) (m₁ m₂ : Module) (j : Nat) : Bool :=
  L.any fun F => vcEquiv F m₁ m₂ j

/-! ## Programs of the library -/

/-- Binaryen `version_123` `-O3` (and `-O2`) of `Silmaril.WasmSpec.SumTo.program`: the loop test
moved into an `if` inside the loop. -/
def sumO3 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (export "sum" (func $sum))
 (func $sum (param $0 i32) (result i32)
  (local $1 i32)
  (loop $again
   (if
    (local.get $0)
    (then
     (local.set $1
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
     (local.set $0
      (i32.sub
       (local.get $0)
       (i32.const 1)
      )
     )
     (br $again)
    )
   )
  )
  (local.get $1)
 )
)
"#

/-- Its function. -/
def sumO3Func : Func := sumO3.funcs[0]

/-- A counting loop in `do … while` form (`acc += n` first, the test at the end), guarded by a
test for `0`: `sum` as a C compiler writes it at `-O1`. -/
def sumDoWhile := wat3! r#"
(module
 (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
  (if (local.get $n)
   (then
    (loop $again
     (local.set $acc (i32.add (local.get $acc) (local.get $n)))
     (local.set $n (i32.sub (local.get $n) (i32.const 1)))
     (br_if $again (local.get $n)))))
  (local.get $acc)))
"#

/-- Its function. -/
def sumDoWhileFunc : Func := sumDoWhile.funcs[0]

/-- `sum n = triBV n` for the `do … while` form: the loop head also knows `n ≠ 0` (the entry test
and the back edge's). -/
def sumDoWhileSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  post := .rel .eq (Silmaril.Wasm.Auto2.VCLib.L32 0) (.fn 0 (Silmaril.Wasm.Auto2.VCLib.P32 0))
  inv := [.and (.rel .eq (.bin .add (Silmaril.Wasm.Auto2.VCLib.L32 1)
      (.fn 0 (Silmaril.Wasm.Auto2.VCLib.L32 0))) (.fn 0 (Silmaril.Wasm.Auto2.VCLib.P32 0)))
    (.nz (Silmaril.Wasm.Auto2.VCLib.L32 0))]
  var := [Silmaril.Wasm.Auto2.VCLib.L32 0]
  total := true

end Silmaril.Wasm.Auto2.VCEquiv
