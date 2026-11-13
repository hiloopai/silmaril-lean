module

public import Silmaril.Wasm.Wat
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Game.Instantiate.Defs

/-!
# Talk-sized Wasm examples written in WAT: the module and its specifications

`demo` is a Core 3.0 module written with silmaril-lean's `wat3!` quotation (the text is parsed,
name-resolved and expanded at elaboration time into an ordinary silmaril-lean `Module`):

```wat
(module
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    local.get $x local.get $y i32.add)
  (func $abs (export "abs") ...)   ;; if/else on i32.lt_s
  (func $max (export "max") ...)   ;; select on i32.gt_s
  (func $sum (export "sum") ...))  ;; block/loop/br_if: 1 + 2 + ... + n
```

`demoStore` is the store after instantiating `demo` against no imports with silmaril-lean's
`instantiateOnce?`, and `exportAddr? demoMI name` finds the function address of an export.

The specifications are every-run Hoare specifications (`Silmaril.Wasm.Logic.Hoare.FSpec`) of
functions that do not touch the store: `retSpec fi a args res` says that the function instance
`fi` stored at address `a`, called on `args`, returns exactly `res` in every run, leaving the
store unchanged (in particular it never traps). Proofs in `Silmaril.Proofs.Wasm.Examples.Wat`.
A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Wat

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Hoare (FSpec)

/-- **The demo module**, written in WAT. -/
def demo : Module := wat3! r#"
(module
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    local.get $x
    local.get $y
    i32.add)
  (func $abs (export "abs") (param $x i32) (result i32)
    (if (result i32) (i32.lt_s (local.get $x) (i32.const 0))
      (then (i32.sub (i32.const 0) (local.get $x)))
      (else (local.get $x))))
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y))))
  (func $sum (export "sum") (param $n i32) (result i32) (local $i i32) (local $acc i32)
    (block $done
      (loop $next
        (br_if $done (i32.eq (local.get $i) (local.get $n)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (local.set $acc (i32.add (local.get $acc) (local.get $i)))
        (br $next)))
    (local.get $acc)))
"#

/-- The instantiation of `demo` against no imports. -/
def demoRun : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? (importStore []) demo []

/-- The store after instantiation. -/
def demoStore : Store Nat :=
  match demoRun with
  | some (s, _, _) => s
  | none => {}

/-- The module instance. -/
def demoMI : ModuleInst :=
  match demoRun with
  | some (_, f, _) => f.module
  | none => {}

/-- The function address of the export `name` of a module instance. -/
def exportAddr? (mi : ModuleInst) (name : String) : Option Nat :=
  (mi.exports.find? (·.name == name)).bind fun x => match x.addr with
    | .func a => some a
    | _ => none

/-- `0 + 1 + ⋯ + n`. -/
def triangle : Nat → Nat
  | 0 => 0
  | k + 1 => triangle k + (k + 1)

/-- **The loop invariant of `sum`** on the argument `n` and the initial store `s₀`: the store is
unchanged, the loop has no parameters, and the locals are `n, i, acc` with `i ≤ n` and
`acc = 0 + 1 + ⋯ + i` (modulo `2³²`). -/
def sumInv {H : Type} (n : BitVec 32) (s₀ : Store H) (s : Store H) (f : Frame) (a : List Val) :
    Prop :=
  s = s₀ ∧ a = [] ∧ ∃ i acc : BitVec 32,
    f.locals = [some (.i32 n), some (.i32 i), some (.i32 acc)] ∧ i.toNat ≤ n.toNat ∧
    acc = BitVec.ofNat 32 (triangle i.toNat)

variable {H : Type}

/-- **A store-preserving function returning `res` on `args`**: the function instance `fi` is
at address `a`; every run of a call on `args` returns `res` and leaves the store unchanged. -/
def retSpec (fi : FuncInst H) (a : Nat) (args res : List Val) : FSpec H where
  pre s args' := s.funcs[a]? = some fi ∧ args' = args
  post s _ s' o := s' = s ∧ o = .normal res

end Silmaril.Wasm.Examples.Wat
