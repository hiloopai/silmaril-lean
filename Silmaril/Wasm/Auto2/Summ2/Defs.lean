module

public import Silmaril.Wasm.Auto2.Calls.Defs
public import Silmaril.Wasm.Auto2.Kernel.Defs

/-!
# Function summaries, pass 2 of the summaries track: a third simplifier, kernel-cheap checks

Round 2 of `docs/projects/wasm-binaryen-tooling.md`, section "Round 2, track summaries (pass 2)". Two additions
to the summaries with unrolled loops and inlined calls (`Silmaril.Wasm.Auto2.Calls`):

* **A third simplifier** `simp3`, applied after `Silmaril.Wasm.Auto2.Summ.canon2` (`canon3`): an
  unsigned remainder by a constant `2^k` is a mask (`x rem_u 2^k = x and (2^k - 1)`), and the
  count of a shift or rotation by a constant is reduced modulo the width (`rotl x (-2)` is
  `rotl x 30` on `i32`). These are the identities Binaryen `-O2` uses on the `opt-in` corpus'
  `f29` and `f30`, which pass 1 proved only by e-graph lifts. `sumCheckV` is
  `Silmaril.Wasm.Auto2.Summ.sumCheckU` with `canon3` for the results (it accepts every pair
  `sumCheckU` accepts: `canon3 = canon ∘ simp3 ∘ canon2`).
* **Kernel-cheap checks**: `checkAmongVK` is `checkAmongV` over the kernel track's validation-free
  instance `Silmaril.Wasm.Auto2.Kernel.instK?`, with memories compared by
  `Silmaril.Wasm.Auto2.Kernel.bytesEqL` (`checkAmongV_eq_K`, given that both modules validate). The
  `chunkV` theorems of `wasm-check` certificates rewrite to it, so the summaries of modules
  with a data segment (`memsum4`, `adlersum8`) are checked in the kernel.

The theorems are in `Silmaril.Wasm.Auto2.Summ2.Thms`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto2.Summ (canon2 pow2? keys anyDead)
open Silmaril.Wasm.Auto2.Calls (fnSumC? fnSumCI)
open Silmaril.Wasm.Verify (instance?)

/-! ## A third simplifier -/

/-- A shift or rotation count. -/
def countOp : IntBinOp → Bool
  | .shl | .shr _ | .rotl | .rotr => true
  | _ => false

/-- A binary operator on simplified operands: a mask for `rem_u` by `2^k`, counts reduced modulo
the width. -/
def mkBin3 (t : IntType) (op : IntBinOp) (a b : XT) : XT :=
  match b with
  | .const c =>
    if op = .rem .unsigned then
      match pow2? t b with
      | some k => .bin .and a (.const (2 ^ k - 1))
      | none => .bin op a b
    else if countOp op then .bin op a (.const (c % 2 ^ t.width % t.width))
    else .bin op a b
  | _ => .bin op a b

/-- **The third simplifier** of value terms at type `t` (memory terms and loads are kept). -/
def simp3 : IntType → XT → XT
  | t, .un op a => .un op (simp3 t a)
  | t, .bin op a b => mkBin3 t op (simp3 t a) (simp3 t b)
  | _, .rel t' op a b => .rel t' op (simp3 t' a) (simp3 t' b)
  | _, .wrap a => .wrap (simp3 .i64 a)
  | _, .ext sx a => .ext sx (simp3 .i32 a)
  | t, .sel c a b => .sel (simp3 .i32 c) (simp3 t a) (simp3 t b)
  | _, e => e

/-- **The simplifier of pass 2**: `canon2`, the third simplifier, `canon`. -/
def canon3 (t : IntType) (e : XT) : XT := canon t (simp3 t (canon2 t e))

/-- Simplified slots. -/
def slots3 (l : List (IntType × XT)) : List (IntType × XT) := l.map fun p => (p.1, canon3 p.1 p.2)

/-! ## The check -/

/-- **The check of two summaries**: `Silmaril.Wasm.Auto2.Summ.sumCheckU` with `canon3` for the
results. -/
def sumCheckV : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      ((anyDead A.final.guards && anyDead B.final.guards) ||
        ((!(usesMem A.final || usesMem B.final) || decide (A.bytes = B.bytes)) &&
          (keys A.final.guards).all (keys B.final.guards).contains &&
          (keys B.final.guards).all (keys A.final.guards).contains &&
          decide (slots3 A.final.stack = slots3 B.final.stack)))
  | _, _ => false

/-- The check at export `j` of two modules (summaries with unrolled loops and inlined calls). -/
def fnCheckV (fuel : Nat) (m₁ m₂ : Module) (j : Nat) : Bool :=
  sumCheckV (fnSumC? fuel m₁ j) (fnSumC? fuel m₂ j)

/-- **The check on the exports `js`**, each module instantiated once. -/
def checkAmongV (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) => js.map fun j => sumCheckV (fnSumCI fuel I₁ j) (fnSumCI fuel I₂ j)
  | _, _ => []

/-! ## Kernel-cheap checks -/

/-- `sumCheckV` with the memories compared by `bytesEqL`. -/
noncomputable def sumCheckVK : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      ((anyDead A.final.guards && anyDead B.final.guards) ||
        ((!(usesMem A.final || usesMem B.final) ||
            Silmaril.Wasm.Auto2.Kernel.bytesEqL A.bytes.data.toList B.bytes.data.toList) &&
          (keys A.final.guards).all (keys B.final.guards).contains &&
          (keys B.final.guards).all (keys A.final.guards).contains &&
          decide (slots3 A.final.stack = slots3 B.final.stack)))
  | _, _ => false

/-- **`checkAmongV` over the validation-free instance** `instK?` and with `sumCheckVK`. -/
noncomputable def checkAmongVK (fuel : Nat) (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match Silmaril.Wasm.Auto2.Kernel.instK? m₁, Silmaril.Wasm.Auto2.Kernel.instK? m₂ with
  | some I₁, some I₂ => js.map fun j => sumCheckVK (fnSumCI fuel I₁ j) (fnSumCI fuel I₂ j)
  | _, _ => []

end Silmaril.Wasm.Auto2.Summ2
