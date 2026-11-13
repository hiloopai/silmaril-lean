module

public import Silmaril.Wasm.Dataflow.Structured.Defs
public import Silmaril.Wasm.Execution.Core.Step
public import Mathlib.Order.WithBot
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Live locals of structured Wasm code: definitions

Live-variable analysis (*Optimising Compilers* notes §3, p. 9) instantiated on the
structured framework of `Silmaril.Wasm.Dataflow.Structured`. The variables are the *locals* of
the current frame, by index:

* `LiveSet = WithTop (Finset ℕ)`: a finite set of live locals, or `⊤` ("every local may be
  live", the answer for unbound labels, failed loop checks and out-of-fragment control);
* `local.get x` generates `x`; `local.set x` and `local.tee x` kill `x`; every other
  straight-line instruction is the identity. The operand stack is not a set of variables:
  stack values are handled by the dropped-producer pass `Silmaril.Wasm.Dataflow.DropElim`;
* the loop budget is `|reads body| + 1`, the bound of *Concrete Semantics* §10.4.1. Any
  budget is sound because of the check in `loopFix`.

`liveAdmin`/`liveAdminSeq` extend the analysis to administrative code (a running
configuration): values are the identity, `TRAP` is `⊥`, and `LABEL_n{cont} body` analyses
`body` with its label bound to the value of `cont` (for a block label `cont = []`, so the
label value is the value after the label; for a loop label `cont = [loop bt body]`, so it
is the loop-head value). On `expression e` this is `liveSeq`.

The meaning of a live set is `FrameRel L f f'`: same module, same number of locals, and
equal values on every local in `L` (`AgreeOn`).

Ported from an earlier development `Silmaril/Wasm/Dataflow/Liveness.lean` (and
`liveEntry` from `DeadCode.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Sets of live locals: a finite set of local indices, or `⊤`. -/
abbrev LiveSet := WithTop (Finset ℕ)

namespace LiveSet

/-- The singleton `{x}`. -/
def single (x : ℕ) : LiveSet := ((({x} : Finset ℕ)) : LiveSet)

/-- Executable membership. -/
def mem (x : ℕ) : LiveSet → Bool
  | ⊤ => true
  | (s : Finset ℕ) => decide (x ∈ s)

/-- Remove `x` (the identity on `⊤`). -/
def kill (x : ℕ) : LiveSet → LiveSet
  | ⊤ => ⊤
  | (s : Finset ℕ) => ((s.erase x : Finset ℕ) : LiveSet)

end LiveSet

/-- The transfer function of liveness on straight-line instructions. -/
def liveTransfer : Instr → LiveSet → LiveSet
  | .localGet x, L => L ⊔ LiveSet.single x.toNat
  | .localSet x, L | .localTee x, L => LiveSet.kill x.toNat L
  | _, L => L

mutual
/-- Locals read by an instruction (`rvars` of Concrete Semantics, App. A). -/
def readsInstr : Instr → Finset ℕ
  | .localGet x => {x.toNat}
  | .block _ b | .loop _ b => readsSeq b
  | .if_ _ b₁ b₂ => readsSeq b₁ ∪ readsSeq b₂
  | _ => ∅

/-- Locals read by an instruction sequence. -/
def readsSeq : List Instr → Finset ℕ
  | [] => ∅
  | i :: is => readsInstr i ∪ readsSeq is
end

/-- Liveness of locals as a structured backward analysis. -/
def liveness : Backward LiveSet where
  transfer := liveTransfer
  loopFuel _ _ body := (readsSeq body).card + 1

/-- Live locals before an instruction. -/
abbrev liveInstr (env : List LiveSet) (out : LiveSet) (i : Instr) : LiveSet :=
  liveness.instr env out i

/-- Live locals before an instruction sequence. -/
abbrev liveSeq (env : List LiveSet) (out : LiveSet) (is : List Instr) : LiveSet :=
  liveness.seq env out is

mutual
/-- Live locals before one administrative instruction. -/
def liveAdmin (env : List LiveSet) (out : LiveSet) : Admin → LiveSet
  | .plain i => liveInstr env out i
  | .ref _ => out
  | .label _ cont body => liveAdminSeq (liveSeq env out cont :: env) out body
  | .trap => ⊥
  | _ => ⊤

/-- Live locals before administrative code. -/
def liveAdminSeq (env : List LiveSet) (out : LiveSet) : List Admin → LiveSet
  | [] => out
  | a :: as => liveAdmin env (liveAdminSeq env out as) a
end

/-- Two frames agree on the locals of `L`. -/
def AgreeOn (L : LiveSet) (f f' : Frame) : Prop :=
  ∀ x : ℕ, LiveSet.single x ≤ L → f.locals[x]? = f'.locals[x]?

/-- Frames related by a live set: same module and number of locals, agreement on
the live locals. -/
structure FrameRel (L : LiveSet) (f f' : Frame) : Prop where
  module : f.module = f'.module
  length : f.locals.length = f'.locals.length
  agree : AgreeOn L f f'

/-- Live-in locals of a function body: its outer label is bound to the empty live set (the
function's results are on the stack, no local is read after it). -/
def liveEntry (e : Expr) : LiveSet := liveSeq [⊥] ⊥ e

@[simp] theorem liveAdminSeq_nil (env : List LiveSet) (out : LiveSet) :
    liveAdminSeq env out [] = out := by
  simp [liveAdminSeq]

@[simp] theorem liveAdminSeq_cons (env : List LiveSet) (out : LiveSet) (a : Admin)
    (as : List Admin) :
    liveAdminSeq env out (a :: as) = liveAdmin env (liveAdminSeq env out as) a := by
  simp [liveAdminSeq]

end Silmaril.Wasm.Dataflow
