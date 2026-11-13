module

public import Silmaril.Wasm.Dataflow.Liveness.Defs
public import Silmaril.Wasm.Dataflow.Fragment.Defs

/-!
# The fused one-pass DCE (retired): definitions

The *Optimising Compilers* DCE (notes §4, p. 10; slides Lecture 5, pp. 68–69): "if the
variable `x` is not live on exit from an instruction which assigns some value to `x`, then
the whole instruction is dead", lifted to Wasm's structured code and operand stack in one
pass with one instruction of lookahead:

* a dead `local.set x` becomes `drop`; a dead `local.tee x` is deleted;
* a removable producer immediately followed by a *dead consumer* (`drop`, or a dead
  `local.set`) is replaced by `n` `drop`s, which discard its operands.

This transform has **no correctness theorem**. Its natural step simulation is false for
both candidate relations (`Silmaril.Wasm.Dataflow.Litmus`):

* for `RelBase` (no condition on label continuations): a `br` splices a continuation into
  the outer code, where the lookahead crosses the old label boundary;
* for `Rel` (continuations `[]` or `[loop bt body]`, the only ones reduction from source
  code creates): a trap absorbs the code after it one instruction at a time, and the
  lookahead reads across the absorbed instruction.

The proved DCE is the two-pass `dce2` of `Silmaril.Wasm.Dataflow.Dce`, which also removes
strictly more (`dce2_removes_more`). The fused transform is kept as the subject of the
litmus theorems.

Ported from an earlier development `Silmaril/Wasm/Dataflow/DeadCode.lean`. The source's
lemmas for the retired simulation (`dceAdminSeq_append`, `dceAdminSeq_vals_append` and the
result lemmas) are not ported.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A consumer that discards its operand, given the live set after it: `drop`, or
a dead `local.set`. -/
def deadConsumer (live : LiveSet) : Instr → Bool
  | .drop => true
  | .localSet x => !live.mem x.toNat
  | _ => false

mutual
/-- Transform one instruction whose live-out set is `out`. -/
def dceInstr (env : List LiveSet) (out : LiveSet) : Instr → List Instr
  | .block bt body => [.block bt (dceSeq (out :: env) out body)]
  | .loop bt body => [.loop bt (dceSeq (liveInstr env out (.loop bt body) :: env) out body)]
  | .if_ bt b₁ b₂ => [.if_ bt (dceSeq (out :: env) out b₁) (dceSeq (out :: env) out b₂)]
  | .localSet x => if out.mem x.toNat then [.localSet x] else [.drop]
  | .localTee x => if out.mem x.toNat then [.localTee x] else []
  | i => [i]

/-- Transform an instruction sequence whose live-out set is `out`. -/
def dceSeq (env : List LiveSet) (out : LiveSet) : List Instr → List Instr
  | [] => []
  | [i] => dceInstr env out i
  | i :: j :: is =>
      match pureArity? i with
      | some n =>
          if deadConsumer (liveSeq env out is) j then
            List.replicate n .drop ++ dceSeq env out is
          else dceInstr env (liveSeq env out (j :: is)) i ++ dceSeq env out (j :: is)
      | none => dceInstr env (liveSeq env out (j :: is)) i ++ dceSeq env out (j :: is)
end

/-- A dead consumer in administrative code. -/
def adminDeadConsumer (live : LiveSet) : Admin → Bool
  | .plain i => deadConsumer live i
  | _ => false

mutual
/-- Transform one administrative instruction whose live-out set is `out`. -/
def dceAdmin (env : List LiveSet) (out : LiveSet) : Admin → List Admin
  | .plain i => (dceInstr env out i).map .plain
  | .label n cont body =>
      [.label n (dceSeq env out cont) (dceAdminSeq (liveSeq env out cont :: env) out body)]
  | a => [a]

/-- Transform administrative code whose live-out set is `out`. -/
def dceAdminSeq (env : List LiveSet) (out : LiveSet) : List Admin → List Admin
  | [] => []
  | [a] => dceAdmin env out a
  | a :: b :: as =>
      match adminPureArity? a with
      | some n =>
          if adminDeadConsumer (liveAdminSeq env out as) b then
            List.replicate n (.plain .drop) ++ dceAdminSeq env out as
          else dceAdmin env (liveAdminSeq env out (b :: as)) a ++ dceAdminSeq env out (b :: as)
      | none => dceAdmin env (liveAdminSeq env out (b :: as)) a ++ dceAdminSeq env out (b :: as)
end

/-- DCE of a function body: its outer label is bound to the empty live set (the
function's result values are on the stack, no local is read after it). -/
def dce (e : Expr) : Expr := dceSeq [⊥] ⊥ e

/-- The label continuations that reduction from source code creates: `[]` (a
`block`, or an `if` through `block`) and `[loop bt body]` (a `loop`). -/
def contOk : List Instr → Bool
  | [] => true
  | [.loop _ _] => true
  | _ => false

mutual
/-- Every label inside the instruction has an admissible continuation. -/
def labelsOkAdmin : Admin → Bool
  | .label _ cont body => contOk cont && labelsOkSeq body
  | _ => true

/-- Every label inside the code has an admissible continuation. -/
def labelsOkSeq : List Admin → Bool
  | [] => true
  | a :: as => labelsOkAdmin a && labelsOkSeq as
end

/-- The relation of the first skeleton, without a condition on label
continuations. `step_sim` is false for it
(`Litmus.not_step_sim_relBase`). -/
structure RelBase {H : Type} (env : List LiveSet) (out : LiveSet) (c d : Config H) : Prop where
  store : d.store = c.store
  frame : FrameRel (liveAdminSeq env out c.code) c.frame d.frame
  frag : fragAdminSeq c.code = true
  code : d.code = dceAdminSeq env out c.code

/-- The DCE simulation relation (slides p. 68): same store, frames related by the
live set of the source code, source in the fragment, label continuations of the
source admissible, target code the transform of the source code. -/
structure Rel {H : Type} (env : List LiveSet) (out : LiveSet) (c d : Config H) : Prop where
  store : d.store = c.store
  frame : FrameRel (liveAdminSeq env out c.code) c.frame d.frame
  frag : fragAdminSeq c.code = true
  labels : labelsOkSeq c.code = true
  code : d.code = dceAdminSeq env out c.code

end Silmaril.Wasm.Dataflow
