module

public import Silmaril.Wasm.Dataflow.Liveness.Defs
public import Silmaril.Wasm.Dataflow.Fragment.Defs

/-!
# an earlier step of the two-pass DCE, dead stores of locals: definitions

The first pass of `Silmaril.Wasm.Dataflow.Dce` removes only the stores that liveness
(`Silmaril.Wasm.Dataflow.Liveness`) proves dead:

* a dead `local.set x` (`x` not live after it) becomes `drop`;
* a dead `local.tee x` is deleted (its operand stays on the stack).

The pass has **no lookahead**: each instruction is rewritten on its own, given the live set
after it. Its administrative form is therefore a homomorphism for `++`
(`localDceAdminSeq_append`), which is what the context rule `Step/ctxt-instrs` needs, and a
branch that splices a label continuation into the outer code meets the same transform on
both sides of the old label boundary. Liveness is computed on the *source*; the pass never
re-analyses its own output.

`LRel` is the simulation relation of `Silmaril.Wasm.Dataflow.LocalDce.Thms`: same store,
frames related by the live set of the source code (`FrameRel`), source in the fragment, and
target code related by `LCode`. The only source step that is not matched in lock-step is a
dead `local.tee x`: `v; local.tee x` steps to `v; v; local.set x`, whose transform is
`v; v; drop`, while the target is already at `v`. The source is then one step behind, with
a *pending* dead store `v; local.set x` at its first non-value position, which `LCode.pend`
records.

Ported from an earlier development `Silmaril/Wasm/Dataflow/LocalDce.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

mutual
/-- an earlier step on one instruction whose live-out set is `out`. -/
def localDceInstr (env : List LiveSet) (out : LiveSet) : Instr → List Instr
  | .block bt body => [.block bt (localDceSeq (out :: env) out body)]
  | .loop bt body =>
      [.loop bt (localDceSeq (liveInstr env out (.loop bt body) :: env) out body)]
  | .if_ bt b₁ b₂ =>
      [.if_ bt (localDceSeq (out :: env) out b₁) (localDceSeq (out :: env) out b₂)]
  | .localSet x => if out.mem x.toNat then [.localSet x] else [.drop]
  | .localTee x => if out.mem x.toNat then [.localTee x] else []
  | i => [i]

/-- an earlier step on an instruction sequence whose live-out set is `out`: each
instruction is rewritten given the live set after it, without lookahead. -/
def localDceSeq (env : List LiveSet) (out : LiveSet) : List Instr → List Instr
  | [] => []
  | i :: is => localDceInstr env (liveSeq env out is) i ++ localDceSeq env out is
end

mutual
/-- an earlier step on one administrative instruction whose live-out set is `out`. -/
def localDceAdmin (env : List LiveSet) (out : LiveSet) : Admin → List Admin
  | .plain i => (localDceInstr env out i).map .plain
  | .label n cont body =>
      [.label n (localDceSeq env out cont)
        (localDceAdminSeq (liveSeq env out cont :: env) out body)]
  | a => [a]

/-- an earlier step on administrative code whose live-out set is `out`. -/
def localDceAdminSeq (env : List LiveSet) (out : LiveSet) : List Admin → List Admin
  | [] => []
  | a :: as => localDceAdmin env (liveAdminSeq env out as) a ++ localDceAdminSeq env out as
end

/-- an earlier step on a function body: the outer label is bound to the empty live set. -/
def localDce (e : Expr) : Expr := localDceSeq [⊥] ⊥ e

@[simp] theorem localDceSeq_nil (env : List LiveSet) (out : LiveSet) :
    localDceSeq env out [] = [] := by
  simp [localDceSeq]

@[simp] theorem localDceSeq_cons (env : List LiveSet) (out : LiveSet) (i : Instr)
    (is : List Instr) :
    localDceSeq env out (i :: is) =
      localDceInstr env (liveSeq env out is) i ++ localDceSeq env out is := by
  simp [localDceSeq]

@[simp] theorem localDceAdminSeq_nil (env : List LiveSet) (out : LiveSet) :
    localDceAdminSeq env out [] = [] := by
  simp [localDceAdminSeq]

@[simp] theorem localDceAdminSeq_cons (env : List LiveSet) (out : LiveSet) (a : Admin)
    (as : List Admin) :
    localDceAdminSeq env out (a :: as) =
      localDceAdmin env (liveAdminSeq env out as) a ++ localDceAdminSeq env out as := by
  simp [localDceAdminSeq]

variable {H : Type}

/-- Target code for source code under the transform of the source code
(`clean`), or the transform with one *pending* dead store `w; local.set x` at the
first non-value position removed (`pend`, the state after the first step of a
dead `local.tee x`), possibly inside the body of a label at the first non-value
position (`label`). -/
inductive LCode : List LiveSet → LiveSet → List Admin → List Admin → Prop where
  | clean {env : List LiveSet} {out : LiveSet} (c : List Admin) :
      LCode env out c (localDceAdminSeq env out c)
  | pend {env : List LiveSet} {out : LiveSet} (vs : List Val) (w : Val) (x : LocalIdx)
      (rest : List Admin) (hx : (liveAdminSeq env out rest).mem x.toNat = false) :
      LCode env out (vals vs ++ w.toAdmin :: .plain (.localSet x) :: rest)
        (vals vs ++ localDceAdminSeq env out rest)
  | label {env : List LiveSet} {out : LiveSet} (vs : List Val) (n : Nat) (cont : List Instr)
      {body bd : List Admin} (rest : List Admin)
      (h : LCode (liveSeq env (liveAdminSeq env out rest) cont :: env)
        (liveAdminSeq env out rest) body bd) :
      LCode env out (vals vs ++ .label n cont body :: rest)
        (vals vs ++ .label n (localDceSeq env (liveAdminSeq env out rest) cont) bd ::
          localDceAdminSeq env out rest)

/-- The pass-1 simulation relation: same store, frames related by the live set of
the source code, source in the fragment, target code related by `LCode`. -/
structure LRel (env : List LiveSet) (out : LiveSet) (c d : Config H) : Prop where
  store : d.store = c.store
  frame : FrameRel (liveAdminSeq env out c.code) c.frame d.frame
  frag : fragAdminSeq c.code = true
  code : LCode env out c.code d.code

/-- Code made of values, `throw_ref`, `return` and `TRAP` (results and pending
returns). -/
def Inert (c : List Admin) : Prop :=
  ∀ a ∈ c, a.val? ≠ none ∨ a = .plain .throwRef ∨ a = .plain .return_ ∨ a = .trap

end Silmaril.Wasm.Dataflow
