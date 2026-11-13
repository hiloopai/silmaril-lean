module

public import Silmaril.Wasm.Dataflow.Fused.Defs
public import Silmaril.Wasm.Dataflow.DropElim.Defs

/-!
# Litmus programs for the Wasm dataflow DCE: definitions

Three refuted first statements, and the small programs of the statement checks.

* **Relational base case** (`RelBase` namespace). The fused transform's step simulation is
  false for `RelBase`, the relation without the condition that every label continuation is
  `[]` or `[loop bt body]`. Source `LABEL_1{i32.eqz} (i32.const 0; br 0); drop` (`codeA`),
  left unchanged by the transform, steps to `i32.const 0; i32.eqz; drop` (`codeB`), whose
  transform is `i32.const 0; drop` (`codeX`); the target only reaches `codeB`,
  `i32.const 1; drop` and `[]`. The `br` splices the continuation into the outer code,
  where the transform's lookahead crosses the old label boundary.
* **Trap** (`Trap` namespace). The fused simulation is false for `Rel` as well: source
  `TRAP; i32.const 1; drop` (`codeA`), whose transform is `TRAP`, steps by `trap-instrs`
  under `ctxt-instrs` to `TRAP; drop` (`codeB`), whose transform is itself, and the target
  `TRAP` does not step. A trap absorbs the code after it one instruction at a time, and the
  lookahead reads across the absorbed instruction. Both configurations are reachable from
  fragment source code (`unreachable; i32.const 1; drop`).
* **Exception** (`ThrowRef` namespace). an earlier simulation is false for the source's first
  erasure relation `OldErase`, which lets a trap but not a pending exception absorb its
  suffix: `REF.EXN_ADDR 0; THROW_REF; REF.NULL; drop` (`codeA`), erased to
  `REF.EXN_ADDR 0; THROW_REF` (`codeT`), steps by `throw_ref-instrs` to
  `REF.EXN_ADDR 0; THROW_REF; drop` (`codeB`), which `OldErase` relates only to itself.
  `Erase` (`Silmaril.Wasm.Dataflow.DropElim`) has the missing constructor.

All three are in the deterministic profile without a host, from any store and frame.

Ported from an earlier development `Silmaril/Wasm/Dataflow/{RelBaseCounterexample,
TrapCounterexample,ThrowRefCounterexample,Examples}.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The deterministic profile with a grow oracle that never fails (no `grow` runs here). -/
abbrev prof : Numerics.Profile := Numerics.Profile.deterministic fun _ _ _ _ => false

namespace RelBase

/-- `i32.eqz`. -/
abbrev eqzI : Instr := .intTestOp .i32 .eqz

/-- `br 0`. -/
abbrev br0 : Instr := .br ⟨0⟩

/-- `LABEL_1{i32.eqz} (i32.const 0; br 0); drop`. -/
def codeA : List Admin := [.label 1 [eqzI] [.plain (.intConst .i32 0), .plain br0], .plain .drop]

/-- `i32.const 0; i32.eqz; drop`. -/
def codeB : List Admin := [.plain (.intConst .i32 0), .plain eqzI, .plain .drop]

/-- `i32.const (eqz 0); drop`. -/
def codeC : List Admin := [constI32 (Numerics.intTestOp .i32 .eqz 0), .plain .drop]

/-- `i32.const 0; drop`. -/
def codeX : List Admin := [.plain (.intConst .i32 0), .plain .drop]

end RelBase

namespace Trap

/-- `i32.const 1`. -/
abbrev one : Admin := .plain (.intConst .i32 1)

/-- `TRAP; i32.const 1; drop`. -/
def codeA : List Admin := [.trap, one, .plain .drop]

/-- `TRAP; drop`. -/
def codeB : List Admin := [.trap, .plain .drop]

/-- `unreachable; i32.const 1; drop`: fragment source code that reaches `codeA`. -/
def source : Expr := [.unreachable, .intConst .i32 1, .drop]

end Trap

namespace ThrowRef

/-- The source's first erasure relation: `Erase` without absorption of the code after a
pending exception. -/
inductive OldErase : List Admin → List Admin → Prop where
  | nil : OldErase [] []
  | append {a a' b b' : List Admin} (ha : OldErase a a') (hb : OldErase b b') :
      OldErase (a ++ b) (a' ++ b')
  | keep (a : Admin) : OldErase [a] [a]
  | pure {a : Admin} {n : Nat} (h : adminPureArity? a = some n) :
      OldErase [a, .plain .drop] (List.replicate n (.plain .drop))
  | block (bt : BlockType) {b b' : List Instr} (h : OldErase (expression b) (expression b')) :
      OldErase [.plain (.block bt b)] [.plain (.block bt b')]
  | loop (bt : BlockType) {b b' : List Instr} (h : OldErase (expression b) (expression b')) :
      OldErase [.plain (.loop bt b)] [.plain (.loop bt b')]
  | if_ (bt : BlockType) {b₁ b₁' b₂ b₂' : List Instr}
      (h₁ : OldErase (expression b₁) (expression b₁'))
      (h₂ : OldErase (expression b₂) (expression b₂')) :
      OldErase [.plain (.if_ bt b₁ b₂)] [.plain (.if_ bt b₁' b₂')]
  | label (n : Nat) {cont cont' : List Instr} {body body' : List Admin}
      (hc : OldErase (expression cont) (expression cont')) (hb : OldErase body body') :
      OldErase [.label n cont body] [.label n cont' body']
  | trap (rest : List Admin) : OldErase (.trap :: rest) [.trap]

/-- The source's first pass-2 relation, with code field `OldErase`. -/
structure OldERel {H : Type} (c d : Config H) : Prop where
  store : d.store = c.store
  frame : d.frame = c.frame
  code : OldErase c.code d.code

/-- `REF.EXN_ADDR 0; THROW_REF; REF.NULL; drop`. -/
def codeA : List Admin := [.ref (.exn 0), .plain .throwRef, .ref .null, .plain .drop]

/-- `REF.EXN_ADDR 0; THROW_REF; drop`. -/
def codeB : List Admin := [.ref (.exn 0), .plain .throwRef, .plain .drop]

/-- `REF.EXN_ADDR 0; THROW_REF`. -/
def codeT : List Admin := throwing 0

end ThrowRef

/-! ## Programs of the statement checks -/

/-- `local.get 0; local.set 1; local.get 0`: local 1 is never read. -/
def deadSet : Expr := [.localGet ⟨0⟩, .localSet ⟨1⟩, .localGet ⟨0⟩]

/-- `i32.const 1; local.set 0; local.get 0`. -/
def liveSet : Expr := [.intConst .i32 1, .localSet ⟨0⟩, .localGet ⟨0⟩]

/-- `loop (local.get 1; local.set 2; local.get 0; local.set 1; local.get 2; br_if 0)`:
local 1 is read before its write, so it is live at the head; local 2 is written before
every read. -/
def loopEx : Expr :=
  [.loop .empty [.localGet ⟨1⟩, .localSet ⟨2⟩, .localGet ⟨0⟩, .localSet ⟨1⟩,
    .localGet ⟨2⟩, .brIf ⟨0⟩]]

/-- `i32.const 5; local.tee 1; drop`. -/
def deadTee : Expr := [.intConst .i32 5, .localTee ⟨1⟩, .drop]

end Silmaril.Wasm.Dataflow.Litmus
