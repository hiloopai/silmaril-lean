module

public import Silmaril.X86.BlockCert.Store.Defs
public import Silmaril.X86.Open.Thms

/-!
# Function certificates with contract calls

`BlockCert.FunCert` (with writing blocks, `BlockCert.Store`) covers functions that call no
other function. The translation-validation census found that loops whose
body calls a contracted function are the largest class of loops that need an invariant.
This module adds **call blocks** to the function certificate:

* `CKind.plain L`: a straight-line listing, checked by `listingAtW` (one memory write, as the
  last instruction), as in `BlockCert.Store`;
* `CKind.call rel C`: a single `call rel32` instruction, checked by `listingAtW` (the call's
  push is its last and only write), **discharged against the callee contract `C`** (a total
  System V `FnContract` on the open machine, for instance an imported TU export such as
  libmini's `strlen`, or a separation-logic `FnSpec` through `FnSpec.Sat.toFnContract`).

A `CallCert` is a function certificate whose blocks are of either kind, with an annotation
(the cut invariant, from the entry state `m0` to the current state) and a measure per block
offset. Loop headers are ordinary annotated blocks: cutting at the loop header with a
decreasing measure gives total correctness, and **the call's own run is not measured**: the
callee's contract is total, so the caller's measure only has to decrease from the call block
to the block after the call.

* `CallCert.NextC`: where a block may arrive (the exit condition, or an annotated block of
  either kind with a smaller measure, the code still loaded);
* `CallCert.PlainVC`: the VC of a plain block (as `FunCert.BlockVCW`);
* `CallCert.CallVC`: **the call rule at the state level.** At the call site, the call
  executes (the return slot is writable); in the state after the `call` instruction the
  System V entry obligations and the callee's precondition hold; and from every result of
  the callee's contract, the caller arrives somewhere `NextC` allows.
* `CallCert.VC`: every block's VC.

The assembly (`CallCert.total`: VCs give a total `FnContract.Spec`) and the helper lemmas
that compute the state after a `call` (`runL_call`, `call_abiEntry`) and after a `push`
(`runL_push`) are in `Calls/Thms.lean`. A `call_result` lemma restating a callee's `Result`
in caller terms is not written yet.
-/

@[expose] public section

namespace Silmaril.X86.BlockCert

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (LInstr)

/-- The kind of a block of a function certificate with calls. -/
inductive CKind where
  /-- A straight-line listing (at most one write, as the last instruction). -/
  | plain (instrs : List (LInstr × Nat))
  /-- A `call rel32` discharged against the callee's contract. -/
  | call (rel : BitVec 32) (callee : FnContract Open.isa)

/-- The listing a block's kind is checked as. A call block is the one-instruction listing
`call rel32` (five bytes, `E8 cd`). -/
def CKind.listing : CKind → List (LInstr × Nat)
  | .plain L => L
  | .call rel _ => [(.ext (.call rel), 5)]

/-- A block of a function certificate with calls: its offset and kind. -/
structure CBlk where
  off : Nat
  kind : CKind

/-- **A function certificate with contract calls**: the code it is loaded from, its blocks,
and per block offset an annotation (from the entry state `m0` to the current state) and a
measure. -/
structure CallCert where
  code : List Byte
  base : Word
  blocks : List CBlk
  ann : Nat → MState → MState → Prop
  measure : Nat → MState → MState → Nat

namespace CallCert

variable (F : CallCert)

/-- Every block's listing (a call block's `call rel32`) is checked against the code by
`listingAtW`. -/
def checked : Bool := F.blocks.all fun b => listingAtW F.code b.off b.kind.listing

/-- Where a block may arrive, from entry state `m0`, under the measure bound `μ`: the exit
condition `Q`, or an annotated block (plain or call) with a smaller measure, in a memory where
the code is still loaded. -/
def NextC (Q : MState → MState → Prop) (m0 : MState) (μ : Nat) (m' : MState) : Prop :=
  Q m0 m' ∨ ∃ b ∈ F.blocks, m'.core.rip = F.base + BitVec.ofNat 64 b.off ∧
    Loaded m'.memory F.base F.code ∧ F.ann b.off m0 m' ∧ F.measure b.off m0 m' < μ

/-- The VC of a plain block. -/
def PlainVC (Q : MState → MState → Prop) (off : Nat) (L : List (LInstr × Nat)) : Prop :=
  ∀ m0 m, F.ann off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 off → Loaded m.memory F.base F.code →
    ∃ m', runL L m = some m' ∧ F.NextC Q m0 (F.measure off m0 m) m'

/-- **The VC of a call block** (the call rule on machine states). From an annotated state at
the call site: the `call` executes; in every state `m1` it executes to, the System V entry
obligations and the callee's precondition hold, and every result `t` of the callee's
contract from `m1` arrives where `NextC` allows, under the call block's measure. -/
def CallVC (Q : MState → MState → Prop) (off : Nat) (rel : BitVec 32)
    (C : FnContract Open.isa) : Prop :=
  ∀ m0 m, F.ann off m0 m →
    m.core.rip = F.base + BitVec.ofNat 64 off → Loaded m.memory F.base F.code →
    (∃ m1, runL [(.ext (.call rel), 5)] m = some m1) ∧
    ∀ m1, runL [(.ext (.call rel), 5)] m = some m1 →
      FnContract.AbiEntry m1.core m1.memory ∧ C.entry m1 ∧
      ∀ t, C.Result m1 t → F.NextC Q m0 (F.measure off m0 m) t

/-- The VC of a block, by kind. -/
def BlockVC (Q : MState → MState → Prop) (b : CBlk) : Prop :=
  match b.kind with
  | .plain L => F.PlainVC Q b.off L
  | .call rel C => F.CallVC Q b.off rel C

/-- **The verification condition** of a function certificate with calls. -/
def VC (Q : MState → MState → Prop) : Prop := ∀ b ∈ F.blocks, F.BlockVC Q b

end CallCert

end Silmaril.X86.BlockCert
