module

public import Silmaril.X86.FnContract.Defs

/-!
# One generic block certificate

The block certificates (`BlockCert.FunCert`, its writing-block form `FunCert.VCW`,
`BlockCert8.Cert`, `BlockCert9.FunCert9`, `BlockCert.CallCert`) all have the same shape: a function's code, a list of blocks at code
offsets, an annotation and a measure per block offset, and a verification condition "from
every annotated block, the block runs and arrives at the exit condition or at an annotated
block with a smaller measure". This module states that shape **once**, over any segment-VC
machine `I : SegVC.Isa σ` and any **block kind** `K : BlockKind I`.

* `BlockKind I`: what a kind of block supplies:
  * `B`: the block's data (a listing, a listing plus a callee, a jump node, …);
  * `check code o b`: the decidable check that `b` is what the code holds at offset `o`;
  * `WP b R s Q`: the block's weakest precondition: from `s`, running `b` reaches a state
    in `Q`, every step taken from a state satisfying the run predicate `R` (a call block's
    WP asks the callee's run to stay inside `R`; a listing's WP ignores `R`);
  * `Admits base len R`: the run predicates the kind can guarantee for code of length `len`
    at `base` (for listing kinds, every `R` containing the code region `InCode`);
  * `sound`: a checked block at the program counter of a loaded image whose WP holds runs,
    inside `R`, to a state in `Q`.
* `Cert I K`: a function certificate over blocks of kind `K`;
  `Cert.Next`, `Cert.BlockVCIn`, `Cert.VCIn R Q`, `Cert.VC Q` (the `R = True` case).

The assembly is proved once, in `Cert/Thms.lean`: `Cert.totalIn` (a run inside `R`),
`Cert.total` (`Spec.Total`) and `Cert.strict` (first return, `Spec.Strict`). The block kinds of
the existing certificates and the bridges from each existing certificate are in
`Cert/Kinds/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open FnContract (RunsIn InCode AbiEntry Spec)

/-- **A kind of block** for function certificates over the machine `I`. -/
structure BlockKind {σ : Type} (I : Isa σ) where
  /-- The data of a block. -/
  B : Type
  /-- The check that a block is what the code holds at an offset. -/
  check : List Byte → Nat → B → Bool
  /-- The block's weakest precondition for a run predicate `R` and a postcondition. -/
  WP : B → (σ → Prop) → σ → (σ → Prop) → Prop
  /-- The run predicates the kind guarantees for code at `base` of length `len`. -/
  Admits : Word → Nat → (σ → Prop) → Prop
  admits_top : ∀ base len, Admits base len fun _ => True
  /-- **Soundness**: a checked block at the program counter whose WP holds runs, inside `R`,
  to a state in `Q`. -/
  sound : ∀ {code : List Byte} {base : Word} {o : Nat} {b : B} {R : σ → Prop} {s : σ}
    {Q : σ → Prop}, check code o b = true → I.live s → Loaded (I.mem s) base code →
    (I.core s).rip = base + BitVec.ofNat 64 o → Admits base code.length R → WP b R s Q →
    ∃ t, RunsIn I R s t ∧ Q t

namespace BlockKind

variable {σ : Type} {I : Isa σ}

/-- The admissibility of a local kind: every run predicate containing the code region. -/
def Local (I : Isa σ) (base : Word) (len : Nat) (R : σ → Prop) : Prop :=
  ∀ m, InCode I base len m → R m

end BlockKind

/-- A block of a certificate: its offset in the code and its data. -/
structure CBlock {σ : Type} {I : Isa σ} (K : BlockKind I) where
  off : Nat
  blk : K.B

/-- **The generic function certificate**: the code it is loaded from, its blocks, and per
block offset an annotation (from the entry state `s0` to the current state) and a measure. -/
structure Cert {σ : Type} (I : Isa σ) (K : BlockKind I) where
  code : List Byte
  base : Word
  blocks : List (CBlock K)
  ann : Nat → σ → σ → Prop
  measure : Nat → σ → σ → Nat

namespace Cert

variable {σ : Type} {I : Isa σ} {K : BlockKind I} (F : Cert I K)

/-- Every block is checked against the code. -/
def checked : Bool := F.blocks.all fun b => K.check F.code b.off b.blk

/-- Where a block may arrive, from entry state `s0`, under the measure bound `μ`: the exit
condition `Q`, or an annotated block with a smaller measure in a memory where the code is
still loaded. -/
def Next (Q : σ → σ → Prop) (s0 : σ) (μ : Nat) (m' : σ) : Prop :=
  Q s0 m' ∨ ∃ b ∈ F.blocks, (I.core m').rip = F.base + BitVec.ofNat 64 b.off ∧
    Loaded (I.mem m') F.base F.code ∧ F.ann b.off s0 m' ∧ F.measure b.off s0 m' < μ

/-- The VC of one block, for the run predicate `R` (indexed by the entry state). -/
def BlockVCIn (R : σ → σ → Prop) (Q : σ → σ → Prop) (b : CBlock K) : Prop :=
  ∀ s0 m, F.ann b.off s0 m → I.live m →
    (I.core m).rip = F.base + BitVec.ofNat 64 b.off → Loaded (I.mem m) F.base F.code →
    K.WP b.blk (R s0) m (F.Next Q s0 (F.measure b.off s0 m))

/-- **The verification condition** for the run predicate `R`. -/
def VCIn (R : σ → σ → Prop) (Q : σ → σ → Prop) : Prop :=
  ∀ b ∈ F.blocks, F.BlockVCIn R Q b

/-- The verification condition with the trivial run predicate (total correctness). -/
def VC (Q : σ → σ → Prop) : Prop := F.VCIn (fun _ _ => True) Q

end Cert

end Silmaril.X86
