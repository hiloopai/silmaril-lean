module

public import Silmaril.X86.Partition.Shard.Defs
public import Silmaril.X86.Partition.Thms
import Silmaril.Proofs.X86.Partition.Shard.Compose

/-!
# The sharded partition check implies `check2`

`check2_of_shards`: if the global check accepts, every piece check accepts, and the
certificate's piece bytes are the region's bytes, then `check2 r p fuel = none` for every
`fuel` at least the region's length. Every theorem of `Partition/Thms.lean` (`sound_step`,
`sound_run`, `return_site`, the `noreturn` facts, `entry`, `exported_abi`, `listed`, `slot`,
`layout`) then applies to the proposal. PROVED with standard axioms; the proof is in
`Silmaril/Proofs/X86/Partition/Shard/Compose.lean`.

A fixture states the three hypotheses as separate theorems, each a kernel `decide`
(`hp` is `Below`, nested conjunctions, so that each piece is its own theorem, possibly in its
own module), and obtains `accepted : check2 region proposal fuel = none` without a
whole-image `decide`.

The certificate (pieces and bitmaps) is untrusted. It can only cause a rejection: the proof
uses nothing about it beyond what the checks verify.
-/

@[expose] public section

namespace Silmaril.X86.Partition.Shard

open Silmaril.X86.Decompile (Region)

/-- **Sharded acceptance.** -/
theorem accepted_of_shards {r : Region} {p : Proposal} {c : Cert} {len fuel : Nat}
    (hbytes : r.bytes = (c.pieces.map Piece.bytes).flatten)
    (hg : checkGlobal r.base len p c = none)
    (hp : Below (fun j => checkPiece r.base p c j = none) c.pieces.length)
    (hfuel : len ≤ fuel) : check2 r p fuel = none :=
  Proofs.X86.Partition.Shard.check2_of_shards hbytes hg hp hfuel

end Silmaril.X86.Partition.Shard
