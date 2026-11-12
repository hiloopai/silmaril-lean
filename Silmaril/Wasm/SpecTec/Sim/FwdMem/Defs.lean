module

public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs

/-!
# SpecTec ↔ Core 3.0, round 3, track fwd-mem: the byte primitives

The pinned script declares `$nbytes_(nt, c)` and `$ibytes_(N, i)` (`3.1-numerics.scalar.spectec`,
the bit/byte representation functions) `hint(builtin)` with no clause, so `callDef` always takes
the interpretation `B`'s answer. The load and store rules read and write memory through them
(`Step_read/load-num-val`, `load-pack-val`; `Step/store-num-val`, `store-pack-val`).

`nbytesCall`/`ibytesCall` interpret them by Core's little-endian encoding
`Silmaril.Wasm.Execution.Memory.encodeLE`, on the images of Core's numerals (`numV`, decoded by the
float track's `Floats.decNumType`/`Floats.decNum`) and of `iN(N)` values (`%`-wrapped naturals).
`Prims.builtins` answers both names by them (`Prims.call`).

`SliceTotal` names the property of the IL evaluator's slices that the load and store rules need at
an access ending at the last byte of memory: a slice `vs[i : n]` (and a slice update) is defined
whenever `i + n ≤ |vs|`. The evaluator as ported has the strict bound `i + n < |vs|`
(`Sem.Value.slice?`, obstruction 2), so `SliceTotal` is false until upstream item U2 is applied;
the forward lemmas therefore take either `SliceTotal` or the strict bound.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (NumVal)
open Silmaril.SpecTec.Equiv.Execution (pctV)

/-- `b*` for a Core byte string: each byte `%`-wrapped (as `memInstToValue` encodes `BYTES`). -/
def bytesV (b : ByteArray) : List Value :=
  b.data.toList.map fun c => pctV c.toNat

/-- The image of the `k`-byte little-endian encoding of `n`. -/
def leBytesV (k n : Nat) : List Value :=
  bytesV (Silmaril.Wasm.Execution.Memory.encodeLE k n)

/-- `$nbytes_(nt, c)`: the `$size(nt)/8`-byte little-endian encoding of the bits of `c`. -/
noncomputable def nbytesCall (nt c : Value) : Option Value := do
  let t ← Floats.decNumType nt
  let b ← Floats.decNum t c
  pure (.list (leBytesV (t.width / 8) b.toNat))

/-- `$ibytes_(N, i)`: the `N/8`-byte little-endian encoding of `i`. -/
def ibytesCall (N c : Value) : Option Value :=
  match N, c with
  | .num (.natN N), .case "%" (.tuple [.num (.natN n)]) => some (.list (leBytesV (N / 8) n))
  | _, _ => none

/-- **What the load and store rules need of `B`**: `$nbytes_` and `$ibytes_` are Core's
little-endian encoding on images. Proved for `Prims.builtins` (`bytesFuns_builtins`). -/
structure BytesFuns (env : Env) : Prop where
  /-- `$nbytes_(nt, c)` on the image of a numeral. -/
  nbytes : ∀ v : NumVal, Silmaril.SpecTec.Equiv.ExecNumeric.Applies env "nbytes_"
    [.val (Encode.toValue v.type), .val (numV v)] (.list (leBytesV (v.type.width / 8) v.bits.toNat))
  /-- `$ibytes_(N, i)` on a `%`-wrapped natural. -/
  ibytes : ∀ N k : Nat, Silmaril.SpecTec.Equiv.ExecNumeric.Applies env "ibytes_"
    [.val (.num (.natN N)), .val (pctV k)] (.list (leBytesV (N / 8) k))

/-- **Slices are total up to the end of the list** (`i + n ≤ |vs|`). False for the evaluator as
ported (strict bound, obstruction 2); true once upstream item U2 is applied. -/
def SliceTotal : Prop :=
  (∀ (vs : List Value) (i n : Nat), i + n ≤ vs.length →
    Value.slice? (.list vs) i n = some (.list ((vs.drop i).take n))) ∧
  (∀ (vs ws : List Value) (i n : Nat), i + n ≤ vs.length →
    Value.setSlice (.list vs) i n (.list ws) = some (.list (vs.take i ++ ws ++ vs.drop (i + n))))

end Silmaril.Wasm.SpecTec.Sim.FwdMem
