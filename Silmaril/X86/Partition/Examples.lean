module

public import Silmaril.X86.Partition.Thms
public import Silmaril.X86.Partition.Shard.Thms

/-!
# A checked partition: a function with a cold range

Ten bytes at `0x1000`, as `gcc -O2` lays out a function `f` whose unlikely path was moved
past another function `g`:

```
1000  e8 03 00 00 00   call 0x1008      f      (hot range)
1005  eb 02            jmp  0x1009      f
1007  90               nop              padding
1008  c3               ret              g
1009  c3               ret              f      (cold range)
```

`f` is one function with two ranges (`[0x1000, 0x1007)` and `[0x1009, 0x100a)`); its `jmp`
crosses `g` without being a tail call. `check2` accepts the proposal by one kernel `decide`
(`accepted`), and so does the sharded check, one `decide` per piece (`accepted'`). The
soundness theorems then apply: for instance one `Open9` step from the `jmp` stays in `f`
(`jmp_stays`). Two wrong proposals are rejected with the offending address: dropping the
cold range from `f` (`escapingEdge`), and calling into the middle of `g`'s range set
(`callToNonEntry`).
-/

@[expose] public section

namespace Silmaril.X86.Partition.Examples

open Silmaril.X86 (MState)
open Silmaril.X86.Decompile (Region)
open Silmaril.X86.Partition.Shard (Piece Cert Below checkGlobal checkPiece accepted_of_shards)

/-- The region. -/
def region : Region :=
  ⟨0x1000, [0xe8, 0x03, 0x00, 0x00, 0x00, 0xeb, 0x02, 0x90, 0xc3, 0xc3]⟩

/-- `f` (exported, System V) and `g` (local, a compiler-chosen convention). -/
def funcs : List Fn :=
  [⟨"f", 0x1000, .sysv64, true, false⟩,
   ⟨"g", 0x1008, .inferred ⟨[], [], []⟩, false, false⟩]

/-- The proposal: `f` owns two ranges. -/
def proposal : Proposal where
  funcs := funcs
  layout := [.code 0 0x1000 0x1007, .padding 0x1007 0x1008, .code 1 0x1008 0x1009,
    .code 0 0x1009 0x100a]
  tailCalls := []
  unmodelled := []

theorem accepted : check2 region proposal 10 = none := by decide

/-- The `jmp` at `0x1005`. -/
theorem jmp_listed : (⟨0x1005, .base (.jmp8 2), 2⟩ : D8) ∈ listing region proposal 10 := by
  decide

/-- **One step of the default open machine from the `jmp` stays in `f`.** -/
theorem jmp_stays {m next : MState} (hload : region.LoadedIn m.memory)
    (hrip : m.core.rip.toNat = 0x1005) (hstep : Silmaril.X86.Open9.step m = some next) :
    InFn region proposal 10 0 next.core.rip.toNat := by
  rcases sound_step_open9 (i := 0) accepted hload jmp_listed (by decide) hrip (by decide) hstep with
    h | h | h | h
  · exact h
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact absurd h (by decide)

/-- Without the cold range, the `jmp` leaves `f`. -/
theorem reject_cold :
    check2 region { proposal with
      layout := [.code 0 0x1000 0x1007, .padding 0x1007 0x1008, .code 1 0x1008 0x100a] } 10 =
      some (.escapingEdge 0x1005 0x1009) := by decide

/-- A call must enter a function at its entry. -/
theorem reject_entry :
    check2 ⟨0x1000, [0xe8, 0x04, 0x00, 0x00, 0x00, 0xeb, 0x02, 0x90, 0xc3, 0xc3]⟩
      proposal 10 = some (.callToNonEntry 0x1000 0x1009) := by decide

/-! ## The same proposal, sharded -/

/-- One piece per slot; `f`'s bitmap has bits 0, 5 and 9, `g`'s bit 8. -/
def cert : Cert where
  pieces := [⟨0, 0x1000, 0x1007, [0xe8, 0x03, 0x00, 0x00, 0x00, 0xeb, 0x02]⟩,
    ⟨1, 0x1007, 0x1008, [0x90]⟩, ⟨2, 0x1008, 0x1009, [0xc3]⟩, ⟨3, 0x1009, 0x100a, [0xc3]⟩]
  bits := [0b1000100001, 0b100000000]

theorem cert_bytes : region.bytes = (cert.pieces.map Piece.bytes).flatten := by decide

theorem cert_global : checkGlobal region.base 10 proposal cert = none := by decide

theorem cert_piece0 : checkPiece region.base proposal cert 0 = none := by decide
theorem cert_piece1 : checkPiece region.base proposal cert 1 = none := by decide
theorem cert_piece2 : checkPiece region.base proposal cert 2 = none := by decide
theorem cert_piece3 : checkPiece region.base proposal cert 3 = none := by decide

/-- **Acceptance from the pieces**, without a whole-region `decide`. -/
theorem accepted' : check2 region proposal 10 = none :=
  accepted_of_shards cert_bytes cert_global
    ⟨⟨⟨⟨trivial, cert_piece0⟩, cert_piece1⟩, cert_piece2⟩, cert_piece3⟩ (Nat.le_refl _)

end Silmaril.X86.Partition.Examples
