module

public import Silmaril.Process.Memory

/-! # Read-after-write for the VC's memory facts

Symbolic execution leaves each store as a hypothesis `hw : m.writeBytes a bs = some m'`
(`x86_mem`). A later read of `m'` is a read of `m` when its span is disjoint from the store
(`readWith_wb_disjoint`), and returns the stored bytes when it is exactly the stored span and
readable (`readWith_wb_same`). `x86_mem` applies these by itself, discharging the
disjointness with `bv_omega`, so a read through any chain of stack pushes reaches the facts
of the segment's precondition.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift

open Silmaril.Process (Memory Byte Access)

theorem readWith_wb_disjoint {m m' : Memory} {a : Nat} {bs : List Byte}
    (hw : m.writeBytes a bs = some m') {acc : Access} {b n : Nat}
    (hd : b + n ≤ a ∨ a + bs.length ≤ b) : m'.readWith acc b n = m.readWith acc b n := by
  have w := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hw)
  exact w.readWith fun off hoff hin => by omega

theorem readWith_wb_same {m m' : Memory} {a : Nat} {bs : List Byte}
    (hw : m.writeBytes a bs = some m') {acc : Access}
    (hp : m.Permitted acc a bs.length) : m'.readWith acc a bs.length = some bs := by
  have frame := Memory.writeBytes_writesOnly hw
  apply Memory.readWith_eq
  · unfold Memory.Permitted Memory.checkSpan at hp ⊢
    simpa [Memory.permits, frame.1] using hp
  · exact fun index bound => Memory.writeBytes_get hw index bound

end Silmaril.Apps.Sha256sum.Lift
