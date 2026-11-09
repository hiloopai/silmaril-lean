module

public import Silmaril.X86.Stencils.AccumFold.Defs
import Silmaril.Proofs.X86.Stencils.AccumFold.Laws

/-!
# Accumulator-fold stencil: theorems

* `rawFold_mod`: reducing the raw sums once equals the reference that reduces after every
  byte;
* `chunked_eq_modFold`: chunked deferral (any chunk size) equals the reference;
* `rawFold_lt`: under `RawBound M N w`, a chunk of at most `N` bytes from reduced sums stays
  below `2^w` (no wrap-around in a `w`-bit register), so machine arithmetic modulo `2^w` is
  exact on the raw sums;
* `rawFold_append`, `modFold_append`: folds over concatenations (one `DO16` block is 16 raw
  steps).
-/

@[expose] public section

namespace Silmaril.X86.Stencils.AccumFold

theorem rawFold_mod (M : Nat) (s : Nat × Nat) (bs : List (BitVec 8)) :
    red M (rawFold s bs) = modFold M (red M s) bs :=
  Silmaril.Proofs.X86.Stencils.AccumFold.rawFold_mod M s bs

theorem chunked_eq_modFold (M N : Nat) (hN : 0 < N) (s : Nat × Nat) (bs : List (BitVec 8)) :
    chunked M N hN s bs = modFold M (red M s) bs :=
  Silmaril.Proofs.X86.Stencils.AccumFold.chunked_eq_modFold M N hN s bs

theorem rawFold_lt {M N w : Nat} (hB : RawBound M N w) {s : Nat × Nat} (h1 : s.1 < M)
    (h2 : s.2 < M) {bs : List (BitVec 8)} (hn : bs.length ≤ N) :
    (rawFold s bs).1 < 2 ^ w ∧ (rawFold s bs).2 < 2 ^ w :=
  Silmaril.Proofs.X86.Stencils.AccumFold.rawFold_lt hB h1 h2 hn

theorem rawFold_append (s : Nat × Nat) (xs ys : List (BitVec 8)) :
    rawFold s (xs ++ ys) = rawFold (rawFold s xs) ys := List.foldl_append

theorem modFold_append (M : Nat) (s : Nat × Nat) (xs ys : List (BitVec 8)) :
    modFold M s (xs ++ ys) = modFold M (modFold M s xs) ys := List.foldl_append

end Silmaril.X86.Stencils.AccumFold
