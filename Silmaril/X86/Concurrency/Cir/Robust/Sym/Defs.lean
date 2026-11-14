module

public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# Thread-symmetry reduction for the CIR TSO explorer

The explorer
(`Robust.tsoCheck`) stores one configuration per interleaving class of silent steps. With `N`
threads running the same code, the configurations that differ only by a renaming of the threads
are explored separately, up to `N!` copies of each. This module explores them once:

* `CSt.canon N c` sorts the threads of `c` (each with its statement, registers and store buffer)
  by a hash key (`thKey`). The result is `c` with its threads **permuted**; the sort need not be
  a canonical form (equal keys keep their order, and a hash collision only costs a missed
  identification), because soundness uses only "a permutation of `c`".
* `symStates`: the depth-first exploration of `canon ∘ ftsoSucc` from the canonical start.
* `closedSymB N S`: every element of `S` is well shaped and has no silent step, and the
  **canonical form of each of its fused TSO successors** is in `S`.
* `symCheck N fuel c0 P`: `S := symStates …` is closed in this sense, contains the canonical
  normalised start, and `P` holds of every finished, drained element.

`Robust.Sym.Thms` proves (`symCheck_sound`) that every finished, drained configuration the TSO
machine reaches from `c0` is a **thread permutation** of an element of `S` satisfying `P`. For a
property of memory alone (a counter, a flag) that is the property itself (`symCheck_mem`). The
TSO machine (`Csl.OStep`) has no thread identifiers in its rules (spawn and join are not explored
steps), so it is symmetric whatever the threads run; the reduction **pays** when threads run the
same code. As with `tsoCheck`, the search is untrusted: only the closure check matters.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Robust

open Silmaril.X86.Concurrency.Cir.Csl (Ent OCfg)

/-! ## Thread permutations -/

/-- A permutation of the thread indices that maps the first `N` onto themselves: `f` and `g`
are inverse, and `x < N ↔ f x < N`. -/
structure TPerm (N : Nat) where
  f : Nat → Nat
  g : Nat → Nat
  fg : ∀ x, f (g x) = x
  gf : ∀ x, g (f x) = x
  lt : ∀ x, x < N ↔ f x < N

/-- A buffered configuration with its threads renamed: thread `t` of `permCfg C f` is thread
`f t` of `C`. -/
def permCfg (C : OCfg) (f : Nat → Nat) : OCfg := ⟨fun t => C.ts (f t), C.mem, fun t => C.buf (f t)⟩

/-! ## Canonical forms -/

/-- The hash key of one thread: its statement, registers and buffer. -/
def thKey (p : Stmt × List Word) (b : List Ent) : Nat :=
  b.foldl (fun h e => mix h (entFp e)) (p.2.foldl (fun h w => mix h w.toNat) (mix 7 (stmtFp p.1)))

/-- Insert into a list sorted by the first component. -/
def insKey (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: l => if x.1 ≤ y.1 then x :: y :: l else y :: insKey x l

/-- Insertion sort by the first component (structural, so the kernel evaluates it). -/
def sortKey : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | x :: l => insKey x (sortKey l)

/-- The threads of `c` in the order of the index list `p`. -/
def CSt.permute (c : CSt) (p : List Nat) : CSt :=
  ⟨p.map fun i => c.ts.getD i (.skip, []), c.mem, p.map fun i => c.buf.getD i []⟩

/-- The order in which `canon` lists the threads: the indices sorted by key. -/
def canonOrder (N : Nat) (c : CSt) : List Nat :=
  (sortKey ((List.range N).map fun i => (thKey (c.ts.getD i (.skip, [])) (c.buf.getD i []), i))).map
    (·.2)

/-- **The canonical form** of a configuration of `N` threads: its threads sorted by key. -/
def CSt.canon (N : Nat) (c : CSt) : CSt := c.permute (canonOrder N c)

/-! ## The reduced exploration and check -/

/-- The canonical forms of the fused TSO successors. -/
def symSucc (N : Nat) (c : CSt) : List CSt := (ftsoSucc N c).map (CSt.canon N)

/-- The canonical normalised start. -/
def symStart (N : Nat) (c0 : CSt) : CSt := (normAll N tauFuel c0).canon N

/-- The canonical fused TSO configurations explored from `c0`. -/
def symStates (N fuel : Nat) (c0 : CSt) : List CSt :=
  let c := symStart N c0
  explore (symSucc N) fuel [c] (HTree.leaf.ins c.hash c) [c]

/-- `S` is **closed up to thread permutation**: every element is well shaped and has no silent
step, and every fused TSO successor has `N` threads and `N` buffers and its canonical form in
`S`. -/
def closedSymB (N : Nat) (S : List CSt) : Bool :=
  let T := HTree.ofList S
  S.all fun c => c.okB N && c.normalB N &&
    (ftsoSucc N c).all fun e => e.ts.length == N && e.buf.length == N && T.memB (e.canon N)

/-- **The symmetry-reduced TSO final-state check.** -/
def symCheck (N fuel : Nat) (c0 : CSt) (P : CSt → Bool) : Bool :=
  let S := symStates N fuel c0
  closedSymB N S && (HTree.ofList S).memB (symStart N c0) && c0.buf.all List.isEmpty &&
    (normAll N tauFuel c0).ts.length == N && (normAll N tauFuel c0).buf.length == N &&
    S.all fun c => !(c.doneB N && c.drainedB) || P c

end Silmaril.X86.Concurrency.Cir.Robust
