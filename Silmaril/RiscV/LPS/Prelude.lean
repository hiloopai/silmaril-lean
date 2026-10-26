module

public import Mathlib.Data.Num.Lemmas

/-!
# LPS RISC-V prelude: bitvector helpers and a radix-tree map

Agentic (hand) translation of `theories/Riscv/Prelude.v` from
theorem-labs/rocq-linux-process-semantics ("LPS"), commit
`f1006fe8178338a499b5e5c41be83006c4edd058` (MIT licence; see
`Silmaril/RiscV/LPS/LICENSE-LPS`). Every definition names its Rocq original; the full
correspondence table is in `docs/RiscVLPS.md`.

Representation choices (applied throughout `Silmaril.RiscV.LPS`):

* stdpp's `bv n` (with `n : N`) is Lean's `BitVec n` (with `n : Nat`);
* `bv_unsigned` is `BitVec.toNat`, `bv_signed` is `BitVec.toInt`, `Z_to_bv n z` is
  `BitVec.ofInt n z`, `bv_extract lo len` is `BitVec.extractLsb' lo len` and
  `bv_concat n hi lo` is `hi ++ lo` (the widths always add up to `n` in LPS);
* `bv_sign_extend m` is `BitVec.signExtend m` and `bv_zero_extend m` is
  `BitVec.setWidth m`; both are, like stdpp's, `ofInt`/`ofNat` of the source value;
* Rocq's `positive` is Mathlib's `PosNum`.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

/-- `word` (Prelude.v). -/
abbrev Word := BitVec 64
/-- `reg` (Prelude.v). -/
abbrev Reg := BitVec 5

/-- `bits lo len w`: bits `[lo, lo + len)` of `w` (Prelude.v `bits`). -/
def bits {n : Nat} (lo len : Nat) (w : BitVec n) : BitVec len := w.extractLsb' lo len

/-- Sign extension (or truncation) to `m` bits (Prelude.v `sext`). -/
def sext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := b.signExtend m

/-- Zero extension (or truncation) to `m` bits (Prelude.v `zext`). -/
def zext {n : Nat} (m : Nat) (b : BitVec n) : BitVec m := b.setWidth m

/-- Untyped bit test of the unsigned value (Prelude.v `bit`). -/
def bit {n : Nat} (i : Nat) (w : BitVec n) : Bool := w.toNat.testBit i

/-! ## Signedness-explicit wrappers (Prelude.v) -/

/-- Signed less-than (`bv_lts`). -/
def ltS {n : Nat} (a b : BitVec n) : Bool := decide (a.toInt < b.toInt)
/-- Unsigned less-than (`bv_ltu`). -/
def ltU {n : Nat} (a b : BitVec n) : Bool := decide (a.toNat < b.toNat)
/-- Equality of unsigned values (`bv_eqb`). -/
def eqB {n : Nat} (a b : BitVec n) : Bool := a.toNat == b.toNat

/-- High half of the exact signed × signed product (`bv_mulhss`): the exact product shifted
right arithmetically (floor) by `n`. -/
def mulhSS {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n (Int.fdiv (a.toInt * b.toInt) (2 ^ n))
/-- High half of the exact signed × unsigned product (`bv_mulhsu`). -/
def mulhSU {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n (Int.fdiv (a.toInt * (b.toNat : Int)) (2 ^ n))
/-- High half of the exact unsigned × unsigned product (`bv_mulhuu`). -/
def mulhUU {n : Nat} (a b : BitVec n) : BitVec n :=
  BitVec.ofInt n (Int.fdiv ((a.toNat : Int) * (b.toNat : Int)) (2 ^ n))

/-! ## Radix-tree map keyed by `PosNum` (Prelude.v `tree`)

Rocq's `positive` is Mathlib's `PosNum`: `xH` is `one`, `xO` is `bit0` and `xI` is
`bit1`. Both `get` and `set` are structural, so lookups reduce in the kernel. -/

/-- `tree A` (Prelude.v). -/
inductive Tree (α : Type) where
  | empty
  | node (l : Tree α) (v : Option α) (r : Tree α)
  deriving DecidableEq, Repr

namespace Tree

variable {α : Type}

/-- `tget` (Prelude.v). -/
def get : PosNum → Tree α → Option α
  | _, .empty => none
  | .one, .node _ v _ => v
  | .bit0 p, .node l _ _ => get p l
  | .bit1 p, .node _ _ r => get p r

/-- `tset` (Prelude.v). -/
def set : PosNum → α → Tree α → Tree α
  | .one, x, .empty => .node .empty (some x) .empty
  | .bit0 p, x, .empty => .node (set p x .empty) none .empty
  | .bit1 p, x, .empty => .node .empty none (set p x .empty)
  | .one, x, .node l _ r => .node l (some x) r
  | .bit0 p, x, .node l v r => .node (set p x l) v r
  | .bit1 p, x, .node l v r => .node l v (set p x r)

/-- `tget_tset_same` (Prelude.v). -/
theorem get_set_same (p : PosNum) (x : α) (t : Tree α) : get p (set p x t) = some x := by
  induction p generalizing t with
  | one => cases t <;> rfl
  | bit0 p ih => cases t <;> simp [set, get, ih]
  | bit1 p ih => cases t <;> simp [set, get, ih]

@[simp] theorem get_empty (p : PosNum) : get p (Tree.empty : Tree α) = none := by
  cases p <;> rfl

/-- `tget_tset_other` (Prelude.v). -/
theorem get_set_other (p q : PosNum) (x : α) (t : Tree α) (hne : p ≠ q) :
    get q (set p x t) = get q t := by
  induction p generalizing q t with
  | one => cases q <;> cases t <;> simp_all [set, get]
  | bit0 p ih =>
    cases q with
    | bit0 q => cases t <;> simp [set, get, ih q _ (fun h => hne (by rw [h]))]
    | _ => cases t <;> simp [set, get]
  | bit1 p ih =>
    cases q with
    | bit1 q => cases t <;> simp [set, get, ih q _ (fun h => hne (by rw [h]))]
    | _ => cases t <;> simp [set, get]

end Tree

/-- Map a bitvector key into `PosNum` (Prelude.v `bv_key`: `Z.to_pos (bv_unsigned b + 1)`). -/
def bvKey {n : Nat} (b : BitVec n) : PosNum := PosNum.ofNatSucc b.toNat

theorem ofNatSucc_toNat (k : Nat) : ((PosNum.ofNatSucc k : PosNum) : Nat) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [PosNum.ofNatSucc, PosNum.succ_to_nat, ih]

/-- `bv_key_inj` (Prelude.v). -/
theorem bvKey_inj {n : Nat} {b₁ b₂ : BitVec n} (h : bvKey b₁ = bvKey b₂) : b₁ = b₂ := by
  have := congrArg (fun p : PosNum => (p : Nat)) h
  simp only [bvKey, ofNatSucc_toNat] at this
  exact BitVec.eq_of_toNat_eq (by omega)

/-- `bvmap n A` (Prelude.v): a radix tree keyed by `n`-bit vectors. -/
abbrev BvMap (_n : Nat) (α : Type) := Tree α

namespace BvMap

variable {n : Nat} {α : Type}

/-- `bvmap_get` (Prelude.v). -/
def get (k : BitVec n) (m : BvMap n α) : Option α := Tree.get (bvKey k) m
/-- `bvmap_set` (Prelude.v). -/
def set (k : BitVec n) (x : α) (m : BvMap n α) : BvMap n α := Tree.set (bvKey k) x m
/-- `bvmap_empty` (Prelude.v). -/
def empty : BvMap n α := Tree.empty

/-- `bvmap_get_set_same` (Prelude.v). -/
theorem get_set_same (k : BitVec n) (x : α) (m : BvMap n α) : get k (set k x m) = some x :=
  Tree.get_set_same _ _ _

/-- `bvmap_get_set_other` (Prelude.v). -/
theorem get_set_other {k k' : BitVec n} (x : α) (m : BvMap n α) (h : k ≠ k') :
    get k' (set k x m) = get k' m :=
  Tree.get_set_other _ _ _ _ (fun e => h (bvKey_inj e))

end BvMap

end Silmaril.RiscV.LPS
