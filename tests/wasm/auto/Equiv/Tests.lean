module

public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Auto.Bridge.Thms

/-!
# Automatic equivalence: regression benchmark

Pinned segment pairs, each decided in the kernel (`decide` on the checker; no
compiled evaluation, no SAT solving). The table in `docs/projects/wasm-binaryen-tooling.md` (track
equiv) lists them with their verdicts, times and memory.

* Binaryen peephole rules of `Silmaril/Wasm/Binaryen` (`NeutralOps`, `EqzPair`,
  `DropGet`, `TeeForm`, `RseLine`), as local segment pairs, for `i32` and `i64`:
  proved by `check`.
* Algebraic identities (strength reduction, commutation, comparison orientation):
  proved by `check`.
* Wrong rewrites: refuted by a counterexample that `findCex` found and `decide`
  checks.
* Identities outside the normaliser (a shift as a division, the remainder by its
  definition): left as residual bitvector goals and closed by `omega` on `toNat`.
* The `div10` kernel (`the div10 benchmark kernel`) as
  straight-line `i64` code (hand-compiled from the C, pinned below; not clang's output):
  one residual goal, closed by `omega` on `toNat`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Equiv.Tests

open Silmaril.Wasm Silmaril.Wasm.Auto.Equiv

abbrev lg (n : Fin (2 ^ 32)) : Instr := .localGet ⟨n⟩
abbrev ls (n : Fin (2 ^ 32)) : Instr := .localSet ⟨n⟩
abbrev lte (n : Fin (2 ^ 32)) : Instr := .localTee ⟨n⟩
abbrev k (t : IntType) (c : Nat) : Instr := .intConst t (BitVec.ofNat t.width c)
abbrev bo (t : IntType) (op : IntBinOp) : Instr := .intBinOp t op
abbrev ro (t : IntType) (op : IntRelOp) : Instr := .intRelOp t op
abbrev eqz (t : IntType) : Instr := .intTestOp t .eqz

/-! ## Binaryen peephole rules -/

/-- `NeutralOps`: `x op k ⟶ x` for a neutral right operand. -/
def neutral (t : IntType) (op : IntBinOp) (c : Nat) : List Instr × List Instr :=
  ([lg 0, k t c, bo t op], [lg 0])

theorem neutral_i32 :
    [neutral .i32 .add 0, neutral .i32 .sub 0, neutral .i32 .mul 1, neutral .i32 .or 0,
      neutral .i32 .xor 0, neutral .i32 .and (2 ^ 32 - 1), neutral .i32 .shl 0,
      neutral .i32 (.shr .unsigned) 0, neutral .i32 (.shr .signed) 0, neutral .i32 .rotl 0,
      neutral .i32 .rotr 0, neutral .i32 .shl 32, neutral .i32 .rotl 64].all
      (fun p => check [.i32] [] p.1 p.2) = true := by decide

theorem neutral_i64 :
    [neutral .i64 .add 0, neutral .i64 .sub 0, neutral .i64 .mul 1, neutral .i64 .or 0,
      neutral .i64 .xor 0, neutral .i64 .and (2 ^ 64 - 1), neutral .i64 .shl 0,
      neutral .i64 (.shr .unsigned) 0, neutral .i64 (.shr .signed) 0, neutral .i64 .rotl 0,
      neutral .i64 .rotr 0, neutral .i64 .shl 64].all
      (fun p => check [.i64] [] p.1 p.2) = true := by decide

theorem neutral_add0 : SegEquiv [.i32] [] [lg 0, k .i32 0, bo .i32 .add] [lg 0] :=
  segEquiv_of_check (by decide)

/-- `EqzPair` on a boolean consumer `i32.eqz`: `eqz (eqz (eqz c)) ⟶ eqz c`. -/
theorem eqzPair : SegEquiv [] [.i32] [eqz .i32, eqz .i32, eqz .i32] [eqz .i32] :=
  segEquiv_of_check (by decide)

/-- `DropGet`: `local.get x; drop ⟶ nop`. -/
theorem dropGet : SegEquiv [.i64] [] [lg 0, .drop] [.nop] := segEquiv_of_check (by decide)

/-- `TeeForm`: `local.set x; local.get x ⟶ local.tee x`. -/
theorem teeForm : SegEquiv [.i32, .i64] [.i64] [ls 1, lg 1] [lte 1] :=
  segEquiv_of_check (by decide)

/-- `RseLine`: `local.get x; local.set x ⟶ local.get x; drop` and
`local.get x; local.tee x ⟶ local.get x`. -/
theorem rseLine : SegEquiv [.i32] [] [lg 0, ls 0] [lg 0, .drop] ∧
    SegEquiv [.i32] [] [lg 0, lte 0] [lg 0] :=
  ⟨segEquiv_of_check (by decide), segEquiv_of_check (by decide)⟩

/-! ## Algebra -/

theorem strength : SegEquiv [.i32] [] [lg 0, k .i32 8, bo .i32 .mul] [lg 0, k .i32 3, bo .i32 .shl] ∧
    SegEquiv [.i64] [] [lg 0, k .i64 5, bo .i64 .mul]
      [lg 0, k .i64 2, bo .i64 .shl, lg 0, bo .i64 .add] ∧
    SegEquiv [.i32] [] [lg 0, lg 0, bo .i32 .add] [lg 0, k .i32 1, bo .i32 .shl] :=
  ⟨segEquiv_of_check (by decide), segEquiv_of_check (by decide), segEquiv_of_check (by decide)⟩

/-- Reassociation and cancellation: `(x + 7) - (y + 7) == 0` and `x == y`. -/
theorem cancel : SegEquiv [.i32, .i32] []
    [lg 0, k .i32 7, bo .i32 .add, lg 1, k .i32 7, bo .i32 .add, bo .i32 .sub, eqz .i32]
    [lg 1, lg 0, ro .i32 .eq] := segEquiv_of_check (by decide)

/-- Comparison orientation and commuted bitwise operators. -/
theorem orient : SegEquiv [.i64, .i64] [] [lg 0, lg 1, ro .i64 (.gt .signed)]
      [lg 1, lg 0, ro .i64 (.lt .signed)] ∧
    SegEquiv [.i32, .i32] [] [lg 0, lg 1, bo .i32 .xor, lg 1, bo .i32 .and]
      [lg 1, lg 1, lg 0, bo .i32 .xor, bo .i32 .and] :=
  ⟨segEquiv_of_check (by decide), segEquiv_of_check (by decide)⟩

/-- Swapping two locals twice changes nothing. -/
theorem swap2 : SegEquiv [.i32, .i32] []
    [lg 0, lg 1, ls 0, ls 1, lg 0, lg 1, ls 0, ls 1] [] := segEquiv_of_check (by decide)

/-! ## Refutations -/

theorem sub_not_comm : ¬ SegEquiv [.i32, .i32] [] [lg 0, lg 1, bo .i32 .sub] [lg 1, lg 0, bo .i32 .sub] :=
  not_segEquiv_of_cex (envOf [0, 256]) (by decide)

theorem shr_not_sar : ¬ SegEquiv [.i32] [] [lg 0, k .i32 1, bo .i32 (.shr .unsigned)]
    [lg 0, k .i32 1, bo .i32 (.shr .signed)] :=
  not_segEquiv_of_cex (envOf [2 ^ 31]) (by decide)

/-- A wrong `NeutralOps` rule (`x * 0 ⟶ x`). -/
theorem mul0_wrong : ¬ SegEquiv [.i64] [] [lg 0, k .i64 0, bo .i64 .mul] [lg 0] :=
  not_segEquiv_of_cex (envOf [1]) (by decide)

/-! ## Residual goals -/

theorem shr1_eq_div2 (x : BitVec 32) : x >>> 1 = x / 2 := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]

theorem mod65521 (x : BitVec 32) : x % 65521 = x + 4294901775 * (x / 65521) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv]
  simp
  have := x.isLt
  omega

theorem shr_is_div : SegEquiv [.i32] [] [lg 0, k .i32 1, bo .i32 (.shr .unsigned)]
    [lg 0, k .i32 2, bo .i32 (.div .unsigned)] := by
  refine segEquiv_of_residuals (gs := [(.i32, .bin (.shr .unsigned) (.var 0) (.const 1),
    .bin (.div .unsigned) (.var 0) (.const 2))]) (by decide) ?_
  simp only [List.mem_singleton, forall_eq]
  intro ρ
  have h : ∀ x : BitVec (IntType.width .i32),
      binV .i32 (.shr .unsigned) x 1 = binV .i32 (.div .unsigned) x 2 := by
    intro x
    rw [binV_shrU, binV_divU (t := .i32) (y := 2) (by decide)]
    exact shr1_eq_div2 x
  exact h _

/-- The Adler-32 reduction: `a % 65521 = a - 65521 * (a / 65521)`. -/
theorem adler_mod : SegEquiv [.i32] [] [lg 0, k .i32 65521, bo .i32 (.rem .unsigned)]
    [lg 0, lg 0, k .i32 65521, bo .i32 (.div .unsigned), k .i32 65521, bo .i32 .mul,
      bo .i32 .sub] := by
  refine segEquiv_of_residuals (gs := [(.i32, .bin (.rem .unsigned) (.var 0) (.const 65521),
    .bin .add (.var 0) (.bin .mul (.const 4294901775)
      (.bin (.div .unsigned) (.var 0) (.const 65521))))]) (by decide) ?_
  simp only [List.mem_singleton, forall_eq]
  intro ρ
  have h : ∀ x : BitVec (IntType.width .i32), binV .i32 (.rem .unsigned) x 65521 =
      x + 4294901775 * binV .i32 (.div .unsigned) x 65521 := by
    intro x
    rw [binV_remU (t := .i32) (y := 65521) (by decide),
      binV_divU (t := .i32) (y := 65521) (by decide)]
    exact mod65521 x
  exact h _

/-! ## `div10` (straight-line `i64`) -/

/-- `div10` from `the div10 benchmark kernel`, hand-compiled: local `0`
is `x`; locals `1`–`4` hold `a_lo`, `a_hi`, `p1`, `p2` of `mulhi(x, M)`. -/
def div10Impl : List Instr :=
  [lg 0, k .i64 0xffffffff, bo .i64 .and, ls 1,
   lg 0, k .i64 32, bo .i64 (.shr .unsigned), ls 2,
   lg 1, k .i64 0xCCCCCCCC, bo .i64 .mul, ls 3,
   lg 2, k .i64 0xCCCCCCCD, bo .i64 .mul, ls 4,
   lg 2, k .i64 0xCCCCCCCC, bo .i64 .mul,
   lg 3, k .i64 32, bo .i64 (.shr .unsigned), bo .i64 .add,
   lg 4, k .i64 32, bo .i64 (.shr .unsigned), bo .i64 .add,
   lg 1, k .i64 0xCCCCCCCD, bo .i64 .mul, k .i64 32, bo .i64 (.shr .unsigned),
   lg 3, k .i64 0xffffffff, bo .i64 .and, bo .i64 .add,
   lg 4, k .i64 0xffffffff, bo .i64 .and, bo .i64 .add,
   k .i64 32, bo .i64 (.shr .unsigned),
   bo .i64 .add,
   k .i64 3, bo .i64 (.shr .unsigned)]

/-- The contract: `x / 10`. -/
def div10Spec : List Instr := [lg 0, k .i64 10, bo .i64 (.div .unsigned)]

/-- The normal form of `div10Impl`'s result (computed by `norm`, pinned). -/
def div10Lhs : Term :=
  .bin (.shr .unsigned) (.bin .add (.bin .mul (.const 3435973836)
    (.bin (.shr .unsigned) (.var 0) (.const 32))) (.bin .add (.bin (.shr .unsigned)
    (.bin .add (.bin .and (.const 4294967295) (.bin .mul (.const 3435973836)
    (.bin .and (.var 0) (.const 4294967295)))) (.bin .add (.bin .and (.const 4294967295)
    (.bin .mul (.const 3435973837) (.bin (.shr .unsigned) (.var 0) (.const 32))))
    (.bin (.shr .unsigned) (.bin .mul (.const 3435973837) (.bin .and (.var 0)
    (.const 4294967295))) (.const 32)))) (.const 32)) (.bin .add (.bin (.shr .unsigned)
    (.bin .mul (.const 3435973836) (.bin .and (.var 0) (.const 4294967295))) (.const 32))
    (.bin (.shr .unsigned) (.bin .mul (.const 3435973837) (.bin (.shr .unsigned) (.var 0)
    (.const 32))) (.const 32))))) (.const 3)

/-- The checker reduces `div10` to one residual `i64` goal. -/
theorem div10_residuals : residualsOut [.i64, .i64, .i64, .i64, .i64] [] div10Impl div10Spec =
    some [(.i64, div10Lhs, .bin (.div .unsigned) (.var 0) (.const 10))] := by decide

/-- No probe value separates the results (differential testing). -/
theorem div10_probes :
    findCexOut [.i64, .i64, .i64, .i64, .i64] [] div10Impl div10Spec = none := by
  decide

/-- The residual goal is the `div10` goal of the lemma library (`Silmaril.Wasm.Auto.Bridge`; the
same term). -/
theorem div10_goal : Goal.Holds (.i64, div10Lhs, .bin (.div .unsigned) (.var 0) (.const 10)) :=
  Silmaril.Wasm.Auto.Bridge.div10_goal

/-- **`div10` meets its contract**: the hand-compiled straight-line `i64` code computes
`x / 10`, as an equivalence of results in every context of the every-run logic. -/
theorem div10_outEquiv : OutEquiv [.i64, .i64, .i64, .i64, .i64] [] div10Impl div10Spec :=
  outEquiv_of_residualsOut div10_residuals (by
    intro g hg
    simp only [List.mem_singleton] at hg
    exact hg ▸ div10_goal)

end Silmaril.Wasm.Auto.Equiv.Tests
