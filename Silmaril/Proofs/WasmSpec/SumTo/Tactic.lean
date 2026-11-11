module

public import Silmaril.Proofs.WasmSpec.SumTo.Arith
import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `SumTo` v1, mode `tactic`

`spec_of_vcs : VCs → Spec`, by hand: enter the block, apply the loop rule
(`wp_loop_cons`) with the invariant `Inv` (the stack is empty, the locals are
`n` and `acc` with `acc + triBV n = triBV n₀`, the measure is `n`), and prove
the loop body in two cases: `inv_exit` (`n = 0`: `br_if` leaves the block and
the function returns `acc`) and `inv_step` (`n ≠ 0`: one iteration re-enters the
loop with a smaller measure). What remains are the pure verification conditions
`VCs` (initialisation, exit, preservation, decrease), which `vcs_tactic` proves
from `Arith` (`triBV_step`, `sub_one_lt`). `spec_tactic` combines them.
Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.SumTo

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- The loop body. -/
def loopBody : List Instr :=
  [.localGet ⟨0⟩, .intTestOp .i32 .eqz, .brIf ⟨1⟩,
    .localGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i32 .add, .localSet ⟨1⟩,
    .localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .sub, .localSet ⟨0⟩, .br ⟨0⟩]

/-- The quoted body: a block around the loop, then the result. -/
theorem sumFunc_body : sumFunc.body = [.block .empty [.loop .empty loopBody], .localGet ⟨1⟩] :=
  rfl

/-- One declared local, the accumulator. -/
theorem sumFunc_locals : sumFunc.locals = [.i32] := rfl

/-- `i32.eqz` on an `i32`. -/
theorem eqz32 (x : BitVec 32) : intTestOp .i32 .eqz x = bool32 (x == 0) := rfl

/-- The loop invariant, for the call from store `s₀` and instance `m` on `n₀`. -/
def Inv {H : Type} (s₀ : Store H) (m : ModuleInst) (n₀ : BitVec 32) :
    Nat → Store H → Frame → List Val → Prop := fun k s f vs =>
  s = s₀ ∧ vs = [] ∧ ∃ i acc : BitVec 32,
    f = ⟨[some (.i32 i), some (.i32 acc)], m⟩ ∧ k = i.toNat ∧ acc + triBV i = triBV n₀

/-- The pure verification conditions of the loop for the invariant `Inv`. -/
structure VCs : Prop where
  init : ∀ n₀ : BitVec 32, 0 + triBV n₀ = triBV n₀
  exit : ∀ n₀ acc : BitVec 32, acc + triBV 0 = triBV n₀ → acc = triBV n₀
  step : ∀ n₀ i acc : BitVec 32, i ≠ 0 → acc + triBV i = triBV n₀ →
    acc + i + triBV (i - 1#32) = triBV n₀
  dec : ∀ i : BitVec 32, i ≠ 0 → (i - 1#32).toNat < i.toNat

/-- `VCs` from the arithmetic of `tri`. -/
theorem vcs_tactic : VCs where
  init n₀ := BitVec.zero_add _
  exit n₀ acc hinv := by
    rw [← hinv, triBV_zero]
    exact (BitVec.add_zero acc).symm
  step n₀ i acc hi hinv := by
    rw [← hinv, triBV_step hi]
    ac_rfl
  dec _ hi := sub_one_lt hi

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- What the loop body must establish, for the invariant at measure `k`. -/
abbrev LoopPost (s₀ : Store H) (m : ModuleInst) (n₀ : BitVec 32) (k : Nat) : Post H :=
  loopPost 0 (Inv s₀ m n₀) k (seqPost P host [] (blockPost 0
    (seqPost P host (expression [.localGet ⟨1⟩])
      (funcPost P host 1 fun s' r => s' = s₀ ∧ r = [.i32 (triBV n₀)]))))

/-- The exit case: `n = 0`, so `acc = triBV n₀` is returned. -/
theorem inv_exit (vcs : VCs) {s₀ : Store H} {m : ModuleInst} {n₀ acc : BitVec 32}
    (hinv : acc + triBV 0 = triBV n₀) :
    LoopPost (P := P) (host := host) s₀ m n₀ 0 s₀ ⟨[some (.i32 0), some (.i32 acc)], m⟩
      (.br 1 []) := by
  have hacc : acc = triBV n₀ := vcs.exit n₀ acc hinv
  refine ⟨[], [], rfl, rfl, ?_⟩
  wasm_step [Idx.toNat, Fin.val_one]
  exact ⟨rfl, rfl, by rw [hacc]⟩

/-- The iteration: `n ≠ 0`, so the body adds `n` to `acc`, decrements `n` and
re-enters the loop at a smaller measure. -/
theorem inv_step (vcs : VCs) {s₀ : Store H} {m : ModuleInst} {n₀ i acc : BitVec 32}
    (hi : i ≠ 0)
    (hinv : acc + triBV i = triBV n₀) :
    WP P host s₀ ⟨[some (.i32 i), some (.i32 acc)], m⟩ (vals [] ++ expression (loopBody.drop 3))
      (LoopPost (P := P) (host := host) s₀ m n₀ i.toNat) := by
  have heq : acc + i + triBV (i - 1#32) = triBV n₀ := vcs.step n₀ i acc hi hinv
  show WP P host s₀ _ (vals [] ++ expression [.localGet ⟨1⟩, .localGet ⟨0⟩, .intBinOp .i32 .add,
      .localSet ⟨1⟩, .localGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .sub, .localSet ⟨0⟩] ++
    .plain (.br ⟨0⟩) :: []) _
  wasm_step [Idx.toNat, Fin.val_zero, Fin.val_one, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]
  exact wp_br (rest := [])
    ⟨[], [], (i - 1#32).toNat, rfl, rfl, vcs.dec i hi, rfl, rfl, i - 1#32, acc + i, rfl, rfl, heq⟩

/-- The loop body preserves the invariant or leaves the block. -/
theorem inv_body (vcs : VCs) {s₀ : Store H} {m : ModuleInst} {n₀ : BitVec 32} {k : Nat} {s : Store H}
    {f : Frame} {vs : List Val} (h : Inv s₀ m n₀ k s f vs) :
    WP P host s f (vals vs ++ expression loopBody)
      (LoopPost (P := P) (host := host) s₀ m n₀ k) := by
  obtain ⟨rfl, rfl, i, acc, rfl, rfl, hinv⟩ := h
  show WP P host s _ (vals [] ++ expression [.localGet ⟨0⟩, .intTestOp .i32 .eqz] ++
    .plain (.brIf ⟨1⟩) :: expression (loopBody.drop 3)) _
  wasm_step [Idx.toNat, Fin.val_zero, eqz32]
  refine wp_brIf_bool32 (vs := []) ?_
  cases hb : (i == 0)
  · have hi : i ≠ 0 := by simpa using hb
    simp only [Bool.false_eq_true, ite_false]
    exact inv_step vcs hi hinv
  · have hi : i = 0 := by simpa using hb
    subst hi
    simp only [ite_true]
    exact inv_exit vcs hinv

/-- **Reduction**: the loop rule with the invariant `Inv` leaves exactly `VCs`. -/
theorem spec_of_vcs (vcs : VCs) : Spec := by
  intro n H P host s m
  rw [sumFunc_body, sumFunc_locals]
  simp only [Frame.forCall, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  show WP P host s _ ([] ++ .plain (.block .empty [.loop .empty loopBody]) ::
    expression [.localGet ⟨1⟩]) _
  refine wp_block_cons (vs := []) (t₁ := []) (t₂ := []) rfl rfl ?_
  show WP P host s _ (vals [] ++ .plain (.loop .empty loopBody) :: []) _
  refine wp_loop_cons (t₁ := []) (t₂ := []) (Inv s m n) ?_ (fun _ _ _ _ h => inv_body vcs h)
    ⟨rfl, rfl, n, 0, rfl, rfl, vcs.init n⟩
  rintro k s' f vs ⟨-, rfl, -⟩
  exact ⟨rfl, rfl⟩

/-- Mode `tactic`. -/
theorem spec_tactic : Spec := spec_of_vcs vcs_tactic

end Silmaril.WasmSpec.SumTo
