module

public import Silmaril.Machine.LambdaRTLLir.Sim.Defs
public import Silmaril.Machine.LambdaRTLLir.Thms
import Silmaril.Proofs.Machine.LambdaRTLLir.Sim

/-!
# λRTL to the C-backend `Lir` machine: simulation

All statements are about the small-step machine `Silmaril.Machine.Lir.step` (C-backend `Lir`,
header `Silmaril.Machine.CBackend.Lir.Semantics.Defs`) and its behaviours `Behaves`, which are
unique (`Behaves.unique`). `AgreeOn k.fv σ fr`: the frame holds `w` exactly where the λRTL store
holds `word w`, on the free registers of the region.

* `capp_unary`, `capp_binary`, `capp_test`: the re-based instruction semantics *is* the
  C-backend `Unop.eval` / `Binop.eval` / branch test, by `rfl`.
* `prefix_sim`: the lowered `let1` prefix and the λRTL prefix fail together or succeed together,
  leaving agreeing store and frame, with the memory unchanged.
* `behaves_straight_iff` (straight-line fragment, one block ending in `ret [reg r]`): from the
  block entry, in an agreeing frame, the `Lir` behaviour is **exactly** `expect`: it returns
  `[w]` iff `k.evalObs cmodel σ = some (ℓ, word w)`, and is stuck otherwise (λRTL `none`, e.g.
  a zero divisor or an unwritten operand, or a non-word result); it never traps or diverges.
  `straight_returned_iff` and `straight_stuck_iff` spell out the two directions;
  `lowerStraight_behaves_iff` restates it for `Prog.start` of the lowered program.
* `behaves_cond_iff`: the same exact statement for a lowered prefix ending in
  `case (app test (var c)) x r₁ y r₂` with straight-line branches whose payload binders are dead.
* `absDiffC`: the `|x - y|` example of `Silmaril.Machine.LambdaRTLLir.Thms` over the C-backend operators; it lowers (`absDiffC_lowerCond`),
  evaluates to `7` on `3, 10` on both sides by kernel evaluation (`absDiffC_eval`,
  `absDiffProg_run`), and `absDiffProg_behaves` instantiates the simulation theorem.
-/

@[expose] public section

namespace Silmaril.Machine.LambdaRTLLir.Sim

open Silmaril.Machine.Lir
open Silmaril.SSA.LambdaRTL (Region Model Val upd obs)

theorem capp_unary (u : Unop) (x : Word) : capp (.unary u) (.word x) = some (.word (u.eval x)) :=
  rfl

theorem capp_binary (b : Binop) (x y : Word) :
    capp (.binary b) (.pair (.word x) (.word y)) = (b.eval x y).map .word := rfl

theorem capp_test (x : Word) :
    capp .test (.word x) = some (if x ≠ 0 then .inl .unit else .inr .unit) := rfl

variable {R L : Type} [DecidableEq R] [DecidableEq L]

omit [DecidableEq R] [DecidableEq L] in
theorem straightWord_iff (k : Region R L COp) :
    StraightWord k ↔ ∃ ℓ r, tail k = .br ℓ (.var r) := by
  unfold StraightWord
  cases h : tail k with
  | br ℓ a => cases a <;> simp [retReg]
  | _ => simp [retReg]

theorem prefix_sim (k : Region R L COp) (σ : R → LVal) (fr : Frame R) (m : Memory)
    (hag : AgreeOn k.fv σ fr) :
    (execOps (lower k) fr m = none ∧ k.evalObs cmodel σ = none) ∨
      ∃ σ' fr', execOps (lower k) fr m = some (fr', m) ∧
        k.evalObs cmodel σ = (tail k).evalObs cmodel σ' ∧ AgreeOn (tail k).fv σ' fr' :=
  Silmaril.Proofs.Machine.LambdaRTLLir.Sim.prefix_sim k σ fr m hag

omit [DecidableEq L] in
theorem expect_eq_returned (o : Option (L × LVal)) (m m' : Memory) (vs : List Word) :
    expect o m = .returned vs m' ↔ ∃ ℓ w, o = some (ℓ, .word w) ∧ [w] = vs ∧ m = m' := by
  rcases o with _ | ⟨ℓ, v⟩
  · simp [expect]
  · cases v <;> simp [expect, wordOf]

omit [DecidableEq L] in
theorem expect_eq_stuck (o : Option (L × LVal)) (m : Memory) :
    expect o m = .stuck ↔ ∀ ℓ w, o ≠ some (ℓ, .word w) := by
  rcases o with _ | ⟨ℓ, v⟩
  · simp [expect]
  · cases v <;> simp [expect, wordOf]

/-- **Straight-line simulation.** From the entry of the lowered block (any program containing it,
top-level activation), in a frame agreeing with the store on `k.fv`, the `Lir` behaviour is
exactly the one predicted by `k.evalObs`. -/
theorem behaves_straight_iff {p : Prog R} {s : State R} {k : Region R L COp} {ℓ : L} {r : R}
    {σ : R → LVal} (htail : tail k = .br ℓ (.var r))
    (hb : p.block? s.point.func s.point.label = some (retBlock k r))
    (hi : s.point.index = 0) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame) (b : Behavior) :
    Behaves p s b ↔ b = expect (k.evalObs cmodel σ) s.mem :=
  Silmaril.Proofs.Machine.LambdaRTLLir.Sim.behaves_iff_of
    (Silmaril.Proofs.Machine.LambdaRTLLir.Sim.behaves_straight htail hb hi hs hag) b

/-- Returns `[w]` exactly when λRTL exits with `word w`. -/
theorem straight_returned_iff {p : Prog R} {s : State R} {k : Region R L COp} {ℓ : L} {r : R}
    {σ : R → LVal} (htail : tail k = .br ℓ (.var r))
    (hb : p.block? s.point.func s.point.label = some (retBlock k r))
    (hi : s.point.index = 0) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame) (w : Word) :
    Behaves p s (.returned [w] s.mem) ↔ ∃ ℓ', k.evalObs cmodel σ = some (ℓ', .word w) := by
  rw [behaves_straight_iff htail hb hi hs hag, eq_comm, expect_eq_returned]
  simp

/-- Stuck exactly when λRTL fails (`none`) or exits with a non-word. -/
theorem straight_stuck_iff {p : Prog R} {s : State R} {k : Region R L COp} {ℓ : L} {r : R}
    {σ : R → LVal} (htail : tail k = .br ℓ (.var r))
    (hb : p.block? s.point.func s.point.label = some (retBlock k r))
    (hi : s.point.index = 0) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame) :
    Behaves p s .stuck ↔ ∀ ℓ' w, k.evalObs cmodel σ ≠ some (ℓ', .word w) := by
  rw [behaves_straight_iff htail hb hi hs hag, eq_comm, expect_eq_stuck]

/-- The simulation for a whole lowered program started at function `0`. -/
theorem lowerStraight_behaves_iff {params : List (Loc R)} {k : Region R L COp} {p : Prog R}
    (hp : lowerStraight params k = some p) {args : List Word} {mem : Memory} {s : State R}
    (hs : p.start 0 args mem = some s) {σ : R → LVal} (hag : AgreeOn k.fv σ s.frame)
    (b : Behavior) :
    Behaves p s b ↔ b = expect (k.evalObs cmodel σ) mem := by
  unfold lowerStraight at hp
  cases hr : retReg (tail k) with
  | none => simp [hr] at hp
  | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at hp
    subst hp
    obtain ⟨fn, fr, hfn, -, rfl⟩ := Silmaril.Proofs.Machine.LambdaRTLLir.Sim.start_eq hs
    have hfn' : fn = ⟨params, 0, [retBlock k r]⟩ := by
      simpa [straightProg, Prog.func?] using hfn.symm
    subst hfn'
    have htail : ∃ ℓ, tail k = .br ℓ (.var r) := by
      revert hr
      cases tail k with
      | br ℓ a => cases a <;> simp [retReg]
      | _ => simp [retReg]
    obtain ⟨ℓ, htail⟩ := htail
    exact behaves_straight_iff htail rfl rfl rfl hag b

/-- **Conditional simulation.** The lowered three-block program, from its entry, in a frame
agreeing with the store on `k.fv`, has exactly the behaviour predicted by `k.evalObs`. -/
theorem behaves_cond_iff {params : List (Loc R)} {k r₁ r₂ : Region R L COp} {c x y a b : R}
    {ℓ₁ ℓ₂ : L} {s : State R} {σ : R → LVal}
    (htail : tail k = .case (.app .test (.var c)) x r₁ y r₂)
    (h₁ : tail r₁ = .br ℓ₁ (.var a)) (h₂ : tail r₂ = .br ℓ₂ (.var b))
    (hx : x ∉ r₁.fv) (hy : y ∉ r₂.fv)
    (hpt : s.point = ⟨0, 0, 0⟩) (hs : s.stack = []) (hag : AgreeOn k.fv σ s.frame)
    (beh : Behavior) :
    Behaves (condProg params k c r₁ a r₂ b) s beh ↔ beh = expect (k.evalObs cmodel σ) s.mem :=
  Silmaril.Proofs.Machine.LambdaRTLLir.Sim.behaves_iff_of
    (Silmaril.Proofs.Machine.LambdaRTLLir.Sim.behaves_cond htail h₁ h₂ hx hy hpt hs hag) beh

/-! ## Example: `|x - y|` -/

/-- Branch `x < y`: `d := y - x`. -/
def absDiffLt : Region ℕ Unit COp :=
  .let1 3 (.app (.binary .sub) (.pair (.var 1) (.var 0))) (.br () (.var 3))

/-- Branch `x ≥ y`: `d := x - y`. -/
def absDiffGe : Region ℕ Unit COp :=
  .let1 3 (.app (.binary .sub) (.pair (.var 0) (.var 1))) (.br () (.var 3))

/-- The `absDiff` example over the C-backend operators (`x = 0`, `y = 1`, `c = 2`, payload `4`). -/
def absDiffC : Region ℕ Unit COp :=
  .let1 2 (.app (.binary (.cmp .ltu)) (.pair (.var 0) (.var 1)))
    (.case (.app .test (.var 2)) 4 absDiffLt 4 absDiffGe)

/-- The lowered program: parameters `x`, `y` in registers `0`, `1`. -/
def absDiffProg : Prog ℕ := condProg [.reg 0, .reg 1] absDiffC 2 absDiffLt 3 absDiffGe 3

theorem absDiffC_lowerCond : lowerCond [.reg 0, .reg 1] absDiffC = some absDiffProg := by
  decide

theorem absDiffC_eval : absDiffC.evalObs cmodel σ₀ = some ((), .word 7) := by decide

theorem absDiffProg_run :
    (absDiffProg.runMain 10 0 [3, 10] (Memory.ofList 0 [])).returnedValues? = some [7] := by
  decide

/-- The start state on `x = 3`, `y = 10`. -/
def absDiffStart (mem : Memory) : State ℕ :=
  ⟨⟨0, 0, 0⟩, (Frame.empty.set 0 3).set 1 10, [], mem⟩

theorem absDiffProg_start (mem : Memory) :
    absDiffProg.start 0 [3, 10] mem = some (absDiffStart mem) := rfl

/-- The simulation theorem instantiated: the lowered program's only behaviour on `3, 10` is to
return `[7]`, as predicted by the λRTL semantics. -/
theorem absDiffProg_behaves (mem : Memory) (beh : Behavior) :
    Behaves absDiffProg (absDiffStart mem) beh ↔ beh = .returned [7] mem := by
  have hfv : absDiffC.fv = {0, 1} := by decide
  have hag : AgreeOn absDiffC.fv σ₀ (absDiffStart mem).frame := by
    rw [hfv]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> rfl
  have hx : (4 : ℕ) ∉ absDiffLt.fv := by decide
  have hy : (4 : ℕ) ∉ absDiffGe.fv := by decide
  unfold absDiffProg
  rw [behaves_cond_iff (ℓ₁ := ()) (ℓ₂ := ()) rfl rfl rfl hx hy rfl rfl hag,
    absDiffC_eval]
  rfl

end Silmaril.Machine.LambdaRTLLir.Sim
