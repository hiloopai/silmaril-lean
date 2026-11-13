module

public import Silmaril.Wasm.Models.FunRefCloGame.Defs
public import Silmaril.Proofs.Wasm.Models.FunRefCloGame.Sim

/-!
# FunRefClo observed at first-order function type: closures that share cells, compiled

**The compiled strategy is the source strategy.** `wasmStrat_eq`: for every program that
`Prog.GOk` accepts, at every profile and for every host relation,

    wasmStrat P host p = srcStrat p.

The source strategy threads the heap through the questions, and the compiled one threads the
Wasm store, in which cells are `$cell` structures. The proof
(`Silmaril.Proofs.Wasm.Models.FunRefCloGame.Sim`) carries FunRefCloCompile's heap representation
(`HeapRep`) and a heap typing from one question to the next. Terminating steps meet
FunRefCloCompile's total specifications (`spec_all`); diverging ones have no returning invocation
(FunRefCloDiv's `div_all`).

* `mem_srcStrat_iff`, `mem_wasmStrat_iff`: the complete plays are the plays of the source runs.
* `main_ground`, `main_ground_compiled`: at ground type, the first move is `funRefCloModel`'s
  observation and what the compiled `main` returns.
* `exCounterG` (`let r = ref n in λm. r := !r + m; !r`) and `exAdderR` (`λm. n + m`): the same
  answers to every play with one call (`exCounterG_one`, `exAdderR_one`), but the counter's
  second call sees the first (`exCounterG_wasm`), and the adder's does not (`exAdderR_not`), so
  their compiled strategies differ (`strat_ne`). The ground reading cannot see either program.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Games
open Silmaril.Wasm.Models.FunRefClo (Tm Ty Prog Heap HasTy eval obsWord)
open Silmaril.Wasm.Models.FunCloGame (Op Ans cloSig toPlay toPlay_legal toPlay_prefix
  toPlay_eq_nil toPlay_ne_concat_O)
open Silmaril.Proofs.Wasm.Models.FunRefCloGame (wasmPlays_eq)
open Silmaril.Wasm.Numerics (Profile)

variable {p : Prog}

/-! ## Plays -/

/-- Source runs are closed under prefixes. -/
theorem SrcRun.of_prefix {σ : Heap} {H : List FunRefClo.Val} {t' : List (Op × Ans)}
    (hr : SrcRun p σ H t') : ∀ {t : List (Op × Ans)}, t <+: t' → SrcRun p σ H t := by
  induction hr with
  | nil σ H => intro t ht; rw [List.prefix_nil.1 ht]; exact .nil _ _
  | @cons σ σ' H o v t' hst _ ih =>
    intro t ht
    cases t with
    | nil => exact .nil _ _
    | cons x t =>
      obtain ⟨hx, ht'⟩ := List.cons_prefix_cons.1 ht
      subst hx
      exact .cons hst (ih ht')

/-- Inversion of a source run. -/
theorem SrcRun.cons_inv {σ : Heap} {H : List FunRefClo.Val} {o : Op} {a : Ans}
    {t : List (Op × Ans)} (h : SrcRun p σ H ((o, a) :: t)) :
    ∃ v σ', SrcStep p σ H o v σ' ∧ ansOf v = a ∧ SrcRun p σ' (push H v) t := by
  cases h with
  | cons hst hr => exact ⟨_, _, hst, rfl, hr⟩

/-- **The complete plays of the source strategy** are the plays of the source runs. -/
theorem mem_srcStrat_iff {t : List (Op × Ans)} : toPlay t ∈ srcStrat p ↔ SrcRun p [] [] t := by
  constructor
  · rintro ⟨-, u, hu, hpre⟩
    rcases hpre with hpre | ⟨p₀, x, he, -, hx⟩
    · rcases hu with rfl | ⟨⟨t', hr, rfl⟩, -⟩
      · rw [toPlay_eq_nil (List.prefix_nil.1 hpre)]
        exact .nil _ _
      · exact hr.of_prefix (toPlay_prefix hpre)
    · exact (toPlay_ne_concat_O he hx).elim
  · intro hr
    exact Strategy.subset_generate ⟨t, hr, rfl⟩ (toPlay_legal t)

/-! ## The compiled strategy -/

/-- **The compiled strategy is the source strategy**, at every profile and for every host. -/
theorem wasmStrat_eq (P : Profile) (host : HostSemantics Nat) (hp : p.GOk) :
    wasmStrat P host p = srcStrat p := by
  unfold wasmStrat srcStrat
  rw [wasmPlays_eq hp]

/-- **The complete plays of the compiled strategy** are the plays of the source runs. -/
theorem mem_wasmStrat_iff (P : Profile) (host : HostSemantics Nat) (hp : p.GOk)
    {t : List (Op × Ans)} : toPlay t ∈ wasmStrat P host p ↔ SrcRun p [] [] t := by
  rw [wasmStrat_eq P host hp]
  exact mem_srcStrat_iff

/-! ## Ground type -/

theorem Ty.FO_of_ground {τ : Ty} (h : τ.Ground) : τ.FO := by
  cases τ with
  | int => trivial
  | bool => trivial
  | prod => exact h.elim
  | sum => exact h.elim
  | arr => exact h.elim
  | ref => exact h.elim

/-- A program accepted by the ground reading is accepted by the game reading. -/
theorem gOk_of_ok (hp : p.Ok) : p.GOk := ⟨hp.1.1, Ty.FO_of_ground hp.1.2, hp.2⟩

/-- A value of ground type is answered by its word. -/
theorem ansOf_ground {Ψ : List Ty} {v : FunRefClo.Val} {τ : Ty} (ht : FunRefClo.ValTy Ψ v τ)
    (hg : τ.Ground) : ansOf v = .word (obsWord v) := by
  cases ht with
  | int => rfl
  | bool => rfl
  | pair => exact hg.elim
  | inl => exact hg.elim
  | inr => exact hg.elim
  | clo => exact hg.elim
  | loc => exact hg.elim

/-- **At ground type, the answer to the first `main n`** is the word of the program's value. -/
theorem main_ground (hp : p.Ok) {n : BitVec 31} {a : Ans} :
    SrcRun p [] [] [(.main n, a)] ↔ ∃ v, p.Eval n v ∧ a = .word (obsWord v) := by
  constructor
  · intro h
    obtain ⟨v, σ', ⟨k, hk⟩, rfl, -⟩ := h.cons_inv
    obtain ⟨Ψ, ht⟩ := FunRefClo.Prog.Eval.sound hp.1 ⟨k, σ', hk⟩
    exact ⟨v, ⟨k, σ', hk⟩, ansOf_ground ht hp.1.2⟩
  · rintro ⟨v, ⟨k, σ', hk⟩, rfl⟩
    obtain ⟨Ψ, ht⟩ := FunRefClo.Prog.Eval.sound hp.1 ⟨k, σ', hk⟩
    rw [← ansOf_ground ht hp.1.2]
    exact .cons ⟨k, hk⟩ (.nil _ _)

/-- **At ground type, the first move of the compiled game is the compiled `main`**. -/
theorem main_ground_compiled (P : Profile) (host : HostSemantics Nat) (hp : p.Ok)
    {n : BitVec 31} {v : FunRefClo.Val} (hv : p.Eval n v) :
    toPlay [(.main n, .word (obsWord v))] ∈ wasmStrat P host p ∧
      behaviours P host (FunRefCloCompile.storeOf p) 0 [.i32 (n.setWidth 32)] =
        {.returns [.i32 ((obsWord v).setWidth 32)]} :=
  ⟨(mem_wasmStrat_iff P host (gOk_of_ok hp)).2 ((main_ground hp).2 ⟨v, hv, rfl⟩),
    FunRefCloCompile.behaviours_compile P host hp hv⟩

/-! ## Examples: a counter and an adder -/

/-- The body of the counter closure: `r := !r + m; !r` (`m` is `var 0`, `r` is `var 2`). -/
def counterBody : Tm :=
  .let_ (.set (.var 2) (.arith .add (.get (.var 2)) (.var 0))) (.get (.var 3))

/-- `let r = ref n in λm. r := !r + m; !r`: a closure over a cell. -/
def exCounterG : Prog := ⟨.let_ (.ref (.var 0)) (.fix counterBody), .arr .int .int⟩

theorem exCounterG_ok : exCounterG.GOk :=
  ⟨.let_ (.ref (.var rfl))
    (.fix (.let_ (.set (.var rfl) (.arith .add (.get (.var rfl)) (.var rfl))) (.get (.var rfl)))),
    trivial, by unfold Prog.Fits; decide⟩

/-- `λm. n + m`. -/
def exAdderR : Prog := ⟨.fix (.arith .add (.var 2) (.var 0)), .arr .int .int⟩

theorem exAdderR_ok : exAdderR.GOk :=
  ⟨.fix (.arith .add (.var rfl) (.var rfl)), trivial, by unfold Prog.Fits; decide⟩

/-- The counter closure on `n` with its cell at location `l`. -/
def counterClo (l : Nat) (n : BitVec 31) : FunRefClo.Val :=
  .clo counterBody [.loc l, .int n]

/-- **One call**: the counter on `n`, called on `m`, answers `n + m`. -/
theorem exCounterG_one (n m : BitVec 31) :
    SrcRun exCounterG [] [] [(.main n, .fn), (.call 0 m, .word (n + m))] :=
  .cons (v := counterClo 0 n) ⟨3, rfl⟩ <|
  .cons (v := .int (n + m)) ⟨_, _, 6, rfl, rfl⟩ (.nil _ _)

/-- **One call**: the adder on `n`, called on `m`, answers `n + m`. -/
theorem exAdderR_one (n m : BitVec 31) :
    SrcRun exAdderR [] [] [(.main n, .fn), (.call 0 m, .word (n + m))] :=
  .cons (v := .clo (.arith .add (.var 2) (.var 0)) [.int n]) ⟨1, rfl⟩ <|
  .cons (v := .int (n + m)) ⟨_, _, 2, rfl, rfl⟩ (.nil _ _)

/-- The play that tells them apart: two calls on `1` after `main 0`. -/
def twicePlay (a : BitVec 31) : List (Op × Ans) :=
  [(.main 0, .fn), (.call 0 1, .word 1), (.call 0 1, .word a)]

/-- **The compiled counter remembers**: its second call answers `2`, at every profile and host;
a second counter is independent of the first. -/
theorem exCounterG_wasm (P : Profile) (host : HostSemantics Nat) :
    toPlay (twicePlay 2 ++ [(.main 10, .fn), (.call 1 5, .word 15), (.call 0 0, .word 2)]) ∈
      wasmStrat P host exCounterG :=
  (mem_wasmStrat_iff P host exCounterG_ok).2 <|
  .cons (v := counterClo 0 0) ⟨3, rfl⟩ <|
  .cons (v := .int 1) ⟨_, _, 6, rfl, rfl⟩ <|
  .cons (v := .int 2) ⟨_, _, 6, rfl, rfl⟩ <|
  .cons (v := counterClo 1 10) ⟨3, rfl⟩ <|
  .cons (v := .int 15) ⟨_, _, 6, rfl, rfl⟩ <|
  .cons (v := .int 2) ⟨_, _, 6, rfl, rfl⟩ (.nil _ _)

/-- The adder's closure on `n`. -/
def adderClo (n : BitVec 31) : FunRefClo.Val := .clo (.arith .add (.var 2) (.var 0)) [.int n]

/-- `main n` of the adder returns its closure and leaves the heap alone. -/
theorem adder_main {σ σ' : Heap} {H : List FunRefClo.Val} {n : BitVec 31} {v : FunRefClo.Val}
    (h : SrcStep exAdderR σ H (.main n) v σ') : v = adderClo n ∧ σ' = σ := by
  obtain ⟨k, hk⟩ := h
  have e : (v, σ') = (adderClo n, σ) := FunRefClo.eval_det (k' := 1) hk rfl
  simpa using e

/-- A call of the adder's closure on `m` returns `n + m` and leaves the heap alone. -/
theorem adder_call {σ σ' : Heap} {n m : BitVec 31} {v : FunRefClo.Val}
    (h : SrcStep exAdderR σ [adderClo n] (.call 0 m) v σ') : v = .int (n + m) ∧ σ' = σ := by
  obtain ⟨b, ρ, k, hH, hk⟩ := h
  have hc : FunRefClo.Val.clo b ρ = adderClo n := (Option.some.inj hH).symm
  simp only [adderClo, FunRefClo.Val.clo.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have e : (v, σ') = (.int (n + m), σ) := FunRefClo.eval_det (k' := 2) hk rfl
  simpa using e

/-- **The compiled adder does not remember**: its second call on `1` answers `1`, never `2`. -/
theorem exAdderR_not (P : Profile) (host : HostSemantics Nat) :
    toPlay (twicePlay 2) ∉ wasmStrat P host exAdderR := by
  rw [mem_wasmStrat_iff P host exAdderR_ok]
  intro h
  obtain ⟨v₁, σ₁, h₁s, -, h₁⟩ := h.cons_inv
  obtain ⟨rfl, rfl⟩ := adder_main h₁s
  obtain ⟨v₂, σ₂, h₂s, -, h₂⟩ := h₁.cons_inv
  obtain ⟨rfl, rfl⟩ := adder_call h₂s
  obtain ⟨v₃, σ₃, h₃s, hans, -⟩ := h₂.cons_inv
  obtain ⟨rfl, rfl⟩ := adder_call h₃s
  exact absurd hans (by decide)

/-- **The compiled counter and adder are told apart by the closure game**, at every profile and
for every host. -/
theorem strat_ne (P : Profile) (host : HostSemantics Nat) :
    wasmStrat P host exCounterG ≠ wasmStrat P host exAdderR := fun h =>
  exAdderR_not P host (h ▸ (wasmStrat P host exCounterG).of_prefix (exCounterG_wasm P host)
    ⟨toPlay [(.main 10, .fn), (.call 1 5, .word 15), (.call 0 0, .word 2)], by
      simp [twicePlay, toPlay]⟩)

end Silmaril.Wasm.Models.FunRefCloGame
