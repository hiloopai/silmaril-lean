module

public import Silmaril.Wasm.Models.FunCloGame.Defs
public import Silmaril.Proofs.Wasm.Models.FunCloGame.Sim

/-!
# FunClo observed at first-order function type: the closure game, compiled

The closure game (`Silmaril.Wasm.Models.FunCloGame.Defs`) observes a FunClo program whose result
is a first-order function by the plays in which the environment calls the closures it has been
given, named by handles.

**The compiled strategy is the source strategy.** `wasmStrat_eq`: for every program that
`Prog.GOk` accepts (a first-order result type, within the compiler's limits), at every profile
and for every host relation,

    wasmStrat P host p = srcStrat p.

The compiled strategy runs the invocations of the compiled code from `storeG p` (the store of
`moduleOf p` with the harness entry `mainR`), threading the store: closures stay in the Wasm
store as `$box` structures and the environment holds references to them. The proof
(`Silmaril.Proofs.Wasm.Models.FunCloGame.Sim`) is a simulation with the invariant that the Wasm
handles represent the source handles (FunCloCompile's `Rep`) in the current store. A returning
invocation of a terminating source step meets FunCloCompile's total specification of `apply`
(`spec_all`); a source step that diverges has no returning invocation (FunCloDiv's `div_all`,
and `mainR_div`). So the equality includes programs and closures that diverge: a diverging call
is an unanswered question on both sides.

* `toPlay_legal`, `mem_srcStrat_iff`, `mem_wasmStrat_iff`: the complete plays of either strategy
  are exactly the plays of the source runs.
* `Prog.Ok.gOk`, `main_ground`, `main_ground_compiled`: at ground type, the answer to `main n`
  is the word that `funCloModel` observes and that the compiled `main` returns
  (`FunCloCompile.behaviours_compile`): the first move of the closure game is the ground
  reading.
* Examples: `exAdder` (`λm. m + n`), `exCurry` (`λx. λy. y + (x + n)`, whose closures return
  closures: handles name both), and `exSpin` (a closure that diverges when called; `main` is
  answered, the call never is).

What is not covered: results of product or sum type (no closure-free reading of a pair holding
closures is given), and higher-order arguments (`(int → int) → int`), which need Opponent
closures, a game in which the program calls back into the environment.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCloGame

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Games
open Silmaril.Wasm.Models.FunClo (Tm Ty Prog HasTy eval obsWord)
open Silmaril.Proofs.Wasm.Models.FunCloGame (wasmPlays_eq)
open Silmaril.Wasm.Numerics (Profile)

variable {p : Prog}

/-! ## Plays -/

/-- The plays of runs are legal: questions answered in turn. -/
theorem toPlay_path : ∀ t : List (Op × Ans), Path (E := Sig.empty) (F := cloSig) .idle (toPlay t) .idle
  | [] => .nil _
  | (o, a) :: t => by
    show Path .idle (.inr (.ask o) :: .inr (.ans o a) :: toPlay t) .idle
    exact Path.cons (Step.ask (E := Sig.empty) (F := cloSig) o)
      (Path.cons (Step.ret (E := Sig.empty) (F := cloSig) o a) (toPlay_path t))

theorem toPlay_legal (t : List (Op × Ans)) : Legal (toPlay t) := ⟨_, toPlay_path t⟩

theorem toPlay_eq_nil {t : List (Op × Ans)} (h : toPlay t = []) : t = [] := by
  cases t with
  | nil => rfl
  | cons x t => obtain ⟨o, a⟩ := x; simp [toPlay] at h

/-- A prefix of the play of a run is the play of a prefix. -/
theorem toPlay_prefix : ∀ {t t' : List (Op × Ans)}, toPlay t <+: toPlay t' → t <+: t'
  | [], _, _ => List.nil_prefix
  | (o, a) :: t, [], h => by
    simp [toPlay] at h
  | (o, a) :: t, (o', a') :: t', h => by
    simp only [toPlay, List.cons_prefix_cons, Sum.inr.injEq] at h
    obtain ⟨h1, h2, ht⟩ := h
    cases h1
    cases h2
    exact List.cons_prefix_cons.2 ⟨rfl, toPlay_prefix ht⟩

/-- The last move of a nonempty play of a run is an answer, not an Opponent move. -/
theorem toPlay_last : ∀ {t : List (Op × Ans)}, t ≠ [] →
    ∃ (l : List (Move Sig.empty cloSig)) (o : Op) (a : Ans),
      toPlay t = l ++ [.inr (.ans (E := cloSig) o a)]
  | [], h => absurd rfl h
  | [(o, a)], _ => ⟨[.inr (.ask o)], o, a, rfl⟩
  | (o, a) :: (o₂, a₂) :: t, _ => by
    obtain ⟨l, o', a', hl⟩ := toPlay_last (t := (o₂, a₂) :: t) (by simp)
    refine ⟨.inr (.ask o) :: .inr (.ans (E := cloSig) o a) :: l, o', a', ?_⟩
    rw [show toPlay ((o, a) :: (o₂, a₂) :: t) =
      .inr (.ask o) :: .inr (.ans o a) :: toPlay ((o₂, a₂) :: t) from rfl, hl]
    rfl

theorem toPlay_ne_concat_O {t : List (Op × Ans)} {p₀ : List (Move Sig.empty cloSig)}
    {x : Move Sig.empty cloSig} (h : toPlay t = p₀ ++ [x]) (hx : Move.IsO x) : False := by
  by_cases ht : t = []
  · subst ht
    simp [toPlay] at h
  · obtain ⟨l, o, a, hl⟩ := toPlay_last ht
    rw [hl] at h
    have hlast := congrArg List.getLast? h
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hlast
    subst hlast
    exact hx

/-- Source runs are closed under prefixes. -/
theorem SrcRun.of_prefix {H : List FunClo.Val} {t' : List (Op × Ans)} (hr : SrcRun p H t') :
    ∀ {t : List (Op × Ans)}, t <+: t' → SrcRun p H t := by
  induction hr with
  | nil H => intro t ht; rw [List.prefix_nil.1 ht]; exact .nil _
  | @cons H o v t' hst _ ih =>
    intro t ht
    cases t with
    | nil => exact .nil _
    | cons x t =>
      obtain ⟨hx, ht'⟩ := List.cons_prefix_cons.1 ht
      subst hx
      exact .cons hst (ih ht')

/-- **The complete plays of the source strategy** are the plays of the source runs. -/
theorem mem_srcStrat_iff {t : List (Op × Ans)} : toPlay t ∈ srcStrat p ↔ SrcRun p [] t := by
  constructor
  · rintro ⟨-, u, hu, hpre⟩
    rcases hpre with hpre | ⟨p₀, x, he, -, hx⟩
    · rcases hu with rfl | ⟨⟨t', hr, rfl⟩, -⟩
      · rw [toPlay_eq_nil (List.prefix_nil.1 hpre)]
        exact .nil _
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
    {t : List (Op × Ans)} : toPlay t ∈ wasmStrat P host p ↔ SrcRun p [] t := by
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

/-- A program accepted by the ground reading is accepted by the game reading. -/
theorem gOk_of_ok (hp : p.Ok) : p.GOk := ⟨hp.1.1, Ty.FO_of_ground hp.1.2, hp.2⟩

/-- A value of ground type is answered by its word. -/
theorem ansOf_ground {v : FunClo.Val} {τ : Ty} (ht : FunClo.ValTy v τ) (hg : τ.Ground) :
    ansOf v = .word (obsWord v) := by
  cases ht with
  | int => rfl
  | bool => rfl
  | pair => exact hg.elim
  | inl => exact hg.elim
  | inr => exact hg.elim
  | clo => exact hg.elim

/-- Inversion of a source run. -/
theorem SrcRun.cons_inv {H : List FunClo.Val} {o : Op} {a : Ans} {t : List (Op × Ans)}
    (h : SrcRun p H ((o, a) :: t)) : ∃ v, SrcStep p H o v ∧ ansOf v = a ∧ SrcRun p (push H v) t := by
  cases h with
  | cons hst hr => exact ⟨_, hst, rfl, hr⟩

/-- **At ground type, the answer to `main n`** is the word of the program's value. -/
theorem main_ground (hp : p.Ok) {n : BitVec 31} {a : Ans} :
    SrcRun p [] [(.main n, a)] ↔ ∃ v, p.Eval n v ∧ a = .word (obsWord v) := by
  constructor
  · intro h
    obtain ⟨v, hst, rfl, -⟩ := h.cons_inv
    exact ⟨v, hst, ansOf_ground (FunClo.Prog.Eval.sound hp.1 hst) hp.1.2⟩
  · rintro ⟨v, hv, rfl⟩
    rw [← ansOf_ground (FunClo.Prog.Eval.sound hp.1 hv) hp.1.2]
    exact .cons hv (.nil _)

/-- **At ground type, the first move of the compiled closure game is the compiled `main`**: the
play `main n ↦ word w` is in the compiled strategy, and the compiled `main` returns `w`. -/
theorem main_ground_compiled (P : Profile) (host : HostSemantics Nat) (hp : p.Ok)
    {n : BitVec 31} {v : FunClo.Val} (hv : p.Eval n v) :
    toPlay [(.main n, .word (obsWord v))] ∈ wasmStrat P host p ∧
      behaviours P host (FunCloCompile.storeOf p) 0 [.i32 (n.setWidth 32)] =
        {.returns [.i32 ((obsWord v).setWidth 32)]} :=
  ⟨(mem_wasmStrat_iff P host (gOk_of_ok hp)).2 (main_ground hp |>.2 ⟨v, hv, rfl⟩),
    FunCloCompile.behaviours_compile P host hp hv⟩

/-! ## Examples -/

/-- `λm. m + n`: an adder closure over the argument. -/
def exAdder : Prog := ⟨.fix (.arith .add (.var 0) (.var 2)), .arr .int .int⟩

theorem exAdder_ok : exAdder.GOk :=
  ⟨.fix (.arith .add (.var rfl) (.var rfl)), trivial, by unfold Prog.Fits; decide⟩

/-- `main 5` is answered by a closure; calling it on `3` gives `8`. -/
theorem exAdder_run : SrcRun exAdder [] [(.main 5, .fn), (.call 0 3, .word 8)] :=
  .cons (v := .clo (.arith .add (.var 0) (.var 2)) [.int 5]) ⟨1, rfl⟩
    (.cons (v := .int 8) ⟨_, _, 2, rfl, rfl⟩ (.nil _))

/-- The compiled adder plays the same play, at every profile and for every host. -/
theorem exAdder_wasm (P : Profile) (host : HostSemantics Nat) :
    toPlay [(.main 5, .fn), (.call 0 3, .word 8)] ∈ wasmStrat P host exAdder :=
  (mem_wasmStrat_iff P host exAdder_ok).2 exAdder_run

/-- `λx. λy. y + (x + n)`: a curried adder, whose closures return closures. -/
def exCurry : Prog :=
  ⟨.fix (.fix (.arith .add (.var 0) (.arith .add (.var 2) (.var 4)))),
    .arr .int (.arr .int .int)⟩

theorem exCurry_ok : exCurry.GOk :=
  ⟨.fix (.fix (.arith .add (.var rfl) (.arith .add (.var rfl) (.var rfl)))), trivial,
    by unfold Prog.Fits; decide⟩

/-- The inner body of `exCurry`. -/
def curryIn : Tm := .arith .add (.var 0) (.arith .add (.var 2) (.var 4))

/-- The outer closure of `exCurry` on `n`. -/
def curryOut (n : BitVec 31) : FunClo.Val := .clo (.fix curryIn) [.int n]

/-- The play: `main 1` gives handle `0`; `call 0 10` gives handle `1` (`λy. y + 11`); calling
it on `100` gives `111`; `call 0 20` gives handle `2` (`λy. y + 21`); calling handle `2` on `7`
gives `28`, and handle `1` is still there: on `1` it gives `12`. -/
def curryPlay : List (Op × Ans) :=
  [(.main 1, .fn), (.call 0 10, .fn), (.call 1 100, .word 111), (.call 0 20, .fn),
    (.call 2 7, .word 28), (.call 1 1, .word 12)]

theorem exCurry_run : SrcRun exCurry [] curryPlay :=
  .cons (v := curryOut 1) ⟨1, rfl⟩ <|
  .cons (v := .clo curryIn [.int 10, curryOut 1, .int 1]) ⟨_, _, 1, rfl, rfl⟩ <|
  .cons (v := .int 111) ⟨_, _, 3, rfl, rfl⟩ <|
  .cons (v := .clo curryIn [.int 20, curryOut 1, .int 1]) ⟨_, _, 1, rfl, rfl⟩ <|
  .cons (v := .int 28) ⟨_, _, 3, rfl, rfl⟩ <|
  .cons (v := .int 12) ⟨_, _, 3, rfl, rfl⟩ (.nil _)

/-- The compiled curried adder plays the same play, at every profile and for every host. -/
theorem exCurry_wasm (P : Profile) (host : HostSemantics Nat) :
    toPlay curryPlay ∈ wasmStrat P host exCurry :=
  (mem_wasmStrat_iff P host exCurry_ok).2 exCurry_run

/-- `fix f x. f x` as a result: a closure that diverges when called. -/
def exSpin : Prog := ⟨.fix FunCloDiv.loopBody, .arr .int .int⟩

theorem exSpin_ok : exSpin.GOk :=
  ⟨.fix (.app (.var rfl) (.var rfl)), trivial, by unfold Prog.Fits; decide⟩

/-- `main 0` is answered by a closure. -/
theorem exSpin_main (P : Profile) (host : HostSemantics Nat) :
    toPlay [(.main 0, .fn)] ∈ wasmStrat P host exSpin :=
  (mem_wasmStrat_iff P host exSpin_ok).2
    (.cons (v := .clo FunCloDiv.loopBody [.int 0]) ⟨1, rfl⟩ (.nil _))

/-- **A call of the spinning closure is never answered** by the compiled code, at any profile
and for any host: no run of `apply` on it returns. -/
theorem exSpin_call (P : Profile) (host : HostSemantics Nat) (m : BitVec 31) (a : Ans) :
    toPlay [(.main 0, .fn), (.call 0 m, a)] ∉ wasmStrat P host exSpin := by
  rw [mem_wasmStrat_iff P host exSpin_ok]
  intro h
  obtain ⟨v, ⟨k₀, hk₀⟩, -, h'⟩ := h.cons_inv
  obtain ⟨u, ⟨b, ρ, k, hH, hev⟩, -, -⟩ := h'.cons_inv
  have hv : v = .clo FunCloDiv.loopBody [.int 0] := by
    have h1 : FunClo.eval 1 [.int 0] exSpin.body = some (.clo FunCloDiv.loopBody [.int 0]) :=
      rfl
    exact FunClo.eval_det hk₀ h1
  subst hv
  simp only [push, List.nil_append, List.getElem?_cons_zero, Option.some.injEq,
    FunClo.Val.clo.injEq] at hH
  obtain ⟨rfl, rfl⟩ := hH
  rw [FunCloDiv.loopBody_div] at hev
  exact absurd hev (by simp)

end Silmaril.Wasm.Models.FunCloGame
