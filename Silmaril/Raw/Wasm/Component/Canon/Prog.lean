module

public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Defs

/-!
# Generic free monad `Prog` over an effect signature

This module defines the carrier of the whole Canonical ABI specification: every
function of the reference `definitions.py` (component-model revision `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
is transcribed, in later modules, as a program `Prog S α` over an explicit effect
signature `S : Sig` (the concrete signature `Eff E σ` is defined elsewhere).

* `Sig` is an effect signature: a type of operations `Op` and, for each operation,
  a type of responses `Resp o`.
* `Prog S α` is the free monad over `S`: a program either returns (`pure`) or issues an
  operation and continues with a continuation indexed by the response (`op`).
* Semantics:
  1. `Prog.run` interprets a program in any monad given a handler (`run_pure`,
     `run_bind`);
  2. `Prog.Eval H` is the relational big-step semantics given a relational handler
     `H o s r s'` over a state `σ` (`Eval.bind`, `Eval.bind_inv`);
  3. `Prog.Every P` states that every operation a program can reach satisfies `P`
     (`Every.bind`, `Every.pure`, `Every.mono`, `Every.lift`).
* `Prog` is inductive, so every program is a well-founded tree (`Prog.child_wf`); along
  any fixed choice of responses a program issues finitely many operations
  (`Prog.depthAlong`). A `Nat`-valued depth over *all* responses does not exist in
  general because a response type may be infinite (the tree is infinitely branching),
  which is why no `Nat`-valued `Prog.depth` is provided.
* List helpers `Prog.mapM`, `Prog.forM`, `Prog.foldlM` (by list recursion, equal to the
  core `List` combinators) with `Every` lemmas, and `Prog.ofExcept` / `Prog.ofOption`
  that take the failure program (`throw`) as an argument so that this module stays
  generic in how failure is signalled.

**Loops.** `Prog` has no fixpoint combinator and no general recursion: programs are
finite trees. Every `while` loop of the reference is expressed by a *late-bound machine
call* (a tail operation `call (.loop ...)` in the concrete signature) that the machine
resolves and runs under its fuel; only the machine's fuel loop recurses. Consequently
`Prog.run` is a total, structurally recursive function, and `Prog.Eval` is an inductive
relation whose derivations follow the finite program tree; whether a program relates to
any result at all depends on the handler `H` (a partial or empty handler may relate it
to none).

The program logic (Hoare triples, invariants) lives in `Canon/Prog/Properties.lean`.
Nothing here is specific to the Component Model; no upstream function is transcribed in
this file.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

universe u v w

namespace Prog

variable {S : Sig} {α β γ : Type}

/-! ## Interpretation in a monad -/

section run
variable {m : Type → Type w} [Monad m] (h : (o : S.Op) → m (S.Resp o))

theorem run_bind [LawfulMonad m] (p : Prog S α) (f : α → Prog S β) :
    (p >>= f).run h = p.run h >>= fun a => (f a).run h := by
  induction p with
  | pure a => simp only [bind_eq, pure_bind', run, LawfulMonad.pure_bind]
  | op o k ih =>
    simp only [bind_eq, op_bind, run, LawfulMonad.bind_assoc]
    congr 1
    funext r
    exact ih r

end run

/-! ## Relational big-step semantics -/

section eval
variable {σ : Type u} {H : (o : S.Op) → σ → S.Resp o → σ → Prop}

end eval

/-- For a deterministic state handler, `Eval` coincides with `run` in `StateM`. -/
theorem eval_iff_run_stateM {σ : Type} (h : (o : S.Op) → StateM σ (S.Resp o))
    (p : Prog S α) (s s' : σ) (a : α) :
    Eval (fun o s r s' => (h o).run s = (r, s')) p s a s' ↔ (p.run h).run s = (a, s') := by
  induction p generalizing s with
  | pure b =>
    simp only [eval_pure_iff, run, StateT.run_pure]
    constructor
    · rintro ⟨rfl, rfl⟩; rfl
    · intro h; cases h; exact ⟨rfl, rfl⟩
  | op o k ih =>
    simp only [eval_op_iff, run, StateT.run_bind]
    constructor
    · rintro ⟨r, s₁, hH, hk⟩
      rw [ih] at hk
      simp only [hH]
      exact hk
    · intro hrun
      refine ⟨((h o).run s).1, ((h o).run s).2, rfl, ?_⟩
      rw [ih]
      exact hrun

/-! ## Predicates over all reachable operations -/

section every
variable {P Q : S.Op → Prop}

theorem Every.mono {p : Prog S α} (hp : Every P p) (hPQ : ∀ o, P o → Q o) : Every Q p := by
  induction hp with
  | pure a => exact Every.pure a
  | op ho _ ih => exact Every.op (hPQ _ ho) ih

theorem Every.of_forall {p : Prog S α} (hP : ∀ o, P o) : Every P p := by
  induction p with
  | pure a => exact Every.pure a
  | op o k ih => exact Every.op (hP o) ih

/-- The left program of a bind satisfies every property the composition satisfies. -/
theorem Every.bind_left {p : Prog S α} {f : α → Prog S β} (h : Every P (p >>= f)) :
    Every P p := by
  induction p with
  | pure a => exact Every.pure a
  | op o k ih =>
    rw [bind_eq, op_bind, every_op_iff] at h
    exact Every.op h.1 (fun r => ih r (h.2 r))

theorem Every.and {p : Prog S α} (hP : Every P p) (hQ : Every Q p) :
    Every (fun o => P o ∧ Q o) p := by
  induction hP with
  | pure a => exact Every.pure a
  | op ho _ ih =>
    rw [every_op_iff] at hQ
    exact Every.op ⟨ho, hQ.1⟩ (fun r => ih r (hQ.2 r))

end every

/-! ## Finiteness -/

/-- Programs are well-founded trees: there is no infinite chain of continuations. -/
theorem child_wf : WellFounded (@Child S α) := by
  constructor
  intro p
  induction p with
  | pure a =>
    constructor
    intro q hq
    cases hq
  | op o k ih =>
    constructor
    intro q hq
    cases hq with
    | op _ _ r => exact ih r

/-! ## List helpers -/

theorem mapM_eq_list_mapM (f : α → Prog S β) (xs : List α) :
    mapM f xs = List.mapM f xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [mapM_cons, List.mapM_cons, ih, bind_eq, pure_eq]

theorem forM_eq_list_forM (f : α → Prog S PUnit) (xs : List α) :
    forM xs f = List.forM xs f := by
  induction xs with
  | nil => rfl
  | cons a as ih => rw [forM_cons, ih]; rfl

section everyList
variable {P : S.Op → Prop}

end everyList

/-! ## Failure adapters -/

theorem Every.ofExcept {ε : Type} {P : S.Op → Prop} {throw : ε → Prog S α}
    (h : ∀ e, Every P (throw e)) (x : Except ε α) : Every P (ofExcept throw x) := by
  cases x with
  | error e => exact h e
  | ok a => exact Every.pure a

theorem Every.ofOption {P : S.Op → Prop} {throw : Prog S α} (h : Every P throw)
    (x : Option α) : Every P (ofOption throw x) := by
  cases x with
  | none => exact h
  | some a => exact Every.pure a

end Prog

/-! ## Examples: a get/put signature over `Nat` -/

namespace ProgExamples

example : ((prog.run handler).run' 0 : Nat) = 3 := rfl

/-- `prog` never writes zero. -/
example : Prog.Every (S := cellSig) (fun o => o ≠ CellOp.put 0) prog := by
  refine Prog.Every.bind (Prog.Every.lift (fun h => ?_)) fun _ => ?_
  · cases h
  refine Prog.Every.bind (Prog.Every.lift (fun h => ?_)) fun n => ?_
  · cases h
  refine Prog.Every.bind (Prog.Every.lift (fun h => ?_)) fun _ =>
    Prog.Every.lift (fun h => ?_)
  · injection h with h; omega
  · cases h

end ProgExamples

end Silmaril.Wasm.Component.Canon
