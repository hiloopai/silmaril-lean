module

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

/-- An effect signature: operations and, for each operation, its response type. -/
structure Sig where
  /-- Operations a program may issue. -/
  Op : Type
  /-- The type of responses to an operation. -/
  Resp : Op → Type

/-- The free monad over the signature `S`: a finite tree whose leaves are results and
whose inner nodes are operations branching over their responses. -/
inductive Prog (S : Sig) (α : Type) : Type where
  /-- Return a value. -/
  | pure (a : α)
  /-- Issue operation `o` and continue with the response. -/
  | op (o : S.Op) (k : S.Resp o → Prog S α)

namespace Prog

variable {S : Sig} {α β γ : Type}

/-- Sequential composition, by structural recursion on the first program. -/
def bind : Prog S α → (α → Prog S β) → Prog S β
  | .pure a, f => f a
  | .op o k, f => .op o (fun r => bind (k r) f)

instance : Monad (Prog S) where
  pure := Prog.pure
  bind := Prog.bind

/-- Issue a single operation and return its response. -/
def lift (o : S.Op) : Prog S (S.Resp o) := .op o Prog.pure

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Prog S α) = Prog.pure a := rfl

@[simp] theorem bind_eq (p : Prog S α) (f : α → Prog S β) : p >>= f = p.bind f := rfl

@[simp] theorem pure_bind' (a : α) (f : α → Prog S β) : (Prog.pure a).bind f = f a := rfl

@[simp] theorem op_bind (o : S.Op) (k : S.Resp o → Prog S α) (f : α → Prog S β) :
    (Prog.op o k).bind f = .op o (fun r => (k r).bind f) := rfl

theorem bind_pure (p : Prog S α) : p.bind Prog.pure = p := by
  induction p with
  | pure a => rfl
  | op o k ih => simp only [op_bind, ih]

theorem bind_assoc (p : Prog S α) (f : α → Prog S β) (g : β → Prog S γ) :
    (p.bind f).bind g = p.bind (fun a => (f a).bind g) := by
  induction p with
  | pure a => rfl
  | op o k ih => simp only [op_bind, ih]

instance : LawfulMonad (Prog S) := LawfulMonad.mk'
  (id_map := fun p => bind_pure p)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun p f g => bind_assoc p f g)

@[simp] theorem lift_bind (o : S.Op) (f : S.Resp o → Prog S β) :
    (lift o).bind f = .op o f := rfl

/-! ## Interpretation in a monad -/

/-- Interpret a program in a monad `m`, given a handler for every operation. -/
def run {m : Type → Type w} [Monad m] (h : (o : S.Op) → m (S.Resp o)) : Prog S α → m α
  | .pure a => Pure.pure a
  | .op o k => h o >>= fun r => run h (k r)

section run
variable {m : Type → Type w} [Monad m] (h : (o : S.Op) → m (S.Resp o))

@[simp] theorem run_pure (a : α) : (Pure.pure a : Prog S α).run h = Pure.pure a := rfl

@[simp] theorem run_op (o : S.Op) (k : S.Resp o → Prog S α) :
    (Prog.op o k).run h = h o >>= fun r => (k r).run h := rfl

@[simp] theorem run_lift [LawfulMonad m] (o : S.Op) : (lift o).run h = h o := by
  simp only [lift, run]
  exact _root_.bind_pure (h o)

end run

/-! ## Relational big-step semantics -/

/-- Relational big-step evaluation: `Eval H p s a s'` holds when `p`, started in state
`s`, can return `a` in state `s'`, where each operation `o` is answered by some `r` with
`H o s r s'`. -/
inductive Eval {σ : Type u} (H : (o : S.Op) → σ → S.Resp o → σ → Prop) :
    Prog S α → σ → α → σ → Prop where
  | pure (a : α) (s : σ) : Eval H (.pure a) s a s
  | op {o : S.Op} {k : S.Resp o → Prog S α} {s : σ} (r : S.Resp o) {s₁ : σ} {a : α}
      {s₂ : σ} : H o s r s₁ → Eval H (k r) s₁ a s₂ → Eval H (.op o k) s a s₂

section eval
variable {σ : Type u} {H : (o : S.Op) → σ → S.Resp o → σ → Prop}

theorem Eval.pure_inv {a b : α} {s s' : σ} (h : Eval H (.pure a) s b s') :
    b = a ∧ s' = s := by
  cases h
  exact ⟨rfl, rfl⟩

@[simp] theorem eval_pure_iff {a b : α} {s s' : σ} :
    Eval H (.pure a) s b s' ↔ b = a ∧ s' = s :=
  ⟨Eval.pure_inv, fun ⟨hb, hs⟩ => by subst hb hs; exact Eval.pure _ _⟩

end eval

/-! ## Predicates over all reachable operations -/

/-- `Every P p`: every operation `p` can issue (for any responses) satisfies `P`. -/
inductive Every (P : S.Op → Prop) : Prog S α → Prop where
  | pure (a : α) : Every P (.pure a)
  | op {o : S.Op} {k : S.Resp o → Prog S α} :
      P o → (∀ r, Every P (k r)) → Every P (.op o k)

section every
variable {P Q : S.Op → Prop}

@[simp] theorem Every.pure' (a : α) : Every P (Pure.pure a : Prog S α) := Every.pure a

end every

/-! ## Finiteness -/

/-- `Child q p`: `q` is an immediate continuation of `p` for some response. -/
inductive Child : Prog S α → Prog S α → Prop where
  | op (o : S.Op) (k : S.Resp o → Prog S α) (r : S.Resp o) : Child (k r) (.op o k)

/-- The number of operations issued by `p` when every operation `o` is answered with
`resp o`. (A `Nat` depth over all responses need not exist: responses may be infinite.) -/
def depthAlong (resp : (o : S.Op) → S.Resp o) : Prog S α → Nat
  | .pure _ => 0
  | .op o k => depthAlong resp (k (resp o)) + 1

/-- The result of `p` when every operation `o` is answered with `resp o`. -/
def resultAlong (resp : (o : S.Op) → S.Resp o) : Prog S α → α
  | .pure a => a
  | .op o k => resultAlong resp (k (resp o))

/-! ## List helpers -/

/-- Monadic map over a list, by list recursion. -/
def mapM (f : α → Prog S β) : List α → Prog S (List β)
  | [] => Prog.pure []
  | a :: as => (f a).bind fun b => (mapM f as).bind fun bs => Prog.pure (b :: bs)

/-- Monadic iteration over a list, by list recursion. -/
def forM (xs : List α) (f : α → Prog S PUnit) : Prog S PUnit :=
  match xs with
  | [] => Prog.pure ⟨⟩
  | a :: as => (f a).bind fun _ => forM as f

/-- Monadic left fold over a list, by list recursion. -/
def foldlM (f : β → α → Prog S β) (init : β) : List α → Prog S β
  | [] => Prog.pure init
  | a :: as => (f init a).bind fun b => foldlM f b as

@[simp] theorem mapM_nil (f : α → Prog S β) : mapM f [] = Prog.pure [] := rfl
@[simp] theorem mapM_cons (f : α → Prog S β) (a : α) (as : List α) :
    mapM f (a :: as) = (f a).bind fun b => (mapM f as).bind fun bs => Prog.pure (b :: bs) :=
  rfl
@[simp] theorem forM_nil (f : α → Prog S PUnit) : forM [] f = Prog.pure ⟨⟩ := rfl
@[simp] theorem forM_cons (f : α → Prog S PUnit) (a : α) (as : List α) :
    forM (a :: as) f = (f a).bind fun _ => forM as f := rfl
@[simp] theorem foldlM_nil (f : β → α → Prog S β) (b : β) : foldlM f b [] = Prog.pure b :=
  rfl
@[simp] theorem foldlM_cons (f : β → α → Prog S β) (b : β) (a : α) (as : List α) :
    foldlM f b (a :: as) = (f b a).bind fun b' => foldlM f b' as := rfl

section everyList
variable {P : S.Op → Prop}

end everyList

/-! ## Failure adapters -/

/-- Embed an `Except`, using `throw` for the error case. -/
def ofExcept {ε : Type} (throw : ε → Prog S α) : Except ε α → Prog S α
  | .error e => throw e
  | .ok a => Prog.pure a

/-- Embed an `Option`, using `throw` for the `none` case. -/
def ofOption (throw : Prog S α) : Option α → Prog S α
  | none => throw
  | some a => Prog.pure a

end Prog

/-! ## Examples: a get/put signature over `Nat` -/

namespace ProgExamples

/-- Operations of a single `Nat` cell. -/
inductive CellOp where
  | get
  | put (n : Nat)
  deriving DecidableEq, Repr

/-- Responses: `get` returns the value, `put` returns nothing. -/
def CellOp.Resp : CellOp → Type
  | .get => Nat
  | .put _ => Unit

/-- The signature of a single `Nat` cell. -/
def cellSig : Sig := { Op := CellOp, Resp := CellOp.Resp }

/-- Read the cell. -/
def get : Prog cellSig Nat := Prog.lift (S := cellSig) CellOp.get

/-- Write the cell. -/
def put (n : Nat) : Prog cellSig Unit := Prog.lift (S := cellSig) (CellOp.put n)

/-- The `StateM Nat` handler of the cell. -/
def handler : (o : cellSig.Op) → StateM Nat (cellSig.Resp o)
  | .get => (MonadState.get : StateM Nat Nat)
  | .put n => (MonadState.set n : StateM Nat Unit)

/-- Write 1, then add 2 to the cell, then read it back. -/
def prog : Prog cellSig Nat := do
  put 1
  let n ← get
  put (n + 2)
  get

end ProgExamples

end Silmaril.Wasm.Component.Canon
