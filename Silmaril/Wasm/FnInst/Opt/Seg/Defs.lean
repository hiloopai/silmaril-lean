module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.List.Infix

@[expose] public section

/-! # A straight-line Wasm fragment with calls: segments, holes, environments

The object language of the optimiser rules (docs/projects/logic-inst.md). It is a
small fragment of Wasm function bodies, enough to state the peephole rules of
wasm-opt's `OptimizeInstructions`, `Vacuum`, `SimplifyLocals` and `rse-line`
subrules over one value type (`i32`):

* `i32.const`, `i32.add`, `i32.sub`, `i32.mul`, `i32.and`, `i32.or`, `i32.xor`, `i32.eqz`;
* `local.get`, `local.set`, `local.tee`, `global.get`, `global.set`, `drop`;
* `call f`, with the type `(params, results)` of `f` read from the visible function types `ft`.

Not covered yet: blocks, branches, loops, memory, tables, exceptions, other value types.

**Calls go to an environment.** A call does not run a body; it asks an environment
`E : Env`, the *abstract semantic function* of every function index (models (c) of the
design): from the arguments and the globals to a set of answers (`ret results globals'`, `trap`,
`div`). An unspecified function is the full relation `Env.top`; a more informative
environment is a narrower one (`E ≤ M` pointwise). Locals are frame-private, so a callee sees
and changes only the globals. Divergence is an explicit answer, so a *completion* of a model
(an implementation it allows) is a narrower environment that always answers something:
narrowing never turns "returns" into "never answers".

**Holes.** A *hole* is a code position given only by its stack type: `n` operands on entry,
`m` results on exit, over the visible function types `ft` (`HSig`). Values are all `i32`,
so a stack type is a height; the checker `chk` computes heights. A segment of a hole is
code with `chk ft s n = some m`.

**Modules.** `Mdl` is a module of the fragment: function types, a number of imported
functions answered by an import environment, and bodies of the others. Its semantics `fsem`
is the call-depth-indexed environment of all its functions.
-/

namespace Silmaril.Wasm.FnInst.Opt

/-- The only value type of the fragment: `i32`. -/
abbrev Val := BitVec 32

/-- Instructions of the fragment. -/
inductive Instr where
  | const (k : Val)
  | add | sub | mul | and | or | xor
  | eqz
  | localGet (x : ℕ) | localSet (x : ℕ) | localTee (x : ℕ)
  | globalGet (x : ℕ) | globalSet (x : ℕ)
  | drop
  | call (f : ℕ)
  deriving DecidableEq, Repr

/-- Code: a sequence of instructions. -/
abbrev Code := List Instr

/-- Function types visible to code: `ft[f] = (params, results)`. -/
abbrev FTypes := List (ℕ × ℕ)

/-- A machine state: locals and globals as total maps (absent ones read `0` in practice),
and the operand stack, top first. -/
structure St where
  locals : ℕ → Val
  globals : ℕ → Val
  stack : List Val

/-- Outcomes of running code: a final state, a trap, or divergence. -/
inductive Out where
  | ok (s : St)
  | trap
  | div

/-- Answers of a function: results and globals, a trap, or divergence. -/
inductive Ans where
  | ret (r : List Val) (g : ℕ → Val)
  | trap
  | div

/-- Environments: the abstract semantic function of every function index, from arguments
(top of stack first) and globals to the set of possible answers. -/
def Env : Type := ℕ → List Val → (ℕ → Val) → Set Ans

namespace Env

/-- The least informative environment: every function may do anything. -/
def top : Env := fun _ _ _ => Set.univ

/-- Information order: `E ≤ M` iff `E` is narrower than `M` (more informative). -/
instance : LE Env := ⟨fun E M => ∀ f args g, E f args g ⊆ M f args g⟩

theorem le_def {E M : Env} : E ≤ M ↔ ∀ f args g, E f args g ⊆ M f args g := Iff.rfl

theorem le_refl (E : Env) : E ≤ E := fun _ _ _ => subset_rfl

theorem le_trans {E M N : Env} (h₁ : E ≤ M) (h₂ : M ≤ N) : E ≤ N :=
  fun f a g => (h₁ f a g).trans (h₂ f a g)

theorem le_top (E : Env) : E ≤ top := fun _ _ _ => Set.subset_univ _

/-- An environment respects the function types: every result list has the declared length. -/
def Typed (ft : FTypes) (E : Env) : Prop :=
  ∀ f n m, ft[f]? = some (n, m) → ∀ args g r g', Ans.ret r g' ∈ E f args g → r.length = m

/-- An environment always answers (divergence is an answer, `Ans.div`). -/
def Total (E : Env) : Prop := ∀ f args g, (E f args g).Nonempty

/-- `E` is a completion of the (partial) model `M` at `ft`: an implementation of every
function that `M` allows. It is narrower than `M`, typed and total. -/
abbrev Completion (ft : FTypes) (E M : Env) : Prop := E ≤ M ∧ Typed ft E ∧ Total E

end Env

/-! ## Semantics -/

namespace Out

/-- Whether an outcome is a final state. -/
def isOk : Out → Bool
  | .ok _ => true
  | _ => false

/-- Sequential composition of outcome sets: continue every final state, keep traps and
divergence. -/
def bind (S : Set Out) (k : St → Set Out) : Set Out :=
  {o | (∃ st, Out.ok st ∈ S ∧ o ∈ k st) ∨ (o ∈ S ∧ o.isOk = false)}

end Out

/-- Pop two operands `b` (top) and `a`, push `f a b`. -/
def binop (f : Val → Val → Val) (st : St) : Out :=
  match st.stack with
  | b :: a :: r => .ok { st with stack := f a b :: r }
  | _ => .trap

/-- Pop one operand `a`, push `f a`. -/
def unop (f : Val → Val) (st : St) : Out :=
  match st.stack with
  | a :: r => .ok { st with stack := f a :: r }
  | _ => .trap

/-- `i32.eqz` on one value. -/
def eqzV (a : Val) : Val := if a = 0 then 1 else 0

/-- Pop one operand `v` and continue with `k v` on the rest. -/
def pop1 (st : St) (k : Val → St → St) : Out :=
  match st.stack with
  | v :: r => .ok (k v { st with stack := r })
  | [] => .trap

/-- The deterministic instructions (everything but `call`, which traps here). -/
def exec1 : Instr → St → Out
  | .const k, st => .ok { st with stack := k :: st.stack }
  | .add, st => binop (· + ·) st
  | .sub, st => binop (· - ·) st
  | .mul, st => binop (· * ·) st
  | .and, st => binop (· &&& ·) st
  | .or, st => binop (· ||| ·) st
  | .xor, st => binop (· ^^^ ·) st
  | .eqz, st => unop eqzV st
  | .localGet x, st => .ok { st with stack := st.locals x :: st.stack }
  | .localSet x, st => pop1 st fun v s => { s with locals := Function.update s.locals x v }
  | .localTee x, st =>
    pop1 st fun v s => { s with locals := Function.update s.locals x v, stack := v :: s.stack }
  | .globalGet x, st => .ok { st with stack := st.globals x :: st.stack }
  | .globalSet x, st => pop1 st fun v s => { s with globals := Function.update s.globals x v }
  | .drop, st => pop1 st fun _ s => s
  | .call _, _ => .trap

/-- The outcomes of calling `f` with `n` arguments from `st`: the environment's answers. -/
def callOut (E : Env) (f n : ℕ) (st : St) : Set Out :=
  {o | (∃ r g', Ans.ret r g' ∈ E f (st.stack.take n) st.globals ∧
      o = .ok { st with globals := g', stack := r ++ st.stack.drop n }) ∨
    (o = .trap ∧ Ans.trap ∈ E f (st.stack.take n) st.globals) ∨
    (o = .div ∧ Ans.div ∈ E f (st.stack.take n) st.globals)}

/-- One instruction, under function types `ft` and environment `E`. -/
def step (ft : FTypes) (E : Env) : Instr → St → Set Out
  | .call f, st =>
    match ft[f]? with
    | some (n, _) => if n ≤ st.stack.length then callOut E f n st else {.trap}
    | none => {.trap}
  | i, st => {exec1 i st}

/-- Code, under function types `ft` and environment `E`. -/
def run (ft : FTypes) (E : Env) : Code → St → Set Out
  | [], st => {.ok st}
  | i :: c, st => Out.bind (step ft E i st) (run ft E c)

/-! ## Stack typing -/

/-- Operands popped and results pushed by an instruction (`none`: unknown function). -/
def arity (ft : FTypes) : Instr → Option (ℕ × ℕ)
  | .const _ | .localGet _ | .globalGet _ => some (0, 1)
  | .add | .sub | .mul | .and | .or | .xor => some (2, 1)
  | .eqz | .localTee _ => some (1, 1)
  | .localSet _ | .globalSet _ | .drop => some (1, 0)
  | .call f => ft[f]?

/-- The stack height after an instruction, from height `h`. -/
def hgt (ft : FTypes) (i : Instr) (h : ℕ) : Option ℕ :=
  match arity ft i with
  | some (p, q) => if p ≤ h then some (h - p + q) else none
  | none => none

/-- The stack height after code, from height `h` (`none`: ill-typed). -/
def chk (ft : FTypes) : Code → ℕ → Option ℕ
  | [], h => some h
  | i :: c, h => (hgt ft i h).bind (chk ft c)

/-! ## Holes and segments -/

/-- A hole: the visible function types and a stack type `n → m`. -/
structure HSig where
  ft : FTypes
  n : ℕ
  m : ℕ

/-- A segment of a hole: code of stack type `n → m`. -/
def Seg (X : HSig) : Type := {c : Code // chk X.ft c X.n = some X.m}

/-! ## Equivalence and refinement of code at a hole -/

/-- `s` and `s'` run the same under `E` from every state with at least `n` operands. -/
def RunEq (ft : FTypes) (n : ℕ) (E : Env) (s s' : Code) : Prop :=
  ∀ st : St, n ≤ st.stack.length → run ft E s st = run ft E s' st

/-- Every outcome of `s` under `E` is one of `s'`, from every state with at least `n`
operands. -/
def RunLe (ft : FTypes) (n : ℕ) (E : Env) (s s' : Code) : Prop :=
  ∀ st : St, n ≤ st.stack.length → run ft E s st ⊆ run ft E s' st

/-- Equivalence of two codes at a hole of `n` operands, in every completion of `M`. -/
def SegEquiv (ft : FTypes) (n : ℕ) (M : Env) (s s' : Code) : Prop :=
  ∀ E, E.Completion ft M → RunEq ft n E s s'

/-! ## Modules -/

/-- A module of the fragment: function types (imports first), the number of imports, and
the bodies of the defined functions. A body starts with an empty stack and its arguments in
locals `0, 1, …`; its final stack is its result list. -/
structure Mdl where
  ft : FTypes
  nimp : ℕ
  bodies : List Code

/-- The initial state of a function body. -/
def initSt (args : List Val) (g : ℕ → Val) : St :=
  ⟨fun j => args.getD j 0, g, []⟩

/-- The answers of a body run: the final stack and globals, a trap, or divergence. -/
def answers (S : Set Out) : Set Ans :=
  {a | (∃ st, Out.ok st ∈ S ∧ a = .ret st.stack st.globals) ∨ (a = .trap ∧ Out.trap ∈ S) ∨
    (a = .div ∧ Out.div ∈ S)}

/-- The semantics of the module's functions up to call depth `k`, with imports answered by
`imp`. At depth `0` a defined function is not run: it answers `div` ("did not return within
the depth"). An index without a body traps (valid code never calls one). -/
def fsem (M : Mdl) (imp : Env) : ℕ → Env
  | 0 => fun f args g => if f < M.nimp then imp f args g else {Ans.div}
  | k + 1 => fun f args g =>
    if f < M.nimp then imp f args g
    else match M.bodies[f - M.nimp]? with
      | some b => answers (run M.ft (fsem M imp k) b (initSt args g))
      | none => {Ans.trap}

/-- The terminating denotation of a module function: the returns and traps it reaches at some
call depth. -/
def den (M : Mdl) (imp : Env) (f : ℕ) (args : List Val) (g : ℕ → Val) : Set Ans :=
  {a | a ≠ .div ∧ ∃ k, a ∈ fsem M imp k f args g}

/-- A module is well typed: every defined function has a type, and its body takes the empty
stack to its result count. -/
def Mdl.Typed (M : Mdl) : Prop :=
  ∀ i b, M.bodies[i]? = some b → ∃ n m, M.ft[M.nimp + i]? = some (n, m) ∧ chk M.ft b 0 = some m

/-! ## Rewriting a segment at typed positions -/

/-- `Rw ft s s' n m h c c'`: `c'` is `c` with some occurrences of `s` replaced by `s'`, each
at a position where the static stack height is at least `n` (the hole's operand count). The
code is read from height `h`; after an occurrence the height is `h - n + m`. -/
inductive Rw (ft : FTypes) (s s' : Code) (n m : ℕ) : ℕ → Code → Code → Prop
  | nil (h : ℕ) : Rw ft s s' n m h [] []
  | keep {h h₂ : ℕ} (i : Instr) {c c' : Code} :
      hgt ft i h = some h₂ → Rw ft s s' n m h₂ c c' → Rw ft s s' n m h (i :: c) (i :: c')
  | seg {h : ℕ} {c c' : Code} :
      n ≤ h → Rw ft s s' n m (h - n + m) c c' → Rw ft s s' n m h (s ++ c) (s' ++ c')

/-- A module rewritten in its bodies by `Rw` (each body read from height `0`). -/
def Mdl.Rewrites (s s' : Code) (n m : ℕ) (M M' : Mdl) : Prop :=
  M'.ft = M.ft ∧ M'.nimp = M.nimp ∧ List.Forall₂ (Rw M.ft s s' n m 0) M.bodies M'.bodies

end Silmaril.Wasm.FnInst.Opt
