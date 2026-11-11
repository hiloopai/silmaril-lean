module

public import Silmaril.Wasm.FnInst.Models.Version.Defs
public import Silmaril.Wasm.FnInst.Models.Entry.Defs
public import Silmaril.Wasm.Models.Features.Thms

/-!
# A small Wasm fragment as a body language

A first instance of the generic models (simplest version first; to be widened). Values are
`i32` (`BitVec 32`), the state is one `i32` global, functions take one argument (a function
type is its arity, `Ty := ℕ`, used only by signature morphisms). Expressions in the style of
Binaryen IR:

| constructor | Wasm | capability (`Silmaril.Wasm.Models.Cap`) |
| --- | --- | --- |
| `const c` | `i32.const c` | `intNum` |
| `param k` | `local.get k` (a parameter) | `intNum` |
| `add a b` | `i32.add` | `intNum` |
| `ext8 a` | `i32.extend8_s` | `signExt` (2.0) |
| `gget` | `global.get 0` | `globals` |
| `gset a` | `global.set 0` then `global.get 0` (a tee) | `mutGlobal` |
| `call f a` | `call f` | `directCall` |
| `seq a b` | `a; drop; b` | none |
| `trap` | `unreachable` | `control` |

Semantics (`sem`): a function behaviour (`Den`) maps arguments and the state to a *set* of
results (`Option Val` with `none` a trap, and the new state): nondeterminism stands for what is
unknown about callees (imports, unspecified functions). `eval env args e` evaluates left to
right; a trap stops evaluation.

Versions: `uses e S` (every capability `caps e` is in the feature set `S`) makes it a
`Versioned` language over `FeatureSet`. `adm S d` is the context-restricting reading: without
`mutGlobal`, no function can change the global.

`obs0` observes a behaviour from global `0` for the entry logics.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models.Frag

open Silmaril.Wasm.Models Silmaril.Wasm

/-- Values: `i32`. -/
abbrev Val : Type := BitVec 32

/-- The state: one `i32` global. -/
abbrev St : Type := BitVec 32

/-- Results: a value (or a trap, `none`) and the new state. -/
abbrev Res : Type := Option Val × St

/-- Function behaviours. -/
abbrev Den : Type := List Val → St → Set Res

/-- Expressions over `n` callable functions. -/
inductive Expr (n : ℕ) : Type where
  | const (c : Val)
  | param (k : ℕ)
  | add (a b : Expr n)
  | ext8 (a : Expr n)
  | gget
  | gset (a : Expr n)
  | call (f : Fin n) (a : Expr n)
  | seq (a b : Expr n)
  | trap

namespace Expr

/-- Renumbering of calls. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : Expr n → Expr m
  | const c => const c
  | param k => param k
  | add a b => add (rename ρ a) (rename ρ b)
  | ext8 a => ext8 (rename ρ a)
  | gget => gget
  | gset a => gset (rename ρ a)
  | call f a => call (ρ f) (rename ρ a)
  | seq a b => seq (rename ρ a) (rename ρ b)
  | trap => trap

theorem rename_id {n : ℕ} (e : Expr n) : rename id e = e := by
  induction e <;> simp_all [rename]

theorem rename_comp {n m k : ℕ} (ρ : Fin n → Fin m) (τ : Fin m → Fin k) (e : Expr n) :
    rename (τ ∘ ρ) e = rename τ (rename ρ e) := by
  induction e <;> simp_all [rename]

/-- The capabilities an expression needs. -/
def caps {n : ℕ} : Expr n → List Cap
  | const _ => [.intNum]
  | param _ => [.intNum]
  | add a b => .intNum :: (caps a ++ caps b)
  | ext8 a => .signExt :: caps a
  | gget => [.globals]
  | gset a => .mutGlobal :: caps a
  | call _ a => .directCall :: caps a
  | seq a b => caps a ++ caps b
  | trap => [.control]

theorem caps_rename {n m : ℕ} (ρ : Fin n → Fin m) (e : Expr n) :
    caps (rename ρ e) = caps e := by
  induction e <;> simp_all [rename, caps]

end Expr

/-- Returning a value. -/
def ret (v : Val) : St → Set Res := fun s => {(some v, s)}

/-- Sequencing: run `m`; on a trap stop, else continue with `k`. -/
def bind (m : St → Set Res) (k : Val → St → Set Res) : St → Set Res := fun s =>
  {r | ∃ p ∈ m s, match p.1 with
    | none => r = (none, p.2)
    | some v => r ∈ k v p.2}

/-- Evaluation of an expression with arguments `args`, callees behaving as `env`. -/
def eval {n : ℕ} (env : Fin n → Den) (args : List Val) : Expr n → St → Set Res
  | .const c => ret c
  | .param k => ret (args.getD k 0)
  | .add a b => bind (eval env args a) fun x => bind (eval env args b) fun y => ret (x + y)
  | .ext8 a => bind (eval env args a) fun x => ret ((x.truncate 8).signExtend 32)
  | .gget => fun s => {(some s, s)}
  | .gset a => bind (eval env args a) fun x _ => {(some x, x)}
  | .call f a => bind (eval env args a) fun x => env f [x]
  | .seq a b => bind (eval env args a) fun _ => eval env args b
  | .trap => fun s => {(none, s)}

theorem eval_rename {n m : ℕ} (ρ : Fin n → Fin m) (env : Fin m → Den) (args : List Val)
    (e : Expr n) : eval env args (e.rename ρ) = eval (env ∘ ρ) args e := by
  induction e <;> simp_all [Expr.rename, eval]

/-- The fragment as a body language. -/
abbrev syn : FnSyntax where
  Ty := ℕ
  Body := Expr
  rename := Expr.rename
  rename_id := Expr.rename_id
  rename_comp := Expr.rename_comp

/-- The fragment's semantics. -/
abbrev sem : FnSem syn where
  Den := Den
  eval env b := fun args => eval env args b
  eval_rename ρ env b := funext fun args => eval_rename ρ env args b

/-- Feature set `S` allows `e`. -/
def uses {n : ℕ} (e : Expr n) (S : FeatureSet) : Prop := ∀ c ∈ e.caps, S.has c = true

/-- The fragment as a language versioned by feature sets. -/
def versioned : Versioned syn FeatureSet where
  Uses e S := uses e S
  uses_mono h hb c hc := has_of_le h (hb c hc)
  uses_rename ρ e S := by
    show (∀ c ∈ (Expr.rename ρ e).caps, S.has c = true) ↔ ∀ c ∈ e.caps, S.has c = true
    rw [Expr.caps_rename]

/-- Behaviours admissible at feature set `S`: without `mutGlobal`, the global is unchanged. -/
def adm (S : FeatureSet) : Set sem.Den :=
  {d | S.has .mutGlobal = true ∨ ∀ args s r, r ∈ (d : Den) args s → r.2 = s}

/-- Observing a behaviour from the initial global `0`: a value is returned, a trap traps. -/
def obs0 (d : sem.Den) (vs : List Val) : Set (Behaviour Val) :=
  {β | ∃ r ∈ (d : Den) vs 0, β = match r.1 with
    | some v => .returns [v]
    | none => .traps}

/-- A signature: `n` unary functions, focus `i`. -/
def sig (n : ℕ) (i : Fin n) : Sig syn := ⟨⟨n, fun _ => (1 : ℕ)⟩, i⟩

end Silmaril.Wasm.FnInst.Models.Frag
