module

public import Silmaril.Wasm.FnInst.Core.Defs
public import Mathlib.Data.BitVec

/-!
# A Wasm instruction fragment as a function-level `Lang`

A small fragment of Wasm code, enough to exercise every part of a module context that a body
can name: `i32` constants and arithmetic, locals, globals, memories, calls, and structured
control (`block`, `br`, `br_if`, `if`). Sequencing is a binary constructor (`seq`), so `Instr`
is a plain inductive type.

Simplifications, stated once:

* values are `i32` only (`BitVec 32`);
* calls, global and memory accesses are **events** answered by the handler (the model): the
  fragment has no store of its own;
* a stack underflow traps (there is no validation), locals read out of range as `0` and
  writes out of range are ignored; `block` and `if` have no result arity: a branch keeps the
  whole operand stack;
* there are no loops and no `return` (a branch out of the body is a return).

`frag` packages the fragment as a `Lang`; naturality (`exec_rename`) is proved by induction on
code in `Silmaril.Wasm.FnInst.Frag.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Frag

open CategoryTheory

/-- `i32` values. -/
abbrev Val : Type := BitVec 32

/-- Instructions over a module context. -/
inductive Instr (C : Ctx) where
  | nop
  | unreachable
  | const (v : Val)
  | add
  | sub
  | mul
  | eqz
  | drop
  | localGet (n : ℕ)
  | localSet (n : ℕ)
  | localTee (n : ℕ)
  | globalGet (g : C.Idx .global)
  | globalSet (g : C.Idx .global)
  | load (m : C.Idx .mem)
  | store (m : C.Idx .mem)
  | call (f : C.Idx .func)
  | seq (a b : Instr C)
  | block (b : Instr C)
  | br (n : ℕ)
  | brIf (n : ℕ)
  | ite (t e : Instr C)

namespace Instr

variable {C C' : Ctx}

/-- Renaming along an embedding. -/
def rename (σ : C ⟶ C') : Instr C → Instr C'
  | nop => nop
  | unreachable => unreachable
  | const v => const v
  | add => add
  | sub => sub
  | mul => mul
  | eqz => eqz
  | drop => drop
  | localGet n => localGet n
  | localSet n => localSet n
  | localTee n => localTee n
  | globalGet g => globalGet (Ctx.Hom.map σ .global g)
  | globalSet g => globalSet (Ctx.Hom.map σ .global g)
  | load m => load (Ctx.Hom.map σ .mem m)
  | store m => store (Ctx.Hom.map σ .mem m)
  | call f => call (Ctx.Hom.map σ .func f)
  | seq a b => seq (a.rename σ) (b.rename σ)
  | block b => block (b.rename σ)
  | br n => br n
  | brIf n => brIf n
  | ite t e => ite (t.rename σ) (e.rename σ)

end Instr

/-- Events: calls, global and memory accesses. -/
inductive Ev (C : Ctx) where
  | call (f : C.Idx .func) (args : List Val)
  | globalGet (g : C.Idx .global)
  | globalSet (g : C.Idx .global) (v : Val)
  | load (m : C.Idx .mem) (addr : Val)
  | store (m : C.Idx .mem) (addr v : Val)

/-- Renaming events. -/
def Ev.map {C C' : Ctx} (σ : C ⟶ C') : Ev C → Ev C'
  | call f a => call (Ctx.Hom.map σ .func f) a
  | globalGet g => globalGet (Ctx.Hom.map σ .global g)
  | globalSet g v => globalSet (Ctx.Hom.map σ .global g) v
  | load m a => load (Ctx.Hom.map σ .mem m) a
  | store m a v => store (Ctx.Hom.map σ .mem m) a v

/-- Answers to events: a list of values (`globalGet`, `load` and calls answer their results,
stores answer `[]`), or `none` for a trap. -/
abbrev Resp : Type := Option (List Val)

/-- Outcomes: normal completion with operand stack and locals, a branch to the `n`-th enclosing
label, or a trap; each with the final world. -/
inductive Out (W : Type) where
  | normal (s l : List Val) (w : W)
  | br (n : ℕ) (s l : List Val) (w : W)
  | trap (w : W)

namespace Out

variable {W : Type}

/-- Sequencing: continue after normal completion. -/
def bind : Out W → (List Val → List Val → W → Out W) → Out W
  | normal s l w, k => k s l w
  | o, _ => o

/-- Leaving a block: a branch to label `0` completes normally, others go one label out. -/
def unlabel : Out W → Out W
  | br 0 s l w => normal s l w
  | br (n + 1) s l w => br n s l w
  | o => o

end Out

variable {C : Ctx} {W : Type}

/-- Push the answer of an event, or trap. -/
def answer (r : Resp × W) (s l : List Val) : Out W :=
  match r with
  | (some vs, w') => .normal (vs.reverse ++ s) l w'
  | (none, w') => .trap w'

/-- A binary operator on the top two stack values (the top is the right operand). -/
def binop (f : Val → Val → Val) (s l : List Val) (w : W) : Out W :=
  match s with
  | a :: b :: s => .normal (f b a :: s) l w
  | _ => .trap w

/-- Execution of an instruction from operand stack `s` (top first) and locals `l`, under a
handler. -/
def exec (h : Ev C → W → Resp × W) : Instr C → List Val → List Val → W → Out W
  | .nop, s, l, w => .normal s l w
  | .unreachable, _, _, w => .trap w
  | .const v, s, l, w => .normal (v :: s) l w
  | .add, s, l, w => binop (· + ·) s l w
  | .sub, s, l, w => binop (· - ·) s l w
  | .mul, s, l, w => binop (· * ·) s l w
  | .eqz, s, l, w =>
    match s with
    | a :: s => .normal ((if a = 0 then 1 else 0) :: s) l w
    | [] => .trap w
  | .drop, s, l, w =>
    match s with
    | _ :: s => .normal s l w
    | [] => .trap w
  | .localGet n, s, l, w => .normal (l.getD n 0 :: s) l w
  | .localSet n, s, l, w =>
    match s with
    | a :: s => .normal s (l.set n a) w
    | [] => .trap w
  | .localTee n, s, l, w =>
    match s with
    | a :: s => .normal (a :: s) (l.set n a) w
    | [] => .trap w
  | .globalGet g, s, l, w => answer (h (.globalGet g) w) s l
  | .globalSet g, s, l, w =>
    match s with
    | a :: s => answer (h (.globalSet g a) w) s l
    | [] => .trap w
  | .load m, s, l, w =>
    match s with
    | a :: s => answer (h (.load m a) w) s l
    | [] => .trap w
  | .store m, s, l, w =>
    match s with
    | v :: a :: s => answer (h (.store m a v) w) s l
    | _ => .trap w
  | .call f, s, l, w =>
    if (C.fty f).params.length ≤ s.length then
      answer (h (.call f (s.take (C.fty f).params.length).reverse) w)
        (s.drop (C.fty f).params.length) l
    else .trap w
  | .seq a b, s, l, w => (exec h a s l w).bind (exec h b)
  | .block b, s, l, w => (exec h b s l w).unlabel
  | .br n, s, l, w => .br n s l w
  | .brIf n, s, l, w =>
    match s with
    | a :: s => if a = 0 then .normal s l w else .br n s l w
    | [] => .trap w
  | .ite t e, s, l, w =>
    match s with
    | a :: s => if a = 0 then exec h e s l w else exec h t s l w
    | [] => .trap w

/-- The call result of an outcome: the operand stack (bottom first), or `none` on a trap. -/
def ret : Out W → Resp × W
  | .normal s _ w => (some s.reverse, w)
  | .br _ s _ w => (some s.reverse, w)
  | .trap w => (none, w)

/-- Configurations fitting a segment type: enough operands and locals. -/
def Fits (τ : SegTy) (c : List Val × List Val) : Prop :=
  τ.params.length ≤ c.1.length ∧ τ.locals.length ≤ c.2.length

/-- Holes in instructions: one-hole contexts, for plugging a segment into a body. -/
inductive Hole (C : Ctx) where
  | here
  | seqL (K : Hole C) (b : Instr C)
  | seqR (a : Instr C) (K : Hole C)
  | block (K : Hole C)
  | iteT (K : Hole C) (e : Instr C)
  | iteE (t : Instr C) (K : Hole C)

/-- Plugging a segment into a hole. -/
def Hole.plug : Hole C → Instr C → Instr C
  | here, b => b
  | seqL K c, b => .seq (K.plug b) c
  | seqR a K, b => .seq a (K.plug b)
  | block K, b => .block (K.plug b)
  | iteT K e, b => .ite (K.plug b) e
  | iteE t K, b => .ite t (K.plug b)

/-- Renaming holes. -/
def Hole.rename {C C' : Ctx} (σ : C ⟶ C') : Hole C → Hole C'
  | here => here
  | seqL K b => seqL (K.rename σ) (b.rename σ)
  | seqR a K => seqR (a.rename σ) (K.rename σ)
  | block K => block (K.rename σ)
  | iteT K e => iteT (K.rename σ) (e.rename σ)
  | iteE t K => iteE (t.rename σ) (K.rename σ)

/-! ### Laws, and the fragment as a `Lang` -/

theorem Instr.rename_id {C : Ctx} (i : Instr C) : i.rename (𝟙 C) = i := by
  induction i <;> simp only [Instr.rename, Ctx.id_map, *]

theorem Instr.rename_comp {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'') (i : Instr C) :
    i.rename (σ ≫ τ) = (i.rename σ).rename τ := by
  induction i <;> simp only [Instr.rename, Ctx.comp_map, *]

theorem Ev.map_id {C : Ctx} (e : Ev C) : e.map (𝟙 C) = e := by
  cases e <;> rfl

theorem Ev.map_comp {C C' C'' : Ctx} (σ : C ⟶ C') (τ : C' ⟶ C'') (e : Ev C) :
    e.map (σ ≫ τ) = (e.map σ).map τ := by
  cases e <;> rfl

/-- Naturality of execution in embeddings. -/
theorem exec_rename {C C' : Ctx} {W : Type} (σ : C ⟶ C') (h : Ev C' → W → Resp × W)
    (i : Instr C) : exec h (i.rename σ) = exec (fun e => h (e.map σ)) i := by
  induction i with
  | call f =>
    funext s l w
    simp only [Instr.rename, exec, Ctx.Hom.fty, Ev.map]
  | seq a b iha ihb =>
    funext s l w
    simp only [Instr.rename, exec, iha, ihb]
  | block b ih =>
    funext s l w
    simp only [Instr.rename, exec, ih]
  | ite t e iht ihe =>
    funext s l w
    cases s <;> simp only [Instr.rename, exec, iht, ihe]
  | _ => rfl

/-- The fragment as a function-level language. -/
def frag : Lang where
  Code := Instr
  rename σ i := i.rename σ
  rename_id := Instr.rename_id
  rename_comp := Instr.rename_comp
  Ev := Ev
  evMap σ e := e.map σ
  evMap_id := Ev.map_id
  evMap_comp := Ev.map_comp
  Resp := Resp
  Cfg := List Val × List Val
  Args := List Val
  Out := Out
  exec h i c w := exec h i c.1 c.2 w
  exec_rename σ h i := funext fun c => funext fun w => by rw [exec_rename]
  fits := Fits
  argsFit t a := a.length = t.params.length
  entry a := ([], a)
  ret := ret
  callEv f a := .call f a
  evMap_callEv _ _ _ := rfl

end Silmaril.Wasm.FnInst.Frag
