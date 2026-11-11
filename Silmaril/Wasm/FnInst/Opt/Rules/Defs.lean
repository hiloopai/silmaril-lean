module

public import Silmaril.Wasm.FnInst.Opt.Inst.Defs

@[expose] public section

/-! # A peephole family at minimal holes

The rewrites of wasm-opt's peephole stages, restricted to the fragment of
`Silmaril.Wasm.FnInst.Opt.Seg`, as segment pairs at their *minimal* holes: no visible functions
(`ft = []`) and the smallest stack type the rule needs.

| Rule | Hole | Before | After | wasm-opt stage |
| --- | --- | --- | --- | --- |
| `neutral` | `1 → 1` | `i32.const k; op` | (nothing) | `neutral-ops` (`x+0`, `x-0`, `x*1`, `x|0`, `x^0`, `x&-1`) |
| `eqz3` | `1 → 1` | `i32.eqz; i32.eqz; i32.eqz` | `i32.eqz` | `eqz-pair` (consumer `i32.eqz`) |
| `dropGet x` | `0 → 0` | `local.get x; drop` | (nothing) | `drop-get` |
| `dropGlobal x` | `0 → 0` | `global.get x; drop` | (nothing) | Vacuum (dropped pure read) |
| `teeForm x` | `1 → 1` | `local.set x; local.get x` | `local.tee x` | `tee-form` |
| `rseSet x` | `0 → 0` | `local.get x; local.set x` | (nothing) | `rse-line` then `drop-get` |
| `rseTee x` | `0 → 1` | `local.get x; local.tee x` | `local.get x` | `rse-line` |

`callDrop` (`call 0; drop` against nothing, with function `0 : [] → [i32]` visible) is the
information example: not valid over the least informative model (the callee may trap,
diverge or write globals), valid over the model where function `0` is known to return `0` and
leave the globals alone.
-/

namespace Silmaril.Wasm.FnInst.Opt.Rules

open Silmaril.Wasm.FnInst.Opt

/-- The minimal hole `n → m` with no visible functions. -/
def hole (n m : ℕ) : HSig := ⟨[], n, m⟩

/-- A neutral right operand: `op a k = a` for every `a`. -/
inductive Neutral : Instr → Val → Prop
  | add : Neutral .add 0
  | sub : Neutral .sub 0
  | mul : Neutral .mul 1
  | or : Neutral .or 0
  | xor : Neutral .xor 0
  | and : Neutral .and (BitVec.allOnes 32)

/-- The binary operators of the fragment. -/
def IsBinop (i : Instr) : Prop := i = .add ∨ i = .sub ∨ i = .mul ∨ i = .and ∨ i = .or ∨ i = .xor

theorem Neutral.isBinop {i : Instr} {k : Val} (h : Neutral i k) : IsBinop i := by
  cases h <;> simp [IsBinop]

theorem chk_binop {i : Instr} (hi : IsBinop i) (k : Val) :
    chk [] [.const k, i] 1 = some 1 := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `i32.const k; op` at `1 → 1`. -/
def neutralL {i : Instr} {k : Val} (h : Neutral i k) : Seg (hole 1 1) :=
  ⟨[.const k, i], chk_binop h.isBinop k⟩

/-- The empty segment of a hole `n → n`. -/
def skip (n : ℕ) : Seg (hole n n) := ⟨[], rfl⟩

def eqz3L : Seg (hole 1 1) := ⟨[.eqz, .eqz, .eqz], rfl⟩
def eqz1 : Seg (hole 1 1) := ⟨[.eqz], rfl⟩

def dropGetL (x : ℕ) : Seg (hole 0 0) := ⟨[.localGet x, .drop], rfl⟩
def dropGlobalL (x : ℕ) : Seg (hole 0 0) := ⟨[.globalGet x, .drop], rfl⟩

def teeFormL (x : ℕ) : Seg (hole 1 1) := ⟨[.localSet x, .localGet x], rfl⟩
def teeFormR (x : ℕ) : Seg (hole 1 1) := ⟨[.localTee x], rfl⟩

def rseSetL (x : ℕ) : Seg (hole 0 0) := ⟨[.localGet x, .localSet x], rfl⟩
def rseTeeL (x : ℕ) : Seg (hole 0 1) := ⟨[.localGet x, .localTee x], rfl⟩
def rseTeeR (x : ℕ) : Seg (hole 0 1) := ⟨[.localGet x], rfl⟩

/-! ## The information example -/

/-- The hole `0 → 0` with one visible function `0 : [] → [i32]`. -/
def callHole : HSig := ⟨[(0, 1)], 0, 0⟩

def callDropL : Seg callHole := ⟨[.call 0, .drop], rfl⟩
def callDropR : Seg callHole := ⟨[], rfl⟩

/-- The model where every function returns `0` and leaves the globals unchanged. -/
def pureZero : Env := fun _ _ g => {Ans.ret [0] g}

end Silmaril.Wasm.FnInst.Opt.Rules
