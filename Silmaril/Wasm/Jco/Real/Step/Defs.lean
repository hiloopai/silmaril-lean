module

public import Silmaril.Wasm.Jco.Real.Inst.Defs
public import Silmaril.Wasm.Jco.Styles.Lime.Defs

/-!
# Adaptor instructions against the reference engine: definitions

`XInstr.toLime fi` encodes an adaptor instruction as a Lime1 instruction, and
`Lime1.Instr.toCore` reads it in Core 3.0. This module fixes how a running adaptor function
(`Frame`: locals and operand stack, over flat values) is represented in a Core 3.0
configuration, so that `XInstr.step` over the real instance `realInst` can be compared with the
reference semantics `Steps` (`Silmaril.Wasm.Jco.Real.Step.Thms`):

* `coreOf fi i`: the Core 3.0 image of `i`;
* `stackCode st`: the operand stack `st` (top first) as Core value instructions (deepest
  first);
* `localsOf ls`: the locals as a Core frame's locals (all set);
* `FrameEnv mi ma fi cf`: the Core frame `cf` of the adaptor function is linked to the instance
  `mi`: its memory 0 is the instance's memory `ma`, and its function index `fi g` (as encoded,
  modulo `2^32`) is the function that `mi` exports under `g` (the adaptor imports the exports of
  the wrapped module in that order, `adaptorLime`);
* `Frag i`: **the fragment** of the agreement theorems: `local.get`, `local.set` (at indices
  below `2^32`), `i32.const`, `call`, `i32.eqz`, `i32.lt_u`, untyped `select`, and the integer
  loads of a width that Wasm has (`intWidthOk`) at an offset below `2^32`. Outside the fragment:
  `memory.copy`, `if … else … end`, and stores (stores are handled one at a time, with a typing
  hypothesis, see `Thms`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Binaryen (exportFunc?)
open Silmaril.Wasm (IntType NumType)

/-- The Core 3.0 image of an adaptor instruction (through its Lime1 encoding). -/
def coreOf (fi : String → Nat) (i : XInstr) : Silmaril.Wasm.Instr :=
  (XInstr.toLime fi i).toCore

/-- The Core 3.0 image of an instruction sequence, as administrative code. -/
def codeOf (fi : String → Nat) (is : List XInstr) : List Admin :=
  is.map fun i => .plain (coreOf fi i)

/-- An operand stack (top first) as Core value instructions (deepest first). -/
def stackCode (st : List Flat) : List Admin := vals (st.reverse.map toVal)

/-- Locals as the (all set) locals of a Core frame. -/
def localsOf (ls : List Flat) : List (Option Val) := ls.map fun v => some (toVal v)

/-- The Core frame `cf` of an adaptor function is linked to the instance `mi`. -/
structure FrameEnv (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)
    (cf : Silmaril.Wasm.Execution.Core.Frame) : Prop where
  /-- Memory 0 is the instance's memory. -/
  mem : cf.module.mems[0]? = some ma
  /-- Function index `fi g` is the function exported under `g`. -/
  call : ∀ g a, exportFunc? mi g = some a → cf.module.funcs[fi g % 2 ^ 32]? = some a

/-- The access widths (in bytes) of integer loads and stores of type `it`. -/
def intWidthOk : IntType → Nat → Bool
  | .i32, n => n == 1 || n == 2 || n == 4
  | .i64, n => n == 1 || n == 2 || n == 4 || n == 8

/-- **The fragment** of the agreement theorems. -/
inductive Frag : XInstr → Prop
  | localGet {i : Nat} (h : i < 2 ^ 32) : Frag (.base (.localGet i))
  | localSet {i : Nat} (h : i < 2 ^ 32) : Frag (.base (.localSet i))
  | i32Const (c : BitVec 32) : Frag (.base (.i32Const c))
  | call (g : String) (n : Nat) : Frag (.base (.call g n))
  | i32Eqz : Frag .i32Eqz
  | i32LtU : Frag .i32LtU
  | select : Frag .select
  | loadInt {it : IntType} {n : Nat} {sx : Bool} {off : Nat} (hn : intWidthOk it n = true)
      (hoff : off < 2 ^ 32) : Frag (.load (.int it) n sx off)

end Silmaril.Wasm.Jco.Real
