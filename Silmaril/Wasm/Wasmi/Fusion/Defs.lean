module

public import Silmaril.Wasm.Wasmi.Defs

/-!
# The select fusion of wasmi 2.0.0, as the harness probes observe it

`Silmaril.Wasm.Wasmi` models issue #2046 by `fuse`, which rewrites exactly the reported shape
`i32.const 0; local.get x; i32.ne; select`. The probe scripts of the conformance harness
(`tools/wasm-conformance/probes/issue2046.wast`, run against `wasmi = "=2.0.0"`) show a wider
class. wasmi 2.0.0 returns the second operand of `select` whatever the condition when it is
`i32.ne` of a local and `0` **in either order**, and the first operand when the condition is
`i32.eq` of a local and `0` or `i32.eqz` of a local; any operand type, typed or untyped
`select`, also inside a block. It is correct when the operand of the comparison is not a
`local.get`, when the constant is not `0`, for `i64` comparisons, `lt`/`gt`, and when the
condition goes through a local, `br_if` or `if`.

This topic names the three variants of the reproducer the probes add, and a wider translation:

* `swapBody`, `eqBody`, `eqzBody`: `f a b` returning `7` when the condition holds, else `a`,
  with conditions `b != 0` (operands swapped), `0 == b` and `eqz b`; `modOf`, `storeOf`,
  `ptOf`: the module (the reproducer's type and export), its allocation and its point;
* `fusedSel1`: the translation of an `eq`/`eqz` shape, which reads the condition `1`;
* `fuseW`, `fuseStoreW`, `obsW`: **the wider translation**, `fuse` plus the four further shapes
  `local.get x; i32.const 0; i32.ne; select`, `i32.const 0; local.get x; i32.eq; select`,
  `local.get x; i32.const 0; i32.eq; select` and `local.get x; i32.eqz; select`, and its
  observations (Core 3.0 on the translated store).

The shapes are read off the probe; they are not derived from wasmi's source. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.Fusion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Atlas

variable {H : Type}

/-! ## The probe's variants of the reproducer -/

/-- `(select (i32.const 7) (local.get $a) (i32.ne (local.get $b) (i32.const 0)))`. -/
def swapBody : List Instr :=
  [.intConst .i32 7, .localGet ⟨0⟩, .localGet ⟨1⟩, .intConst .i32 0, .intRelOp .i32 .ne,
    .select none]

/-- `(select (i32.const 7) (local.get $a) (i32.eq (i32.const 0) (local.get $b)))`. -/
def eqBody : List Instr :=
  [.intConst .i32 7, .localGet ⟨0⟩, .intConst .i32 0, .localGet ⟨1⟩, .intRelOp .i32 .eq,
    .select none]

/-- `(select (i32.const 7) (local.get $a) (i32.eqz (local.get $b)))`. -/
def eqzBody : List Instr :=
  [.intConst .i32 7, .localGet ⟨0⟩, .localGet ⟨1⟩, .intTestOp .i32 .eqz, .select none]

/-- The reproducer's module with another body for `f`. -/
def modOf (body : List Instr) : Module := { reproMod with funcs := [⟨⟨0⟩, [], body⟩] }

/-- The spec's allocation of `modOf body`. -/
def prepOf (body : List Instr) : Config Empty × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Empty) (modOf body) []).getD (⟨{}, {}, []⟩, none)

/-- Its store. -/
def storeOf (body : List Instr) : Store Empty := (prepOf body).1.store

/-- Its point, with no host functions. -/
def ptOf (body : List Instr) : Core.Pt Empty := (storeOf body, fun _ _ _ _ => False)

/-! ## The wider translation -/

/-- The translation of an `eq`/`eqz` shape: the condition read is `1`. -/
def fusedSel1 (x : LocalIdx) (t : Option (List ValType)) : List Instr :=
  [.localGet x, .drop, .intConst .i32 1, .select t]

mutual
/-- The wider translation of one instruction: recursion into structured bodies. -/
def fuseWI : Instr → Instr
  | .block bt b => .block bt (fuseW b)
  | .loop bt b => .loop bt (fuseW b)
  | .if_ bt b₁ b₂ => .if_ bt (fuseW b₁) (fuseW b₂)
  | .tryTable bt cs b => .tryTable bt cs (fuseW b)
  | i => i

/-- **The wider select fusion**: `fuse`'s shape, the swapped `ne` shape (condition `0`), and the
`eq` and `eqz` shapes (condition `1`). -/
def fuseW : List Instr → List Instr
  | [] => []
  | .intConst .i32 c :: .localGet x :: .intRelOp .i32 .ne :: .select t :: rest =>
    if c = 0 then fusedSel x t ++ fuseW rest
    else .intConst .i32 c :: fuseW (.localGet x :: .intRelOp .i32 .ne :: .select t :: rest)
  | .localGet x :: .intConst .i32 c :: .intRelOp .i32 .ne :: .select t :: rest =>
    if c = 0 then fusedSel x t ++ fuseW rest
    else .localGet x :: fuseW (.intConst .i32 c :: .intRelOp .i32 .ne :: .select t :: rest)
  | .intConst .i32 c :: .localGet x :: .intRelOp .i32 .eq :: .select t :: rest =>
    if c = 0 then fusedSel1 x t ++ fuseW rest
    else .intConst .i32 c :: fuseW (.localGet x :: .intRelOp .i32 .eq :: .select t :: rest)
  | .localGet x :: .intConst .i32 c :: .intRelOp .i32 .eq :: .select t :: rest =>
    if c = 0 then fusedSel1 x t ++ fuseW rest
    else .localGet x :: fuseW (.intConst .i32 c :: .intRelOp .i32 .eq :: .select t :: rest)
  | .localGet x :: .intTestOp .i32 .eqz :: .select t :: rest => fusedSel1 x t ++ fuseW rest
  | i :: rest => fuseWI i :: fuseW rest
end

/-- The wider translation of a function instance (Wasm code only). -/
def fuseFuncW (fi : FuncInst H) : FuncInst H :=
  match fi.code with
  | .wasm g => { fi with code := .wasm { g with body := fuseW g.body } }
  | .host _ => fi

/-- The wider translation of a store. -/
def fuseStoreW (s : Store H) : Store H := { s with funcs := s.funcs.map fuseFuncW }

/-- **The observations of the wider model**: Core 3.0 on the translated store. -/
def obsW (P : Numerics.Profile) (x : Core.Pt H) (c : Core.Call) : Set (Behaviour Val) :=
  Core.obs P (fuseStoreW x.1, x.2) c

end Silmaril.Wasm.Wasmi.Fusion
