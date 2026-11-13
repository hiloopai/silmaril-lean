module

public import Mathlib.Data.Set.Basic

/-!
# A universal carrier for Wasm syntax

One syntax for every Wasm dialect in this repository (Wasm 1.0, 2.0, 3.0, Lime, WasmFX and
whatever comes next): an instruction is an **opcode** applied to **immediates**, **nested
blocks** and a **handler table**. Nothing about a particular opcode is built in; which opcodes
exist, and what they mean, is the business of signatures (`Silmaril.Wasm.Unified.Sig`) and models
(`Silmaril.Wasm.Unified.Model`). See `docs/projects/wasm-wasi.md`.

* `Opcode`: a binary opcode (an optional prefix byte and a number, e.g. `0xFC 10` for
  `memory.copy`), or an open name with numeric parameters (e.g. a family name and the codes of
  its operator fields). Both forms are open: any number, any name.
* `Imm`: an immediate: a natural number, an integer, a string, or a list of immediates.
* `Handler`: an entry of a handler table (`try_table` catch clauses, WasmFX `resume` handlers):
  a kind name and immediates.
* `UInstr O`: instructions over an opcode type `O`. It is a functor in `O`: `UInstr.map f`
  renames opcodes, recursively through the nested blocks. The universal syntax is
  `UInstr Opcode`; the syntax of a signature `S` is `UInstr S.Op` over the subtype of its
  opcodes, and renaming along a signature morphism is sentence translation.
* `UInstr.ops`: the opcodes occurring in an instruction (recursively).
-/

@[expose] public section

namespace Silmaril.Wasm.Unified

/-- An opcode of the universal syntax: binary (optional prefix and number) or an open name with
numeric parameters. -/
inductive Opcode where
  /-- A binary opcode: an optional prefix byte (`0xFB`, `0xFC`, `0xFD`, ...) and a number. -/
  | bin (pre : Option Nat) (code : Nat)
  /-- An open name with numeric parameters (e.g. operator codes). -/
  | named (name : String) (params : List Nat)
  deriving DecidableEq, Repr, Inhabited

/-- An immediate operand. -/
inductive Imm where
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  | list (l : List Imm)
  deriving Repr, Inhabited

/-- An entry of a handler table: a kind (`catch`, `catch_ref`, `on`, `switch`, ...) and its
immediates (tags, labels). -/
structure Handler where
  /-- The kind of the entry. -/
  kind : String
  /-- Its immediates. -/
  imms : List Imm
  deriving Repr, Inhabited

/-- **Universal instructions** over an opcode type `O`: an opcode, immediates, nested blocks
(instruction sequences) and a handler table. -/
inductive UInstr (O : Type) where
  | op (o : O) (imms : List Imm) (blocks : List (List (UInstr O))) (handlers : List Handler)
  deriving Inhabited

/-- Instruction sequences. -/
abbrev UCode (O : Type) : Type := List (UInstr O)

namespace UInstr

variable {O O' O'' : Type}

mutual
/-- Rename the opcodes of an instruction (through its blocks). -/
def map (f : O → O') : UInstr O → UInstr O'
  | .op o imms bs hs => .op (f o) imms (mapBlocks f bs) hs
/-- Rename the opcodes of an instruction sequence. -/
def mapCode (f : O → O') : UCode O → UCode O'
  | [] => []
  | i :: c => map f i :: mapCode f c
/-- Rename the opcodes of a list of blocks. -/
def mapBlocks (f : O → O') : List (UCode O) → List (UCode O')
  | [] => []
  | b :: bs => mapCode f b :: mapBlocks f bs
end

mutual
/-- The opcodes occurring in an instruction. -/
def ops : UInstr O → Set O
  | .op o _ bs _ => insert o (opsBlocks bs)
/-- The opcodes occurring in an instruction sequence. -/
def opsCode : UCode O → Set O
  | [] => ∅
  | i :: c => ops i ∪ opsCode c
/-- The opcodes occurring in a list of blocks. -/
def opsBlocks : List (UCode O) → Set O
  | [] => ∅
  | b :: bs => opsCode b ∪ opsBlocks bs
end

mutual
theorem map_id : (i : UInstr O) → i.map id = i
  | .op o imms bs hs => by rw [map, mapBlocks_id]; rfl
theorem mapCode_id : (c : UCode O) → mapCode id c = c
  | [] => rfl
  | i :: c => by rw [mapCode, map_id, mapCode_id]
theorem mapBlocks_id : (bs : List (UCode O)) → mapBlocks id bs = bs
  | [] => rfl
  | b :: bs => by rw [mapBlocks, mapCode_id, mapBlocks_id]
end

mutual
theorem map_map (f : O → O') (g : O' → O'') : (i : UInstr O) → (i.map f).map g = i.map (g ∘ f)
  | .op o imms bs hs => by rw [map, map, map, mapBlocks_map]; rfl
theorem mapCode_map (f : O → O') (g : O' → O'') :
    (c : UCode O) → mapCode g (mapCode f c) = mapCode (g ∘ f) c
  | [] => rfl
  | i :: c => by rw [mapCode, mapCode, mapCode, map_map, mapCode_map]
theorem mapBlocks_map (f : O → O') (g : O' → O'') :
    (bs : List (UCode O)) → mapBlocks g (mapBlocks f bs) = mapBlocks (g ∘ f) bs
  | [] => rfl
  | b :: bs => by rw [mapBlocks, mapBlocks, mapBlocks, mapCode_map, mapBlocks_map]
end

/-- `mapCode` is `List.map` of `map`. -/
theorem mapCode_eq (f : O → O') (c : UCode O) : mapCode f c = c.map (map f) := by
  induction c with
  | nil => rfl
  | cons i c ih => rw [mapCode, ih]; rfl

end UInstr

end Silmaril.Wasm.Unified
