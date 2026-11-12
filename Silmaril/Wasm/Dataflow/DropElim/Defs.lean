module

public import Silmaril.Wasm.Dataflow.Fragment.Defs

/-!
# an earlier step of the two-pass DCE, dropped pure producers: definitions

The second pass of `Silmaril.Wasm.Dataflow.Dce` needs no liveness: a removable producer
(`pureArity? i = some n`: a constant, `local.get`, a trap-free numeric operator, `select`)
immediately followed by `drop` is replaced by `n` `drop`s, which discard its operands. A
value followed by `drop` is the case `n = 0` and disappears. The pass recurses into
`block`, `loop` and `if` bodies. This is the "dead code with no live side effects" of the
*Optimising Compilers* slides (Lecture 5, p. 68) on the operand stack; in Binaryen it is
part of `Vacuum`.

The proofs describe the transformation by the inductive *erasure* relation `Erase` rather
than by `dropElimSeq`. `Erase` is closed under `++` by a constructor, so the fusion of a
producer with a `drop` across an append boundary is a constructor rather than a case
split. It also lets a `TRAP` or a pending exception (`REF.EXN_ADDR a; THROW_REF`) absorb the
code after it: `Step/trap-instrs` and `Step/throw_ref-instrs` under `Step/ctxt-instrs`
absorb that code one instruction at a time, and without these constructors the simulation
fails (`Silmaril.Wasm.Dataflow.Litmus`).

`ERel` is the simulation relation: equal store, equal frame, erased code.

Ported from an earlier development `Silmaril/Wasm/Dataflow/DropElim.lean`. The source
had two relations, `Erase` (no exception absorption) for source bodies and `EraseT` for
running code, and proved most lemmas for both; the port keeps one relation, `EraseT` under
the name `Erase`. The source's
`Erase` survives as `Litmus.OldErase`, the relation of the throw counterexample.
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Is the instruction `drop`? -/
def isDrop : Instr → Bool
  | .drop => true
  | _ => false

mutual
/-- an earlier step on one instruction: recurse into structured bodies. -/
def dropElimInstr : Instr → Instr
  | .block bt body => .block bt (dropElimSeq body)
  | .loop bt body => .loop bt (dropElimSeq body)
  | .if_ bt b₁ b₂ => .if_ bt (dropElimSeq b₁) (dropElimSeq b₂)
  | i => i

/-- an earlier step on an instruction sequence. -/
def dropElimSeq : List Instr → List Instr
  | [] => []
  | [i] => [dropElimInstr i]
  | i :: j :: is =>
      match pureArity? i with
      | some n =>
          if isDrop j then List.replicate n .drop ++ dropElimSeq is
          else dropElimInstr i :: dropElimSeq (j :: is)
      | none => dropElimInstr i :: dropElimSeq (j :: is)
end

/-- an earlier step on a function body. -/
def dropElim (e : Expr) : Expr := dropElimSeq e

/-- Erasure of dropped pure producers, as a relation on administrative code. It is closed
under `++` by a constructor, and a `TRAP` or a pending exception absorbs the code after it.
Only labels need recursive closure: the pass leaves handler and frame bodies unchanged. -/
inductive Erase : List Admin → List Admin → Prop where
  | nil : Erase [] []
  /-- Erasure is closed under `++`. -/
  | append {a a' b b' : List Admin} (ha : Erase a a') (hb : Erase b b') :
      Erase (a ++ b) (a' ++ b')
  /-- Any instruction may be kept. -/
  | keep (a : Admin) : Erase [a] [a]
  /-- A removable producer of arity `n` followed by `drop` becomes `n` drops (a value
  followed by `drop` disappears). -/
  | pure {a : Admin} {n : Nat} (h : adminPureArity? a = some n) :
      Erase [a, .plain .drop] (List.replicate n (.plain .drop))
  | block (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      Erase [.plain (.block bt b)] [.plain (.block bt b')]
  | loop (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      Erase [.plain (.loop bt b)] [.plain (.loop bt b')]
  | if_ (bt : BlockType) {b₁ b₁' b₂ b₂' : List Instr}
      (h₁ : Erase (expression b₁) (expression b₁'))
      (h₂ : Erase (expression b₂) (expression b₂')) :
      Erase [.plain (.if_ bt b₁ b₂)] [.plain (.if_ bt b₁' b₂')]
  | label (n : Nat) {cont cont' : List Instr} {body body' : List Admin}
      (hc : Erase (expression cont) (expression cont')) (hb : Erase body body') :
      Erase [.label n cont body] [.label n cont' body']
  /-- A `TRAP` absorbs the code after it. -/
  | trap (rest : List Admin) : Erase (.trap :: rest) [.trap]
  /-- A pending exception absorbs the code after it. -/
  | throwRef (a : Nat) (rest : List Admin) : Erase (throwing a ++ rest) (throwing a)

/-- A single erasure rewrite whose source is not entirely values. -/
inductive Erase.Atom : List Admin → List Admin → Prop where
  | keep (a : Admin) (ha : a.val? = none) : Atom [a] [a]
  | pure {a : Admin} {n : Nat} (h : adminPureArity? a = some n) :
      Atom [a, .plain .drop] (List.replicate n (.plain .drop))
  | block (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      Atom [.plain (.block bt b)] [.plain (.block bt b')]
  | loop (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      Atom [.plain (.loop bt b)] [.plain (.loop bt b')]
  | if_ (bt : BlockType) {b₁ b₁' b₂ b₂' : List Instr}
      (h₁ : Erase (expression b₁) (expression b₁'))
      (h₂ : Erase (expression b₂) (expression b₂')) :
      Atom [.plain (.if_ bt b₁ b₂)] [.plain (.if_ bt b₁' b₂')]
  | label (n : Nat) {cont cont' : List Instr} {body body' : List Admin}
      (hc : Erase (expression cont) (expression cont')) (hb : Erase body body') :
      Atom [.label n cont body] [.label n cont' body']
  | trap (rest : List Admin) : Atom (.trap :: rest) [.trap]
  | throwRef (a : Nat) (rest : List Admin) : Atom (throwing a ++ rest) (throwing a)

/-- The single-instruction exits which labels bubble without executing. -/
def Erase.ExitOne (a : Admin) : Prop :=
  (∃ l, a = .plain (.br l)) ∨ a = .plain .return_ ∨ a.IsReturnCallRef

/-- The structured source-instruction congruences used . -/
inductive Erase.StructPair : Instr → Instr → Prop where
  | block (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      StructPair (.block bt b) (.block bt b')
  | loop (bt : BlockType) {b b' : List Instr} (h : Erase (expression b) (expression b')) :
      StructPair (.loop bt b) (.loop bt b')
  | if_ (bt : BlockType) {b₁ b₁' b₂ b₂' : List Instr}
      (h₁ : Erase (expression b₁) (expression b₁'))
      (h₂ : Erase (expression b₂) (expression b₂')) :
      StructPair (.if_ bt b₁ b₂) (.if_ bt b₁' b₂')

/-- The pass-2 simulation relation: equal store and frame, erased code. -/
structure ERel {H : Type} (c d : Config H) : Prop where
  store : d.store = c.store
  frame : d.frame = c.frame
  code : Erase c.code d.code

end Silmaril.Wasm.Dataflow
