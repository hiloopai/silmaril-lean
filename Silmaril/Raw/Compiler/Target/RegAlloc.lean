module

public import Silmaril.Machine.CBackend.Lir.Syntax.Defs
public import Std.Data.HashMap
public import Std.Data.TreeMap

/-! # Register allocation by renumbering virtual registers

`Lir.Alloc.firstK k` keeps virtual registers `0 … k - 1` in physical registers and spills
the others. `renumber k p` renames the virtual registers of each function of a linked
Lir program before that spill, so that the `k` register homes go to the most used
virtual registers and are shared between virtual registers whose live ranges are
disjoint:

* block-level liveness (backward dataflow to a fixpoint) gives each virtual register a
  live interval over the function's blocks in list order: every point where it is
  defined, read, live into a block (the block's header) or live out of it (after its
  terminator), and the entry header for parameters; an instruction reads before it
  writes, so its dying operands may share their number with its destination;
* each use or definition weighs `8 ^ d`, where `d` (at most 4) is the number of
  backward edges, in list order, whose range contains the block;
* in decreasing weight, a virtual register takes the first number below `k` whose
  intervals do not meet its own; failing that, it gets a fresh number `≥ k` of its own
  (a spill slot of its own);
* moves between two virtual registers that receive the same number are dropped.

A function whose liveness does not converge within its fuel is left unchanged.

## Intended theorem

For every function, two virtual registers with the same new number are never live at
the same point, nor is one written while the other is live; so the renamed program
refines the original one (`Lir.sem`, the identity convention), and `spill (firstK k)`
of it is valid by `Lir.Alloc.spill_behaves`. Reads of registers never written (stuck in
Lir) may observe another register's value.
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine

/-! ## Registers read and written -/

def opUses : Lir.Op Nat → List Nat
  | .const _ _ | .slotGet _ _ => []
  | .move _ s | .unary _ _ s | .load _ _ _ s _ | .slotSet _ s => [s]
  | .binary _ _ x y | .store _ x _ y => [x, y]

def opDefs : Lir.Op Nat → List Nat
  | .const d _ | .move d _ | .unary _ d _ | .binary _ d _ _ | .load _ _ d _ _
  | .slotGet d _ => [d]
  | .store .. | .slotSet .. => []

def locRegs (ls : List (Lir.Loc Nat)) : List Nat :=
  ls.filterMap fun | .reg r => some r | .slot _ => none

def instrUses : Lir.Instr Nat → List Nat
  | .op o => opUses o
  | .call _ args _ => locRegs args
  | .fop _ _ x y => [x, y]

def instrDefs : Lir.Instr Nat → List Nat
  | .op o => opDefs o
  | .call _ _ res => locRegs res
  | .fop _ d _ _ => [d]

def termUses : Lir.Term Nat → List Nat
  | .branch c _ _ => [c]
  | .ret ls => locRegs ls
  | .jump _ | .trap => []

def termSuccs : Lir.Term Nat → List Nat
  | .jump l => [l]
  | .branch _ l₁ l₂ => [l₁, l₂]
  | .ret _ | .trap => []

/-! ## Sets as sorted arrays without duplicates -/

def ofList (l : List Nat) : Array Nat :=
  (l.toArray.qsort (· < ·)).foldl (fun a x => if a.back? == some x then a else a.push x) #[]

/-- The union of two sorted sets. -/
def union (a b : Array Nat) : Array Nat := Id.run do
  let mut out := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  for _ in [0:a.size + b.size] do
    match a[i]?, b[j]? with
    | some x, some y =>
      if x < y then
        out := out.push x
        i := i + 1
      else if y < x then
        out := out.push y
        j := j + 1
      else
        out := out.push x
        i := i + 1
        j := j + 1
    | some x, none =>
      out := out.push x
      i := i + 1
    | none, some y =>
      out := out.push y
      j := j + 1
    | none, none => pure ()
  return out

/-- The elements of the sorted set `a` that are not in the sorted set `b`. -/
def diff (a b : Array Nat) : Array Nat := Id.run do
  let mut out := Array.mkEmpty a.size
  let mut j := 0
  for x in a do
    while j < b.size && b[j]! < x do j := j + 1
    if !(j < b.size && b[j]! == x) then out := out.push x
  return out

/-! ## Liveness -/

/-- Upward-exposed uses and definitions of a block. -/
def genKill (b : Lir.Block Nat) : Array Nat × Array Nat := Id.run do
  let mut gen : List Nat := []
  let mut kill : Std.HashSet Nat := {}
  for i in b.instrs do
    for u in instrUses i do
      if !kill.contains u then gen := u :: gen
    for d in instrDefs i do
      kill := kill.insert d
  for u in termUses b.term do
    if !kill.contains u then gen := u :: gen
  return (ofList gen, ofList kill.toList)

/-- Live-in and live-out sets of every block, or `none` if no fixpoint is reached
within `fuel` backward passes. -/
def liveness (blocks : Array (Lir.Block Nat)) (fuel : Nat) :
    Option (Array (Array Nat) × Array (Array Nat)) := Id.run do
  let gk := blocks.map genKill
  let mut liveIn : Array (Array Nat) := blocks.map fun _ => #[]
  let mut liveOut : Array (Array Nat) := blocks.map fun _ => #[]
  for _ in [0:fuel] do
    let mut changed := false
    for k in [0:blocks.size] do
      let b := blocks.size - 1 - k
      let out := (termSuccs (blocks[b]?.map (·.term) |>.getD .trap)).foldl (fun s l => union s (liveIn[l]?.getD #[])) #[]
      let inn := union gk[b]!.1 (diff out gk[b]!.2)
      -- The sets only grow, so a change is a change of size.
      if inn.size != liveIn[b]!.size || out.size != liveOut[b]!.size then
        changed := true
        liveIn := liveIn.set! b inn
        liveOut := liveOut.set! b out
    if !changed then return some (liveIn, liveOut)
  return none

/-! ## Intervals and weights -/

structure Info where
  start : Nat
  stop : Nat
  weight : Nat

def Info.extend (i : Option Info) (pos w : Nat) : Info :=
  match i with
  | none => ⟨pos, pos, w⟩
  | some i => ⟨min i.start pos, max i.stop pos, i.weight + w⟩

/-- Loop depth of each block: the number of backward edges `b → t` (`t ≤ b`) with
`t ≤ i ≤ b`. -/
def loopDepth (blocks : Array (Lir.Block Nat)) : Array Nat := Id.run do
  let mut delta : Array Int := Array.replicate (blocks.size + 1) 0
  for h : b in [0:blocks.size] do
    for t in termSuccs blocks[b].term do
      if t ≤ b then
        delta := delta.modify t (· + 1)
        delta := delta.modify (b + 1) (· - 1)
  let mut d : Int := 0
  let mut out := Array.mkEmpty blocks.size
  for i in [0:blocks.size] do
    d := d + delta[i]!
    out := out.push d.toNat
  return out

/-- Interval and weight of every virtual register of a function. The `n`-th point of the
function in list order (a block header, an instruction or a terminator) reads at `2n` and
writes at `2n + 1`, so a register read for the last time by an instruction can share its
number with the register that instruction writes. -/
def infos (fn : Lir.Func Nat) (blocks : Array (Lir.Block Nat))
    (liveIn liveOut : Array (Array Nat)) : Std.HashMap Nat Info := Id.run do
  let depth := loopDepth blocks
  let mut m : Std.HashMap Nat Info := {}
  let mut pos := 0
  for h : b in [0:blocks.size] do
    let blk := blocks[b]
    let w := 8 ^ min depth[b]! 4
    for v in liveIn[b]! do m := m.insert v (Info.extend m[v]? (2 * pos) 0)
    if b == fn.entry then
      for v in locRegs fn.params do m := m.insert v (Info.extend m[v]? (2 * pos + 1) 1)
    pos := pos + 1
    for i in blk.instrs do
      for v in instrUses i do m := m.insert v (Info.extend m[v]? (2 * pos) w)
      for v in instrDefs i do m := m.insert v (Info.extend m[v]? (2 * pos + 1) w)
      pos := pos + 1
    for v in termUses blk.term do m := m.insert v (Info.extend m[v]? (2 * pos) w)
    for v in liveOut[b]! do m := m.insert v (Info.extend m[v]? (2 * pos + 1) 0)
    pos := pos + 1
  -- Registers outside every block (parameters of a function without its entry block).
  for v in locRegs fn.params do
    if !m.contains v then m := m.insert v ⟨2 * pos, 2 * pos, 0⟩
  return m

/-! ## Assignment -/

/-- Does the interval `[s, e]` meet one of the disjoint intervals of `t` (start ↦ end)? -/
def meets (t : Std.TreeMap Nat Nat) (s e : Nat) : Bool :=
  match t.getEntryLE? e with
  | some (_, e') => s ≤ e'
  | none => false

/-- The new number of every virtual register of a function. -/
def assign (k : Nat) (m : Std.HashMap Nat Info) : Std.HashMap Nat Nat := Id.run do
  let order := m.toArray.qsort fun (v, a) (w, b) =>
    a.weight > b.weight || (a.weight == b.weight &&
      (a.start < b.start || (a.start == b.start && v < w)))
  let mut colors : Array (Std.TreeMap Nat Nat) := Array.replicate k {}
  let mut out : Std.HashMap Nat Nat := {}
  let mut next := k
  for (v, i) in order do
    match (List.range k).find? fun c => !meets colors[c]! i.start i.stop with
    | some c =>
      colors := colors.modify c (·.insert i.start i.stop)
      out := out.insert v c
    | none =>
      out := out.insert v next
      next := next + 1
  return out

/-! ## Renaming -/

def renameOp (σ : Nat → Nat) : Lir.Op Nat → Lir.Op Nat
  | .const d v => .const (σ d) v
  | .move d s => .move (σ d) (σ s)
  | .unary op d s => .unary op (σ d) (σ s)
  | .binary op d x y => .binary op (σ d) (σ x) (σ y)
  | .load w e d b off => .load w e (σ d) (σ b) off
  | .store w b off s => .store w (σ b) off (σ s)
  | .slotGet d n => .slotGet (σ d) n
  | .slotSet n s => .slotSet n (σ s)

def renameLoc (σ : Nat → Nat) : Lir.Loc Nat → Lir.Loc Nat
  | .reg r => .reg (σ r)
  | .slot n => .slot n

def renameInstr (σ : Nat → Nat) : Lir.Instr Nat → List (Lir.Instr Nat)
  | .op o =>
    match renameOp σ o with
    | .move d s => if d == s then [] else [.op (.move d s)]
    | o' => [.op o']
  | .call f args res => [.call f (args.map (renameLoc σ)) (res.map (renameLoc σ))]
  | .fop op d x y => [.fop op (σ d) (σ x) (σ y)]

def renameTerm (σ : Nat → Nat) : Lir.Term Nat → Lir.Term Nat
  | .jump l => .jump l
  | .branch c l₁ l₂ => .branch (σ c) l₁ l₂
  | .ret ls => .ret (ls.map (renameLoc σ))
  | .trap => .trap

def renameFunc (σ : Nat → Nat) (fn : Lir.Func Nat) : Lir.Func Nat where
  params := fn.params.map (renameLoc σ)
  entry := fn.entry
  blocks := fn.blocks.map fun b => ⟨b.instrs.flatMap (renameInstr σ), renameTerm σ b.term⟩

/-- Renumber the virtual registers of one function for `k` register homes. -/
def renumberFunc (k : Nat) (fn : Lir.Func Nat) : Lir.Func Nat :=
  let blocks := fn.blocks.toArray
  match liveness blocks (blocks.size + 2) with
  | none => fn
  | some (liveIn, liveOut) =>
    let σ := assign k (infos fn blocks liveIn liveOut)
    renameFunc (fun v => σ.getD v v) fn

/-- Renumber every function of a program for `k` register homes. -/
def renumber (k : Nat) (p : Lir.Prog Nat) : Lir.Prog Nat :=
  ⟨p.funcs.map (renumberFunc k)⟩

end Silmaril.Compile.Target.RegAlloc
