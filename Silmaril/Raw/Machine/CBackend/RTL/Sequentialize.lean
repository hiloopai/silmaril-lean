module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Mathlib.Data.Nat.Pairing
public import Silmaril.Foundations.ForwardSim

/-!
# Landing every well-formed SSA function inside the sequentializable fragment

`Machine.Lift.erase` destructs `RTL.SSA` to `RTL` by turning each block
argument into a `move`. Emitting those moves in the order the argument list
gives is **wrong** when a target parameter is written before a later argument
reads it — the swap `L(a, b): … jump L(b, a)` becomes `a := b; b := a` and
loses `a` — so `erase`'s domain is restricted by `Lift.SequentialTransfers`,
and a λSSA swap loop flattened to `RTL.SSA` is outside it.

This pass removes the restriction without touching `erase`. It is a
semantics-preserving `RTL.SSA → RTL.SSA` transformation after which **every**
transfer is sequentializable, uniformly and by construction rather than by a
case analysis.

## The transformation

Give every block *fresh* parameters and copy them into the originals at the top
of the block:

```
L(p₀, p₁):  ops                 L(q₀, q₁):  p₀ := q₀
            jump M(a₀, a₁)   ↦              p₁ := q₁
                                            ops
                                            jump M(a₀, a₁)
```

The fresh names need a supply the register type does not have, so the pass
changes it: `sequentialize : Func R → Func (R ⊕ Nat)`, with the original
registers embedded by `Sum.inl` and the fresh parameter at position `i` of
block `l` named `Sum.inr (Nat.pair l i)`.

Every transfer's arguments are then `Sum.inl`s and every block's parameters are
`Sum.inr`s, so the two lists are disjoint and no parameter can be written before
an argument reads it. That is `sequentialize_argsDisjoint`, and it is what
`Lift.SequentialTransfers` follows from.

## Why not critical-edge splitting

Edge splitting is what anyone who knows the problem reaches for first, so it is
worth recording why this file does something else.

The textbook repair is to split every edge whose arguments permute the target's
parameters, inserting a block that receives the arguments into fresh parameters
and forwards them positionally. That works, but it **changes the control-flow
graph**, and `Func.WellFormed` contains `UsesDominated`, which is stated over
`Func.digraph`. Preserving it would need a path-correspondence argument showing
dominance survives the insertion of the new blocks — the projection of a path in
the split graph onto a path in the original, and back.

Moving the copies to the *head of the target block* instead of the *tail of the
edge* achieves the same thing and leaves the graph alone:
`sequentialize_digraph` says `(sequentialize fn).digraph = fn.digraph` on the
nose, so dominance is not merely preserved but literally the same relation, and
`UsesDominated` transports by a local argument about each block. The cost is
that a block with `k` parameters gains `k` moves whether it needed them or not,
which is the same cost edge splitting pays on the edges it splits.

The copies are correct with no scratch register for the reason the split block
is: the fresh parameters are written by the transfer and read by the moves, and
nothing else reads them, so the moves may run in any order. The original
parameters, which the body reads, are written by the moves and by nothing else.

## What is proved

* `sequentialize_wellFormed` — well-formedness is preserved, all four clauses.
  `SingleAssignment` holds because the fresh names are pairwise distinct
  (`Nat.pair` is injective) and disjoint from the `Sum.inl` image;
  `UsesDominated` holds because a use of an original parameter inside its block
  is now a use of a `move` destination earlier in the same block, and every
  other use is unchanged over an unchanged graph.
* `sequentialize_argsDisjoint` — no transfer's argument list meets its target's
  parameter list.
* `sequentializeProg_behaves` — a **behavioural `iff` with no hypotheses at
  all**, not even well-formedness: the transformation is syntactic and the
  correspondence is exact, so the two programs have the same four behaviours,
  stuck included. This is stronger than the pass needs to be — its consumer
  only ever applies it to well-formed programs — but the proof never uses
  well-formedness, so stating it as a side condition would be a claim about the
  proof rather than about the pass.

## Where `SequentialTransfers` is discharged

`Lift.SequentialTransfers` is defined in `Silmaril/Machine/Lift/Ssa.lean`, and
`Machine/RTL/` must not import `Machine/Lift/`: the lift checkers read the
pipeline, not the other way round. So the theorem named for the condition,
`Pipeline.sequentialize_sequentialTransfers`, lives one file up in
`Silmaril/Machine/Pipeline.lean`, where both are in scope. What this file states
is the `Lift`-free fact it rests on, `sequentialize_argsDisjoint`. The split is
deliberate layering, not an oversight.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.SSA

open Silmaril.Machine.Lir (Word Memory)

variable {R S : Type}

/-! ## Renaming registers

The pass embeds the original registers by `Sum.inl`, so it needs the action of
a register renaming on the syntax. Nothing here is specific to `Sum.inl`. -/

/-- An operation with its registers renamed. -/
def Op.mapRegs (g : R → S) : Op R → Op S
  | .const d v => .const (g d) v
  | .move d s => .move (g d) (g s)
  | .unary op d s => .unary op (g d) (g s)
  | .binary op d a b => .binary op (g d) (g a) (g b)
  | .load w e d base off => .load w e (g d) (g base) off
  | .store w base off src => .store w (g base) off (g src)
  | .call f args results => .call f (args.map g) (results.map g)

/-- A terminator with its registers renamed. Targets are untouched. -/
def Term.mapRegs (g : R → S) : Term R → Term S
  | .jump t as => .jump t (as.map g)
  | .cond c t₁ a₁ t₂ a₂ => .cond (g c) t₁ (a₁.map g) t₂ (a₂.map g)
  | .ret vs => .ret (vs.map g)
  | .trap => .trap

@[simp] theorem Op.uses_mapRegs (g : R → S) (o : Op R) :
    (o.mapRegs g).uses = o.uses.map g := by
  cases o <;> simp [Op.mapRegs, Op.uses]

@[simp] theorem Op.defs_mapRegs (g : R → S) (o : Op R) :
    (o.mapRegs g).defs = o.defs.map g := by
  cases o <;> simp [Op.mapRegs, Op.defs]

@[simp] theorem Term.uses_mapRegs (g : R → S) (t : Term R) :
    (t.mapRegs g).uses = t.uses.map g := by
  cases t <;> simp [Term.mapRegs, Term.uses]

@[simp] theorem Term.successors_mapRegs (g : R → S) (t : Term R) :
    (t.mapRegs g).successors = t.successors := by
  cases t <;> simp [Term.mapRegs, Term.successors]

@[simp] theorem Term.args_mapRegs (g : R → S) (t : Term R) :
    (t.mapRegs g).args = t.args.map (fun ta => (ta.1, ta.2.map g)) := by
  cases t <;> simp [Term.mapRegs, Term.args]

@[simp] theorem Term.okIn_mapRegs (g : R → S) (t : Term R) (results n : Nat) :
    (t.mapRegs g).okIn results n = t.okIn results n := by
  cases t <;> simp [Term.mapRegs, Term.okIn, Term.successors]

/-! ## Fresh parameters and the moves that consume them

Both lists are built by structural recursion threading the position, for the
reason `Silmaril/Machine/Lift/Ssa.lean` gives for its own layout functions: the
indexing lemmas below are then one induction each, rather than an exercise in
arithmetic over `zipIdx`. -/

/-- The fresh parameters of block `l` from position `i`: one `Sum.inr` per
original parameter, named by `Nat.pair` of the block and the position. -/
def freshParams (l : Label) : Nat → List R → List (R ⊕ Nat)
  | _, [] => []
  | i, _ :: ps => .inr (Nat.pair l i) :: freshParams l (i + 1) ps

/-- The entry moves of block `l` from position `i`: each original parameter
copied out of the fresh one that replaced it. -/
def paramMoves (l : Label) : Nat → List R → List (Op (R ⊕ Nat))
  | _, [] => []
  | i, p :: ps => .move (.inl p) (.inr (Nat.pair l i)) :: paramMoves l (i + 1) ps

@[simp] theorem freshParams_length (l : Label) (i : Nat) (ps : List R) :
    (freshParams l i ps).length = ps.length := by
  induction ps generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [freshParams, ih]

@[simp] theorem paramMoves_length (l : Label) (i : Nat) (ps : List R) :
    (paramMoves l i ps).length = ps.length := by
  induction ps generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [paramMoves, ih]

/-- The moves define exactly the original parameters, in order. -/
@[simp] theorem paramMoves_flatMap_defs (l : Label) (i : Nat) (ps : List R) :
    (paramMoves l i ps).flatMap Op.defs = ps.map Sum.inl := by
  induction ps generalizing i with
  | nil => rfl
  | cons _ _ ih => simp [paramMoves, Op.defs, ih]

/-- The move at position `j` copies parameter `j`. -/
theorem paramMoves_getElem? (l : Label) : ∀ (ps : List R) (i j : Nat),
    (paramMoves l i ps)[j]? = (ps[j]?).map fun p => .move (.inl p) (.inr (Nat.pair l (i + j)))
  | [], _, _ => by simp [paramMoves]
  | _ :: _, i, 0 => by simp [paramMoves]
  | _ :: ps, i, j + 1 => by
    simpa [paramMoves, Nat.add_assoc, Nat.add_comm 1 j] using paramMoves_getElem? l ps (i + 1) j

/-- Every fresh parameter of block `l` from position `i` is the name of some
position `i + j` with `j` inside the parameter list. -/
theorem mem_freshParams {l : Label} : ∀ (ps : List R) (i : Nat) (x : R ⊕ Nat),
    x ∈ freshParams l i ps → ∃ j, j < ps.length ∧ x = .inr (Nat.pair l (i + j))
  | [], _, _, h => by simp [freshParams] at h
  | _ :: ps, i, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨j, hj, rfl⟩ := mem_freshParams ps (i + 1) x h
      exact ⟨j + 1, by simpa using hj, by rw [Nat.add_assoc, Nat.add_comm 1 j]⟩

/-- `Nat.pair` is injective in its second argument. -/
theorem pair_inj_right {l i j : Nat} (h : Nat.pair l i = Nat.pair l j) : i = j := by
  have := congrArg Nat.unpair h
  simpa using this

/-- The fresh parameters of one block are pairwise distinct: `Nat.pair` is
injective and the positions differ. -/
theorem freshParams_nodup (l : Label) : ∀ (ps : List R) (i : Nat),
    (freshParams l i ps).Nodup
  | [], _ => by simp [freshParams]
  | _ :: ps, i => by
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, freshParams_nodup l ps (i + 1)⟩
    obtain ⟨j, -, hx⟩ := mem_freshParams (l := l) ps (i + 1) _ hmem
    have : Nat.pair l i = Nat.pair l (i + 1 + j) := by simpa using hx
    have := pair_inj_right this
    omega

/-! ## The pass -/

/-- One block with fresh parameters and the moves that copy them into the
originals. The body and the terminator are the originals with their registers
embedded by `Sum.inl`. -/
def seqBlock (l : Label) (b : Block R) : Block (R ⊕ Nat) where
  params := freshParams l 0 b.params
  ops := paramMoves l 0 b.params ++ b.ops.map (Op.mapRegs Sum.inl)
  term := b.term.mapRegs Sum.inl

/-- The blocks from label `l` on, each sequentialized under its own label. -/
def seqBlocks (l : Nat) : List (Block R) → List (Block (R ⊕ Nat))
  | [] => []
  | b :: bs => seqBlock l b :: seqBlocks (l + 1) bs

/-- **Give every block fresh parameters and copy them in at its head.** The
signature, the entry label and the control-flow graph are unchanged. -/
def sequentialize (fn : Func R) : Func (R ⊕ Nat) where
  sig := fn.sig
  entry := fn.entry
  blocks := seqBlocks 0 fn.blocks

/-- The pass applied to a whole program, function by function. -/
def sequentializeProg (p : Prog R) : Prog (R ⊕ Nat) := ⟨p.funcs.map sequentialize⟩

/-! ## Structure

The block list keeps its length and its indexing, which is what makes the
control-flow graph literally unchanged. -/

@[simp] theorem seqBlocks_length (l : Nat) (bs : List (Block R)) :
    (seqBlocks l bs).length = bs.length := by
  induction bs generalizing l with
  | nil => rfl
  | cons _ _ ih => simp [seqBlocks, ih]

theorem seqBlocks_getElem? (l : Nat) : ∀ (bs : List (Block R)) (j : Nat),
    (seqBlocks l bs)[j]? = (bs[j]?).map (seqBlock (l + j))
  | [], _ => by simp [seqBlocks]
  | _ :: _, 0 => by simp [seqBlocks]
  | _ :: bs, j + 1 => by
    simpa [seqBlocks, Nat.add_assoc, Nat.add_comm 1 j] using seqBlocks_getElem? (l + 1) bs j

/-- A property of every sequentialized block follows from the property of each
original block under its own label. -/
theorem forall_mem_seqBlocks {P : Block (R ⊕ Nat) → Prop} :
    ∀ (bs : List (Block R)) (l : Nat),
      (∀ (j : Nat) (b : Block R), bs[j]? = some b → P (seqBlock (l + j) b)) →
      ∀ b ∈ seqBlocks l bs, P b
  | [], _, _, _, h => by simp [seqBlocks] at h
  | b₀ :: bs, l, h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · simpa using h 0 b₀ rfl
    · refine forall_mem_seqBlocks bs (l + 1) (fun j b' hj => ?_) b hb
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j + 1) b' (by simpa using hj)

@[simp] theorem sequentialize_sig (fn : Func R) : (sequentialize fn).sig = fn.sig := rfl

@[simp] theorem sequentialize_entry (fn : Func R) : (sequentialize fn).entry = fn.entry := rfl

@[simp] theorem sequentialize_blocks_length (fn : Func R) :
    (sequentialize fn).blocks.length = fn.blocks.length := by simp [sequentialize]

@[simp] theorem sequentialize_block? (fn : Func R) (l : Label) :
    (sequentialize fn).block? l = (fn.block? l).map (seqBlock l) := by
  simpa [sequentialize, Func.block?] using seqBlocks_getElem? (R := R) 0 fn.blocks l

/-- The parameters of a sequentialized block are the fresh ones, and there are
as many as before. -/
@[simp] theorem seqBlock_params_length (l : Label) (b : Block R) :
    (seqBlock l b).params.length = b.params.length := by simp [seqBlock]

/-! ## The control-flow graph is unchanged

This is the point of copying at the head of the target rather than splitting
the edge: nothing about the graph moves, so dominance is not preserved but
*identical*, and `UsesDominated` needs no path argument. -/

@[simp] theorem sequentialize_succ (fn : Func R) (l : Label) :
    (sequentialize fn).succ l = fn.succ l := by
  simp only [Func.succ, sequentialize_block?]
  cases fn.block? l <;> simp [seqBlock]

/-- **The sequentialized function has the same control-flow graph.** -/
@[simp] theorem sequentialize_digraph (fn : Func R) :
    (sequentialize fn).digraph = fn.digraph := by
  simp only [Func.digraph, sequentialize_blocks_length, sequentialize_entry]
  congr 1
  funext l
  exact sequentialize_succ fn l

@[simp] theorem sequentialize_dominates (fn : Func R) (a b : Label) :
    (sequentialize fn).Dominates a b ↔ fn.Dominates a b := by
  simp [Func.Dominates]

/-! ## Definitions

A sequentialized block defines its fresh parameters and then everything the
original block defined. -/

theorem flatMap_defs_map_mapRegs (g : R → S) (os : List (Op R)) :
    (os.map (Op.mapRegs g)).flatMap Op.defs = (os.flatMap Op.defs).map g := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [ih]

@[simp] theorem seqBlock_defs (l : Label) (b : Block R) :
    (seqBlock l b).defs = freshParams l 0 b.params ++ b.defs.map Sum.inl := by
  simp [seqBlock, Block.defs, flatMap_defs_map_mapRegs]

@[simp] theorem sequentialize_defsOf (fn : Func R) (l : Label) :
    (sequentialize fn).defsOf l =
      (fn.block? l).elim [] (fun b => freshParams l 0 b.params) ++ (fn.defsOf l).map Sum.inl := by
  simp only [Func.defsOf, sequentialize_block?]
  cases fn.block? l <;> simp

/-! ## Every transfer is sequentializable

The two halves: a transfer's arguments are all original registers, and a
block's parameters are all fresh ones. Disjointness is then the disjointness of
`Sum.inl` from `Sum.inr`, which is why this holds for *every* transfer and not
only the offending ones. -/

/-- Every argument of every transfer is an original register. -/
theorem mem_args_isInl (fn : Func R) :
    ∀ b ∈ (sequentialize fn).blocks, ∀ ta ∈ b.term.args, ∀ r ∈ ta.2, ∃ x, r = Sum.inl x := by
  show ∀ b ∈ seqBlocks 0 fn.blocks, _
  refine forall_mem_seqBlocks fn.blocks 0 (fun j b₀ _ => ?_)
  intro ta hta r hr
  simp only [seqBlock, Term.args_mapRegs, List.mem_map] at hta
  obtain ⟨ta₀, -, rfl⟩ := hta
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hr
  exact ⟨x, rfl⟩

/-- Every parameter of every block is a fresh register. -/
theorem mem_params_isInr (fn : Func R) {l : Label} {b : Block (R ⊕ Nat)}
    (hb : (sequentialize fn).block? l = some b) {r : R ⊕ Nat} (hr : r ∈ b.params) :
    ∃ m, r = Sum.inr m := by
  rw [sequentialize_block?] at hb
  obtain ⟨b₀, -, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨j, -, hx⟩ := mem_freshParams b₀.params 0 r hr
  exact ⟨_, hx⟩

/-- **No transfer's argument list meets its target's parameter list.** This is
the condition `Machine.Lift.erase` needs: with the two lists disjoint, no
parameter can be written before a later argument reads it, so the moves `erase`
emits in order implement the simultaneous write. -/
theorem sequentialize_argsDisjoint (fn : Func R) {b : Block (R ⊕ Nat)}
    (hb : b ∈ (sequentialize fn).blocks) {ta : Label × List (R ⊕ Nat)} (hta : ta ∈ b.term.args)
    {tb : Block (R ⊕ Nat)} (htb : (sequentialize fn).block? ta.1 = some tb) :
    ∀ r ∈ tb.params, r ∉ ta.2 := by
  intro r hr hmem
  obtain ⟨m, rfl⟩ := mem_params_isInr fn htb hr
  obtain ⟨x, hx⟩ := mem_args_isInl fn b hb ta hta _ hmem
  simp at hx

/-! ## Well-formedness is preserved -/

theorem sequentialize_argsMatch (fn : Func R) (h : fn.ArgsMatch) :
    (sequentialize fn).ArgsMatch := by
  rw [Func.ArgsMatch, Func.argsMatch, List.all_eq_true] at h ⊢
  show ∀ b ∈ seqBlocks 0 fn.blocks, _
  refine forall_mem_seqBlocks fn.blocks 0 (fun j b₀ hj => ?_)
  have h₀ := h b₀ (List.mem_of_getElem? hj)
  rw [List.all_eq_true] at h₀ ⊢
  intro ta hta
  simp only [seqBlock, Term.args_mapRegs, List.mem_map] at hta
  obtain ⟨ta₀, hta₀, rfl⟩ := hta
  have hm := h₀ ta₀ hta₀
  simp only [sequentialize_block?]
  cases hbl : fn.block? ta₀.1 with
  | none => rw [hbl] at hm; simp at hm
  | some tb => rw [hbl] at hm; simpa using hm

theorem sequentialize_wellFormedSig (fn : Func R) (h : fn.WellFormedSig) :
    (sequentialize fn).WellFormedSig := by
  obtain ⟨he, hp, hok⟩ := h
  refine ⟨by simpa using he, ?_, ?_⟩
  · simp only [sequentialize_entry, sequentialize_block?, sequentialize_sig]
    cases hbl : fn.block? fn.entry with
    | none => rw [hbl] at hp; simp at hp
    | some b => rw [hbl] at hp; simpa using hp
  · rw [List.all_eq_true] at hok ⊢
    show ∀ b ∈ seqBlocks 0 fn.blocks, _
    refine forall_mem_seqBlocks fn.blocks 0 (fun j b₀ hj => ?_)
    simpa [seqBlock] using hok b₀ (List.mem_of_getElem? hj)

/-! ### Single assignment

A sequentialized block defines its fresh parameters and then the `Sum.inl`
image of what the original defined. The fresh names of block `l` are `inr`s
whose first `Nat.unpair` component is `l`, so blocks cannot collide with each
other, and no fresh name is an `inl`, so they cannot collide with the original
definitions. -/

/-- Every register defined by a sequentialized block list is either the image
of an original definition or a fresh name owned by one of the blocks. -/
theorem mem_flatMap_seqBlocks : ∀ (bs : List (Block R)) (l : Nat) (x : R ⊕ Nat),
    x ∈ (seqBlocks l bs).flatMap Block.defs →
      (∃ r, x = .inl r ∧ r ∈ bs.flatMap Block.defs) ∨
        (∃ m, x = .inr m ∧ l ≤ (Nat.unpair m).1)
  | [], _, _, h => by simp [seqBlocks] at h
  | b :: bs, l, x, h => by
    rw [seqBlocks, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · rw [seqBlock_defs, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨j, -, rfl⟩ := mem_freshParams b.params 0 x h
        exact .inr ⟨_, rfl, by simp⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
        exact .inl ⟨r, rfl, by simp [hr]⟩
    · rcases mem_flatMap_seqBlocks bs (l + 1) x h with ⟨r, rfl, hr⟩ | ⟨m, rfl, hm⟩
      · exact .inl ⟨r, rfl, by simp [hr]⟩
      · exact .inr ⟨m, rfl, by omega⟩

theorem nodup_flatMap_seqBlocks : ∀ (bs : List (Block R)) (l : Nat),
    (bs.flatMap Block.defs).Nodup → ((seqBlocks l bs).flatMap Block.defs).Nodup
  | [], _, _ => by simp [seqBlocks]
  | b :: bs, l, h => by
    rw [List.flatMap_cons] at h
    obtain ⟨hb, hbs, hdisj⟩ := List.nodup_append.mp h
    rw [seqBlocks, List.flatMap_cons, seqBlock_defs]
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨freshParams_nodup l b.params 0,
      hb.map Sum.inl_injective, ?_⟩, nodup_flatMap_seqBlocks bs (l + 1) hbs, ?_⟩
    · intro a ha c hc
      obtain ⟨j, -, rfl⟩ := mem_freshParams b.params 0 a ha
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hc
      simp
    · intro a ha c hc
      rcases mem_flatMap_seqBlocks bs (l + 1) c hc with ⟨r, rfl, hr⟩ | ⟨m, rfl, hm⟩
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨j, -, rfl⟩ := mem_freshParams b.params 0 a ha
          simp
        · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp ha
          simpa using hdisj r' hr' r hr
      · rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨j, -, rfl⟩ := mem_freshParams b.params 0 a ha
          simp only [ne_eq, Sum.inr.injEq]
          intro heq
          rw [← heq] at hm
          simp only [Nat.unpair_pair] at hm
          omega
        · obtain ⟨r', -, rfl⟩ := List.mem_map.mp ha
          simp

theorem sequentialize_singleAssignment (fn : Func R) (h : fn.SingleAssignment) :
    (sequentialize fn).SingleAssignment :=
  nodup_flatMap_seqBlocks fn.blocks 0 h

/-! ### Uses stay dominated

`Func.okUse` and `Func.usesDominated` are `Bool`-valued; these read them as
propositions, so that the argument below can be made one case at a time. -/

variable [DecidableEq R]

theorem okUse_iff (fn : Func R) (l : Label) (j : Nat) (r : R) :
    fn.okUse l j r = true ↔
      ((∃ b, fn.block? l = some b ∧ (r ∈ b.params ∨ ∃ o ∈ b.ops.take j, r ∈ o.defs)) ∨
        (∃ a, a < fn.blocks.length ∧ a ≠ l ∧ fn.Dominates a l ∧ r ∈ fn.defsOf a)) := by
  rw [Func.okUse]
  cases hbl : fn.block? l <;>
    simp [List.any_eq_true, List.mem_range, and_assoc]

omit [DecidableEq R] in
/-- A block that exists has a label inside the block list. -/
theorem lt_length_of_block? {fn : Func R} {l : Label} {b : Block R}
    (h : fn.block? l = some b) : l < fn.blocks.length := by
  by_contra hc
  rw [Func.block?, List.getElem?_eq_none (Nat.not_lt.mp hc)] at h
  simp at h

theorem usesDominated_iff (fn : Func R) :
    fn.UsesDominated ↔
      ∀ (l : Label) (b : Block R), fn.block? l = some b →
        ((∀ (j : Nat) (o : Op R), b.ops[j]? = some o → ∀ r ∈ o.uses, fn.okUse l j r = true) ∧
          (∀ r ∈ b.term.uses, fn.okUse l b.ops.length r = true)) := by
  rw [Func.UsesDominated, Func.usesDominated, List.all_eq_true]
  constructor
  · intro h l b hbl
    have hh := h l (List.mem_range.mpr (lt_length_of_block? hbl))
    rw [hbl, Bool.and_eq_true] at hh
    obtain ⟨hops, hterm⟩ := hh
    rw [List.all_eq_true] at hops hterm
    refine ⟨fun j o hj r hr => ?_, fun r hr => hterm r hr⟩
    have hjl : j < b.ops.length := by
      by_contra hc
      rw [List.getElem?_eq_none (Nat.not_lt.mp hc)] at hj
      simp at hj
    have hj' := hops j (List.mem_range.mpr hjl)
    rw [hj, List.all_eq_true] at hj'
    exact hj' r hr
  · intro h l _
    cases hbl : fn.block? l with
    | none => rfl
    | some b =>
      obtain ⟨hops, hterm⟩ := h l b hbl
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
      refine ⟨fun j _ => ?_, fun r hr => hterm r hr⟩
      cases hj : b.ops[j]? with
      | none => rfl
      | some o =>
        rw [List.all_eq_true]
        exact fun r hr => hops j o hj r hr

/-! ### The layout of a sequentialized block

Its ops are the moves followed by the original ops, so an op index below
`b.params.length` is a move and one at or above it is an original op shifted by
that much. -/

omit [DecidableEq R] in
/-- The fresh name of position `j` really is a parameter of the block. -/
theorem mem_freshParams_of_lt (l : Label) : ∀ (ps : List R) (i j : Nat), j < ps.length →
    (Sum.inr (Nat.pair l (i + j)) : R ⊕ Nat) ∈ freshParams l i ps
  | [], _, _, h => absurd h (by simp)
  | _ :: _, _, 0, _ => by simp [freshParams]
  | _ :: ps, i, j + 1, h => by
    rw [freshParams]
    refine List.mem_cons_of_mem _ ?_
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using
      mem_freshParams_of_lt l ps (i + 1) j (by simpa using h)

omit [DecidableEq R] in
/-- A sequentialized block has one op per parameter before the original ops. -/
@[simp] theorem seqBlock_ops_length (l : Label) (b : Block R) :
    (seqBlock l b).ops.length = b.params.length + b.ops.length := by simp [seqBlock]

omit [DecidableEq R] in
/-- The moves all sit in any prefix long enough to contain them. -/
theorem mem_take_of_mem_paramMoves (l : Label) (b : Block R) {j : Nat}
    (hj : b.params.length ≤ j) {o : Op (R ⊕ Nat)} (ho : o ∈ paramMoves l 0 b.params) :
    o ∈ (seqBlock l b).ops.take j := by
  show o ∈ (paramMoves l 0 b.params ++ b.ops.map (Op.mapRegs Sum.inl)).take j
  rw [List.take_append, List.take_of_length_le (by simpa using hj)]
  exact List.mem_append.mpr (.inl ho)

omit [DecidableEq R] in
/-- An original op in a prefix of length `j` is in the prefix of length
`b.params.length + j` of the sequentialized block. -/
theorem mem_take_of_mem_ops (l : Label) (b : Block R) (j : Nat) {o : Op R}
    (ho : o ∈ b.ops.take j) :
    o.mapRegs Sum.inl ∈ (seqBlock l b).ops.take (b.params.length + j) := by
  show _ ∈ (paramMoves l 0 b.params ++ b.ops.map (Op.mapRegs Sum.inl)).take _
  rw [List.take_append, List.take_of_length_le (by simp)]
  refine List.mem_append.mpr (.inr ?_)
  rw [show b.params.length + j - (paramMoves l 0 b.params).length = j by simp, ← List.map_take]
  exact List.mem_map_of_mem ho

/-- **A use that was dominated stays dominated**, shifted past the moves. The
three ways `okUse` can hold all survive: a parameter of the block is now the
destination of one of its moves, an earlier op is still an earlier op, and a
definition of a strictly dominating block is still one because the graph has
not changed. -/
theorem okUse_seq (fn : Func R) {l : Label} {b₀ : Block R} (hbl : fn.block? l = some b₀)
    {i : Nat} {r : R} (h : fn.okUse l i r = true) :
    (sequentialize fn).okUse l (b₀.params.length + i) (Sum.inl r) = true := by
  rw [okUse_iff] at h ⊢
  rcases h with ⟨b, hb, hcase⟩ | ⟨a, ha, hal, hdom, hdef⟩
  · rw [hbl] at hb
    cases hb
    refine .inl ⟨seqBlock l b₀, by simp [hbl], .inr ?_⟩
    rcases hcase with hp | ⟨o, ho, hro⟩
    · have hmem : (Sum.inl r : R ⊕ Nat) ∈ (paramMoves l 0 b₀.params).flatMap Op.defs := by
        rw [paramMoves_flatMap_defs]
        exact List.mem_map_of_mem hp
      obtain ⟨o, ho, hro⟩ := List.mem_flatMap.mp hmem
      exact ⟨o, mem_take_of_mem_paramMoves l b₀ (Nat.le_add_right _ _) ho, hro⟩
    · exact ⟨o.mapRegs Sum.inl, mem_take_of_mem_ops l b₀ i ho,
        by simpa using hro⟩
  · exact .inr ⟨a, by simpa using ha, hal, by simpa using hdom,
      by simp [hdef]⟩

theorem sequentialize_usesDominated (fn : Func R) (h : fn.UsesDominated) :
    (sequentialize fn).UsesDominated := by
  rw [usesDominated_iff] at h ⊢
  intro l b' hb'
  rw [sequentialize_block?] at hb'
  obtain ⟨b₀, hbl, rfl⟩ := Option.map_eq_some_iff.mp hb'
  obtain ⟨hops, hterm⟩ := h l b₀ hbl
  refine ⟨fun j o hj x hx => ?_, fun x hx => ?_⟩
  · by_cases hjk : j < b₀.params.length
    · rw [show (seqBlock l b₀).ops = paramMoves l 0 b₀.params ++ b₀.ops.map (Op.mapRegs Sum.inl)
          from rfl, List.getElem?_append_left (by simpa using hjk), paramMoves_getElem?] at hj
      obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp hj
      simp only [Op.uses, List.mem_singleton] at hx
      subst hx
      rw [okUse_iff]
      exact .inl ⟨seqBlock l b₀, by simp [hbl],
        .inl (by simpa [seqBlock] using mem_freshParams_of_lt l b₀.params 0 j hjk)⟩
    · have hk : b₀.params.length ≤ j := Nat.not_lt.mp hjk
      rw [show (seqBlock l b₀).ops = paramMoves l 0 b₀.params ++ b₀.ops.map (Op.mapRegs Sum.inl)
          from rfl, List.getElem?_append_right (by simpa using hk), paramMoves_length,
        List.getElem?_map] at hj
      obtain ⟨o₀, ho₀, rfl⟩ := Option.map_eq_some_iff.mp hj
      rw [Op.uses_mapRegs] at hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      have := okUse_seq fn hbl (hops (j - b₀.params.length) o₀ ho₀ r hr)
      rwa [Nat.add_sub_cancel' hk] at this
  · rw [show (seqBlock l b₀).term = b₀.term.mapRegs Sum.inl from rfl, Term.uses_mapRegs] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    simpa using okUse_seq fn hbl (hterm r hr)

/-- **Sequentialization preserves well-formedness**, all four clauses. -/
theorem sequentialize_wellFormed {fn : Func R} (h : fn.WellFormed) :
    (sequentialize fn).WellFormed where
  sig := sequentialize_wellFormedSig fn h.sig
  singleAssignment := sequentialize_singleAssignment fn h.singleAssignment
  usesDominated := sequentialize_usesDominated fn h.usesDominated
  argsMatch := sequentialize_argsMatch fn h.argsMatch

/-- Well-formedness of a whole program is preserved. -/
theorem sequentializeProg_wellFormed {p : Prog R} (h : p.WellFormed) :
    (sequentializeProg p).WellFormed := by
  intro fn hfn
  obtain ⟨fn₀, hfn₀, rfl⟩ := List.mem_map.mp hfn
  exact sequentialize_wellFormed (h fn₀ hfn₀)

/-! ## Semantics

The target runs the same code with the registers embedded by `Sum.inl`, except
that arriving at a block costs one extra step per parameter. The correspondence
is therefore: the same block, the index shifted past the moves, frames agreeing
on the original registers, and the stack corresponding activation by
activation. The fresh registers are deliberately *unconstrained* in the
relation — they hold the values in flight across a transfer and nothing reads
them again. -/

/-! ### Frames -/

/-- Two frames agree on the original registers. -/
def FrameRel (fr : Frame R) (gr : Frame (R ⊕ Nat)) : Prop :=
  ∀ r, gr.get (Sum.inl r) = fr.get r

theorem FrameRel.set {fr : Frame R} {gr : Frame (R ⊕ Nat)} (hrel : FrameRel fr gr)
    (d : R) (v : Word) : FrameRel (fr.set d v) (gr.set (Sum.inl d) v) := by
  intro r
  simp only [Frame.get_set, Sum.inl.injEq]
  by_cases h : r = d <;> simp [h, hrel r]

omit [DecidableEq R] in
/-- Reading the `Sum.inl` image of a list reads the same words. -/
theorem readAll_map_inl {fr : Frame R} {gr : Frame (R ⊕ Nat)} (hrel : FrameRel fr gr) :
    ∀ rs : List R, gr.readAll (rs.map Sum.inl) = fr.readAll rs
  | [] => rfl
  | r :: rs => by
    have ih : (rs.map Sum.inl).mapM gr.get = rs.mapM fr.get := readAll_map_inl hrel rs
    show ((r :: rs).map Sum.inl).mapM gr.get = (r :: rs).mapM fr.get
    simp only [List.map_cons, List.mapM_cons, hrel r, ih]

/-- Writing succeeds exactly when there are as many values as registers. -/
theorem writeAll_isSome_iff {T : Type} [DecidableEq T] : ∀ (fr : Frame T) (rs : List T)
    (vs : List Word), (fr.writeAll rs vs).isSome = true ↔ rs.length = vs.length
  | _, [], [] => by simp [Frame.writeAll]
  | _, [], _ :: _ => by simp [Frame.writeAll]
  | _, _ :: _, [] => by simp [Frame.writeAll]
  | fr, r :: rs, v :: vs => by
    rw [Frame.writeAll]
    simpa using writeAll_isSome_iff (fr.set r v) rs vs

/-- Writing the `Sum.inl` image of a list preserves the correspondence. -/
theorem writeAll_map_inl {fr : Frame R} {gr : Frame (R ⊕ Nat)} (hrel : FrameRel fr gr) :
    ∀ (rs : List R) (vs : List Word) (fr' : Frame R), fr.writeAll rs vs = some fr' →
      ∃ gr', gr.writeAll (rs.map Sum.inl) vs = some gr' ∧ FrameRel fr' gr'
  | [], [], fr', h => by
    rw [Frame.writeAll, Option.some.injEq] at h
    exact ⟨gr, rfl, h ▸ hrel⟩
  | [], _ :: _, _, h => by simp [Frame.writeAll] at h
  | _ :: _, [], _, h => by simp [Frame.writeAll] at h
  | r :: rs, v :: vs, fr', h => by
    rw [Frame.writeAll] at h
    obtain ⟨gr', hg, hrel'⟩ := writeAll_map_inl (hrel.set r v) rs vs fr' h
    exact ⟨gr', by rw [List.map_cons, Frame.writeAll]; exact hg, hrel'⟩

/-- **Writing the fresh parameters touches nothing else.** The original
registers keep their values, and each fresh parameter holds the argument that
was written to it, because the fresh names are pairwise distinct. -/
theorem writeAll_freshParams (l : Label) : ∀ (ps : List R) (i : Nat) (vals : List Word),
    ps.length = vals.length → ∀ gr : Frame (R ⊕ Nat),
    ∃ g, gr.writeAll (freshParams l i ps) vals = some g ∧
      (∀ y : R ⊕ Nat, (∀ j, j < ps.length → y ≠ Sum.inr (Nat.pair l (i + j))) →
        g.get y = gr.get y) ∧
      (∀ j, j < ps.length → g.get (Sum.inr (Nat.pair l (i + j))) = vals[j]?)
  | [], _, [], _, gr => ⟨gr, rfl, fun _ _ => rfl, fun _ h => absurd h (by simp)⟩
  | [], _, _ :: _, hlen, _ => by simp at hlen
  | _ :: _, _, [], hlen, _ => by simp at hlen
  | p :: ps, i, v :: vals, hlen, gr => by
    obtain ⟨g, hg, hframe, hval⟩ :=
      writeAll_freshParams l ps (i + 1) vals (by simpa using hlen) (gr.set (.inr (Nat.pair l i)) v)
    refine ⟨g, by rw [freshParams, Frame.writeAll]; exact hg, fun y hy => ?_, fun j hj => ?_⟩
    · have hy' : ∀ j, j < ps.length → y ≠ Sum.inr (Nat.pair l (i + 1 + j)) := by
        intro j hj
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hy (j + 1) (by simpa using hj)
      have h0 : y ≠ Sum.inr (Nat.pair l i) := by simpa using hy 0 (by simp)
      rw [hframe y hy', Frame.get_set]
      simp [h0]
    · cases j with
      | zero =>
        have hne : ∀ j', j' < ps.length →
            (Sum.inr (Nat.pair l (i + 0)) : R ⊕ Nat) ≠ Sum.inr (Nat.pair l (i + 1 + j')) := by
          intro j' _ heq
          have h2 : Nat.pair l (i + 0) = Nat.pair l (i + 1 + j') := by simpa using heq
          have := pair_inj_right h2
          omega
        rw [hframe _ hne, Frame.get_set]
        simp
      | succ j' =>
        simpa [Nat.add_assoc, Nat.add_comm 1 j'] using hval j' (by simpa using hj)

/-! ### Points, states and code -/

/-- The number of moves at the head of the block a point names. -/
def shift (p : Prog R) (pt : Point) : Nat :=
  match p.block? pt.func pt.label with
  | some b => b.params.length
  | none => 0

/-- The point of the sequentialized program a source point corresponds to: the
same block, with the index shifted past that block's moves. -/
def seqPoint (p : Prog R) (pt : Point) : Point :=
  ⟨pt.func, pt.label, shift p pt + pt.index⟩

omit [DecidableEq R] in
@[simp] theorem seqPoint_func (p : Prog R) (pt : Point) : (seqPoint p pt).func = pt.func := rfl

omit [DecidableEq R] in
@[simp] theorem seqPoint_label (p : Prog R) (pt : Point) : (seqPoint p pt).label = pt.label := rfl

omit [DecidableEq R] in
@[simp] theorem seqPoint_next (p : Prog R) (pt : Point) :
    seqPoint p pt.next = (seqPoint p pt).next := rfl

/-- Two suspended callers correspond. -/
def ActRel (p : Prog R) (a : Activation R) (a' : Activation (R ⊕ Nat)) : Prop :=
  a'.point = seqPoint p a.point ∧ FrameRel a.frame a'.frame

/-- **Two machine states correspond**: the same point past the moves, frames
agreeing on the original registers, corresponding stacks and the same memory. -/
structure StateRel (p : Prog R) (s : State R) (t : State (R ⊕ Nat)) : Prop where
  /-- The point is the source's, shifted past the block's moves. -/
  point : t.point = seqPoint p s.point
  /-- The frames agree on the original registers. -/
  frame : FrameRel s.frame t.frame
  /-- The stacks correspond activation by activation. -/
  stack : List.Forall₂ (ActRel p) s.stack t.stack
  /-- The memories are equal. -/
  mem : t.mem = s.mem

/-- Fetched code with its registers renamed. -/
def Code.mapRegs (g : R → S) : Code R → Code S
  | .op o => .op (o.mapRegs g)
  | .term t => .term (t.mapRegs g)

omit [DecidableEq R] in
@[simp] theorem sequentializeProg_func? (p : Prog R) (f : FuncId) :
    (sequentializeProg p).func? f = (p.func? f).map sequentialize := by
  simp [sequentializeProg, Prog.func?, List.getElem?_map]

omit [DecidableEq R] in
@[simp] theorem sequentializeProg_block? (p : Prog R) (f : FuncId) (l : Label) :
    (sequentializeProg p).block? f l = (p.block? f l).map (seqBlock l) := by
  simp only [Prog.block?, sequentializeProg_func?]
  cases p.func? f <;> simp

omit [DecidableEq R] in
/-- **The sequentialized program fetches the same code at the corresponding
point**, with its registers renamed. An index at or past the moves lands on an
original op, and the terminator stays the terminator because the block grew by
exactly the number of moves. -/
theorem sequentializeProg_fetch (p : Prog R) (pt : Point) :
    (sequentializeProg p).fetch (seqPoint p pt) = (p.fetch pt).map (Code.mapRegs Sum.inl) := by
  rw [Prog.fetch, Prog.fetch]
  simp only [seqPoint_func, seqPoint_label, sequentializeProg_block?]
  cases hb : p.block? pt.func pt.label with
  | none => simp
  | some b =>
    simp only [Option.map_some, Option.bind_some]
    have hops : (seqBlock pt.label b).ops[(seqPoint p pt).index]? =
        (b.ops[pt.index]?).map (Op.mapRegs Sum.inl) := by
      show (paramMoves pt.label 0 b.params ++ b.ops.map (Op.mapRegs Sum.inl))[_]? = _
      rw [show (seqPoint p pt).index = b.params.length + pt.index by
            simp [seqPoint, shift, hb],
        List.getElem?_append_right (by simp), paramMoves_length, Nat.add_sub_cancel_left,
        List.getElem?_map]
    rw [hops]
    cases b.ops[pt.index]? with
    | some o => simp [Code.mapRegs]
    | none =>
      simp only [Option.map_none]
      have hlen : (seqPoint p pt).index = b.params.length + pt.index := by
        simp [seqPoint, shift, hb]
      by_cases hi : pt.index = b.ops.length
      · simp [hi, hlen, seqBlock, Code.mapRegs]
      · have hne : (seqPoint p pt).index ≠ b.params.length + b.ops.length := by
          rw [hlen]; omega
        simp [hne, hi]

/-! ### Operations -/

omit [DecidableEq R] in
/-- A renamed operation is a call exactly when the original is. -/
theorem mapRegs_eq_call_iff {o : Op R} {f : FuncId} {args results : List (R ⊕ Nat)} :
    o.mapRegs Sum.inl = .call f args results ↔
      ∃ args₀ results₀, o = .call f args₀ results₀ ∧
        args = args₀.map Sum.inl ∧ results = results₀.map Sum.inl := by
  cases o <;> simp [Op.mapRegs, eq_comm, and_assoc]

/-- A renamed operation that succeeds succeeds the same way. -/
theorem exec_mapRegs_some {fr : Frame R} {gr : Frame (R ⊕ Nat)} (hrel : FrameRel fr gr)
    {o : Op R} {fr' : Frame R} {m m' : Memory} (h : o.exec fr m = some (fr', m')) :
    ∃ gr', (o.mapRegs Sum.inl).exec gr m = some (gr', m') ∧ FrameRel fr' gr' := by
  cases o with
  | const d v =>
    rw [Op.exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨gr.set (.inl d) v, rfl, hrel.set d v⟩
  | move d a =>
    rw [Op.exec] at h
    cases hg : fr.get a with
    | none => rw [hg] at h; simp at h
    | some x =>
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨gr.set (.inl d) x, by rw [Op.mapRegs, Op.exec, hrel a, hg]; rfl, hrel.set d x⟩
  | unary op d a =>
    rw [Op.exec] at h
    cases hg : fr.get a with
    | none => rw [hg] at h; simp at h
    | some x =>
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨gr.set (.inl d) (op.eval x), by rw [Op.mapRegs, Op.exec, hrel a, hg]; rfl,
        hrel.set d _⟩
  | binary op d a b =>
    rw [Op.exec] at h
    cases hga : fr.get a with
    | none => rw [hga] at h; simp at h
    | some x =>
      rw [hga] at h
      simp only [Option.bind_some] at h
      cases hgb : fr.get b with
      | none => rw [hgb] at h; simp at h
      | some y =>
        rw [hgb] at h
        simp only [Option.bind_some] at h
        cases hev : op.eval x y with
        | none => rw [hev] at h; simp at h
        | some z =>
          rw [hev] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨gr.set (.inl d) z, ?_, hrel.set d z⟩
          rw [Op.mapRegs, Op.exec, hrel a, hrel b, hga, hgb]
          simp only [Option.bind_some, hev, Option.map_some]
  | load w e d base off =>
    rw [Op.exec] at h
    cases hg : fr.get base with
    | none => rw [hg] at h; simp at h
    | some a =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      cases hl : m.load w e (a.toNat + off) with
      | none => rw [hl] at h; simp at h
      | some z =>
        rw [hl] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨gr.set (.inl d) z, ?_, hrel.set d z⟩
        rw [Op.mapRegs, Op.exec, hrel base, hg]
        simp only [Option.bind_some, hl, Option.map_some]
  | store w base off src =>
    rw [Op.exec] at h
    cases hg : fr.get base with
    | none => rw [hg] at h; simp at h
    | some a =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      cases hs : fr.get src with
      | none => rw [hs] at h; simp at h
      | some x =>
        rw [hs] at h
        simp only [Option.bind_some] at h
        cases hm : m.store w (a.toNat + off) x with
        | none => rw [hm] at h; simp at h
        | some m₂ =>
          rw [hm] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨gr, ?_, hrel⟩
          rw [Op.mapRegs, Op.exec, hrel base, hrel src, hg, hs]
          simp only [Option.bind_some, hm, Option.map_some]
  | call f args results => rw [Op.exec] at h; simp at h

/-- A renamed operation that goes wrong goes wrong the same way. -/
theorem exec_mapRegs_none {fr : Frame R} {gr : Frame (R ⊕ Nat)} (hrel : FrameRel fr gr)
    {o : Op R} {m : Memory} (h : o.exec fr m = none) :
    (o.mapRegs Sum.inl).exec gr m = none := by
  have hg : ∀ x : R, gr.get (Sum.inl x) = fr.get x := hrel
  cases o with
  | const d v => rw [Op.exec] at h; simp at h
  | call f args results => rfl
  | _ =>
    rw [Op.mapRegs, Op.exec]
    rw [Op.exec] at h
    simp only [hg, Option.bind_eq_none_iff, Option.map_eq_none_iff] at h ⊢
    exact h

/-! ### Running the moves -/

omit [DecidableEq R] in
/-- The sequentialized program fetches the move at position `i` of block `l`. -/
theorem fetch_paramMove (p : Prog R) {f : FuncId} {l : Label} {b₀ : Block R}
    (hb : p.block? f l = some b₀) {i : Nat} (hi : i < b₀.params.length) {pp : R}
    (hp : b₀.params[i]? = some pp) :
    (sequentializeProg p).fetch ⟨f, l, i⟩ =
      some (.op (.move (Sum.inl pp) (Sum.inr (Nat.pair l i)))) := by
  rw [Prog.fetch]
  simp only [sequentializeProg_block?, hb, Option.map_some, Option.bind_some, seqBlock]
  rw [List.getElem?_append_left (by simpa using hi), paramMoves_getElem?, hp]
  simp

/-- **Running a block's entry moves.** From the head of a block whose fresh
parameters hold the transferred values, one step per parameter copies them into
the original parameters. The frame that results is the one the `Sum.inl` image
of the simultaneous write would produce. -/
theorem moves_run (p : Prog R) {f : FuncId} {l : Label} {b₀ : Block R}
    (hb : p.block? f l = some b₀) (stk : List (Activation (R ⊕ Nat))) (mem : Memory) :
    ∀ (ps : List R) (i : Nat) (vals : List Word) (g : Frame (R ⊕ Nat)),
      b₀.params.drop i = ps → ps.length = vals.length →
      (∀ j, j < ps.length → g.get (Sum.inr (Nat.pair l (i + j))) = vals[j]?) →
      ∃ g', g.writeAll (ps.map Sum.inl) vals = some g' ∧
        Relation.ReflTransGen (Step (sequentializeProg p))
          ⟨⟨f, l, i⟩, g, stk, mem⟩ ⟨⟨f, l, i + ps.length⟩, g', stk, mem⟩
  | [], i, vals, g, _, hlen, _ => by
    cases vals with
    | nil => exact ⟨g, rfl, by simpa using Relation.ReflTransGen.refl⟩
    | cons _ _ => simp at hlen
  | pp :: ps, i, vals, g, hdrop, hlen, hval => by
    cases vals with
    | nil => simp at hlen
    | cons v vals =>
      have hi : i < b₀.params.length := by
        by_contra hc
        rw [List.drop_eq_nil_of_le (Nat.not_lt.mp hc)] at hdrop
        simp at hdrop
      have hp : b₀.params[i]? = some pp := by
        have : (b₀.params.drop i)[0]? = some pp := by rw [hdrop]; rfl
        simpa using this
      have hgv : g.get (Sum.inr (Nat.pair l i)) = some v := by
        simpa using hval 0 (by simp)
      have hstep : Step (sequentializeProg p) ⟨⟨f, l, i⟩, g, stk, mem⟩
          ⟨⟨f, l, i + 1⟩, g.set (Sum.inl pp) v, stk, mem⟩ := by
        show step _ _ = _
        rw [step, fetch_paramMove p hb hi hp]
        simp [Op.exec, hgv, Point.next]
      have hdrop' : b₀.params.drop (i + 1) = ps := by
        rw [← List.tail_drop, hdrop]; rfl
      obtain ⟨g', hw, hsteps⟩ := moves_run p hb stk mem ps (i + 1) vals (g.set (Sum.inl pp) v)
        hdrop' (by simpa using hlen) (fun j hj => by
          have h1 := hval (j + 1) (by simpa using hj)
          have h2 : (g.set (Sum.inl pp) v).get (Sum.inr (Nat.pair l (i + 1 + j)))
              = g.get (Sum.inr (Nat.pair l (i + 1 + j))) := by rw [Frame.get_set]; simp
          rw [h2]
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using h1)
      refine ⟨g', by rw [List.map_cons, Frame.writeAll]; exact hw, ?_⟩
      have := Relation.ReflTransGen.head hstep hsteps
      simpa [Nat.add_assoc, Nat.add_comm 1 ps.length] using this

/-! ### Arriving at a block -/

omit [DecidableEq R] in
/-- The empty frames correspond. -/
theorem frameRel_empty : FrameRel (Frame.empty : Frame R) (Frame.empty : Frame (R ⊕ Nat)) :=
  fun _ => rfl

/-- **Arriving at a block.** The transfer writes the fresh parameters, which
touches no original register, and the moves then copy them into the original
parameters. The two together have exactly the effect of the source's
simultaneous write, and land on the point the source's state corresponds to. -/
theorem seq_arrive (p : Prog R) {f : FuncId} {l : Label} {b₀ : Block R}
    (hb : p.block? f l = some b₀) {fr fr' : Frame R} {gr : Frame (R ⊕ Nat)}
    (hrel : FrameRel fr gr) {vals : List Word} (hw : fr.writeAll b₀.params vals = some fr')
    (stk : List (Activation (R ⊕ Nat))) (mem : Memory) :
    ∃ g g', gr.writeAll (freshParams l 0 b₀.params) vals = some g ∧
      Relation.ReflTransGen (Step (sequentializeProg p))
        ⟨⟨f, l, 0⟩, g, stk, mem⟩ ⟨seqPoint p ⟨f, l, 0⟩, g', stk, mem⟩ ∧
      FrameRel fr' g' := by
  have hlen : b₀.params.length = vals.length :=
    (writeAll_isSome_iff fr b₀.params vals).mp (by rw [hw]; rfl)
  obtain ⟨g, hg, hframe, hvals⟩ := writeAll_freshParams l b₀.params 0 vals hlen gr
  have hrel' : FrameRel fr g := fun r => by
    rw [hframe (Sum.inl r) (by intro j _; simp)]; exact hrel r
  obtain ⟨g', hwm, hsteps⟩ := moves_run p hb stk mem b₀.params 0 vals g rfl hlen hvals
  obtain ⟨g'', hwm', hrel''⟩ := writeAll_map_inl hrel' b₀.params vals fr' hw
  refine ⟨g, g', hg, ?_, Option.some.inj (hwm.symm.trans hwm') ▸ hrel''⟩
  rw [show seqPoint p ⟨f, l, 0⟩ = ⟨f, l, 0 + b₀.params.length⟩ by simp [seqPoint, shift, hb]]
  exact hsteps

/-- **Entering a function.** The callee's entry block receives the arguments in
its fresh parameters and copies them into the originals, so the call lands on
the point the source's entry state corresponds to. -/
theorem seq_enter (p : Prog R) {f : FuncId} {vals : List Word} {pt : Point} {fr : Frame R}
    (h : p.enter f vals = some (pt, fr)) (stk : List (Activation (R ⊕ Nat))) (mem : Memory) :
    ∃ g g', (sequentializeProg p).enter f vals = some (pt, g) ∧
      Relation.ReflTransGen (Step (sequentializeProg p))
        ⟨pt, g, stk, mem⟩ ⟨seqPoint p pt, g', stk, mem⟩ ∧ FrameRel fr g' := by
  rw [Prog.enter] at h
  cases hfn : p.func? f with
  | none => rw [hfn] at h; simp at h
  | some fn =>
    rw [hfn] at h
    simp only [Option.bind_some] at h
    cases hbe : fn.block? fn.entry with
    | none => rw [hbe] at h; simp at h
    | some b₀ =>
      rw [hbe] at h
      simp only [Option.bind_some] at h
      cases hwe : (Frame.empty : Frame R).writeAll b₀.params vals with
      | none => rw [hwe] at h; simp at h
      | some fr₀ =>
        rw [hwe] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb : p.block? f fn.entry = some b₀ := by rw [Prog.block?, hfn]; exact hbe
        obtain ⟨g, g', hg, hsteps, hrel⟩ := seq_arrive p hb frameRel_empty hwe stk mem
        refine ⟨g, g', ?_, hsteps, hrel⟩
        rw [Prog.enter]
        simp only [sequentializeProg_func?, hfn, Option.map_some, Option.bind_some,
          sequentialize_entry, sequentialize_block?, hbe, seqBlock]
        rw [hg]
        rfl

/-! ### The forward simulation -/

omit [DecidableEq R] in
/-- A fetched instruction of the sequentialized program, at a corresponding
point. -/
theorem fetch_seq {p : Prog R} {pt : Point} {c : Code R} (hc : p.fetch pt = some c) :
    (sequentializeProg p).fetch (seqPoint p pt) = some (Code.mapRegs Sum.inl c) := by
  rw [sequentializeProg_fetch, hc]; rfl

/-- **One source step is matched by at least one target step.** An operation is
matched one for one; a transfer or a call is matched by the transfer itself and
then one move per parameter of the block it lands on. -/
theorem seq_step (p : Prog R) {s s' : State R} {t : State (R ⊕ Nat)}
    (hst : StateRel p s t) (hstep : Step p s s') :
    ∃ t', Relation.TransGen (Step (sequentializeProg p)) t t' ∧ StateRel p s' t' := by
  have htr : Transition p s (.running s') := Transition.of_step hstep (by simp)
  obtain ⟨hpt, hfr, hstk, hmm⟩ := hst
  obtain ⟨tp, tf, ts, tm⟩ := t
  simp only at hpt hfr hstk hmm
  subst hpt
  subst hmm
  cases htr with
  | op hf he =>
    rename_i o fr m
    obtain ⟨gr', hex, hrel'⟩ := exec_mapRegs_some hfr he
    exact ⟨⟨(seqPoint p s.point).next, gr', ts, m⟩,
      Relation.TransGen.single
        (Transition.op (p := sequentializeProg p) (fetch_seq hf) hex).step_eq,
      ⟨rfl, hrel', hstk, rfl⟩⟩
  | call hf ha he =>
    rename_i f args results vals pt fr
    obtain ⟨g, g', henter, hsteps, hrel'⟩ :=
      seq_enter p he (⟨seqPoint p s.point, tf⟩ :: ts) s.mem
    refine ⟨⟨seqPoint p pt, g', ⟨seqPoint p s.point, tf⟩ :: ts, s.mem⟩,
      Relation.TransGen.head' ?_ hsteps, ⟨rfl, hrel', List.Forall₂.cons ⟨rfl, hfr⟩ hstk, rfl⟩⟩
    exact (Transition.call (p := sequentializeProg p) (fetch_seq hf)
      (by rw [readAll_map_inl hfr]; exact ha) henter).step_eq
  | jump hf hv hb hw =>
    rename_i tgt as vals b fr
    obtain ⟨g, g', hg, hsteps, hrel'⟩ := seq_arrive p hb hfr hw ts s.mem
    refine ⟨⟨seqPoint p ⟨s.point.func, tgt, 0⟩, g', ts, s.mem⟩,
      Relation.TransGen.head' ?_ hsteps, ⟨rfl, hrel', hstk, rfl⟩⟩
    exact (Transition.jump (p := sequentializeProg p) (b := seqBlock tgt b) (fetch_seq hf)
      (by rw [readAll_map_inl hfr]; exact hv)
      (by rw [sequentializeProg_block?]; exact congrArg _ hb) (by simpa [seqBlock] using hg)).step_eq
  | cond hf hc hv hb hw =>
    rename_i c t₁ t₂ a₁ a₂ x vals b fr
    obtain ⟨g, g', hg, hsteps, hrel'⟩ := seq_arrive p hb hfr hw ts s.mem
    refine ⟨⟨seqPoint p ⟨s.point.func, if x = 0 then t₂ else t₁, 0⟩, g', ts, s.mem⟩,
      Relation.TransGen.head' ?_ hsteps, ⟨rfl, hrel', hstk, rfl⟩⟩
    refine (Transition.cond (p := sequentializeProg p)
      (b := seqBlock (if x = 0 then t₂ else t₁) b) (fetch_seq hf)
      (by rw [hfr]; exact hc) ?_ (by rw [sequentializeProg_block?]; exact congrArg _ hb)
      (by simpa [seqBlock] using hg)).step_eq
    rw [show (if x = 0 then a₂.map Sum.inl else a₁.map Sum.inl)
        = (if x = 0 then a₂ else a₁).map Sum.inl by split <;> rfl, readAll_map_inl hfr]
    exact hv
  | ret hf hv hs ha hw =>
    rename_i regs vals a rest f args results fr
    rw [hs] at hstk
    cases hstk with
    | @cons _ a' _ rest' hact hrest =>
      obtain ⟨hapt, hafr⟩ := hact
      obtain ⟨gr, hgw, hrel'⟩ := writeAll_map_inl hafr results vals fr hw
      refine ⟨⟨a'.point.next, gr, rest', s.mem⟩, Relation.TransGen.single ?_,
        ⟨by rw [hapt]; rfl, hrel', hrest, rfl⟩⟩
      exact (Transition.ret (p := sequentializeProg p) (fetch_seq hf)
        (by rw [readAll_map_inl hfr]; exact hv) rfl
        (by rw [hapt]; exact fetch_seq ha) hgw).step_eq

/-! ### Going wrong, returning and trapping

The target never goes wrong where the source does not, and never returns or
traps differently. For `stuck` the argument runs the other way round: a target
transition is inverted into a source transition, which contradicts the source
being stuck. -/

omit [DecidableEq R] in
/-- A fetch of the sequentialized program comes from a fetch of the source. -/
theorem fetch_seq_inv {p : Prog R} {pt : Point} {c' : Code (R ⊕ Nat)}
    (h : (sequentializeProg p).fetch (seqPoint p pt) = some c') :
    ∃ c, p.fetch pt = some c ∧ c' = Code.mapRegs Sum.inl c := by
  rw [sequentializeProg_fetch] at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c, hc, rfl⟩

/-- Writing succeeds on exactly the same lengths, so one write succeeds when
the other does. -/
theorem writeAll_eq_none_iff {T : Type} [DecidableEq T] {fr : Frame T} {rs : List T}
    {vs : List Word} : fr.writeAll rs vs = none ↔ rs.length ≠ vs.length := by
  constructor
  · intro h he
    have := (writeAll_isSome_iff fr rs vs).mpr he
    rw [h] at this
    simp at this
  · intro h
    cases hw : fr.writeAll rs vs with
    | none => rfl
    | some fr' => exact absurd ((writeAll_isSome_iff fr rs vs).mp (by rw [hw]; rfl)) h

/-- A successful write of the fresh parameters means the source's simultaneous
write succeeds too: the two lists have the same length. -/
theorem writeAll_some_of_fresh {l : Label} {b : Block R} {vals : List Word}
    {gr g : Frame (R ⊕ Nat)} (h : gr.writeAll (freshParams l 0 b.params) vals = some g)
    (fr : Frame R) : ∃ fr', fr.writeAll b.params vals = some fr' := by
  have hlen : b.params.length = vals.length := by
    simpa using (writeAll_isSome_iff gr (freshParams l 0 b.params) vals).mp (by rw [h]; rfl)
  exact Option.isSome_iff_exists.mp ((writeAll_isSome_iff fr b.params vals).mpr hlen)

/-- A successful write of a `Sum.inl` image means the source's write succeeds
too. -/
theorem writeAll_some_of_map {rs : List R} {vals : List Word} {gr g : Frame (R ⊕ Nat)}
    (h : gr.writeAll (rs.map Sum.inl) vals = some g) (fr : Frame R) :
    ∃ fr', fr.writeAll rs vals = some fr' := by
  have hlen : rs.length = vals.length := by
    simpa using (writeAll_isSome_iff gr (rs.map Sum.inl) vals).mp (by rw [h]; rfl)
  exact Option.isSome_iff_exists.mp ((writeAll_isSome_iff fr rs vals).mpr hlen)

/-- Entering a function that does not exist, or with the wrong number of
arguments, fails in the sequentialized program too. -/
theorem seq_enter_none (p : Prog R) (f : FuncId) (vals : List Word)
    (h : p.enter f vals = none) : (sequentializeProg p).enter f vals = none := by
  rw [Prog.enter] at h ⊢
  simp only [sequentializeProg_func?]
  cases hfn : p.func? f with
  | none => rfl
  | some fn =>
    rw [hfn] at h
    simp only [Option.bind_some] at h
    simp only [Option.map_some, Option.bind_some, sequentialize_entry, sequentialize_block?]
    cases hbe : fn.block? fn.entry with
    | none => rfl
    | some b =>
      rw [hbe] at h
      simp only [Option.bind_some, Option.map_eq_none_iff] at h
      simp only [Option.map_some, Option.bind_some, seqBlock]
      rw [writeAll_eq_none_iff.mpr (by simpa using writeAll_eq_none_iff.mp h)]
      rfl

/-- **A source run that goes wrong makes the target go wrong at the same
point.** The argument runs backwards: were the target to make a transition,
inverting it would give a source transition, and the source is stuck. -/
theorem seq_stuck (p : Prog R) {s : State R} {t : State (R ⊕ Nat)} (hst : StateRel p s t)
    (h : step p s = .stuck) : step (sequentializeProg p) t = .stuck := by
  obtain ⟨hpt, hfr, hstk, hmm⟩ := hst
  obtain ⟨tp, tf, ts, tm⟩ := t
  simp only at hpt hfr hstk hmm
  subst hpt
  subst hmm
  by_contra hc
  obtain ⟨r, hr⟩ :
      ∃ r, step (sequentializeProg p) ⟨seqPoint p s.point, tf, ts, s.mem⟩ = r := ⟨_, rfl⟩
  have htr : Transition (sequentializeProg p) ⟨seqPoint p s.point, tf, ts, s.mem⟩ r :=
    Transition.of_step hr (fun he => hc (hr.trans he))
  have hswap : ∀ {q : Result R}, step p s = q → q = .stuck := fun hq => hq.symm.trans h
  cases htr with
  | op hf he =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | term _ => simp [Code.mapRegs] at hceq
    | op o =>
      simp only [Code.mapRegs, Code.op.injEq] at hceq
      subst hceq
      cases hex : o.exec s.frame s.mem with
      | none => rw [exec_mapRegs_none hfr hex] at he; simp at he
      | some w =>
        obtain ⟨fr₁, m₁⟩ := w
        exact absurd (hswap (Transition.op hcc hex).step_eq) (by simp)
  | call hf ha he =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | term _ => simp [Code.mapRegs] at hceq
    | op o =>
      simp only [Code.mapRegs, Code.op.injEq] at hceq
      obtain ⟨args₀, results₀, rfl, rfl, -⟩ := mapRegs_eq_call_iff.mp hceq.symm
      rw [readAll_map_inl hfr] at ha
      cases hen : p.enter _ _ with
      | none => rw [seq_enter_none p _ _ hen] at he; simp at he
      | some w => exact absurd (hswap (Transition.call hcc ha hen).step_eq) (by simp)
  | jump hf hv hb hw =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | op _ => simp [Code.mapRegs] at hceq
    | term tm =>
      cases tm with
      | jump tgt₀ as₀ =>
        simp only [Code.mapRegs, Term.mapRegs, Code.term.injEq, Term.jump.injEq] at hceq
        obtain ⟨rfl, rfl⟩ := hceq
        rw [readAll_map_inl hfr] at hv
        rw [seqPoint_func, sequentializeProg_block?] at hb
        obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.mp hb
        obtain ⟨fr₀, hfr₀⟩ := writeAll_some_of_fresh (by simpa [seqBlock] using hw) s.frame
        exact absurd (hswap (Transition.jump hcc hv hb₀ hfr₀).step_eq) (by simp)
      | _ => simp [Code.mapRegs, Term.mapRegs] at hceq
  | cond hf hcnd hv hb hw =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | op _ => simp [Code.mapRegs] at hceq
    | term tm =>
      cases tm with
      | cond c₀ u₁ b₁ u₂ b₂ =>
        simp only [Code.mapRegs, Term.mapRegs, Code.term.injEq, Term.cond.injEq] at hceq
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hceq
        rw [hfr] at hcnd
        rw [show ∀ y : Word, (if y = 0 then b₂.map Sum.inl else b₁.map Sum.inl)
            = (if y = 0 then b₂ else b₁).map Sum.inl from fun y => by split <;> rfl,
          readAll_map_inl hfr] at hv
        rw [seqPoint_func, sequentializeProg_block?] at hb
        obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.mp hb
        obtain ⟨fr₀, hfr₀⟩ := writeAll_some_of_fresh (by simpa [seqBlock] using hw) s.frame
        exact absurd (hswap (Transition.cond hcc hcnd hv hb₀ hfr₀).step_eq) (by simp)
      | _ => simp [Code.mapRegs, Term.mapRegs] at hceq
  | ret hf hv hs ha hw =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | op _ => simp [Code.mapRegs] at hceq
    | term tm =>
      cases tm with
      | ret regs₀ =>
        simp only [Code.mapRegs, Term.mapRegs, Code.term.injEq, Term.ret.injEq] at hceq
        rw [hceq, readAll_map_inl hfr] at hv
        subst hs
        rw [List.forall₂_cons_right_iff] at hstk
        obtain ⟨a₀, rest₀, hact, hrest, hsk⟩ := hstk
        obtain ⟨hapt, hafr⟩ := hact
        rw [hapt] at ha
        obtain ⟨c₂, hcc₂, hceq₂⟩ := fetch_seq_inv ha
        cases c₂ with
        | term _ => simp [Code.mapRegs] at hceq₂
        | op o₂ =>
          simp only [Code.mapRegs, Code.op.injEq] at hceq₂
          obtain ⟨args₀, results₀, rfl, -, rfl⟩ := mapRegs_eq_call_iff.mp hceq₂.symm
          obtain ⟨fr₀, hfr₀⟩ := writeAll_some_of_map hw a₀.frame
          exact absurd (hswap (Transition.ret hcc hv hsk hcc₂ hfr₀).step_eq) (by simp)
      | _ => simp [Code.mapRegs, Term.mapRegs] at hceq
  | halt hf hv hs =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | op _ => simp [Code.mapRegs] at hceq
    | term tm =>
      cases tm with
      | ret regs₀ =>
        simp only [Code.mapRegs, Term.mapRegs, Code.term.injEq, Term.ret.injEq] at hceq
        rw [hceq, readAll_map_inl hfr] at hv
        subst hs
        rw [List.forall₂_nil_right_iff] at hstk
        exact absurd (hswap (Transition.halt hcc hv hstk).step_eq) (by simp)
      | _ => simp [Code.mapRegs, Term.mapRegs] at hceq
  | trap hf =>
    obtain ⟨c, hcc, hceq⟩ := fetch_seq_inv hf
    cases c with
    | op _ => simp [Code.mapRegs] at hceq
    | term tm =>
      cases tm with
      | trap => exact absurd (hswap (Transition.trap hcc).step_eq) (by simp)
      | _ => simp [Code.mapRegs, Term.mapRegs] at hceq

/-- A source run that returns makes the target return the same words and
memory. -/
theorem seq_returned (p : Prog R) {s : State R} {t : State (R ⊕ Nat)} (hst : StateRel p s t)
    {vs : List Word} {m : Memory} (h : step p s = .returned vs m) :
    step (sequentializeProg p) t = .returned vs m := by
  have htr := Transition.of_step h (by simp)
  obtain ⟨hpt, hfr, hstk, hmm⟩ := hst
  obtain ⟨tp, tf, ts, tm⟩ := t
  simp only at hpt hfr hstk hmm
  subst hpt
  subst hmm
  cases htr with
  | halt hf hv hs =>
    rw [hs] at hstk
    cases hstk
    exact (Transition.halt (p := sequentializeProg p) (fetch_seq hf)
      (by rw [readAll_map_inl hfr]; exact hv) rfl).step_eq

/-- A source run that traps makes the target trap with the same memory. -/
theorem seq_trapped (p : Prog R) {s : State R} {t : State (R ⊕ Nat)} (hst : StateRel p s t)
    {m : Memory} (h : step p s = .trapped m) :
    step (sequentializeProg p) t = .trapped m := by
  have htr := Transition.of_step h (by simp)
  obtain ⟨hpt, hfr, hstk, hmm⟩ := hst
  obtain ⟨tp, tf, ts, tm⟩ := t
  simp only at hpt hfr hstk hmm
  subst hpt
  subst hmm
  cases htr with
  | trap hf => exact (Transition.trap (p := sequentializeProg p) (fetch_seq hf)).step_eq

/-! ### The behavioural `iff` -/

/-- A behaviour of a state is a behaviour of anything that reaches it. -/
theorem behaves_of_steps {p : Prog R} {s s' : State R} {b : Behavior}
    (hr : Steps p s s') (hb : Behaves p s' b) : Behaves p s b := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head hstep _ ih => exact Behaves.head hstep ih

/-- **The start states correspond**, after the entry block's moves have run. -/
theorem seq_start (p : Prog R) {f : FuncId} {args : List Word} {mem : Memory} {s : State R}
    (h : p.start f args mem = some s) :
    ∃ t₀ t, (sequentializeProg p).start f args mem = some t₀ ∧
      Steps (sequentializeProg p) t₀ t ∧ StateRel p s t := by
  rw [Prog.start] at h
  cases he : p.enter f args with
  | none => rw [he] at h; simp at h
  | some r =>
    obtain ⟨pt, fr⟩ := r
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨g, g', henter, hsteps, hrel⟩ := seq_enter p he [] mem
    exact ⟨⟨pt, g, [], mem⟩, ⟨seqPoint p pt, g', [], mem⟩,
      by rw [Prog.start, henter]; rfl, hsteps, ⟨rfl, hrel, List.Forall₂.nil, rfl⟩⟩

/-- **Sequentialization preserves and reflects behaviour.** The two programs
have exactly the same four behaviours, stuck included, started on the same
function, arguments and memory — and **with no hypotheses at all**, not even
well-formedness, because the transformation is syntactic and the correspondence
is exact. -/
theorem sequentializeProg_behaves (p : Prog R) {f : FuncId} {args : List Word} {mem : Memory}
    {s : State R} (hs : p.start f args mem = some s) :
    ∃ t, (sequentializeProg p).start f args mem = some t ∧
      ∀ b : Behavior, Behaves p s b ↔ Behaves (sequentializeProg p) t b := by
  obtain ⟨t₀, t, hstart, hpre, hrel⟩ := seq_start p hs
  refine ⟨t₀, hstart, ?_⟩
  have sim : Silmaril.LockstepSim (Step p) (Step (sequentializeProg p)) (StateRel p) :=
    ⟨fun hst hr => seq_step p hr hst⟩
  have fwd : ∀ b : Behavior, Behaves p s b → Behaves (sequentializeProg p) t₀ b := by
    intro b hb
    refine behaves_of_steps hpre ?_
    cases b with
    | returned vs m =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨u', hu', hrel'⟩ := sim.steps hu hrel
      exact ⟨u', hu', seq_returned p hrel' hfin⟩
    | trapped m =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨u', hu', hrel'⟩ := sim.steps hu hrel
      exact ⟨u', hu', seq_trapped p hrel' hfin⟩
    | stuck =>
      obtain ⟨u, hu, hfin⟩ := hb
      obtain ⟨u', hu', hrel'⟩ := sim.steps hu hrel
      exact ⟨u', hu', seq_stuck p hrel' hfin⟩
    | diverges => exact sim.diverges hb hrel
  obtain ⟨b₀, hb₀⟩ := Behaves.exists p s
  exact fun b => ⟨fwd b, fun hb => (Behaves.unique hb (fwd b₀ hb₀)) ▸ hb₀⟩

end Silmaril.Machine.RTL.SSA
