module

public import Silmaril.Machine.CBackend.RTL.SSA.Defs
public import Silmaril.Machine.CBackend.RTL.Examples.Defs
/-!
# Maximal SSA construction: general `RTL` to `RTL.SSA`

`RTL` is a control-flow graph of single instructions, each naming its own
successors; `RTL.SSA` is block-structured and in static single assignment form.
This file relates the two by an SSA-construction pass. The pass implemented
here is the **maximal construction**: every register of the function becomes a
block argument of every block, and every jump passes every register. It is the
simplest construction that is literally in SSA form, it needs no dominance
computation and no dominance-frontier machinery, and its correctness argument is
a near-lockstep simulation in which the SSA frame merely records, under a fresh
name per block, the value the `RTL` frame holds — one source step for one or two
target steps, except at a call, where the callee's entry block runs first.

A Braun et al.-style *minimal* construction — one that inserts a block argument
only where two definitions actually meet, and otherwise forwards the single
reaching definition — is a later optimisation of this pass, not a different one:
its output is the maximal output with redundant block arguments removed. Doing
the simple thing first is deliberate, and the simple thing is what is here.

## The shape of the output

A function with `code.length` nodes becomes a function with `code.length + 1`
blocks. For `n < code.length`, block `n` is RTL node `n`: it takes the
function's registers as parameters, holds the single straight-line operation
that node `n`'s instruction performs (none, for `nop`, `cond`, `jump`, `ret` and
`trap`), and ends in the terminator that node `n`'s instruction induces. A
`call` is an SSA `call` op followed by a jump, exactly as a `const` is a `const`
op followed by a jump, because `RTL` calls have successors and SSA calls are
straight-line ops. Block `code.length` is a fresh entry block, described below.

## Where the sketch did not survive contact with the definitions

The original sketch asked for `construct : RTL.Func R → SSA.Func R`, one theorem
for well-formedness and one for behaviour. Five things had to change, and all
five are visible in the statements below.

* **The register type is indexed.** `SSA.Func.SingleAssignment` demands that no
  register is defined twice anywhere in the function, and the maximal
  construction makes every register a parameter of every block, so the same name
  would be defined `code.length` times. The output is therefore
  `SSA.Func (Name R)` for the four-constructor type `Name R`: `Name.param n r`
  is RTL register `r` on entry to block `n`, `Name.result n r` is the value node
  `n` writes into `r`, and `Name.arg r` and `Name.init r` are the entry block's
  two kinds of definition. `R` must have `DecidableEq`, which it needed anyway
  to run either machine. `Name.node?` is the tag that separates the definitions
  of distinct blocks and is what `construct_singleAssignment` runs on.

* **There is a fresh entry block, and it writes zero into every register that is
  not a parameter.** `SSA.Func.WellFormedSig` checks the entry block's parameter
  count against `sig.params`, so the entry block cannot be the block for
  `fn.entry`, whose parameters are *all* the registers. Block `code.length`
  therefore takes exactly the images of `fn.params` under `Name.arg` and jumps
  to block `fn.entry`. That jump must supply a value for every register, and
  there is no word denoting "unwritten": in `RTL` an unwritten register reads as
  `none` and the machine is stuck, whereas in SSA every block argument is a
  register that has to have been written. The entry block hence defines
  `Name.init r` by a `const … 0` for every register that is not a parameter and
  passes it. **This makes the SSA function strictly more defined than its
  source**: where `RTL` would be stuck reading an unwritten register, the
  construction reads zero and carries on. The simulation is stated accordingly
  (see below).

* **Two side conditions.** `Func.Constructible` asks that `fn.params` be
  duplicate-free and that every instruction's `defs` be duplicate-free (only
  `call` can violate the second, by naming the same result register twice).
  Both are exactly what `SingleAssignment` needs of the entry block and of a
  node block, and neither follows from `WellFormedSig`, which constrains only
  lengths. They turned out to be enough: no further strengthening of
  `Constructible` was needed for any of the four well-formedness theorems.

* **`AgreesAt` has to say that the SSA frame is *total* on the function's
  registers, not merely that it extends the RTL frame.** The sketch's relation
  recorded only that every register the RTL frame had written the SSA frame had
  written to the same value. That is not an invariant of the simulation, because
  a jump of the output passes *every* register of the function: the target run
  would be stuck reading an argument the source had never written. `AgreesAt`
  therefore also asserts `(fr'.get (.param pt.node r)).isSome` for every
  `r ∈ fn.regs`. It is an invariant precisely because the fresh entry block
  writes every register and every jump passes every register, which is the one
  place where the maximality of the construction is load-bearing for the
  semantics rather than for the syntax.

* **The simulation takes one-or-more target steps, and the behavioural
  statement is an `iff` only for stuck-free source runs.** One RTL step becomes
  one SSA step for `nop`, `jump` and `cond`, two for a node that computes (the
  block's operation and the block's jump), two for a `ret` into a caller (the
  return and the caller block's jump), and `|initRegs| + 2` for a `call` (the
  call op, the callee entry block's initialising `const`s, and its jump), so
  `construct_step` produces a `Relation.TransGen` of SSA steps. The start states
  are not related on the nose either: `construct_start_steps` says the SSA start
  state *reaches* a state agreeing with the RTL start state, after running the
  entry block. Finally `construct_behaves_of_ne_stuck` holds with no safety
  hypothesis for every behaviour other than `stuck`, and the two-directional
  `construct_behaves` adds the hypothesis that the source run does not get
  stuck. The hypothesis is not an artefact: a source run that is stuck on an
  unwritten register has a target run that continues.

## What is proved

Everything stated. There is no `sorry` in this file.

* `construct_wellFormedSig`, `construct_singleAssignment`, `construct_argsMatch`
  from `WellFormedSig` and `Constructible` as appropriate, and
  `construct_usesDominated` with no hypothesis at all — the maximal
  construction's whole point is that a block uses only its own parameters and
  the results of its own single operation. `construct_wellFormed` and
  `constructProg_wellFormed` follow.
* `construct_start_steps` and `construct_step`, the forward simulation, via
  `enter_steps` (a whole entry block) and `transfer_regs` (a whole edge).
* `construct_behaves_of_ne_stuck` for every behaviour but `stuck`, and the
  two-directional `construct_behaves` under `¬ Behaves p s .stuck`.

The last of these is checked against `RTL.Examples.factorial` at the end of the
file: the construction of that program is well-formed both by the theorems and
by `decide`, and it returns the same values.

-/

@[expose] public section

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)

/-- The SSA register names the construction produces for a single function.
`param n r` carries the value of RTL register `r` into the block for node `n`,
`result n r` is the value node `n`'s instruction writes into `r`, `arg r` is the
entry block's parameter for the RTL parameter register `r`, and `init r` is the
zero the entry block supplies for a register that is not a parameter. The node
index is what makes the construction single-assignment: `r` is defined once per
block, under a name mentioning that block. -/
inductive Name (R : Type) where
  | arg (r : R)
  | init (r : R)
  | param (n : Node) (r : R)
  | result (n : Node) (r : R)
  deriving DecidableEq, Repr

/-- The node a name belongs to: the names `param n r` and `result n r` are the
definitions of the block for node `n`, while `arg r` and `init r` are the
definitions of the fresh entry block and belong to no node. Separating the
definitions of distinct blocks is what makes the construction
single-assignment, and this is the function that separates them. -/
def Name.node? {R : Type} : Name R → Option Node
  | .arg _ | .init _ => none
  | .param n _ | .result n _ => some n

variable {R : Type} [DecidableEq R]

/-! ## Reading and writing lists of registers

The construction renames every register, so the simulation needs to know how
`Frame.readAll` and `Frame.writeAll` behave under a renaming: a write leaves
every other register alone, a write defines what it names, and a write of
`rs.map g` for an injective `g` mirrors a write of `rs` itself. -/

section Frames

variable {S T : Type} [DecidableEq S] [DecidableEq T]

omit [DecidableEq S] in
/-- Reading a non-empty list reads its head and then its tail. -/
theorem readAll_cons (fr : Frame S) (r : S) (rs : List S) :
    fr.readAll (r :: rs) = (fr.get r).bind fun v => (fr.readAll rs).map (v :: ·) := by
  simp only [Frame.readAll, List.mapM_cons]
  cases h : fr.get r <;> cases h' : List.mapM fr.get rs <;> rfl

omit [DecidableEq S] in
/-- Reading depends only on the values of the registers read. -/
theorem readAll_congr {fr fr' : Frame S} :
    ∀ {rs : List S}, (∀ r ∈ rs, fr.get r = fr'.get r) → fr.readAll rs = fr'.readAll rs
  | [], _ => rfl
  | r :: rs, h => by
    rw [readAll_cons, readAll_cons, h r (by simp), readAll_congr fun x hx => h x (by simp [hx])]

omit [DecidableEq S] in
/-- A list of registers that have all been written can be read back, yielding
one value per register. -/
theorem readAll_isSome :
    ∀ {fr : Frame S} {rs : List S}, (∀ r ∈ rs, (fr.get r).isSome) →
      ∃ vals, fr.readAll rs = some vals ∧ vals.length = rs.length
  | _, [], _ => ⟨[], rfl, rfl⟩
  | fr, r :: rs, h => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h r (by simp))
    obtain ⟨vals, hvals, hlen⟩ :=
      readAll_isSome (fr := fr) (rs := rs) fun x hx => h x (by simp [hx])
    exact ⟨v :: vals, by rw [readAll_cons, hv, hvals]; rfl, by simp [hlen]⟩

/-- Writing a list of registers leaves every register outside it alone. -/
theorem writeAll_get_of_not_mem :
    ∀ {rs : List S} {vals : List Word} {fr fr' : Frame S} {r : S},
      fr.writeAll rs vals = some fr' → r ∉ rs → fr'.get r = fr.get r
  | [], [], fr, fr', r, h, _ => by cases h; rfl
  | [], _ :: _, _, _, _, h, _ => by simp [Frame.writeAll] at h
  | _ :: _, [], _, _, _, h, _ => by simp [Frame.writeAll] at h
  | x :: xs, v :: vs, fr, fr', r, h, hr => by
    have h' : (fr.set x v).writeAll xs vs = some fr' := h
    rw [writeAll_get_of_not_mem h' fun hx => hr (by simp [hx]), Frame.get_set,
      ite_eq_right fun hx => hr (by simp [hx])]

/-- Writing a list of registers never unwrites a register. -/
theorem writeAll_isSome_mono :
    ∀ {rs : List S} {vals : List Word} {fr fr' : Frame S} {r : S},
      fr.writeAll rs vals = some fr' → (fr.get r).isSome → (fr'.get r).isSome
  | [], [], fr, fr', r, h, hr => by cases h; exact hr
  | [], _ :: _, _, _, _, h, _ => by simp [Frame.writeAll] at h
  | _ :: _, [], _, _, _, h, _ => by simp [Frame.writeAll] at h
  | x :: xs, v :: vs, fr, fr', r, h, hr => by
    have h' : (fr.set x v).writeAll xs vs = some fr' := h
    refine writeAll_isSome_mono h' ?_
    rw [Frame.get_set]
    split <;> simp [hr]

/-- Every register a write names is afterwards written. -/
theorem writeAll_isSome_of_mem :
    ∀ {rs : List S} {vals : List Word} {fr fr' : Frame S} {r : S},
      fr.writeAll rs vals = some fr' → r ∈ rs → (fr'.get r).isSome
  | [], _, _, _, _, _, hr => by simp at hr
  | _ :: _, [], _, _, _, h, _ => by simp [Frame.writeAll] at h
  | x :: xs, v :: vs, fr, fr', r, h, hr => by
    have h' : (fr.set x v).writeAll xs vs = some fr' := h
    rcases List.mem_cons.mp hr with rfl | hr
    · exact writeAll_isSome_mono h' (by simp [Frame.get_set])
    · exact writeAll_isSome_of_mem h' hr

/-- A write succeeds exactly when it has one value per register. -/
theorem writeAll_isSome_iff :
    ∀ {rs : List S} {vals : List Word} {fr : Frame S},
      (fr.writeAll rs vals).isSome ↔ rs.length = vals.length
  | [], [], _ => by simp [Frame.writeAll]
  | [], _ :: _, _ => by simp [Frame.writeAll]
  | _ :: _, [], _ => by simp [Frame.writeAll]
  | x :: xs, v :: vs, fr =>
    by simpa [Frame.writeAll] using writeAll_isSome_iff (rs := xs) (vals := vs) (fr := fr.set x v)

/-- A write through an injective renaming mirrors the write itself: a frame
that agrees with another under `g` still agrees after both write the same
values, one to `rs` and the other to `rs.map g`. -/
theorem writeAll_agree {g : S → T} (hg : Function.Injective g) :
    ∀ {rs : List S} {vals : List Word} {fr fr' : Frame S} {sr sr' : Frame T},
      fr.writeAll rs vals = some fr' → sr.writeAll (rs.map g) vals = some sr' →
      (∀ (r : S) (w : Word), fr.get r = some w → sr.get (g r) = some w) →
      ∀ (r : S) (w : Word), fr'.get r = some w → sr'.get (g r) = some w
  | [], [], _, _, _, _, hw, hw', hb => by cases hw; cases hw'; exact hb
  | [], _ :: _, _, _, _, _, hw, _, _ => by simp [Frame.writeAll] at hw
  | _ :: _, [], _, _, _, _, hw, _, _ => by simp [Frame.writeAll] at hw
  | x :: xs, v :: vs, fr, fr', sr, sr', hw, hw', hb => by
    have h1 : (fr.set x v).writeAll xs vs = some fr' := hw
    have h2 : (sr.set (g x) v).writeAll (xs.map g) vs = some sr' := hw'
    refine writeAll_agree hg h1 h2 ?_
    intro r w hr
    simp only [Frame.get_set] at hr ⊢
    by_cases hx : r = x
    · subst hx; rw [ite_eq_left rfl] at hr; rw [ite_eq_left rfl]; exact hr
    · rw [ite_eq_right hx] at hr
      rw [ite_eq_right fun he => hx (hg he)]
      exact hb r w hr

/-- A write through an injective renaming writes the same values: on the
registers written, the renamed frame holds exactly what the original does. -/
theorem writeAll_map_get {g : S → T} (hg : Function.Injective g) :
    ∀ {rs : List S}, rs.Nodup → ∀ {vals : List Word} {fr fr' : Frame S} {sr sr' : Frame T},
      fr.writeAll rs vals = some fr' → sr.writeAll (rs.map g) vals = some sr' →
      ∀ r ∈ rs, sr'.get (g r) = fr'.get r
  | [], _, _, _, _, _, _, _, _, r, hr => by simp at hr
  | _ :: _, _, [], _, _, _, _, hw, _, _, _ => by simp [Frame.writeAll] at hw
  | x :: xs, hnd, v :: vs, fr, fr', sr, sr', hw, hw', r, hr => by
    have h1 : (fr.set x v).writeAll xs vs = some fr' := hw
    have h2 : (sr.set (g x) v).writeAll (xs.map g) vs = some sr' := hw'
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    rcases List.mem_cons.mp hr with rfl | hr
    · have hgx : g r ∉ xs.map g := fun hmem => by
        obtain ⟨y, hy, hgy⟩ := List.mem_map.mp hmem
        exact hx (hg hgy ▸ hy)
      rw [writeAll_get_of_not_mem h2 hgx, writeAll_get_of_not_mem h1 hx]
      simp [Frame.get_set]
    · exact writeAll_map_get hg (List.nodup_cons.mp hnd).2 h1 h2 r hr

omit [DecidableEq S] in
/-- The frame a transfer of the construction produces. The target's parameters
are `rs.map g` and the arguments are `rs.map h`, so afterwards `g r` holds what
`h r` held. The hypothesis `hsep` is what stops a parameter written early in
the transfer from clobbering an argument read later, and holds in the
construction because an argument name and a parameter name agree only on the
same register. -/
theorem writeAll_readAll_map {g h : S → T} (hg : Function.Injective g)
    (hsep : ∀ r r' : S, r ≠ r' → h r ≠ g r') :
    ∀ {rs : List S}, rs.Nodup → ∀ {vals : List Word} {fr fr' : Frame T},
      fr.readAll (rs.map h) = some vals → fr.writeAll (rs.map g) vals = some fr' →
      ∀ r ∈ rs, fr'.get (g r) = fr.get (h r)
  | [], _, _, _, _, _, _, r, hr => by simp at hr
  | x :: xs, hnd, vals, fr, fr', hread, hwrite, r, hr => by
    have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, readAll_cons] at hread
    cases hv : fr.get (h x) with
    | none => rw [hv] at hread; simp at hread
    | some v =>
      rw [hv] at hread
      simp only [Option.bind_some, Option.map_eq_some_iff] at hread
      obtain ⟨vs, hvs, rfl⟩ := hread
      have h2 : (fr.set (g x) v).writeAll (xs.map g) vs = some fr' := hwrite
      have hcong : ∀ z ∈ xs.map h, fr.get z = (fr.set (g x) v).get z := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
        rw [Frame.get_set, ite_eq_right (hsep y x fun he => hx (he ▸ hy))]
      have hread' : (fr.set (g x) v).readAll (xs.map h) = some vs := by
        rw [← readAll_congr hcong]; exact hvs
      rcases List.mem_cons.mp hr with rfl | hr
      · have hgx : g r ∉ xs.map g := fun hmem => by
          obtain ⟨y, hy, hgy⟩ := List.mem_map.mp hmem
          exact hx (hg hgy ▸ hy)
        rw [writeAll_get_of_not_mem h2 hgx, Frame.get_set, ite_eq_left rfl, hv]
      · rw [writeAll_readAll_map hg hsep (List.nodup_cons.mp hnd).2 hread' h2 r hr,
          Frame.get_set, ite_eq_right (hsep r x fun he => hx (he ▸ hr))]

end Frames


omit [DecidableEq R] in
/-- `Name.arg` is injective, so the entry block's parameters are as distinct as
the function's. -/
theorem Name.arg_injective : Function.Injective (Name.arg (R := R)) := by
  intro a b h; simpa using h

omit [DecidableEq R] in
/-- `Name.init` is injective. -/
theorem Name.init_injective : Function.Injective (Name.init (R := R)) := by
  intro a b h; simpa using h

omit [DecidableEq R] in
/-- `Name.param n` is injective, so the parameters of the block for node `n`
are as distinct as the function's registers. -/
theorem Name.param_injective (n : Node) : Function.Injective (Name.param (R := R) n) := by
  intro a b h; simpa using h

omit [DecidableEq R] in
/-- `Name.result n` is injective. -/
theorem Name.result_injective (n : Node) : Function.Injective (Name.result (R := R) n) := by
  intro a b h; simpa using h

omit [DecidableEq R] in
/-- An entry-block argument belongs to no node. -/
@[simp] theorem Name.node?_arg (r : R) : (Name.arg r).node? = none := rfl

omit [DecidableEq R] in
/-- An entry-block initialisation belongs to no node. -/
@[simp] theorem Name.node?_init (r : R) : (Name.init r).node? = none := rfl

omit [DecidableEq R] in
/-- A block parameter belongs to the node whose block it is. -/
@[simp] theorem Name.node?_param (n : Node) (r : R) : (Name.param n r).node? = some n := rfl

omit [DecidableEq R] in
/-- An operation result belongs to the node whose operation it is. -/
@[simp] theorem Name.node?_result (n : Node) (r : R) : (Name.result n r).node? = some n := rfl

namespace Func

/-- Every register the function mentions, each once: its parameters together
with the registers read and written by every instruction of its code. This is
the list that becomes the parameter list of every block and the argument list of
every jump, which is what "maximal" means. -/
def regs (fn : Func R) : List R :=
  (fn.params ++ fn.code.flatMap fun i => i.uses ++ i.defs).dedup

/-- The registers the entry block has to invent a value for: those the function
mentions but does not receive as parameters. -/
def initRegs (fn : Func R) : List R :=
  fn.regs.filter fun r => decide (r ∉ fn.params)

/-- The label of the fresh entry block, one past the last node. Block `n` is
RTL node `n` for every `n < fn.code.length`, so this is the only label left. -/
def entryLabel (fn : Func R) : SSA.Label := fn.code.length

/-- The registers of a function are pairwise distinct, since `regs` deduplicates. -/
theorem regs_nodup (fn : Func R) : fn.regs.Nodup := List.nodup_dedup _

/-- A parameter is a register of the function. -/
theorem mem_regs_of_mem_params {fn : Func R} {r : R} (h : r ∈ fn.params) : r ∈ fn.regs := by
  simp only [regs, List.mem_dedup, List.mem_append]
  exact .inl h

/-- A register read by an instruction of the code is a register of the function. -/
theorem mem_regs_of_mem_uses {fn : Func R} {i : Instr R} (hi : i ∈ fn.code) {r : R}
    (h : r ∈ i.uses) : r ∈ fn.regs := by
  simp only [regs, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact .inr ⟨i, hi, .inl h⟩

/-- A register written by an instruction of the code is a register of the function. -/
theorem mem_regs_of_mem_defs {fn : Func R} {i : Instr R} (hi : i ∈ fn.code) {r : R}
    (h : r ∈ i.defs) : r ∈ fn.regs := by
  simp only [regs, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact .inr ⟨i, hi, .inr h⟩

/-- The registers the entry block initialises are pairwise distinct. -/
theorem initRegs_nodup (fn : Func R) : fn.initRegs.Nodup := List.Nodup.filter _ fn.regs_nodup

/-- A register of the function that is not a parameter is initialised. -/
theorem mem_initRegs {fn : Func R} {r : R} (h : r ∈ fn.regs) (hp : r ∉ fn.params) :
    r ∈ fn.initRegs := List.mem_filter.mpr ⟨h, by simpa using hp⟩

/-- An initialised register is a register of the function, and not a parameter. -/
theorem mem_regs_of_mem_initRegs {fn : Func R} {r : R} (h : r ∈ fn.initRegs) :
    r ∈ fn.regs ∧ r ∉ fn.params := by
  rw [initRegs, List.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

end Func

namespace Instr

/-- The straight-line operations of the block for node `n`: one operation for
each instruction that computes something, and none for `nop` and for the
instructions that become terminators. Operands are read from the block's
parameters, since no earlier operation of the block can have redefined them, and
results are written to fresh `Name.result` names. -/
def toOps (n : Node) : Instr R → List (SSA.Op (Name R))
  | .nop _ | .cond _ _ _ | .jump _ | .ret _ | .trap => []
  | .const d v _ => [.const (.result n d) v]
  | .move d src _ => [.move (.result n d) (.param n src)]
  | .unary op d src _ => [.unary op (.result n d) (.param n src)]
  | .binary op d a b _ => [.binary op (.result n d) (.param n a) (.param n b)]
  | .load w e d base off _ => [.load w e (.result n d) (.param n base) off]
  | .store w base off src _ => [.store w (.param n base) off (.param n src)]
  | .call f args results _ => [.call f (args.map (Name.param n)) (results.map (Name.result n))]

/-- The name under which the block for node `n` holds the value of register `r`
once the node's instruction has run: the operation's result when the
instruction writes `r`, and the block parameter otherwise. -/
def nameAt (n : Node) (i : Instr R) (r : R) : Name R :=
  if r ∈ i.defs then .result n r else .param n r

/-- The arguments the block for node `n` passes to any successor: for each
register of the function, the latest definition of it in the block, which is
`nameAt`. -/
def jumpArgs (fn : Func R) (n : Node) (i : Instr R) : List (Name R) :=
  fn.regs.map (i.nameAt n)

/-- The terminator of the block for node `n`. An instruction with a single
successor ends its block in a jump carrying `jumpArgs`; `cond` becomes an SSA
`cond` passing the same arguments on both edges; `ret` and `trap` become
themselves, reading the block's parameters. -/
def toTerm (fn : Func R) (n : Node) (i : Instr R) : SSA.Term (Name R) :=
  match i with
  | .nop s | .const _ _ s | .move _ _ s | .unary _ _ _ s | .binary _ _ _ _ s
  | .load _ _ _ _ _ s | .store _ _ _ _ s | .call _ _ _ s
  | .jump s => .jump s (i.jumpArgs fn n)
  | .cond c t₁ t₂ => .cond (.param n c) t₁ (i.jumpArgs fn n) t₂ (i.jumpArgs fn n)
  | .ret values => .ret (values.map (Name.param n))
  | .trap => .trap

/-- The block for node `n`: the function's registers as parameters, the node's
operation, and the node's terminator. -/
def toBlock (fn : Func R) (n : Node) (i : Instr R) : SSA.Block (Name R) where
  params := fn.regs.map (Name.param n)
  ops := i.toOps n
  term := i.toTerm fn n

/-- The terminator of the block for node `n` transfers exactly where the node's
instruction does. -/
theorem toTerm_successors (fn : Func R) (n : Node) (i : Instr R) :
    (i.toTerm fn n).successors = i.successors := by cases i <;> rfl

/-- A terminator of the output fits a function with one more block than the
source has nodes, because the source instruction's successors are nodes of the
source code. -/
theorem toTerm_okIn {fn : Func R} {n : Node} {i : Instr R} {res nodes : Nat}
    (h : i.okIn res nodes = true) : (i.toTerm fn n).okIn res (nodes + 1) = true := by
  have lt : ∀ a b : Nat, a < b → a < b + 1 := fun _ _ h => Nat.lt_succ_of_lt h
  cases i <;> simp_all [Instr.okIn, SSA.Term.okIn, Instr.toTerm, Instr.successors,
    SSA.Term.successors]

omit [DecidableEq R] in
/-- An instruction that fits a function has every successor inside the code. -/
theorem lt_of_mem_successors {res nodes : Nat} {i : Instr R} (h : i.okIn res nodes = true)
    {t : Node} (ht : t ∈ i.successors) : t < nodes := by
  cases i <;> simp_all [Instr.okIn, Instr.successors]
  rcases ht with rfl | rfl
  · exact h.1
  · exact h.2

/-- Every target of the terminator of the block for node `n` is a successor of
the node's instruction, and is passed one argument per register of the
function. -/
theorem mem_toTerm_args {fn : Func R} {n : Node} {i : Instr R}
    {ta : SSA.Label × List (Name R)} (h : ta ∈ (i.toTerm fn n).args) :
    ta.1 ∈ i.successors ∧ ta.2.length = fn.regs.length := by
  cases i <;> simp_all [Instr.toTerm, SSA.Term.args, Instr.successors, Instr.jumpArgs]
  rcases h with rfl | rfl <;> simp

omit [DecidableEq R] in
omit [DecidableEq R] in
/-- The operations of the block for node `n` define exactly the registers the
node's instruction writes, under `Name.result n`. -/
theorem toOps_flatMap_defs (n : Node) (i : Instr R) :
    (i.toOps n).flatMap SSA.Op.defs = i.defs.map (Name.result n) := by
  cases i <;> simp [Instr.toOps, SSA.Op.defs, Instr.defs, Instr.dest?]

/-- The block for node `n` defines the function's registers under `Name.param n`
and the instruction's own writes under `Name.result n`. -/
theorem toBlock_defs (fn : Func R) (n : Node) (i : Instr R) :
    (i.toBlock fn n).defs = fn.regs.map (Name.param n) ++ i.defs.map (Name.result n) := by
  rw [SSA.Block.defs, show (i.toBlock fn n).params = fn.regs.map (Name.param n) from rfl,
    show (i.toBlock fn n).ops = i.toOps n from rfl, toOps_flatMap_defs]

/-- Every name the block for node `n` defines mentions `n`, which is what keeps
the definitions of distinct blocks apart. -/
theorem toBlock_defs_node? {fn : Func R} {n : Node} {i : Instr R} {x : Name R}
    (h : x ∈ (i.toBlock fn n).defs) : x.node? = some n := by
  rw [toBlock_defs] at h
  rcases List.mem_append.mp h with h | h <;> obtain ⟨r, -, rfl⟩ := List.mem_map.mp h <;> rfl

/-- The block for a node whose instruction writes no register twice defines no
name twice. -/
theorem toBlock_defs_nodup {fn : Func R} {n : Node} {i : Instr R} (h : i.defs.Nodup) :
    (i.toBlock fn n).defs.Nodup := by
  rw [toBlock_defs]
  refine List.Nodup.append (List.Nodup.map (Name.param_injective n) fn.regs_nodup)
    (List.Nodup.map (Name.result_injective n) h) ?_
  rw [List.disjoint_left]
  rintro x hx hx'
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hx'
  exact absurd hb (by simp)

/-- Every register an operation of the block for node `n` reads is a parameter
of that block, because operands are read from the block's parameters. -/
theorem mem_toBlock_params_of_op_uses {fn : Func R} {n : Node} {i : Instr R} (hi : i ∈ fn.code)
    {o : SSA.Op (Name R)} (ho : o ∈ i.toOps n) {x : Name R} (hx : x ∈ o.uses) :
    x ∈ (i.toBlock fn n).params := by
  have key : ∃ r ∈ i.uses, Name.param n r = x := by
    cases i <;> simp_all [Instr.toOps, SSA.Op.uses, Instr.uses, eq_comm]
  obtain ⟨r, hr, rfl⟩ := key
  exact List.mem_map_of_mem (fn.mem_regs_of_mem_uses hi hr)

/-- Every argument the block for node `n` passes along an edge is a parameter of
the block or a result of its own operation. -/
theorem mem_jumpArgs {fn : Func R} {n : Node} {i : Instr R} {x : Name R}
    (h : x ∈ i.jumpArgs fn n) :
    x ∈ (i.toBlock fn n).params ∨ ∃ o ∈ (i.toBlock fn n).ops, x ∈ o.defs := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  rw [Instr.nameAt]
  split
  · refine .inr (List.mem_flatMap.mp ?_)
    rw [show (i.toBlock fn n).ops = i.toOps n from rfl, toOps_flatMap_defs]
    exact List.mem_map_of_mem (by assumption)
  · exact .inl (List.mem_map_of_mem hr)

/-- Every register the terminator of the block for node `n` reads is a parameter
of the block or a result of its own operation. This is what makes the maximal
construction's uses trivially dominated. -/
theorem mem_toBlock_term_uses {fn : Func R} {n : Node} {i : Instr R} (hi : i ∈ fn.code)
    {x : Name R} (hx : x ∈ (i.toBlock fn n).term.uses) :
    x ∈ (i.toBlock fn n).params ∨ ∃ o ∈ (i.toBlock fn n).ops, x ∈ o.defs := by
  have hterm : (i.toBlock fn n).term = i.toTerm fn n := rfl
  rw [hterm] at hx
  have hparam : ∀ r ∈ i.uses, (Name.param n r : Name R) ∈ (i.toBlock fn n).params :=
    fun r hr => List.mem_map_of_mem (fn.mem_regs_of_mem_uses hi hr)
  cases i with
  | nop s => exact mem_jumpArgs hx
  | const d v s => exact mem_jumpArgs hx
  | move d src s => exact mem_jumpArgs hx
  | unary op d src s => exact mem_jumpArgs hx
  | binary op d a b s => exact mem_jumpArgs hx
  | load w e d base off s => exact mem_jumpArgs hx
  | store w base off src s => exact mem_jumpArgs hx
  | call g args results s => exact mem_jumpArgs hx
  | jump t => exact mem_jumpArgs hx
  | cond c t₁ t₂ =>
    rw [Instr.toTerm, SSA.Term.uses, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact .inl (hparam c (by simp [Instr.uses]))
    · rcases List.mem_append.mp hx with hx | hx <;> exact mem_jumpArgs hx
  | ret values =>
    rw [Instr.toTerm, SSA.Term.uses] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact .inl (hparam r hr)
  | trap => rw [Instr.toTerm, SSA.Term.uses] at hx; simp at hx

end Instr

namespace Func

/-- The fresh entry block. Its parameters are exactly the images of the
function's parameters, so that its parameter count is the signature's; it
defines zero for every other register of the function, because the jump into the
block for `fn.entry` must supply a value for every register and `RTL` has no
value for an unwritten one; and it jumps to the block for `fn.entry`. -/
def entryBlock (fn : Func R) : SSA.Block (Name R) where
  params := fn.params.map Name.arg
  ops := fn.initRegs.map fun r => .const (Name.init r) 0
  term := .jump fn.entry (fn.regs.map fun r => if r ∈ fn.params then .arg r else .init r)

end Func

/-- **The maximal SSA construction.** Block `n` is RTL node `n` for every
`n < fn.code.length`, every block takes `fn.regs` as parameters and every jump
passes `fn.regs`; the last block, at label `fn.entryLabel`, is the fresh entry
block that binds the function's parameters and initialises the remaining
registers. The signature is unchanged, so a caller's `call` is unaffected. -/
def construct (fn : Func R) : SSA.Func (Name R) where
  sig := fn.sig
  entry := fn.entryLabel
  blocks := (fn.code.zipIdx.map fun p => p.1.toBlock fn p.2) ++ [fn.entryBlock]

/-- The construction applied to every function of a program, keeping function
identifiers, so that a `call` names the same callee before and after. -/
def constructProg (p : Prog R) : SSA.Prog (Name R) where
  funcs := p.funcs.map construct

namespace Func

/-- The side conditions the construction needs beyond `WellFormedSig`, which
constrains only lengths: the parameter list must not repeat a register, and no
instruction may write the same register twice, which only a `call` naming a
result register twice can do. Both are what `SingleAssignment` asks of the entry
block and of a node block respectively. -/
structure Constructible (fn : Func R) : Prop where
  params : fn.params.Nodup
  defs : ∀ i ∈ fn.code, i.defs.Nodup

instance (fn : Func R) : Decidable fn.Constructible :=
  decidable_of_iff (fn.params.Nodup ∧ ∀ i ∈ fn.code, i.defs.Nodup)
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.params, h.defs⟩⟩

end Func

namespace Prog

/-- Every function of the program satisfies the construction's side
conditions. -/
def Constructible (p : Prog R) : Prop := ∀ fn ∈ p.funcs, fn.Constructible

instance (p : Prog R) : Decidable p.Constructible := inferInstanceAs (Decidable (∀ _ ∈ _, _))

end Prog

/-! ## The shape of the output -/

/-- The signature of the output is the source signature. -/
@[simp] theorem construct_sig (fn : Func R) : (construct fn).sig = fn.sig := rfl

/-- The entry block of the output is the fresh one. -/
@[simp] theorem construct_entry (fn : Func R) : (construct fn).entry = fn.entryLabel := rfl

/-- The blocks of the output are the node blocks followed by the fresh entry
block. -/
theorem construct_blocks (fn : Func R) :
    (construct fn).blocks =
      (fn.code.zipIdx.map fun p => p.1.toBlock fn p.2) ++ [fn.entryBlock] := rfl

/-- The output has one block per node and one more for the fresh entry. -/
@[simp] theorem construct_blocks_length (fn : Func R) :
    (construct fn).blocks.length = fn.code.length + 1 := by
  simp [construct_blocks]

/-- The block for an existing node is the block that node's instruction
induces. -/
theorem construct_block?_of_instr? {fn : Func R} {n : Node} {i : Instr R}
    (h : fn.instr? n = some i) : (construct fn).block? n = some (i.toBlock fn n) := by
  have hn : n < fn.code.length := (List.getElem?_eq_some_iff.mp h).1
  rw [SSA.Func.block?, construct_blocks, List.getElem?_append_left (by simpa using hn),
    List.getElem?_map, List.getElem?_zipIdx, show fn.code[n]? = some i from h]
  simp

/-- The fresh entry block is the last block of the output. -/
theorem construct_block?_entryLabel (fn : Func R) :
    (construct fn).block? fn.entryLabel = some fn.entryBlock := by
  rw [SSA.Func.block?, construct_blocks, Func.entryLabel, List.getElem?_append_right (by simp)]
  simp

/-- Every block for a node takes one parameter per register of the function. -/
theorem construct_block?_params_length {fn : Func R} {t : Node} (h : t < fn.code.length) :
    ∃ b, (construct fn).block? t = some b ∧ b.params.length = fn.regs.length := by
  refine ⟨_, construct_block?_of_instr? (i := fn.code[t]) (List.getElem?_eq_getElem h), ?_⟩
  simp [Instr.toBlock]

/-- The entry block defines the function's parameters under `Name.arg` and the
remaining registers under `Name.init`. -/
theorem entryBlock_defs (fn : Func R) :
    fn.entryBlock.defs = fn.params.map Name.arg ++ fn.initRegs.map Name.init := by
  rw [SSA.Block.defs, show fn.entryBlock.params = fn.params.map Name.arg from rfl,
    show fn.entryBlock.ops = fn.initRegs.map (fun r => SSA.Op.const (Name.init r) 0) from rfl,
    List.flatMap_map]
  congr 1
  induction fn.initRegs with
  | nil => rfl
  | cons r rs ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

/-- Every name the entry block defines belongs to no node. -/
theorem entryBlock_defs_node? {fn : Func R} {x : Name R} (h : x ∈ fn.entryBlock.defs) :
    x.node? = none := by
  rw [entryBlock_defs] at h
  rcases List.mem_append.mp h with h | h <;> obtain ⟨r, -, rfl⟩ := List.mem_map.mp h <;> rfl

/-- The entry block of a constructible function defines no name twice. -/
theorem entryBlock_defs_nodup {fn : Func R} (h : fn.Constructible) :
    fn.entryBlock.defs.Nodup := by
  rw [entryBlock_defs]
  refine List.Nodup.append (List.Nodup.map Name.arg_injective h.params)
    (List.Nodup.map Name.init_injective fn.initRegs_nodup) ?_
  rw [List.disjoint_left]
  rintro x hx hx'
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hx'
  exact absurd hb (by simp)

/-- Every register the entry block's jump reads is a parameter of the entry
block or a result of one of its initialising operations. -/
theorem entryBlock_term_uses {fn : Func R} {x : Name R} (h : x ∈ fn.entryBlock.term.uses) :
    x ∈ fn.entryBlock.params ∨ ∃ o ∈ fn.entryBlock.ops, x ∈ o.defs := by
  have hterm : fn.entryBlock.term.uses =
      fn.regs.map fun r => if r ∈ fn.params then Name.arg r else Name.init r := rfl
  rw [hterm] at h
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  by_cases hp : r ∈ fn.params
  · exact .inl (by rw [ite_eq_left hp]; exact List.mem_map_of_mem hp)
  · refine .inr ⟨SSA.Op.const (Name.init r) 0, ?_, by rw [ite_eq_right hp]; simp [SSA.Op.defs]⟩
    exact List.mem_map_of_mem (fn.mem_initRegs hr hp)

/-- A pair of a list zipped with its indices has its first component in the
list. -/
theorem mem_of_mem_zipIdx {α : Type} {l : List α} {a : α} {n : Nat} (h : (a, n) ∈ l.zipIdx) :
    a ∈ l := by
  have := List.mem_map_of_mem (f := Prod.fst) h
  rwa [List.zipIdx_map_fst] at this

/-- Definitions tagged by position are globally distinct: if each element of
`l` contributes at index `n` a duplicate-free list of items all tagged `n`, the
concatenation over `l.zipIdx` is duplicate-free, and every item it contains is
tagged at least `k`. This is the shape of the output's definition list. -/
theorem nodup_flatMap_zipIdx {α β : Type} {f : α → Nat → List β} {tag : β → Option Nat}
    (htag : ∀ a n, ∀ b ∈ f a n, tag b = some n) :
    ∀ (l : List α), (∀ a ∈ l, ∀ n, (f a n).Nodup) → ∀ k : Nat,
      ((l.zipIdx k).flatMap fun p => f p.1 p.2).Nodup ∧
        ∀ b ∈ (l.zipIdx k).flatMap fun p => f p.1 p.2, ∃ m, k ≤ m ∧ tag b = some m
  | [], _, _ => ⟨by simp, by simp⟩
  | a :: l, hnd, k => by
    rw [List.zipIdx_cons, List.flatMap_cons]
    obtain ⟨ih1, ih2⟩ :=
      nodup_flatMap_zipIdx htag l (fun x hx => hnd x (by simp [hx])) (k + 1)
    refine ⟨List.Nodup.append (hnd a (by simp) k) ih1 ?_, ?_⟩
    · rw [List.disjoint_left]
      intro x hx hx'
      obtain ⟨m, hm, htm⟩ := ih2 x hx'
      rw [htag a k x hx] at htm
      exact absurd (Option.some.inj htm) (by omega)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨k, Nat.le_refl k, htag a k x hx⟩
      · obtain ⟨m, hm, htm⟩ := ih2 x hx
        exact ⟨m, Nat.le_of_succ_le hm, htm⟩

/-- A name of the output is available at any point of its own block when it is
a parameter of that block. -/
theorem okUse_of_mem_params {fn : Func R} {l : SSA.Label} {b : SSA.Block (Name R)}
    {x : Name R} (hb : (construct fn).block? l = some b) (hx : x ∈ b.params) (j : Nat) :
    (construct fn).okUse l j x = true := by
  rw [SSA.Func.okUse, hb]
  simp [hx]

/-- A name of the output is available at its block's terminator when one of the
block's operations defines it. -/
theorem okUse_of_mem_defs {fn : Func R} {l : SSA.Label} {b : SSA.Block (Name R)}
    {x : Name R} {o : SSA.Op (Name R)} (hb : (construct fn).block? l = some b)
    (ho : o ∈ b.ops) (hx : x ∈ o.defs) : (construct fn).okUse l b.ops.length x = true := by
  rw [SSA.Func.okUse, hb]
  simp only [Bool.or_eq_true, List.take_length]
  exact .inl (.inr (List.any_eq_true.mpr ⟨o, ho, by simpa using hx⟩))

/-! ## Well-formedness of the output -/

/-- The output agrees with its signature. The entry block exists because it is
the last of `fn.code.length + 1` blocks, its parameter count is the function's
because its parameters are the images of `fn.params`, every terminator target is
a successor of the corresponding instruction and so is a node of the code, and
every `ret` returns the values of the source `ret`. -/
theorem construct_wellFormedSig {fn : Func R} (h : fn.WellFormedSig) :
    (construct fn).WellFormedSig := by
  obtain ⟨hparams, hentry, hcode⟩ := h
  rw [List.all_eq_true] at hcode
  refine ⟨by simp [Func.entryLabel], ?_, ?_⟩
  · rw [construct_entry, construct_block?_entryLabel]
    simpa [Func.entryBlock] using hparams
  · rw [List.all_eq_true]
    intro b hb
    rw [construct_sig, construct_blocks_length, construct_blocks] at *
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨⟨i, m⟩, hm, rfl⟩ := List.mem_map.mp hb
      exact Instr.toTerm_okIn (hcode i (mem_of_mem_zipIdx hm))
    · rw [List.mem_singleton] at hb
      subst hb
      have hle : fn.entry ≤ fn.code.length := Nat.le_of_lt hentry
      simp [SSA.Term.okIn, Func.entryBlock, SSA.Term.successors, hle]

/-- The output is in single assignment form. Across blocks the node index of
`Name.param` and `Name.result` separates the definitions; within the block for
node `n` the parameters are `fn.regs`, which is duplicate-free by construction,
and the operation's results are the duplicate-free `i.defs` under a different
constructor; and the entry block defines `fn.params` under `Name.arg` and
`fn.initRegs` under `Name.init`. -/
theorem construct_singleAssignment {fn : Func R} (h : fn.Constructible) :
    (construct fn).SingleAssignment := by
  have key := nodup_flatMap_zipIdx (f := fun i m => (i.toBlock fn m).defs) (tag := Name.node?)
    (fun _ _ _ hx => Instr.toBlock_defs_node? hx) fn.code
    (fun i hi _ => Instr.toBlock_defs_nodup (h.defs i hi)) 0
  rw [SSA.Func.SingleAssignment, SSA.Func.allDefs, construct_blocks, List.flatMap_append,
    List.flatMap_map]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.Nodup.append key.1 (entryBlock_defs_nodup h) ?_
  rw [List.disjoint_left]
  intro x hx hx'
  obtain ⟨m, -, hm⟩ := key.2 x hx
  rw [entryBlock_defs_node? hx'] at hm
  simp at hm

/-- Every use of the output is dominated by its definition, and no dominance
computation is needed to see it: a block of the output uses only its own
parameters and the results of its own single operation, which that operation
precedes. This is the property the maximal construction exists to make
trivial. -/
theorem construct_usesDominated (fn : Func R) : (construct fn).UsesDominated := by
  rw [SSA.Func.UsesDominated, SSA.Func.usesDominated, List.all_eq_true]
  intro l hl
  rw [List.mem_range, construct_blocks_length] at hl
  obtain ⟨b, hb, hops, hterm⟩ : ∃ b, (construct fn).block? l = some b ∧
      (∀ o ∈ b.ops, ∀ x ∈ o.uses, x ∈ b.params) ∧
      (∀ x ∈ b.term.uses, x ∈ b.params ∨ ∃ o ∈ b.ops, x ∈ o.defs) := by
    by_cases hlt : l < fn.code.length
    · exact ⟨_, construct_block?_of_instr? (i := fn.code[l]) (List.getElem?_eq_getElem hlt),
        fun o ho x hx => Instr.mem_toBlock_params_of_op_uses (List.getElem_mem hlt) ho hx,
        fun x hx => Instr.mem_toBlock_term_uses (List.getElem_mem hlt) hx⟩
    · have heq : l = fn.code.length :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp hl) (Nat.not_lt.mp hlt)
      subst heq
      refine ⟨_, construct_block?_entryLabel fn, fun o ho x hx => ?_,
        fun x hx => entryBlock_term_uses hx⟩
      have ho' : o ∈ fn.initRegs.map (fun r => SSA.Op.const (Name.init r) 0) := ho
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ho'
      simp [SSA.Op.uses] at hx
  rw [hb, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro j _
    cases ho : b.ops[j]? with
    | none => rfl
    | some o =>
      rw [List.all_eq_true]
      exact fun x hx => okUse_of_mem_params hb (hops o (List.mem_of_getElem? ho) x hx) j
  · rw [List.all_eq_true]
    intro x hx
    rcases hterm x hx with hx' | ⟨o, ho, hd⟩
    · exact okUse_of_mem_params hb hx' _
    · exact okUse_of_mem_defs hb ho hd

/-- Every jump of the output carries as many arguments as its target has
parameters: all jumps between node blocks pass `fn.regs`, which is also every
node block's parameter list, and the entry block's jump targets the block for
`fn.entry`, which exists because `fn.WellFormedSig` places the entry node in the
code. -/
theorem construct_argsMatch {fn : Func R} (h : fn.WellFormedSig) :
    (construct fn).ArgsMatch := by
  obtain ⟨-, hentry, hcode⟩ := h
  rw [List.all_eq_true] at hcode
  rw [SSA.Func.ArgsMatch, SSA.Func.argsMatch, List.all_eq_true]
  intro b hb
  rw [List.all_eq_true]
  intro ta hta
  have main : ta.1 < fn.code.length ∧ ta.2.length = fn.regs.length := by
    rw [construct_blocks] at hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨⟨i, m⟩, hm, rfl⟩ := List.mem_map.mp hb
      obtain ⟨hs, hlen⟩ := Instr.mem_toTerm_args (ta := ta) hta
      exact ⟨Instr.lt_of_mem_successors (hcode i (mem_of_mem_zipIdx hm)) hs, hlen⟩
    · rw [List.mem_singleton] at hb
      subst hb
      have hta' : ta ∈ [((fn.entry : SSA.Label),
          fn.regs.map fun r => if r ∈ fn.params then Name.arg r else Name.init r)] := hta
      rw [List.mem_singleton] at hta'
      subst hta'
      exact ⟨hentry, List.length_map ..⟩
  obtain ⟨tb, htb, hp⟩ := construct_block?_params_length main.1
  rw [htb]
  simp [hp, main.2]

/-- **The construction produces a well-formed SSA function**, from a function
that agrees with its signature and satisfies the construction's side
conditions. -/
theorem construct_wellFormed {fn : Func R} (hsig : fn.WellFormedSig)
    (hc : fn.Constructible) : (construct fn).WellFormed where
  sig := construct_wellFormedSig hsig
  singleAssignment := construct_singleAssignment hc
  usesDominated := construct_usesDominated fn
  argsMatch := construct_argsMatch hsig

/-- **The construction produces a well-formed SSA program.** -/
theorem constructProg_wellFormed {p : Prog R} (hsig : p.WellFormedSig)
    (hc : p.Constructible) : (constructProg p).WellFormed := by
  rintro fn' hfn'
  simp only [constructProg, List.mem_map] at hfn'
  obtain ⟨fn, hfn, rfl⟩ := hfn'
  exact construct_wellFormed (hsig fn hfn) (hc fn hfn)

/-! ## Semantic correspondence

The relation below is one-sided, and deliberately so. An `RTL` frame leaves
every register it has not written at `none`, while the constructed function has
written zero into each of them before the first node runs, so the two frames can
never be equal. What is true is that the SSA frame *extends* the RTL one, under
the names of the block the state currently sits in, and that it is defined on
every register of the function whether or not the RTL frame is. The second half
is what makes the relation an invariant: every jump of the output passes every
register, so a frame that was merely an extension would not survive an edge. -/

/-- One activation of the two machines corresponds: the SSA point is at the
start of the block for the RTL node of the same function, and the SSA frame
holds, under the current block's `Name.param`, a value for *every* register of
the function, which is the value the RTL frame holds wherever the RTL frame
holds one. Registers the RTL frame has not written are written in the SSA frame
all the same — that is where the maximal construction's zeros live — and only
their values are unconstrained.

The totality conjunct is a strengthening of the sketch's relation and is not
optional: a jump of the output passes every register of the function, so the
target run would be stuck reading an argument the source had never written if
the relation did not record that the output has one. It is an invariant because
the fresh entry block writes every register and every jump passes every
register. -/
def AgreesAt (p : Prog R) (pt : Point) (fr : Frame R) (pt' : SSA.Point)
    (fr' : Frame (Name R)) : Prop :=
  pt'.func = pt.func ∧ pt'.label = pt.node ∧ pt'.index = 0 ∧
    ∀ fn, p.func? pt.func = some fn → ∀ r ∈ fn.regs,
      (fr'.get (.param pt.node r)).isSome ∧
        ∀ w : Word, fr.get r = some w → fr'.get (.param pt.node r) = some w

/-- An `RTL` state and a state of the constructed program correspond: the
current activations correspond, the suspended activations correspond in order,
and the memories are equal. A suspended SSA activation sits at index `0` of its
block, which is the `call` op, matching the `RTL` activation at the `call`
node. -/
def Agrees (p : Prog R) (s : State R) (s' : SSA.State (Name R)) : Prop :=
  AgreesAt p s.point s.frame s'.point s'.frame ∧
    List.Forall₂ (fun a a' => AgreesAt p a.point a.frame a'.point a'.frame) s.stack s'.stack ∧
    s.mem = s'.mem

/-- The SSA behaviour an `RTL` behaviour corresponds to. The two `Behavior`
types have the same constructors; this is the renaming between them. -/
def Behavior.toSSA : Behavior → SSA.Behavior
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck
  | .diverges => .diverges

/-! ### Looking the output's code up

The output's function table, block table and point fetching are all the source
tables renamed, so each of the following reduces a lookup in the output to a
lookup in the source. -/

/-- The output's function table is the source's, function by function. -/
theorem constructProg_func? (p : Prog R) (f : FuncId) :
    (constructProg p).func? f = (p.func? f).map construct := by
  simp [constructProg, SSA.Prog.func?, Prog.func?, List.getElem?_map]

/-- The block for an existing node of an existing function is the block that
node's instruction induces. -/
theorem constructProg_block?_of_instr? {p : Prog R} {f : FuncId} {fn : Func R} {n : Node}
    {i : Instr R} (hfn : p.func? f = some fn) (hi : fn.instr? n = some i) :
    (constructProg p).block? f n = some (i.toBlock fn n) := by
  simp [SSA.Prog.block?, constructProg_func?, hfn, construct_block?_of_instr? hi]

/-- The entry block of an existing function of the output is the fresh one. -/
theorem constructProg_block?_entryLabel {p : Prog R} {f : FuncId} {fn : Func R}
    (hfn : p.func? f = some fn) :
    (constructProg p).block? f fn.entryLabel = some fn.entryBlock := by
  simp [SSA.Prog.block?, constructProg_func?, hfn, construct_block?_entryLabel]

/-- At index `0` of the block for a node whose instruction computes, the output
fetches that computation. -/
theorem fetch_op_of_instr? {p : Prog R} {f : FuncId} {fn : Func R} {n : Node} {i : Instr R}
    {o : SSA.Op (Name R)} (hfn : p.func? f = some fn) (hi : fn.instr? n = some i)
    (hops : i.toOps n = [o]) : (constructProg p).fetch ⟨f, n, 0⟩ = some (.op o) := by
  rw [SSA.Prog.fetch, constructProg_block?_of_instr? hfn hi]
  simp [show (i.toBlock fn n).ops = i.toOps n from rfl, hops]

/-- One past the last operation of the block for a node, the output fetches
that node's terminator. -/
theorem fetch_term_of_instr? {p : Prog R} {f : FuncId} {fn : Func R} {n : Node} {i : Instr R}
    (hfn : p.func? f = some fn) (hi : fn.instr? n = some i) :
    (constructProg p).fetch ⟨f, n, (i.toOps n).length⟩ = some (.term (i.toTerm fn n)) := by
  rw [SSA.Prog.fetch, constructProg_block?_of_instr? hfn hi]
  simp [show (i.toBlock fn n).ops = i.toOps n from rfl,
    show (i.toBlock fn n).term = i.toTerm fn n from rfl]

omit [DecidableEq R] in
/-- A function of the source that the program's point names exists, and so does
the instruction at the point. -/
theorem fetch_elim {p : Prog R} {pt : Point} {i : Instr R} (h : p.fetch pt = some i) :
    ∃ fn, p.func? pt.func = some fn ∧ fn.instr? pt.node = some i ∧ i ∈ fn.code := by
  rw [Prog.fetch, Prog.instr?] at h
  cases hfn : p.func? pt.func with
  | none => rw [hfn] at h; simp at h
  | some fn =>
    rw [hfn] at h
    simp only [Option.bind_some] at h
    exact ⟨fn, rfl, h, List.mem_of_getElem? h⟩

omit [DecidableEq R] in
/-- A successor of an instruction of a function that agrees with its signature
is a node of that function. -/
theorem lt_of_succ {p : Prog R} {fn : Func R} {f : FuncId} {n t : Node} {i : Instr R}
    (hsig : p.WellFormedSig) (hfn : p.func? f = some fn) (hi : fn.instr? n = some i)
    (ht : t ∈ i.successors) : t < fn.code.length :=
  Instr.lt_of_mem_successors
    (List.all_eq_true.mp (hsig fn (List.mem_of_getElem? hfn)).2.2 i (List.mem_of_getElem? hi)) ht

/-- The name under which the block for node `n` holds a register the node does
not write is the block parameter. -/
theorem Instr.nameAt_of_not_mem {n : Node} {i : Instr R} {r : R} (h : r ∉ i.defs) :
    i.nameAt n r = .param n r := ite_eq_right h

/-- The name under which the block for node `n` holds a register the node
writes is the operation's result. -/
theorem Instr.nameAt_of_mem {n : Node} {i : Instr R} {r : R} (h : r ∈ i.defs) :
    i.nameAt n r = .result n r := ite_eq_left h

/-- A block's jump terminator steps by transferring. -/
theorem step_jump {S : Type} [DecidableEq S] {p : SSA.Prog S} {s : SSA.State S} {t : SSA.Label}
    {as : List S} (hf : p.fetch s.point = some (.term (.jump t as))) :
    SSA.step p s = SSA.transfer p s t as := by simp [SSA.step, hf]

/-- A block's conditional terminator steps by transferring along the edge the
condition selects. -/
theorem step_cond {S : Type} [DecidableEq S] {p : SSA.Prog S} {s : SSA.State S} {c : S}
    {t₁ t₂ : SSA.Label} {a₁ a₂ : List S} {x : Word}
    (hf : p.fetch s.point = some (.term (.cond c t₁ a₁ t₂ a₂))) (hc : s.frame.get c = some x) :
    SSA.step p s = SSA.transfer p s (if x = 0 then t₂ else t₁) (if x = 0 then a₂ else a₁) := by
  simp [SSA.step, hf, hc]

/-! ### Matching one source step

A source node becomes at most one operation followed by one terminator, so a
step of the source is matched by establishing what the block holds between the
two (`mid_keep` and `mid_set`) and then crossing the edge (`transfer_regs`). -/

/-- What the block for node `n` holds for the function's registers once the
node's instruction has run, when the instruction writes nothing: the block
parameters, unchanged. -/
theorem mid_keep {fn : Func R} {n : Node} {i : Instr R} {fr : Frame R} {sr : Frame (Name R)}
    (hdefs : i.defs = []) (hA : ∀ r ∈ fn.regs, (sr.get (.param n r)).isSome ∧
      ∀ w : Word, fr.get r = some w → sr.get (.param n r) = some w) :
    ∀ r ∈ fn.regs, (sr.get (i.nameAt n r)).isSome ∧
      ∀ w : Word, fr.get r = some w → sr.get (i.nameAt n r) = some w := by
  intro r hr
  rw [Instr.nameAt_of_not_mem (by rw [hdefs]; simp)]
  exact hA r hr

/-- What the block for node `n` holds for the function's registers once the
node's instruction has run, when the instruction writes the single register
`d`: the operation's result for `d` and the block parameters elsewhere. -/
theorem mid_set {fn : Func R} {n : Node} {i : Instr R} {d : R} {v : Word} {fr : Frame R}
    {sr : Frame (Name R)} (hdefs : i.defs = [d])
    (hA : ∀ r ∈ fn.regs, (sr.get (.param n r)).isSome ∧
      ∀ w : Word, fr.get r = some w → sr.get (.param n r) = some w) :
    ∀ r ∈ fn.regs, ((sr.set (.result n d) v).get (i.nameAt n r)).isSome ∧
      ∀ w : Word, (fr.set d v).get r = some w →
        (sr.set (.result n d) v).get (i.nameAt n r) = some w := by
  intro r hr
  by_cases hrd : r = d
  · subst hrd
    rw [Instr.nameAt_of_mem (by rw [hdefs]; simp)]
    simp [Frame.get_set]
  · rw [Instr.nameAt_of_not_mem (by rw [hdefs]; simpa using hrd), Frame.get_set,
      ite_eq_right (by simp)]
    refine ⟨(hA r hr).1, fun w hw => (hA r hr).2 w ?_⟩
    rwa [Frame.get_set, ite_eq_right hrd] at hw

/-- The transfer a terminator of the output performs along the edge to node
`t`, when its argument list names, for each register of the function, a name
`g r` the frame holds. Afterwards the target block's parameter for each register
holds what `g r` held, so the correspondence crosses the edge. `hsep` is what
stops a parameter written early in the transfer from clobbering an argument read
later, and holds in the construction because `g r` is a result name, an entry
name, or the parameter name of `r` itself. -/
theorem transfer_regs {p : Prog R} {f : FuncId} {fn : Func R} {t : Node} {g : R → Name R}
    {sr : Frame (Name R)} {stack : List (SSA.Activation (Name R))} {mem : Memory}
    {pt : SSA.Point} {fr' : Frame R} (hfn : p.func? f = some fn) (hpt : pt.func = f)
    (ht : t < fn.code.length) (hsep : ∀ r r' : R, r ≠ r' → g r ≠ Name.param t r')
    (hmid : ∀ r ∈ fn.regs, (sr.get (g r)).isSome ∧
      ∀ w : Word, fr'.get r = some w → sr.get (g r) = some w) :
    ∃ sr₂, SSA.transfer (constructProg p) ⟨pt, sr, stack, mem⟩ t (fn.regs.map g) =
        .running ⟨⟨f, t, 0⟩, sr₂, stack, mem⟩ ∧
      ∀ r ∈ fn.regs, (sr₂.get (.param t r)).isSome ∧
        ∀ w : Word, fr'.get r = some w → sr₂.get (.param t r) = some w := by
  obtain ⟨vals, hvals, hlen⟩ :=
    readAll_isSome (fr := sr) (rs := fn.regs.map g)
      (by rintro x hx; obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx; exact (hmid r hr).1)
  have hb : (constructProg p).block? f t = some ((fn.code[t]'ht).toBlock fn t) :=
    constructProg_block?_of_instr? hfn (List.getElem?_eq_getElem ht)
  have hplen : ((fn.code[t]'ht).toBlock fn t).params.length = vals.length := by
    simp [Instr.toBlock, hlen]
  obtain ⟨sr₂, hsr₂⟩ :=
    Option.isSome_iff_exists.mp
      ((writeAll_isSome_iff (fr := sr) (rs := _) (vals := vals)).mpr hplen)
  have hkey : ∀ r ∈ fn.regs, sr₂.get (.param t r) = sr.get (g r) :=
    writeAll_readAll_map (Name.param_injective t) hsep fn.regs_nodup hvals hsr₂
  refine ⟨sr₂, ?_, fun r hr => ?_⟩
  · simp only [SSA.transfer, hvals, hpt, hb, hsr₂]
  · rw [hkey r hr]
    exact hmid r hr

/-- The names the block for node `n` passes along an edge are separated from the
target's parameters, which is the side condition `transfer_regs` asks for. -/
theorem nameAt_sep {n t : Node} {i : Instr R} (r r' : R) (hne : r ≠ r') :
    i.nameAt n r ≠ Name.param t r' := by
  rw [Instr.nameAt]
  split <;> simp [hne]

/-- Reading a renamed list of registers from a frame that agrees with another
under the renaming yields the same values. -/
theorem readAll_map_agree {S T : Type} [DecidableEq S] [DecidableEq T] {g : S → T}
    {fr : Frame S} {sr : Frame T} :
    ∀ {rs : List S} {vals : List Word},
      (∀ r ∈ rs, ∀ w : Word, fr.get r = some w → sr.get (g r) = some w) →
      fr.readAll rs = some vals → sr.readAll (rs.map g) = some vals := by
  intro rs
  induction rs with
  | nil =>
    intro vals _ h
    rw [show fr.readAll [] = some [] from rfl] at h
    cases h
    rfl
  | cons r rs ih =>
    intro vals hagr h
    rw [readAll_cons] at h
    cases hv : fr.get r with
    | none => rw [hv] at h; simp at h
    | some v =>
      rw [hv] at h
      simp only [Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      rw [List.map_cons, readAll_cons, hagr r (by simp) v hv,
        ih (fun x hx => hagr x (by simp [hx])) hvs]
      rfl

/-- Running the initialising operations of the fresh entry block. They are all
`const`s, so the block runs straight through to its terminator, defining zero
for every register it names and leaving every other register alone. -/
theorem steps_init {p : SSA.Prog (Name R)} {f : FuncId} {l : SSA.Label} {b : SSA.Block (Name R)}
    {stack : List (SSA.Activation (Name R))} {mem : Memory} (hb : p.block? f l = some b) :
    ∀ (rs : List R) (j : Nat) (fr : Frame (Name R)),
      b.ops.drop j = rs.map (fun r => SSA.Op.const (Name.init r) 0) → j ≤ b.ops.length →
      ∃ fr', SSA.Steps p ⟨⟨f, l, j⟩, fr, stack, mem⟩ ⟨⟨f, l, b.ops.length⟩, fr', stack, mem⟩ ∧
        (∀ r ∈ rs, fr'.get (Name.init r) = some 0) ∧
        (∀ x, (∀ r ∈ rs, x ≠ Name.init r) → fr'.get x = fr.get x)
  | [], j, fr, hdrop, hj => by
    have hle : b.ops.length ≤ j := List.drop_eq_nil_iff.mp (by simpa using hdrop)
    have hjeq : j = b.ops.length := Nat.le_antisymm hj hle
    subst hjeq
    exact ⟨fr, .refl, by simp, fun _ _ => rfl⟩
  | r :: rs, j, fr, hdrop, hj => by
    have hget : b.ops[j]? = some (SSA.Op.const (Name.init r) 0) := by
      have h0 : (b.ops.drop j)[0]? = b.ops[j]? := by rw [List.getElem?_drop]; simp
      rw [hdrop] at h0
      simpa using h0.symm
    have hfetch : p.fetch ⟨f, l, j⟩ = some (.op (.const (Name.init r) 0)) := by
      rw [SSA.Prog.fetch, hb]
      simp [hget]
    have hstep : SSA.Step p ⟨⟨f, l, j⟩, fr, stack, mem⟩
        ⟨⟨f, l, j + 1⟩, fr.set (Name.init r) 0, stack, mem⟩ :=
      (SSA.Transition.op (p := p) (s := ⟨⟨f, l, j⟩, fr, stack, mem⟩) hfetch rfl).step_eq
    have hjlt : j < b.ops.length := by
      by_contra hcon
      rw [List.drop_eq_nil_iff.mpr (Nat.le_of_not_lt hcon)] at hdrop
      simp at hdrop
    have hdrop' : b.ops.drop (j + 1) = rs.map (fun r => SSA.Op.const (Name.init r) 0) := by
      have hdd : b.ops.drop (j + 1) = (b.ops.drop j).drop 1 := by rw [List.drop_drop]
      rw [hdd, hdrop]
      rfl
    obtain ⟨fr', hsteps, h1, h2⟩ := steps_init hb rs (j + 1) (fr.set (Name.init r) 0) hdrop' hjlt
    refine ⟨fr', Relation.ReflTransGen.head hstep hsteps, ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_cons.mp hr' with rfl | hr'
      · by_cases hin : r' ∈ rs
        · exact h1 r' hin
        · rw [h2 (Name.init r') fun y hy hcon => hin (by rw [Name.init_injective hcon]; exact hy)]
          simp [Frame.get_set]
      · exact h1 r' hr'
    · intro x hx
      rw [h2 x fun y hy => hx y (by simp [hy]), Frame.get_set,
        ite_eq_right fun hcon => hx r (by simp) hcon]

/-- **Entering a function corresponds.** The output's fresh entry block binds
the arguments under `Name.arg`, writes zero into every other register under
`Name.init` and jumps to the block for the source entry node; after those steps
the two machines stand at the same node with corresponding frames. This is what
`construct_start_steps` needs for a whole-program start and what `construct_step`
needs for a `call`. -/
theorem enter_steps {p : Prog R} {f : FuncId} {fn : Func R} {vals : List Word} {pt : Point}
    {fr : Frame R} {stack : List (SSA.Activation (Name R))} {mem : Memory}
    (hsig : p.WellFormedSig) (hfn : p.func? f = some fn) (he : p.enter f vals = some (pt, fr)) :
    ∃ sfr sr, (constructProg p).enter f vals = some (⟨f, fn.entryLabel, 0⟩, sfr) ∧
      pt = ⟨f, fn.entry⟩ ∧
      SSA.Steps (constructProg p) ⟨⟨f, fn.entryLabel, 0⟩, sfr, stack, mem⟩
        ⟨⟨f, fn.entry, 0⟩, sr, stack, mem⟩ ∧
      ∀ r ∈ fn.regs, (sr.get (.param fn.entry r)).isSome ∧
        ∀ w : Word, fr.get r = some w → sr.get (.param fn.entry r) = some w := by
  rw [Prog.enter, hfn] at he
  simp only [Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at he
  obtain ⟨fr₀, hw, hpt, hfr⟩ := he
  subst hfr
  have hsigfn : fn.WellFormedSig := hsig fn (List.mem_of_getElem? hfn)
  have hfunc : (constructProg p).func? f = some (construct fn) := by
    rw [constructProg_func?, hfn]; rfl
  have hlen : (fn.params.map Name.arg).length = vals.length := by
    rw [List.length_map]
    exact writeAll_isSome_iff.mp (by rw [hw]; rfl)
  obtain ⟨sfr, hsw⟩ := Option.isSome_iff_exists.mp
    ((writeAll_isSome_iff (fr := (Frame.empty : Frame (Name R)))
      (rs := fn.params.map Name.arg) (vals := vals)).mpr hlen)
  have hse : (constructProg p).enter f vals = some (⟨f, fn.entryLabel, 0⟩, sfr) := by
    rw [SSA.Prog.enter, hfunc]
    simp only [Option.bind_some, construct_entry, construct_block?_entryLabel,
      show fn.entryBlock.params = fn.params.map Name.arg from rfl, hsw, Option.map_some]
  have hbase : ∀ r : R, ∀ w : Word, fr₀.get r = some w → sfr.get (.arg r) = some w :=
    writeAll_agree Name.arg_injective hw hsw
      (fun r w h => absurd h (by simp [Frame.empty, Frame.get]))
  have hargSome : ∀ r ∈ fn.params, (sfr.get (Name.arg r)).isSome :=
    fun r hr => writeAll_isSome_of_mem hsw (List.mem_map_of_mem hr)
  have hnotparam : ∀ r : R, r ∉ fn.params → fr₀.get r = none := by
    intro r hr
    rw [writeAll_get_of_not_mem hw hr]
    rfl
  obtain ⟨sr₀, hsteps, hinit, hkeep⟩ :=
    steps_init (p := constructProg p) (stack := stack) (mem := mem)
      (constructProg_block?_entryLabel hfn) fn.initRegs 0 sfr rfl (Nat.zero_le _)
  have hname : ∀ r ∈ fn.regs, (sr₀.get (if r ∈ fn.params then Name.arg r else Name.init r)).isSome ∧
      ∀ w : Word, fr₀.get r = some w →
        sr₀.get (if r ∈ fn.params then Name.arg r else Name.init r) = some w := by
    intro r hr
    by_cases hp : r ∈ fn.params
    · rw [ite_eq_left hp, hkeep (Name.arg r) (by simp)]
      exact ⟨hargSome r hp, fun w hw' => hbase r w hw'⟩
    · rw [ite_eq_right hp, hinit r (fn.mem_initRegs hr hp)]
      exact ⟨rfl, fun w hw' => absurd hw' (by rw [hnotparam r hp]; simp)⟩
  obtain ⟨sr, htr, hmid⟩ :=
    transfer_regs (p := p) (g := fun r => if r ∈ fn.params then Name.arg r else Name.init r)
      (pt := ⟨f, fn.entryLabel, fn.entryBlock.ops.length⟩) (stack := stack) (mem := mem)
      hfn rfl hsigfn.2.1 (fun r r' _ => by split <;> simp) hname
  have hfetch : (constructProg p).fetch ⟨f, fn.entryLabel, fn.entryBlock.ops.length⟩ =
      some (.term fn.entryBlock.term) := by
    rw [SSA.Prog.fetch, constructProg_block?_entryLabel hfn]
    simp
  refine ⟨sfr, sr, hse, hpt.symm, ?_, hmid⟩
  refine hsteps.tail ?_
  show SSA.step (constructProg p) _ = _
  rw [step_jump (s := ⟨⟨f, fn.entryLabel, fn.entryBlock.ops.length⟩, sr₀, stack, mem⟩) hfetch]
  exact htr

/-- The correspondence at a node, assembled from its three components. -/
theorem agrees_mk {p : Prog R} {f : FuncId} {fn : Func R} {nd : Node} {fr : Frame R}
    {sr : Frame (Name R)} {stk : List (Activation R)} {sstk : List (SSA.Activation (Name R))}
    {mem : Memory} (hfn : p.func? f = some fn)
    (h : ∀ r ∈ fn.regs, (sr.get (.param nd r)).isSome ∧
      ∀ w : Word, fr.get r = some w → sr.get (.param nd r) = some w)
    (hstk : List.Forall₂ (fun a a' => AgreesAt p a.point a.frame a'.point a'.frame) stk sstk) :
    Agrees p ⟨⟨f, nd⟩, fr, stk, mem⟩ ⟨⟨f, nd, 0⟩, sr, sstk, mem⟩ := by
  refine ⟨⟨rfl, rfl, rfl, fun fn' hfn' => ?_⟩, hstk, rfl⟩
  rw [hfn] at hfn'
  cases hfn'
  exact h

/-- A call that enters names an existing function. -/
theorem func?_of_enter {p : Prog R} {f : FuncId} {vals : List Word} {q : Point × Frame R}
    (h : p.enter f vals = some q) : ∃ fn, p.func? f = some fn := by
  rw [Prog.enter] at h
  cases hfn : p.func? f with
  | none => rw [hfn] at h; simp at h
  | some fn => exact ⟨fn, rfl⟩

/-- The terminator step of the block for node `nd` along the edge to `t`, for
any terminator that transfers there with the node's `jumpArgs`. -/
theorem term_jump_steps {p : Prog R} {f : FuncId} {fn : Func R} {nd t : Node} {i : Instr R}
    {sr : Frame (Name R)} {stack : List (SSA.Activation (Name R))} {mem : Memory} {j : Nat}
    {fr₁ : Frame R} (hfn : p.func? f = some fn) (ht : t < fn.code.length)
    (hstep : ∀ st : SSA.State (Name R),
      SSA.transfer (constructProg p) ⟨⟨f, nd, j⟩, sr, stack, mem⟩ t (i.jumpArgs fn nd) =
        .running st → SSA.Step (constructProg p) ⟨⟨f, nd, j⟩, sr, stack, mem⟩ st)
    (hmid : ∀ r ∈ fn.regs, (sr.get (i.nameAt nd r)).isSome ∧
      ∀ w : Word, fr₁.get r = some w → sr.get (i.nameAt nd r) = some w) :
    ∃ sr₂, SSA.Step (constructProg p) ⟨⟨f, nd, j⟩, sr, stack, mem⟩
        ⟨⟨f, t, 0⟩, sr₂, stack, mem⟩ ∧
      ∀ r ∈ fn.regs, (sr₂.get (.param t r)).isSome ∧
        ∀ w : Word, fr₁.get r = some w → sr₂.get (.param t r) = some w := by
  obtain ⟨sr₂, htr, hmid₂⟩ :=
    transfer_regs (g := i.nameAt nd) (pt := ⟨f, nd, j⟩) (stack := stack) (mem := mem)
      hfn rfl ht nameAt_sep hmid
  exact ⟨sr₂, hstep _ htr, hmid₂⟩

/-- One source node that computes and jumps becomes two steps of the output: the
block's single operation and the block's jump. -/
theorem op_jump_steps {p : Prog R} {f : FuncId} {fn : Func R} {nd t : Node} {i : Instr R}
    {o : SSA.Op (Name R)} {sr sr₁ : Frame (Name R)} {stack : List (SSA.Activation (Name R))}
    {mem mem₁ : Memory} {fr₁ : Frame R}
    (hfn : p.func? f = some fn) (hi : fn.instr? nd = some i) (hops : i.toOps nd = [o])
    (hterm : i.toTerm fn nd = .jump t (i.jumpArgs fn nd)) (ht : t < fn.code.length)
    (hexec : o.exec sr mem = some (sr₁, mem₁))
    (hmid : ∀ r ∈ fn.regs, (sr₁.get (i.nameAt nd r)).isSome ∧
      ∀ w : Word, fr₁.get r = some w → sr₁.get (i.nameAt nd r) = some w) :
    ∃ sr₂, Relation.TransGen (SSA.Step (constructProg p))
        ⟨⟨f, nd, 0⟩, sr, stack, mem⟩ ⟨⟨f, t, 0⟩, sr₂, stack, mem₁⟩ ∧
      ∀ r ∈ fn.regs, (sr₂.get (.param t r)).isSome ∧
        ∀ w : Word, fr₁.get r = some w → sr₂.get (.param t r) = some w := by
  have hstep1 : SSA.Step (constructProg p) ⟨⟨f, nd, 0⟩, sr, stack, mem⟩
      ⟨⟨f, nd, 1⟩, sr₁, stack, mem₁⟩ :=
    (SSA.Transition.op (p := constructProg p) (s := ⟨⟨f, nd, 0⟩, sr, stack, mem⟩)
      (fetch_op_of_instr? hfn hi hops) hexec).step_eq
  have hfetch : (constructProg p).fetch ⟨f, nd, 1⟩ =
      some (.term (.jump t (i.jumpArgs fn nd))) := by
    have hft := fetch_term_of_instr? hfn hi
    rw [hops] at hft
    simpa [hterm] using hft
  obtain ⟨sr₂, hstep2, hmid₂⟩ :=
    term_jump_steps (i := i) (j := 1) (fr₁ := fr₁) hfn ht
      (fun st h => by
        show SSA.step (constructProg p) _ = _
        rw [step_jump (s := ⟨⟨f, nd, 1⟩, sr₁, stack, mem₁⟩) hfetch]
        exact h) hmid
  exact ⟨sr₂, Relation.TransGen.head hstep1 (Relation.TransGen.single hstep2), hmid₂⟩

/-- The start states correspond after a prefix of SSA steps, not on the nose:
the constructed program starts in the fresh entry block, and has to bind the
parameters, write zero into every other register and jump to the block for
`fn.entry` before it stands where the `RTL` start state stands. The statement
also records that the constructed start state exists whenever the source one
does, since the entry block's parameters have the length of `fn.params`. -/
theorem construct_start_steps {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State R} (hsig : p.WellFormedSig) (hstart : p.start f args mem = some s) :
    ∃ s₀ s', (constructProg p).start f args mem = some s₀ ∧
      SSA.Steps (constructProg p) s₀ s' ∧ Agrees p s s' := by
  rw [Prog.start] at hstart
  simp only [Option.map_eq_some_iff] at hstart
  obtain ⟨⟨pt, fr⟩, he, rfl⟩ := hstart
  obtain ⟨fn, hfn⟩ := func?_of_enter he
  obtain ⟨sfr, sr, hse, hpt, hsteps, hmid⟩ := enter_steps (stack := []) (mem := mem) hsig hfn he
  refine ⟨⟨⟨f, fn.entryLabel, 0⟩, sfr, [], mem⟩, ⟨⟨f, fn.entry, 0⟩, sr, [], mem⟩, ?_, hsteps, ?_⟩
  · rw [SSA.Prog.start, hse]
    rfl
  · subst hpt
    exact agrees_mk hfn hmid List.Forall₂.nil

/-- **Forward simulation.** One step of `RTL` from a state the constructed
program agrees with is matched by one or more steps of the constructed program,
ending in a state that agrees with the `RTL` successor. It is one or more rather
than exactly one because a node that computes becomes an op and a jump, and
because a `call` additionally runs the callee's entry block. -/
theorem construct_step {p : Prog R} {s t : State R} {s' : SSA.State (Name R)}
    (hsig : p.WellFormedSig) (hc : p.Constructible) (ha : Agrees p s s')
    (hstep : Step p s t) :
    ∃ t', Relation.TransGen (SSA.Step (constructProg p)) s' t' ∧ Agrees p t t' := by
  obtain ⟨⟨hpf, hpl, hpi, hagr⟩, hstk, hmem⟩ := ha
  obtain ⟨⟨f, nd, pidx⟩, sr, sstack, smem⟩ := s'
  obtain ⟨⟨rf, rn⟩, fr, stk, mem⟩ := s
  dsimp only at hpf hpl hpi hagr hstk hmem
  subst hpf
  subst hpl
  subst hpi
  subst hmem
  have htr := Transition.of_step hstep (by simp)
  cases htr with
  | nop hf =>
    rename_i n'
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    have hfetch : (constructProg p).fetch ⟨f, nd, 0⟩ =
        some (.term (.jump n' ((Instr.nop n').jumpArgs fn nd))) := fetch_term_of_instr? hfn hi
    obtain ⟨sr₂, hstep2, hmid₂⟩ :=
      term_jump_steps (i := Instr.nop n') (j := 0) (fr₁ := fr) hfn ht
        (fun st h => by
          show SSA.step (constructProg p) _ = _
          rw [step_jump (s := ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩) hfetch]
          exact h) (mid_keep rfl hA)
    exact ⟨_, Relation.TransGen.single hstep2, agrees_mk hfn hmid₂ hstk⟩
  | jump hf =>
    rename_i n'
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    have hfetch : (constructProg p).fetch ⟨f, nd, 0⟩ =
        some (.term (.jump n' ((Instr.jump n').jumpArgs fn nd))) := fetch_term_of_instr? hfn hi
    obtain ⟨sr₂, hstep2, hmid₂⟩ :=
      term_jump_steps (i := Instr.jump n') (j := 0) (fr₁ := fr) hfn ht
        (fun st h => by
          show SSA.step (constructProg p) _ = _
          rw [step_jump (s := ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩) hfetch]
          exact h) (mid_keep rfl hA)
    exact ⟨_, Relation.TransGen.single hstep2, agrees_mk hfn hmid₂ hstk⟩
  | cond hf hcv =>
    rename_i c n₁ n₂ x
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hc' : sr.get (.param nd c) =  some x :=
      (hA c (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 x hcv
    have ht : (if x = 0 then n₂ else n₁) < fn.code.length := by
      refine lt_of_succ hsig hfn hi ?_
      show (if x = 0 then n₂ else n₁) ∈ [n₁, n₂]
      split <;> simp
    have hfetch : (constructProg p).fetch ⟨f, nd, 0⟩ =
        some (.term (.cond (.param nd c) n₁ ((Instr.cond c n₁ n₂).jumpArgs fn nd)
          n₂ ((Instr.cond c n₁ n₂).jumpArgs fn nd))) := fetch_term_of_instr? hfn hi
    obtain ⟨sr₂, hstep2, hmid₂⟩ :=
      term_jump_steps (i := Instr.cond c n₁ n₂) (j := 0) (fr₁ := fr) hfn ht
        (fun st h => by
          show SSA.step (constructProg p) _ = _
          rw [step_cond (s := ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩) hfetch hc', ite_self]
          exact h) (mid_keep rfl hA)
    exact ⟨_, Relation.TransGen.single hstep2, agrees_mk hfn hmid₂ hstk⟩
  | const hf =>
    rename_i d v n'
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr.set d v)
        (sr₁ := sr.set (.result nd d) v) (mem₁ := mem) hfn hi rfl rfl ht
        (by simp [SSA.Op.exec]) (mid_set rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | move hf hx =>
    rename_i d src n' x
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hsrc : sr.get (.param nd src) = some x :=
      (hA src (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 x hx
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr.set d x)
        (sr₁ := sr.set (.result nd d) x) (mem₁ := mem) hfn hi rfl rfl ht
        (by simp [SSA.Op.exec, hsrc]) (mid_set rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | unary hf hx =>
    rename_i op d src n' x
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hsrc : sr.get (.param nd src) = some x :=
      (hA src (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 x hx
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr.set d (op.eval x))
        (sr₁ := sr.set (.result nd d) (op.eval x)) (mem₁ := mem) hfn hi rfl rfl ht
        (by simp [SSA.Op.exec, hsrc]) (mid_set rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | binary hf hx hy hz =>
    rename_i op d a b n' x y z
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have ha' : sr.get (.param nd a) = some x :=
      (hA a (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 x hx
    have hb' : sr.get (.param nd b) = some y :=
      (hA b (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 y hy
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr.set d z)
        (sr₁ := sr.set (.result nd d) z) (mem₁ := mem) hfn hi rfl rfl ht
        (by simp [SSA.Op.exec, ha', hb', hz]) (mid_set rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | load hf hb hl =>
    rename_i w e d base off n' addr z
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hb' : sr.get (.param nd base) = some addr :=
      (hA base (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 addr hb
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr.set d z)
        (sr₁ := sr.set (.result nd d) z) (mem₁ := mem) hfn hi rfl rfl ht
        (by simp [SSA.Op.exec, hb', hl]) (mid_set rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | store hf hb hx hm =>
    rename_i w base off src n' addr x m'
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hb' : sr.get (.param nd base) = some addr :=
      (hA base (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 addr hb
    have hx' : sr.get (.param nd src) = some x :=
      (hA src (fn.mem_regs_of_mem_uses hcode (by simp [Instr.uses]))).2 x hx
    have ht : n' < fn.code.length := lt_of_succ hsig hfn hi (by simp [Instr.successors])
    obtain ⟨sr₂, hsteps, hmid₂⟩ :=
      op_jump_steps (sr := sr) (stack := sstack) (mem := mem) (fr₁ := fr) (sr₁ := sr) (mem₁ := m')
        hfn hi rfl rfl ht (by simp [SSA.Op.exec, hb', hx', hm]) (mid_keep rfl hA)
    exact ⟨_, hsteps, agrees_mk hfn hmid₂ hstk⟩
  | call hf hargs henter =>
    rename_i f' cargs cresults n' vals pt' fr'
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hread : sr.readAll (cargs.map (Name.param nd)) = some vals :=
      readAll_map_agree
        (fun r hr w hw =>
          (hA r (fn.mem_regs_of_mem_uses hcode (by simpa [Instr.uses] using hr))).2 w hw)
        hargs
    obtain ⟨fn', hfn'⟩ := func?_of_enter henter
    obtain ⟨sfr, sr₀, hse, hpt, hsteps, hmid⟩ :=
      enter_steps (stack := ⟨⟨f, nd, 0⟩, sr⟩ :: sstack) (mem := mem) hsig hfn' henter
    have hstep1 : SSA.Step (constructProg p) ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩
        ⟨⟨f', fn'.entryLabel, 0⟩, sfr, ⟨⟨f, nd, 0⟩, sr⟩ :: sstack, mem⟩ :=
      (SSA.Transition.call (p := constructProg p) (s := ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩)
        (fetch_op_of_instr? hfn hi rfl) hread hse).step_eq
    subst hpt
    exact ⟨_, Relation.TransGen.head' hstep1 hsteps,
      agrees_mk hfn' hmid (List.Forall₂.cons ⟨rfl, rfl, rfl, hagr⟩ hstk)⟩
  | ret hf hvals hstack hcall hwrite =>
    rename_i regs vals a rest f₂ cargs cresults n₂ fr₂
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hread : sr.readAll (regs.map (Name.param nd)) = some vals :=
      readAll_map_agree
        (fun r hr w hw =>
          (hA r (fn.mem_regs_of_mem_uses hcode (by simpa [Instr.uses] using hr))).2 w hw)
        hvals
    have hstk' : List.Forall₂ (fun a a' => AgreesAt p a.point a.frame a'.point a'.frame)
        (a :: rest) sstack := by rw [← hstack]; exact hstk
    cases hstk' with
    | cons hhead htail =>
      rename_i a' rest'
      obtain ⟨hpf2, hpl2, hpi2, hagr2⟩ := hhead
      have ha'pt : a'.point = ⟨a.point.func, a.point.node, 0⟩ := by
        rw [← hpf2, ← hpl2, ← hpi2]
      obtain ⟨fn₂, hfn₂, hi₂, hcode₂⟩ := fetch_elim hcall
      have hA2 := hagr2 fn₂ hfn₂
      have hnd : cresults.Nodup :=
        (hc fn₂ (List.mem_of_getElem? hfn₂)).defs _ hcode₂
      have hlen : cresults.length = vals.length := writeAll_isSome_iff.mp (by rw [hwrite]; rfl)
      obtain ⟨sfr₂, hswrite⟩ := Option.isSome_iff_exists.mp
        ((writeAll_isSome_iff (fr := a'.frame)
          (rs := cresults.map (Name.result a.point.node)) (vals := vals)).mpr
          (by rw [List.length_map]; exact hlen))
      have hfetch1 : (constructProg p).fetch ⟨f, nd, 0⟩ =
          some (.term (.ret (regs.map (Name.param nd)))) := fetch_term_of_instr? hfn hi
      have hfetch2 : (constructProg p).fetch a'.point =
          some (.op (.call f₂ (cargs.map (Name.param a.point.node))
            (cresults.map (Name.result a.point.node)))) := by
        rw [ha'pt]
        exact fetch_op_of_instr? hfn₂ hi₂ rfl
      have hstep1 : SSA.Step (constructProg p) ⟨⟨f, nd, 0⟩, sr, a' :: rest', mem⟩
          ⟨a'.point.next, sfr₂, rest', mem⟩ :=
        (SSA.Transition.ret (p := constructProg p)
          (s := ⟨⟨f, nd, 0⟩, sr, a' :: rest', mem⟩) hfetch1 hread rfl hfetch2 hswrite).step_eq
      have ht : n₂ < fn₂.code.length := lt_of_succ hsig hfn₂ hi₂ (by simp [Instr.successors])
      have hmid : ∀ r ∈ fn₂.regs,
          (sfr₂.get ((Instr.call f₂ cargs cresults n₂).nameAt a.point.node r)).isSome ∧
          ∀ w : Word, fr₂.get r = some w →
            sfr₂.get ((Instr.call f₂ cargs cresults n₂).nameAt a.point.node r) = some w := by
        intro r hr
        by_cases hmem : r ∈ cresults
        · rw [Instr.nameAt_of_mem (by simpa [Instr.defs] using hmem),
            writeAll_map_get (Name.result_injective a.point.node) hnd hwrite hswrite r hmem]
          exact ⟨writeAll_isSome_of_mem hwrite hmem, fun w hw => hw⟩
        · rw [Instr.nameAt_of_not_mem (by simpa [Instr.defs] using hmem),
            writeAll_get_of_not_mem hswrite (by simp),
            writeAll_get_of_not_mem hwrite hmem]
          exact hA2 r hr
      obtain ⟨sr₃, hstep2, hmid₂⟩ :=
        term_jump_steps (i := Instr.call f₂ cargs cresults n₂) (j := 1) (fr₁ := fr₂)
          (sr := sfr₂) (stack := rest') (mem := mem) hfn₂ ht
          (fun st h => by
            show SSA.step (constructProg p) _ = _
            rw [step_jump (s := ⟨⟨a.point.func, a.point.node, 1⟩, sfr₂, rest', mem⟩)
              (fetch_term_of_instr? hfn₂ hi₂)]
            exact h) hmid
      refine ⟨_, Relation.TransGen.head (by rw [ha'pt] at hstep1; exact hstep1)
        (Relation.TransGen.single hstep2), agrees_mk hfn₂ hmid₂ htail⟩

/-! ### Matching whole runs -/

/-- The renaming between source and target behaviours is injective, so an
equality of target behaviours is an equality of source behaviours. -/
theorem Behavior.toSSA_injective : Function.Injective Behavior.toSSA := by
  intro a b h
  cases a <;> cases b <;> simp_all [Behavior.toSSA]

/-- **Forward simulation of whole executions.** Any number of source steps from
a state the output agrees with is matched by any number of output steps. -/
theorem construct_steps {p : Prog R} {s t : State R} {s' : SSA.State (Name R)}
    (hsig : p.WellFormedSig) (hc : p.Constructible) (ha : Agrees p s s') (h : Steps p s t) :
    ∃ t', SSA.Steps (constructProg p) s' t' ∧ Agrees p t t' := by
  induction h with
  | refl => exact ⟨s', .refl, ha⟩
  | tail _ hstep ih =>
    obtain ⟨u', hu, hau⟩ := ih
    obtain ⟨v', hv, hav⟩ := construct_step hsig hc hau hstep
    exact ⟨v', hu.trans hv.to_reflTransGen, hav⟩

/-- A source state that returns has an output state that returns the same
values in the same memory, in one step. -/
theorem construct_returned {p : Prog R} {s : State R} {s' : SSA.State (Name R)}
    {vs : List Word} {m : Memory} (ha : Agrees p s s') (h : step p s = .returned vs m) :
    SSA.step (constructProg p) s' = .returned vs m := by
  obtain ⟨⟨hpf, hpl, hpi, hagr⟩, hstk, hmem⟩ := ha
  obtain ⟨⟨f, nd, pidx⟩, sr, sstack, smem⟩ := s'
  obtain ⟨⟨rf, rn⟩, fr, stk, mem⟩ := s
  dsimp only at hpf hpl hpi hagr hstk hmem
  subst hpf
  subst hpl
  subst hpi
  subst hmem
  cases Transition.of_step h (by simp) with
  | halt hf hvals hst =>
    rename_i regs
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    have hA := hagr fn hfn
    have hread : sr.readAll (regs.map (Name.param nd)) = some vs :=
      readAll_map_agree
        (fun r hr w hw =>
          (hA r (fn.mem_regs_of_mem_uses hcode (by simpa [Instr.uses] using hr))).2 w hw)
        hvals
    have hst' : stk = [] := hst
    subst hst'
    cases hstk
    exact (SSA.Transition.halt (p := constructProg p) (s := ⟨⟨f, nd, 0⟩, sr, [], mem⟩)
      (fetch_term_of_instr? hfn hi) hread rfl).step_eq

/-- A source state that traps has an output state that traps in the same
memory, in one step. -/
theorem construct_trapped {p : Prog R} {s : State R} {s' : SSA.State (Name R)} {m : Memory}
    (ha : Agrees p s s') (h : step p s = .trapped m) :
    SSA.step (constructProg p) s' = .trapped m := by
  obtain ⟨⟨hpf, hpl, hpi, hagr⟩, hstk, hmem⟩ := ha
  obtain ⟨⟨f, nd, pidx⟩, sr, sstack, smem⟩ := s'
  obtain ⟨⟨rf, rn⟩, fr, stk, mem⟩ := s
  dsimp only at hpf hpl hpi hagr hstk hmem
  subst hpf
  subst hpl
  subst hpi
  subst hmem
  cases Transition.of_step h (by simp) with
  | trap hf =>
    obtain ⟨fn, hfn, hi, hcode⟩ := fetch_elim hf
    exact (SSA.Transition.trap (p := constructProg p) (s := ⟨⟨f, nd, 0⟩, sr, sstack, mem⟩)
      (fetch_term_of_instr? hfn hi)).step_eq

/-- A source run that never stops has an output run that never stops: the
forward simulation turns each source step into at least one output step, and
the coinduction keeps the remaining output steps of the current block as a
pending prefix. -/
theorem construct_diverges {p : Prog R} {s : State R} {s' : SSA.State (Name R)}
    (hsig : p.WellFormedSig) (hc : p.Constructible) (ha : Agrees p s s') (hd : Diverges p s) :
    SSA.Diverges (constructProg p) s' := by
  refine InfiniteTrace.coinduct
    (fun u => ∃ x v, Diverges p x ∧ Agrees p x v ∧ SSA.Steps (constructProg p) u v) ?_
    ⟨s, s', hd, ha, .refl⟩
  rintro u ⟨x, v, hdx, hax, huv⟩
  rcases Relation.ReflTransGen.cases_head huv with rfl | ⟨w, hw, hwv⟩
  · obtain ⟨y, hy, hdy⟩ := InfiniteTrace.unfold hdx
    obtain ⟨v', htg, hav⟩ := construct_step hsig hc hax hy
    obtain ⟨z, hz, hzv⟩ := Relation.TransGen.head'_iff.mp htg
    exact ⟨z, hz, y, v', hdy, hav, hzv⟩
  · exact ⟨w, hw, x, v, hdx, hax, hwv⟩

/-- **Every source behaviour other than `stuck` is preserved**, with no safety
hypothesis: a source run that returns, traps or diverges never reads an
unwritten register, so the zeros the entry block writes are never observed and
the forward simulation carries the whole run across. -/
theorem construct_behaves_of_ne_stuck {p : Prog R} {f : FuncId} {args : List Word}
    {mem : Memory} {s : State R} {s₀ : SSA.State (Name R)} {b : Behavior}
    (hsig : p.WellFormedSig) (hc : p.Constructible) (hstart : p.start f args mem = some s)
    (hstart' : (constructProg p).start f args mem = some s₀) (hb : Behaves p s b)
    (hne : b ≠ .stuck) : SSA.Behaves (constructProg p) s₀ b.toSSA := by
  obtain ⟨t₀, t₁, hst, hsteps, ha⟩ := construct_start_steps hsig hstart
  have heq : s₀ = t₀ := Option.some.inj (hstart'.symm.trans hst)
  subst heq
  cases b with
  | returned vs m =>
    obtain ⟨u, hu, hfu⟩ := hb
    obtain ⟨u', hu', hau⟩ := construct_steps hsig hc ha hu
    exact ⟨u', hsteps.trans hu', construct_returned hau hfu⟩
  | trapped m =>
    obtain ⟨u, hu, hfu⟩ := hb
    obtain ⟨u', hu', hau⟩ := construct_steps hsig hc ha hu
    exact ⟨u', hsteps.trans hu', construct_trapped hau hfu⟩
  | stuck => exact absurd rfl hne
  | diverges => exact InfiniteTrace.of_steps hsteps (construct_diverges hsig hc ha hb)

/-- **Semantics are preserved in both directions, for source runs that do not
get stuck.** The hypothesis `¬ Behaves p s .stuck` is genuinely needed and is
exactly the "every register is written before it is read" condition in
behavioural form: the construction gives a register that `RTL` leaves unwritten
the value zero, so a source run stuck on such a read has a target run that
continues, and the `stuck` case of the equivalence is false without it. Under
the hypothesis the correspondence is exact, by the forward simulation together
with the determinism of both machines.

This is the same decision an earlier change reached from the other side, where the
`Admissible` predicate had to gain a source-safety conjunct for exactly this
reason: `RTL` has undefined behaviour by design, and a source program that may
go wrong has no claim on the behaviour of its target. The two should be read as
one decision, not as two coincidences. -/
theorem construct_behaves {p : Prog R} {f : FuncId} {args : List Word} {mem : Memory}
    {s : State R} {s₀ : SSA.State (Name R)} {b : Behavior}
    (hsig : p.WellFormedSig) (hc : p.Constructible) (hstart : p.start f args mem = some s)
    (hstart' : (constructProg p).start f args mem = some s₀) (hsafe : ¬ Behaves p s .stuck) :
    Behaves p s b ↔ SSA.Behaves (constructProg p) s₀ b.toSSA := by
  obtain ⟨b', hb'⟩ := Behaves.exists p s
  have hne : b' ≠ .stuck := by rintro rfl; exact hsafe hb'
  have hssa := construct_behaves_of_ne_stuck hsig hc hstart hstart' hb' hne
  constructor
  · intro h
    rw [Behaves.unique h hb']
    exact hssa
  · intro h
    rw [Behavior.toSSA_injective (SSA.Behaves.unique h hssa)]
    exact hb'

/-! ## The construction on the repository's factorial example

The checks below run the construction on `RTL.Examples.factorial`, the factorial
loop as an `RTL` control-flow graph, and confirm that the output is a
well-formed SSA function computing the same results. They are the executable
counterpart of the theorems above and guard the definitions against drift. -/

section Factorial

open Silmaril.Machine.RTL.Examples

/-- The source function satisfies the construction's side conditions. -/
example : Examples.factorial.Constructible := by decide

/-- **The construction of the factorial loop is a well-formed SSA program**, by
`constructProg_wellFormed` rather than by evaluation. -/
example : (constructProg Examples.factorial).WellFormed :=
  constructProg_wellFormed (by decide) (by decide)

/-- The construction of the factorial loop is well-formed by evaluation too,
which checks `UsesDominated` and so exercises the dominance computation. -/
example : (constructProg Examples.factorial).WellFormed := by decide

example :
    ((constructProg Examples.factorial).runMain 200 0 [5] emptyMem).returnedValues? =
      some [120] := by decide

example :
    ((constructProg Examples.factorial).runMain 200 0 [0] emptyMem).returnedValues? =
      some [1] := by decide

example :
    ((constructProg Examples.factorial).runMain 400 0 [10] emptyMem).returnedValues? =
      some [3628800] := by decide

end Factorial

end Silmaril.Machine.RTL
