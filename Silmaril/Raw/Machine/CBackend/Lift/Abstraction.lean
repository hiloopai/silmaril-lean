module

public import Silmaril.Machine.CBackend.Lir.Alloc.Defs
public import Silmaril.Machine.CBackend.RTL.Behaviour.Defs
public import Silmaril.Machine.CallingConvention
public import Silmaril.Machine.CBackend.Lift.Diff.Defs
/-!
# Rung 3: abstracting a physical Lir program to RTL

A decompiler holds a `Lir.Prog P` over *physical* registers and numbered stack
slots and wants a program over *pseudo-registers*. It proposes one, together
with the allocation that puts the pseudo-registers back on the machine. The
proposal is untrusted; the check is **translation validation by recompilation**:
lower the proposed RTL program to Lir, spill it with the proposed allocation,
and compare the result with the program that was actually recovered. The
comparison is a `DecidableEq` test on `Lir.Prog P`, so the checker is decidable
and total, and soundness is `Lir.Alloc.spill_behaves` composed with the
lowering's own preservation theorem.

## The lowering is a parameter

`RTL.toLir` is being written on the sibling branch `machine/rtl-to-lir` and is
not available here. This rung therefore takes the lowering as a parameter: a
plain function `Lowering := RTL.Prog Nat → Lir.Prog Nat`, with the hypothesis
`LowerBehaves` — every non-stuck RTL behaviour is a behaviour of the lowered
program from the corresponding start state — carried by the soundness theorems
rather than bundled into the data, so that a checker call on concrete data
reduces without anyone having to supply the proof. Nothing is instantiated. `RTL.toLir` together
with its preservation theorem is the intended instance, and wiring it up is a
one-line follow-up once both branches land. Keeping it abstract is what makes
the theorem honest: this rung proves exactly what spilling contributes and
nothing about a lowering it cannot see.

## Why the pseudo-register type is `Nat`

`Lir.Alloc.Allocation.Valid` quantifies over *every* virtual register — `∀ v,
a.home v ≠ .reg a.scratch₀`, and `Function.Injective a.home` — so it is **not
decidable** for an arbitrary register type, and the sketch's claim that it is
does not survive contact with the definition. A checker cannot verify a
condition it cannot evaluate. `TableAlloc` is the finite presentation that
can be: a table giving the homes of the registers `0 … table.length - 1`, with
every higher register spilled to a slot above every slot the table mentions.
`TableAlloc.Valid` is three decidable conditions on that finite table, and
`TableAlloc.toAllocation_valid` promotes them to the full `Allocation.Valid`.
Pseudo-registers are therefore `Nat`, which is what `RTL.Examples` and
`Lir.Alloc.firstK` already use.

## The direction of the theorem, and the determinism it rests on

A decompiler needs to conclude things about the *machine* program from the
*abstract* one, which is the backward direction: every behaviour of the
physical Lir program is a behaviour of the proposed RTL program. Forward
simulation gives the opposite direction. Both languages are deterministic and
every state of each has a behaviour (`Lir.Behaves.unique`/`exists`,
`RTL.Behaves.unique`/`exists`), so the forward direction plus determinism gives
the **iff** — conditional, as in CompCert, on the abstract program not getting
stuck from that start state. That hypothesis is not a technicality: a stuck RTL
state is source-level undefined behaviour, about which a compiled program may do
anything at all, so no conclusion about the machine program could be drawn from
one.

## The footprint

The brief asks this rung to check the footprint — red zone, callee-saved
registers — "using the footprint vocabulary". **That vocabulary is not in
this repository.** `docs/X86FootprintSurvey.md` §R1 specifies a `MayChange` /
`Separate` / `ProgramAt` algebra; none of it exists on `main`, and this rung
does not invent a half-version of it. What does exist is
`Machine/CallingConvention.lean`, and `checkFrame` checks the two
calling-convention-level conditions it supports:

* every spill slot the allocation uses lies within `cc.frameExtent frame`, with
  one Lir slot occupying `slotSize` bytes — a *backend* parameter, not a
  calling-convention one, because the byte size of a Lir slot is a fact about
  the code generator and not about the ABI (`x86SlotSize`);
* every physical register the allocation uses that the convention declares
  callee-saved is listed in the proposal's `saved` set.

These are **syntactic** conditions on the allocation. They are not a semantic
footprint theorem and `checkFrame` claims none: Lir's stack slots are abstract
numbered cells with no byte addresses and no relation to a stack pointer, so
there is nothing in this repository against which "the callee wrote only inside
its frame" could be stated, let alone proved. `checkFrame_slots_within` and
`checkFrame_saves_calleeSaved` read the two checks back, and say exactly that
much.
-/

@[expose] public section

namespace Silmaril.Machine.Lift

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine (CallingConvention)

/-! ## Behaviours, transported

`RTL.Behavior` and `Lir.Behavior` are the same four-constructor type in two
namespaces, and `behaviorToLir` is the transport between them.
`docs/CompCertLessons.md` §0 already records that the repository has about ten
such structurally identical `Behavior` inductives with transport functions
between them, and that a generic simulation kit is where they all
belong. This file adds one more rather than refactoring, deliberately: the
cleanup belongs to that kit and should happen once, not in a decompilation PR. -/

/-- An RTL behaviour as a Lir behaviour. -/
def behaviorToLir : RTL.Behavior → Lir.Behavior
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck
  | .diverges => .diverges

/-- Transporting a behaviour loses nothing. -/
theorem behaviorToLir_injective : Function.Injective behaviorToLir := by
  intro a b h
  cases a <;> cases b <;> simp_all [behaviorToLir]

/-- Transport takes a stuck behaviour to a stuck behaviour and nothing else to
one. -/
@[simp] theorem behaviorToLir_eq_stuck {b : RTL.Behavior} :
    behaviorToLir b = .stuck ↔ b = .stuck := by
  cases b <;> simp [behaviorToLir]

/-! ## Lowerings

The parameter this rung is written against. The lowering is *data* — a plain
function — and its correctness is a separate hypothesis, so that a checker call
can be evaluated by `decide` without anyone having to produce the proof first.
The proof is what the soundness theorems take. -/

/-- A lowering from RTL to Lir. The checker is parametric in it; the intended
instance is `RTL.toLir`, whose `LowerBehaves` proof is
`X86.Decompile.Lift.toLir_lowerBehaves` (it lives there because it is used
there, and importing it here would make this file depend on the backend). -/
abbrev Lowering := RTL.Prog Nat → Lir.Prog Nat

/-- A lowering preserves behaviour: every non-stuck behaviour of the RTL
program is a behaviour of the lowered program started on the same function,
arguments and memory. This is stated exactly as `Lir.Alloc.spill_behaves`
states its conclusion, so that the two compose. `RTL.toLir` together with its
preservation theorem is the intended instance, discharged by
`X86.Decompile.Lift.toLir_lowerBehaves`; nothing is instantiated here, to keep
this rung independent of the backend. -/
def LowerBehaves (lower : Lowering) : Prop :=
  ∀ (p : RTL.Prog Nat) (f : RTL.FuncId) (args : List Word) (mem : Memory)
    (s : RTL.State Nat) (b : RTL.Behavior), p.start f args mem = some s →
    RTL.Behaves p s b → b ≠ .stuck →
    ∃ t, (lower p).start f args mem = some t ∧ Lir.Behaves (lower p) t (behaviorToLir b)

/-! ## Allocations as finite data -/

/-- An allocation proposed as a finite table: `table[v]` is the home of the
pseudo-register `v`, and every register at or beyond `table.length` is spilled
to a slot above every slot the table mentions, which keeps the whole function
injective without any condition on the table's slot numbering.

**`Lir.Alloc.Allocation.Valid` is not decidable, and this structure exists
because of that.** Its `home_ne₀`, `home_ne₁` and `injective` fields quantify
over the whole register type — `∀ v, a.home v ≠ .reg a.scratch₀` and
`Function.Injective a.home` — so for `V = Nat` there is nothing for a `decide`
to evaluate and no `Decidable` instance to be had. Do not try. `Valid` below is
three finite conditions on the table, and `toAllocation_valid` promotes them to
the real `Allocation.Valid` for the total `home` this table denotes. -/
structure TableAlloc (P : Type) where
  /-- The homes of the pseudo-registers `0 … table.length - 1`. -/
  table : List (Lir.Alloc.Home P)
  /-- The first scratch register. -/
  scratch₀ : P
  /-- The second scratch register. -/
  scratch₁ : P
  deriving DecidableEq, Repr

namespace TableAlloc

variable {P : Type}

/-- The spill slots the table mentions. -/
def slots (a : TableAlloc P) : List Nat :=
  a.table.filterMap fun h => match h with | .spill m => some m | .reg _ => none

/-- One more than the largest spill slot the table mentions, and `0` when it
mentions none: the first slot number free for registers outside the table. -/
def slotCeiling (a : TableAlloc P) : Nat := a.slots.foldl (fun n m => max n (m + 1)) 0

/-- The physical registers the table mentions. -/
def regs (a : TableAlloc P) : List P :=
  a.table.filterMap fun h => match h with | .reg p => some p | .spill _ => none

/-- The home of a pseudo-register: the table's entry, or a fresh spill slot
above every slot the table mentions. -/
def home (a : TableAlloc P) (v : Nat) : Lir.Alloc.Home P :=
  (a.table[v]?).getD (.spill (a.slotCeiling + v))

/-- The allocation a table denotes. -/
def toAllocation (a : TableAlloc P) : Lir.Alloc.Allocation Nat P where
  home := a.home
  scratch₀ := a.scratch₀
  scratch₁ := a.scratch₁

/-- The three decidable conditions on a table that make the allocation it
denotes valid: the scratch registers are distinct, no tabled home is a scratch
register, and no two registers share a tabled home. -/
structure Valid [DecidableEq P] (a : TableAlloc P) : Prop where
  /-- The scratch registers are distinct. -/
  scratch_ne : a.scratch₀ ≠ a.scratch₁
  /-- No register is homed in the first scratch register. -/
  not_scratch₀ : (Lir.Alloc.Home.reg a.scratch₀) ∉ a.table
  /-- No register is homed in the second scratch register. -/
  not_scratch₁ : (Lir.Alloc.Home.reg a.scratch₁) ∉ a.table
  /-- No two registers share a home. -/
  nodup : a.table.Nodup

instance [DecidableEq P] (a : TableAlloc P) : Decidable a.Valid :=
  decidable_of_iff (a.scratch₀ ≠ a.scratch₁ ∧ (Lir.Alloc.Home.reg a.scratch₀) ∉ a.table ∧
      (Lir.Alloc.Home.reg a.scratch₁) ∉ a.table ∧ a.table.Nodup)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
     fun h => ⟨h.scratch_ne, h.not_scratch₀, h.not_scratch₁, h.nodup⟩⟩

/-- A fold that keeps the running maximum never decreases it. -/
private theorem le_foldl_max : ∀ (l : List Nat) (n : Nat),
    n ≤ l.foldl (fun n m => max n (m + 1)) n
  | [], _ => Nat.le_refl _
  | c :: t, n => le_trans (Nat.le_max_left n (c + 1)) (le_foldl_max t _)

/-- Every element of the fold is strictly below the running maximum. -/
private theorem lt_foldl_max : ∀ (l : List Nat) (n m : Nat), m ∈ l →
    m < l.foldl (fun n m => max n (m + 1)) n
  | [], _, _, hm => absurd hm (by simp)
  | c :: t, n, m, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_max_right n (m + 1)))
        (le_foldl_max t _)
    · exact lt_foldl_max t _ m hm

/-- A slot number appears in `slots` exactly when the table homes some register
in it. -/
theorem mem_slots_iff {a : TableAlloc P} {m : Nat} :
    m ∈ a.slots ↔ (Lir.Alloc.Home.spill m : Lir.Alloc.Home P) ∈ a.table := by
  simp only [slots, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h with
    | reg p => exact absurd he (by simp)
    | spill k => exact (by simpa using he) ▸ hh
  · intro hm
    exact ⟨.spill m, hm, rfl⟩

/-- Every slot the table mentions is below the ceiling, which is what makes the
registers outside the table land clear of it. -/
theorem lt_slotCeiling {a : TableAlloc P} {m : Nat} (hm : m ∈ a.slots) :
    m < a.slotCeiling := lt_foldl_max a.slots 0 m hm

/-- The home of a register inside the table is the table's entry. -/
theorem home_of_lt {a : TableAlloc P} {v : Nat} (hv : v < a.table.length) :
    a.home v = a.table[v] := by
  simp [home, List.getElem?_eq_getElem hv]

/-- The home of a register outside the table is a fresh spill slot. -/
theorem home_of_le {a : TableAlloc P} {v : Nat} (hv : a.table.length ≤ v) :
    a.home v = .spill (a.slotCeiling + v) := by
  simp [home, List.getElem?_eq_none hv]

/-- **A valid table denotes a valid allocation**, which is what makes the
decidable check above stand in for `Lir.Alloc.Allocation.Valid`'s quantification
over the whole, infinite, register type. -/
theorem toAllocation_valid [DecidableEq P] {a : TableAlloc P} (h : a.Valid) :
    a.toAllocation.Valid := by
  have hne : ∀ (p : P), (Lir.Alloc.Home.reg p : Lir.Alloc.Home P) ∉ a.table →
      ∀ v, a.home v ≠ .reg p := by
    intro p hp v
    rcases Nat.lt_or_ge v a.table.length with hv | hv
    · rw [home_of_lt hv]
      exact fun he => hp (he ▸ List.getElem_mem hv)
    · rw [home_of_le hv]
      exact fun he => absurd he (by simp)
  refine ⟨h.scratch_ne, hne _ h.not_scratch₀, hne _ h.not_scratch₁, ?_⟩
  intro v w hvw
  simp only [toAllocation] at hvw
  rcases Nat.lt_or_ge v a.table.length with hv | hv <;>
    rcases Nat.lt_or_ge w a.table.length with hw | hw
  · rw [home_of_lt hv, home_of_lt hw] at hvw
    exact (h.nodup.getElem_inj_iff).mp hvw
  · rw [home_of_lt hv, home_of_le hw] at hvw
    have hm : a.table[v] ∈ a.table := List.getElem_mem hv
    rw [hvw] at hm
    exact absurd (lt_slotCeiling (mem_slots_iff.mpr hm)) (by omega)
  · rw [home_of_le hv, home_of_lt hw] at hvw
    have hm : a.table[w] ∈ a.table := List.getElem_mem hw
    rw [← hvw] at hm
    exact absurd (lt_slotCeiling (mem_slots_iff.mpr hm)) (by omega)
  · rw [home_of_le hv, home_of_le hw] at hvw
    have := Lir.Alloc.Home.spill.inj hvw
    omega

end TableAlloc

/-! ## Proposals -/

/-- A proposed abstraction of a physical Lir program: the RTL program it came
from, and the allocation that maps the RTL pseudo-registers onto the physical
registers and slots. -/
structure AbstractionSpec (P : Type) where
  /-- The abstract program the decompiler proposes. -/
  source : RTL.Prog Nat
  /-- The allocation putting its pseudo-registers back on the machine. -/
  alloc : TableAlloc P

/-- Why an abstraction proposal was rejected. -/
inductive AbstractReject where
  /-- The two scratch registers are the same register. -/
  | scratchClash
  /-- The pseudo-register at this index is homed in a scratch register, which
  spilling uses for its own temporaries. -/
  | homeIsScratch (reg : Nat)
  /-- Two pseudo-registers share a home, so one would overwrite the other. -/
  | homesCollide (first second : Nat)
  /-- Recompiling the proposal yields a program with a different number of
  functions than the one recovered. -/
  | functionCount (proposed recovered : Nat)
  /-- Recompiling the proposal yields a different body for this function. -/
  | functionMismatch (func : Lir.FuncId)
  deriving DecidableEq, Repr

/-- Check the proposed allocation's table, naming the register at fault. -/
def checkAlloc {P : Type} [DecidableEq P] (a : TableAlloc P) : Except AbstractReject Unit :=
  if a.scratch₀ = a.scratch₁ then .error .scratchClash
  else
    match a.table.idxOf? (.reg a.scratch₀) with
    | some i => .error (.homeIsScratch i)
    | none =>
      match a.table.idxOf? (.reg a.scratch₁) with
      | some i => .error (.homeIsScratch i)
      | none =>
        match firstDuplicate a.table with
        | some (i, j) => .error (.homesCollide i j)
        | none => .ok ()

/-- The Lir program a proposal recompiles to: lower the proposed RTL program,
then spill it with the proposed allocation. -/
def recompile {P : Type} (lower : Lowering) (spec : AbstractionSpec P) : Lir.Prog P :=
  Lir.Alloc.spill spec.alloc.toAllocation (lower spec.source)

/-- **Accept when recompiling the proposed RTL program with the proposed
allocation reproduces the given Lir program exactly.** `L` supplies the
lowering; the spilling pass is `Lir.Alloc.spill`. -/
def checkAbstraction {P : Type} [DecidableEq P] (lower : Lowering) (target : Lir.Prog P)
    (spec : AbstractionSpec P) : Except AbstractReject Unit :=
  match checkAlloc spec.alloc with
  | .error e => .error e
  | .ok () =>
    if (recompile lower spec).funcs.length ≠ target.funcs.length then
      .error (.functionCount (recompile lower spec).funcs.length target.funcs.length)
    else
      match firstDiff 0 (recompile lower spec).funcs target.funcs with
      | some i => .error (.functionMismatch i)
      | none => .ok ()

/-! ## Inverting the checker -/

/-- Acceptance establishes the table's validity. -/
theorem checkAlloc_valid {P : Type} [DecidableEq P] {a : TableAlloc P}
    (h : checkAlloc a = .ok ()) : a.Valid := by
  rw [checkAlloc] at h
  split at h
  case isTrue => exact absurd h (by simp)
  rename_i hscr
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i h₀
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i h₁
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hdup
  exact ⟨hscr, List.idxOf?_eq_none_iff.mp h₀, List.idxOf?_eq_none_iff.mp h₁,
    nodup_of_firstDuplicate_none 0 _ hdup⟩

/-- Acceptance establishes that recompiling reproduces the target exactly. -/
theorem checkAbstraction_eq {P : Type} [DecidableEq P] {lower : Lowering} {target : Lir.Prog P}
    {spec : AbstractionSpec P} (h : checkAbstraction lower target spec = .ok ()) :
    Lir.Alloc.spill spec.alloc.toAllocation (lower spec.source) = target := by
  rw [checkAbstraction] at h
  split at h
  case h_1 => exact absurd h (by simp)
  split at h
  case isTrue => exact absurd h (by simp)
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hdiff
  exact congrArg Lir.Prog.mk (eq_of_firstDiff_none 0 _ _ hdiff)

/-- Acceptance establishes that the proposed allocation is valid. -/
theorem checkAbstraction_valid {P : Type} [DecidableEq P] {lower : Lowering}
    {target : Lir.Prog P} {spec : AbstractionSpec P}
    (h : checkAbstraction lower target spec = .ok ()) : spec.alloc.toAllocation.Valid := by
  rw [checkAbstraction] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hal
  exact TableAlloc.toAllocation_valid (checkAlloc_valid hal)

/-! ## Soundness -/

/-- The forward half on its own, without the safety hypothesis: every non-stuck
behaviour of the abstract program is a behaviour of the machine program. -/
theorem checkAbstraction_forward {P : Type} [DecidableEq P] {lower : Lowering}
    (hlow : LowerBehaves lower) {target : Lir.Prog P}
    {spec : AbstractionSpec P} (hok : checkAbstraction lower target spec = .ok ())
    {f : RTL.FuncId} {args : List Word} {mem : Memory} {s : RTL.State Nat} {b : RTL.Behavior}
    (hs : spec.source.start f args mem = some s) (hb : RTL.Behaves spec.source s b)
    (hns : b ≠ .stuck) :
    ∃ t, target.start f args mem = some t ∧ Lir.Behaves target t (behaviorToLir b) := by
  obtain ⟨u, hu, hbu⟩ := hlow spec.source f args mem s b hs hb hns
  obtain ⟨t, ht, hbt⟩ := Lir.Alloc.spill_behaves (checkAbstraction_valid hok) hu hbu
    (by simpa using hns)
  rw [checkAbstraction_eq hok] at ht hbt
  exact ⟨t, ht, hbt⟩

/-- **An accepted abstraction is sound.** If the checker accepts, every
behaviour of the physical Lir program is a behaviour of the proposed RTL
program and conversely, so reasoning about the abstract program is reasoning
about the machine-level one. The hypothesis is that the abstract program does
not get stuck from this start state: a stuck RTL state is source-level
undefined behaviour, and nothing about the machine program follows from it. -/
theorem checkAbstraction_sound {P : Type} [DecidableEq P] {lower : Lowering}
    (hlow : LowerBehaves lower) {target : Lir.Prog P}
    {spec : AbstractionSpec P} (hok : checkAbstraction lower target spec = .ok ())
    {f : RTL.FuncId} {args : List Word} {mem : Memory} {s : RTL.State Nat}
    (hs : spec.source.start f args mem = some s)
    (hsafe : ¬ RTL.Behaves spec.source s .stuck) :
    ∃ t, target.start f args mem = some t ∧
      ∀ b : RTL.Behavior,
        (RTL.Behaves spec.source s b ↔ Lir.Behaves target t (behaviorToLir b)) := by
  obtain ⟨b₀, hb₀⟩ := RTL.Behaves.exists spec.source s
  have hns : b₀ ≠ .stuck := fun he => hsafe (he ▸ hb₀)
  obtain ⟨t, ht, hbt⟩ := checkAbstraction_forward hlow hok hs hb₀ hns
  refine ⟨t, ht, fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · exact RTL.Behaves.unique hb hb₀ ▸ hbt
  · exact behaviorToLir_injective (Lir.Behaves.unique hb hbt) ▸ hb₀

/-! ## The footprint, at the level the repository supports

See the module docstring: the `MayChange` / `Separate` / `ProgramAt` algebra of
That vocabulary is not in this repository, and this section does not pretend otherwise.
It checks the two conditions `Machine/CallingConvention.lean` does support, and
the inversion lemmas below state exactly those two and nothing more. -/

/-- What the proposal claims about the machine frame: the convention, the frame
size in bytes measured from the entry stack pointer, and the callee-saved
registers the function is claimed to save and restore. -/
structure FrameSpec (P : Type) where
  /-- The calling convention the recovered function is claimed to follow. -/
  cc : CallingConvention P
  /-- The frame size in bytes, measured from the entry stack pointer. -/
  frame : Nat
  /-- The callee-saved physical registers the function saves and restores. -/
  saved : List P

/-- Why a frame proposal was rejected. -/
inductive FrameReject where
  /-- The source program uses a pseudo-register the allocation's table does not
  home, so the register is spilled to a slot outside any declared frame. -/
  | unhomedRegister (reg : Nat)
  /-- A spill slot lies outside `cc.frameExtent frame`: its last byte is at or
  beyond the frame floor's extent. -/
  | slotOutsideFrame (slot : Nat)
  /-- The allocation homes a pseudo-register — or a scratch register — in a
  callee-saved physical register that the proposal does not claim to save. -/
  | clobbersCalleeSaved (index : Nat)
  deriving DecidableEq, Repr

/-- The pseudo-registers an RTL instruction mentions. -/
def RTL.Instr.regs {V : Type} (i : Silmaril.Machine.RTL.Instr V) : List V := i.uses ++ i.defs

/-- The pseudo-registers an RTL function mentions: its parameters and every
register read or written by its code. -/
def usedRegsOfFunc {V : Type} (fn : Silmaril.Machine.RTL.Func V) : List V :=
  fn.params ++ fn.code.flatMap RTL.Instr.regs

/-- The pseudo-registers an RTL program mentions. -/
def usedRegs {V : Type} (p : Silmaril.Machine.RTL.Prog V) : List V :=
  p.funcs.flatMap usedRegsOfFunc

/-- The target slot a source spill slot becomes, as `Lir.Alloc.Home.loc`
defines it: source slot `m` becomes target slot `2 * m + 1`. -/
def spillTargetSlot (m : Nat) : Nat := 2 * m + 1

/-- The bytes a Lir stack slot occupies in the backend's frame. A Lir slot is
an abstract numbered cell with no byte address of its own, so this is a
parameter and not something read off a `CallingConvention`: the size of a slot
is a fact about the code generator. `cc.stackArgSlot` is deliberately *not*
used here, because it means the size of a stack-passed **argument** slot, which
is a different thing that happens to agree on x86-64. -/
abbrev SlotSize := Nat

/-- The slot size of the x86-64 backend. `Silmaril.X86.Backend` lays slot `n`
of a function with `nslots` slots at `B + 8 * n` from the body stack pointer;
`X86.Backend.frameSize nslots = 8 * frameWords nslots` is the frame it reserves
and `X86.Backend.slot_lt_frame` is the proof that slot `n` ends at or before the
save area, hence inside the frame. Those are the facts that justify the `8`;
this definition only names it, and nothing here imports the backend. -/
def x86SlotSize : SlotSize := 8

/-- A target slot fits in the frame when its last byte does: slot `n` occupies
the `slotSize` bytes at offsets `[n * slotSize, (n + 1) * slotSize)` of the
region of `cc.frameExtent frame` bytes at and below the entry stack pointer. -/
def SlotWithin {P : Type} (cc : CallingConvention P) (slotSize frame slot : Nat) : Prop :=
  (slot + 1) * slotSize ≤ cc.frameExtent frame

instance {P : Type} (cc : CallingConvention P) (slotSize frame slot : Nat) :
    Decidable (SlotWithin cc slotSize frame slot) := inferInstanceAs (Decidable (_ ≤ _))

/-- Check the calling-convention conditions on an accepted abstraction: that
the source program's registers are all homed, that every spill slot used lies
inside the declared frame, and that every callee-saved physical register the
allocation writes is declared saved. -/
def checkFrame {P : Type} [DecidableEq P] (slotSize : SlotSize) (spec : AbstractionSpec P)
    (fs : FrameSpec P) : Except FrameReject Unit :=
  match (usedRegs spec.source).find? fun v => decide (spec.alloc.table.length ≤ v) with
  | some v => .error (.unhomedRegister v)
  | none =>
    match spec.alloc.slots.find? fun m =>
        !decide (SlotWithin fs.cc slotSize fs.frame (spillTargetSlot m)) with
    | some m => .error (.slotOutsideFrame m)
    | none =>
      match (spec.alloc.regs ++ [spec.alloc.scratch₀, spec.alloc.scratch₁]).findIdx? fun p =>
          decide (p ∈ fs.cc.calleeSaved) && !decide (p ∈ fs.saved) with
      | some i => .error (.clobbersCalleeSaved i)
      | none => .ok ()

/-- Everything a successful `checkFrame` established, in one statement. -/
theorem checkFrame_inv {P : Type} [DecidableEq P] {slotSize : SlotSize}
    {spec : AbstractionSpec P} {fs : FrameSpec P} (h : checkFrame slotSize spec fs = .ok ()) :
    ((usedRegs spec.source).find? fun v => decide (spec.alloc.table.length ≤ v)) = none ∧
      (spec.alloc.slots.find? fun m =>
        !decide (SlotWithin fs.cc slotSize fs.frame (spillTargetSlot m))) = none ∧
      ((spec.alloc.regs ++ [spec.alloc.scratch₀, spec.alloc.scratch₁]).findIdx? fun p =>
        decide (p ∈ fs.cc.calleeSaved) && !decide (p ∈ fs.saved)) = none := by
  rw [checkFrame] at h
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i homed
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hslots
  split at h
  case h_1 => exact absurd h (by simp)
  rename_i hsaved
  exact ⟨homed, hslots, hsaved⟩

/-- **An accepted frame proposal places every spill slot inside the declared
frame.** This is a syntactic statement about the allocation; Lir slots have no
byte addresses, so it is not and does not claim to be a statement about what the
machine program writes. -/
theorem checkFrame_slots_within {P : Type} [DecidableEq P] {slotSize : SlotSize}
    {spec : AbstractionSpec P} {fs : FrameSpec P} (h : checkFrame slotSize spec fs = .ok ()) :
    ∀ m ∈ spec.alloc.slots, SlotWithin fs.cc slotSize fs.frame (spillTargetSlot m) := by
  obtain ⟨-, hslots, -⟩ := checkFrame_inv h
  exact fun m hm => by simpa using List.find?_eq_none.mp hslots m hm

/-- **An accepted frame proposal declares every callee-saved register the
allocation writes.** Again syntactic: it says the proposal's `saved` list covers
the allocation's physical registers, not that the recovered code restores
them. -/
theorem checkFrame_saves_calleeSaved {P : Type} [DecidableEq P] {slotSize : SlotSize}
    {spec : AbstractionSpec P} {fs : FrameSpec P} (h : checkFrame slotSize spec fs = .ok ()) :
    ∀ p ∈ spec.alloc.regs ++ [spec.alloc.scratch₀, spec.alloc.scratch₁],
      p ∈ fs.cc.calleeSaved → p ∈ fs.saved := by
  obtain ⟨-, -, hsaved⟩ := checkFrame_inv h
  intro p hp hcs
  have := List.findIdx?_eq_none_iff.mp hsaved p hp
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not] at this
  rcases this with h' | h'
  · exact absurd hcs h'
  · simpa using h'

/-- **An accepted frame proposal homes every register the source program
uses**, so no register of the source is spilled to a slot outside the table and
hence outside the frame the first check bounds. -/
theorem checkFrame_homed {P : Type} [DecidableEq P] {slotSize : SlotSize}
    {spec : AbstractionSpec P} {fs : FrameSpec P} (h : checkFrame slotSize spec fs = .ok ()) :
    ∀ v ∈ usedRegs spec.source, v < spec.alloc.table.length := by
  obtain ⟨homed, -, -⟩ := checkFrame_inv h
  exact fun v hv => by simpa using List.find?_eq_none.mp homed v hv

end Silmaril.Machine.Lift
