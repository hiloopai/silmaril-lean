module

public import Silmaril.Compiler.Core.Verified.ArrCreate.Defs
public import Silmaril.Compiler.Core.Verified.StateMem.Defs
/-! # Array objects and their defined integer elements

`Inv` is the array counterpart of `StateMem.Inv`. Each array has one allocation;
definitions are indexed by `(symbol key, element index)`, and initialized elements
are `IntSubobject.Slot`s. Distinct elements of the same array need disjoint byte
ranges, not distinct allocation ids. `Separated` is the interface to existing
scalar and pointer locals; it does not require pretending elements are whole
four-byte allocations.

This module supplies source-memory invariants and frame rules only. No array
program is accepted by the compiler on the strength of these facts alone.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open StateExpr (Key)
open StateMem (Local)
open ArrDesig (Arr)

/-- One array allocation, with a static number of `int` elements. -/
structure Array where
  object : Local
  length : Nat

/-- The source address of an element; all elements share the array's provenance. -/
def Array.addr (a : Array) (i : Nat) : Int := a.object.addr + 4 * i

abbrev ElemKey := Key × Nat
abbrev Defs := ElemKey → Option IntExpr.Term

/-- Change exactly one element's definition. -/
def update (ds : Defs) (q : ElemKey) (d : Option IntExpr.Term) : Defs :=
  fun q' => if q' = q then d else ds q'

/-- Array symbols denote whole array objects, rather than synthetic element slots. -/
def EnvOk (env : Env) (arrays : List Array) : Prop :=
  ∀ a ∈ arrays, ∀ x : Sym, x.key = a.object.sym.key →
    env.lookup x = some (StateMem.ptr a.object)

/-- Live arrays and their defined elements, with exact bounds and alignment. -/
structure Inv (m : Mem.Concrete.State) (arrays : List Array) (ds : Defs) : Prop where
  live : ∀ a ∈ arrays, Arr m a.object.id a.object.addr a.length
  aligned : ∀ a ∈ arrays, a.object.addr % 4 = 0
  unique : ∀ a ∈ arrays, ∀ b ∈ arrays, a.object.sym.key = b.object.sym.key → a = b
  apart : ∀ a ∈ arrays, ∀ b ∈ arrays, a.object.sym.key ≠ b.object.sym.key →
    a.object.id ≠ b.object.id ∧ Slots.Apart a.object.addr (4 * a.length) b.object.addr (4 * b.length)
  defs : ∀ q d, ds q = some d → d.Ok 0 ∧ ∃ a ∈ arrays,
    a.object.sym.key = q.1 ∧ q.2 < a.length ∧
      IntSubobject.Slot m a.object.id (a.addr q.2) (d.val 0)

/-- Arrays are disjoint from the existing four-byte int and eight-byte pointer objects. -/
structure Separated (arrays : List Array) (ints ptrs : List Local) : Prop where
  ints : ∀ a ∈ arrays, ∀ l ∈ ints,
    a.object.sym.key ≠ l.sym.key ∧ a.object.id ≠ l.id ∧
      Slots.Apart a.object.addr (4 * a.length) l.addr 4
  ptrs : ∀ a ∈ arrays, ∀ l ∈ ptrs,
    a.object.sym.key ≠ l.sym.key ∧ a.object.id ≠ l.id ∧
      Slots.Apart a.object.addr (4 * a.length) l.addr 8

theorem Arr.mono {m m' : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) (dead : m'.dead = m.dead)
    (alloc : m'.allocations = m.allocations) : Arr m' id addr N :=
  ⟨dead ▸ h.alive, alloc ▸ h.found⟩

theorem Arr.stored {m : Mem.Concrete.State} {id addr : Int} {N : Nat}
    (h : Arr m id addr N) (wid waddr v : Int) :
    Arr (Locals.stored m wid waddr v) id addr N := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 v)) m
  unfold Locals.stored
  rw [hw]
  exact Arr.mono h rfl rfl

theorem Inv.empty (m : Mem.Concrete.State) : Inv m [] (fun _ => none) := by
  constructor <;> simp

theorem Inv.touched {m m' : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (t : LoadTask.Touched m m') : Inv m' arrays ds :=
  { h with
    live := fun a ha => (h.live a ha).touched t
    defs := fun q d hd => by
      obtain ⟨ok, a, ha, key, bound, slot⟩ := h.defs q d hd
      exact ⟨ok, a, ha, key, bound, slot.touched t⟩ }

theorem Inv.nextExcluded {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (n : Nat) : Inv {m with nextExcluded := n} arrays ds :=
  { h with
    live := fun a ha => Arr.mono (h.live a ha) rfl rfl
    defs := fun q d hd => by
      obtain ⟨ok, a, ha, key, bound, slot⟩ := h.defs q d hd
      exact ⟨ok, a, ha, key, bound, slot.nextExcluded n⟩ }

/-- Two different indices within one array occupy disjoint four-byte ranges. -/
theorem Array.elem_apart (a : Array) {i j : Nat} (ne : i ≠ j) :
    Slots.Apart (a.addr i) 4 (a.addr j) 4 := by
  unfold Slots.Apart Array.addr
  omega

/-- Whole-array separation implies separation of any in-bounds pair of elements. -/
theorem Array.elems_apart {a b : Array}
    (apart : Slots.Apart a.object.addr (4 * a.length) b.object.addr (4 * b.length))
    {i j : Nat} (hi : i < a.length) (hj : j < b.length) :
    Slots.Apart (a.addr i) 4 (b.addr j) 4 := by
  unfold Slots.Apart Array.addr at *
  rcases apart with h | h <;> omega

/-- A store updates just its element; neighbors in the same allocation retain their definitions. -/
theorem Inv.store {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) {a : Array} (ha : a ∈ arrays) {i : Nat} (hi : i < a.length)
    (d : IntExpr.Term) (ok : d.Ok 0) :
    Inv (Locals.stored m a.object.id (a.addr i) (d.val 0)) arrays
      (update ds (a.object.sym.key, i) (some d)) := by
  refine { h with
    live := fun b hb => Arr.stored (h.live b hb) _ _ _
    defs := ?_ }
  intro q d' hd
  unfold update at hd
  split at hd
  · rename_i eq
    cases hd
    subst q
    exact ⟨ok, a, ha, rfl, hi,
      IntSubobject.stored_slot ((h.live a ha).live (by omega) (by exact_mod_cast hi)) _⟩
  · rename_i ne
    obtain ⟨ok', b, hb, key, bound, slot⟩ := h.defs q d' hd
    refine ⟨ok', b, hb, key, bound, slot.stored _ _ _ ?_⟩
    by_cases same : a.object.sym.key = b.object.sym.key
    · obtain rfl := h.unique a ha b hb same
      exact a.elem_apart (by intro eq; apply ne; exact Prod.ext key.symm eq.symm)
    · exact Array.elems_apart (h.apart a ha b hb same).2 hi bound

/-- A disjoint scalar store preserves every array definition. -/
theorem Inv.storeOutside {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) (wid addr v : Int)
    (apart : ∀ a ∈ arrays, Slots.Apart addr 4 a.object.addr (4 * a.length)) :
    Inv (Locals.stored m wid addr v) arrays ds := by
  refine { h with
    live := fun a ha => Arr.stored (h.live a ha) _ _ _
    defs := ?_ }
  intro q d hd
  obtain ⟨ok, a, ha, key, bound, slot⟩ := h.defs q d hd
  refine ⟨ok, a, ha, key, bound, slot.stored _ _ _ ?_⟩
  have sep := apart a ha
  unfold Slots.Apart Array.addr at *
  rcases sep with h | h <;> omega

/-- Element separation from an entire scalar or pointer object. -/
theorem Array.elem_outside {a : Array} {addr : Int} {size i : Nat}
    (apart : Slots.Apart a.object.addr (4 * a.length) addr size) (hi : i < a.length) :
    Slots.Apart (a.addr i) 4 addr size := by
  unfold Slots.Apart Array.addr at *
  rcases apart with h | h <;> omega

/-- Array-element writes frame the existing scalar and pointer invariants unchanged. -/
theorem scalarInv_storeElem {env : Env} {m : Mem.Concrete.State}
    {ints ptrs : List Local} {ds : Key → Option IntExpr.Term}
    {pts : Key → Option StateExpr.PtsTo} {arrays : List Array}
    (h : StateMem.Inv env m ints ds ptrs pts) (sep : Separated arrays ints ptrs)
    {a : Array} (ha : a ∈ arrays) {i : Nat} (hi : i < a.length) (v : Int) :
    StateMem.Inv env (Locals.stored m a.object.id (a.addr i) v) ints ds ptrs pts := by
  have pf : StateMem.PFrame ptrs m (Locals.stored m a.object.id (a.addr i) v) := by
    apply StateMem.PFrame.write
    intro p hp
    simpa [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length] using
      (Array.elem_outside (sep.ptrs a ha p hp).2.2 hi).symm
  have := h.ptrs.frame pf
  refine ⟨h.env, fun l hl => Slots.live_stored (h.live l hl) _ _ _, h.apart, ?_⟩
  intro q d hd
  obtain ⟨ok, l, hl, key, slot⟩ := h.defs q d hd
  exact ⟨ok, l, hl, key, Slots.slot_stored slot _ _ _
    (Array.elem_outside (sep.ints a ha l hl).2.2 hi)⟩

/-- Conversely, a scalar assignment frames every array element. -/
theorem Inv.storeScalar {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    {ints ptrs : List Local} (h : Inv m arrays ds) (sep : Separated arrays ints ptrs)
    {l : Local} (hl : l ∈ ints) (v : Int) :
    Inv (Locals.stored m l.id l.addr v) arrays ds :=
  h.storeOutside _ _ _ fun a ha => (sep.ints a ha l hl).2.2.symm

/-- Recover the concrete cell and its exact bounds for a known definition. -/
theorem Inv.element {m : Mem.Concrete.State} {arrays : List Array} {ds : Defs}
    (h : Inv m arrays ds) {a : Array} (ha : a ∈ arrays) {i : Nat} {d : IntExpr.Term}
    (hd : ds (a.object.sym.key, i) = some d) :
    d.Ok 0 ∧ i < a.length ∧ IntSubobject.Slot m a.object.id (a.addr i) (d.val 0) := by
  obtain ⟨ok, b, hb, key, bound, slot⟩ := h.defs _ d hd
  obtain rfl := h.unique b hb a ha key
  exact ⟨ok, bound, slot⟩

end Silmaril.Compile.Core.Verified.ArrMem
