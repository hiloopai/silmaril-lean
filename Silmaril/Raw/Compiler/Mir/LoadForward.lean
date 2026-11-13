module

public import Silmaril.Compiler.Mir.MemoryFuncPass.Defs
public import Silmaril.Compiler.Mir.LoadForwardMemory.Defs
/-! # Block-local full-width load forwarding

`LoadForward.pass` remembers the most recent full-width store or zero-extended load
in a block. A matching 64-bit load becomes a move. Stores clear earlier facts,
calls clear all facts, and writes to either tracked register invalidate the fact.
Narrow accesses are never forwarded. The analysis has one fact, so costs linear
time and constant space per block.

The intended theorem is backward refinement at the identity convention on MirSem;
`correct` proves the frozen `Contract.mirPass` via a memory-aware function-local
simulation. The shared memory and the entire frame stay equal at every step, and
the memory fact includes a successful read, so no successful execution is lost.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.LoadForward

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass (Shape mapFuncs refKey funcRefs)
open Silmaril.Compile.Mir.MemoryFuncPass

structure Fact where
  base : Nat
  offset : Nat
  value : Nat
  deriving DecidableEq, Repr

abbrev Facts := Option Fact

/-- The known register contains the exact result of a successful full-width read. -/
def Holds : Facts → Lir.Frame Nat → Lir.Memory → Prop
  | none, _, _ => True
  | some p, fr, m => ∃ a v, fr.get p.base = some a ∧ fr.get p.value = some v ∧
      m.load .b8 .zero (a.toNat + p.offset) = some v

def kill (F : Facts) (d : Nat) : Facts :=
  F.filter fun p => p.base != d && p.value != d

/-- Recording a load must not use the overwritten destination as its own address. -/
def loaded (d base off : Nat) : Facts :=
  if d = base then none else some ⟨base, off, d⟩

def rewriteLoad (F : Facts) (d base off : Nat) : Lir.Op Nat :=
  match F with
  | some p => if p.base = base ∧ p.offset = off then .move d p.value
      else .load .b8 .zero d base off
  | none => .load .b8 .zero d base off

def rwOp (F : Facts) : Lir.Op Nat → Lir.Op Nat × Facts
  | .load .b8 .zero d base off => (rewriteLoad F d base off, loaded d base off)
  | .store .b8 base off src => (.store .b8 base off src, some ⟨base, off, src⟩)
  | .store w base off src => (.store w base off src, none)
  | .load w e d base off => (.load w e d base off, kill F d)
  | .const d v => (.const d v, kill F d)
  | .move d s => (.move d s, kill F d)
  | .unary op d s => (.unary op d s, kill F d)
  | .binary op d a b => (.binary op d a b, kill F d)
  | .slotGet d n => (.slotGet d n, kill F d)
  | .slotSet n s => (.slotSet n s, F)

def rwInstr (F : Facts) : Instr → Instr × Facts
  | .op o => let p := rwOp F o; (.op p.1, p.2)
  | .fop op d a b => (.fop op d a b, kill F d)
  | .addr d s off => (.addr d s off, kill F d)
  | .call s args res => (.call s args res, none)
  | .callIndirect t args res => (.callIndirect t args res, none)

def rwList : Facts → List Instr → List Instr × Facts
  | F, [] => ([], F)
  | F, x :: xs =>
    let p := rwInstr F x
    let q := rwList p.2 xs
    (p.1 :: q.1, q.2)

def rwBlock (b : Block) : Block := ⟨(rwList none b.instrs.toList).1.toArray, b.term⟩

def rwFunc (f : Func) : Func := { f with blocks := f.blocks.map rwBlock }

def run : Array Mir.Unit → Array Mir.Unit := mapFuncs rwFunc

def fold (F : Facts) (xs : List Instr) : Facts := xs.foldl (fun F x => (rwInstr F x).2) F

theorem holds_kill {F : Facts} {fr : Lir.Frame Nat} {m : Lir.Memory}
    (h : Holds F fr m) (d : Nat) (w : Lir.Word) : Holds (kill F d) (fr.set d w) m := by
  cases F with
  | none => trivial
  | some p =>
    unfold kill
    simp only [Option.filter_some]
    split
    · rename_i hp
      simp only [Bool.and_eq_true, bne_iff_ne] at hp
      obtain ⟨a, v, ha, hv, hm⟩ := h
      exact ⟨a, v, by simpa [hp.1] using ha, by simpa [hp.2] using hv, hm⟩
    · trivial

theorem holds_slot {F : Facts} {fr : Lir.Frame Nat} {m : Lir.Memory}
    (h : Holds F fr m) (n : Nat) (w : Lir.Word) : Holds F (fr.setSlot n w) m := by
  cases F with
  | none => trivial
  | some p => exact h

theorem holds_loaded {fr : Lir.Frame Nat} {m : Lir.Memory} {d base off : Nat}
    {a v : Lir.Word} (ha : fr.get base = some a)
    (hv : m.load .b8 .zero (a.toNat + off) = some v) :
    Holds (loaded d base off) (fr.set d v) m := by
  unfold loaded
  split
  · trivial
  · rename_i hd
    exact ⟨a, v, by simpa [Ne.symm hd] using ha, by simp, hv⟩

theorem rewriteLoad_correct {F : Facts} {fr : Lir.Frame Nat} {m : Lir.Memory}
    (h : Holds F fr m) {d base off : Nat} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory}
    (he : (Lir.Op.load .b8 .zero d base off).exec fr m = some (fr₁, m₁)) :
    (rewriteLoad F d base off).exec fr m = some (fr₁, m₁) := by
  cases F with
  | none => exact he
  | some p =>
    simp only [rewriteLoad]
    split
    · rename_i hp
      obtain ⟨a, v, ha, hv, hm⟩ := h
      have ha' : fr.get base = some a := by simpa only [hp.1] using ha
      have hm' : m.load .b8 .zero (a.toNat + off) = some v := by
        simpa only [hp.2] using hm
      simp only [Lir.Op.exec, ha', hm', Option.bind_some, Option.map_some] at he
      simpa [Lir.Op.exec, hv] using he
    · exact he

theorem rwOp_correct {F : Facts} {fr : Lir.Frame Nat} {m : Lir.Memory}
    (h : Holds F fr m) {o : Lir.Op Nat} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory}
    (he : o.exec fr m = some (fr₁, m₁)) :
    (rwOp F o).1.exec fr m = some (fr₁, m₁) ∧ Holds (rwOp F o).2 fr₁ m₁ := by
  cases o with
  | const d v =>
    simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, holds_kill h d v⟩
  | move d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d v⟩
  | unary op d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d _⟩
  | binary op d a b =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hx, hy, hz], holds_kill h d _⟩
  | load w e d base off =>
    have he₀ := he
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, v, hv, rfl, rfl⟩ := he
    cases w <;> cases e
    all_goals try exact ⟨he₀, holds_kill h d v⟩
    exact ⟨rewriteLoad_correct h he₀, holds_loaded ha hv⟩
  | store w base off src =>
    have he₀ := he
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, v, hv, m', hm, rfl, rfl⟩ := he
    cases w
    all_goals try exact ⟨he₀, trivial⟩
    exact ⟨he₀, a, v, ha, hv, load_store8 hm⟩
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d _⟩
  | slotSet n s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_slot h n v⟩

theorem rwList_length (F : Facts) (xs : List Instr) : (rwList F xs).1.length = xs.length := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp [rwList, ih]

theorem rwList_snd (F : Facts) (xs : List Instr) : (rwList F xs).2 = fold F xs := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih => simp [rwList, ih, fold]

theorem rwList_get (F : Facts) (xs : List Instr) (i : Nat) :
    (rwList F xs).1[i]? = xs[i]?.map fun x => (rwInstr (fold F (xs.take i)) x).1 := by
  induction xs generalizing F i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => simp [rwList, fold]
    | succ i => simp [rwList, ih, fold]

theorem refKey_rwInstr (F : Facts) (x : Instr) : refKey (rwInstr F x).1 = refKey x := by
  cases x <;> rfl

theorem rwList_refs (F : Facts) (xs : List Instr) :
    (rwList F xs).1.filterMap refKey = xs.filterMap refKey := by
  induction xs generalizing F with
  | nil => rfl
  | cons x xs ih =>
    simp only [rwList, List.filterMap_cons, refKey_rwInstr, ih]

theorem shape : Shape rwFunc where
  name _ := rfl
  params _ := rfl
  results _ := rfl
  weak _ := rfl
  size _ := Array.size_map ..
  refs f := by
    simp only [funcRefs, rwFunc, Array.toList_map, List.flatMap_map, rwBlock, List.toList_toArray,
      rwList_refs]

/-- The facts at instruction `i` of block `l` of `f`. -/
def factsAt (f : Func) (l i : Nat) : Facts :=
  match f.blocks[l]? with
  | some b => fold none (b.instrs.toList.take i)
  | none => none

/-- The point relation: the same index and frame, the facts hold. -/
def PR : PointRel := fun f l i fr i' fr' m => i' = i ∧ fr' = fr ∧ Holds (factsAt f l i) fr m

theorem rwFunc_block {f : Func} {l : Nat} {b b' : Block} (hb : f.blocks[l]? = some b)
    (hb' : (rwFunc f).blocks[l]? = some b') : b' = rwBlock b := by
  simp only [rwFunc, Array.getElem?_map, hb, Option.map_some, Option.some.injEq] at hb'
  exact hb'.symm

theorem factsAt_succ {f : Func} {l : Nat} {b : Block} (hb : f.blocks[l]? = some b) {i : Nat}
    {x : Instr} (hx : b.instrs[i]? = some x) :
    factsAt f l (i + 1) = (rwInstr (factsAt f l i) x).2 := by
  have hx' : b.instrs.toList[i]? = some x := by simpa using hx
  simp only [factsAt, hb, fold, List.take_add_one, hx', Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem fsim (f : Func) : FSim f (rwFunc f) (PR f) where
  entry fr m := ⟨rfl, rfl, by simp only [factsAt]; split <;> simp [fold, Holds]⟩
  instr l b b' i fr i' fr' m x hb hb' hp hx := by
    obtain ⟨hi', hfr, hh⟩ := hp
    subst i' fr'
    obtain rfl := rwFunc_block hb hb'
    have hy : (rwBlock b).instrs[i]? = some (rwInstr (factsAt f l i) x).1 := by
      have hx' : b.instrs.toList[i]? = some x := by simpa using hx
      simp only [rwBlock, List.getElem?_toArray, rwList_get, hx', Option.map_some, factsAt, hb]
    rw [hy]
    have hsucc := factsAt_succ hb hx
    cases x with
    | op o =>
      intro fr₁ m₁ he
      obtain ⟨he', hh'⟩ := rwOp_correct hh he
      exact .inr ⟨_, rfl, fr₁, he', rfl, rfl, by rw [hsucc]; exact hh'⟩
    | fop op d a c =>
      intro fr₁ he
      refine ⟨op, d, a, c, rfl, fr₁,
        he, rfl, rfl, ?_⟩
      simp only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨_, _, _, _, rfl⟩ := he
      rw [hsucc]; exact holds_kill hh d _
    | addr d s off =>
      exact ⟨rfl, fun w => ⟨rfl, rfl, by rw [hsucc]; exact holds_kill hh d w⟩⟩
    | call c args res =>
      intro vals hv
      refine ⟨_, rfl, hv, fun vals' fr₁ fr₁' m' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, by rw [hsucc]; trivial⟩
    | callIndirect t args res =>
      intro v vals ht hv
      refine ⟨_, _, rfl, ht, hv,
        fun vals' fr₁ fr₁' m' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, by rw [hsucc]; trivial⟩
  term l b b' i fr i' fr' m hb hb' hp hi := by
    obtain ⟨hi', hfr, hh⟩ := hp
    subst i' fr'
    obtain rfl := rwFunc_block hb hb'
    refine ⟨by simp [rwBlock, rwList_length, hi], fun _ => ⟨rfl, fun l' _ => ⟨rfl, rfl, ?_⟩⟩⟩
    simp only [factsAt]
    split <;> simp [fold, Holds]

theorem sim : Sim rwFunc PR := fsim

/-- Full-width load forwarding refines its input at the identity convention. -/
theorem correct : Contract.mirPass run := MemoryFuncPass.mirPass shape sim

/-- A separate, proved Mir-to-Mir compiler stage. -/
def pass : Mir.Pass := ⟨"loadForward", run, correct⟩

/-- The store/load pair actually rewrites, with the value moved from the store. -/
example : (rwList none [.op (.store .b8 0 16 1), .op (.load .b8 .zero 2 0 16)]).1 =
    [.op (.store .b8 0 16 1), .op (.move 2 1)] := by rfl

/-- Two loads of the same address share the first result. -/
example : (rwList none [.op (.load .b8 .zero 1 0 16), .op (.load .b8 .zero 2 0 16)]).1 =
    [.op (.load .b8 .zero 1 0 16), .op (.move 2 1)] := by rfl

/-- A possibly aliasing narrow store invalidates the previous full-width fact. -/
example : (rwList none [.op (.store .b8 0 0 1), .op (.store .b1 3 0 4),
    .op (.load .b8 .zero 2 0 0)]).1 =
    [.op (.store .b8 0 0 1), .op (.store .b1 3 0 4), .op (.load .b8 .zero 2 0 0)] := by rfl

end Silmaril.Compile.Mir.LoadForward
