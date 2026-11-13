module

public import Silmaril.Machine.RiscV.Lir.Emit.Defs
/-!
# Compilation errors and the compiler entry point

`compile` accepts a Lir program over physical registers exactly when every
condition the backend relies on holds, and otherwise returns the first
violation as an `Error`:

* **calling convention**: parameters, call arguments, call results and returned
  values travel in `a0 … a7`, so each list may have at most 8 entries
  (`tooManyParams`, `tooManyArgs`, `tooManyResults`, `tooManyReturnValues`);
* **offset ranges**: every `JAL` offset must fit in 21 signed bits
  (`jumpOutOfRange`), and the frame must fit in 12-bit immediates
  (`frameTooLarge`, at most 239 stack slots);
* **selection**: an operator without selection would be rejected
  (`unsupported`); currently every Lir operator is selected;
* **slots**: every slot index is below the frame's slot count
  (`slotOutOfRange`; `slotBound` computes a count that satisfies it).

Programs that pass these checks are the subject of the correctness theorems;
nothing is claimed about the code of rejected programs.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Machine.Lir (Prog Func Block Point Loc Op Term Unop Binop Label FuncId)

variable {P : Type}

inductive Error where
  | tooManyParams (func : FuncId) (count : Nat)
  | tooManyArgs (func : FuncId) (label : Label) (index : Nat) (count : Nat)
  | tooManyResults (func : FuncId) (label : Label) (index : Nat) (count : Nat)
  | tooManyReturnValues (func : FuncId) (label : Label) (count : Nat)
  | unsupported (func : FuncId) (label : Label) (index : Nat) (op : Unop)
  | jumpOutOfRange (func : FuncId) (label : Label) (index : Nat)
  | frameTooLarge (slots : Nat)
  | slotOutOfRange (func : FuncId) (label : Label) (index : Nat)
  /-- Floating-point instructions are not compiled to RV64 (yet). -/
  | floatOp (func : FuncId) (label : Label) (index : Nat)
  deriving DecidableEq, Repr

/-! ## Slot bound -/

def locSlot : Loc P → Nat
  | .reg _ => 0
  | .slot n => n + 1

def locsSlot (locs : List (Loc P)) : Nat := (locs.map locSlot).foldr max 0

def instrSlot : Machine.Lir.Instr P → Nat
  | .op (.slotGet _ n) | .op (.slotSet n _) => n + 1
  | .op _ => 0
  | .call _ args results => max (locsSlot args) (locsSlot results)
  | .fop .. => 0

def termSlot : Term P → Nat
  | .ret locs => locsSlot locs
  | _ => 0

def blockSlot (b : Block P) : Nat := max ((b.instrs.map instrSlot).foldr max 0) (termSlot b.term)

def funcSlot (fn : Func P) : Nat := max (locsSlot fn.params) ((fn.blocks.map blockSlot).foldr max 0)

/-- One more than the largest slot index used anywhere in the program. -/
def slotBound (p : Prog P) : Nat := (p.funcs.map funcSlot).foldr max 0

/-! ## Checks -/

def locsBelow (N : Nat) (locs : List (Loc P)) : Bool :=
  locs.all fun
    | .reg _ => true
    | .slot n => decide (n < N)

section Checks

variable (p : Prog P) (N : Nat)

def checkInstr (pt : Point) : Machine.Lir.Instr P → Option Error
  | .op (.unary op _ _) =>
    if (selUnop op 0#5 0#5).isSome then none else some (.unsupported pt.func pt.label pt.index op)
  | .op (.slotGet _ n) | .op (.slotSet n _) =>
    if n < N then none else some (.slotOutOfRange pt.func pt.label pt.index)
  | .op _ => none
  | .call g args results =>
    if 8 < args.length then some (.tooManyArgs pt.func pt.label pt.index args.length)
    else if 8 < results.length then some (.tooManyResults pt.func pt.label pt.index results.length)
    else if !(locsBelow N args && locsBelow N results) then
      some (.slotOutOfRange pt.func pt.label pt.index)
    else if !jalFits (pointIdx p pt + 14 + args.length) (funcStart p g) then
      some (.jumpOutOfRange pt.func pt.label pt.index)
    else none
  | .fop .. => some (.floatOp pt.func pt.label pt.index)

def checkTerm (pt : Point) : Term P → Option Error
  | .jump l =>
    if jalFits (pointIdx p pt) (blockStart p pt.func l) then none
    else some (.jumpOutOfRange pt.func pt.label pt.index)
  | .branch _ l₁ l₂ =>
    if jalFits (pointIdx p pt + 1) (blockStart p pt.func l₁) &&
        jalFits (pointIdx p pt + 2) (blockStart p pt.func l₂) then none
    else some (.jumpOutOfRange pt.func pt.label pt.index)
  | .ret locs =>
    if 8 < locs.length then some (.tooManyReturnValues pt.func pt.label locs.length)
    else if !locsBelow N locs then some (.slotOutOfRange pt.func pt.label pt.index)
    else none
  | .trap =>
    if jalFits (pointIdx p pt) trapIdx then none
    else some (.jumpOutOfRange pt.func pt.label pt.index)

def checkFuncHead (g : FuncId) (fn : Func P) : Option Error :=
  if 8 < fn.params.length then some (.tooManyParams g fn.params.length)
  else if !locsBelow N fn.params then some (.slotOutOfRange g fn.entry 0)
  else if !(jalFits (funcStart p g + 2) overflowIdx &&
      jalFits (funcStart p g + 4 + fn.params.length) (blockStart p g fn.entry)) then
    some (.jumpOutOfRange g fn.entry 0)
  else none

def checkBlock (f l : Nat) (b : Block P) : Option Error :=
  ((b.instrs.mapIdx fun i ins => checkInstr p N ⟨f, l, i⟩ ins) ++
    [checkTerm p N ⟨f, l, b.instrs.length⟩ b.term]).findSome? id

def checkFunc (g : FuncId) (fn : Func P) : Option Error :=
  (checkFuncHead p N g fn :: fn.blocks.mapIdx fun l b => checkBlock p N g l b).findSome? id

def checkProg : Option Error :=
  ((if frameSize N ≤ 2032 then none else some (.frameTooLarge N)) ::
    p.funcs.mapIdx fun g fn => checkFunc p N g fn).findSome? id

end Checks

/-! ## The compiler -/

/-- A compiled program: the instruction list and the slot count of every frame. -/
structure Image where
  code : List Ext.Instr
  slots : Nat
  deriving Repr

def compile (A : Assign P) (p : Prog P) : Except Error Image :=
  match checkProg p (slotBound p) with
  | some e => .error e
  | none => .ok ⟨emitProg A.reg (slotBound p) p, slotBound p⟩

/-! ## Soundness of the checks -/

theorem findSome_id_none {α : Type} {L : List (Option α)} :
    L.findSome? id = none ↔ ∀ x ∈ L, x = none := by
  rw [List.findSome?_eq_none_iff]; simp

theorem compile_ok {A : Assign P} {p : Prog P} {img : Image} (h : compile A p = .ok img) :
    img.code = emitProg A.reg img.slots p ∧ checkProg p img.slots = none := by
  unfold compile at h
  split at h
  · cases h
  · rename_i hc
    cases h
    exact ⟨rfl, hc⟩

section Sound

variable {p : Prog P} {N : Nat} (hc : checkProg p N = none)
include hc

theorem check_frame : frameSize N ≤ 2032 := by
  have := findSome_id_none.mp hc _ List.mem_cons_self
  by_contra h
  simp [h] at this

theorem check_func {g : FuncId} {fn : Func P} (hfn : p.func? g = some fn) :
    checkFunc p N g fn = none := by
  unfold Prog.func? at hfn
  obtain ⟨hg, rfl⟩ := List.getElem?_eq_some_iff.mp hfn
  apply findSome_id_none.mp hc
  apply List.mem_cons_of_mem
  have : (p.funcs.mapIdx fun g fn => checkFunc p N g fn)[g]'(by simpa using hg) ∈
      p.funcs.mapIdx fun g fn => checkFunc p N g fn := List.getElem_mem _
  simpa using this

theorem check_head {g : FuncId} {fn : Func P} (hfn : p.func? g = some fn) :
    checkFuncHead p N g fn = none :=
  findSome_id_none.mp (check_func hc hfn) _ List.mem_cons_self

theorem check_block {f l : Nat} {fn : Func P} {b : Block P} (hfn : p.func? f = some fn)
    (hb : fn.blocks[l]? = some b) : checkBlock p N f l b = none := by
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  apply findSome_id_none.mp (check_func hc hfn)
  apply List.mem_cons_of_mem
  have : (fn.blocks.mapIdx fun l b => checkBlock p N f l b)[l]'(by simpa using hl) ∈
      fn.blocks.mapIdx fun l b => checkBlock p N f l b := List.getElem_mem _
  simpa using this

theorem check_instr {pt : Point} {ins : Machine.Lir.Instr P} (hf : p.fetch pt = some (.instr ins)) :
    checkInstr p N pt ins = none := by
  obtain ⟨fn, b, hfn, hb, hblk⟩ := prog_block p hf
  obtain ⟨b', hb', hcode⟩ := Prog.fetch_eq_some hf
  rw [hblk] at hb'; cases hb'
  rcases hcode with ⟨i, hi, e⟩ | ⟨_, e⟩
  · cases e
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    apply findSome_id_none.mp (check_block hc hfn hb)
    apply List.mem_append_left
    have : (b.instrs.mapIdx fun i ins => checkInstr p N ⟨pt.func, pt.label, i⟩ ins)[pt.index]'
        (by simpa using hlt) ∈ b.instrs.mapIdx fun i ins => checkInstr p N ⟨pt.func, pt.label, i⟩ ins :=
      List.getElem_mem _
    simpa using this
  · cases e

theorem check_term {pt : Point} {t : Term P} (hf : p.fetch pt = some (.term t)) :
    checkTerm p N pt t = none := by
  obtain ⟨fn, b, hfn, hb, hblk⟩ := prog_block p hf
  obtain ⟨b', hb', hcode⟩ := Prog.fetch_eq_some hf
  rw [hblk] at hb'; cases hb'
  rcases hcode with ⟨i, _, e⟩ | ⟨hlen, e⟩
  · cases e
  · cases e
    apply findSome_id_none.mp (check_block hc hfn hb)
    apply List.mem_append_right
    rw [← hlen]
    exact List.mem_singleton_self _

end Sound

theorem locsBelow_slot {N : Nat} {locs : List (Loc P)} (h : locsBelow N locs = true) {n : Nat}
    (hn : Loc.slot n ∈ locs) : n < N := by
  have := List.all_eq_true.mp h _ hn
  simpa using this

end Silmaril.RiscV.Backend
