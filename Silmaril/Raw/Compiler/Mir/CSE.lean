module

public import Silmaril.Compiler.Mir.FuncPass.Defs
public import Silmaril.Compiler.Mir.DeadCode.Defs
/-! # Block-local common-subexpression elimination

`CSE.run` replaces repeated pure integer unary and non-faulting binary operations
by moves from an earlier result. At most 32 expression facts are retained. Writing
an operand or the saved result invalidates a fact; calls and block entries clear
all facts. Loads, division/remainder and floating-point operations are not reused.

The intended theorem is backward refinement at the identity convention on MirSem.
`correct` proves `Contract.mirPass` through `FuncPass.FSim`: indices, frames and
memory stay equal, and every saved expression evaluates to its saved register.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.CSE

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass

inductive Expr where
  | unary (op : Lir.Unop) (src : Nat)
  | binary (op : Lir.Binop) (left right : Nat)
  deriving DecidableEq, Repr

def Expr.eval (fr : Lir.Frame Nat) : Expr → Option Lir.Word
  | .unary op s => (fr.get s).map op.eval
  | .binary op a b => (fr.get a).bind fun x => (fr.get b).bind fun y => op.eval x y

def Expr.uses (d : Nat) : Expr → Bool
  | .unary _ s => s == d
  | .binary _ a b => a == d || b == d

def Expr.toOp (d : Nat) : Expr → Lir.Op Nat
  | .unary op s => .unary op d s
  | .binary op a b => .binary op d a b

abbrev Facts := List (Expr × Nat)

def Holds (F : Facts) (fr : Lir.Frame Nat) : Prop :=
  ∀ p ∈ F, ∃ v, p.1.eval fr = some v ∧ fr.get p.2 = some v

def kill (F : Facts) (d : Nat) : Facts :=
  F.filter fun p => !p.1.uses d && p.2 != d

def lookup (F : Facts) (e : Expr) : Option Nat :=
  (F.find? fun p => decide (p.1 = e)).map (·.2)

/-- Do not record an expression whose own operands were overwritten. -/
def record (F : Facts) (e : Expr) (d : Nat) : Facts :=
  if e.uses d then kill F d else ((e, d) :: kill F d).take 32

def rwExpr (F : Facts) (e : Expr) (d : Nat) : Lir.Op Nat × Facts :=
  (match lookup F e with
   | some r => .move d r
   | none => e.toOp d, record F e d)

def rwOp (F : Facts) : Lir.Op Nat → Lir.Op Nat × Facts
  | .unary op d s => rwExpr F (.unary op s) d
  | .binary op d a b =>
    if DeadCode.faults op then (.binary op d a b, kill F d)
    else rwExpr F (.binary op a b) d
  | .const d v => (.const d v, kill F d)
  | .move d s => (.move d s, kill F d)
  | .load w e d base off => (.load w e d base off, kill F d)
  | .store w base off src => (.store w base off src, F)
  | .slotGet d n => (.slotGet d n, kill F d)
  | .slotSet n s => (.slotSet n s, F)

def rwInstr (F : Facts) : Instr → Instr × Facts
  | .op o => let p := rwOp F o; (.op p.1, p.2)
  | .fop op d a b => (.fop op d a b, kill F d)
  | .addr d s off => (.addr d s off, kill F d)
  | .call s args res => (.call s args res, [])
  | .callIndirect t args res => (.callIndirect t args res, [])

def rwList : Facts → List Instr → List Instr × Facts
  | F, [] => ([], F)
  | F, x :: xs =>
    let p := rwInstr F x
    let q := rwList p.2 xs
    (p.1 :: q.1, q.2)

def rwBlock (b : Block) : Block := ⟨(rwList [] b.instrs.toList).1.toArray, b.term⟩

def rwFunc (f : Func) : Func := { f with blocks := f.blocks.map rwBlock }

def run : Array Mir.Unit → Array Mir.Unit := mapFuncs rwFunc

def fold (F : Facts) (xs : List Instr) : Facts := xs.foldl (fun F x => (rwInstr F x).2) F

theorem Expr.eval_set (e : Expr) (fr : Lir.Frame Nat) (d : Nat) (v : Lir.Word)
    (h : e.uses d = false) : e.eval (fr.set d v) = e.eval fr := by
  cases e with
  | unary op s => simp only [Expr.uses, beq_eq_false_iff_ne] at h; simp [Expr.eval, h]
  | binary op a b =>
    simp only [Expr.uses, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp [Expr.eval, h.1, h.2]

theorem Expr.exec (e : Expr) (fr : Lir.Frame Nat) (m : Lir.Memory) (d : Nat) :
    (e.toOp d).exec fr m = (e.eval fr).map (fun v => (fr.set d v, m)) := by
  cases e <;> simp [Expr.toOp, Expr.eval, Lir.Op.exec, Option.map_bind, Function.comp_def]

theorem holds_kill {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr)
    (d : Nat) (v : Lir.Word) : Holds (kill F d) (fr.set d v) := by
  intro p hp
  simp only [kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hp
  obtain ⟨hp, he, hd⟩ := hp
  obtain ⟨w, hw, hr⟩ := h p hp
  exact ⟨w, by rw [Expr.eval_set _ _ _ _ he]; exact hw, by simpa [hd] using hr⟩

theorem holds_record {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr)
    {e : Expr} {d : Nat} {v : Lir.Word} (hv : e.eval fr = some v) :
    Holds (record F e d) (fr.set d v) := by
  unfold record
  split
  · exact holds_kill h d v
  · rename_i he
    intro p hp
    have hp := List.mem_of_mem_take hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨v, by rw [Expr.eval_set _ _ _ _ (by simpa using he)]; exact hv, by simp⟩
    · exact holds_kill h d v p hp

theorem lookup_spec {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr)
    {e : Expr} {r : Nat} (hl : lookup F e = some r) :
    ∃ v, e.eval fr = some v ∧ fr.get r = some v := by
  simp only [lookup, Option.map_eq_some_iff] at hl
  obtain ⟨p, hp, hr⟩ := hl
  have he := List.find?_some hp
  simp only [decide_eq_true_eq] at he
  have hh := h p (List.mem_of_find?_eq_some hp)
  simpa only [he, hr] using hh

theorem rwExpr_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr)
    {e : Expr} {d : Nat} {m : Lir.Memory} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory}
    (he : (e.toOp d).exec fr m = some (fr₁, m₁)) :
    (rwExpr F e d).1.exec fr m = some (fr₁, m₁) ∧ Holds (rwExpr F e d).2 fr₁ := by
  rw [Expr.exec] at he
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
  obtain ⟨v, hv, rfl, rfl⟩ := he
  refine ⟨?_, holds_record h hv⟩
  cases hl : lookup F e with
  | none => simp [rwExpr, hl, Expr.exec, hv]
  | some r =>
    obtain ⟨w, hw, hr⟩ := lookup_spec h hl
    have : w = v := Option.some.inj (hw.symm.trans hv)
    subst w
    simp [rwExpr, hl, Lir.Op.exec, hr]

theorem rwOp_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {o : Lir.Op Nat}
    {m : Lir.Memory} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory} (he : o.exec fr m = some (fr₁, m₁)) :
    (rwOp F o).1.exec fr m = some (fr₁, m₁) ∧ Holds (rwOp F o).2 fr₁ := by
  cases o with
  | const d v =>
    simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, holds_kill h d v⟩
  | move d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d v⟩
  | unary op d s => exact rwExpr_correct (e := .unary op s) h he
  | binary op d a b =>
    simp only [rwOp]
    split
    · simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
      exact ⟨by simp [Lir.Op.exec, hx, hy, hz], holds_kill h d z⟩
    · exact rwExpr_correct (e := .binary op a b) h he
  | load w e d base off =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, ha, hv], holds_kill h d v⟩
  | store w base off src =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, v, hv, m', hm, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, ha, hv, hm], h⟩
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d v⟩
  | slotSet n s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    refine ⟨by simp [rwOp, Lir.Op.exec, hv], fun p hp => ?_⟩
    obtain ⟨w, hw, hr⟩ := h p hp
    refine ⟨w, ?_, hr⟩
    have hs : p.1.eval (fr.setSlot n v) = p.1.eval fr := by cases p.1 <;> rfl
    exact hs.trans hw

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
  | some b => fold [] (b.instrs.toList.take i)
  | none => []

/-- The point relation: the same index and frame, the facts hold. -/
def PR : PointRel := fun f l i fr i' fr' => i' = i ∧ fr' = fr ∧ Holds (factsAt f l i) fr

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
  entry fr := ⟨rfl, rfl, by simp only [factsAt]; split <;> simp [fold, Holds]⟩
  instr l b b' i fr i' fr' x hb hb' hp hx := by
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
      intro m fr₁ m₁ he
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
      refine ⟨_, rfl, hv, fun vals' fr₁ fr₁' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, by rw [hsucc]; simp [rwInstr, Holds]⟩
    | callIndirect t args res =>
      intro v vals ht hv
      refine ⟨_, _, rfl, ht, hv,
        fun vals' fr₁ fr₁' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, by rw [hsucc]; simp [rwInstr, Holds]⟩
  term l b b' i fr i' fr' hb hb' hp hi := by
    obtain ⟨hi', hfr, hh⟩ := hp
    subst i' fr'
    obtain rfl := rwFunc_block hb hb'
    refine ⟨by simp [rwBlock, rwList_length, hi], fun _ => ⟨rfl, fun l' _ => ⟨rfl, rfl, ?_⟩⟩⟩
    simp only [factsAt]
    split <;> simp [fold, Holds]

theorem sim : Sim rwFunc PR := fsim

/-- Common-subexpression elimination refines its input at the identity convention. -/
theorem correct : Contract.mirPass run := FuncPass.mirPass shape sim

/-- A separate, proved Mir-to-Mir compiler stage. -/
def pass : Mir.Pass := ⟨"cse", run, correct⟩

/-- Repeated binary expressions reuse the earlier result. -/
example : (rwList [] [.op (.binary .add 2 0 1), .op (.binary .add 3 0 1)]).1 =
    [.op (.binary .add 2 0 1), .op (.move 3 2)] := by rfl

/-- Repeated unary expressions reuse the earlier result. -/
example : (rwList [] [.op (.unary .sext8 2 0), .op (.unary .sext8 3 0)]).1 =
    [.op (.unary .sext8 2 0), .op (.move 3 2)] := by rfl

/-- Writing an operand invalidates its expression. -/
example : (rwList [] [.op (.binary .add 2 0 1), .op (.const 0 9),
    .op (.binary .add 3 0 1)]).1 =
    [.op (.binary .add 2 0 1), .op (.const 0 9), .op (.binary .add 3 0 1)] := by rfl

/-- Writing the saved result invalidates its expression. -/
example : (rwList [] [.op (.binary .add 2 0 1), .op (.const 2 9),
    .op (.binary .add 3 0 1)]).1 =
    [.op (.binary .add 2 0 1), .op (.const 2 9), .op (.binary .add 3 0 1)] := by rfl

/-- An operation that overwrites its own operand is never recorded. -/
example : (rwList [] [.op (.binary .add 0 0 1), .op (.binary .add 3 0 1)]).1 =
    [.op (.binary .add 0 0 1), .op (.binary .add 3 0 1)] := by rfl

/-- Faulting binary operations remain untouched even when repeated. -/
example : (rwList [] [.op (.binary .divu 2 0 1), .op (.binary .divu 3 0 1)]).1 =
    [.op (.binary .divu 2 0 1), .op (.binary .divu 3 0 1)] := by rfl

/-- Calls clear the cache, including indirect calls. -/
example : (rwList [] [.op (.unary .eqz 2 0), .callIndirect 4 [] [],
    .op (.unary .eqz 3 0)]).1 =
    [.op (.unary .eqz 2 0), .callIndirect 4 [] [], .op (.unary .eqz 3 0)] := by rfl

/-- A nonempty cache invariant is satisfiable on concrete initialized registers. -/
example : Holds [(.binary .add 0 1, 2)]
    (((Lir.Frame.empty.set 0 7).set 1 9).set 2 16) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact ⟨16, rfl, rfl⟩

end Silmaril.Compile.Mir.CSE
