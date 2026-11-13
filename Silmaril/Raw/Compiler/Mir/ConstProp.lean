module

public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! # Constant and copy propagation on Mir

`ConstProp.pass` rewrites each basic block from its first instruction with a set of
**facts** about the registers: `r = w` (a constant) or `r = x` (a copy of another
register). The facts start at each block from its **entry facts** (an unverified forward
fixpoint across the blocks, checked per function, with no facts anywhere as the
fallback; see "Entry facts across blocks") and are updated by each instruction, which is
rewritten under the facts before it:

* an operation whose operands are all known constants becomes a `const` (folding; a
  division whose `Binop.eval` fails is kept), a `move` of a constant becomes a `const`;
* an operation with one known operand that is an algebraic identity (`alg`: `x + 0`,
  `x * 1`, `x & 0`, …) becomes a `move` of the other operand or a `const`;
* every other operand register that is a known copy is replaced by its source (also in
  call arguments and float operands);
* a `branch` on a known constant becomes a `jump`, and the registers a `ret` returns
  are replaced by their sources.

Writing a register kills the facts that mention it; a call kills the facts on its result
registers (the callee has a frame of its own). At most `maxFacts` facts are kept, so the
pass is linear in the size of the function. Every instruction stays at its index, so the
pass is a lock-step simulation with equal frames (`FuncPass.Sim` with `PR f l i fr i' fr' :=
i' = i ∧ fr' = fr ∧` block `l` is reached by the analysis `∧` the facts at `(l, i)` hold in
`fr`; the check carries them across a jump), and `ConstProp.correct` proves
`Contract.mirPass` through `FuncPass.mirPass`. -/

@[expose] public section

namespace Silmaril.Compile.Mir.ConstProp

open Silmaril.Machine
open Silmaril.Compile.Mir.FuncPass

/-! ## Facts -/

/-- What is known of a register: a constant, or a copy of another register. -/
inductive Val where
  | const (w : Lir.Word)
  | copy (x : Nat)
  deriving DecidableEq, Repr

abbrev Facts := List (Nat × Val)

/-- The fact `r = v` in a frame. -/
def Val.Holds (fr : Lir.Frame Nat) (r : Nat) : Val → Prop
  | .const w => fr.get r = some w
  | .copy x => fr.get r = fr.get x

def Holds (F : Facts) (fr : Lir.Frame Nat) : Prop := ∀ p ∈ F, p.2.Holds fr p.1

/-- Facts kept at most (older ones are dropped). -/
def maxFacts : Nat := 32

def lookup (F : Facts) (r : Nat) : Option Val := (F.find? (·.1 == r)).map (·.2)

def constOf (F : Facts) (r : Nat) : Option Lir.Word :=
  match lookup F r with
  | some (.const w) => some w
  | _ => none

def resolve (F : Facts) (r : Nat) : Nat :=
  match lookup F r with
  | some (.copy x) => x
  | _ => r

def Val.uses (d : Nat) : Val → Bool
  | .copy x => x == d
  | .const _ => false

/-- Forget the facts on `d` and on copies of `d`. -/
def kill (F : Facts) (d : Nat) : Facts := F.filter fun p => p.1 != d && !p.2.uses d

/-- Forget the facts on the registers `rs` and on copies of them. -/
def killAll (F : Facts) (rs : List Nat) : Facts :=
  F.filter fun p => !rs.contains p.1 && !rs.any p.2.uses

def add (F : Facts) (d : Nat) (v : Val) : Facts := ((d, v) :: F).take maxFacts

theorem lookup_mem {F : Facts} {r : Nat} {v : Val} (h : lookup F r = some v) : (r, v) ∈ F := by
  simp only [lookup, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have := List.find?_some hp
  simp only [beq_iff_eq] at this
  subst this
  exact List.mem_of_find?_eq_some hp

theorem get_constOf {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {r : Nat} {w : Lir.Word}
    (hc : constOf F r = some w) : fr.get r = some w := by
  unfold constOf at hc
  split at hc
  · cases hc; exact h _ (lookup_mem (by assumption))
  · cases hc

theorem get_resolve {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) (r : Nat) :
    fr.get (resolve F r) = fr.get r := by
  unfold resolve
  split
  · rename_i x hx
    exact (show fr.get r = fr.get x from h _ (lookup_mem hx)).symm
  · rfl

theorem Val.holds_of {fr fr' : Lir.Frame Nat} {r : Nat} {v : Val} (h : v.Holds fr r)
    (hr : fr'.get r = fr.get r) (hx : ∀ x, v = .copy x → fr'.get x = fr.get x) : v.Holds fr' r := by
  cases v with
  | const w => exact hr.trans h
  | copy x => exact hr.trans (h.trans (hx x rfl).symm)

theorem holds_kill {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) (d : Nat) (w : Lir.Word) :
    Holds (kill F d) (fr.set d w) := by
  intro p hp
  simp only [kill, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hp
  obtain ⟨hp, hd, hu⟩ := hp
  refine Val.holds_of (h p hp) (by simp [hd]) fun x hx => ?_
  rw [hx] at hu
  simp only [Val.uses, beq_eq_false_iff_ne, ne_eq] at hu
  simp [hu]

theorem holds_killAll {F : Facts} {fr fr' : Lir.Frame Nat} (h : Holds F fr) {rs : List Nat}
    {vals : List Lir.Word} (hw : fr.writeAll (rs.map .reg) vals = some fr') : Holds (killAll F rs) fr' := by
  intro p hp
  simp only [killAll, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hp
  obtain ⟨hp, hd, hu⟩ := hp
  refine Val.holds_of (h p hp) (LinkCorrect.writeAll_regs_other hw (by simpa using hd)) fun x hx => ?_
  rw [hx] at hu
  exact LinkCorrect.writeAll_regs_other hw fun hm => hu x hm (by simp [Val.uses])

theorem holds_add {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {d : Nat} {v : Val}
    (hv : v.Holds fr d) : Holds (add F d v) fr := by
  intro p hp
  have hp := List.mem_of_mem_take hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hv
  · exact h p hp

/-! ## Algebraic identities -/

/-- The value of an operation with a known operand: its first operand, its second, or a
constant. -/
inductive Alg where
  | left
  | right
  | const (w : Lir.Word)

def Alg.val : Alg → Lir.Word → Lir.Word → Lir.Word
  | .left, x, _ => x
  | .right, _, y => y
  | .const w, _, _ => w

/-- `x + 0`, `0 + x`, `x - 0`, `x | 0`, `x ^ 0`, shifts by `0`, `x * 1`, `x * 0`, `x & 0`,
`x & -1` and their mirrors, from the known constants `ca` and `cb` of the operands. -/
def alg (op : Lir.Binop) (ca cb : Option Lir.Word) : Option Alg :=
  if cb = some 0 ∧ op ∈ [.add, .sub, .or, .xor, .shl, .shrs, .shru] then some .left
  else if ca = some 0 ∧ op ∈ [.add, .or, .xor] then some .right
  else if cb = some 1 ∧ op = .mul then some .left
  else if ca = some 1 ∧ op = .mul then some .right
  else if (cb = some 0 ∨ ca = some 0) ∧ (op = .mul ∨ op = .and) then some (.const 0)
  else if cb = some (BitVec.allOnes 64) ∧ op = .and then some .left
  else if ca = some (BitVec.allOnes 64) ∧ op = .and then some .right
  else none

theorem alg_spec {op : Lir.Binop} {ca cb : Option Lir.Word} {s : Alg} (h : alg op ca cb = some s)
    {x y z : Lir.Word} (ha : ∀ w, ca = some w → x = w) (hb : ∀ w, cb = some w → y = w)
    (he : op.eval x y = some z) : s.val x y = z := by
  unfold alg at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> cases h
  · obtain ⟨hc, hop⟩ := h1
    obtain rfl := hb _ hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Lir.Binop.eval, Alg.val, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero]
  · obtain ⟨hc, hop⟩ := h2
    obtain rfl := ha _ hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;> simp_all [Lir.Binop.eval, Alg.val]
  · obtain ⟨hc, rfl⟩ := h3
    obtain rfl := hb _ hc
    simp_all [Lir.Binop.eval, Alg.val]
  · obtain ⟨hc, rfl⟩ := h4
    obtain rfl := ha _ hc
    simp_all [Lir.Binop.eval, Alg.val]
  · obtain ⟨hc, hop⟩ := h5
    rcases hc with hc | hc
    · obtain rfl := hb _ hc
      rcases hop with rfl | rfl <;> simp_all [Lir.Binop.eval, Alg.val]
    · obtain rfl := ha _ hc
      rcases hop with rfl | rfl <;> simp_all [Lir.Binop.eval, Alg.val, BitVec.zero_mul]
  · obtain ⟨hc, rfl⟩ := h6
    obtain rfl := hb _ hc
    simp only [Lir.Binop.eval, Option.some.injEq, BitVec.and_allOnes] at he
    exact he
  · obtain ⟨hc, rfl⟩ := h7
    obtain rfl := ha _ hc
    simp only [Lir.Binop.eval, Option.some.injEq, BitVec.allOnes_and] at he
    exact he

/-! ## Rewriting -/

/-- `move d s'` and the facts after it. -/
def moveTo (F : Facts) (d s' : Nat) : Lir.Op Nat × Facts :=
  (.move d s', if s' = d then kill F d else add (kill F d) d (.copy s'))

/-- A `binary` operation that is not folded: an algebraic identity, or the operation with
its operands' copies replaced. -/
def rwBin (F : Facts) (op : Lir.Binop) (d a b : Nat) (ca cb : Option Lir.Word) : Lir.Op Nat × Facts :=
  match alg op ca cb with
  | some .left => moveTo F d (resolve F a)
  | some .right => moveTo F d (resolve F b)
  | some (.const w) => (.const d w, add (kill F d) d (.const w))
  | none => (.binary op d (resolve F a) (resolve F b), kill F d)

/-- Rewrite an operation under the facts before it; the facts after it. -/
def rwOp (F : Facts) : Lir.Op Nat → Lir.Op Nat × Facts
  | .const d w => (.const d w, add (kill F d) d (.const w))
  | .move d s =>
    match constOf F s with
    | some w => (.const d w, add (kill F d) d (.const w))
    | none => moveTo F d (resolve F s)
  | .unary op d s =>
    match constOf F s with
    | some w => (.const d (op.eval w), add (kill F d) d (.const (op.eval w)))
    | none => (.unary op d (resolve F s), kill F d)
  | .binary op d a b =>
    match constOf F a, constOf F b with
    | some x, some y =>
      match op.eval x y with
      | some z => (.const d z, add (kill F d) d (.const z))
      | none => rwBin F op d a b none none
    | ca, cb => rwBin F op d a b ca cb
  | .load w e d base off => (.load w e d (resolve F base) off, kill F d)
  | .store w base off src => (.store w (resolve F base) off (resolve F src), F)
  | .slotGet d n => (.slotGet d n, kill F d)
  | .slotSet n s => (.slotSet n (resolve F s), F)

/-- Rewrite an instruction under the facts before it; the facts after it. -/
def rwInstr (F : Facts) : Instr → Instr × Facts
  | .op o => let p := rwOp F o; (.op p.1, p.2)
  | .fop op d a b => (.fop op d (resolve F a) (resolve F b), kill F d)
  | .addr d s off => (.addr d s off, kill F d)
  | .call c args res => (.call c (args.map (resolve F)) res, killAll F res)
  | .callIndirect t args res => (.callIndirect (resolve F t) (args.map (resolve F)) res, killAll F res)

def rwLoc (F : Facts) : Lir.Loc Nat → Lir.Loc Nat
  | .reg r => .reg (resolve F r)
  | .slot n => .slot n

/-- Rewrite a terminator under the facts at the end of its block. -/
def rwTerm (F : Facts) : Lir.Term Nat → Lir.Term Nat
  | .branch c l₁ l₂ =>
    match constOf F c with
    | some x => .jump (if x = 0 then l₂ else l₁)
    | none => .branch (resolve F c) l₁ l₂
  | .ret locs => .ret (locs.map (rwLoc F))
  | t => t

def rwList : Facts → List Instr → List Instr × Facts
  | F, [] => ([], F)
  | F, x :: xs =>
    let p := rwInstr F x
    let q := rwList p.2 xs
    (p.1 :: q.1, q.2)

/-- Rewrite a block from the facts `F` at its start. -/
def rwBlock (F : Facts) (b : Block) : Block :=
  let p := rwList F b.instrs.toList
  ⟨p.1.toArray, rwTerm p.2 b.term⟩

/-- The facts after a list of instructions. -/
def fold (F : Facts) (xs : List Instr) : Facts := xs.foldl (fun F x => (rwInstr F x).2) F

/-! ## Entry facts across blocks

The facts at the start of each block come from an unverified forward fixpoint over the
control-flow graph (`analyze`): block 0 starts with no facts, and the facts at the start
of a block are those that hold at the end of every predecessor reached so far (`none`: no
predecessor reached yet, the block is unreachable). The result is **checked** (`check`):
block 0 has no facts, and the facts at the start of every successor of a reached block
are among the facts at its end. A function whose analysis fails the check (or does not
settle within `rounds` rounds) is rewritten from no facts at every block (`#[]`), the
block-local pass, which passes the check trivially. -/

/-- The blocks a terminator may jump to. -/
def succs : Lir.Term Nat → List Nat
  | .jump l => [l]
  | .branch _ l₁ l₂ => [l₁, l₂]
  | _ => []

/-- The facts at the start of block `l`; a label past the array has no facts. -/
def entryAt (E : Array (Option Facts)) (l : Nat) : Option Facts := E[l]?.getD (some [])

/-- The facts at the start of every successor of every reached block are among those at
its end, and block 0 has no facts. -/
def check (f : Func) (E : Array (Option Facts)) : Bool :=
  entryAt E 0 == some [] &&
  (List.range f.blocks.size).all fun l =>
    match f.blocks[l]?, entryAt E l with
    | some b, some F =>
      let X := fold F b.instrs.toList
      (succs b.term).all fun l' =>
        match entryAt E l' with
        | some G => G.all fun p => decide (p ∈ X)
        | none => false
    | _, _ => true

/-- Meet the facts `X` at the end of a predecessor into a block's entry facts. -/
def join (X : Facts) : Option Facts → Option Facts
  | none => some X
  | some G => some (G.filter fun p => decide (p ∈ X))

/-- One forward round over the blocks in order. -/
def round (f : Func) (E : Array (Option Facts)) : Array (Option Facts) :=
  (List.range f.blocks.size).foldl (fun E l =>
    match f.blocks[l]?, E[l]? with
    | some b, some (some F) =>
      let X := fold F b.instrs.toList
      (succs b.term).foldl (fun E l' => E.modify l' (join X)) E
    | _, _ => E) E

/-- Rounds of the fixpoint at most. -/
def rounds : Nat := 8

/-- Iterate rounds until nothing changes; `none` if it does not settle. -/
def iterate (f : Func) : Nat → Array (Option Facts) → Option (Array (Option Facts))
  | 0, _ => none
  | k + 1, E =>
    let E' := round f E
    if E' == E then some E else iterate f k E'

/-- The unverified analysis: block 0 from no facts, the others unreached at first. -/
def analyze (f : Func) : Array (Option Facts) :=
  let E₀ := (Array.replicate f.blocks.size none).set! 0 (some [])
  (iterate f rounds E₀).getD #[]

/-- The checked entry facts of the blocks of `f`; no facts anywhere when the check fails. -/
def entryFacts (f : Func) : Array (Option Facts) :=
  let E := analyze f
  if check f E then E else #[]

def rwFunc (f : Func) : Func :=
  let E := entryFacts f
  { f with blocks := f.blocks.mapIdx fun l b => rwBlock ((entryAt E l).getD []) b }

/-- The pass on units. -/
def run : Array Mir.Unit → Array Mir.Unit := mapFuncs rwFunc

/-! ## Correctness -/

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

theorem flatMap_mapIdx {α β γ : Type} (l : List α) {g : Nat → α → β} {h : β → List γ}
    {h' : α → List γ} (hg : ∀ i a, h (g i a) = h' a) : (l.mapIdx g).flatMap h = l.flatMap h' := by
  induction l generalizing g with
  | nil => rfl
  | cons a l ih => simp [List.mapIdx_cons, hg, ih (g := fun i => g (i + 1)) (fun i a => hg (i + 1) a)]

theorem shape : Shape rwFunc where
  name _ := rfl
  params _ := rfl
  results _ := rfl
  weak _ := rfl
  size _ := Array.size_mapIdx
  refs f := by
    simp only [funcRefs, rwFunc, Array.toList_mapIdx]
    exact flatMap_mapIdx _ fun _ b => by simp only [rwBlock, List.toList_toArray, rwList_refs]

theorem moveTo_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {s : Nat} {v : Lir.Word}
    (hv : fr.get s = some v) (d : Nat) (m : Lir.Memory) :
    (moveTo F d (resolve F s)).1.exec fr m = some (fr.set d v, m) ∧
      Holds (moveTo F d (resolve F s)).2 (fr.set d v) := by
  refine ⟨by simp [moveTo, Lir.Op.exec, get_resolve h, hv], ?_⟩
  simp only [moveTo]
  split
  · exact holds_kill h d v
  · refine holds_add (holds_kill h d v) ?_
    simp [Val.Holds, get_resolve h, hv]

theorem rwBin_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {op : Lir.Binop} {d a b : Nat}
    {x y z : Lir.Word} (hx : fr.get a = some x) (hy : fr.get b = some y) (hz : op.eval x y = some z)
    {ca cb : Option Lir.Word} (ha : ∀ w, ca = some w → x = w) (hb : ∀ w, cb = some w → y = w)
    (m : Lir.Memory) :
    (rwBin F op d a b ca cb).1.exec fr m = some (fr.set d z, m) ∧ Holds (rwBin F op d a b ca cb).2 (fr.set d z) := by
  unfold rwBin
  cases hal : alg op ca cb with
  | none => exact ⟨by simp [Lir.Op.exec, get_resolve h, hx, hy, hz], holds_kill h d z⟩
  | some s =>
    have hs := alg_spec hal ha hb hz
    cases s with
    | left => simp only [Alg.val] at hs; subst hs; exact moveTo_correct h hx d m
    | right => simp only [Alg.val] at hs; subst hs; exact moveTo_correct h hy d m
    | const w =>
      simp only [Alg.val] at hs; subst hs
      exact ⟨rfl, holds_add (holds_kill h d _) (by simp [Val.Holds])⟩

theorem rwOp_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) {o : Lir.Op Nat}
    {m : Lir.Memory} {fr₁ : Lir.Frame Nat} {m₁ : Lir.Memory} (he : o.exec fr m = some (fr₁, m₁)) :
    (rwOp F o).1.exec fr m = some (fr₁, m₁) ∧ Holds (rwOp F o).2 fr₁ := by
  cases o with
  | const d w =>
    simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, holds_add (holds_kill h d w) (by simp [Val.Holds])⟩
  | move d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    cases hc : constOf F s with
    | some w =>
      have := (get_constOf h hc).symm.trans hv
      cases this
      simp only [rwOp, hc]
      exact ⟨rfl, holds_add (holds_kill h d v) (by simp [Val.Holds])⟩
    | none =>
      simp only [rwOp, hc]
      exact moveTo_correct h hv d m
  | unary op d s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    cases hc : constOf F s with
    | some w =>
      have := (get_constOf h hc).symm.trans hv
      cases this
      simp only [rwOp, hc]
      exact ⟨rfl, holds_add (holds_kill h d _) (by simp [Val.Holds])⟩
    | none =>
      simp only [rwOp, hc]
      exact ⟨by simp [Lir.Op.exec, get_resolve h, hv], holds_kill h d _⟩
  | binary op d a b =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
    have hca : ∀ w, constOf F a = some w → x = w := fun w hw =>
      Option.some.inj (hx.symm.trans (get_constOf h hw))
    have hcb : ∀ w, constOf F b = some w → y = w := fun w hw =>
      Option.some.inj (hy.symm.trans (get_constOf h hw))
    cases ha : constOf F a with
    | none =>
      simp only [rwOp, ha]
      exact rwBin_correct h hx hy hz (by simp) hcb m
    | some x' =>
    cases hb : constOf F b with
    | none =>
      simp only [rwOp, ha, hb]
      exact rwBin_correct h hx hy hz (ha ▸ hca) (by simp) m
    | some y' =>
    have := (get_constOf h ha).symm.trans hx
    cases this
    have := (get_constOf h hb).symm.trans hy
    cases this
    simp only [rwOp, ha, hb, hz]
    exact ⟨rfl, holds_add (holds_kill h d z) (by simp [Val.Holds])⟩
  | load w e d base off =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, z, hz, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, get_resolve h, ha, hz], holds_kill h d z⟩
  | store w base off src =>
    simp only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨a, ha, x, hx, m', hm', rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, get_resolve h, ha, hx, hm'], h⟩
  | slotGet d n =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    exact ⟨by simp [rwOp, Lir.Op.exec, hv], holds_kill h d v⟩
  | slotSet n s =>
    simp only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
    obtain ⟨v, hv, rfl, rfl⟩ := he
    refine ⟨by simp [rwOp, Lir.Op.exec, get_resolve h, hv], fun p hp => ?_⟩
    refine Val.holds_of (h p hp) rfl fun _ _ => rfl

theorem readAll_rwLoc {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) (locs : List (Lir.Loc Nat)) :
    fr.readAll (locs.map (rwLoc F)) = fr.readAll locs := by
  induction locs with
  | nil => rfl
  | cons l ls ih =>
    simp only [Lir.Frame.readAll, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]
    cases l with
    | reg r => simp only [rwLoc, Lir.Frame.read]; rw [show fr.regs (resolve F r) = fr.regs r from get_resolve h r]
    | slot n => rfl

theorem readAll_resolve {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) (args : List Nat) :
    fr.readAll ((args.map (resolve F)).map .reg) = fr.readAll (args.map .reg) := by
  rw [← readAll_rwLoc h (args.map .reg)]
  simp [rwLoc, Function.comp_def]

theorem rwTerm_correct {F : Facts} {fr : Lir.Frame Nat} (h : Holds F fr) (t : Lir.Term Nat)
    (hns : termOut fr t ≠ .stuck) : termOut fr (rwTerm F t) = termOut fr t := by
  cases t with
  | jump l => rfl
  | trap => rfl
  | ret locs => simp only [rwTerm, termOut, readAll_rwLoc h]
  | branch c l₁ l₂ =>
    simp only [rwTerm]
    cases hc : constOf F c with
    | some x => simp [termOut, get_constOf h hc]
    | none => simp [termOut, get_resolve h]

/-! ## The check -/

theorem check_empty (f : Func) : check f #[] = true := by
  simp [check, entryAt]
  intro l _
  split <;> simp_all

theorem check_spec {f : Func} {E : Array (Option Facts)} (h : check f E = true) :
    entryAt E 0 = some [] ∧ ∀ l b F, f.blocks[l]? = some b → entryAt E l = some F →
      ∀ l' ∈ succs b.term, ∃ G, entryAt E l' = some G ∧ ∀ p ∈ G, p ∈ fold F b.instrs.toList := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, h⟩ := h
  refine ⟨h0, fun l b F hb hF l' hl' => ?_⟩
  have := h l (Array.getElem?_eq_some_iff.mp hb).1
  simp only [hb, hF, List.all_eq_true] at this
  have := this l' hl'
  split at this
  · rename_i G hG
    exact ⟨G, hG, by simpa using this⟩
  · cases this

theorem check_entryFacts (f : Func) : check f (entryFacts f) = true := by
  simp only [entryFacts]
  split
  · assumption
  · exact check_empty f

theorem mem_succs {fr : Lir.Frame Nat} {t : Lir.Term Nat} {l : Nat} (h : termOut fr t = .goto l) :
    l ∈ succs t := by
  cases t with
  | jump l' => cases h; simp [succs]
  | branch c l₁ l₂ =>
    simp only [termOut] at h
    split at h
    · cases h; split <;> simp [succs]
    · cases h
  | ret locs => simp only [termOut] at h; split at h <;> cases h
  | trap => cases h

/-- The facts at instruction `i` of block `l` of `f`. -/
def factsAt (f : Func) (l i : Nat) : Facts :=
  match f.blocks[l]? with
  | some b => fold ((entryAt (entryFacts f) l).getD []) (b.instrs.toList.take i)
  | none => []

/-- The point relation: the same index and frame, the block is reached by the analysis,
and the facts hold. -/
def PR : PointRel := fun f l i fr i' fr' =>
  i' = i ∧ fr' = fr ∧ (entryAt (entryFacts f) l).isSome ∧ Holds (factsAt f l i) fr

theorem rwFunc_block {f : Func} {l : Nat} {b b' : Block} (hb : f.blocks[l]? = some b)
    (hb' : (rwFunc f).blocks[l]? = some b') :
    b' = rwBlock ((entryAt (entryFacts f) l).getD []) b := by
  simp only [rwFunc, Array.getElem?_mapIdx, hb, Option.map_some, Option.some.injEq] at hb'
  exact hb'.symm

theorem factsAt_succ {f : Func} {l : Nat} {b : Block} (hb : f.blocks[l]? = some b) {i : Nat}
    {x : Instr} (hx : b.instrs[i]? = some x) :
    factsAt f l (i + 1) = (rwInstr (factsAt f l i) x).2 := by
  have hx' : b.instrs.toList[i]? = some x := by simpa using hx
  simp only [factsAt, hb, fold, List.take_add_one, hx', Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem factsAt_zero {f : Func} {l : Nat} {G : Facts} (hG : entryAt (entryFacts f) l = some G)
    {fr : Lir.Frame Nat} (h : Holds G fr) : Holds (factsAt f l 0) fr := by
  intro p hp
  simp only [factsAt, hG, Option.getD_some] at hp
  split at hp
  · exact h p (by simpa [fold] using hp)
  · simp at hp

theorem fsim (f : Func) : FSim f (rwFunc f) (PR f) where
  entry fr := by
    obtain ⟨h0, -⟩ := check_spec (check_entryFacts f)
    exact ⟨rfl, rfl, by simp [h0], factsAt_zero h0 (by simp [Holds])⟩
  instr l b b' i fr i' fr' x hb hb' hp hx := by
    obtain ⟨hi', hfr, hreach, hh⟩ := hp
    subst i' fr'
    obtain rfl := rwFunc_block hb hb'
    have hy : (rwBlock ((entryAt (entryFacts f) l).getD []) b).instrs[i]? =
        some (rwInstr (factsAt f l i) x).1 := by
      have hx' : b.instrs.toList[i]? = some x := by simpa using hx
      simp only [rwBlock, List.getElem?_toArray, rwList_get, hx', Option.map_some, factsAt, hb]
    rw [hy]
    have hsucc := factsAt_succ hb hx
    cases x with
    | op o =>
      intro m fr₁ m₁ he
      obtain ⟨he', hh'⟩ := rwOp_correct hh he
      exact .inr ⟨_, rfl, fr₁, he', rfl, rfl, hreach, by rw [hsucc]; exact hh'⟩
    | fop op d a c =>
      intro fr₁ he
      refine ⟨op, d, resolve (factsAt f l i) a, resolve (factsAt f l i) c, rfl, fr₁,
        by simpa [Lir.FOp.exec, get_resolve hh] using he, rfl, rfl, hreach, ?_⟩
      simp only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
      obtain ⟨_, _, _, _, rfl⟩ := he
      rw [hsucc]; exact holds_kill hh d _
    | addr d s off =>
      exact ⟨rfl, fun w => ⟨rfl, rfl, hreach, by rw [hsucc]; exact holds_kill hh d w⟩⟩
    | call c args res =>
      intro vals hv
      refine ⟨_, rfl, by rw [readAll_resolve hh, hv], fun vals' fr₁ fr₁' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, hreach, by rw [hsucc]; exact holds_killAll hh hw⟩
    | callIndirect t args res =>
      intro v vals ht hv
      refine ⟨_, _, rfl, by rw [get_resolve hh, ht], by rw [readAll_resolve hh, hv],
        fun vals' fr₁ fr₁' hw hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      exact ⟨rfl, rfl, hreach, by rw [hsucc]; exact holds_killAll hh hw⟩
  term l b b' i fr i' fr' hb hb' hp hi := by
    obtain ⟨hi', hfr, hreach, hh⟩ := hp
    subst i' fr'
    obtain rfl := rwFunc_block hb hb'
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp hreach
    have hX : factsAt f l i = fold F b.instrs.toList := by
      simp only [factsAt, hb, hF, Option.getD_some, hi]
      rw [List.take_of_length_le (by simp)]
    have hF' : factsAt f l i = (rwList ((entryAt (entryFacts f) l).getD []) b.instrs.toList).2 := by
      rw [hX, rwList_snd, hF, Option.getD_some]
    refine ⟨by simp [rwBlock, rwList_length, hi], fun hns => ⟨?_, fun l' hl' => ?_⟩⟩
    · simp only [rwBlock]
      rw [← hF']
      exact rwTerm_correct hh _ hns
    · obtain ⟨-, hsucc⟩ := check_spec (check_entryFacts f)
      obtain ⟨G, hG, hsub⟩ := hsucc l b F hb hF l' (mem_succs hl')
      exact ⟨rfl, rfl, by simp [hG], factsAt_zero hG fun p hp => hh p (hX ▸ hsub p hp)⟩

theorem sim : Sim rwFunc PR := fsim

/-- **Constant and copy propagation refines its input** (`Contract.mirPass`). -/
theorem correct : Contract.mirPass run := FuncPass.mirPass shape sim

end Silmaril.Compile.Mir.ConstProp
