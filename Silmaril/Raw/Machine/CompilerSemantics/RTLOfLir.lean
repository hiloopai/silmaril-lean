module

public import Silmaril.Machine.CBackend.RTL.Semantics.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Silmaril.Foundations.ForwardSim

@[expose] public section

/-!
# Lifting Lir to RTL: one node per instruction

`Prog.ofLir` is the converse of `RTL.toLir` on the register-only fragment of Lir (no stack
slots, every call, parameter and return location a register; `Prog.RegOnly`, decidable):
block `l` of a Lir function is laid out from node `off l` (the sizes of the blocks before
it, each its instructions plus its terminator), its `k`-th instruction at node `off l + k`
continuing at `off l + k + 1`, and its terminator at `off l + length`, with every label `l`
replaced by `off l`. A label outside the function lands at `code.length`, which is missing
and so stuck, as it is in Lir.

The matching relation is a function, `liftState`: the point `(f, l, k)` goes to node
`off l + k` of `f`, frames keep their registers (there are no slots), the stack is mapped
and the memory kept. Each Lir step is exactly one RTL step (`liftState_step`), so the
simulation is lock-step, and with both machines deterministic every RTL behaviour of the
lifted program is the Lir behaviour (`behaves_ofLir_of_ne_stuck`); a stuck Lir run is
undefined behaviour and claims nothing.

Every call of a Mir link is register-only (`Mir.link` emits `call` with register locations
and no slots), so `ofLir` applies to the output of ccomp's front end.
-/

namespace Silmaril.Machine.RTL

open Silmaril.Machine.Lir (Word Memory)

variable {R : Type}

/-! ## The register-only fragment -/

/-- A register location. -/
def locReg? : Lir.Loc R → Option R
  | .reg r => some r
  | .slot _ => none

/-- Every location is a register. -/
def locsReg (ls : List (Lir.Loc R)) : Bool := ls.all fun l => (locReg? l).isSome

/-- A Lir instruction without stack slots. RTL has no floating-point instruction, so the
fragment also excludes ccomp's `fop`. -/
def instrRegOnly : Lir.Instr R → Bool
  | .op (.slotGet ..) | .op (.slotSet ..) => false
  | .op _ => true
  | .call _ args results => locsReg args && locsReg results
  | .fop .. => false

/-- A Lir terminator without stack slots. -/
def termRegOnly : Lir.Term R → Bool
  | .ret locs => locsReg locs
  | _ => true

/-- A Lir function without stack slots. -/
def funcRegOnly (fn : Lir.Func R) : Bool :=
  locsReg fn.params && fn.blocks.all fun b => b.instrs.all instrRegOnly && termRegOnly b.term

/-- The register-only fragment of Lir: no stack slots anywhere. -/
def Prog.RegOnly (p : Lir.Prog R) : Prop := p.funcs.all funcRegOnly = true

instance (p : Lir.Prog R) : Decidable (Prog.RegOnly p) := inferInstanceAs (Decidable (_ = _))

/-! ## The translation -/

/-- The nodes one block occupies: its instructions and its terminator. -/
def blockSize (b : Lir.Block R) : Nat := b.instrs.length + 1

/-- The first node of block `l`: the sizes of the blocks before it. Past the last block it is
the number of nodes of the function, a missing node. -/
def offset (bs : List (Lir.Block R)) (l : Lir.Label) : Nat := ((bs.take l).map blockSize).sum

theorem offset_cons_succ (b : Lir.Block R) (bs : List (Lir.Block R)) (l : Lir.Label) :
    offset (b :: bs) (l + 1) = blockSize b + offset bs l := by
  simp [offset]

/-! ## The matching relation -/

/-- The node of a Lir point. -/
def nodeOf (p : Lir.Prog R) (pt : Lir.Point) : Nat :=
  match p.func? pt.func with
  | some fn => offset fn.blocks pt.label + pt.index
  | none => 0

/-- The RTL point of a Lir point. -/
def liftPoint (p : Lir.Prog R) (pt : Lir.Point) : Point := ⟨pt.func, nodeOf p pt⟩

/-- The RTL frame of a Lir frame: its registers. -/
def liftFrame (fr : Lir.Frame R) : Frame R := ⟨fr.regs⟩

/-- The RTL activation of a Lir activation. -/
def liftAct (p : Lir.Prog R) (a : Lir.Activation R) : Activation R :=
  ⟨liftPoint p a.point, liftFrame a.frame⟩

/-- The RTL state matching a Lir state. -/
def liftState (p : Lir.Prog R) (s : Lir.State R) : State R :=
  ⟨liftPoint p s.point, liftFrame s.frame, s.stack.map (liftAct p), s.mem⟩

/-- The RTL result matching a Lir result. -/
def liftResult (p : Lir.Prog R) : Lir.Result R → Result R
  | .running t => .running (liftState p t)
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck

/-- The RTL behaviour of a Lir behaviour. -/
def liftBehavior : Lir.Behavior → Behavior
  | .returned vs m => .returned vs m
  | .trapped m => .trapped m
  | .stuck => .stuck
  | .diverges => .diverges

theorem nodeOf_next (p : Lir.Prog R) (pt : Lir.Point) {fn : Lir.Func R}
    (hf : p.func? pt.func = some fn) : nodeOf p pt.next = nodeOf p pt + 1 := by
  simp only [nodeOf, Lir.Point.next_func, hf, Lir.Point.next_label, Lir.Point.next_index]

  omega

theorem nodeOf_label (p : Lir.Prog R) (pt : Lir.Point) {fn : Lir.Func R}
    (hf : p.func? pt.func = some fn) (l : Lir.Label) :
    nodeOf p ⟨pt.func, l, 0⟩ = offset fn.blocks l := by
  simp [nodeOf, hf]

theorem locReg?_isSome {l : Lir.Loc R} (h : (locReg? l).isSome = true) :
    ∃ r, l = .reg r := by
  cases l with
  | reg r => exact ⟨r, rfl⟩
  | slot n => simp [locReg?] at h

@[simp] theorem liftFrame_get (fr : Lir.Frame R) (r : R) : (liftFrame fr).get r = fr.get r := rfl

theorem readAll_lift (fr : Lir.Frame R) (rs : List R) :
    (liftFrame fr).readAll rs = fr.readAll (rs.map .reg) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [Frame.readAll, Lir.Frame.readAll, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]
    rfl

section
variable [DecidableEq R]

theorem liftFrame_set (fr : Lir.Frame R) (r : R) (w : Word) :
    liftFrame (fr.set r w) = (liftFrame fr).set r w := rfl

theorem writeAll_lift (rs : List R) : ∀ (fr : Lir.Frame R) (vs : List Word),
    (liftFrame fr).writeAll rs vs = (fr.writeAll (rs.map .reg) vs).map liftFrame := by
  induction rs with
  | nil => intro fr vs; cases vs <;> rfl
  | cons r rs ih =>
    intro fr vs
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [Frame.writeAll, List.map_cons, Lir.Frame.writeAll, Lir.Frame.write]
      rw [← liftFrame_set, ih]

end

/-! ## The translation -/

variable [Inhabited R]

/-- The register of a location (a default for a slot, never used on the fragment). -/
def locReg (l : Lir.Loc R) : R := (locReg? l).getD default

/-- The registers of locations. -/
def locRegs (ls : List (Lir.Loc R)) : List R := ls.map locReg

/-- An instruction as an RTL node continuing at `succ`. -/
def instrOf (succ : Nat) : Lir.Instr R → Instr R
  | .op (.const d v) => .const d v succ
  | .op (.move d s) => .move d s succ
  | .op (.unary op d s) => .unary op d s succ
  | .op (.binary op d a b) => .binary op d a b succ
  | .op (.load w e d base off) => .load w e d base off succ
  | .op (.store w base off src) => .store w base off src succ
  | .op (.slotGet ..) | .op (.slotSet ..) => .trap
  | .call f args results => .call f (locRegs args) (locRegs results) succ
  | .fop .. => .trap

/-- A terminator as an RTL node, labels replaced by their first nodes. -/
def termOf (lbl : Lir.Label → Nat) : Lir.Term R → Instr R
  | .jump l => .jump (lbl l)
  | .branch c l₁ l₂ => .cond c (lbl l₁) (lbl l₂)
  | .ret locs => .ret (locRegs locs)
  | .trap => .trap

/-- A block's instructions, one node each from `base`. -/
def instrsCode (base : Nat) : List (Lir.Instr R) → List (Instr R)
  | [] => []
  | i :: is => instrOf (base + 1) i :: instrsCode (base + 1) is

/-- Blocks laid out from `base`. -/
def codeFrom (lbl : Lir.Label → Nat) (base : Nat) : List (Lir.Block R) → List (Instr R)
  | [] => []
  | b :: bs => instrsCode base b.instrs ++ termOf lbl b.term :: codeFrom lbl (base + blockSize b) bs

/-- The RTL function of a Lir function. The signature records the parameter count and the
width of the first `ret`; the semantics does not read it. -/
def funcOfLir (fn : Lir.Func R) : Func R where
  sig := ⟨fn.params.length,
    (fn.blocks.findSome? fun b => match b.term with | .ret ls => some ls.length | _ => none).getD 0⟩
  params := locRegs fn.params
  entry := offset fn.blocks fn.entry
  code := codeFrom (offset fn.blocks) 0 fn.blocks

/-- **The RTL program of a Lir program**, one node per instruction. -/
def Prog.ofLir (p : Lir.Prog R) : Prog R := ⟨p.funcs.map funcOfLir⟩

/-! ## Layout -/

@[simp] theorem instrsCode_length (base : Nat) (is : List (Lir.Instr R)) :
    (instrsCode base is).length = is.length := by
  induction is generalizing base with
  | nil => rfl
  | cons i is ih => simp [instrsCode, ih]

theorem instrsCode_get (base : Nat) : ∀ (is : List (Lir.Instr R)) (k : Nat),
    (instrsCode base is)[k]? = is[k]?.map (instrOf (base + k + 1))
  | [], _ => rfl
  | i :: is, 0 => rfl
  | i :: is, k + 1 => by
    rw [instrsCode, List.getElem?_cons_succ, instrsCode_get (base + 1) is k,
      List.getElem?_cons_succ, show base + 1 + k + 1 = base + (k + 1) + 1 by omega]

theorem codeFrom_split (lbl : Lir.Label → Nat) (base : Nat) (c : Lir.Block R)
    (bs : List (Lir.Block R)) (n : Nat) :
    (codeFrom lbl base (c :: bs))[blockSize c + n]? = (codeFrom lbl (base + blockSize c) bs)[n]? := by
  have hl : (instrsCode base c.instrs ++ [termOf lbl c.term]).length = blockSize c := by
    simp [blockSize]
  rw [codeFrom, show instrsCode base c.instrs ++ termOf lbl c.term :: codeFrom lbl (base + blockSize c) bs
      = (instrsCode base c.instrs ++ [termOf lbl c.term]) ++ codeFrom lbl (base + blockSize c) bs
      by simp, ← hl, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- The node of an instruction of a block. -/
theorem codeFrom_instr (lbl : Lir.Label → Nat) : ∀ (base : Nat) (bs : List (Lir.Block R))
    (l : Lir.Label) (b : Lir.Block R) (k : Nat) (i : Lir.Instr R),
    bs[l]? = some b → b.instrs[k]? = some i →
    (codeFrom lbl base bs)[offset bs l + k]? = some (instrOf (base + offset bs l + k + 1) i)
  | _, [], _, _, _, _, h, _ => by simp at h
  | base, c :: bs, 0, b, k, i, h, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have hk : k < (instrsCode base c.instrs).length := by
      simpa using (List.getElem?_eq_some_iff.mp hi).1
    simp only [offset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, codeFrom,
      List.getElem?_append_left hk, instrsCode_get, hi, Option.map_some, Nat.add_zero]
  | base, c :: bs, l + 1, b, k, i, h, hi => by
    simp only [List.getElem?_cons_succ] at h
    rw [offset_cons_succ, Nat.add_assoc, codeFrom_split,
      codeFrom_instr lbl (base + blockSize c) bs l b k i h hi]
    congr 2
    omega

/-- The node of a block's terminator. -/
theorem codeFrom_term (lbl : Lir.Label → Nat) : ∀ (base : Nat) (bs : List (Lir.Block R))
    (l : Lir.Label) (b : Lir.Block R),
    bs[l]? = some b →
    (codeFrom lbl base bs)[offset bs l + b.instrs.length]? = some (termOf lbl b.term)
  | _, [], _, _, h => by simp at h
  | base, c :: bs, 0, b, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [offset, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, codeFrom]
    rw [List.getElem?_append_right (by simp)]
    simp
  | base, c :: bs, l + 1, b, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [offset_cons_succ, Nat.add_assoc, codeFrom_split]
    exact codeFrom_term lbl (base + blockSize c) bs l b h

/-! ## Fetching -/

theorem ofLir_func? (p : Lir.Prog R) (f : FuncId) :
    (Prog.ofLir p).func? f = (p.func? f).map funcOfLir := by
  simp [Prog.func?, Prog.ofLir, Lir.Prog.func?]

/-- An instruction fetched in Lir is fetched, translated, at its node. -/
theorem ofLir_fetch_instr {p : Lir.Prog R} {pt : Lir.Point} {i : Lir.Instr R}
    (h : p.fetch pt = some (.instr i)) :
    (Prog.ofLir p).fetch (liftPoint p pt) = some (instrOf (nodeOf p pt + 1) i) ∧
      ∃ fn b, p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b ∧ i ∈ b.instrs := by
  obtain ⟨b, hb, hc⟩ := Lir.Prog.fetch_eq_some h
  rcases hc with ⟨i', hi', he⟩ | ⟨-, he⟩
  · cases he
    unfold Lir.Prog.block? at hb
    cases hf : p.func? pt.func with
    | none => rw [hf] at hb; cases hb
    | some fn =>
      rw [hf, Option.bind_some] at hb
      refine ⟨?_, fn, b, rfl, hb, List.mem_of_getElem? hi'⟩
      simp only [Prog.fetch, Prog.instr?, liftPoint, ofLir_func?, hf, Option.map_some,
        Option.bind_some, Func.instr?, funcOfLir, nodeOf]
      rw [codeFrom_instr _ 0 fn.blocks pt.label b pt.index i hb hi', Nat.zero_add]
  · cases he

/-- A terminator fetched in Lir is fetched, translated, at its node. -/
theorem ofLir_fetch_term {p : Lir.Prog R} {pt : Lir.Point} {t : Lir.Term R}
    (h : p.fetch pt = some (.term t)) :
    ∃ fn b, p.func? pt.func = some fn ∧ fn.blocks[pt.label]? = some b ∧ b.term = t ∧
      (Prog.ofLir p).fetch (liftPoint p pt) = some (termOf (offset fn.blocks) t) := by
  obtain ⟨b, hb, hc⟩ := Lir.Prog.fetch_eq_some h
  rcases hc with ⟨i', -, he⟩ | ⟨hk, he⟩
  · cases he
  · cases he
    unfold Lir.Prog.block? at hb
    cases hf : p.func? pt.func with
    | none => rw [hf] at hb; cases hb
    | some fn =>
      rw [hf, Option.bind_some] at hb
      refine ⟨fn, b, rfl, hb, rfl, ?_⟩
      simp only [Prog.fetch, Prog.instr?, liftPoint, ofLir_func?, hf, Option.map_some,
        Option.bind_some, Func.instr?, funcOfLir, nodeOf, hk]
      exact codeFrom_term _ 0 fn.blocks pt.label b hb

/-! ## The fragment -/

theorem locsReg_eq {ls : List (Lir.Loc R)} (h : locsReg ls = true) :
    ls = (locRegs ls).map .reg := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [locsReg, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨r, rfl⟩ := locReg?_isSome h.1
    simp only [locRegs, List.map_cons, List.map_map] at ih ⊢
    exact congrArg₂ _ rfl (ih h.2)

theorem instrRegOnly_of_fetch {p : Lir.Prog R} (hp : Prog.RegOnly p) {pt : Lir.Point}
    {i : Lir.Instr R} (h : p.fetch pt = some (.instr i)) : instrRegOnly i = true := by
  obtain ⟨-, fn, b, hf, hb, hi⟩ := ofLir_fetch_instr h
  have hfn := List.all_eq_true.mp hp fn (List.mem_of_getElem? hf)
  simp only [funcRegOnly, Bool.and_eq_true, List.all_eq_true] at hfn
  exact (hfn.2 b (List.mem_of_getElem? hb)).1 i hi

theorem termRegOnly_of_fetch {p : Lir.Prog R} (hp : Prog.RegOnly p) {pt : Lir.Point}
    {t : Lir.Term R} (h : p.fetch pt = some (.term t)) : termRegOnly t = true := by
  obtain ⟨fn, b, hf, hb, rfl, -⟩ := ofLir_fetch_term h
  have hfn := List.all_eq_true.mp hp fn (List.mem_of_getElem? hf)
  simp only [funcRegOnly, Bool.and_eq_true, List.all_eq_true] at hfn
  exact (hfn.2 b (List.mem_of_getElem? hb)).2

variable [DecidableEq R]

/-! ## Entering a function -/

theorem ofLir_enter {p : Lir.Prog R} (hp : Prog.RegOnly p) (f : FuncId) (vals : List Word) :
    (Prog.ofLir p).enter f vals =
      (p.enter f vals).map fun x => (liftPoint p x.1, liftFrame x.2) := by
  simp only [Prog.enter, Lir.Prog.enter, ofLir_func?]
  cases hf : p.func? f with
  | none => rfl
  | some fn =>
    have hreg : funcRegOnly fn = true := List.all_eq_true.mp hp fn (List.mem_of_getElem? hf)
    simp only [funcRegOnly, Bool.and_eq_true] at hreg
    simp only [Option.map_some, Option.bind_some, funcOfLir]
    rw [show (Frame.empty : Frame R) = liftFrame Lir.Frame.empty from rfl, writeAll_lift,
      ← locsReg_eq hreg.1]
    cases Lir.Frame.empty.writeAll fn.params vals with
    | none => rfl
    | some fr => simp [liftPoint, nodeOf, hf]

theorem ofLir_start {p : Lir.Prog R} (hp : Prog.RegOnly p) (f : FuncId) (args : List Word)
    (mem : Memory) :
    (Prog.ofLir p).start f args mem = (p.start f args mem).map (liftState p) := by
  simp only [Prog.start, Lir.Prog.start, ofLir_enter hp]
  cases p.enter f args <;> rfl

/-! ## The simulation -/

/-- **One Lir step is one RTL step.** -/
theorem liftState_step {p : Lir.Prog R} (hp : Prog.RegOnly p) {s : Lir.State R}
    (hr : Lir.step p s ≠ .stuck) :
    step (Prog.ofLir p) (liftState p s) = liftResult p (Lir.step p s) := by
  have tr := Lir.Transition.of_step rfl hr
  generalize Lir.step p s = r at tr
  cases tr with
  | op hf he =>
    rename_i o fr m
    obtain ⟨hfetch, fn, -, hfn, -, -⟩ := ofLir_fetch_instr hf
    have hreg := instrRegOnly_of_fetch hp hf
    have hnext := nodeOf_next p s.point hfn
    unfold step
    simp only [liftState, hfetch]
    cases o with
    | const d v =>
      simp only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp [instrOf, liftResult, liftState, liftPoint, Point.at, hnext, liftFrame_set]
    | move d src =>
      simp only [Lir.Op.exec] at he
      cases hg : s.frame.get src with
      | none => simp [hg] at he
      | some x =>
        simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp [instrOf, hg, liftResult, liftState, liftPoint, Point.at, hnext, liftFrame_set]
    | unary op d src =>
      simp only [Lir.Op.exec] at he
      cases hg : s.frame.get src with
      | none => simp [hg] at he
      | some x =>
        simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp [instrOf, hg, liftResult, liftState, liftPoint, Point.at, hnext, liftFrame_set]
    | binary op d a b =>
      simp only [Lir.Op.exec] at he
      cases ha : s.frame.get a with
      | none => simp [ha] at he
      | some x =>
        cases hb : s.frame.get b with
        | none => simp [ha, hb] at he
        | some y =>
          cases hz : op.eval x y with
          | none => simp [ha, hb, hz] at he
          | some z =>
            simp only [ha, hb, hz, Option.bind_some, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp [instrOf, ha, hb, hz, liftResult, liftState, liftPoint, Point.at, hnext,
              liftFrame_set]
    | load w e d base off =>
      simp only [Lir.Op.exec] at he
      cases ha : s.frame.get base with
      | none => simp [ha] at he
      | some x =>
        cases hz : s.mem.load w e (x.toNat + off) with
        | none => simp [ha, hz] at he
        | some z =>
          simp only [ha, hz, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp [instrOf, ha, hz, liftResult, liftState, liftPoint, Point.at, hnext,
            liftFrame_set]
    | store w base off src =>
      simp only [Lir.Op.exec] at he
      cases ha : s.frame.get base with
      | none => simp [ha] at he
      | some x =>
        cases hb : s.frame.get src with
        | none => simp [ha, hb] at he
        | some y =>
          cases hz : s.mem.store w (x.toNat + off) y with
          | none => simp [ha, hb, hz] at he
          | some m' =>
            simp only [ha, hb, hz, Option.bind_some, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            simp [instrOf, ha, hb, hz, liftResult, liftState, liftPoint, Point.at, hnext]
    | slotGet d n => simp [instrRegOnly] at hreg
    | slotSet n src => simp [instrRegOnly] at hreg
  | fop hf he =>
    have hreg := instrRegOnly_of_fetch hp hf
    simp [instrRegOnly] at hreg
  | call hf ha he =>
    rename_i f args results vals pt fr
    obtain ⟨hfetch, -⟩ := ofLir_fetch_instr hf
    have hreg := instrRegOnly_of_fetch hp hf
    simp only [instrRegOnly, Bool.and_eq_true] at hreg
    unfold step
    simp only [liftState, hfetch, instrOf, readAll_lift, ← locsReg_eq hreg.1, ha,
      ofLir_enter hp, he, Option.map_some]
    rfl
  | jump hf =>
    rename_i l
    obtain ⟨fn, -, hfn, -, -, hfetch⟩ := ofLir_fetch_term hf
    unfold step
    simp only [liftState, hfetch]
    simp [termOf, liftResult, liftState, liftPoint, Point.at, nodeOf_label p s.point hfn]
  | branch hf hc =>
    rename_i c l₁ l₂ x
    obtain ⟨fn, -, hfn, -, -, hfetch⟩ := ofLir_fetch_term hf
    unfold step
    simp only [liftState, hfetch]
    simp only [termOf, liftFrame_get, hc, liftResult, liftState, liftPoint, Point.at,
      nodeOf_label p s.point hfn]
    rw [apply_ite (offset fn.blocks)]
  | ret hf hv hs ha hw =>
    rename_i locs vals a rest g args results fr
    obtain ⟨fn, -, hfn, -, -, hfetch⟩ := ofLir_fetch_term hf
    have hreg := termRegOnly_of_fetch hp hf
    simp only [termRegOnly] at hreg
    obtain ⟨hfa, fna, -, hfna, -, -⟩ := ofLir_fetch_instr ha
    have hrega := instrRegOnly_of_fetch hp ha
    simp only [instrRegOnly, Bool.and_eq_true] at hrega
    unfold step
    simp only [liftState, hfetch, termOf, readAll_lift, ← locsReg_eq hreg, hv, hs,
      List.map_cons, liftAct, hfa, instrOf, writeAll_lift, ← locsReg_eq hrega.2, hw,
      Option.map_some, liftResult]
    simp [liftPoint, Point.at, nodeOf_next p a.point hfna]
  | halt hf hv hs =>
    obtain ⟨fn, -, hfn, -, -, hfetch⟩ := ofLir_fetch_term hf
    have hreg := termRegOnly_of_fetch hp hf
    simp only [termRegOnly] at hreg
    unfold step
    simp only [liftState, hfetch]
    simp [termOf, readAll_lift, ← locsReg_eq hreg, hv, hs, liftResult]
  | trap hf =>
    obtain ⟨fn, -, hfn, -, -, hfetch⟩ := ofLir_fetch_term hf
    unfold step
    simp only [liftState, hfetch]
    simp [termOf, liftResult]

theorem Step.ofLir {p : Lir.Prog R} (hp : Prog.RegOnly p) {s t : Lir.State R}
    (h : Lir.Step p s t) : Step (Prog.ofLir p) (liftState p s) (liftState p t) := by
  unfold Lir.Step at h
  unfold Step
  rw [liftState_step hp (by rw [h]; nofun), h]
  rfl

theorem Steps.ofLir {p : Lir.Prog R} (hp : Prog.RegOnly p) {s t : Lir.State R}
    (h : Lir.Steps p s t) : Steps (Prog.ofLir p) (liftState p s) (liftState p t) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (Step.ofLir hp hst)

/-- **The lifted program has every non-stuck behaviour of the Lir program.** -/
theorem behaves_ofLir {p : Lir.Prog R} (hp : Prog.RegOnly p) {s : Lir.State R}
    {b : Lir.Behavior} (hb : Lir.Behaves p s b) (hns : b ≠ .stuck) :
    Behaves (Prog.ofLir p) (liftState p s) (liftBehavior b) := by
  cases b with
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := hb
    exact ⟨liftState p t, Steps.ofLir hp ht, by rw [liftState_step hp (by rw [hf]; nofun), hf]; rfl⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := hb
    exact ⟨liftState p t, Steps.ofLir hp ht, by rw [liftState_step hp (by rw [hf]; nofun), hf]; rfl⟩
  | stuck => exact absurd rfl hns
  | diverges => exact InfiniteTrace.map (liftState p) (fun _ _ h => Step.ofLir hp h) hb

/-- **Every behaviour of the lifted program is a behaviour of the Lir program**, unless the Lir
run gets stuck (undefined behaviour), from the forward simulation and determinism. -/
theorem behaves_of_ofLir {p : Lir.Prog R} (hp : Prog.RegOnly p) {s : Lir.State R}
    {b : Behavior} (hb : Behaves (Prog.ofLir p) (liftState p s) b) :
    Lir.Behaves p s .stuck ∨ ∃ b', Lir.Behaves p s b' ∧ liftBehavior b' = b := by
  obtain ⟨b', hb'⟩ := Lir.Behaves.exists p s
  by_cases hst : b' = .stuck
  · subst hst
    exact .inl hb'
  · exact .inr ⟨b', hb', Behaves.unique (behaves_ofLir hp hb' hst) hb⟩

end Silmaril.Machine.RTL
