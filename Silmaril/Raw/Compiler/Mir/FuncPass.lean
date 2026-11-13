module

public import Silmaril.Compiler.Mir.Pass.Defs
public import Silmaril.Compiler.Mir.LinkCorrect.Defs
public import Silmaril.Foundations.ForwardSim

/-! # Function-local Mir passes

Most Mir optimizations (constant and copy propagation, dead-code elimination, …) rewrite
the body of each function and nothing else. `FuncPass.mapFuncs g` applies `g : Func → Func`
to every function of every unit. It proves `Contract.mirPass` (`FuncPass.mirPass`) when

* `g` keeps the interface of a function and its symbol references (`Shape`): name,
  parameters, results, weakness, number of blocks, and the list of `addr` and `call`
  symbols in order (so the names in force, `MirSem.taken`, `MirSem.Reach` and the valid
  placements are those of the input, and the data, hence the initial memory, are
  unchanged);
* a per-function relation `PR f l i fr i' fr'` between a point `(l, i)` of `f` with frame
  `fr` and the point `(l, i')` of `g f` with frame `fr'` is a forward simulation of one
  instruction or terminator (`Sim`): an operation is matched by one operation or by none
  (it is deleted; the memory is unchanged), every other instruction by one of the same
  kind with the same effect, a terminator by one with the same outcome.

The state relation `Rel` (same label and memory, `PR` on the point and frame, the same on
each suspended caller after it receives its results) is then a `Silmaril.ForwardSim` of
`MirSem.Step` with the number of instructions left in the block as its measure, and the
final results are equal (`step_match`). Since `MirSem` is deterministic, the forward
simulation gives the backward refinement of the contract: the input's behaviour, unless
stuck, is the output's (`MirSem.Behaves.unique`).

The general form `FuncPass.mirPass_of` lets the function map depend on the units
(`mapFuncs (G us) us`) and needs only `Iface` (`Shape` without the `call` references) and
a valid input placement for each valid output placement. `valid_of` gives one for a map
that drops only references to symbols that no unit defines (`Undefined`): those impose no
placement, and every reachable defined symbol stays reachable (`reach_of`). -/

@[expose] public section

namespace Silmaril.Compile.Mir.FuncPass

open Silmaril.Machine Relation
open Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem

/-! ## Shape -/

/-- The symbol an instruction refers to, with whether it is an `addr` (`MirSem.instrRefs`
and `MirSem.taken` read these). -/
def refKey : Instr → Option (Bool × String)
  | .addr _ s _ => some (true, s)
  | .call s _ _ => some (false, s)
  | _ => none

/-- The symbol references of a function, in order. -/
def funcRefs (f : Func) : List (Bool × String) :=
  f.blocks.toList.flatMap fun b => b.instrs.toList.filterMap refKey

/-- Apply `g` to every function of every unit. -/
def mapFuncs (g : Func → Func) (us : Array Mir.Unit) : Array Mir.Unit :=
  us.map fun u => { u with funcs := u.funcs.map g }

/-- `g` keeps what `MirSem` reads of a function outside its body. -/
structure Shape (g : Func → Func) : Prop where
  name : ∀ f, (g f).name = f.name
  params : ∀ f, (g f).params = f.params
  results : ∀ f, (g f).results = f.results
  weak : ∀ f, (g f).weak = f.weak
  size : ∀ f, (g f).blocks.size = f.blocks.size
  refs : ∀ f, funcRefs (g f) = funcRefs f

/-- `g` keeps the interface of a function and its `addr` symbols, but may drop `call`
references (`Shape` without `refs`): the names in force, `MirSem.taken`, the data and the
initial memory are those of the input, and `MirSem.Reach` may shrink (`reach_of`). -/
structure Iface (g : Func → Func) : Prop where
  name : ∀ f, (g f).name = f.name
  params : ∀ f, (g f).params = f.params
  results : ∀ f, (g f).results = f.results
  weak : ∀ f, (g f).weak = f.weak
  size : ∀ f, (g f).blocks.size = f.blocks.size
  addrs : ∀ f n, (true, n) ∈ funcRefs (g f) ↔ (true, n) ∈ funcRefs f

theorem Shape.iface {g : Func → Func} (hg : Shape g) : Iface g :=
  ⟨hg.name, hg.params, hg.results, hg.weak, hg.size, fun f _ => by rw [hg.refs f]⟩

section Iface

variable {g : Func → Func} (hg : Iface g) (us : Array Mir.Unit)
include hg

omit hg in
theorem map_filter_map {α : Type} {l : List Func} {q : Func → Bool} {h : Func → α}
    (hq : ∀ f, q (g f) = q f) (hh : ∀ f, h (g f) = h f) :
    ((l.map g).filter q).map h = (l.filter q).map h := by
  induction l with
  | nil => rfl
  | cons f l ih => by_cases hf : q f = true <;> simp_all

omit hg in
theorem filter_map_comm {l : List Func} {q : Func → Bool} (hq : ∀ f, q (g f) = q f) :
    (l.map g).filter q = (l.filter q).map g := by
  induction l with
  | nil => rfl
  | cons f l ih => by_cases hf : q f = true <;> simp_all

omit hg in
theorem flatMap_funcs : (mapFuncs g us).toList.flatMap (·.funcs.toList) =
    (us.toList.flatMap (·.funcs.toList)).map g := by
  simp [mapFuncs, List.flatMap_map, List.map_flatMap]

omit hg in
theorem flatMap_data : (mapFuncs g us).toList.flatMap (·.data.toList) = us.toList.flatMap (·.data.toList) := by
  simp [mapFuncs, List.flatMap_map]

theorem strongNames_eq : strongNames (mapFuncs g us) = strongNames us := by
  simp only [strongNames, mapFuncs, Array.toList_map, List.flatMap_map, Array.toList_map]
  congr 1; funext u
  rw [map_filter_map (fun f => by simp [hg.weak]) hg.name]

theorem funcDefs_eq : funcDefs (mapFuncs g us) = (funcDefs us).map g := by
  rw [funcDefs, funcDefs, strongNames_eq hg, flatMap_funcs]
  exact filter_map_comm fun f => by simp [hg.weak, hg.name]

theorem dataDefs_eq : dataDefs (mapFuncs g us) = dataDefs us := by
  rw [dataDefs, dataDefs, strongNames_eq hg, flatMap_data]

theorem funcOf_eq (n : String) : funcOf (mapFuncs g us) n = (funcOf us n).map g := by
  simp [funcOf, funcDefs_eq hg, List.find?_map, hg.name]

theorem dataOf_eq (n : String) : dataOf (mapFuncs g us) n = dataOf us n := by
  simp [dataOf, dataDefs_eq hg]

omit hg in
theorem need_eq (base : Nat) : need (mapFuncs g us) base = need us base := by
  simp only [need, flatMap_data]

theorem symValue_eq (P : Placement) (s : String) : symValue (mapFuncs g us) P s = symValue us P s := by
  simp [symValue, dataOf_eq hg, funcOf_eq hg]

theorem initMem_eq (P : Placement) (m : Nat) : initMem (mapFuncs g us) P m = initMem us P m := by
  simp only [initMem, dataDefs_eq hg]
  congr 1; funext a; split <;> simp [objectByte, symValue_eq hg]

omit hg in
theorem mem_refs_iff (f : Func) (k : Bool) (s : String) :
    (k, s) ∈ funcRefs f ↔ ∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs.toList, refKey i = some (k, s) := by
  simp [funcRefs]

omit hg in
theorem instrRefs_iff (i : Instr) (s : String) : s ∈ instrRefs i ↔ ∃ k, refKey i = some (k, s) := by
  cases i <;> simp [instrRefs, refKey, eq_comm]

omit hg in
theorem any_refs {P : Instr → Bool} {k : Bool} {n : String} (hP : ∀ i, P i = true ↔ refKey i = some (k, n))
    (f : Func) : (f.blocks.any fun b => b.instrs.any P) = decide ((k, n) ∈ funcRefs f) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_refs_iff]
  simp only [Array.any_eq_true, ← hP]
  constructor
  · rintro ⟨j, hj, k, hk, h⟩
    exact ⟨_, Array.getElem_mem_toList hj, _, Array.getElem_mem_toList hk, h⟩
  · rintro ⟨b, hb, i, hi, h⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    exact ⟨j, by simpa using hj, k, by simpa using hk, by simpa using h⟩

omit hg in
theorem any_congr_refs {P : Instr → Bool} {k : Bool} {n : String}
    (hP : ∀ i, P i = true ↔ refKey i = some (k, n)) {f f' : Func} (h : funcRefs f' = funcRefs f) :
    (f'.blocks.any fun b => b.instrs.any P) = (f.blocks.any fun b => b.instrs.any P) := by
  rw [any_refs hP, any_refs hP, h]

omit hg in
theorem any_congr_mem {P : Instr → Bool} {k : Bool} {n : String}
    (hP : ∀ i, P i = true ↔ refKey i = some (k, n)) {f f' : Func}
    (h : (k, n) ∈ funcRefs f' ↔ (k, n) ∈ funcRefs f) :
    (f'.blocks.any fun b => b.instrs.any P) = (f.blocks.any fun b => b.instrs.any P) := by
  rw [any_refs hP, any_refs hP]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact h

theorem taken_eq (n : String) : taken (mapFuncs g us) n = taken us n := by
  simp only [taken, mapFuncs, Array.any_map]
  congr 1; funext u
  simp only [Function.comp_def, Array.any_map]
  congr 2; funext f
  exact any_congr_mem (k := true) (n := n) (fun i => by cases i <;> simp [refKey]) (hg.addrs f n)

theorem target_eq (P : Placement) (v : Lir.Word) (n r : Nat) :
    target (mapFuncs g us) P v n r = (target us P v n r).map g := by
  simp [target, funcDefs_eq hg, List.find?_map, taken_eq hg, hg.name, hg.params,
    hg.results]

theorem enter_eq (f : Func) (vals : List Lir.Word) : enter (g f) vals = enter f vals := by
  simp [enter, hg.params]

/-- A symbol no unit defines: no function and no data object in force. -/
def Undefined (us : Array Mir.Unit) (n : String) : Prop := funcOf us n = none ∧ dataOf us n = none

omit hg in
theorem funcRefs_of {f : Func} {b : Block} {i : Instr} {s : String} (hb : b ∈ f.blocks.toList)
    (hi : i ∈ b.instrs.toList) (hs : s ∈ instrRefs i) : ∃ k, (k, s) ∈ funcRefs f := by
  obtain ⟨k, hk⟩ := (instrRefs_iff i s).mp hs
  exact ⟨k, (mem_refs_iff f k s).mpr ⟨b, hb, i, hi, hk⟩⟩

/-- **A pass that drops only references to undefined symbols keeps the reachable defined
symbols**: what the input reaches, the output reaches, or it is undefined. -/
theorem reach_of (hd : ∀ f k n, (k, n) ∈ funcRefs f → (k, n) ∈ funcRefs (g f) ∨ Undefined us n)
    {s : String} (h : Reach us s) : Reach (mapFuncs g us) s ∨ Undefined us s := by
  induction h with
  | entry hf =>
    refine .inl ((hg.name _) ▸ .entry (f := g _) ?_)
    rw [funcDefs_eq hg, List.head?_map, hf]; rfl
  | @func n s f b i _ hf hb hi hs ih =>
    have hn : Reach (mapFuncs g us) n := ih.resolve_right fun hu => by simp [hu.1] at hf
    obtain ⟨k, hk⟩ := funcRefs_of hb hi hs
    rcases hd f k s hk with hk' | hu
    · obtain ⟨b', hb', i', hi', hi'k⟩ := (mem_refs_iff (g f) k s).mp hk'
      exact .inl (.func hn (by rw [funcOf_eq hg, hf]; rfl) hb' hi'
        ((instrRefs_iff i' s).mpr ⟨k, hi'k⟩))
    · exact .inr hu
  | data _ hdn hr ih =>
    have hn := ih.resolve_right fun hu => by simp [hu.2] at hdn
    exact .inl (.data hn (by rw [dataOf_eq hg]; exact hdn) hr)

/-- A valid placement of such an output is a valid placement of its input. -/
theorem valid_of (hd : ∀ f k n, (k, n) ∈ funcRefs f → (k, n) ∈ funcRefs (g f) ∨ Undefined us n)
    {m : Nat} {P : Placement} (hP : P.Valid (mapFuncs g us) m) : P.Valid us m := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  simp only [dataOf_eq hg, dataDefs_eq hg, funcOf_eq hg, Option.isSome_map] at h1 h2 h3 h4
  refine ⟨fun s hs hd' => ?_, fun s hs hn hf => ?_, h3, h4, h5, h6, h7⟩
  · rcases reach_of hg us hd hs with hr | hu
    · exact h1 s hr hd'
    · simp [hu.2] at hd'
  · rcases reach_of hg us hd hs with hr | hu
    · exact h2 s hr hn hf
    · simp [hu.1] at hf

end Iface

section Shape

variable {g : Func → Func} (hg : Shape g) (us : Array Mir.Unit)
include hg

theorem reach_iff (s : String) : Reach (mapFuncs g us) s ↔ Reach us s := by
  have key : ∀ f : Func, ∀ s, (∃ b ∈ (g f).blocks.toList, ∃ i ∈ b.instrs.toList, s ∈ instrRefs i) ↔
      (∃ b ∈ f.blocks.toList, ∃ i ∈ b.instrs.toList, s ∈ instrRefs i) := by
    intro f s
    have := fun k => (mem_refs_iff (g f) k s).symm.trans ((hg.refs f) ▸ mem_refs_iff f k s)
    simp only [instrRefs_iff]
    constructor
    · rintro ⟨b, hb, i, hi, k, hk⟩
      exact ((this k).mp ⟨b, hb, i, hi, hk⟩).elim fun b' ⟨hb', i', hi', h'⟩ => ⟨b', hb', i', hi', k, h'⟩
    · rintro ⟨b, hb, i, hi, k, hk⟩
      exact ((this k).mpr ⟨b, hb, i, hi, hk⟩).elim fun b' ⟨hb', i', hi', h'⟩ => ⟨b', hb', i', hi', k, h'⟩
  constructor
  · intro h
    induction h with
    | entry hf =>
      rw [funcDefs_eq hg.iface, List.head?_map] at hf
      obtain ⟨f, hf', rfl⟩ := Option.map_eq_some_iff.mp hf
      rw [hg.name]; exact .entry hf'
    | func _ hf hb hi hs ih =>
      rw [funcOf_eq hg.iface] at hf
      obtain ⟨f, hf', rfl⟩ := Option.map_eq_some_iff.mp hf
      obtain ⟨b', hb', i', hi', hs'⟩ := (key f _).mp ⟨_, hb, _, hi, hs⟩
      exact .func ih hf' hb' hi' hs'
    | data _ hd hr ih =>
      rw [dataOf_eq hg.iface] at hd
      exact .data ih hd hr
  · intro h
    induction h with
    | entry hf =>
      refine (hg.name _) ▸ .entry (f := g _) ?_
      rw [funcDefs_eq hg.iface, List.head?_map, hf]; rfl
    | func _ hf hb hi hs ih =>
      obtain ⟨b', hb', i', hi', hs'⟩ := (key _ _).mpr ⟨_, hb, _, hi, hs⟩
      exact .func ih (by rw [funcOf_eq hg.iface, hf]; rfl) hb' hi' hs'
    | data _ hd hr ih =>
      exact .data ih (by rw [dataOf_eq hg.iface]; exact hd) hr

theorem valid_iff (m : Nat) (P : Placement) : P.Valid (mapFuncs g us) m ↔ P.Valid us m := by
  simp only [Placement.Valid, reach_iff hg, dataOf_eq hg.iface, dataDefs_eq hg.iface, funcOf_eq hg.iface,
    Option.isSome_map]

end Shape

/-! ## The simulation obligations -/

/-- A point relation: `PR f l i fr i' fr'` relates the point `(l, i)` of `f` with frame
`fr` to the point `(l, i')` of the transformed function with frame `fr'`. -/
abbrev PointRel := Func → Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop

/-- After a call at `i` (input) and `i'` (output): the frames that receive the same results
are related at the next points. -/
def RetSim (Q : Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop) (i : Nat) (fr : Lir.Frame Nat)
    (i' : Nat) (fr' : Lir.Frame Nat) (res : List Nat) : Prop :=
  ∀ vals fr₁ fr₁', fr.writeAll (res.map .reg) vals = some fr₁ →
    fr'.writeAll (res.map .reg) vals = some fr₁' → Q (i + 1) fr₁ (i' + 1) fr₁'

/-- One input instruction `x` at `i` (frame `fr`, memory `m`) and the output's instruction
`y` at `i'` (frame `fr'`, same memory): an operation is deleted (`y` unused, memory
unchanged) or matched by an operation, any other instruction by one of the same kind. -/
def InstrSim (Q : Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop) (i : Nat) (fr : Lir.Frame Nat)
    (i' : Nat) (fr' : Lir.Frame Nat) : Instr → Option Instr → Prop
  | .op o, y => ∀ m fr₁ m₁, o.exec fr m = some (fr₁, m₁) →
      (m₁ = m ∧ Q (i + 1) fr₁ i' fr') ∨
      ∃ o', y = some (.op o') ∧ ∃ fr₁', o'.exec fr' m = some (fr₁', m₁) ∧ Q (i + 1) fr₁ (i' + 1) fr₁'
  | .fop op d a b, y => ∀ fr₁, Lir.FOp.exec op d a b fr = some fr₁ →
      ∃ op' d' a' b', y = some (.fop op' d' a' b') ∧
        ∃ fr₁', Lir.FOp.exec op' d' a' b' fr' = some fr₁' ∧ Q (i + 1) fr₁ (i' + 1) fr₁'
  | .addr d sym off, y => y = some (.addr d sym off) ∧ ∀ w, Q (i + 1) (fr.set d w) (i' + 1) (fr'.set d w)
  | .call c args res, y => ∀ vals, fr.readAll (args.map .reg) = some vals →
      ∃ args', y = some (.call c args' res) ∧ fr'.readAll (args'.map .reg) = some vals ∧
        RetSim Q i fr i' fr' res
  | .callIndirect t args res, y => ∀ v vals, fr.get t = some v → fr.readAll (args.map .reg) = some vals →
      ∃ t' args', y = some (.callIndirect t' args' res) ∧ fr'.get t' = some v ∧
        fr'.readAll (args'.map .reg) = some vals ∧ RetSim Q i fr i' fr' res

/-- The outcome of a terminator in a frame. -/
inductive TermOut where
  | goto (l : Nat)
  | ret (vals : List Lir.Word)
  | trap
  | stuck
  deriving DecidableEq

def termOut (fr : Lir.Frame Nat) : Lir.Term Nat → TermOut
  | .jump l => .goto l
  | .branch c l₁ l₂ =>
    match fr.get c with
    | some x => .goto (if x = 0 then l₂ else l₁)
    | none => .stuck
  | .ret locs =>
    match fr.readAll locs with
    | some vals => .ret vals
    | none => .stuck
  | .trap => .trap

/-- A terminator and its output: the same outcome, and related entry points after a jump
(`Q l fr fr'` relates the starts of block `l`). -/
def TermSim (Q : Nat → Lir.Frame Nat → Lir.Frame Nat → Prop) (fr fr' : Lir.Frame Nat)
    (t t' : Lir.Term Nat) : Prop :=
  termOut fr t ≠ .stuck → termOut fr' t' = termOut fr t ∧ ∀ l, termOut fr t = .goto l → Q l fr fr'

/-- The obligations of a function `f` and its output `f'`, with the point relation
`Q l i fr i' fr'`. -/
structure FSim (f f' : Func) (Q : Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop) : Prop where
  /-- Function entry: a fresh frame is related to itself. -/
  entry : ∀ fr, Q 0 0 fr 0 fr
  /-- At an input instruction. -/
  instr : ∀ l b b' i fr i' fr' x, f.blocks[l]? = some b → f'.blocks[l]? = some b' →
    Q l i fr i' fr' → b.instrs[i]? = some x →
    InstrSim (Q l) i fr i' fr' x b'.instrs[i']?
  /-- At an input terminator. -/
  term : ∀ l b b' i fr i' fr', f.blocks[l]? = some b → f'.blocks[l]? = some b' →
    Q l i fr i' fr' → i = b.instrs.size →
    i' = b'.instrs.size ∧ TermSim (fun l fr fr' => Q l 0 fr 0 fr') fr fr' b.term b'.term

/-- The obligations of a function-local pass `g` with point relation `PR`. -/
def Sim (g : Func → Func) (PR : PointRel) : Prop := ∀ f, FSim f (g f) (PR f)

/-- The identity relation: same index, same frame. -/
def idRel : Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Prop :=
  fun _ i fr i' fr' => i' = i ∧ fr' = fr

/-- A function left unchanged (a checker's fallback) simulates itself. -/
theorem FSim.id (f : Func) : FSim f f idRel where
  entry _ := ⟨rfl, rfl⟩
  instr l b b' i fr i' fr' x hb hb' hp hx := by
    obtain ⟨rfl, rfl⟩ := hp
    rw [hb] at hb'; cases hb'
    rw [hx]
    cases x with
    | op o => exact fun m fr₁ m₁ he => .inr ⟨o, rfl, fr₁, he, rfl, rfl⟩
    | fop op d a c => exact fun fr₁ he => ⟨op, d, a, c, rfl, fr₁, he, rfl, rfl⟩
    | addr d s off => exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    | call c args res =>
      exact fun vals hv => ⟨args, rfl, hv, fun _ _ _ hw hw' => by rw [hw] at hw'; cases hw'; exact ⟨rfl, rfl⟩⟩
    | callIndirect t args res =>
      exact fun v vals ht hv => ⟨t, args, rfl, ht, hv,
        fun _ _ _ hw hw' => by rw [hw] at hw'; cases hw'; exact ⟨rfl, rfl⟩⟩
  term l b b' i fr i' fr' hb hb' hp hi := by
    obtain ⟨rfl, rfl⟩ := hp
    rw [hb] at hb'; cases hb'
    exact ⟨hi, fun _ => ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩

/-! ## The simulation -/

section Simulation

variable {g : Func → Func} {PR : PointRel}

/-- A suspended input caller and its output. -/
def ActRel (g : Func → Func) (PR : PointRel) (a a' : Act) : Prop :=
  a'.func = g a.func ∧ a'.label = a.label ∧ a'.results = a.results ∧
    RetSim (PR a.func a.label) a.index a.frame a'.index a'.frame a.results

/-- An input state and its output. -/
def Rel (g : Func → Func) (PR : PointRel) (s t : State) : Prop :=
  t.func = g s.func ∧ t.label = s.label ∧ t.mem = s.mem ∧
    PR s.func s.label s.index s.frame t.index t.frame ∧ List.Forall₂ (ActRel g PR) s.stack t.stack

/-- The instructions left in the current block. -/
def measure (s : State) : Nat :=
  match s.func.blocks[s.label]? with
  | some b => b.instrs.size - s.index
  | none => 0

/-- What the output does from `t` when the input's step from `s` gives `r`. -/
inductive Match (us us' : Array Mir.Unit) (P : Placement) (g : Func → Func) (PR : PointRel)
    (s t : State) : Result → Prop
  | run {s₁ t₁ : State} : step us' P t = .running t₁ → Rel g PR s₁ t₁ → Match us us' P g PR s t (.running s₁)
  | stutter {s₁ : State} : Rel g PR s₁ t → measure s₁ < measure s → Match us us' P g PR s t (.running s₁)
  | returned {vs m} : step us' P t = .returned vs m → Match us us' P g PR s t (.returned vs m)
  | trapped {m} : step us' P t = .trapped m → Match us us' P g PR s t (.trapped m)

theorem step_term (us : Array Mir.Unit) (P : Placement) (s : State) (b : Block)
    (hb : s.func.blocks[s.label]? = some b) (hi : s.index = b.instrs.size) :
    step us P s =
      match termOut s.frame b.term with
      | .goto l => .running { s with label := l, index := 0 }
      | .ret vals =>
        match s.stack with
        | [] => .returned vals s.mem
        | a :: rest =>
          match a.frame.writeAll (a.results.map .reg) vals with
          | some fr => .running ⟨a.func, a.label, a.index + 1, fr, rest, s.mem⟩
          | none => .stuck
      | .trap => .trapped s.mem
      | .stuck => .stuck := by
  have hn : b.instrs[b.instrs.size]? = none := by simp
  simp only [step, hb, hi, hn, ne_eq, not_true_eq_false, ↓reduceIte]
  cases b.term with
  | jump l => rfl
  | branch c l₁ l₂ => simp only [termOut]; cases s.frame.get c <;> rfl
  | ret locs =>
    simp only [termOut]
    cases s.frame.readAll locs <;> rfl
  | trap => rfl

theorem writeAll_some_of {fr₁ fr₂ fr : Lir.Frame Nat} {rs : List Nat} {vals : List Lir.Word}
    (h : fr₁.writeAll (rs.map .reg) vals = some fr) : ∃ fr', fr₂.writeAll (rs.map .reg) vals = some fr' :=
  Option.isSome_iff_exists.mp (LinkCorrect.writeAll_isSome (LinkCorrect.writeAll_length h))

variable (hg : Iface g) (hs : Sim g PR) (us : Array Mir.Unit) (P : Placement)
include hg hs

/-- The one-step simulation, and the equal final results. -/
theorem step_match {s t : State} (hr : Rel g PR s t) (hstuck : step us P s ≠ .stuck) :
    Match us (mapFuncs g us) P g PR s t (step us P s) := by
  obtain ⟨hf, hl, hm, hp, hst⟩ := hr
  obtain ⟨func, label, index, frame, stack, mem⟩ := s
  obtain ⟨tfunc, tlabel, tindex, tframe, tstack, tmem⟩ := t
  simp only at hf hl hm hp hst
  subst hf; subst tlabel; subst tmem
  cases hb : func.blocks[label]? with
  | none => exact absurd (by simp [step, hb]) hstuck
  | some b =>
  obtain ⟨b', hb'⟩ : ∃ b', (g func).blocks[label]? = some b' := by
    have hlt : label < func.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    exact ⟨_, Array.getElem?_eq_getElem (by rw [hg.size]; exact hlt)⟩
  cases hx : b.instrs[index]? with
  | some x =>
    have hlt : index < b.instrs.size := (Array.getElem?_eq_some_iff.mp hx).1
    have hsim := (hs func).instr label b b' index frame tindex tframe x hb hb' hp hx
    cases x with
    | op o =>
      cases he : o.exec frame mem with
      | none => exact absurd (by simp [step, hb, hx, he]) hstuck
      | some p =>
        obtain ⟨fr₁, m₁⟩ := p
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, fr₁, stack, m₁⟩ := by simp [step, hb, hx, he]
        rw [hstep]
        rcases hsim mem fr₁ m₁ he with ⟨rfl, hq⟩ | ⟨o', hy, fr₁', he', hq⟩
        · refine .stutter ⟨rfl, rfl, rfl, hq, hst⟩ ?_
          simp only [measure, hb]; omega
        · refine .run (t₁ := ⟨g func, label, tindex + 1, fr₁', tstack, m₁⟩) ?_ ⟨rfl, rfl, rfl, hq, hst⟩
          simp [step, hb', hy, he']
    | fop op d a c =>
      cases he : Lir.FOp.exec op d a c frame with
      | none => exact absurd (by simp [step, hb, hx, he]) hstuck
      | some fr₁ =>
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, fr₁, stack, mem⟩ := by simp [step, hb, hx, he]
        rw [hstep]
        obtain ⟨op', d', a', c', hy, fr₁', he', hq⟩ := hsim fr₁ he
        refine .run (t₁ := ⟨g func, label, tindex + 1, fr₁', tstack, mem⟩) ?_ ⟨rfl, rfl, rfl, hq, hst⟩
        simp [step, hb', hy, he']
    | addr d sym off =>
      obtain ⟨hy, hq⟩ := hsim
      cases hv : symValue us P sym with
      | none => exact absurd (by simp [step, hb, hx, hv]) hstuck
      | some v =>
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, frame.set d (BitVec.ofNat 64 (v + off)), stack, mem⟩ := by
          simp [step, hb, hx, hv]
        rw [hstep]
        refine .run (t₁ := ⟨g func, label, tindex + 1, tframe.set d (BitVec.ofNat 64 (v + off)), tstack, mem⟩)
          ?_ ⟨rfl, rfl, rfl, hq _, hst⟩
        simp [step, hb', hy, symValue_eq hg, hv]
    | call c args res =>
      cases hfn : funcOf us c with
      | none => exact absurd (by simp [step, hb, hx, hfn]) hstuck
      | some fn =>
      cases hv : frame.readAll (args.map .reg) with
      | none => exact absurd (by simp [step, hb, hx, hfn, hv]) hstuck
      | some vals =>
      cases hen : enter fn vals with
      | none => exact absurd (by simp [step, hb, hx, hfn, hv, call, hen]) hstuck
      | some fr₀ =>
      have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
          .running ⟨fn, 0, 0, fr₀, ⟨func, label, index, frame, res⟩ :: stack, mem⟩ := by
        simp [step, hb, hx, hfn, hv, call, hen]
      rw [hstep]
      obtain ⟨args', hy, hv', hret⟩ := hsim vals hv
      refine .run (t₁ := ⟨g fn, 0, 0, fr₀, ⟨g func, label, tindex, tframe, res⟩ :: tstack, mem⟩) ?_
        ⟨rfl, rfl, rfl, (hs fn).entry fr₀, .cons ⟨rfl, rfl, rfl, hret⟩ hst⟩
      simp [step, hb', hy, funcOf_eq hg, hfn, hv', call, enter_eq hg, hen]
    | callIndirect tr args res =>
      cases htr : frame.get tr with
      | none => exact absurd (by simp [step, hb, hx, htr]) hstuck
      | some v =>
      cases hv : frame.readAll (args.map .reg) with
      | none => exact absurd (by simp [step, hb, hx, htr, hv]) hstuck
      | some vals =>
      cases hfn : target us P v args.length res.length with
      | none => exact absurd (by simp [step, hb, hx, htr, hv, hfn]) hstuck
      | some fn =>
      cases hen : enter fn vals with
      | none => exact absurd (by simp [step, hb, hx, htr, hv, hfn, call, hen]) hstuck
      | some fr₀ =>
      have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
          .running ⟨fn, 0, 0, fr₀, ⟨func, label, index, frame, res⟩ :: stack, mem⟩ := by
        simp [step, hb, hx, htr, hv, hfn, call, hen]
      rw [hstep]
      obtain ⟨tr', args', hy, htr', hv', hret⟩ := hsim v vals htr hv
      have hlen : args'.length = args.length := by
        have h1 := LinkCorrect.readAll_length hv
        have h2 := LinkCorrect.readAll_length hv'
        simp only [List.length_map] at h1 h2
        omega
      refine .run (t₁ := ⟨g fn, 0, 0, fr₀, ⟨g func, label, tindex, tframe, res⟩ :: tstack, mem⟩) ?_
        ⟨rfl, rfl, rfl, (hs fn).entry fr₀, .cons ⟨rfl, rfl, rfl, hret⟩ hst⟩
      simp [step, hb', hy, htr', hv', hlen, target_eq hg, hfn, call, enter_eq hg, hen]
  | none =>
    by_cases hi : index = b.instrs.size
    swap
    · exact absurd (by simp [step, hb, hx, hi]) hstuck
    obtain ⟨hi', hterm⟩ := (hs func).term label b b' index frame tindex tframe hb hb' hp hi
    have hstep' := step_term (mapFuncs g us) P ⟨g func, label, tindex, tframe, tstack, mem⟩ b' hb' hi'
    rw [step_term us P ⟨func, label, index, frame, stack, mem⟩ b hb hi] at hstuck ⊢
    cases hout : termOut frame b.term with
    | stuck => simp [hout] at hstuck
    | goto l =>
      obtain ⟨hout', hq⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      exact .run hstep' ⟨rfl, rfl, rfl, hq l hout, hst⟩
    | trap =>
      obtain ⟨hout', -⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      exact .trapped hstep'
    | ret vals =>
      obtain ⟨hout', -⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      rw [hout] at hstuck
      cases hst with
      | nil => exact .returned hstep'
      | @cons a a' rest rest' ha hrest =>
        obtain ⟨haf, hal, har, hret⟩ := ha
        simp only at hstep' hstuck ⊢
        cases hw : a.frame.writeAll (a.results.map .reg) vals with
        | none => simp [hw] at hstuck
        | some fr₁ =>
        obtain ⟨fr₁', hw'⟩ := writeAll_some_of (fr₂ := a'.frame) hw
        rw [har, hw'] at hstep'
        exact .run hstep' ⟨haf, hal, rfl, hret vals fr₁ fr₁' hw hw', hrest⟩

/-- `Rel` is a forward simulation of `MirSem.Step`. -/
def forwardSim : ForwardSim (Step us P) (Step (mapFuncs g us) P) (Rel g PR) where
  measure := measure
  step := by
    intro s s₁ t hstep hr
    have hm := step_match hg hs us P hr (by rw [hstep]; simp)
    rw [hstep] at hm
    cases hm with
    | run ht hr₁ => exact ⟨_, .inl (.single ht), hr₁⟩
    | stutter hr₁ hlt => exact ⟨t, .inr ⟨rfl, hlt⟩, hr₁⟩

/-- The output of a related state has the input's behaviour, unless the input is stuck. -/
theorem behaves {s t : State} (hr : Rel g PR s t) {b : Lir.Behavior} (hb : Behaves us P s b)
    (hns : b ≠ .stuck) : Behaves (mapFuncs g us) P t b := by
  have sim := forwardSim hg hs us P
  cases b with
  | stuck => exact absurd rfl hns
  | diverges => exact sim.diverges hb hr
  | returned vs m =>
    obtain ⟨s₁, hs₁, hf⟩ := hb
    obtain ⟨t₁, ht₁, hr₁⟩ := sim.steps hs₁ hr
    have hm := step_match hg hs us P hr₁ (by rw [hf]; simp)
    rw [hf] at hm
    cases hm with
    | returned h => exact ⟨t₁, ht₁, h⟩
  | trapped m =>
    obtain ⟨s₁, hs₁, hf⟩ := hb
    obtain ⟨t₁, ht₁, hr₁⟩ := sim.steps hs₁ hr
    have hm := step_match hg hs us P hr₁ (by rw [hf]; simp)
    rw [hf] at hm
    cases hm with
    | trapped h => exact ⟨t₁, ht₁, h⟩

end Simulation

/-- **A function-local pass with a forward simulation refines its input**, in the general
form: the function map `G us` may depend on the units it rewrites, and may drop references,
as long as every valid placement of the output is one of the input (`valid_of`). -/
theorem mirPass_of {G : Array Mir.Unit → Func → Func} {PR : Array Mir.Unit → PointRel}
    (hg : ∀ us, Iface (G us)) (hs : ∀ us, Sim (G us) (PR us))
    (hv : ∀ us m (P : Placement), P.Valid (mapFuncs (G us) us) m → P.Valid us m) :
    Contract.mirPass fun us => mapFuncs (G us) us := by
  intro us
  have hg := hg us
  have hs := hs us
  refine ⟨fun base => (need_eq us base).le, fun memSize _ P hP => ?_⟩
  refine ⟨P, hv us memSize P hP, fun s hs₀ => ?_⟩
  have hstart : start (mapFuncs (G us) us) P memSize =
      some { s with func := G us s.func, stack := [] } := by
    simp only [start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs₀
    obtain ⟨fn, hfn, fr, hfr, rfl⟩ := hs₀
    simp [start, funcDefs_eq hg, List.head?_map, hfn, enter_eq hg, hfr, initMem_eq hg]
  have hr : Rel (G us) (PR us) s { s with func := G us s.func, stack := [] } := by
    simp only [start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs₀
    obtain ⟨fn, -, fr, -, rfl⟩ := hs₀
    exact ⟨rfl, rfl, rfl, (hs fn).entry fr, .nil⟩
  refine ⟨⟨_, hstart⟩, fun t ht b hb => ?_⟩
  rw [hstart] at ht
  obtain rfl := Option.some.inj ht
  obtain ⟨b', hb'⟩ := Behaves.exists us P s
  refine ⟨b', hb', ?_⟩
  by_cases hns : b' = .stuck
  · exact .inl hns
  · exact .inr (Behaves.unique (behaves hg hs us P hr hb' hns) hb)

/-- **A function-local pass with a forward simulation refines its input.** -/
theorem mirPass {g : Func → Func} {PR : PointRel} (hg : Shape g) (hs : Sim g PR) :
    Contract.mirPass (mapFuncs g) :=
  mirPass_of (G := fun _ => g) (PR := fun _ => PR) (fun _ => hg.iface) (fun _ => hs)
    fun us m P => (valid_iff hg us m P).mp

end Silmaril.Compile.Mir.FuncPass
