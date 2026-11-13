module

public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
# A faster runner for Lir, equal to `Lir.run`

`Lir.Frame` keeps registers and slots as functions, so every write wraps a closure and a read
walks all earlier writes of the frame: `Lir.run` is quadratic in the length of a loop; and
`Prog.fetch` indexes lists. `Lir.Memory` is a function too, so a load walks every earlier store.
`FastLir` is the same stepper with frames as hash maps, memory as the bytes stored since the start
in a hash map over the start memory (`Mem`), fetching from the program's code in arrays (`table`,
`fetch_table`). An abstraction `abs` maps its states to Lir's, and one step commutes with it
(`step_abs`), so the fast runner computes `Lir.run` exactly (`run_abs`): its returned and trapped
results are Lir behaviours with no other argument.
-/

namespace Silmaril.Compile.C.Sem.FastLir

open Silmaril.Machine Silmaril.Machine.Lir

/-- A frame: registers and slots in hash maps. -/
structure Frame where
  regs : Std.HashMap Nat Word := {}
  slots : Std.HashMap Nat Word := {}

namespace Frame

/-- Lir's frame of a fast frame. -/
def abs (f : Frame) : Lir.Frame Nat := ⟨fun r => f.regs[r]?, fun n => f.slots[n]?⟩

def set (f : Frame) (r : Nat) (w : Word) : Frame := { f with regs := f.regs.insert r w }

def setSlot (f : Frame) (n : Nat) (w : Word) : Frame := { f with slots := f.slots.insert n w }

def read (f : Frame) : Loc Nat → Option Word
  | .reg r => f.regs[r]?
  | .slot n => f.slots[n]?

def write (f : Frame) : Loc Nat → Word → Frame
  | .reg r, w => f.set r w
  | .slot n, w => f.setSlot n w

def readAll (f : Frame) (locs : List (Loc Nat)) : Option (List Word) := locs.mapM f.read

def writeAll (f : Frame) : List (Loc Nat) → List Word → Option Frame
  | [], [] => some f
  | l :: ls, v :: vs => (f.write l v).writeAll ls vs
  | _, _ => none

theorem abs_set (f : Frame) (r : Nat) (w : Word) : (f.set r w).abs = f.abs.set r w := by
  simp only [abs, set, Lir.Frame.set, Std.HashMap.getElem?_insert, beq_iff_eq]
  congr 1
  funext r'
  by_cases h : r' = r <;> simp [h, Ne.symm]

theorem abs_setSlot (f : Frame) (n : Nat) (w : Word) :
    (f.setSlot n w).abs = f.abs.setSlot n w := by
  simp only [abs, setSlot, Lir.Frame.setSlot, Std.HashMap.getElem?_insert, beq_iff_eq]
  congr 1
  funext n'
  by_cases h : n' = n <;> simp [h, Ne.symm]

theorem abs_read (f : Frame) : f.abs.read = f.read := by
  funext l; cases l <;> rfl

theorem abs_write (f : Frame) (l : Loc Nat) (w : Word) : (f.write l w).abs = f.abs.write l w := by
  cases l
  · exact abs_set f _ w
  · exact abs_setSlot f _ w

theorem abs_readAll (f : Frame) (locs : List (Loc Nat)) : f.abs.readAll locs = f.readAll locs := by
  simp only [Lir.Frame.readAll, readAll, abs_read]

theorem abs_writeAll (f : Frame) (ls : List (Loc Nat)) (vs : List Word) :
    f.abs.writeAll ls vs = (f.writeAll ls vs).map abs := by
  induction ls generalizing f vs with
  | nil => cases vs <;> rfl
  | cons l ls ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [Lir.Frame.writeAll, writeAll]
      rw [← abs_write, ih]

end Frame

/-- A memory: the bytes stored since the start, in a hash map over the start memory `base`. -/
structure Mem where
  base : Memory
  over : Std.HashMap Nat Byte := {}

namespace Mem

/-- The byte at an address. -/
def byte (m : Mem) (a : Nat) : Byte := m.over[a]?.getD (m.base.bytes a)

/-- Lir's memory of a fast memory. -/
def abs (m : Mem) : Memory := ⟨m.base.size, m.byte⟩

/-- The bytes `0 … n - 1` of `value` stored from `addr`.

Insert before the recursive call so the accumulator is consumed: inserting into the result
of a recursive call makes the compiler borrow `o` and retain it through every store, forcing
a copy of the hash map's bucket array. The distinct byte addresses permit reverse order. -/
def writeOver (o : Std.HashMap Nat Byte) (addr : Nat) (value : Word) : Nat → Std.HashMap Nat Byte
  | 0 => o
  | n + 1 => writeOver (o.insert (addr + n) (LittleEndian.wordByte value n)) addr value n

theorem getElem?_writeOver (o : Std.HashMap Nat Byte) (addr : Nat) (value : Word) (n a : Nat) :
    (writeOver o addr value n)[a]? =
      if addr ≤ a ∧ a < addr + n then some (LittleEndian.wordByte value (a - addr)) else o[a]? := by
  induction n generalizing o with
  | zero => simp [writeOver]
  | succ n ih =>
    simp only [writeOver, Std.HashMap.getElem?_insert, beq_iff_eq, ih]
    by_cases h : addr + n = a
    · subst h; simp
    · have he : (addr ≤ a ∧ a < addr + (n + 1)) ↔ (addr ≤ a ∧ a < addr + n) := by omega
      simp [h, he]

def load (m : Mem) (width : Width) (ext : Ext) (addr : Nat) : Option Word :=
  m.abs.load width ext addr

def store (m : Mem) (width : Width) (addr : Nat) (value : Word) : Option Mem :=
  if addr + width.bytes ≤ m.base.size then
    some { m with over := writeOver m.over addr value width.bytes }
  else none

theorem abs_store (m : Mem) (width : Width) (addr : Nat) (value : Word) :
    m.abs.store width addr value = (m.store width addr value).map abs := by
  unfold Memory.store store
  by_cases h : addr + width.bytes ≤ m.base.size
  · simp only [Memory.InBounds, abs, h, ite_true, Option.map_some, Option.some.injEq]
    congr 1
    funext a
    simp only [writeLE, byte, getElem?_writeOver]
    split <;> rfl
  · simp [Memory.InBounds, abs, h]

/-- The fast memory of a start memory. -/
def ofMemory (m : Memory) : Mem := { base := m }

theorem abs_ofMemory (m : Memory) : (ofMemory m).abs = m := by
  cases m
  simp only [abs, ofMemory, Memory.mk.injEq, true_and]
  funext a
  simp [byte]

end Mem

/-- `Op.exec` on a fast frame. -/
def execOp : Op Nat → Frame → Mem → Option (Frame × Mem)
  | .const d v, fr, m => some (fr.set d v, m)
  | .move d s, fr, m => fr.regs[s]?.map fun x => (fr.set d x, m)
  | .unary op d s, fr, m => fr.regs[s]?.map fun x => (fr.set d (op.eval x), m)
  | .binary op d a b, fr, m =>
      fr.regs[a]?.bind fun x => fr.regs[b]?.bind fun y =>
        (op.eval x y).map fun z => (fr.set d z, m)
  | .load w e d base off, fr, m =>
      fr.regs[base]?.bind fun a => (m.load w e (a.toNat + off)).map fun z => (fr.set d z, m)
  | .store w base off src, fr, m =>
      fr.regs[base]?.bind fun a => fr.regs[src]?.bind fun x =>
        (m.store w (a.toNat + off) x).map fun m' => (fr, m')
  | .slotGet d n, fr, m => fr.slots[n]?.map fun x => (fr.set d x, m)
  | .slotSet n s, fr, m => fr.regs[s]?.map fun x => (fr.setSlot n x, m)

theorem execOp_abs (o : Op Nat) (fr : Frame) (m : Mem) :
    o.exec fr.abs m.abs = (execOp o fr m).map fun r => (r.1.abs, r.2.abs) := by
  have hg : ∀ r, fr.abs.get r = fr.regs[r]? := fun _ => rfl
  have hs : ∀ n, fr.abs.slots n = fr.slots[n]? := fun _ => rfl
  cases o with
  | const d v => simp [Op.exec, execOp, Frame.abs_set]
  | move d s => cases h : fr.regs[s]? <;> simp [Op.exec, execOp, hg, h, Frame.abs_set]
  | unary op d s => cases h : fr.regs[s]? <;> simp [Op.exec, execOp, hg, h, Frame.abs_set]
  | binary op d a b =>
    cases h : fr.regs[a]? <;> cases h' : fr.regs[b]? <;>
      simp [Op.exec, execOp, hg, h, h']
    cases op.eval _ _ <;> simp [Frame.abs_set]
  | load w e d base off =>
    cases h : fr.regs[base]? <;> simp [Op.exec, execOp, hg, h, Mem.load]
    cases m.abs.load _ _ _ <;> simp [Frame.abs_set]
  | store w base off src =>
    cases h : fr.regs[base]? <;> cases h' : fr.regs[src]? <;>
      simp [Op.exec, execOp, hg, h, h', Mem.abs_store]
    cases m.store _ _ _ <;> simp
  | slotGet d n => cases h : fr.slots[n]? <;> simp [Op.exec, execOp, hs, h, Frame.abs_set]
  | slotSet n s => cases h : fr.regs[s]? <;> simp [Op.exec, execOp, hg, h, Frame.abs_setSlot]

/-- `FOp.exec` on fast frames. -/
def execFop (op : FOp) (d a b : Nat) (fr : Frame) : Option Frame :=
  fr.regs[a]?.bind fun x => fr.regs[b]?.map fun y => fr.set d (op.eval x y)

theorem execFop_abs (op : FOp) (d a b : Nat) (fr : Frame) :
    op.exec d a b fr.abs = (execFop op d a b fr).map Frame.abs := by
  have hg : ∀ r, fr.abs.get r = fr.regs[r]? := fun _ => rfl
  cases h : fr.regs[a]? <;> cases h' : fr.regs[b]? <;>
    simp [FOp.exec, execFop, hg, h, h', Frame.abs_set]

/-! ## States and steps -/

structure Activation where
  point : Point
  frame : Frame

structure State where
  point : Point
  frame : Frame
  stack : List Activation
  mem : Mem

def Activation.abs (a : Activation) : Lir.Activation Nat := ⟨a.point, a.frame.abs⟩

/-- Lir's state of a fast state. -/
def State.abs (s : State) : Lir.State Nat := ⟨s.point, s.frame.abs, s.stack.map (·.abs), s.mem.abs⟩

inductive Result where
  | running (s : State)
  | returned (values : List Word) (mem : Mem)
  | trapped (mem : Mem)
  | stuck

def Result.abs : Result → Lir.Result Nat
  | .running s => .running s.abs
  | .returned vs m => .returned vs m.abs
  | .trapped m => .trapped m.abs
  | .stuck => .stuck

theorem abs_empty : ({} : Frame).abs = Lir.Frame.empty := by
  simp only [Frame.abs, Lir.Frame.empty, Std.HashMap.getElem?_empty]

/-- `Prog.enter` with a fast frame. -/
def enter (p : Prog Nat) (f : FuncId) (vals : List Word) : Option (Point × Frame) :=
  (p.func? f).bind fun fn =>
    (({} : Frame).writeAll fn.params vals).map fun fr => (⟨f, fn.entry, 0⟩, fr)

theorem enter_abs (p : Prog Nat) (f : FuncId) (vals : List Word) :
    p.enter f vals = (enter p f vals).map fun r => (r.1, r.2.abs) := by
  simp only [Prog.enter, enter, ← abs_empty, Frame.abs_writeAll]
  cases p.func? f <;> simp
  cases Frame.writeAll _ _ _ <;> simp

/-- The code of a program in arrays: per function, per block, its instructions and terminator. -/
abbrev Table := Array (Array (Array (Instr Nat) × Term Nat))

def table (p : Prog Nat) : Table :=
  (p.funcs.map fun fn => (fn.blocks.map fun b => (b.instrs.toArray, b.term)).toArray).toArray

/-- `Prog.fetch` on the arrays of `table`. -/
def fetch (c : Table) (pt : Point) : Option (Lir.Code Nat) :=
  match c[pt.func]?.bind (·[pt.label]?) with
  | none => none
  | some (is, t) =>
    match is[pt.index]? with
    | some i => some (.instr i)
    | none => if pt.index = is.size then some (.term t) else none

theorem fetch_table (p : Prog Nat) (pt : Point) : fetch (table p) pt = p.fetch pt := by
  simp only [fetch, table, Prog.fetch, Prog.block?, Prog.func?, List.getElem?_toArray,
    List.getElem?_map]
  cases p.funcs[pt.func]? with
  | none => rfl
  | some fn =>
    simp only [Option.map_some, Option.bind_some, List.getElem?_toArray, List.getElem?_map]
    cases fn.blocks[pt.label]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.bind_some, List.getElem?_toArray, List.size_toArray]
      cases b.instrs[pt.index]? <;> rfl

/-- `Lir.step` on fast states, fetching from `c = table p`. -/
def step (c : Table) (p : Prog Nat) (s : State) : Result :=
  match fetch c s.point with
  | none => .stuck
  | some (.instr (.op o)) =>
    match execOp o s.frame s.mem with
    | some (fr, m) => .running { s with point := s.point.next, frame := fr, mem := m }
    | none => .stuck
  | some (.instr (.call f args _)) =>
    match s.frame.readAll args with
    | none => .stuck
    | some vals =>
      match enter p f vals with
      | none => .stuck
      | some (pt, fr) => .running ⟨pt, fr, ⟨s.point, s.frame⟩ :: s.stack, s.mem⟩
  | some (.instr (.fop op d a b)) =>
    match execFop op d a b s.frame with
    | some fr => .running { s with point := s.point.next, frame := fr }
    | none => .stuck
  | some (.term (.jump l)) => .running { s with point := ⟨s.point.func, l, 0⟩ }
  | some (.term (.branch c l₁ l₂)) =>
    match s.frame.regs[c]? with
    | none => .stuck
    | some x => .running { s with point := ⟨s.point.func, if x = 0 then l₂ else l₁, 0⟩ }
  | some (.term (.ret locs)) =>
    match s.frame.readAll locs with
    | none => .stuck
    | some vals =>
      match s.stack with
      | [] => .returned vals s.mem
      | a :: rest =>
        match fetch c a.point with
        | some (.instr (.call _ _ results)) =>
          match a.frame.writeAll results vals with
          | some fr => .running ⟨a.point.next, fr, rest, s.mem⟩
          | none => .stuck
        | _ => .stuck
  | some (.term .trap) => .trapped s.mem

/-- **One fast step is one Lir step.** -/
theorem step_abs (p : Prog Nat) (s : State) : Lir.step p s.abs = (step (table p) p s).abs := by
  unfold Lir.step step
  simp only [State.abs, fetch_table]
  cases p.fetch s.point with
  | none => rfl
  | some c =>
    rcases c with (o | ⟨f, args, results⟩ | ⟨op, d, a, b⟩) | (l | ⟨c, l₁, l₂⟩ | locs | _)
    · simp only [execOp_abs]
      cases execOp o s.frame s.mem with
      | none => rfl
      | some r => rfl
    · simp only [Frame.abs_readAll]
      cases s.frame.readAll args with
      | none => rfl
      | some vals =>
        simp only [enter_abs]
        cases enter p f vals with
        | none => rfl
        | some r => rfl
    · simp only [execFop_abs]
      cases execFop op d a b s.frame with
      | none => rfl
      | some r => rfl
    · rfl
    · simp only [Lir.Frame.get, Frame.abs]
      cases s.frame.regs[c]? <;> rfl
    · simp only [Frame.abs_readAll]
      cases s.frame.readAll locs with
      | none => rfl
      | some vals =>
        cases s.stack with
        | nil => rfl
        | cons a rest =>
          simp only [List.map_cons, Activation.abs]
          cases p.fetch a.point with
          | none => rfl
          | some c =>
            rcases c with (o | ⟨g, args, results⟩ | _) | t
            · rfl
            · simp only [Frame.abs_writeAll]
              cases a.frame.writeAll results vals <;> rfl
            · rfl
            · rfl
    · rfl

/-- The fuel-bounded fast runner. -/
def runWith (c : Table) (p : Prog Nat) : Nat → State → Result
  | 0, s => .running s
  | n + 1, s =>
    match step c p s with
    | .running s' => runWith c p n s'
    | r => r

/-- The fuel-bounded fast runner of a program. -/
def run (p : Prog Nat) (n : Nat) (s : State) : Result := runWith (table p) p n s

/-- **The fast runner computes `Lir.run`.** -/
theorem run_abs (p : Prog Nat) (n : Nat) (s : State) : Lir.run p n s.abs = (run p n s).abs := by
  unfold run
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Lir.run, runWith, step_abs]
    cases step (table p) p s with
    | running s' => exact ih s'
    | returned vs m => rfl
    | trapped m => rfl
    | stuck => rfl

/-- The fast start state of a whole-program run. -/
def start (p : Prog Nat) (f : FuncId) (args : List Word) (mem : Memory) : Option State :=
  (enter p f args).map fun (pt, fr) => ⟨pt, fr, [], .ofMemory mem⟩

theorem start_abs (p : Prog Nat) (f : FuncId) (args : List Word) (mem : Memory) :
    p.start f args mem = (start p f args mem).map State.abs := by
  simp only [Prog.start, start, enter_abs]
  cases enter p f args <;> simp [State.abs, Mem.abs_ofMemory]

end Silmaril.Compile.C.Sem.FastLir
