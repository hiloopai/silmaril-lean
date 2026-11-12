module

public import Silmaril.Compiler.Mir.Link.Defs
/-! # A reference interpreter for linked Mir

Mir means the Lir semantics of its link (`Silmaril.Compile.Mir.Syntax`). `Interp.run`
executes that meaning: it runs the `Lir.Prog Nat` of a `Mir.Linked` from a function,
over the linear memory holding the link's image, step by step as `Lir.step` does. It
is `Lir.run` with executable data structures in place of the semantic ones: words are
`UInt64` instead of `BitVec 64` (whose operations compute on `Nat` modulo `2 ^ 64`),
frames are arrays with a written-flag per register instead of functions, the memory is
an array of 64 KiB pages (an absent page is zeros) instead of a function `Nat → Byte`,
the code is pre-converted to arrays, and a call keeps its result locations in the
activation instead of re-fetching its instruction at the return. The operators are
proved equal to Lir's (`unop_eq`, `binop_eq`, `extend_eq`); the rare ones run as Lir's
own `eval` on the `BitVec` view.

Every stuck state of `Lir.step` (a read of an unwritten register or slot, a memory
access outside the memory, a division by zero or a signed overflow, a missing function
or block, an argument or result count mismatch) ends the run with `Outcome.stuck`,
the reason and the program point: undefined behaviour of the program, which the
backends may turn into anything. That is the use of this interpreter: a differential
test of the x86-64 runs (`ccomp --interp`), which also points at the first
undefined step of a miscompiled program.

Two checks go beyond Lir, to match the process of `tools/ccomp/runtime/crt0-*.S`: an
access below `guard` (the startup code's inaccessible NULL page) ends with
`Outcome.fault`, and more than `maxDepth` nested calls (the backends' machine-stack
limit) with `Outcome.exhausted`.

## Intended theorem

For a linked program `l`, an entry `f`, arguments `args` and fuel `n`, with `guard = 0`
and `maxDepth` unbounded: `run (load l) n (start f args mem)` is `returned vs m`,
`trapped m` or `stuck` exactly when `Lir.run l.prog n (Lir.Prog.start …)` is
`returned vs' m'`, `trapped m'` or `stuck`, where `vs' = vs.map UInt64.toBitVec` and `m`
and `m'` hold the same bytes (`Mem.toLir`); `outOfFuel` corresponds to `running`. With a guard, `fault` is
returned only from states whose Lir step is defined, and other outcomes are unchanged.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.Interp

open Silmaril.Machine
open Silmaril.Machine.Lir (Word Width Ext Cond Unop Binop divOp of32 lo32)

/-! ## Operators on `UInt64` -/

def cond : Cond → UInt64 → UInt64 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lts, x, y => x.toInt64 < y.toInt64
  | .ltu, x, y => x < y
  | .les, x, y => x.toInt64 ≤ y.toInt64
  | .leu, x, y => x ≤ y
  | .gts, x, y => x.toInt64 > y.toInt64
  | .gtu, x, y => x > y
  | .ges, x, y => x.toInt64 ≥ y.toInt64
  | .geu, x, y => x ≥ y

def cond32 : Cond → UInt32 → UInt32 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lts, x, y => x.toInt32 < y.toInt32
  | .ltu, x, y => x < y
  | .les, x, y => x.toInt32 ≤ y.toInt32
  | .leu, x, y => x ≤ y
  | .gts, x, y => x.toInt32 > y.toInt32
  | .gtu, x, y => x > y
  | .ges, x, y => x.toInt32 ≥ y.toInt32
  | .geu, x, y => x ≥ y

theorem cond_eq (c : Cond) (x y : UInt64) : cond c x y = c.eval x.toBitVec y.toBitVec := by
  cases c <;> simp [cond, Cond.eval, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
    Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le, UInt64.toBitVec_inj, bne] <;> rfl

theorem cond32_eq (c : Cond) (x y : UInt32) : cond32 c x y = c.eval x.toBitVec y.toBitVec := by
  cases c <;> simp [cond32, Cond.eval, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    Int32.lt_iff_toInt_lt, Int32.le_iff_toInt_le, UInt32.toBitVec_inj, bne] <;> rfl

def ofBool (b : Bool) : UInt64 := if b then 1 else 0

/-- `Lir.Unop.eval`. -/
def unop : Unop → UInt64 → UInt64
  | .sext8, x => x.toUInt8.toInt8.toInt64.toUInt64
  | .sext16, x => x.toUInt16.toInt16.toInt64.toUInt64
  | .sext32, x => x.toUInt32.toInt32.toInt64.toUInt64
  | .zext8, x => x.toUInt8.toUInt64
  | .zext16, x => x.toUInt16.toUInt64
  | .zext32, x => x.toUInt32.toUInt64
  | .eqz, x => ofBool (x == 0)
  | op, x => UInt64.ofBitVec (op.eval x.toBitVec)

/-- `Lir.Binop.eval`. -/
def binop : Binop → UInt64 → UInt64 → Option UInt64
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .and, x, y => some (x &&& y)
  | .or, x, y => some (x ||| y)
  | .xor, x, y => some (x ^^^ y)
  | .shl, x, y => some (x <<< y)
  | .shru, x, y => some (x >>> y)
  | .shl32, x, y => some (x.toUInt32 <<< y.toUInt32).toUInt64
  | .shru32, x, y => some (x.toUInt32 >>> y.toUInt32).toUInt64
  | .divu, x, y => if y = 0 then none else some (x / y)
  | .remu, x, y => if y = 0 then none else some (x % y)
  | .divu32, x, y => if y.toUInt32 = 0 then none else some (x.toUInt32 / y.toUInt32).toUInt64
  | .remu32, x, y => if y.toUInt32 = 0 then none else some (x.toUInt32 % y.toUInt32).toUInt64
  | .cmp c, x, y => some (ofBool (cond c x y))
  | .cmp32 c, x, y => some (ofBool (cond32 c x.toUInt32 y.toUInt32))
  | op, x, y => (op.eval x.toBitVec y.toBitVec).map UInt64.ofBitVec

/-- `Lir.extend`. -/
def extend : Width → Ext → UInt64 → UInt64
  | .b1, .sign, x => unop .sext8 x
  | .b2, .sign, x => unop .sext16 x
  | .b4, .sign, x => unop .sext32 x
  | _, _, x => x

private theorem ofBool_eq (b : Bool) : (ofBool b).toBitVec = Lir.ofBool b := by
  cases b <;> rfl

theorem unop_eq (op : Unop) (x : UInt64) : (unop op x).toBitVec = op.eval x.toBitVec := by
  cases op <;> simp only [unop, Unop.eval, UInt64.toBitVec_ofBitVec]
  · simp
  · simp
  · simp
  · apply BitVec.eq_of_toNat_eq; simp; omega
  · apply BitVec.eq_of_toNat_eq; simp; omega
  · apply BitVec.eq_of_toNat_eq; simp [of32, lo32]; omega
  · rw [ofBool_eq]; simp; rfl

set_option maxHeartbeats 40000 in
theorem binop_eq (op : Binop) (x y : UInt64) :
    binop op x y = (op.eval x.toBitVec y.toBitVec).map UInt64.ofBitVec := by
  cases op <;> simp only [binop, Binop.eval, Option.map_some]
  case add | sub | mul | and | or | xor => rfl
  case shl | shru => congr 1
  case shl32 =>
    congr 1; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    simp [of32, lo32, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (a := y.toNat % 32) (by omega)]
    rw [Nat.mod_eq_of_lt (a := x.toNat * 2 ^ (y.toNat % 32) % 4294967296) (by omega)]
  case shru32 =>
    congr 1; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    simp [of32, lo32, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := y.toNat % 32) (by omega)]
    rw [Nat.mod_eq_of_lt (a := x.toNat % 4294967296) (by omega)]
  case divu | remu =>
    by_cases h : y = 0
    · subst h; simp [divOp]
    · have h' : y.toBitVec ≠ 0 := fun e => h (UInt64.toBitVec_inj.mp e)
      simp only [h, h', divOp, ite_false, Bool.false_eq_true, Option.map_some]; rfl
  case divu32 | remu32 =>
    by_cases h : y.toUInt32 = 0
    · have h' : lo32 y.toBitVec = 0 := by
        unfold lo32; rw [← UInt64.toBitVec_toUInt32, h]; rfl
      simp [h, h', divOp]
    · have h' : lo32 y.toBitVec ≠ 0 := fun e => h (UInt32.toBitVec_inj.mp (by
        rw [UInt64.toBitVec_toUInt32]; exact e))
      simp only [h, h', divOp, ite_false, Bool.false_eq_true, Option.map_some, Option.some.injEq]
      apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
      simp [of32, lo32]
      symm; apply Nat.mod_eq_of_lt
      first
        | exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
        | exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  case cmp c => congr 1; apply UInt64.toBitVec_inj.mp; rw [ofBool_eq, cond_eq]
  case cmp32 c => congr 1; apply UInt64.toBitVec_inj.mp; rw [ofBool_eq, cond32_eq]; rfl

theorem extend_eq (w : Width) (e : Ext) (x : UInt64) :
    (extend w e x).toBitVec = Lir.extend w e x.toBitVec := by
  cases w <;> cases e <;> simp [extend, Lir.extend, unop_eq, Unop.eval, Width.bytes]

/-! ## Memory -/

/-- Memory pages are `2 ^ pageBits` bytes. -/
def pageBits : Nat := 16

def pageSize : Nat := 2 ^ pageBits

/-- The linear memory of `size` bytes, by pages; an empty page is all zeros. -/
structure Mem where
  size : Nat
  pages : Array ByteArray

namespace Mem

/-- A zero memory of `size` bytes. -/
def zero (size : Nat) : Mem := ⟨size, Array.replicate ((size + pageSize - 1) / pageSize) .empty⟩

def getByte (m : Mem) (a : Nat) : UInt8 :=
  let pg := m.pages[a >>> pageBits]!
  if pg.size = 0 then 0 else pg[a % pageSize]!

/-- Set the byte at an address below `size`. -/
def setByte (m : Mem) (a : Nat) (v : UInt8) : Mem :=
  let ⟨size, pages⟩ := m
  ⟨size, pages.modify (a >>> pageBits) fun pg =>
    let pg := if pg.size = 0 then ByteArray.mk (Array.replicate pageSize 0) else pg
    pg.set! (a % pageSize) v⟩

/-- Little-endian read of `n ≤ 8` bytes at `a`. -/
def readLE (m : Mem) (a n : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:n] do
    v := v ||| ((m.getByte (a + i)).toUInt64 <<< (8 * i).toUInt64)
  return v

/-- Little-endian write of the low `n ≤ 8` bytes of `v` at `a`. -/
def writeLE (m : Mem) (a n : Nat) (v : UInt64) : Mem := Id.run do
  let mut m := m
  for i in [0:n] do
    m := m.setByte (a + i) (v >>> (8 * i).toUInt64).toUInt8
  return m

/-- `Lir.Memory.load`, inside the memory. -/
def load (m : Mem) (w : Width) (e : Ext) (a : Nat) : UInt64 :=
  extend w e (m.readLE a w.bytes)

/-- The memory with `image` written from address `base`. -/
def ofImage (size base : Nat) (image : ByteArray) : Mem := Id.run do
  let mut m := zero size
  for i in [0:image.size] do
    if base + i < size then m := m.setByte (base + i) image[i]!
  return m

/-- The bytes `[a, a + n)` (zeros outside the memory). -/
def slice (m : Mem) (a n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    b := b.push (if a + i < m.size then m.getByte (a + i) else 0)
  return b

/-- The Lir memory with the same bytes. -/
def toLir (m : Mem) : Lir.Memory := ⟨m.size, fun a => BitVec.ofNat 8 (m.getByte a).toNat⟩

end Mem

/-! ## Code -/

structure Block where
  instrs : Array (Lir.Instr Nat)
  term : Lir.Term Nat

structure Func where
  params : List (Lir.Loc Nat)
  entry : Nat
  blocks : Array Block
  /-- More than every register the function writes: the initial size of its frames. -/
  regs : Nat

def Op.dest? : Lir.Op Nat → Option Nat
  | .const d _ | .move d _ | .unary _ d _ | .binary _ d _ _ | .load _ _ d _ _ | .slotGet d _ => some d
  | .store .. | .slotSet .. => none

def Loc.reg? : Lir.Loc Nat → Option Nat
  | .reg r => some r
  | .slot _ => none

/-- The executable form of a Lir function. -/
def Func.ofLir (f : Lir.Func Nat) : Func :=
  let dests := f.params.filterMap Loc.reg? ++ f.blocks.flatMap fun b => b.instrs.flatMap fun
    | .op o => (Op.dest? o).toList
    | .call _ _ res => res.filterMap Loc.reg?
    | .fop _ d _ _ => [d]
  { params := f.params, entry := f.entry,
    blocks := (f.blocks.map fun b => ⟨b.instrs.toArray, b.term⟩).toArray,
    regs := dests.foldl (fun n r => max n (r + 1)) 0 }

def load (p : Lir.Prog Nat) : Array Func := (p.funcs.map Func.ofLir).toArray

/-! ## Frames

A frame's registers are `vals`, with `defd[r] = 1` when register `r` was written (Lir's
`some`); slots, which only calls and returns touch, are an array of options. -/

structure Frame where
  vals : Array UInt64
  defd : ByteArray
  slots : Array (Option UInt64)

namespace Frame

def empty (n : Nat) : Frame := ⟨Array.replicate n 0, ByteArray.mk (Array.replicate n 0), #[]⟩

def get (fr : Frame) (r : Nat) : Option UInt64 :=
  if r < fr.defd.size && fr.defd[r]! != 0 then some fr.vals[r]! else none

def set (fr : Frame) (r : Nat) (w : UInt64) : Frame :=
  let ⟨vals, defd, slots⟩ := fr
  if r < vals.size && r < defd.size then ⟨vals.set! r w, defd.set! r 1, slots⟩
  else
    let n := r + 1
    let vals := vals ++ Array.replicate (n - vals.size) 0
    let defd := defd ++ ByteArray.mk (Array.replicate (n - defd.size) 0)
    ⟨vals.set! r w, defd.set! r 1, slots⟩

def getSlot (fr : Frame) (n : Nat) : Option UInt64 := fr.slots[n]?.join

def setSlot (fr : Frame) (n : Nat) (w : UInt64) : Frame :=
  let ⟨vals, defd, slots⟩ := fr
  let slots := if n < slots.size then slots else slots ++ Array.replicate (n + 1 - slots.size) none
  ⟨vals, defd, slots.set! n (some w)⟩

def read (fr : Frame) : Lir.Loc Nat → Option UInt64
  | .reg r => fr.get r
  | .slot n => fr.getSlot n

def readAll (fr : Frame) (locs : List (Lir.Loc Nat)) : Option (List UInt64) :=
  locs.mapM fr.read

/-- `Lir.Frame.writeAll`: `none` on a length mismatch. -/
def writeAll (fr : Frame) : List (Lir.Loc Nat) → List UInt64 → Option Frame
  | [], [] => some fr
  | .reg r :: ls, v :: vs => (fr.set r v).writeAll ls vs
  | .slot n :: ls, v :: vs => (fr.setSlot n v).writeAll ls vs
  | _, _ => none

end Frame

/-! ## Machine states -/

/-- A program point: function, block, instruction index (the terminator at the end). -/
structure Point where
  func : Nat
  label : Nat
  index : Nat
  deriving Repr, Inhabited

/-- A suspended caller: where to resume, its frame, and where the results go. -/
structure Activation where
  point : Point
  frame : Frame
  results : List (Lir.Loc Nat)

structure Machine where
  point : Point
  frame : Frame
  stack : Array Activation
  mem : Mem

/-- How a run ends. -/
inductive Outcome where
  /-- The entry function returned. -/
  | returned (values : List UInt64) (mem : Mem)
  /-- A `trap` terminator. -/
  | trapped (mem : Mem)
  /-- Undefined behaviour: `Lir.step` is stuck here, for this reason. -/
  | stuck (why : String) (pt : Point) (mem : Mem)
  /-- An access to address `addr`, below the guard (the process's NULL page). -/
  | fault (addr : Nat) (pt : Point) (mem : Mem)
  /-- More nested calls than the machine stack holds. -/
  | exhausted (pt : Point) (mem : Mem)
  /-- Still running when the fuel ran out. -/
  | outOfFuel (pt : Point) (mem : Mem)

def Outcome.mem : Outcome → Mem
  | .returned _ m | .trapped m | .stuck _ _ m | .fault _ _ m | .exhausted _ m | .outOfFuel _ m => m

/-! ## Steps -/

/-- Limits of the process beyond Lir's semantics (see the module docstring). -/
structure Limits where
  guard : Nat := 0
  maxDepth : Nat := 1000000

inductive Next where
  | running (m : Machine)
  | done (o : Outcome)

def regName (r : Nat) : String := s!"v{r}"

/-- A load or store of `w` at `a` in `mem`: `none` when allowed, else the outcome. -/
def checkAccess (lim : Limits) (pt : Point) (mem : Mem) (w : Width) (a : Nat) (what : String) :
    Option (Mem → Outcome) :=
  if a < lim.guard then some (.fault a pt)
  else if a + w.bytes ≤ mem.size then none
  else some (.stuck s!"{what} of {w.bytes} bytes at {a}, outside the memory of {mem.size} bytes" pt)

/-- One step of `Lir.step`. -/
def step (code : Array Func) (lim : Limits) (m : Machine) : Next :=
  let ⟨pt, fr, stack, mem⟩ := m
  let stuck (why : String) (mem : Mem) : Next := .done (.stuck why pt mem)
  match code[pt.func]? with
  | none => stuck s!"no function {pt.func}" mem
  | some fn =>
  match fn.blocks[pt.label]? with
  | none => stuck s!"no block {pt.label}" mem
  | some b =>
  let next := { pt with index := pt.index + 1 }
  match b.instrs[pt.index]? with
  | some (.op o) =>
    let unwritten (r : Nat) (mem : Mem) := stuck s!"read of unwritten register {regName r}" mem
    match o with
    | .const d v => .running ⟨next, fr.set d (UInt64.ofBitVec v), stack, mem⟩
    | .move d s =>
      match fr.get s with
      | some x => .running ⟨next, fr.set d x, stack, mem⟩
      | none => unwritten s mem
    | .unary op d s =>
      match fr.get s with
      | some x => .running ⟨next, fr.set d (unop op x), stack, mem⟩
      | none => unwritten s mem
    | .binary op d a c =>
      match fr.get a, fr.get c with
      | some x, some y =>
        match binop op x y with
        | some z => .running ⟨next, fr.set d z, stack, mem⟩
        | none => stuck s!"{repr op} of {x} by {y}: undefined" mem
      | none, _ => unwritten a mem
      | _, none => unwritten c mem
    | .load w e d base off =>
      match fr.get base with
      | none => unwritten base mem
      | some a =>
        let a := a.toNat + off
        match checkAccess lim pt mem w a "load" with
        | some o => .done (o mem)
        | none => .running ⟨next, fr.set d (mem.load w e a), stack, mem⟩
    | .store w base off src =>
      match fr.get base, fr.get src with
      | some a, some x =>
        let a := a.toNat + off
        match checkAccess lim pt mem w a "store" with
        | some o => .done (o mem)
        | none => .running ⟨next, fr, stack, mem.writeLE a w.bytes x⟩
      | none, _ => unwritten base mem
      | _, none => unwritten src mem
    | .slotGet d n =>
      match fr.getSlot n with
      | some x => .running ⟨next, fr.set d x, stack, mem⟩
      | none => stuck s!"read of unwritten slot {n}" mem
    | .slotSet n s =>
      match fr.get s with
      | some x => .running ⟨next, fr.setSlot n x, stack, mem⟩
      | none => unwritten s mem
  | some (.fop op d a c) =>
    match fr.get a, fr.get c with
    | some x, some y => .running ⟨next, fr.set d (UInt64.ofBitVec (op.eval x.toBitVec y.toBitVec)), stack, mem⟩
    | none, _ => stuck s!"read of unwritten register {regName a}" mem
    | _, none => stuck s!"read of unwritten register {regName c}" mem
  | some (.call f args results) =>
    match fr.readAll args with
    | none => stuck s!"call of function {f}: an argument is unwritten" mem
    | some vals =>
      match code[f]? with
      | none => stuck s!"call of a missing function {f}" mem
      | some callee =>
        match (Frame.empty callee.regs).writeAll callee.params vals with
        | none => stuck s!"call of function {f} with {vals.length} arguments, it has {callee.params.length}" mem
        | some cfr =>
          if stack.size ≥ lim.maxDepth then .done (.exhausted pt mem)
          else .running ⟨⟨f, callee.entry, 0⟩, cfr, stack.push ⟨pt, fr, results⟩, mem⟩
  | none =>
    if pt.index ≠ b.instrs.size then stuck s!"no instruction {pt.index}" mem else
    match b.term with
    | .jump l => .running ⟨⟨pt.func, l, 0⟩, fr, stack, mem⟩
    | .branch c l₁ l₂ =>
      match fr.get c with
      | some x => .running ⟨⟨pt.func, if x = 0 then l₂ else l₁, 0⟩, fr, stack, mem⟩
      | none => stuck s!"branch on unwritten register {regName c}" mem
    | .ret locs =>
      match fr.readAll locs with
      | none => stuck "return of an unwritten location" mem
      | some vals =>
        match stack.back? with
        | none => .done (.returned vals mem)
        | some a =>
          let stack := stack.pop
          match a.frame.writeAll a.results vals with
          | some fr => .running ⟨{ a.point with index := a.point.index + 1 }, fr, stack, mem⟩
          | none => stuck s!"return of {vals.length} values to a call expecting {a.results.length}" mem
    | .trap => .done (.trapped mem)

/-- `Lir.run`: at most `fuel` steps. -/
def run (code : Array Func) (lim : Limits) : Nat → Machine → Outcome
  | 0, m => .outOfFuel m.point m.mem
  | fuel + 1, m =>
    match step code lim m with
    | .running m' => run code lim fuel m'
    | .done o => o

/-- `Lir.Prog.start`: the call of function `f` on `args` over `mem`. -/
def start (code : Array Func) (f : Nat) (args : List UInt64) (mem : Mem) : Except String Machine := do
  let some fn := code[f]? | throw s!"no function {f}"
  let some fr := (Frame.empty fn.regs).writeAll fn.params args
    | throw s!"function {f} takes {fn.params.length} arguments, not {args.length}"
  return ⟨⟨f, fn.entry, 0⟩, fr, #[], mem⟩

/-- The name of every Lir function of a link (dispatchers have none in `funcs`). -/
def funcNames (l : Linked) : Array String := Id.run do
  let mut a := Array.replicate l.prog.funcs.length ""
  for (n, i) in l.funcs.toList do
    if i < a.size then a := a.set! i n
  for i in [0:a.size] do
    if a[i]! == "" then a := a.set! i s!"__ccomp_dispatch.{i}"
  return a

def Point.describe (names : Array String) (pt : Point) : String :=
  s!"{names[pt.func]?.getD s!"function {pt.func}"}, block {pt.label}, instruction {pt.index}"

end Silmaril.Compile.Mir.Interp
