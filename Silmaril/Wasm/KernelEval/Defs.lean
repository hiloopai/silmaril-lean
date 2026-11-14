module

@[expose] public section

/-!
# Kernel evaluation of a small Wasm subset: definitions

A prototype for measuring how cheaply Lean's kernel can evaluate Wasm code, with no
compiled evaluation. It is **not** silmaril's Core semantics: it is a self-contained reference
machine for an integer-and-memory subset, written so that the kernel reduces it, and fast
variants of it proved equal to it (`Silmaril.Wasm.KernelEval.Thms`). Measurements and the
soundness boundary are in `docs/projects/wasm-kernel-eval.md`.

**The subset (`Instr`).** `i32.const`, `local.get/set/tee`, `drop`, `select`, the i32
binary operators `add sub mul and or xor shl shr_u` and comparisons `eq ne lt_u`, `i32.eqz`,
`i32.load`, `i32.store`, `i32.load8_u`, `i32.store8` (static offset, alignment ignored),
`block` with a result count, `loop` without parameters, `br`, `br_if`, `unreachable`. No
types, calls, globals, tables, floats, i64 or `memory.grow`. These are the instructions of the
loops that dominate compiled code (see the opcode census in the documentation).

**The machine.** A configuration (`Config`) holds the remaining code of the innermost block,
the operand stack of that block, the enclosing labels (each with its continuation, its branch
arity, its branch target and the outer stack), the locals and the memory. `step` performs one
instruction, or leaves a block whose code is exhausted; `run n c` does at most `n` steps and
returns `.running c'` if the fuel runs out, so that runs compose (`run_add`). Ill-formed code
(a missing operand, an out-of-range local or label) gets stuck (`.stuck`), distinguished from a
Wasm trap (`.trap`: `unreachable`, an out-of-bounds access).

**Memory interface (`MemOps`).** The machine is generic in its memory: `ListMem` (a list of
bytes, read and written by `take`/`drop` splices and little-endian decoding, as Core's
`Memory.load`/`Memory.store` are) is the reference, and `NatMem` (all bytes packed into one
natural number, read and written with shifts, `%`, `-` and `+`, which the kernel computes with
GMP) the fast one.

A Silmaril addition.
-/

namespace Silmaril.Wasm.KernelEval

/-- i32 binary operators of the subset. -/
inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shrU | eq | ne | ltU
  deriving DecidableEq, Repr

/-- The instructions of the subset. `block r body` leaves `r` results; `loop` has none. -/
inductive Instr where
  | const (n : BitVec 32)
  | localGet (i : Nat)
  | localSet (i : Nat)
  | localTee (i : Nat)
  | drop
  | select
  | bin (op : BinOp)
  | eqz
  | load (off : Nat)
  | store (off : Nat)
  | load8u (off : Nat)
  | store8 (off : Nat)
  | block (r : Nat) (body : List Instr)
  | loop (body : List Instr)
  | br (l : Nat)
  | brIf (l : Nat)
  | unreachable
  deriving Repr

/-- Evaluation of a binary operator, as in Core (`shl`, `shr_u` take the shift modulo 32). -/
def BinOp.eval : BinOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< (b.toNat % 32)
  | .shrU, a, b => a >>> (b.toNat % 32)
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .ltU, a, b => if a.toNat < b.toNat then 1 else 0

/-- A memory: `load m a k` reads the `k`-byte little-endian word at address `a`, `store m a k v`
writes `v mod 2^(8k)` there; both are `none` when `a + k` exceeds the memory. -/
class MemOps (M : Type) where
  load : M → Nat → Nat → Option Nat
  store : M → Nat → Nat → Nat → Option M

/-! ## The reference memory: a list of bytes -/

/-- Memory as a list of bytes. -/
structure ListMem where
  bytes : List (BitVec 8)
  deriving Repr, DecidableEq

/-- Little-endian decoding of bytes (`Memory.decodeLE` in Core). -/
def ListMem.pack : List (BitVec 8) → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * pack bs

/-- The `k` little-endian bytes of `v mod 256^k` (`Memory.encodeLE` in Core). -/
def ListMem.encode : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | k + 1, v => BitVec.ofNat 8 v :: encode k (v / 256)

instance : MemOps ListMem where
  load m a k :=
    if a + k ≤ m.bytes.length then some (ListMem.pack ((m.bytes.drop a).take k)) else none
  store m a k v :=
    if a + k ≤ m.bytes.length then
      some ⟨m.bytes.take a ++ ListMem.encode k v ++ m.bytes.drop (a + k)⟩
    else none

/-! ## The packed memory: one natural number -/

/-- Memory as one natural number: byte `a` is bits `8a … 8a+7` of `bits`, and `size` bytes
exist. -/
structure NatMem where
  bits : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- The `k`-byte little-endian word at `a` (no bounds check). -/
def NatMem.read (m : NatMem) (a k : Nat) : Nat := (m.bits >>> (8 * a)) % 2 ^ (8 * k)

/-- Replace the `k`-byte word at `a` by `v mod 2^(8k)` (no bounds check): subtract the old
word and add the new one, at their position. -/
def NatMem.write (m : NatMem) (a k v : Nat) : NatMem :=
  ⟨m.bits - (m.read a k <<< (8 * a)) + ((v % 2 ^ (8 * k)) <<< (8 * a)), m.size⟩

instance : MemOps NatMem where
  load m a k := if a + k ≤ m.size then some (m.read a k) else none
  store m a k v := if a + k ≤ m.size then some (m.write a k v) else none

/-- The packed memory of a list memory. -/
def ListMem.toNatMem (m : ListMem) : NatMem := ⟨ListMem.pack m.bytes, m.bytes.length⟩

/-- `n` zero bytes, packed: the number `0`. -/
def NatMem.zeros (n : Nat) : NatMem := ⟨0, n⟩

/-! ## The machine -/

/-- An enclosing label: code after the block, what a branch to it continues with, how many
values a branch or fall-through keeps, and the stack outside the block. -/
structure Label where
  after : List Instr
  onBr : List Instr
  brArity : Nat
  endArity : Nat
  outer : List (BitVec 32)
  deriving Repr

/-- A configuration. The operand stack is top-first and belongs to the innermost block. -/
structure Config (M : Type) where
  code : List Instr
  stk : List (BitVec 32)
  labels : List Label
  locals : List (BitVec 32)
  mem : M
  deriving Repr

/-- The result of a run. -/
inductive Result (M : Type) where
  | running (c : Config M)
  | done (stk : List (BitVec 32)) (locals : List (BitVec 32)) (mem : M)
  | trap
  | stuck
  deriving Repr

variable {M : Type} [MemOps M]

/-- `br l`: unwind `l` labels, then continue at the target of the next one. -/
def branch (c : Config M) : Nat → Result M
  | l => match c.labels.drop l with
    | lb :: ls =>
      .running { c with code := lb.onBr, stk := c.stk.take lb.brArity ++ lb.outer, labels := ls }
    | [] => .stuck

/-- Overwrite local `i`, if it exists. -/
def setLocal? (ls : List (BitVec 32)) (i : Nat) (v : BitVec 32) : Option (List (BitVec 32)) :=
  if i < ls.length then some (ls.set i v) else none

/-- One step. -/
def step (c : Config M) : Result M :=
  match c.code with
  | [] => match c.labels with
    | [] => .done c.stk c.locals c.mem
    | lb :: ls =>
      .running { c with code := lb.after, stk := c.stk.take lb.endArity ++ lb.outer, labels := ls }
  | i :: rest =>
    let c := { c with code := rest }
    match i, c.stk with
    | .const n, s => .running { c with stk := n :: s }
    | .localGet x, s => match c.locals[x]? with
      | some v => .running { c with stk := v :: s }
      | none => .stuck
    | .localSet x, v :: s => match setLocal? c.locals x v with
      | some ls => .running { c with stk := s, locals := ls }
      | none => .stuck
    | .localTee x, v :: s => match setLocal? c.locals x v with
      | some ls => .running { c with stk := v :: s, locals := ls }
      | none => .stuck
    | .drop, _ :: s => .running { c with stk := s }
    | .select, k :: b :: a :: s => .running { c with stk := (if k = 0 then b else a) :: s }
    | .bin op, b :: a :: s => .running { c with stk := op.eval a b :: s }
    | .eqz, a :: s => .running { c with stk := (if a = 0 then 1 else 0) :: s }
    | .load off, a :: s => match MemOps.load c.mem (a.toNat + off) 4 with
      | some v => .running { c with stk := BitVec.ofNat 32 v :: s }
      | none => .trap
    | .store off, v :: a :: s => match MemOps.store c.mem (a.toNat + off) 4 v.toNat with
      | some m => .running { c with stk := s, mem := m }
      | none => .trap
    | .load8u off, a :: s => match MemOps.load c.mem (a.toNat + off) 1 with
      | some v => .running { c with stk := BitVec.ofNat 32 v :: s }
      | none => .trap
    | .store8 off, v :: a :: s => match MemOps.store c.mem (a.toNat + off) 1 v.toNat with
      | some m => .running { c with stk := s, mem := m }
      | none => .trap
    | .block r body, s =>
      .running { c with code := body, stk := [], labels := ⟨rest, rest, r, r, s⟩ :: c.labels }
    | .loop body, s =>
      .running { c with code := body, stk := [],
                        labels := ⟨rest, Instr.loop body :: rest, 0, 0, s⟩ :: c.labels }
    | .br l, _ => branch c l
    | .brIf l, k :: s => if k = 0 then .running { c with stk := s } else branch { c with stk := s } l
    | .unreachable, _ => .trap
    | _, _ => .stuck

/-- **The reference run**: at most `n` steps. -/
def run : Nat → Config M → Result M
  | 0, c => .running c
  | n + 1, c => match step c with
    | .running c' => run n c'
    | r => r

/-- Continue a run that ran out of fuel. -/
def Result.andThen (r : Result M) (k : Config M → Result M) : Result M :=
  match r with
  | .running c => k c
  | r => r

/-- The initial configuration of a function body with the given locals and memory. -/
def Config.init (body : List Instr) (locals : List (BitVec 32)) (mem : M) : Config M :=
  ⟨body, [], [], locals, mem⟩

/-! ## Changing the memory representation -/

omit [MemOps M] in
/-- A configuration with its memory mapped by `g`. -/
def Config.mapMem {N : Type} (g : M → N) (c : Config M) : Config N :=
  ⟨c.code, c.stk, c.labels, c.locals, g c.mem⟩

omit [MemOps M] in
/-- A result with its memory mapped by `g`. -/
def Result.mapMem {N : Type} (g : M → N) : Result M → Result N
  | .running c => .running (c.mapMem g)
  | .done s l m => .done s l (g m)
  | .trap => .trap
  | .stuck => .stuck

/-- `g` is a simulation of memories: it commutes with loads and stores. -/
structure MemSim {N : Type} [MemOps N] (g : M → N) : Prop where
  load : ∀ m a k, MemOps.load (g m) a k = MemOps.load m a k
  store : ∀ m a k v, MemOps.store (g m) a k v = (MemOps.store m a k v).map g

/-! ## Kernel-oriented variants -/

/-- `run` by the recursor of `Nat`: the kernel reduces it without the `brecOn` encoding of
structural recursion. -/
def runRec (n : Nat) : Config M → Result M :=
  Nat.rec (motive := fun _ => Config M → Result M) (fun c => .running c)
    (fun _ ih c => match step c with
      | .running c' => ih c'
      | r => r) n

/-- Compiled code runs `run` instead of `runRec`: the compiler implements `Nat.rec` by
non-tail recursion on the fuel, which overflows the stack for large fuel. -/
@[csimp] theorem runRec_eq_run_csimp : @runRec = @run := by
  funext M _ n c
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact (congrArg (fun k => match step c with | .running c' => k c' | r => r)
      (funext ih) :)

/-- A result's top-of-stack value, if it is `done` with a non-empty stack. -/
def Result.top? : Result M → Option (BitVec 32)
  | .done (v :: _) _ _ => some v
  | _ => none

/-- A Boolean check that a run of `body` with `fuel` returns `v` on top. This is the
proposition both checking modes decide: `decide +kernel` (by the kernel) and, off main,
compiled evaluation (the fast edge, outside this library). -/
def returns (fuel : Nat) (body : List Instr) (locals : List (BitVec 32)) (mem : M)
    (v : BitVec 32) : Bool :=
  match (runRec fuel (Config.init body locals mem)).top? with
  | some w => w == v
  | none => false

end Silmaril.Wasm.KernelEval
