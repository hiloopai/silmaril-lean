module

public import Silmaril.Wasm.Component.Reference.Engine.Mock.Script.Defs
public import Silmaril.Wasm.Component.Engine.Laws
public import Silmaril.Wasm.Execution.Memory
import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

/-!
# The Mock core engine

A `CoreEngine` whose modules are Script programs (`Engine/Mock/Script.lean`). It is used to
transcribe the core functions of the reference test suite
(`design/mvp/canonical-abi/run_tests.py` of component-model a25fc0b, next to the pinned
`definitions.py`), which are Python lambdas over memories of either address type, and to
exercise the canonical ABI's memory64 paths, which Lime1 cannot execute (Lime1 and V1 only have
`i32` memories).

* `FuncType := V1.FuncType`, `ExternType := CoreExternType` (memories carry their address
  type, so an `i64` memory is `.memory .i64 n (some n)`; Mock memory limits are in bytes).
* The store holds function instances (Script functions closed over their module instance, or
  host functions `V1.FuncType × H`), memories (`AddrType × ByteArray`), funcref tables (with
  their address type) and globals. Addresses are list positions; nothing is ever removed, and
  only memory contents and global values change.
* `prepare?` checks `Module.validate`, resolves imports positionally (each provided extern
  value must have a type that is a subtype of the declared import type), allocates, and
  returns the start function without running it.
* A thread is `entry f args` (fresh invocation), `exec frames pending` (a stack of Script
  frames, head = current, with an optional pending host callout), or `done r`. Calls to other
  Script functions push a frame; calls to host functions first take an internal step that
  records the callout in `pending` (so a thread is a callout exactly when it is parked), and
  `resume` writes the host results and advances the caller. Invoking a host function directly
  is a callout immediately (required by `Lawful.allocHost_callout`).
* `Internal` is the deterministic one-instruction step `stepMock?`; argument, result and
  register type mismatches, out-of-bounds accesses and falling off the end of the code are
  traps (`done .trap`), never stuck states. The only stuck threads are invocations of
  unallocated addresses and the empty frame stack (unreachable).

Proved: `Lawful mock`, `ResumeLawful mock`, `mockExec : mock.Exec` with `step?_sound` by `rfl`,
`ExecDeterministic mockExec` (hence `ExecComplete`), and `stepMock?_isSome_iff` (the stepper is
total exactly on running threads). Tests (kernel-checked by `decide`): an `i64` memory,
an i64 address above 2^32 is bounds checked without truncation, an `i32` pointer register on
an `i64` memory traps at the access, an `i64` table (`tableAddrType? = some .i64`) indexed by
`callIndirect` with signature check and without index truncation, rejection of duplicate
export names, and a host callout round trip (`callout` then `resume`, then `returned`).

Not modelled: WebAssembly validation or typing of Script code, memory or table growth,
exceptions, and any cost model. The Mock engine is a test vehicle, not a WebAssembly semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Mock

open Silmaril.Wasm.Execution.Memory (readBytes writeBytes decodeLE encodeLE)
open Silmaril.Wasm.Execution.Runtime (Value)

/-! ## Store -/

/-- External values: store addresses of each kind. -/
inductive ExternVal where
  | func (a : Nat)
  | memory (a : Nat)
  | table (a : Nat)
  | global (a : Nat)
  deriving DecidableEq, Repr

/-- A module instance: the store addresses of its index spaces, and its exports. -/
structure ModInst where
  funcs : List Nat := []
  mems : List Nat := []
  tables : List Nat := []
  globals : List Nat := []
  exports : List (String × ExternVal) := []
  deriving DecidableEq, Repr

/-- Function instances. -/
inductive FuncInst (H : Type) where
  | wasm (inst : ModInst) (f : Func)
  | host (type : V1.FuncType) (h : H)
  deriving DecidableEq, Repr

def FuncInst.type {H : Type} : FuncInst H → V1.FuncType
  | .wasm _ f => f.type
  | .host t _ => t

/-- A memory: its address type and its bytes (size in bytes). -/
structure MemInst where
  addrType : AddrType
  bytes : ByteArray

/-- A funcref table of function addresses. -/
structure TableInst where
  addrType : AddrType
  elems : List (Option Nat)
  deriving DecidableEq, Repr

structure GlobalInst where
  value : FlatValue
  mutable : Bool
  deriving DecidableEq, Repr

/-- The Mock engine store over host-code identifiers `H`. -/
structure Store (H : Type) where
  funcs : List (FuncInst H) := []
  mems : List MemInst := []
  tables : List TableInst := []
  globals : List GlobalInst := []

variable {H : Type}

def funcType? (s : Store H) (a : Nat) : Option V1.FuncType := (s.funcs[a]?).map FuncInst.type
def memAddrType? (s : Store H) (m : Nat) : Option AddrType := (s.mems[m]?).map (·.addrType)
def memSize? (s : Store H) (m : Nat) : Option Nat := (s.mems[m]?).map (·.bytes.size)
def tableAddrType? (s : Store H) (t : Nat) : Option AddrType := (s.tables[t]?).map (·.addrType)
def tableFunc? (s : Store H) (t i : Nat) : Option (Option Nat) := (s.tables[t]?).bind (·.elems[i]?)

def memRead? (s : Store H) (m st len : Nat) : Option ByteArray :=
  (s.mems[m]?).bind fun mi => readBytes mi.bytes st len

/-- Write bytes into memory `m` (bounds checked). -/
def memWrite? (s : Store H) (m st : Nat) (bs : ByteArray) : Option (Store H) :=
  match s.mems[m]? with
  | some mi =>
    (writeBytes mi.bytes st bs).map fun b => { s with mems := s.mems.set m { mi with bytes := b } }
  | none => none

/-- Set a mutable global to a value of its type. -/
def setGlobal? (s : Store H) (g : Nat) (v : FlatValue) : Option (Store H) :=
  match s.globals[g]? with
  | some gi =>
    if gi.mutable ∧ gi.value.type = v.type then
      some { s with globals := s.globals.set g { gi with value := v } }
    else none
  | none => none

/-- The type of an external value (Mock memory and table limits are their exact sizes). -/
def externType? (s : Store H) : ExternVal → Option CoreExternType
  | .func a => (funcType? s a).map .func
  | .memory a => (s.mems[a]?).map fun mi => .memory mi.addrType mi.bytes.size (some mi.bytes.size)
  | .table a => (s.tables[a]?).map fun ti => .table ti.addrType ti.elems.length
      (some ti.elems.length)
  | .global a => (s.globals[a]?).map fun gi => .global gi.value.type gi.mutable

/-- Allocate a host function. -/
def allocHost (s : Store H) (ft : V1.FuncType) (h : H) : Store H × Nat :=
  ({ s with funcs := s.funcs ++ [.host ft h] }, s.funcs.length)

/-! ## Instantiation -/

/-- Resolve one positional import into the growing instance. -/
def resolveImport (s : Store H) (acc : ModInst) :
    (String × String × CoreExternType) × ExternVal → Option ModInst
  | ((_, _, τ), v) =>
    match externType? s v with
    | some τ' =>
      if τ'.sub τ then
        match v with
        | .func a => some { acc with funcs := acc.funcs ++ [a] }
        | .memory a => some { acc with mems := acc.mems ++ [a] }
        | .table a => some { acc with tables := acc.tables ++ [a] }
        | .global a => some { acc with globals := acc.globals ++ [a] }
      else none
    | none => none

/-- The instance of a module whose imports resolved to `imp`, allocated at the end of `s`. -/
def allocInst (s : Store H) (m : Module) (imp : ModInst) : ModInst where
  funcs := imp.funcs ++ (List.range m.funcs.length).map (s.funcs.length + ·)
  mems := imp.mems ++ (List.range m.memories.length).map (s.mems.length + ·)
  tables := imp.tables ++ (List.range m.tables.length).map (s.tables.length + ·)
  globals := imp.globals ++ (List.range m.globals.length).map (s.globals.length + ·)

def resolveIdx? (mi : ModInst) : ExternKindIdx → Option ExternVal
  | .func i => (mi.funcs[i]?).map .func
  | .memory i => (mi.mems[i]?).map .memory
  | .table i => (mi.tables[i]?).map .table
  | .global i => (mi.globals[i]?).map .global

def resolveElem? (mi : ModInst) : Option Nat → Option (Option Nat)
  | none => some none
  | some i => (mi.funcs[i]?).map some

/-- The store after allocating the module's functions, memories (zero-filled), tables and
globals. -/
def extendStore (s : Store H) (m : Module) (mi : ModInst)
    (tbls : List (AddrType × List (Option Nat))) : Store H where
  funcs := s.funcs ++ m.funcs.map (.wasm mi)
  mems := s.mems ++ m.memories.map fun (a, n) => ⟨a, ⟨Array.replicate n 0⟩⟩
  tables := s.tables ++ tbls.map fun (a, es) => ⟨a, es⟩
  globals := s.globals ++ m.globals.map fun (v, mu) => ⟨v, mu⟩

/-- The start function's address, if any. -/
def startAddr? (mi : ModInst) : Option Nat → Option (Option Nat)
  | none => some none
  | some i => (mi.funcs[i]?).map some

/-- Instantiation: validity, positional import resolution with subtyping, allocation. The
start function is returned, not run. -/
def prepare? (s : Store H) (m : Module) (imps : List ExternVal) :
    Option (Store H × ModInst × Option Nat) := do
  guard m.validate
  guard (m.imports.length = imps.length)
  let imp ← (m.imports.zip imps).foldlM (resolveImport s) {}
  let mi0 := allocInst s m imp
  let exs ← m.exports.mapM fun (n, e) => (resolveIdx? mi0 e).map (n, ·)
  let mi := { mi0 with exports := exs }
  let tbls ← m.tables.mapM fun (a, es) => (es.mapM (resolveElem? mi)).map (a, ·)
  let st ← startAddr? mi m.start
  pure (extendStore s m mi tbls, mi, st)

/-! ## Threads -/

/-- A Script activation frame. `dest` are the caller's registers receiving the results. -/
structure Frame where
  func : Nat
  pc : Nat := 0
  regs : List FlatValue := []
  args : List FlatValue := []
  dest : List Nat := []
  deriving DecidableEq, Repr

/-- A pending host callout of the current frame. -/
structure Pending (H : Type) where
  host : H
  args : List FlatValue
  dest : List Nat
  results : List NumType
  deriving DecidableEq, Repr

/-- Store-free Mock activations. -/
inductive Thread (H : Type) where
  | entry (f : Nat) (args : List FlatValue)
  | exec (frames : List Frame) (pending : Option (Pending H))
  | done (r : CallResult)
  deriving DecidableEq, Repr

def status (s : Store H) : Thread H → Status H
  | .done r => .returned r
  | .entry a args =>
    match s.funcs[a]? with
    | some (.host _ h) => .callout h args
    | some (.wasm ..) => .running
    | none => .stuck
  | .exec _ (some p) => .callout p.host p.args
  | .exec [] none => .stuck
  | .exec (_ :: _) none => .running

/-! ## Registers and values -/

def setReg (regs : List FlatValue) (r : Nat) (v : FlatValue) : List FlatValue :=
  if r < regs.length then regs.set r v
  else regs ++ List.replicate (r - regs.length) (Value.zero (.int .i32)) ++ [v]

def getRegs (regs : List FlatValue) (rs : List Nat) : Option (List FlatValue) :=
  rs.mapM (regs[·]?)

/-- Write `vs` to registers `rs` (lengths must agree). -/
def setRegs? (regs : List FlatValue) (rs : List Nat) (vs : List FlatValue) :
    Option (List FlatValue) :=
  if rs.length = vs.length then
    some ((rs.zip vs).foldl (fun acc (r, v) => setReg acc r v) regs)
  else none

def intVal? (t : IntType) (v : FlatValue) : Option (BitVec t.width) :=
  if v.type = .int t then some (BitVec.ofNat t.width v.bits.toNat) else none

/-- The unsigned value of an integer register (any width). -/
def anyInt? (v : FlatValue) : Option (Nat × Nat) :=
  match v.type with
  | .int t => some (v.bits.toNat, t.width)
  | .float _ => none

def boolVal (b : Bool) : FlatValue := Value.int .i32 (if b then 1 else 0)

def evalBin (t : IntType) (op : BinOp) (x y : BitVec t.width) : FlatValue :=
  match op with
  | .add => Value.int t (x + y)
  | .sub => Value.int t (x - y)
  | .mul => Value.int t (x * y)
  | .and => Value.int t (x &&& y)
  | .or => Value.int t (x ||| y)
  | .xor => Value.int t (x ^^^ y)
  | .shl => Value.int t (x <<< (y.toNat % t.width))
  | .shrU => Value.int t (x >>> (y.toNat % t.width))
  | .eq => boolVal (x.toNat == y.toNat)
  | .ne => boolVal (x.toNat != y.toNat)
  | .ltU => boolVal (decide (x.toNat < y.toNat))
  | .leU => boolVal (decide (x.toNat ≤ y.toNat))
  | .gtU => boolVal (decide (y.toNat < x.toNat))
  | .geU => boolVal (decide (y.toNat ≤ x.toNat))

/-! ## The step -/

/-- The store mutation performed by one step. -/
inductive StoreOp where
  | none
  | writeMem (m st : Nat) (bs : ByteArray)
  | setGlobal (g : Nat) (v : FlatValue)

def applyOp (s : Store H) : StoreOp → Option (Store H)
  | .none => some s
  | .writeMem m st bs => memWrite? s m st bs
  | .setGlobal g v => setGlobal? s g v

def trapStep : StoreOp × Thread H := (.none, .done .trap)

/-- Continue in the current frame at the next instruction with new registers. -/
def advance (fr : Frame) (rest : List Frame) (regs : List FlatValue) : Thread H :=
  .exec ({ fr with pc := fr.pc + 1, regs } :: rest) none

/-- A call from frame `fr` to the function at address `a`. Only the argument value types are
checked against the callee's parameters (`callIndirect` checks the full type first). Host
functions become a pending callout (the frame is advanced on `resume`); Script functions push
a frame. -/
def callStep (s : Store H) (fr : Frame) (rest : List Frame) (a : Nat) (args res : List Nat) :
    StoreOp × Thread H :=
  match getRegs fr.regs args with
  | none => trapStep
  | some vs =>
    match s.funcs[a]? with
    | some (.host ft h) =>
      if vs.map (·.type) = ft.params then
        (.none, .exec (fr :: rest) (some ⟨h, vs, res, ft.results⟩))
      else trapStep
    | some (.wasm _ f) =>
      if vs.map (·.type) = f.type.params then
        (.none, .exec ({ func := a, args := vs, dest := res } :: { fr with pc := fr.pc + 1 } ::
          rest) none)
      else trapStep
    | none => trapStep

/-- Return from frame `fr` of function `fn`. -/
def retStep (fn : Func) (fr : Frame) (rest : List Frame) (rs : List Nat) :
    Option (StoreOp × Thread H) := do
  let vs ← getRegs fr.regs rs
  guard (vs.map (·.type) = fn.type.results)
  match rest with
  | [] => some (.none, .done (.values vs))
  | caller :: rest' =>
    let regs ← setRegs? caller.regs fr.dest vs
    some (.none, .exec ({ caller with regs } :: rest') none)

/-- The memory `mem` of instance `mi`: its address and instance. -/
def memAt? (s : Store H) (mi : ModInst) (mem : Nat) : Option (Nat × MemInst) := do
  let a ← mi.mems[mem]?
  let m ← s.mems[a]?
  pure (a, m)

/-- Effective address: the pointer must be an integer of the memory's address type. -/
def effAddr? (m : MemInst) (p : FlatValue) (off : Nat) : Option Nat :=
  (intVal? m.addrType.intType p).map (·.toNat + off)

/-- Execute one instruction; `none` is a trap. -/
def execInstr (s : Store H) (mi : ModInst) (fn : Func) (fr : Frame) (rest : List Frame) :
    Instr → Option (StoreOp × Thread H)
  | .const r v => some (.none, advance fr rest (setReg fr.regs r v))
  | .arg r i => do
    let v ← fr.args[i]?
    some (.none, advance fr rest (setReg fr.regs r v))
  | .mov d r => do
    let v ← fr.regs[r]?
    some (.none, advance fr rest (setReg fr.regs d v))
  | .binop t op d a b => do
    let x ← intVal? t (← fr.regs[a]?)
    let y ← intVal? t (← fr.regs[b]?)
    some (.none, advance fr rest (setReg fr.regs d (evalBin t op x y)))
  | .eqz t d a => do
    let x ← intVal? t (← fr.regs[a]?)
    some (.none, advance fr rest (setReg fr.regs d (boolVal (x.toNat == 0))))
  | .wrap d a => do
    let x ← intVal? .i64 (← fr.regs[a]?)
    some (.none, advance fr rest (setReg fr.regs d (Value.int .i32 (BitVec.ofNat 32 x.toNat))))
  | .extendU d a => do
    let x ← intVal? .i32 (← fr.regs[a]?)
    some (.none, advance fr rest (setReg fr.regs d (Value.int .i64 (BitVec.ofNat 64 x.toNat))))
  | .call f args res => do
    let a ← mi.funcs[f]?
    some (callStep s fr rest a args res)
  | .callIndirect tbl idx ft args res => do
    let ta ← mi.tables[tbl]?
    let ti ← s.tables[ta]?
    let i ← intVal? ti.addrType.intType (← fr.regs[idx]?)
    let e ← ti.elems[i.toNat]?
    let a ← e
    guard (funcType? s a = some ft)
    some (callStep s fr rest a args res)
  | .callAddr r args res => do
    let (a, _) ← anyInt? (← fr.regs[r]?)
    some (callStep s fr rest a args res)
  | .load t n d mem p off => do
    let (_, m) ← memAt? s mi mem
    let ea ← effAddr? m (← fr.regs[p]?) off
    if n * 8 ≤ t.width then
      let bs ← readBytes m.bytes ea n
      some (.none, advance fr rest
        (setReg fr.regs d (Value.int t (BitVec.ofNat t.width (decodeLE bs)))))
    else none
  | .store n mem p off src => do
    let (a, m) ← memAt? s mi mem
    let ea ← effAddr? m (← fr.regs[p]?) off
    let (x, w) ← anyInt? (← fr.regs[src]?)
    if n * 8 ≤ w then some (.writeMem a ea (encodeLE n x), advance fr rest fr.regs) else none
  | .memWrite mem p off bytes => do
    let (a, m) ← memAt? s mi mem
    let ea ← effAddr? m (← fr.regs[p]?) off
    some (.writeMem a ea ⟨bytes.toArray⟩, advance fr rest fr.regs)
  | .memSize d mem => do
    let (_, m) ← memAt? s mi mem
    some (.none, advance fr rest (setReg fr.regs d
      (Value.int m.addrType.intType (BitVec.ofNat _ m.bytes.size))))
  | .globalGet d g => do
    let a ← mi.globals[g]?
    let gi ← s.globals[a]?
    some (.none, advance fr rest (setReg fr.regs d gi.value))
  | .globalSet g r => do
    let a ← mi.globals[g]?
    let v ← fr.regs[r]?
    some (.setGlobal a v, advance fr rest fr.regs)
  | .branchIfZero r l => do
    let (x, _) ← anyInt? (← fr.regs[r]?)
    let pc := if x = 0 then l else fr.pc + 1
    some (.none, .exec ({ fr with pc } :: rest) none)
  | .jump l => some (.none, .exec ({ fr with pc := l } :: rest) none)
  | .ret rs => retStep fn fr rest rs
  | .trap => none

/-- The pure part of a step: the store mutation and the next thread, for running threads. -/
def next (s : Store H) : Thread H → Option (StoreOp × Thread H)
  | .entry a args =>
    match s.funcs[a]? with
    | some (.wasm _ f) =>
      some (if args.map (·.type) = f.type.params then
        (.none, .exec [{ func := a, args }] none) else trapStep)
    | _ => none
  | .exec (fr :: rest) none =>
    some (match s.funcs[fr.func]? with
      | some (.wasm mi fn) =>
        match fn.code[fr.pc]? with
        | some i => (execInstr s mi fn fr rest i).getD trapStep
        | none => trapStep
      | _ => trapStep)
  | _ => none

/-- The executable one-instruction step. A failing store mutation traps. -/
def stepMock? (c : Store H × Thread H) : Option (Store H × Thread H) :=
  (next c.1 c.2).map fun (op, t') =>
    match applyOp c.1 op with
    | some s' => (s', t')
    | none => (c.1, .done .trap)

def checkResult (tys : List NumType) : CallResult → CallResult
  | .values vs => if vs.map (·.type) = tys then .values vs else .trap
  | .trap => .trap

/-- Resume a parked activation with a host result. Results of the wrong types trap. -/
def resume (s : Store H) : Thread H → CallResult → Thread H
  | .entry a args, r =>
    match s.funcs[a]? with
    | some (.host ft _) => .done (checkResult ft.results r)
    | _ => .entry a args
  | .exec _ (some _), .trap => .done .trap
  | .exec frames (some p), .values vs =>
    if vs.map (·.type) = p.results then
      match frames with
      | fr :: rest =>
        match setRegs? fr.regs p.dest vs with
        | some regs => .exec ({ fr with pc := fr.pc + 1, regs } :: rest) none
        | none => .done .trap
      | [] => .done .trap
    else .done .trap
  | t, _ => t

/-! ## The engine -/

def asFunc? : ExternVal → Option Nat | .func a => some a | _ => none
def asMemory? : ExternVal → Option Nat | .memory a => some a | _ => none
def asTable? : ExternVal → Option Nat | .table a => some a | _ => none
def asGlobal? : ExternVal → Option Nat | .global a => some a | _ => none

/-- The Mock core engine. -/
abbrev mock : CoreEngine where
  Module := Module
  Valid := Module.Valid
  FuncType := V1.FuncType
  ExternType := CoreExternType
  ExternSub := CoreExternType.Sub
  ofFlatType := id
  flatType? := some
  importTypes m := m.imports
  exportTypes m := m.exportTypes
  Store := Store
  empty _ := {}
  FuncAddr := Nat
  MemAddr := Nat
  TableAddr := Nat
  GlobalAddr := Nat
  ExternVal := ExternVal
  asFunc? := asFunc?
  asMemory? := asMemory?
  asTable? := asTable?
  asGlobal? := asGlobal?
  ofFunc := .func
  Inst := ModInst
  exports := ModInst.exports
  externType? := externType?
  prepare? := prepare?
  allocHost := allocHost
  funcType? := funcType?
  memAddrType? := memAddrType?
  memSize? := memSize?
  memRead? := memRead?
  memWrite? := memWrite?
  tableAddrType? := tableAddrType?
  tableFunc? := tableFunc?
  Thread := Thread
  invoke a args := .entry a args
  status := status
  Internal c c' := stepMock? c = some c'
  resume := resume

/-- The executable stepper; sound by definition. -/
def mockExec : mock.Exec where
  step? := stepMock?
  step?_sound h := h

/-! ## Laws -/

theorem next_isSome_iff (s : Store H) (t : Thread H) :
    (next s t).isSome ↔ status s t = .running := by
  rcases t with ⟨a, args⟩ | ⟨_ | ⟨fr, rest⟩, _ | p⟩ | r <;>
    simp only [next, status, Option.isSome_some, Option.isSome_none, reduceCtorEq]
  cases s.funcs[a]? with
  | none => simp
  | some fi => cases fi <;> simp

/-- The stepper is total exactly on running threads. -/
theorem stepMock?_isSome_iff (s : Store H) (t : Thread H) :
    (stepMock? (s, t)).isSome ↔ status s t = .running := by
  rw [← next_isSome_iff]
  simp [stepMock?]

theorem status_running_of_step {s : Store H} {t : Thread H} {c'}
    (h : stepMock? (s, t) = some c') : status s t = .running :=
  (stepMock?_isSome_iff s t).1 (by rw [h]; rfl)

theorem status_callout_append {s s' : Store H} {l} (hf : s'.funcs = s.funcs ++ l)
    {t : Thread H} {h args} (e : status s t = .callout h args) :
    status s' t = .callout h args := by
  rcases t with ⟨a, args'⟩ | ⟨_ | ⟨fr, rest⟩, _ | p⟩ | r <;> simp only [status] at e ⊢
  · rw [hf]
    cases hs : s.funcs[a]? with
    | none => simp [hs] at e
    | some fi =>
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1, hs]
      simpa [hs] using e
  all_goals exact e

/-- Appending functions keeps the type of every function. -/
theorem funcType_of_append {s s' : Store H} (l : List (FuncInst H)) (hf : s'.funcs = s.funcs ++ l) :
    ∀ a ft, mock.funcType? s a = some ft → mock.funcType? s' a = some ft := by
  intro a ft h
  change (s'.funcs[a]?).map FuncInst.type = some ft
  change (s.funcs[a]?).map FuncInst.type = some ft at h
  cases hs : s.funcs[a]? with
  | none => simp [hs] at h
  | some fi =>
    rw [hf, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1, hs]
    simpa [hs] using h

/-- A table that keeps its address type keeps the table's address type at the engine. -/
theorem tableAddrType_of {s s' : Store H}
    (ht : ∀ (i : Nat) (ti : TableInst), s.tables[i]? = some ti →
      ∃ ti', s'.tables[i]? = some ti' ∧ ti'.addrType = ti.addrType) :
    ∀ t a, mock.tableAddrType? s t = some a → mock.tableAddrType? s' t = some a := by
  intro t a h
  change (s'.tables[t]?).map (·.addrType) = some a
  change (s.tables[t]?).map (·.addrType) = some a at h
  cases hs : s.tables[t]? with
  | none => simp [hs] at h
  | some ti =>
    obtain ⟨ti', e, ea⟩ := ht t ti hs
    simp only [hs, Option.map_some, Option.some.injEq] at h
    rw [e, Option.map_some, ea, h]

/-- A sufficient condition for store extension: functions are appended, memories keep their
address type and may grow, tables keep their address type. -/
theorem extends_of {s s' : Store H} (l : List (FuncInst H)) (hf : s'.funcs = s.funcs ++ l)
    (hm : ∀ (i : Nat) (mi : MemInst), s.mems[i]? = some mi →
      ∃ mi', s'.mems[i]? = some mi' ∧ mi'.addrType = mi.addrType ∧
        mi.bytes.size ≤ mi'.bytes.size)
    (ht : ∀ (i : Nat) (ti : TableInst), s.tables[i]? = some ti →
      ∃ ti', s'.tables[i]? = some ti' ∧ ti'.addrType = ti.addrType) :
    mock.Extends s s' where
  funcType := funcType_of_append l hf
  memAddrType m t h := by
    change (s'.mems[m]?).map (·.addrType) = some t
    change (s.mems[m]?).map (·.addrType) = some t at h
    cases hs : s.mems[m]? with
    | none => simp [hs] at h
    | some mi =>
      obtain ⟨mi', e, ea, _⟩ := hm m mi hs
      simp only [hs, Option.map_some, Option.some.injEq] at h
      rw [e, Option.map_some, ea, h]
  memSize m n h := by
    change (s.mems[m]?).map (·.bytes.size) = some n at h
    cases hs : s.mems[m]? with
    | none => simp [hs] at h
    | some mi =>
      obtain ⟨mi', e, _, le⟩ := hm m mi hs
      simp only [hs, Option.map_some, Option.some.injEq] at h
      exact ⟨mi'.bytes.size, by change (s'.mems[m]?).map _ = _; rw [e]; rfl, h ▸ le⟩
  tableAddrType := tableAddrType_of ht
  callout t h args e := status_callout_append hf e

theorem memWrite?_eq_some {s s' : Store H} {m st bs} (h : memWrite? s m st bs = some s') :
    ∃ mi b, s.mems[m]? = some mi ∧ writeBytes mi.bytes st bs = some b ∧
      s' = { s with mems := s.mems.set m { mi with bytes := b } } := by
  unfold memWrite? at h
  cases hs : s.mems[m]? with
  | none => simp [hs] at h
  | some mi =>
    simp only [hs, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨mi, b, rfl, hb, rfl⟩

theorem memWrite?_mems {s s' : Store H} {m st bs} (h : memWrite? s m st bs = some s') (i : Nat) :
    (s'.mems[i]?).map (fun mi => (mi.addrType, mi.bytes.size)) =
      (s.mems[i]?).map (fun mi => (mi.addrType, mi.bytes.size)) := by
  obtain ⟨mi, b, hs, hb, rfl⟩ := memWrite?_eq_some h
  have hsz := Silmaril.Wasm.Execution.Memory.writeBytes_size _ _ _ _ hb
  by_cases hi : i = m
  · subst hi
    have hlt : i < s.mems.length := (List.getElem?_eq_some_iff.1 hs).1
    simp [List.getElem?_set_self hlt, hs, hsz]
  · simp only [List.getElem?_set_ne (Ne.symm hi)]

theorem memWrite?_extends {s s' : Store H} {m st bs} (h : memWrite? s m st bs = some s') :
    mock.Extends s s' := by
  have hm := memWrite?_mems h
  obtain ⟨mi, b, _, _, rfl⟩ := memWrite?_eq_some h
  refine extends_of [] (by simp) (fun i mi' e => ?_) (fun i ti e => ⟨ti, e, rfl⟩)
  have := hm i
  rw [e] at this
  cases e' : ((s.mems.set m { mi with bytes := b })[i]?) with
  | none => simp only [e'] at this; cases this
  | some mi'' =>
    simp only [e', Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨mi'', rfl, this.1, Nat.le_of_eq this.2.symm⟩

theorem setGlobal?_extends {s s' : Store H} {g v} (h : setGlobal? s g v = some s') :
    mock.Extends s s' := by
  unfold setGlobal? at h
  cases hs : s.globals[g]? with
  | none => simp [hs] at h
  | some gi =>
    simp only [hs] at h
    split at h
    · cases h
      exact extends_of [] (by simp) (fun i mi e => ⟨mi, e, rfl, Nat.le_refl _⟩)
        (fun i ti e => ⟨ti, e, rfl⟩)
    · cases h

theorem applyOp_extends {s s' : Store H} {op} (h : applyOp s op = some s') :
    mock.Extends s s' := by
  cases op with
  | none => cases h; exact CoreEngine.Extends.refl _
  | writeMem m st bs => exact memWrite?_extends h
  | setGlobal g v => exact setGlobal?_extends h

theorem stepMock?_extends {s s' : Store H} {t t'} (h : stepMock? (s, t) = some (s', t')) :
    mock.Extends s s' := by
  simp only [stepMock?, Option.map_eq_some_iff] at h
  obtain ⟨⟨op, t''⟩, _, e⟩ := h
  simp only at e
  split at e
  · rename_i s'' ho
    cases e
    exact applyOp_extends ho
  · cases e
    exact CoreEngine.Extends.refl _

theorem extendStore_extends (s : Store H) (m : Module) (mi : ModInst)
    (tbls : List (AddrType × List (Option Nat))) : mock.Extends s (extendStore s m mi tbls) := by
  refine extends_of _ rfl (fun i mi' e => ⟨mi', ?_, rfl, Nat.le_refl _⟩)
    (fun i ti e => ⟨ti, ?_, rfl⟩)
  · simp only [extendStore]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1, e]
  · simp only [extendStore]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1, e]

theorem prepare?_eq_some {s s' : Store H} {m imps i st}
    (h : prepare? s m imps = some (s', i, st)) : ∃ mi tbls, s' = extendStore s m mi tbls := by
  simp only [prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨_, _, h.2.1.symm⟩

theorem allocHost_extends' {s s' : Store H} {ft h a} (e : allocHost s ft h = (s', a)) :
    mock.Extends s s' := by
  cases e
  exact extends_of [.host ft h] rfl (fun i mi e => ⟨mi, e, rfl, Nat.le_refl _⟩)
    (fun i ti e => ⟨ti, e, rfl⟩)

theorem memRead?_isSome_iff {s : Store H} {m st len} :
    (memRead? s m st len).isSome ↔ ∃ n, memSize? s m = some n ∧ st + len ≤ n := by
  unfold memRead? memSize?
  cases s.mems[m]? with
  | none => simp
  | some mi => simp [readBytes]

theorem memWrite?_isSome_iff {s : Store H} {m st bs} :
    (memWrite? s m st bs).isSome ↔ ∃ n, memSize? s m = some n ∧ st + bs.size ≤ n := by
  unfold memWrite? memSize?
  cases s.mems[m]? with
  | none => simp
  | some mi => simp [writeBytes]

theorem memWrite?_read {s s' : Store H} {m st bs} (h : memWrite? s m st bs = some s') :
    memRead? s' m st bs.size = some bs := by
  obtain ⟨mi, b, hs, hb, rfl⟩ := memWrite?_eq_some h
  have hlt : m < s.mems.length := (List.getElem?_eq_some_iff.1 hs).1
  simp only [memRead?, List.getElem?_set_self hlt, Option.bind_some]
  exact Silmaril.Wasm.Execution.Memory.readBytes_writeBytes _ _ _ _ hb

theorem memWrite?_read_other {s s' : Store H} {m st bs m' st' len}
    (h : memWrite? s m st bs = some s')
    (hd : m' ≠ m ∨ st' + len ≤ st ∨ st + bs.size ≤ st') :
    memRead? s' m' st' len = memRead? s m' st' len := by
  obtain ⟨mi, b, hs, hb, rfl⟩ := memWrite?_eq_some h
  simp only [memRead?]
  by_cases hm : m' = m
  · subst hm
    have hlt : m' < s.mems.length := (List.getElem?_eq_some_iff.1 hs).1
    rw [List.getElem?_set_self hlt, hs]
    simp only [Option.bind_some]
    have hd' : st' + len ≤ st ∨ st + bs.size ≤ st' := by simpa using hd
    exact Silmaril.Wasm.Execution.Memory.readBytes_writeBytes_disjoint _ _ _ _ _ _ hb hd'
  · rw [List.getElem?_set_ne (Ne.symm hm)]

instance : mock.Lawful where
  flatType?_ofFlatType _ := rfl
  returned_no_step e h := by
    have := status_running_of_step h
    change status _ _ = _ at e
    rw [this] at e; cases e
  callout_no_step e h := by
    have := status_running_of_step h
    change status _ _ = _ at e
    rw [this] at e; cases e
  stuck_no_step e h := by
    have := status_running_of_step h
    change status _ _ = _ at e
    rw [this] at e; cases e
  externSub_refl := CoreExternType.Sub.refl
  externSub_trans := CoreExternType.Sub.trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := stepMock?_extends h
  prepare_extends h := by
    obtain ⟨mi, tbls, rfl⟩ := prepare?_eq_some h
    exact extendStore_extends _ _ _ _
  allocHost_extends h := allocHost_extends' h
  allocHost_fresh := by
    intro _ s _ _ _ _ e
    cases e
    change (s.funcs[s.funcs.length]?).map _ = none
    simp
  allocHost_frame := by
    intro _ s s' ft h a b e hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e.symm
    change ((s.funcs ++ [.host ft h])[b]?).map FuncInst.type = (s.funcs[b]?).map FuncInst.type
    rw [List.getElem?_append]
    split
    · rfl
    · rename_i hlt
      have hb' : @Ne Nat b s.funcs.length := hb
      have : b - s.funcs.length ≠ 0 :=
        Nat.sub_ne_zero_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hb'))
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hlt), this]
  allocHost_funcType := by
    intro _ s _ ft h _ e
    cases e
    change ((s.funcs ++ [.host ft h])[s.funcs.length]?).map FuncInst.type = some ft
    simp [FuncInst.type]
  allocHost_callout := by
    intro _ s _ ft h _ args e _
    cases e
    change status { s with funcs := s.funcs ++ [.host ft h] } (.entry s.funcs.length args) = _
    simp [status]
  memWrite_extends h := memWrite?_extends h
  memWrite_memSize h m' := by
    have := memWrite?_mems h m'
    change (_ : Option Nat) = _
    simp only [memSize?]
    have e := congrArg (Option.map Prod.snd) this
    simpa [Option.map_map, Function.comp_def] using e
  memWrite_memAddrType h m' := by
    have := memWrite?_mems h m'
    change (_ : Option AddrType) = _
    simp only [memAddrType?]
    have e := congrArg (Option.map Prod.fst) this
    simpa [Option.map_map, Function.comp_def] using e
  memWrite_read h := memWrite?_read h
  memWrite_read_other h hd := memWrite?_read_other h hd
  memRead_isSome_iff := memRead?_isSome_iff
  memRead_size := by
    intro _ s m st len bs h
    change memRead? s m st len = some bs at h
    unfold memRead? at h
    cases hs : s.mems[m]? with
    | none => rw [hs] at h; cases h
    | some mi =>
      rw [hs, Option.bind_some] at h
      exact Silmaril.Wasm.Execution.Memory.readBytes_size _ _ _ _ h
  memWrite_isSome_iff := memWrite?_isSome_iff
  memAddrType_isSome_iff := by
    intro _ s m
    change ((s.mems[m]?).map _).isSome ↔ ((s.mems[m]?).map _).isSome
    simp

theorem status_entry_callout {s : Store H} {a args h args'}
    (e : status s (.entry a args) = .callout h args') :
    ∃ ft, s.funcs[a]? = some (.host ft h) := by
  simp only [status] at e
  split at e
  · cases e; exact ⟨_, by assumption⟩
  · cases e
  · cases e

/-- Resuming a thread with a pending call leaves it running or returned. -/
theorem status_resume_pending (s : Store H) (frames : List Frame) (p : Pending H)
    (r : CallResult) :
    status s (resume s (.exec frames (some p)) r) = .running ∨
      ∃ r', status s (resume s (.exec frames (some p)) r) = .returned r' := by
  rcases r with vs | _
  · simp only [resume]
    split
    · rcases frames with _ | ⟨fr, rest⟩
      · exact Or.inr ⟨_, rfl⟩
      · simp only
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

instance : mock.ResumeLawful where
  resume_unparked := by
    intro _ s s' t h args r e hx
    have e' := hx.callout t h args e
    change status _ _ = _ at e e'
    show status s' (resume s' t r) = .running ∨ ∃ r', status s' (resume s' t r) = .returned r'
    rcases t with ⟨a, args'⟩ | ⟨frames, _ | p⟩ | r0
    · obtain ⟨ft, hf⟩ := status_entry_callout e'
      right
      exact ⟨checkResult ft.results r, by simp [resume, hf, status]⟩
    · simp [status] at e
      rcases frames with _ | ⟨fr, rest⟩ <;> simp at e
    · exact status_resume_pending s' frames p r
    · exact Or.inr ⟨_, rfl⟩

/-! ## Tests -/

namespace Test

def i32 (n : Nat) : FlatValue := Value.int .i32 (BitVec.ofNat 32 n)
def i64 (n : Nat) : FlatValue := Value.int .i64 (BitVec.ofNat 64 n)

/-- One function `read(ptr : i64) : i32` over a 64-byte i64 memory; it first writes
`01 02 03 04` at address 8, then loads 4 bytes at `ptr`. -/
def mem64Module : Module where
  funcs := [⟨⟨[.int .i64], [.int .i32]⟩,
    [.const 1 (i64 8), .memWrite 0 1 0 [1, 2, 3, 4], .arg 0 0, .load32 2 0 0 0, .ret [2]]⟩]
  memories := [(.i64, 64)]
  exports := [("read", .func 0), ("mem", .memory 0)]

def mem64Store : Store Nat := ((prepare? {} mem64Module []).map (·.1)).getD {}

def runRead (p : FlatValue) : Status Nat :=
  let c := (mockExec.runCore 10 (mem64Store, mock.invoke (0 : Nat) [p])).1
  mock.status c.1 c.2

/-- Pointer-width check of a memory access: the function takes an `i32` and uses it directly
as the pointer of a `load32` on the i64 memory. -/
def mem64PtrModule (useExtend : Bool) : Module where
  funcs := [⟨⟨[.int .i32], [.int .i32]⟩,
    [.arg 0 0] ++ (if useExtend then [.extendU 0 0] else []) ++ [.load32 1 0 0 0, .ret [1]]⟩]
  memories := [(.i64, 16)]

def runPtr (useExtend : Bool) : Status Nat :=
  let s := ((prepare? ({} : Store Nat) (mem64PtrModule useExtend) []).map (·.1)).getD {}
  let c := (mockExec.runCore 10 (s, mock.invoke (0 : Nat) [i32 4])).1
  mock.status c.1 c.2

/-- An i64 table: `f0 : [] → [i32]` returns 7, `f1 : [] → [i64]`; the table is
`[null, f0, f1]` at address type i64. `run(i : i64)` calls entry `i` at type `[] → [i32]`. -/
def table64Module : Module where
  funcs := [⟨⟨[], [.int .i32]⟩, [.const 0 (i32 7), .ret [0]]⟩,
    ⟨⟨[], [.int .i64]⟩, [.const 0 (i64 7), .ret [0]]⟩,
    ⟨⟨[.int .i64], [.int .i32]⟩,
      [.arg 0 0, .callIndirect 0 0 ⟨[], [.int .i32]⟩ [] [1], .ret [1]]⟩]
  tables := [(.i64, [none, some 0, some 1])]
  exports := [("run", .func 2), ("tbl", .table 0)]

def table64Store : Store Nat := ((prepare? {} table64Module []).map (·.1)).getD {}

def runTable (p : FlatValue) : Status Nat :=
  let c := (mockExec.runCore 10 (table64Store, mock.invoke (2 : Nat) [p])).1
  mock.status c.1 c.2

/-- A module importing a host function `env.f : [i32 i32] → [i32]` and exporting
`run(x) = 2 * f(x, 5)`. -/
def calloutModule : Module where
  imports := [("env", "f", .func ⟨[.int .i32, .int .i32], [.int .i32]⟩)]
  funcs := [⟨⟨[.int .i32], [.int .i32]⟩,
    [.arg 0 0, .const 1 (i32 5), .call 0 [0, 1] [2], .binop .i32 .add 3 2 2, .ret [3]]⟩]
  exports := [("run", .func 1)]

def hostStore : Store Nat × Nat := allocHost {} ⟨[.int .i32, .int .i32], [.int .i32]⟩ 42

def calloutStore : Store Nat :=
  ((prepare? hostStore.1 calloutModule [.func hostStore.2]).map (·.1)).getD {}

def calloutRun : mock.Config Nat :=
  (mockExec.runCore 10 (calloutStore, mock.invoke (1 : Nat) [i32 7])).1

/-- Resume the parked run with a host result and run to completion. -/
def resumeRun (r : CallResult) : Status Nat :=
  let c := (mockExec.runCore 10 (calloutRun.1, mock.resume calloutRun.1 calloutRun.2 r)).1
  mock.status c.1 c.2

end Test

end Silmaril.Wasm.Component.Engine.Mock
