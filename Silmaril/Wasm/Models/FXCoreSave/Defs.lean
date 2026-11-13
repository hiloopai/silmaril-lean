module

public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Models.FXAsyncPC.Defs

/-!
# Saving and restoring asyncify frames in Core 3.0: GC records and the mode global

The first-order asyncify machine `Silmaril.Wasm.Models.FXAsyncPC.fstep` keeps its state in a mode
register, a buffer of saved frame records (`Rec`: a function number, a resume index, the saved
operands) and a heap of record lists. `Silmaril.Wasm.Models.FXDispatch` gave the Core 3.0
`br_table` prologue that re-enters a frame at its resume index, and the call-site check on the
mode global. This module states the **save and restore code** of an asyncified Core 3.0
function, with the records as **GC structs**:

* **Records are structs.** A record of a function with `n` saved locals is a struct of `n + 3`
  unpacked fields: the locals `0, …, n-1`, then the function number (`i32`), the resume index
  (`i32`) and a reference to the next record (`next`, a nullable struct reference). `RecTy f x n`
  says that type index `x` of the frame's module expands to such a struct type (every field of
  unpacked storage; the field types are otherwise free).
* **The buffer is a linked list** of records, held in global `b`: `BufIs s v qs` says that the
  value `v` (a null reference or a struct reference) is the head of a chain of structs in store
  `s` whose fields are the records `qs`, head first. The head is the most recently saved record.
  `fstep` appends each saved record at the end of its buffer (top frame first) and rewinds the
  buffer bottom first; the linked list holds that buffer reversed, which is the rewinding order.
* **Saved operands are locals.** As in Binaryen's Asyncify, the operand stack of a frame is
  spilled to locals before a call site, so a record saves the locals `0, …, n-1`. Records here
  carry Core values only (`CRec`); continuation references among the operands of an `fstep`
  record are not encoded.
* **`saveCode x b n fn r`** (run at a check in unwinding mode): read the locals, push `fn`, `r`
  and the old head of the buffer, `struct.new x`, store the new struct in `b`, `return`.
* **`restoreCode x b g n`** (run at the entry of a function in rewinding mode, before the
  dispatch prologue): load the locals from the head record, store its resume index in the
  dispatch global `g`, and pop the record (`b := next`).
* **`setMode m k`**: `i32.const k; global.set m`, the mode transitions of `fstep`
  (`0` normal, `1` unwinding, `2` rewinding).
* **`RecRel q p`** relates a Core record `q` to a record `p` of `fstep` with Core values:
  same function number, same resume index, and the saved locals are the saved operands.
* **`chkCode m x b n fn r`**: the call-site check `FXDispatch.check` with this save code, written
  out here (`global.get m; if (save) end`) so that it does not depend on that module.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- An index of any kind (modulo `2 ^ 32`). -/
def ix {k : IndexKind} (j : Nat) : Idx k := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- A saved record with Core values: the saved locals, the function number and the resume
index. -/
structure CRec where
  locals : List Val
  fn : BitVec 32
  r : BitVec 32

/-- The field values of a record whose next pointer is `nx`. -/
def CRec.fields (q : CRec) (nx : Val) : List Val := q.locals ++ [.i32 q.fn, .i32 q.r, nx]

/-- **Record types**: type index `x` expands to a struct type of `n + 3` fields, all of
unpacked storage. -/
def RecTy (f : Frame) (x : TypeIdx) (n : Nat) : Prop :=
  ∃ d fs, f.type? x = some d ∧ Expand d (.struct fs) ∧ fs.toList.length = n + 3 ∧
    ∀ ft ∈ fs.toList, ∃ t, fieldStorage ft = .val t

/-- **The buffer as a linked list of structs**: `v` heads a chain of records `qs`. -/
inductive BufIs {H : Type} (s : Store H) : Val → List CRec → Prop where
  | nil : BufIs s (.ref .null) []
  | cons {a : Nat} {si : StructInst} {q : CRec} {nx : Val} {qs : List CRec}
      (hs : s.structs[a]? = some si) (hf : si.fields = (q.fields nx).map .val)
      (tl : BufIs s nx qs) : BufIs s (.ref (.struct a)) (q :: qs)

/-- `local.get 0, …, local.get (n-1)`. -/
def getLocals (n : Nat) : List Instr := (List.range n).map fun i => .localGet (ix i)

/-- **The save code** at a check: build the record of this frame and push it on the buffer
in global `b`, then return. -/
def saveCode (x : TypeIdx) (b : GlobalIdx) (n : Nat) (fn r : BitVec 32) : List Instr :=
  getLocals n ++ [.intConst .i32 fn, .intConst .i32 r, .globalGet b, .structNew x, .globalSet b,
    .return_]

/-- Load local `i` from the head record of the buffer. -/
def loadLocal (x : TypeIdx) (b : GlobalIdx) (i : Nat) : List Instr :=
  [.globalGet b, .structGet none x (ix i), .localSet (ix i)]

/-- **The restore code** at the entry of a rewound function: load the locals, store the resume
index in the dispatch global `g`, and pop the record. -/
def restoreCode (x : TypeIdx) (b g : GlobalIdx) (n : Nat) : List Instr :=
  ((List.range n).map (loadLocal x b)).flatten ++
    [.globalGet b, .structGet none x (ix (n + 1)), .globalSet g,
     .globalGet b, .structGet none x (ix (n + 2)), .globalSet b]

/-- **A mode transition**: `i32.const k; global.set m`. -/
def setMode (m : GlobalIdx) (k : BitVec 32) : List Instr := [.intConst .i32 k, .globalSet m]

/-- **The call-site check with its save code**: `global.get m; if (save) end`. -/
def chkCode (m : GlobalIdx) (x : TypeIdx) (b : GlobalIdx) (n : Nat) (fn r : BitVec 32) :
    List Instr :=
  [.globalGet m, .if_ .empty (saveCode x b n fn r) []]

/-- **A Core record and a record of `fstep`** (`FXAsyncPC.Rec` over Core values). -/
def RecRel (q : CRec) (p : Silmaril.Wasm.Models.FXAsyncPC.Rec Val) : Prop :=
  p.fn = q.fn.toNat ∧ p.r = q.r.toNat ∧ p.ops = q.locals.map .val

/-- The locals `0, …, n-1` of a frame hold `ls`. -/
def LocalsAre (f : Frame) (ls : List Val) : Prop :=
  ∀ i (h : i < ls.length), f.local? (ix i) = some (some ls[i])

/-- Set the locals `0, …, n-1` of a frame to `ls`. -/
def setLocals (f : Frame) : List Val → Nat → Frame
  | [], _ => f
  | v :: vs, i => setLocals (f.setLocal (ix i) v) vs (i + 1)

/-- The store after the save code: the record struct of `q` (next pointer `bv`, the old head)
is added, and global address `ab` (the buffer) points to it. -/
def saveStore {H : Type} (s : Store H) (d : DefType) (q : CRec) (bv : Val) (ab : Nat) :
    Store H :=
  (s.addStruct ⟨d, (q.fields bv).map .val⟩).setGlobal ab (.ref (.struct s.structs.length))

/-- The store after the restore code: the dispatch global (address `ag`) holds the resume index
of `q` and the buffer (address `ab`) its next pointer `nx`. -/
def restoreStore {H : Type} (s : Store H) (q : CRec) (nx : Val) (ag ab : Nat) : Store H :=
  (s.setGlobal ag (.i32 q.r)).setGlobal ab nx

end Silmaril.Wasm.Models.FXCoreSave
