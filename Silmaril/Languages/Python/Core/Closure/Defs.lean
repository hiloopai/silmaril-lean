module

public import Silmaril.Languages.Python.Core.Module.Defs

/-! # Slot and cell interfaces for lowered Python closures -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure

/-- Counts of direct locals, frame-owned cells and incoming captures. -/
structure Layout where
  locals : Nat
  owned : Nat
  captures : Nat
  deriving DecidableEq, Repr

inductive Slot (layout : Layout) where
  | local (index : Fin layout.locals)
  | owned (index : Fin layout.owned)
  | capture (index : Fin layout.captures)
  deriving DecidableEq, Repr

/-- Parameters initialize a direct local or a cell owned by the callee. -/
inductive ParameterSlot (layout : Layout) where
  | local (index : Fin layout.locals)
  | owned (index : Fin layout.owned)
  deriving DecidableEq, Repr

def ParameterSlot.slot {layout : Layout} : ParameterSlot layout → Slot layout
  | .local index => .local index
  | .owned index => .owned index

/-- Declaration order for the fixed positional profile. -/
structure Parameters (layout : Layout) where
  slots : List (ParameterSlot layout)
  distinct : slots.Nodup

inductive CaptureSlot (layout : Layout) where
  | owned (index : Fin layout.owned)
  | forwarded (index : Fin layout.captures)
  deriving DecidableEq, Repr

structure CellId where
  address : Nat
  deriving DecidableEq, Repr

/-- A code-table key records the layout expected by its frame. -/
structure CodeRef where
  key : Nat
  layout : Layout
  deriving DecidableEq, Repr

structure Function where
  code : CodeRef
  captures : Vector CellId code.layout.captures
  positionalDefaults : List Core.Module.Value := []
  deriving DecidableEq, Repr

/-- Import a compiler-produced capture list in its existing order. -/
def Function.ofCaptureList (code : CodeRef) (captures : List CellId)
    (size : captures.length = code.layout.captures) : Function :=
  ⟨code, ⟨captures.toArray, by simpa using size⟩, []⟩

inductive Value where
  | none
  | int (value : Int)
  | bool (value : Bool)
  | function (value : Function)
  deriving Repr

def Value.ofScalar : Core.Module.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none

def Value.truth : Value → Bool
  | .none => false
  | .int value => decide (value ≠ 0)
  | .bool value => value
  | .function _ => true

/-- Compare a value in this closed closure profile with an integer literal. -/
def Value.equalInt : Value → Int → Bool
  | .int value, right => decide (value = right)
  | .bool false, right => decide (0 = right)
  | .bool true, right => decide (1 = right)
  | .none, _ | .function _, _ => false

/-- Python-level errors carried across frames. An unbound incoming capture
corresponds to `NameError`; an unbound local or owned cell to `UnboundLocalError`. -/
inductive RuntimeError where
  | unboundLocal (slot : Nat)
  | unboundOwned (slot : Nat)
  | unboundCapture (slot : Nat)
  | nameError (name : String)
  | positionalArity (expected actual : Nat)
  | notCallable
  | additionTypeError
  | multiplicationTypeError
  | assertionError
  | arithmetic (error : Exception)
  deriving DecidableEq, Repr

/-- Invalid runtime references are distinct from defined Python exceptions. -/
inductive Failure where
  | defined (error : RuntimeError)
  | danglingCell (identity : CellId)
  | invalidPositionalDefaults
  deriving DecidableEq, Repr

/-- Integer-like values in the closed closure value profile. -/
def Value.asInt? : Value → Option Int
  | .int value => some value
  | .bool false => some 0
  | .bool true => some 1
  | .none | .function _ => Option.none

inductive IntegerOp where
  | add
  | mul
  deriving DecidableEq, Repr

def IntegerOp.eval : IntegerOp → Int → Int → Int
  | .add, lhs, rhs => lhs + rhs
  | .mul, lhs, rhs => lhs * rhs

def IntegerOp.typeError : IntegerOp → RuntimeError
  | .add => .additionTypeError
  | .mul => .multiplicationTypeError

/-- Apply exact integer arithmetic after both operands have been read.
The other modeled values are None and plain functions. -/
def Value.binaryInt (op : IntegerOp) (left right : Value) : Except Failure Value :=
  match left.asInt?, right.asInt? with
  | some lhs, some rhs => .ok (.int (op.eval lhs rhs))
  | _, _ => .error (.defined op.typeError)

abbrev Value.addInt := Value.binaryInt .add

abbrev Result := Except RuntimeError Value

/-- A shared heap with monotone cell allocation. Only addresses below
`next` denote allocated cells. An allocated cell may be unbound. -/
structure Heap where
  next : Nat
  contents : Nat → Option Value

def Heap.empty : Heap := ⟨0, fun _ => none⟩

def Heap.lookup (heap : Heap) (identity : CellId) : Option (Option Value) :=
  if identity.address < heap.next then some (heap.contents identity.address) else none

def Heap.reserve (heap : Heap) (count : Nat) : Heap :=
  ⟨heap.next + count, fun address => if address < heap.next then heap.contents address else none⟩

def Heap.write (heap : Heap) (identity : CellId) (value : Value) : Option Heap :=
  if identity.address < heap.next then
    some ⟨heap.next, fun address => if address = identity.address then some value else heap.contents address⟩
  else none

structure Frame (layout : Layout) where
  locals : Fin layout.locals → Option Value
  owned : Fin layout.owned → CellId
  captures : Fin layout.captures → CellId

variable {layout : Layout}

/-- Allocate owned cells in slot order. Incoming captures keep their identities. -/
def Frame.fresh (heap : Heap) (captures : Fin layout.captures → CellId) : Heap × Frame layout :=
  (heap.reserve layout.owned,
    ⟨fun _ => none, fun slot => ⟨heap.next + slot.val⟩, captures⟩)

def Function.freshFrame (fn : Function) (heap : Heap) : Heap × Frame fn.code.layout :=
  Frame.fresh heap fn.captures.get

def Frame.captureCell (frame : Frame layout) : CaptureSlot layout → CellId
  | .owned index => frame.owned index
  | .forwarded index => frame.captures index

/-- Use the child's index order and retain each selected parent identity. -/
def Frame.closure (frame : Frame layout) (code : CodeRef)
    (select : Fin code.layout.captures → CaptureSlot layout) : Function :=
  ⟨code, Vector.ofFn (frame.captureCell ∘ select), []⟩

def Heap.read (heap : Heap) (identity : CellId) (unbound : RuntimeError) : Except Failure Value :=
  match heap.lookup identity with
  | none => .error (.danglingCell identity)
  | some none => .error (.defined unbound)
  | some (some value) => .ok value

def Frame.read (frame : Frame layout) (heap : Heap) : Slot layout → Except Failure Value
  | .local index =>
    match frame.locals index with
    | none => .error (.defined (.unboundLocal index.val))
    | some value => .ok value
  | .owned index => heap.read (frame.owned index) (.unboundOwned index.val)
  | .capture index => heap.read (frame.captures index) (.unboundCapture index.val)

def Frame.writeCell (frame : Frame layout) (heap : Heap) (identity : CellId)
    (value : Value) : Except Failure (Heap × Frame layout) :=
  match heap.write identity value with
  | none => .error (.danglingCell identity)
  | some heap' => .ok (heap', frame)

def Frame.write (frame : Frame layout) (heap : Heap) (slot : Slot layout)
    (value : Value) : Except Failure (Heap × Frame layout) :=
  match slot with
  | .local index =>
    .ok (heap, { frame with locals := fun slot => if slot = index then some value else frame.locals slot })
  | .owned index => frame.writeCell heap (frame.owned index) value
  | .capture index => frame.writeCell heap (frame.captures index) value

end Silmaril.Languages.Python.Core.Closure
