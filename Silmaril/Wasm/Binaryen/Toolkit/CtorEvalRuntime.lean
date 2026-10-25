module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-! A genuine, bounded constructor-evaluation operation: serialize one scalar
assignment into its global initializer and remove the now-completed start.
Unsupported modules reject explicitly. This is not general constructor execution.
-/

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

def recType (results : List ValType) : RecType :=
  ⟨[⟨true, [], .func ⟨[], results⟩⟩]⟩

def types (t : IntType) : List RecType := [recType [], recType [.num (.int t)]]

def ctor (t : IntType) (value : BitVec t.width) : Func :=
  ⟨⟨0⟩, [], [.intConst t value, .globalSet ⟨0⟩]⟩

def getter : Func := ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩

def exports : List Export := [⟨"get", .func ⟨1⟩⟩, ⟨"state", .global ⟨0⟩⟩]

def mod (t : IntType) (initial value : BitVec t.width) (evaluated : Bool) : Module :=
  { types := types t, globals := [⟨⟨.var, .num (.int t)⟩,
      [.intConst t (if evaluated then value else initial)]⟩],
    funcs := [ctor t value, getter], start := if evaluated then none else some ⟨0⟩,
    exports := exports }

structure Params where
  type : IntType
  initial : BitVec type.width
  value : BitVec type.width

def metadataOk (t : IntType) (ts : List RecType) (es : List Export) : Prop :=
  ts = types t ∧ es = exports

instance (t : IntType) (ts : List RecType) (es : List Export) : Decidable (metadataOk t ts es) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Check the entire source module; no imports, extra definitions, exports or
other initialization effects are silently discarded. -/
def recognize? : Module → Option Params
  | ⟨ts, [], [], [⟨⟨.var, .num (.int .i32)⟩, [.intConst .i32 initial]⟩], [], [],
      [⟨⟨0⟩, [], [.intConst .i32 value, .globalSet ⟨0⟩]⟩,
        ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩], [], [], some ⟨0⟩, es⟩ =>
      if metadataOk .i32 ts es then some ⟨.i32, initial, value⟩ else none
  | ⟨ts, [], [], [⟨⟨.var, .num (.int .i64)⟩, [.intConst .i64 initial]⟩], [], [],
      [⟨⟨0⟩, [], [.intConst .i64 value, .globalSet ⟨0⟩]⟩,
        ⟨⟨1⟩, [], [.globalGet ⟨0⟩]⟩], [], [], some ⟨0⟩, es⟩ =>
      if metadataOk .i64 ts es then some ⟨.i64, initial, value⟩ else none
  | _ => none

def evaluate (m : Module) : Except String Module :=
  match recognize? m with
  | some p => .ok (mod p.type p.initial p.value true)
  | none => .error "ctor-eval: unsupported module; expected the documented closed scalar-assignment constructor"

/-- A total pass-facing view. The partial tool still rejects unsupported input;
composition uses identity fallback rather than erasing or failing the module. -/
def optimize (m : Module) : Module :=
  match recognize? m with
  | some p => mod p.type p.initial p.value true
  | none => m

structure Artifact where
  source : Module
  result : Module
  bytes : ByteArray

/-- Pure checked bytes boundary; output is emitted only for an accepted complete
constructor module with representable specification encoding. -/
def evaluateBytes (input : ByteArray) : Except String Artifact := do
  let source ← (Binary.Core.Decode.decodeModule input).mapError ("ctor-eval: " ++ ·)
  match Validation.validate? source with
  | none => .error "ctor-eval: module validation failed"
  | some _ =>
    let result ← evaluate source
    let bytes ← Exe.encodeModule? result
    pure ⟨source, result, ⟨bytes.toArray⟩⟩

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
