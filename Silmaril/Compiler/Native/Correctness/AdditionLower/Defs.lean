module

public import Silmaril.Compiler.Native.Correctness.AdditionSource.Defs
public import Silmaril.Compiler.Native.Correctness.LiteralEmission.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Cleanup.Defs
/-! Exact actual native addition lowering and its explicit frame placeholder.
The expected syntax is independently stated; real lowering equations are proved
separately. No standalone Mir success or frame/ABI adequacy is assumed. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionLower
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native Silmaril.Compiler.Native.Optimize
open Silmaril.Compile.Contract

def prologue : Mir.Block := ⟨#[.addr 0 "__ccomp_frame" 0], .jump 1⟩

def body (left right : Lir.Word) : Mir.Block :=
  ⟨#[.op (.const 2 left), .op (.unary .sext32 3 2),
    .op (.const 4 right), .op (.unary .sext32 5 4),
    .op (.unary .sext32 6 3), .op (.unary .sext32 7 5),
    .op (.binary .add 8 6 7), .op (.unary .sext32 9 8),
    .op (.unary .sext32 10 9)], .ret [.reg 10]⟩

def fallback : Mir.Block := ⟨#[.op (.const 2 0)], .ret [.reg 2]⟩

def function (left right : Lir.Word) : Mir.Func :=
  { name := "main", params := [], results := 1, blocks := #[prologue, body left right, fallback] }

def unit (left right : Lir.Word) : Mir.Unit := { funcs := #[function left right] }

def artifact (left right : Lir.Word) : Artifact :=
  { mir := unit left right, functions := #[{
      name := "main", signature := ⟨.int 4 true, [], false, true⟩,
      tags := ∅, frameBytes := 0, frameAlign := 16 }], calls := #[] }

def versionedPrologue : Mir.Block :=
  ⟨#[.addr 11 "__ccomp_frame" 0, .op (.move 0 11)], .jump 1⟩

def normalize (value : Lir.Word) : Lir.Word := (value.setWidth 32).signExtend 64

def bodyValue (left right : Lir.Word) : Lir.Word :=
  normalize (normalize (normalize (normalize left) + normalize (normalize right)))

def bodyFrame (frame : Lir.Frame Nat) (left right : Lir.Word) : Lir.Frame Nat :=
  let frame := frame.set 2 left
  let frame := frame.set 3 (normalize left)
  let frame := frame.set 4 right
  let frame := frame.set 5 (normalize right)
  let frame := frame.set 6 (normalize (normalize left))
  let frame := frame.set 7 (normalize (normalize right))
  let frame := frame.set 8 (normalize (normalize left) + normalize (normalize right))
  let frame := frame.set 9 (normalize (normalize (normalize left) + normalize (normalize right)))
  frame.set 10 (bodyValue left right)


end Silmaril.Compiler.Native.Correctness.AdditionLower
