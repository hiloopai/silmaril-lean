module

public import Silmaril.Compiler.Native.Emit.Scalar.Defs
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Defs
public import Silmaril.Compiler.Native.Emit.Epilogue.Defs
/-! The actual nine-operation unoptimized addition body selected through the
small modular scalar instruction interface. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionBody
open Silmaril Silmaril.X86

def operations (left right : Word) : List Scalar.Operation :=
  [.constant 0 left, .sext32 1 0, .constant 2 right, .sext32 3 2,
    .sext32 4 1, .sext32 5 3, .add 6 4 5, .sext32 7 6, .sext32 8 7]

def instructions (left right : Word) : List Ext.Instr :=
  (operations left right).flatMap Scalar.Operation.instructions

def code (left right : Word) : List Byte := (instructions left right).flatMap Ext.encode

def render (left right : Word) : String :=
  (operations left right).foldl (fun text operation => text ++ operation.render) ""

abbrev Entry := Scalar.Entry

abbrev Ready (stack : Word) (before after : X86.MState) (left right : Word) :=
  Scalar.Result stack before after (Correctness.AdditionLower.bodyFrame .empty left right) 109

end Silmaril.Compiler.Native.Emit.AdditionBody
