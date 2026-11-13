module

public import Silmaril.Cerberus.Mem.Typed.Defs

/-! Sequential startup argument objects at Cerberus b3e11ea3.
References are to frontend/model/driver.lem and backend/common/pipeline.ml. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Startup
open Mem.Concrete

def charType : Ctype := .mk [] (.basic (.integer .char))
def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
def charPointer : Ctype := .mk [] (.pointer ⟨false, false, false⟩ charType)
def argvType : Ctype := .mk [] (.pointer ⟨false, false, false⟩ charPointer)

/-- pipeline.ml:588-594 supplies the command name even without --args. -/
def execArguments (args : List String := []) : List String := "cmdname" :: args

/-- driver.lem:1632-1640 calls Decode on each individual OCaml character.
The pin accepts printable ASCII except a lone backslash, and a literal tab.
Other bytes raise a host exception, so they have no enabled startup here. -/
def stringValue (text : String) : Except Failure MemoryValue := do
  let bytes ← text.toList.mapM fun c =>
    if (32 ≤ c.toNat && c.toNat ≤ 126 && c.toNat != 92) || c.toNat == 9 then
      pure (MemoryValue.integer .char c.toNat)
    else throw (.unsupported "startup character decoder host exception")
  pure (.array (bytes ++ [.integer .char 0]))

inductive Contents where
  | literal : MemoryValue → Contents
  | pointers : Contents
  | arrayPointer : Nat → Contents

structure Object where
  type : Ctype
  contents : Contents
  allocationPrefix : Prefix

/-- driver.lem:1628-1703. Strings precede the pointer array. Normal calling
convention adds addressable int and char** parameter objects in that order. -/
def objects (args : List String) (inner : Bool) (loc : Loc)
    (main argc argv : Sym) : Except Failure (List Object) := do
  let strings ← args.mapM fun text => do
    pure (Object.mk (.mk [] (.array charType (some (text.length + 1))))
      (.literal (← stringValue text)) (.other "argv refs"))
  let array := Object.mk (.mk [] (.array charPointer (some (args.length + 1)))) .pointers (.source loc [main, argv])
  pure (strings ++ [array] ++ if inner then [] else
    [⟨intType, .literal (.integer (.signed .int) args.length), .source loc [main, argc]⟩,
     ⟨argvType, .arrayPointer args.length, .source loc [main, argv]⟩])

/-- driver.lem:1665-1667 reverses the accumulated string pointers and places
one null char pointer last. The list here is already in argument order. -/
def contents (pointers : List Pointer) : Contents → Except Failure MemoryValue
  | .literal v => pure v
  | .pointers => pure (.array
      (pointers.map (.pointer charType) ++ [.pointer charType (.null charType)]))
  | .arrayPointer n => match pointers[n]? with
      | some p => pure (.pointer charPointer p)
      | none => throw (.invalid "startup argv array reference")

end Silmaril.Cerberus.Core.Startup
