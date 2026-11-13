module

public import Silmaril.Cerberus.Core.Syntax.Defs
public meta import Silmaril.Cerberus.Core.Syntax.Defs

/-! # Cerberus Core syntax examples

Small Core terms built with the ported syntax over a toy memory model: a pure
expression, the effectful body Cerberus elaborates `int x = 42; return x;` into,
and a one-procedure Core file. The checks at the end show where Lem's equality on
symbols ignores descriptions, and maps use that equality for keys.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.Examples

/-- A toy memory model: integers are `Int`, pointers are optional addresses, and
floats, byte-level values and footprints carry no information. -/
def ToyMem : MemoryModel where
  PointerValue := Option Nat
  IntegerValue := Int
  FloatingValue := Unit
  MemValue := Unit
  Footprint := Unit

/-- The digest of the example translation unit. -/
def tu : Digest := ⟨[0x74, 0x75]⟩

/-- A symbol of the example translation unit. -/
def sym (n : Nat) (name : String) : Sym :=
  ⟨tu, n, .id name⟩

/-- `signed int`. -/
def signedInt : Ctype :=
  .mk [] (.basic (.integer (.signed .int)))

/-- An unannotated, untyped pure expression. -/
def pe (e : PexprNode ToyMem Unit Sym) : Pexpr ToyMem Unit Sym :=
  .mk [] () e

/-- An unannotated effectful expression. -/
def ex (e : ExprNode ToyMem Unit Unit Sym) : Expr ToyMem Unit Unit Sym :=
  .mk [] e

/-- The integer value `n`. -/
def int (n : Int) : Pexpr ToyMem Unit Sym :=
  pe (.val (.object (.integer (show ToyMem.IntegerValue from n))))

/-- A pattern binding `s` at base type `t`. -/
def bind (s : Sym) (t : BaseType) : Pattern Sym :=
  .mk [] (.base (some s, t))

/-- `let x: integer = 1 + 2 in if x < 3 then True else False`. -/
def pureLetIf : Pexpr ToyMem Unit Sym :=
  let x := sym 1 "x"
  pe (.let_ (bind x (.object .integer)) (pe (.op .add (int 1) (int 2)))
    (pe (.if_ (pe (.op .lt (pe (.sym x)) (int 3)))
      (pe (.val .true)) (pe (.val .false)))))

/-- The Core for `int x = 42; return x;`:

```
let strong a_x: pointer = create(Ivalignof('signed int'), 'signed int') in
let strong _: unit = store('signed int', a_x, Specified(42)) in
let strong v: loaded integer = load('signed int', a_x) in
pure(v)
```
-/
def declareStoreLoad : Expr ToyMem Unit Unit Sym :=
  let ax := sym 2 "a_x"
  let v := sym 3 "v"
  let ty := pe (.val (.ctype signedInt))
  let action (act : ActionNode ToyMem Unit Sym) : Expr ToyMem Unit Unit Sym :=
    ex (.action (.mk .pos (.mk .unknown () act)))
  ex (.sseq (bind ax (.object .pointer))
    (action (.create (pe (.ctor .ivAlignof [ty])) ty (.source .unknown [ax])))
    (ex (.sseq (.mk [] (.base (none, .unit)))
      (action (.store false ty (pe (.sym ax)) (pe (.ctor .specified [int 42])) .na))
      (ex (.sseq (bind v (.loaded .integer))
        (action (.load ty (pe (.sym ax)) .na))
        (ex (.pure (pe (.sym v)))))))))

/-- A Core file whose `main` procedure runs `declareStoreLoad`. -/
def mainFile : File ToyMem Unit Unit where
  main := some (sym 0 "main")
  callingConvention := .normal
  tagDefs := ∅
  stdlib := ∅
  impl := ∅
  globs := []
  funs := Map.ofList [(sym 0 "main",
    .procedure .unknown none (.loaded .integer) [] declareStoreLoad)]
  extern := ∅
  funInfo := ∅
  loopAttributes := ∅
  visibleObjects := ∅

example : BaseType.tuple [.unit, .list .boolean] = .tuple [.unit, .list .boolean] := by decide

example : BaseType.tuple [.unit] ≠ .tuple [.unit, .unit] := by decide

example : Ctor.nil (.list .ctype) ≠ .nil .ctype := by decide

/-- The same symbol, described differently. -/
def mainAsReturn : Sym := ⟨tu, 0, .return_⟩

/-- Lem compares symbols by digest and number only; Lean's `=` also compares the
description. -/
example : (sym 0 "main").key = mainAsReturn.key ∧ sym 0 "main" ≠ mainAsReturn := by decide

/-- Map lookups follow Lem's key equality. -/
example : (mainFile.funs.lookup mainAsReturn).isSome := by decide

/-- Two bindings whose keys Lem compares equal are one binding; in a list of
bindings the last one wins. -/
example : (Map.ofList [(sym 0 "main", 1), (mainAsReturn, 2)] : Map Sym Nat).lookup
    (sym 0 "main") = some 2 := by decide

/-- Ordinary duplicate keys also keep the last binding. -/
example : (Map.ofList [(7, 1), (7, 2)] : Map Nat Nat).lookup 7 = some 2 := by decide

/-- Agreement of public lookups suffices for equality, including diagnostic keys. -/
example (m n : Map Sym Nat) (h : ∀ s, m.lookup s = n.lookup s) : m = n :=
  Map.ext_lookup h

example (m n : Map Identifier Nat) (h : ∀ i, m.lookup i = n.lookup i) : m = n :=
  Map.ext_lookup h

/-- Diagnostic symbol descriptions do not affect map equality. -/
example : (Map.ofList [(sym 0 "main", 1)] : Map Sym Nat) =
    Map.ofList [(mainAsReturn, 1)] := by decide

/-- Diagnostic identifier locations do not affect map equality. -/
example : (Map.ofList [(⟨.unknown, "x"⟩, 1)] : Map Identifier Nat) =
    Map.ofList [(⟨.point "test.c" 2 3, "x"⟩, 1)] := by decide

/--
info: Silmaril.Cerberus.Core.Pexpr.mk
  []
  ()
  (Silmaril.Cerberus.Core.PexprNode.op
    (Silmaril.Cerberus.Core.BinOp.add)
    (Silmaril.Cerberus.Core.Pexpr.mk
      []
      ()
      (Silmaril.Cerberus.Core.PexprNode.val
        (Silmaril.Cerberus.Core.Value.object (Silmaril.Cerberus.Core.ObjectValue.integer 1))))
    (Silmaril.Cerberus.Core.Pexpr.mk
      []
      ()
      (Silmaril.Cerberus.Core.PexprNode.val
        (Silmaril.Cerberus.Core.Value.object (Silmaril.Cerberus.Core.ObjectValue.integer 2)))))
-/
#guard_msgs in
#eval pe (.op .add (int 1) (int 2))

end Silmaril.Cerberus.Core.Examples
