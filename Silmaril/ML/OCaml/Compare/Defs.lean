module

public import Silmaril.ML.OCaml.Value.Defs

/-!
# Polymorphic comparison (`caml_compare`)

`compareValues st v₁ v₂` follows `runtime/compare.c` of OCaml 5.4 on the
values of the model:

* immediates (`int`, constant constructors) are compared as integers and are
  smaller than every block;
* blocks are compared by tag, then by size, then field by field from the
  left; strings and bytes (tag 252) byte-wise, then by length;
* `Int32`/`Int64` (custom blocks) as signed integers, Zarith integers
  numerically, exception constructors by their identity;
* mutable objects are compared by contents, read from the store;
* two functional values raise `Invalid_argument "compare: functional value"`.

Floats, channels and mixed custom blocks are not modelled: the result is
`none` (stuck). The traversal uses an explicit worklist, as `compare.c`
does, with a fuel bound of `2 ^ 64` visited pairs; a cyclic structure
exhausts it and is also stuck (OCaml loops or overflows its stack).
-/

@[expose] public section
namespace Silmaril.ML.OCaml

/-- The runtime shape of a value, as seen by `compare.c`. -/
inductive CmpView where
  | imm (n : Int)
  | blk (tag : Nat) (fs : List Value)
  /-- Strings and bytes (`String_tag` = 252). -/
  | bytes (bs : List UInt8)
  /-- Custom blocks: `kind` 0 = Int32, 1 = Int64, 2 = Zarith. -/
  | custom (kind : Nat) (n : Int)
  /-- Exception constructors (`Object_tag` = 248), by identity. -/
  | obj (id : Nat)
  /-- Closures (`Closure_tag` = 247). -/
  | fn

def CmpView.tag : CmpView → Nat
  | .imm _ => 0
  | .blk t _ => t
  | .bytes _ => 252
  | .custom _ _ => 255
  | .obj _ => 248
  | .fn => 247

def cmpView (st : Store) : Value → Option CmpView
  | .int n => some (.imm n.toInt)
  | .cconst t => some (.imm t)
  | .int32 n => some (.custom 0 n.toInt)
  | .int64 n => some (.custom 1 n.toInt)
  | .z n => some (.custom 2 n)
  | .str bs => some (.bytes bs)
  | .float _ => none
  | .block t fs => some (.blk t fs)
  | .mod fs => some (.blk 0 fs)
  | .exnTag i _ => some (.obj i)
  | .exn i _ [] => some (.obj i)
  | .exn i n args => some (.blk 0 (.exnTag i n :: args))
  | .loc l => match st.get? l with
    | some (.fields vs) => some (.blk 0 vs)
    | some (.bytes bs) => some (.bytes bs)
    | _ => none
  | .clos .. | .rclos .. | .prim .. | .fctor .. | .fcoerce .. => some .fn

/-- Result of a comparison: an ordering, or the functional-value error. -/
inductive CmpResult where
  | ord (o : Ordering)
  | functional

/-- Byte-wise comparison, then by length (`caml_string_compare`). -/
def compareBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else compareBytes as bs

/-- One step of `compare.c` on the pair at the head of the worklist. -/
def compareWork : Nat → Store → List (Value × Value) → Option CmpResult
  | 0, _, _ => none
  | _ + 1, _, [] => some (.ord .eq)
  | n + 1, st, (a, b) :: rest =>
    match cmpView st a, cmpView st b with
    | some (.imm x), some (.imm y) =>
      if x = y then compareWork n st rest else some (.ord (Ord.compare x y))
    -- Zarith's `compare_ext`: a small (immediate) `Z.t` against a large one
    | some (.imm x), some (.custom 2 y) => some (.ord (Ord.compare x y))
    | some (.custom 2 x), some (.imm y) => some (.ord (Ord.compare x y))
    | some (.imm _), some _ => some (.ord .lt)
    | some _, some (.imm _) => some (.ord .gt)
    | some va, some vb =>
      if va.tag ≠ vb.tag then some (.ord (Ord.compare va.tag vb.tag)) else
      match va, vb with
      | .blk _ fs, .blk _ gs =>
        if fs.length ≠ gs.length then some (.ord (Ord.compare fs.length gs.length))
        else compareWork n st (fs.zip gs ++ rest)
      | .bytes s, .bytes t =>
        match compareBytes s t with
        | .eq => compareWork n st rest
        | o => some (.ord o)
      | .custom k x, .custom k' y =>
        if k ≠ k' then none
        else if x = y then compareWork n st rest else some (.ord (Ord.compare x y))
      | .obj i, .obj j => if i = j then compareWork n st rest else some (.ord (Ord.compare i j))
      | .fn, .fn => some .functional
      | _, _ => none
    | _, _ => none

def compareValues (st : Store) (a b : Value) : Option CmpResult :=
  compareWork (2 ^ 64) st [(a, b)]

/-- Physical equality `==`, where OCaml specifies it: immediates, mutable
objects and exception constructors. Elsewhere it is stuck. -/
def physEq (a b : Value) : Option Bool :=
  match a, b with
  | .int x, .int y => some (x == y)
  | .cconst x, .cconst y => some (x == y)
  | .int _, .cconst _ | .cconst _, .int _ => none
  | .loc x, .loc y => some (x == y)
  | .exnTag i _, .exnTag j _ => some (i == j)
  | .exn i _ [], .exn j _ [] => some (i == j)
  | _, _ => none

end Silmaril.ML.OCaml
