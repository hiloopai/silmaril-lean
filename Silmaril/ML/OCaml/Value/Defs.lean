module

public import Silmaril.ML.OCaml.Syntax.Defs

/-!
# OCaml deep embedding: values and store

Immutable data is first-order (`block`, `cconst`, `str`, …). Mutable
records, `ref`s, `bytes` and output channels are store cells reached through
`loc`. Exceptions are values `exn id name args`; `id` is the identity of the
(possibly generative) exception constructor, allocated from `Store.nextExn`.

Runtime representations follow OCaml where it is observable by polymorphic
comparison: `()`/`false`/`[]`/`None` are `cconst 0`, `true` is `cconst 1`,
`x :: xs` is `block 0 [x, xs]`, tuples and immutable records are blocks of
tag 0, and polymorphic variants are their hash or `(hash, arg)`.
-/

@[expose] public section
namespace Silmaril.ML.OCaml

abbrev Loc := Nat

mutual
inductive Value where
  /-- Native `int`: 63-bit two's complement, wrapping. -/
  | int (n : BitVec 63)
  | int32 (n : BitVec 32)
  | int64 (n : BitVec 64)
  /-- Immutable strings. -/
  | str (bs : List UInt8)
  /-- Opaque in fragment v1. -/
  | float (bits : BitVec 64)
  /-- Zarith integers, produced only by the `Z` override. -/
  | z (n : Int)
  /-- A constant constructor. -/
  | cconst (tag : Nat)
  /-- A constructor with arguments, tuple or immutable record. -/
  | block (tag : Nat) (fs : List Value)
  /-- A mutable object in the store. -/
  | loc (l : Loc)
  /-- An exception constructor. -/
  | exnTag (id : Nat) (name : String)
  /-- An exception value. -/
  | exn (id : Nat) (name : String) (args : List Value)
  | clos (env : List (Ident × Value)) (x : Ident) (body : Expr)
  /-- Function `i` of a `let rec` bundle `f x = e`. -/
  | rclos (env : List (Ident × Value)) (bundle : List (Ident × Ident × Expr)) (i : Nat)
  /-- A primitive awaiting `op.arity - acc.length` more arguments. -/
  | prim (op : PrimOp) (acc : List Value)
  /-- A structure: fields by runtime position. -/
  | mod (fs : List Value)
  | fctor (env : List (Ident × Value)) (x : Ident) (body : ModExpr)
  /-- A functor seen through a signature: coerce the argument, apply, coerce
  the result. -/
  | fcoerce (f : Value) (arg res : Coercion)
end

instance : Inhabited Value := ⟨.cconst 0⟩

abbrev Env := List (Ident × Value)

/-- Store cells. -/
inductive Cell where
  | fields (vs : List Value)
  | bytes (bs : List UInt8)
  /-- An output channel (file descriptor `fd`). Output is recorded in
  `Store.out`; buffering is not modelled. -/
  | chan (fd : Nat)

/-- The store: cells (allocation appends), the next exception id, the
values of linked compilation units and the output written so far, as
(fd, byte) pairs in order. -/
structure Store where
  cells : List Cell := []
  nextExn : Nat := 12
  globals : List (String × Value) := []
  out : List (Nat × UInt8) := []

inductive Outcome where
  | ret (v : Value)
  | exn (v : Value)

instance : Inhabited Outcome := ⟨.ret default⟩

namespace Value
def unit : Value := .cconst 0
def ofBool (b : Bool) : Value := .cconst (if b then 1 else 0)
/-- The boolean a value denotes, if it is one. -/
def toBool? : Value → Option Bool
  | .cconst 0 => some false
  | .cconst 1 => some true
  | _ => none
def ofInt (i : Int) : Value := .int (BitVec.ofInt 63 i)
def nil : Value := .cconst 0
def cons (x xs : Value) : Value := .block 0 [x, xs]
def ofList : List Value → Value
  | [] => nil
  | x :: xs => cons x (ofList xs)
def none : Value := .cconst 0
def some (v : Value) : Value := .block 0 [v]
/-- UTF-8 bytes of a Lean string, by a kernel-reducible definition. -/
def utf8 (s : String) : List UInt8 := s.toList.flatMap String.utf8EncodeChar
def ofString (s : String) : Value := .str (utf8 s)
/-- A constructor: constant if it has no arguments. -/
def ctor (tag : Nat) : List Value → Value
  | [] => .cconst tag
  | vs => .block tag vs
end Value

/-! ## Predefined exceptions (`Predef`) -/

def predefExns : List String :=
  ["Out_of_memory", "Sys_error", "Failure", "Invalid_argument", "End_of_file",
   "Division_by_zero", "Not_found", "Match_failure", "Stack_overflow",
   "Sys_blocked_io", "Assert_failure", "Undefined_recursive_module"]

def predefId (name : String) : Option Nat := predefExns.idxOf? name

def raiseNamed (name : String) (args : List Value) : Outcome :=
  .exn (.exn ((predefId name).getD 0) name args)

def failure (msg : String) : Outcome := raiseNamed "Failure" [.ofString msg]
def invalidArg (msg : String) : Outcome := raiseNamed "Invalid_argument" [.ofString msg]

/-! ## Store operations -/

namespace Store
def get? (st : Store) (l : Loc) : Option Cell := st.cells[l]?
def alloc (st : Store) (c : Cell) : Loc × Store :=
  (st.cells.length, { st with cells := st.cells ++ [c] })
def set (st : Store) (l : Loc) (c : Cell) : Store :=
  { st with cells := st.cells.set l c }
def newExn (st : Store) : Nat × Store :=
  (st.nextExn, { st with nextExn := st.nextExn + 1 })
def output (st : Store) (fd : Nat) (bs : List UInt8) : Store :=
  { st with out := st.out ++ bs.map (fd, ·) }
/-- Bytes written to `fd`. -/
def written (st : Store) (fd : Nat) : List UInt8 :=
  (st.out.filter (·.1 == fd)).map (·.2)
end Store

/-! ## Environments and paths -/

def Env.lookup (env : Env) (x : Ident) : Option Value := List.lookup x env

def Path.eval (env : Env) (st : Store) : Path → Option Value
  | .local x => env.lookup x
  | .global u => st.globals.lookup u
  | .dot p _ pos => match p.eval env st with
    | some (.mod fs) => fs[pos]?
    | _ => none
  | .predef n => (predefId n).map (.exnTag · n)

def Const.toValue : Const → Value
  | .int n => .int n
  | .int32 n => .int32 n
  | .int64 n => .int64 n
  | .str bs => .str bs
  | .float b => .float b

/-- Does value `v` equal the constant `c`? -/
def Const.matches : Const → Value → Bool
  | .int n, .int m => n == m
  | .int32 n, .int32 m => n == m
  | .int64 n, .int64 m => n == m
  | .str s, .str t => s == t
  | .float b, .float c => b == c
  | _, _ => false

/-- The environment of a `let rec` bundle: every function of the bundle,
closed over `env`. -/
def recEnv (env : Env) (bundle : List (Ident × Ident × Expr)) : Env :=
  (bundle.mapIdx fun i b => (b.1, Value.rclos env bundle i)) ++ env

end Silmaril.ML.OCaml
