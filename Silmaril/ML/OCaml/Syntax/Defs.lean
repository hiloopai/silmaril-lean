module

public import Silmaril.Prelude.Defs

/-!
# OCaml deep embedding: syntax

The untyped image of an OCaml 5.4 `Typedtree` after the importer's
desugaring (`docs/projects/wasm-wasi.md`). Types are erased; the typechecker's
results that matter at runtime are kept as data:

* identifiers carry the typechecker's stamp, so shadowing is resolved;
* global references are paths `unit.field₁.field₂…` with field positions;
* constructors carry their runtime tag (constant constructors and
  constructors with arguments are numbered separately, as in OCaml);
* every n-ary node carries a `NodeId`, so an evaluation order can be
  chosen per node (`Order`).

Polymorphic variants are not a separate form: the importer emits
`` `A `` as the integer hash and `` `A e `` as the pair `(hash, e)`, which is
OCaml's runtime representation. `function`, binding operators, labels,
optional arguments, `(@@)`, `(|>)`, `&&`, `||` and local opens are
desugared by the importer (an OCaml-to-Lean import tool).
-/

@[expose] public section
namespace Silmaril.ML.OCaml

/-- A typechecker identifier: source name and unique stamp. -/
structure Ident where
  name : String
  stamp : Nat
  deriving Repr, Inhabited

/-- Equality of identifiers compares stamps first: stamps are numerals, which
the kernel compares quickly, and differ for almost every pair compared during
environment lookup, so names are compared only when stamps agree. -/
instance : DecidableEq Ident := fun a b =>
  if hs : a.stamp = b.stamp then
    if hn : a.name = b.name then isTrue (by cases a; cases b; simp_all)
    else isFalse (by intro h; exact hn (congrArg Ident.name h))
  else isFalse (by intro h; exact hs (congrArg Ident.stamp h))

/-- Source position of an n-ary node: file, line, column and a counter that
separates nodes at the same position. -/
structure NodeId where
  file : String
  line : Nat
  col : Nat
  counter : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Runtime paths. `dot p name pos` projects field `pos` (the runtime
position computed by the typechecker; `name` is documentation). -/
inductive Path where
  | local (x : Ident)
  | global (unit : String)
  | dot (p : Path) (name : String) (pos : Nat)
  /-- A predefined exception of `Predef` (`Not_found`, `Failure`, …). -/
  | predef (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Literal constants. Strings are byte lists; character literals are
integers, as at runtime (`Char.code` is `%identity`). -/
inductive Const where
  | int (n : BitVec 63)
  | int32 (n : BitVec 32)
  | int64 (n : BitVec 64)
  | str (bs : List UInt8)
  /-- Floats are kept as IEEE bits and are opaque in fragment v1. -/
  | float (bits : BitVec 64)
  deriving DecidableEq, Repr, Inhabited

/-- The OCaml primitives (`external … = "name"`) of the model. Unsupported
externals are kept by name (`ext`); applying one is stuck. -/
inductive PrimOp where
  -- native int
  | negint | succint | predint | addint | subint | mulint | divint | modint
  | andint | orint | xorint | lslint | lsrint | asrint
  -- polymorphic comparison
  | equal | notequal | lessthan | lessequal | greaterthan | greaterequal | compare
  | eq | noteq
  -- booleans and control
  | boolnot | sequand | sequor | identity | ignore | raise | reraise | raiseNotrace
  -- references and fields
  | makemutable | field0 | field1 | setfield0 | incr | decr
  -- Int32 / Int64
  | int32Neg | int32Add | int32Sub | int32Mul | int32Div | int32Mod
  | int32And | int32Or | int32Xor | int32Lsl | int32Lsr | int32Asr
  | int32OfInt | int32ToInt
  | int64Neg | int64Add | int64Sub | int64Mul | int64Div | int64Mod
  | int64And | int64Or | int64Xor | int64Lsl | int64Lsr | int64Asr
  | int64OfInt | int64ToInt | int64OfInt32 | int64ToInt32
  | formatInt | int32Format | int64Format
  -- strings and bytes
  | stringLength | stringSafeGet | stringUnsafeGet
  | stringEqual | stringNotequal | stringCompare
  | bytesLength | bytesSafeGet | bytesUnsafeGet | bytesSafeSet | bytesUnsafeSet
  | createBytes | blitString | blitBytes | fillBytes | bytesToString | bytesOfString
  -- channels (output only) and runtime registration
  | openDescriptorOut | openDescriptorIn | mlOutput | mlOutputBytes | mlOutputChar
  | mlFlush | outChannelsList | registerNamedValue
  -- atomics (single domain: plain cells)
  | atomicLoad | atomicExchange | atomicCas | atomicFetchAdd | atomicSet
  -- Zarith, on `Int` (used only by the whole-unit override `Override.zUnit`)
  | zOfInt | zFitsInt | zToIntUnsafe | zAdd | zSub | zMul | zDiv | zRem | zNeg | zAbs
  | zCompare | zEqual | zLt | zLeq | zGt | zGeq | zToString | zSign | zPow
  -- `Sys` configuration (compile-time constants of x86-64 `ocamlopt`) and
  -- `%raise_with_backtrace` (backtraces are not modelled)
  | wordSize | intSize | maxWosize | bigEndian | ioBufferSize | raiseWithBacktrace
  | ext (name : String) (arity : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Primitive name table: OCaml external name, model operation, arity. -/
def PrimOp.table : List (String × PrimOp × Nat) :=
  [("%negint", .negint, 1), ("%succint", .succint, 1), ("%predint", .predint, 1),
   ("%addint", .addint, 2), ("%subint", .subint, 2), ("%mulint", .mulint, 2),
   ("%divint", .divint, 2), ("%modint", .modint, 2), ("%andint", .andint, 2),
   ("%orint", .orint, 2), ("%xorint", .xorint, 2), ("%lslint", .lslint, 2),
   ("%lsrint", .lsrint, 2), ("%asrint", .asrint, 2),
   ("%equal", .equal, 2), ("%notequal", .notequal, 2), ("%lessthan", .lessthan, 2),
   ("%lessequal", .lessequal, 2), ("%greaterthan", .greaterthan, 2),
   ("%greaterequal", .greaterequal, 2), ("%compare", .compare, 2),
   ("%eq", .eq, 2), ("%noteq", .noteq, 2),
   ("%boolnot", .boolnot, 1), ("%sequand", .sequand, 2), ("%sequor", .sequor, 2),
   ("%identity", .identity, 1), ("%ignore", .ignore, 1), ("%raise", .raise, 1),
   ("%reraise", .reraise, 1), ("%raise_notrace", .raiseNotrace, 1),
   ("%makemutable", .makemutable, 1), ("%field0", .field0, 1), ("%field1", .field1, 1),
   ("%setfield0", .setfield0, 2), ("%incr", .incr, 1), ("%decr", .decr, 1),
   ("%int32_neg", .int32Neg, 1), ("%int32_add", .int32Add, 2), ("%int32_sub", .int32Sub, 2),
   ("%int32_mul", .int32Mul, 2), ("%int32_div", .int32Div, 2), ("%int32_mod", .int32Mod, 2),
   ("%int32_and", .int32And, 2), ("%int32_or", .int32Or, 2), ("%int32_xor", .int32Xor, 2),
   ("%int32_lsl", .int32Lsl, 2), ("%int32_lsr", .int32Lsr, 2), ("%int32_asr", .int32Asr, 2),
   ("%int32_of_int", .int32OfInt, 1), ("%int32_to_int", .int32ToInt, 1),
   ("%int64_neg", .int64Neg, 1), ("%int64_add", .int64Add, 2), ("%int64_sub", .int64Sub, 2),
   ("%int64_mul", .int64Mul, 2), ("%int64_div", .int64Div, 2), ("%int64_mod", .int64Mod, 2),
   ("%int64_and", .int64And, 2), ("%int64_or", .int64Or, 2), ("%int64_xor", .int64Xor, 2),
   ("%int64_lsl", .int64Lsl, 2), ("%int64_lsr", .int64Lsr, 2), ("%int64_asr", .int64Asr, 2),
   ("%int64_of_int", .int64OfInt, 1), ("%int64_to_int", .int64ToInt, 1),
   ("%int64_of_int32", .int64OfInt32, 1), ("%int64_to_int32", .int64ToInt32, 1),
   ("caml_format_int", .formatInt, 2), ("caml_int32_format", .int32Format, 2),
   ("caml_int64_format", .int64Format, 2),
   ("%string_length", .stringLength, 1), ("%string_safe_get", .stringSafeGet, 2),
   ("%string_unsafe_get", .stringUnsafeGet, 2), ("caml_string_equal", .stringEqual, 2),
   ("caml_string_notequal", .stringNotequal, 2), ("caml_string_compare", .stringCompare, 2),
   ("%bytes_length", .bytesLength, 1), ("%bytes_safe_get", .bytesSafeGet, 2),
   ("%bytes_unsafe_get", .bytesUnsafeGet, 2), ("%bytes_safe_set", .bytesSafeSet, 3),
   ("%bytes_unsafe_set", .bytesUnsafeSet, 3), ("caml_create_bytes", .createBytes, 1),
   ("caml_blit_string", .blitString, 5), ("caml_blit_bytes", .blitBytes, 5),
   ("caml_fill_bytes", .fillBytes, 4), ("%bytes_to_string", .bytesToString, 1),
   ("%bytes_of_string", .bytesOfString, 1),
   ("caml_ml_open_descriptor_out", .openDescriptorOut, 1),
   ("caml_ml_open_descriptor_in", .openDescriptorIn, 1),
   ("caml_ml_output", .mlOutput, 4), ("caml_ml_output_bytes", .mlOutputBytes, 4),
   ("caml_ml_output_char", .mlOutputChar, 2), ("caml_ml_flush", .mlFlush, 1),
   ("caml_ml_out_channels_list", .outChannelsList, 1),
   ("caml_register_named_value", .registerNamedValue, 2),
   ("%atomic_load", .atomicLoad, 1), ("%atomic_exchange", .atomicExchange, 2),
   ("%atomic_cas", .atomicCas, 3), ("%atomic_fetch_add", .atomicFetchAdd, 2),
   ("%atomic_set", .atomicSet, 2),
   ("lean_z_of_int", .zOfInt, 1), ("lean_z_fits_int", .zFitsInt, 1),
   ("lean_z_to_int_unsafe", .zToIntUnsafe, 1), ("lean_z_add", .zAdd, 2),
   ("lean_z_sub", .zSub, 2), ("lean_z_mul", .zMul, 2), ("lean_z_div", .zDiv, 2),
   ("lean_z_rem", .zRem, 2), ("lean_z_neg", .zNeg, 1), ("lean_z_abs", .zAbs, 1),
   ("lean_z_compare", .zCompare, 2), ("lean_z_equal", .zEqual, 2), ("lean_z_lt", .zLt, 2),
   ("lean_z_leq", .zLeq, 2), ("lean_z_gt", .zGt, 2), ("lean_z_geq", .zGeq, 2),
   ("lean_z_to_string", .zToString, 1),
   ("%word_size", .wordSize, 1), ("%int_size", .intSize, 1), ("%max_wosize", .maxWosize, 1),
   ("%big_endian", .bigEndian, 1), ("caml_sys_io_buffer_size", .ioBufferSize, 1),
   ("%raise_with_backtrace", .raiseWithBacktrace, 2),
   -- Zarith's own externals (`z.mli`), on the representation of `zVal`
   ("ml_z_fits_int", .zFitsInt, 1), ("ml_z_equal", .zEqual, 2), ("ml_z_compare", .zCompare, 2),
   ("ml_z_sign", .zSign, 1), ("ml_z_pow", .zPow, 2)]

/-- The model operation of an external `name` declared with `arity`
arguments. Unknown names and arity mismatches give `ext`. -/
def PrimOp.ofName (name : String) (arity : Nat) : PrimOp :=
  match PrimOp.table.find? (·.1 == name) with
  | some (_, op, n) => if n == arity then op else .ext name arity
  | none => .ext name arity

def PrimOp.arity : PrimOp → Nat
  | .negint => 1
  | .succint => 1
  | .predint => 1
  | .addint => 2
  | .subint => 2
  | .mulint => 2
  | .divint => 2
  | .modint => 2
  | .andint => 2
  | .orint => 2
  | .xorint => 2
  | .lslint => 2
  | .lsrint => 2
  | .asrint => 2
  | .equal => 2
  | .notequal => 2
  | .lessthan => 2
  | .lessequal => 2
  | .greaterthan => 2
  | .greaterequal => 2
  | .compare => 2
  | .eq => 2
  | .noteq => 2
  | .boolnot => 1
  | .sequand => 2
  | .sequor => 2
  | .identity => 1
  | .ignore => 1
  | .raise => 1
  | .reraise => 1
  | .raiseNotrace => 1
  | .makemutable => 1
  | .field0 => 1
  | .field1 => 1
  | .setfield0 => 2
  | .incr => 1
  | .decr => 1
  | .int32Neg => 1
  | .int32Add => 2
  | .int32Sub => 2
  | .int32Mul => 2
  | .int32Div => 2
  | .int32Mod => 2
  | .int32And => 2
  | .int32Or => 2
  | .int32Xor => 2
  | .int32Lsl => 2
  | .int32Lsr => 2
  | .int32Asr => 2
  | .int32OfInt => 1
  | .int32ToInt => 1
  | .int64Neg => 1
  | .int64Add => 2
  | .int64Sub => 2
  | .int64Mul => 2
  | .int64Div => 2
  | .int64Mod => 2
  | .int64And => 2
  | .int64Or => 2
  | .int64Xor => 2
  | .int64Lsl => 2
  | .int64Lsr => 2
  | .int64Asr => 2
  | .int64OfInt => 1
  | .int64ToInt => 1
  | .int64OfInt32 => 1
  | .int64ToInt32 => 1
  | .formatInt => 2
  | .int32Format => 2
  | .int64Format => 2
  | .stringLength => 1
  | .stringSafeGet => 2
  | .stringUnsafeGet => 2
  | .stringEqual => 2
  | .stringNotequal => 2
  | .stringCompare => 2
  | .bytesLength => 1
  | .bytesSafeGet => 2
  | .bytesUnsafeGet => 2
  | .bytesSafeSet => 3
  | .bytesUnsafeSet => 3
  | .createBytes => 1
  | .blitString => 5
  | .blitBytes => 5
  | .fillBytes => 4
  | .bytesToString => 1
  | .bytesOfString => 1
  | .openDescriptorOut => 1
  | .openDescriptorIn => 1
  | .mlOutput => 4
  | .mlOutputBytes => 4
  | .mlOutputChar => 2
  | .mlFlush => 1
  | .outChannelsList => 1
  | .registerNamedValue => 2
  | .atomicLoad => 1
  | .atomicExchange => 2
  | .atomicCas => 3
  | .atomicFetchAdd => 2
  | .atomicSet => 2
  | .zOfInt => 1
  | .zFitsInt => 1
  | .zToIntUnsafe => 1
  | .zAdd => 2
  | .zSub => 2
  | .zMul => 2
  | .zDiv => 2
  | .zRem => 2
  | .zNeg => 1
  | .zAbs => 1
  | .zCompare => 2
  | .zEqual => 2
  | .zLt => 2
  | .zLeq => 2
  | .zGt => 2
  | .zGeq => 2
  | .zToString => 1
  | .zSign => 1
  | .zPow => 2
  | .wordSize => 1
  | .intSize => 1
  | .maxWosize => 1
  | .bigEndian => 1
  | .ioBufferSize => 1
  | .raiseWithBacktrace => 2
  | .ext _ n => n

/-- Module coercions (`Includemod`), applied when a structure or functor is
constrained by a signature. Positions index the fields of the source. -/
inductive Coercion where
  | id
  | struct (fs : List (Nat × Coercion))
  | functor (arg res : Coercion)
  /-- A `val` in the signature implemented by an `external`. -/
  | prim (op : PrimOp)
  deriving Repr, Inhabited

/-- Patterns. Constructor tags are runtime tags: `ctor t []` is the `t`-th
constant constructor, `ctor t ps` with `ps ≠ []` the `t`-th constructor with
arguments. Record patterns list (position, pattern) pairs. -/
inductive Pat where
  | any
  | var (x : Ident)
  | alias (p : Pat) (x : Ident)
  | const (c : Const)
  | tuple (ps : List Pat)
  | ctor (tag : Nat) (ps : List Pat)
  | exnCtor (p : Path) (ps : List Pat)
  | record (fs : List (Nat × Pat))
  | or (p q : Pat)
  deriving Repr, Inhabited

mutual
/-- Expressions. -/
inductive Expr where
  | path (p : Path)
  | const (c : Const)
  /-- A primitive (`external`) referenced as a value. -/
  | prim (op : PrimOp)
  | fn (x : Ident) (body : Expr)
  /-- `f a₁ … aₙ`; the subterms are `f :: args`. -/
  | app (id : NodeId) (f : Expr) (args : List Expr)
  /-- `let p₁ = e₁ and … in body`. -/
  | let_ (id : NodeId) (bs : List (Pat × Expr)) (body : Expr)
  /-- `let rec f₁ x₁ = e₁ and … in body`: only functions. -/
  | letRec (bs : List (Ident × Ident × Expr)) (body : Expr)
  /-- `match e with cases | exception exnCases`. -/
  | match_ (id : NodeId) (e : Expr) (cases : List (Pat × Option Expr × Expr))
      (exnCases : List (Pat × Option Expr × Expr))
  | try_ (e : Expr) (cases : List (Pat × Option Expr × Expr))
  | tuple (id : NodeId) (es : List Expr)
  | ctor (id : NodeId) (tag : Nat) (es : List Expr)
  | exnCtor (id : NodeId) (p : Path) (es : List Expr)
  /-- `{f₁ = e₁; …}`; `isMut` records live in the store. -/
  | record (id : NodeId) (isMut : Bool) (es : List Expr)
  /-- `{base with f = e; …}` for a record with `n` fields. -/
  | recordWith (id : NodeId) (isMut : Bool) (n : Nat) (fs : List (Nat × Expr)) (base : Expr)
  | field (e : Expr) (pos : Nat)
  /-- `e₁.f <- e₂`; `e₂` is evaluated first. -/
  | setField (e₁ : Expr) (pos : Nat) (e₂ : Expr)
  | ite (c t f : Expr)
  | seq (e₁ e₂ : Expr)
  | assert (e : Expr) (file : String) (line col : Nat)
  | letExn (x : Ident) (body : Expr)
  | letModule (x : Ident) (m : ModExpr) (body : Expr)
  /-- `(module M)`: a first-class module is the module value itself. -/
  | pack (m : ModExpr)

/-- Module expressions. -/
inductive ModExpr where
  | path (p : Path)
  /-- A structure; `exports` lists the bound identifiers of its signature
  in runtime-field order. -/
  | struct (items : List Item) (exports : List Ident)
  /-- `functor (X) -> body`; generative functors `functor () -> …` use a
  dummy parameter and are applied with `applyUnit`. -/
  | functor (x : Ident) (body : ModExpr)
  | apply (f a : ModExpr)
  | applyUnit (f : ModExpr)
  | coerce (m : ModExpr) (c : Coercion)
  | unpack (e : Expr)

/-- Structure items. -/
inductive Item where
  | value (id : NodeId) (bs : List (Pat × Expr))
  | valueRec (bs : List (Ident × Ident × Expr))
  | exn (x : Ident)
  | exnRebind (x : Ident) (p : Path)
  | module (x : Ident) (m : ModExpr)
  /-- `include m`, binding `xs` to its fields in order. -/
  | include (m : ModExpr) (xs : List Ident)
  | eval (e : Expr)
  | primitive (x : Ident) (op : PrimOp)
end

instance : Inhabited Expr := ⟨.const (.int 0)⟩

/-- A match case: pattern, optional guard, body. -/
abbrev Case := Pat × Option Expr × Expr

/-- A compilation unit: its module name and structure. -/
structure CUnit where
  name : String
  items : List Item
  exports : List Ident

/-- A program: units in link order. -/
abbrev Program := List CUnit

/-! ## Encodings of derived forms -/

/-- `()`, `false`, `true`, `[]`, `None` are constant constructors 0/0/1/0/0. -/
def Expr.unit : Expr := .ctor default 0 []
def Expr.bool (b : Bool) : Expr := .ctor default (if b then 1 else 0) []

/-- `` `A `` with OCaml's hash `h`. -/
def Expr.pvariant (h : BitVec 63) : Expr := .const (.int h)
/-- `` `A e ``: the block `(h, e)`. -/
def Expr.pvariantArg (id : NodeId) (h : BitVec 63) (e : Expr) : Expr :=
  .tuple id [.const (.int h), e]

/-- `fun x₁ … xₙ -> body`, curried. -/
def Expr.fun_ : List Ident → Expr → Expr
  | [], body => body
  | x :: xs, body => .fn x (Expr.fun_ xs body)

/-- `if c then t` (no else branch). -/
def Expr.ite1 (c t : Expr) : Expr := .ite c t .unit

end Silmaril.ML.OCaml
