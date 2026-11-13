module

public import Silmaril.ML.OCaml.Prim.Defs

/-!
# Whole-unit overrides: Zarith's `Z`

Zarith's `z.ml` takes fast paths through `Obj` (small integers are
immediates, large ones custom blocks), so it is not imported from source.
Instead the unit `Z` is replaced by `zUnit`, whose functions act on Lean's
`Int` (`Value.z`). `zUnit fields` builds the unit with its fields in the
order `fields` (the runtime order of `z.mli`, which the frontend reads off
the signature); each name is implemented by `zImpl`, and an unknown name
becomes an unsupported primitive that is stuck when applied.

`Z.to_int` raises the unit's own exception `Overflow` outside
`[-2 ^ 62, 2 ^ 62)`; it is written in the embedding, over primitives.
This override is a **trusted definition**.
-/

@[expose] public section
namespace Silmaril.ML.OCaml.Override

def zid (n : String) : NodeId := ⟨"<override Z>", 0, 0, n.length⟩

def overflowId : Ident := ⟨"Overflow", 0⟩

/-- `fun x -> if fits_int x then unsafe_to_int x else raise Overflow` -/
def zToInt : Expr :=
  .fn ⟨"x", 0⟩
    (.ite (.app (zid "fits") (.prim .zFitsInt) [.path (.local ⟨"x", 0⟩)])
      (.app (zid "unsafe") (.prim .zToIntUnsafe) [.path (.local ⟨"x", 0⟩)])
      (.app (zid "raise") (.prim .raise) [.exnCtor (zid "ovf") (.local overflowId) []]))

/-- Implementations of `Z`'s values, by field name. -/
def zImpl : List (String × Expr) :=
  [("of_int", .prim .zOfInt), ("to_int", zToInt), ("fits_int", .prim .zFitsInt),
   ("add", .prim .zAdd), ("+", .prim .zAdd), ("sub", .prim .zSub), ("-", .prim .zSub),
   ("mul", .prim .zMul), ("*", .prim .zMul), ("div", .prim .zDiv), ("/", .prim .zDiv),
   ("rem", .prim .zRem), ("neg", .prim .zNeg), ("~-", .prim .zNeg), ("abs", .prim .zAbs),
   ("compare", .prim .zCompare), ("equal", .prim .zEqual), ("=", .prim .zEqual),
   ("lt", .prim .zLt), ("<", .prim .zLt), ("leq", .prim .zLeq), ("<=", .prim .zLeq),
   ("gt", .prim .zGt), (">", .prim .zGt), ("geq", .prim .zGeq), (">=", .prim .zGeq),
   ("to_string", .prim .zToString), ("sign", .prim .zSign),
   ("~+", .prim .identity),
   ("zero", .const (.int 0)), ("one", .const (.int 1)), ("minus_one", .const (.int (-1)))]

def fieldIdent (i : Nat) (n : String) : Ident := ⟨n, i + 1⟩

/-- The value item for field `n` (position `i`). `zero`/`one` are built by
`of_int`. -/
def zItem (i : Nat) (n : String) : Item :=
  let body := match zImpl.lookup n with
    | some (.const c) => .app (zid n) (.prim .zOfInt) [.const c]
    | some e => e
    | none => .prim (.ext ("Z." ++ n) 1)
  .value (zid n) [(.var (fieldIdent i n), body)]

/-- The `Z` unit with fields in the given runtime order. -/
def zUnit (fields : List String) : CUnit where
  name := "Z"
  items := .exn overflowId :: (fields.mapIdx fun i n => if n = "Overflow" then none else
    some (zItem i n)).filterMap id
  exports := fields.mapIdx fun i n => if n = "Overflow" then overflowId else fieldIdent i n

/-- The run-time fields of Zarith 1.14's `Z`, in order: the `exception`, `val` and
`module` items of `z.mli` (`external`s have no field). Read from `z.mli` of
`ocaml5.4.1-zarith-1.14` (nixpkgs `da6dc0e7…`). -/
def zarithFields : List String :=
  ["Overflow", "zero", "one", "minus_one", "of_int32_unsigned", "of_int64_unsigned",
   "of_nativeint_unsigned", "of_string", "of_substring", "of_string_base", "succ", "pred",
   "abs", "neg", "add", "sub", "mul", "div", "rem", "ediv_rem", "ediv", "erem", "divexact",
   "divisible", "logand", "logor", "logxor", "lognot", "shift_left", "shift_right",
   "shift_right_trunc", "testbit", "to_int", "to_float", "to_string", "print", "output",
   "sprint", "bprint", "pp_print", "leq", "geq", "lt", "gt", "min", "max", "is_even", "is_odd",
   "hash", "seeded_hash", "gcdext", "lcm", "log2", "log2up", "extract", "signed_extract",
   "random_int", "random_bits", "random_int_gen", "random_bits_gen", "~-", "~+", "+", "-", "*",
   "/", "/|", "mod", "land", "lor", "lxor", "~!", "lsl", "asr", "Compare", "version",
   "round_to_float"]

/-- Zarith's `Z` with its real field layout. -/
def zarithUnit : CUnit := zUnit zarithFields

/-- A placeholder for an external unit with `n` fields: every field is an
unsupported primitive, so any use is stuck (never a wrong result). Field `i` is bound to
the identifier `⟨name, i + 1⟩`; no string is computed, since `String` operations do not
reduce in the kernel from a `module`. It lets a
program that refers to the unit link, as long as only paths that never touch
the unit are run. -/
def stubUnit (name : String) (n : Nat) : CUnit where
  name := name
  items := (List.range n).map fun i => .primitive ⟨name, i + 1⟩ (.ext name 1)
  exports := (List.range n).map fun i => ⟨name, i + 1⟩

/-- An external unit with `n` fields, of which those listed are implemented in the
embedding (by position) and the others are stuck, as in `stubUnit`. -/
def partialUnit (name : String) (n : Nat) (impl : List (Nat × Expr)) : CUnit where
  name := name
  items := (List.range n).map fun i => match impl.lookup i with
    | some e => .value (zid name) [(.var ⟨name, i + 1⟩, e)]
    | none => .primitive ⟨name, i + 1⟩ (.ext name 1)
  exports := (List.range n).map fun i => ⟨name, i + 1⟩

/-- `Stdlib.Printexc` as far as link time needs it: `register_printer` (field 8 of
`printexc.mli`) accepts the printer and does nothing, since exception printing is not
modelled. Every other field is stuck. -/
def printexcUnit : CUnit :=
  partialUnit "Stdlib__Printexc" 40 [(8, .fn ⟨"f", 0⟩ (.ctor (zid "unit") 0 []))]

end Silmaril.ML.OCaml.Override
