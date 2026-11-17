module

public import Silmaril.Cerberus.TV.Profile.Defs
public import Silmaril.Cerberus.TV.Behaviour.Defs
public import Silmaril.Cerberus.Codec.File.Defs

/-!
# Which types a program's reachable Core names, and the per-type profile check

A Core→Core statement (`TV.Refines`) is about the port's semantics. A target profile's per-type
check (`Profile.CoherentAt`) is a **necessary filter**, not a transfer: this module computes, per
program, the types named by the Core **reachable by name** (a superset of what any run executes:
no execution analysis), and requires coherence at each.

**What is scanned** (`mentions b`): the wire encoding (`Codec.encodeFileBindings`, round trip
proved in `Silmaril.Cerberus.Codec`) of

* the program part: its own functions, globals, tag definitions, function information and visible
  objects;
* the **runtime library functions and implementation constants it can reach**
  (`reachableStdlib`, `reachableImpl`): every `stdlib` function whose symbol, and every `impl`
  constant whose name (under `PEimpl`/`Impl`), occurs in the program part or, transitively, in a
  reached function or constant.

`Closed.ofBindings b` runs `b.toFile`, which keeps `stdlib` and `impl`; a runtime function or
constant that nothing reached names cannot be called, so leaving it out loses nothing the
dynamics executes. (Core names runtime functions by symbol and implementation constants by
`PEimpl`/`Impl`; a name built at run time would be missed, and Core has none.)

**How the scan reads types** (over-approximating within what it scans):

* a real floating type names its kind (`RealFloating (Float)` …); a Core floating object type or
  value (`OTy_floating`, `OVfloating`) counts as all three kinds;
* `Wint_t` counts as `wchar_t`; Cerberus's `byte` type counts as `unsigned char`;
* exact-width, least, fast and maximum-width integers, enums, `ptraddr_t`, arrays, structs, unions
  and atomics are **outside the coherence table** (`Mention.outside`): the check never passes for
  a program that names one. Every constructor of the C type vocabulary (`ctypeVocabulary`) is
  classified explicitly; a test fails when the vocabulary gains one this module does not know.

**What the scan cannot see**, beside what `Profile.issues` does not compare: operations rather
than types (integer conversions, shifts and division go through runtime functions such as
`conv_int` and `catch_exceptional_condition` and the `impl` constants, whose behaviour is the
port's; builtin functions run natively in the dynamics, and only the types at their call sites
are scanned); allocator addresses; byte-level type punning (only the pointee types written in the
program appear); and the enum registry (`Closed.ofBindings` runs with no enum registrations, which
is harmless only because enums are `outside`).

`Profile.AppliesTo p b` is decidable.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.TaggedCodec (Tree)

/-- A type a program mentions. -/
inductive Mention where
  | scalar (s : Scalar)
  | outside (tag : String)
  deriving DecidableEq, Repr

/-- The constructor tags of the C type vocabulary that `mentionOf` classifies (as a scalar,
`outside`, a wrapper whose arguments are scanned, or a base-type tag read through its parent).
`tests/cerberus/TVApplicability.lean` checks that this is every constructor tag `Names.types`
lists for `Ctype.ctype_`, `Ctype.basicType`, `Ctype.floatingType`, `Ctype.realFloatingType`,
`IntegerType.integerType` and `IntegerType.integerBaseType`, so a constructor added to the
vocabulary fails that test until it is classified (fail closed at review time, not silently). -/
def ctypeVocabulary : List String :=
  ["Void", "Basic", "Array", "Function", "FunctionNoParams", "Pointer", "Atomic", "Struct", "Union",
   "Byte", "Integer", "Floating", "RealFloating", "Float", "Double", "LongDouble",
   "Char", "Bool", "Signed", "Unsigned", "Enum", "Wchar_t", "Wint_t", "Size_t", "Ptrdiff_t",
   "Ptraddr_t", "Ichar", "Short", "Int_", "Long", "LongLong", "IntN_t", "Int_leastN_t",
   "Int_fastN_t", "Intmax_t", "Intptr_t"]

/-- The mentions of one node, from its tag and its first child's tag. -/
def mentionOf (tag : String) (first : Option String) : List Mention :=
  let floats := [Mention.scalar .float, .scalar .double, .scalar .longDouble]
  match tag, first with
  | "RealFloating", some "Float" => [.scalar .float]
  | "RealFloating", some "Double" => [.scalar .double]
  | "RealFloating", some "LongDouble" => [.scalar .longDouble]
  | "RealFloating", _ => floats
  | "OTy_floating", _ => floats
  | "OVfloating", _ => floats
  | "Signed", some "Ichar" => [.scalar .schar]
  | "Signed", some "Short" => [.scalar .short]
  | "Signed", some "Int_" => [.scalar .int]
  | "Signed", some "Long" => [.scalar .long]
  | "Signed", some "LongLong" => [.scalar .longLong]
  | "Signed", some "Intptr_t" => [.scalar .intptr]
  | "Unsigned", some "Ichar" => [.scalar .uchar]
  | "Unsigned", some "Short" => [.scalar .ushort]
  | "Unsigned", some "Int_" => [.scalar .uint]
  | "Unsigned", some "Long" => [.scalar .ulong]
  | "Unsigned", some "LongLong" => [.scalar .ulongLong]
  | "Unsigned", some "Intptr_t" => [.scalar .uintptr]
  | "Signed", some t => [.outside t]
  | "Unsigned", some t => [.outside t]
  | "Char", _ => [.scalar .char]
  | "Bool", _ => [.scalar .bool]
  | "Wchar_t", _ => [.scalar .wchar]
  | "Wint_t", _ => [.scalar .wchar]
  | "Size_t", _ => [.scalar .size]
  | "Ptrdiff_t", _ => [.scalar .ptrdiff]
  | "Pointer", _ => [.scalar .pointer]
  | "OTy_pointer", _ => [.scalar .pointer]
  | "Enum", _ => [.outside "Enum"]
  | "Ptraddr_t", _ => [.outside "Ptraddr_t"]
  | "Array", _ => [.outside "Array"]
  | "Struct", _ => [.outside "Struct"]
  | "Union", _ => [.outside "Union"]
  | "Atomic", _ => [.outside "Atomic"]
  | "OTy_array", _ => [.outside "Array"]
  | "OTy_struct", _ => [.outside "Struct"]
  | "OTy_union", _ => [.outside "Union"]
  -- Cerberus's `byte` type (the runtime's byte-wise copies): one byte, as `unsigned char`.
  | "Byte", _ => [.scalar .uchar]
  -- Constructors that only wrap other types, which are scanned where they occur; base-type tags
  -- (`Int_`, `Float`, …) are read through their `Signed`/`Unsigned`/`RealFloating` parent.
  | _, _ => []

/-- The tag of a tree's root, if it is a node. -/
def rootTag : Tree → Option String
  | .atom _ => none
  | .tag t _ _ => some t

/-- Every mention in a tree. -/
def mentionsTree : Tree → List Mention
  | .atom _ => []
  | .tag t n cs =>
      let first := if h : 0 < n then rootTag (cs ⟨0, h⟩) else none
      mentionOf t first ++ (List.ofFn fun i => mentionsTree (cs i)).flatten

/-- The program part of a file: the runtime library maps emptied. -/
def programPart (b : Codec.FileBindings) : Codec.FileBindings :=
  { b with stdlib := [], impl := [] }

/-- The text of an atom child, or of a `$str` node's atom. -/
def atomText : Tree → Option String
  | .atom a => some a
  | .tag "$str" 1 cs => match cs ⟨0, by decide⟩ with
    | .atom a => some a
    | _ => none
  | _ => none

/-- The symbols a tree names: each `Symbol` node's digest and number (Lem's symbol equality). -/
def symbolsTree : Tree → List (String × String)
  | .atom _ => []
  | .tag t n cs =>
      let here := if t == "Symbol" ∧ 2 ≤ n then
          match (if h : 0 < n then atomText (cs ⟨0, h⟩) else none),
                (if h : 1 < n then atomText (cs ⟨1, h⟩) else none) with
          | some d, some k => [(d, k)]
          | _, _ => []
        else []
      here ++ (List.ofFn fun i => symbolsTree (cs i)).flatten

/-- The key of a symbol, as `symbolsTree` reads it. -/
def symKey (s : Sym) : List (String × String) := symbolsTree (Codec.sym.enc s)

/-- The implementation constants a tree names: the root tag under each `PEimpl` or `Impl` node. -/
def implsTree : Tree → List String
  | .atom _ => []
  | .tag t n cs =>
      let here := if (t == "PEimpl" || t == "Impl") then
          match (if h : 0 < n then rootTag (cs ⟨0, h⟩) else none) with
          | some c => [c]
          | none => []
        else []
      here ++ (List.ofFn fun i => implsTree (cs i)).flatten

/-- The key of an implementation constant, as `implsTree` reads it. -/
def implKey (c : ImplementationConstant) : Option String := rootTag (Codec.implementationConstant.enc c)

/-- One runtime entry as the closure reads it: its own keys, and the symbols and implementation
constants its body names (each body encoded once). -/
structure Entry where
  own : List (String × String) ⊕ Option String
  symbols : List (String × String)
  impls : List String

/-- The closure's state: the names reached so far and which entries are reached. -/
structure Reach where
  keys : List (String × String)
  impls : List String
  reached : List Bool

/-- Whether an entry is named by the names reached so far. -/
def Entry.named (e : Entry) (r : Reach) : Bool :=
  match e.own with
  | .inl ks => ks.any (r.keys.contains ·)
  | .inr (some c) => r.impls.contains c
  | .inr none => false

/-- One round: every entry not yet reached that a reached name names is reached, and adds the
names its body names. Returns whether anything changed. -/
def reachStep (es : List Entry) (r : Reach) : Reach × Bool :=
  let news := (es.zip r.reached).map fun (e, done) => !done && e.named r
  let added := (es.zip news).filter (·.2) |>.map (·.1)
  ({ keys := r.keys ++ added.flatMap (·.symbols), impls := r.impls ++ added.flatMap (·.impls),
     reached := (r.reached.zip news).map fun (x, y) => x || y }, news.any id)

/-- Iterate `reachStep` until nothing changes (at most once per entry, plus one). -/
def reachLoop (es : List Entry) : Nat → Reach → Reach
  | 0, r => r
  | n + 1, r => match reachStep es r with
    | (r', true) => reachLoop es n r'
    | (r', false) => r'

/-- The runtime entries of a file: the `stdlib` functions, then the `impl` constants. -/
def entries (b : Codec.FileBindings) : List Entry :=
  b.stdlib.map (fun e => let t := Codec.funDecl.enc e.2
      ⟨.inl (symKey e.1), symbolsTree t, implsTree t⟩) ++
  b.impl.map (fun e => let t := Codec.implDecl.enc e.2
      ⟨.inr (implKey e.1), symbolsTree t, implsTree t⟩)

/-- Which runtime entries (`stdlib` then `impl`, in order) the program part reaches. -/
def reachedFlags (b : Codec.FileBindings) : List Bool :=
  let es := entries b
  let seed := Codec.encodeFileBindings (programPart b)
  (reachLoop es (es.length + 1) ⟨symbolsTree seed, implsTree seed, es.map fun _ => false⟩).reached

/-- **The runtime functions the program can reach** (by symbol, transitively). -/
def reachableStdlib (b : Codec.FileBindings) : List (Sym × Core.FunDecl Codec.wireModel Unit Unit) :=
  ((b.stdlib.zip (reachedFlags b)).filter (·.2)).map (·.1)

/-- **The implementation constants the program can reach** (transitively). -/
def reachableImpl (b : Codec.FileBindings) :
    List (ImplementationConstant × Core.ImplDecl Codec.wireModel Unit) :=
  ((b.impl.zip ((reachedFlags b).drop b.stdlib.length)).filter (·.2)).map (·.1)

/-- **The types a program's reachable Core names** (module docstring), without repetitions: the
program part, the reachable runtime functions and the reachable implementation constants. -/
def mentions (b : Codec.FileBindings) : List Mention :=
  let flags := reachedFlags b
  let stdlib := ((b.stdlib.zip flags).filter (·.2)).map (·.1)
  let impl := ((b.impl.zip (flags.drop b.stdlib.length)).filter (·.2)).map (·.1)
  (mentionsTree (Codec.encodeFileBindings { b with stdlib, impl })).dedup

/-- Whether the profile is coherent at a mention (never at one outside the table). -/
def Profile.coherentAt (p : Profile) : Mention → Bool
  | .scalar s => (p.issues s).isEmpty
  | .outside _ => false

/-- **The per-type check passes**: every scalar type the reachable Core names (`mentions`) is
coherent, and it names nothing outside the coherence table. A necessary filter, not a transfer. -/
def Profile.AppliesTo (p : Profile) (b : Codec.FileBindings) : Prop :=
  (mentions b).all p.coherentAt = true

instance (p : Profile) (b : Codec.FileBindings) : Decidable (p.AppliesTo b) :=
  inferInstanceAs (Decidable (_ = true))

/-- The mentions that block applicability, with the reason. -/
def Profile.blockers (p : Profile) (b : Codec.FileBindings) : List (Mention × List Issue) :=
  (mentions b).filterMap fun m => match m with
    | .scalar s => match p.issues s with
      | [] => none
      | is => some (m, is)
    | .outside t => some (m, [.unknown s!"{t}: outside the coherence table"])

/-- A closed program from a file's bindings. -/
def Closed.ofBindings (b : Codec.FileBindings) (args : List String := []) : Closed :=
  ⟨b.toFile, ∅, args⟩

/-- **Core refinement with the profile's per-type check on both programs**: a Core→Core
refinement (`Refines`) of two closed programs given by their bindings, with the profile's
`Spec.Impl` choices, and `Profile.AppliesTo` on both. It is a statement about the port's Core
semantics filtered by a necessary condition, not a statement about the target. -/
structure RefinesOn (p : Profile) (src tgt : Codec.FileBindings) : Prop where
  refines : Refines p.impl (Closed.ofBindings src) (Closed.ofBindings tgt)
  source : p.AppliesTo src
  target : p.AppliesTo tgt

end Silmaril.Cerberus.TV
