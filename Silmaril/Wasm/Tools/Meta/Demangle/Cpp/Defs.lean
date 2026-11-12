module

/-!
# C++ (Itanium ABI) demangling: a documented subset of cpp_demangle 0.5.1

`cppDemangle s = some t` when this subset recognises `s` and prints `t` as cpp_demangle 0.5.1
(`Symbol::new(s)` then `demangle()`, the C++ demangler of `wasm-tools 1.262.0`) does;
`none` when the subset does not recognise `s` (then `wasm-tools demangle` keeps the name, which
differs from upstream exactly when cpp_demangle accepts a symbol outside the subset).

**Accepted** (`<mangled-name>`):
* `_Z`/`__Z` `<encoding>` with clone suffixes (`.cold`, `.part.0`, `.123` → ` [clone …]`);
* any string that is wholly one `<type>` (cpp_demangle demangles top-level types: `i` → `int`,
  `PKc` → `char const*`, `3foo` → `foo`, `Sa` → `std::allocator`), and `St` alone (`std`).

`<encoding>`: a function (`name(params)`, with the return type first for template functions,
member function qualifiers ` const`, ` volatile`, ` &`, ` &&`) or a data name; the special names
`TV` `{vtable(…)}`, `TT` `{vtt(…)}`, `TI` `typeinfo for …`, `TS` `typeinfo name for …`,
`TF` `typeinfo fn for …`, `TH`/`TW` TLS init/wrapper functions, `GV` `guard variable for …`,
`TC` `construction vtable for A-in-B`, thunks `Th`/`Tv` (`{virtual override thunk({offset(n)}, …)}`,
`{virtual offset(a, b)}`) and covariant thunks `Tc`.
`<name>`: nested names (`N … E` with qualifiers), `St`, unscoped and unscoped-template names,
local names (`Z … E`, string literals, discriminators), internal-linkage `L` names, the
anonymous namespace, constructors and destructors, the operator names (including conversion
operators `cv`, and the template conversion operator `cv T_ I…E` resolved once its arguments
are read), lambdas `Ul … E [n] _` (`{lambda(…)#k}`, template parameters printed `auto:N` in the
signature and resolved when substituted later) and unnamed types `Ut [n] _`.
`<type>`: the builtin types, `r`/`V`/`K` qualifiers, vendor qualifiers `U name` (`int AS1`),
pointers, references, function types, arrays (dimension a number or an expression), pointers to
members, class names, template parameters (`T_`), pack expansions of template parameter packs
(`Dp`), vector types `Dv n _` (`float __vector(4)`), `decltype` (`DT`/`Dt`), substitutions
(`S_`, `S<seq>_`, `St`, `Sa`, `Sb`, `Ss`, `Si`, `So`, `Sd` with cpp_demangle's spellings).
`<template-args>`: types, packs (`J … E`), literals (`L … E`: integers, booleans, other builtin
types as `(type)value`, enumerators `(Enum)value`, external names `L_Z … E`), and expressions
`X … E`.
`<expression>`: everything `Expression::parse` reads, in its order: prefix `pp_`/`mm_`, calls
`cl`, conversions `cv` (one or `_ … E` many), `tl`/`il` braced lists, the four named casts,
`typeid`/`sizeof`/`alignof` of types and expressions, `noexcept`, member access `dt`/`pt`,
`ds`, `sZ`/`sP` pack sizes, `sp`, the fold expressions `fl`/`fr`/`fL`/`fR`, `throw` and
rethrow, `new`/`new[]`/`delete`/`delete[]` with and without `gs`, template and function
parameters (`fp`, `fL`, `this`), unresolved names (`gs`, `sr`, `srN`, qualifier levels,
`on` operators, `dn` destructors), literals, and the unary, binary and ternary operators
(parenthesised as cpp_demangle does, `((a)>(b))` for `>`, postfix `++`/`--`).
Literals print the text up to `E` as `ExprPrimary` does (`(float)[3f800000]`, `nullptr`,
`(bool)2`, a leading `n` as `-`). Special names also include `GR` (reference temporaries) and
`GT` (transaction clones).

**Printing** is a transcription of cpp_demangle's (`CppPr`): types stay trees until printed,
with its inner stack (`push_inner`/`pop_inner_if`, reference collapsing, `FunctionArgSlice`'s
parentheses, arrays and pointers to members as inner declarators), the pop at the end of every
`<nested-name>`, including the one inside a type substitution used as a prefix (`A::B&::C`) and
inside a lambda signature (which then receives the function's parameters), its last-character
`ensure_space`, and its `is_template_argument_pack` flag (a pack printed once suppresses the
`...` of every later pack expansion). Constructor and destructor names take the leaf of the
enclosing encoding's name; template parameters inside the template arguments being read are
resolved when the symbol is complete (an argument referring to itself or a later argument of
the same list is an error, as upstream).

Substitution candidates follow cpp_demangle: every prefix of a nested name not followed by
`E`, unscoped template names, template parameters and `decltype`s of unresolved types, and
every non-builtin type.

**Tested, not proved**: identical to the pinned `wasm-tools demangle` on the libc++ and
libc++abi symbols of wasi-sdk 27 (4191/4191), on the symbol corpora of
`tools/wasm-tools/tests/symbols/`, and on 20000 mutants of them (`symbols-mutate.py`, seed 1),
including which strings are rejected. Upstream behaviours not modelled: `_GLOBAL_` names, block
invocations, Java resources (`Gr`), exception specifications on function types, explicit object
parameters, `li` literal operators, vendor operators `v n`, `Complex`/`Imaginary` inside the
inner stack's parenthesis rules, and parse-order effects of the pack flag where cpp_demangle
prints a return type before the name (this printer prints in reading order).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Demangle

/-- A C++ type, kept as a tree until it is printed (cpp_demangle's `Type`). Leaves are text;
the character `\x01` inside a leaf marks a point where cpp_demangle's printer pops its inner
stack (the end of a `<nested-name>`, see `CTy.base`). -/
inductive CTy where
  /-- Text: builtin types, class names, template parameters resolved, `decltype`. Each `\x01`
  is a pop point: a `<nested-name>` (`NestedName::demangle`) prints the top of the inner
  stack where it ends. -/
  | base (s : String)
  /-- `Type::Qualified` (the words ` const`, ` volatile`, ` restrict`). -/
  | cv (q : String) (t : CTy)
  | ptr (t : CTy)
  | lref (t : CTy)
  | rref (t : CTy)
  /-- A function type: return type, parameters, cv-qualifiers (words), ref-qualifier (`&`,
  `&&` or empty). -/
  | fn (ret : CTy) (ps : List CTy) (cvq : String) (ref : String)
  | arr (dim : String) (t : CTy)
  | memptr (cls : CTy) (t : CTy)
  /-- A template argument pack (`J … E`, or a template parameter bound to one). -/
  | pack (ts : List CTy)
  /-- A vector type `Dv n _ t` (printed `t __vector(n)`). -/
  | vec (n : String) (t : CTy)
  /-- A pack expansion `Dp t`. -/
  | expn (t : CTy)
  /-- A vendor-qualified type `U name [args] t` (printed `t name<args>`). -/
  | vendor (t : CTy) (suffix : String)
  /-- A template parameter, resolved (printed as its argument; not the builtin `void` of a
  parameter list). -/
  | tparam (t : CTy)
  /-- A template parameter referring to template arguments not read yet (a forward reference,
  resolved when the symbol is complete; printed `\x03 i \x04` until then). -/
  | fwd (i : Nat)
  deriving Inhabited, Repr

/-- The pop-point marker. -/
def popMark : Char := '\x01'

/-- The marker of the enclosing encoding's leaf name (a constructor or destructor name outside
a nested name). -/
def leafMark : Char := '\x02'

/-- Replace the leaf markers by `leaf` (an empty leaf leaves them, and the symbol is then not
demangled: `scope.leaf_name()` fails). -/
def fillLeaf (leaf s : String) : String :=
  if s.contains leafMark && !leaf.isEmpty then
    String.join ((s.splitOn (String.singleton leafMark)).intersperse leaf)
  else s

/-- Text without pop-point markers. -/
def stripMarks (s : String) : String := String.ofList (s.toList.filter (· != popMark))

/-! ## The printer

A transcription of cpp_demangle 0.5.1's printing of types: `Type::demangle` and
`DemangleAsInner::demangle_as_inner`, `FunctionArgSlice::demangle`, `ArrayType`,
`PointerToMemberType` and `NestedName`'s pop of the inner stack, with the context's last written
character (`ensure_space`) and its `is_template_argument_pack` flag (set by printing a pack,
never reset, it suppresses the `...` of later pack expansions). -/

namespace CppPr

/-- An entry of the inner stack, with its identity (`pop_inner_if` compares pointers). -/
inductive Inn where
  | cv (id : Nat) (q : String) (overArr : Bool)
  | ptr (id : Nat)
  | lref (id : Nat)
  | rref (id : Nat)
  | fnT (id : Nat) (cvq ref : String)
  | bare (id : Nat) (ps : List CTy)
  | arr (id : Nat) (dim : String)
  | vec (id : Nat) (n : String)
  | memptr (id : Nat) (cls : CTy)
  deriving Inhabited

def Inn.id : Inn → Nat
  | .cv i .. | .ptr i | .lref i | .rref i | .fnT i .. | .bare i _ | .arr i _ | .vec i _
  | .memptr i _ => i

/-- The printer's state: output, inner stack, fresh identities, the pack flag, whether a pop of
an empty stack marks a pop point (`\x01`) for the enclosing name, and the last character
written before this output. -/
structure PSt where
  out : String := ""
  stack : List Inn := []
  next : Nat := 0
  pack : Bool := false
  mark : Bool := false
  prev : Option Char := none

abbrev PM := StateM PSt

def wr (x : String) : PM Unit := modify fun st => { st with out := st.out ++ x }

def lastC : PM (Option Char) := do
  let st ← get
  pure (if st.out.isEmpty then st.prev else some st.out.back)

def ensureSpace : PM Unit := do if (← lastC) != some ' ' then wr " "

/-- `CvQualifiers::demangle`: each word after `ensure_space`. -/
def cvWords (q : String) : PM Unit := do
  for w in q.splitOn " " do
    if !w.isEmpty then ensureSpace; wr w

def fresh : PM Nat := modifyGet fun st => (st.next, { st with next := st.next + 1 })
def push (i : Inn) : PM Unit := modify fun st => { st with stack := i :: st.stack }
def pop : PM (Option Inn) := modifyGet fun st =>
  match st.stack with
  | [] => (none, st)
  | i :: r => (some i, { st with stack := r })
def top : PM (Option Inn) := do pure (← get).stack.head?

/-- `pop_inner_if`. -/
def popIf (id : Nat) : PM Bool := do
  match ← top with
  | some i => if i.id == id then let _ ← pop; pure true else pure false
  | none => pure false

/-- Pop the r-value references on top of the stack (reference collapsing). -/
def dropRrefs : Nat → PM Unit
  | 0 => pure ()
  | k + 1 => do
    match ← top with
    | some (.rref _) => let _ ← pop; dropRrefs k
    | _ => pure ()

/-- `FunctionArgSlice`'s look at the inner stack: (needs a space, needs parentheses). -/
def parenNeeds (st : List Inn) : Bool × Bool :=
  let cls (i : Inn) : Bool × Bool := match i with
    | .memptr .. | .cv .. => (true, true)
    | .ptr _ | .lref _ | .rref _ => (false, true)
    | _ => (false, false)
  let rec go : List Inn → Bool × Bool
    | [] => (false, false)
    | i :: r =>
      let (s, p) := cls i
      if p then (s, p) else
      let (s', p') := go r
      (s || s', p')
  go st

mutual
/-- `Type::demangle`. -/
def pr : Nat → CTy → PM Unit
  | 0, _ => pure ()
  | f + 1, .base s => wrParts f (s.splitOn "\x01")
  | f + 1, .cv q t => do
    let i ← fresh
    let overArr := match t with | .arr .. => true | _ => false
    push (.cv i q overArr); pr f t
    if ← popIf i then prInn f (.cv i q overArr)
  | f + 1, .ptr t => do let i ← fresh; push (.ptr i); pr f t; if ← popIf i then prInn f (.ptr i)
  | f + 1, .lref t => do let i ← fresh; push (.lref i); pr f t; if ← popIf i then prInn f (.lref i)
  | f + 1, .rref t => do let i ← fresh; push (.rref i); pr f t; if ← popIf i then prInn f (.rref i)
  | f + 1, .fn r ps cvq ref => do
    let i1 ← fresh
    push (.fnT i1 cvq ref)
    let i2 ← fresh
    push (.bare i2 ps)
    pr f r
    if ← popIf i2 then ensureSpace; prArgs f ps
    if ← popIf i1 then prInn f (.fnT i1 cvq ref)
  | f + 1, .arr d t => do
    let i ← fresh; push (.arr i d); pr f t; if ← popIf i then prInn f (.arr i d)
  | f + 1, .memptr c t => do
    let i ← fresh; push (.memptr i c); pr f t; if ← popIf i then prInn f (.memptr i c)
  | f + 1, .vec n t => do
    let i ← fresh; push (.vec i n); pr f t; if ← popIf i then prInn f (.vec i n)
  | f + 1, .pack ts => do
    modify fun st => { st with pack := true }
    prList f ts
  | f + 1, .expn t => do
    pr f t
    if !(← get).pack then wr "..."
  | f + 1, .vendor t suf => do pr f t; wr " "; wr suf
  | f + 1, .tparam t => pr f t
  | _ + 1, .fwd i => wr ("\x03" ++ toString i ++ "\x04")
/-- Types separated by `, `. -/
def prList : Nat → List CTy → PM Unit
  | 0, _ => pure ()
  | _, [] => pure ()
  | f + 1, [t] => pr f t
  | f + 1, t :: ts => do pr f t; wr ", "; prList f ts
/-- Text with pop points. -/
def wrParts : Nat → List String → PM Unit
  | 0, _ => pure ()
  | _, [] => pure ()
  | _, [p] => wr p
  | f + 1, p :: ps => do wr p; popOne f; wrParts f ps
/-- `NestedName`'s `if let Some(inner) = ctx.pop_inner() { inner.demangle_as_inner() }`. -/
def popOne : Nat → PM Unit
  | 0 => pure ()
  | f + 1 => do
    match ← pop with
    | some i => prInn f i
    | none => if (← get).mark then wr "\x01"
/-- `demangle_as_inner`. -/
def prInn : Nat → Inn → PM Unit
  | 0, _ => pure ()
  | _ + 1, .cv _ q _ => cvWords q
  | _ + 1, .ptr _ => wr "*"
  | _ + 1, .lref _ => do
    dropRrefs (← get).stack.length
    match ← top with
    | some (.lref _) => pure ()
    | _ => wr "&"
  | _ + 1, .rref _ => do
    dropRrefs (← get).stack.length
    match ← top with
    | some (.lref _) => pure ()
    | _ => wr "&&"
  | _ + 1, .fnT _ cvq ref => do
    cvWords cvq
    if !ref.isEmpty then ensureSpace; wr ref
  | f + 1, .bare _ ps => prArgs f ps
  | f + 1, .arr _ d => do
    let ns ← arrInners f (← get).stack.length true
    if ns then ensureSpace
    wr ("[" ++ d ++ "]")
  | _ + 1, .vec _ n => wr (" __vector(" ++ n ++ ")")
  | f + 1, .memptr _ c => do
    if (← lastC) != some '(' then ensureSpace
    pr f c
    wr "::*"
/-- The loop of `ArrayType::demangle_as_inner` over the inner stack; whether a space goes
before the dimension. -/
def arrInners : Nat → Nat → Bool → PM Bool
  | 0, _, ns => pure ns
  | _, 0, ns => pure ns
  | f + 1, k + 1, ns => do
    match ← pop with
    | none => pure ns
    | some i =>
      match i with
      | .arr .. => do prInn f i; arrInners f k false
      | .cv _ _ true => do prInn f i; arrInners f k ns
      | .cv .. => do
        ensureSpace; prInn f i; ensureSpace; wr "("
        inners f (← get).stack.length
        wr ")"
        pure ns
      | _ => do
        ensureSpace; wr "("; prInn f i
        inners f (← get).stack.length
        wr ")"
        pure ns
/-- `demangle_inners`: pop and print everything. -/
def inners : Nat → Nat → PM Unit
  | 0, _ => pure ()
  | _, 0 => pure ()
  | f + 1, k + 1 => do
    match ← pop with
    | some i => prInn f i; inners f k
    | none => pure ()
/-- `demangle_inner_prefixes`: print everything but cv-qualified function types, which stay
(in order). -/
def innerPrefixes : Nat → Nat → List Inn → PM Unit
  | 0, _, saved => modify fun st => { st with stack := saved.reverse ++ st.stack }
  | _, 0, saved => modify fun st => { st with stack := saved.reverse ++ st.stack }
  | f + 1, k + 1, saved => do
    match ← pop with
    | some i@(.fnT _ cvq _) =>
      if !cvq.isEmpty then innerPrefixes f k (i :: saved)
      else do prInn f i; innerPrefixes f k saved
    | some i => do prInn f i; innerPrefixes f k saved
    | none => modify fun st => { st with stack := saved.reverse ++ st.stack }
/-- `FunctionArgSlice::demangle`. -/
def prArgs : Nat → List CTy → PM Unit
  | 0, _ => pure ()
  | f + 1, ps => do
    let (sp, pa) := parenNeeds (← get).stack
    if pa then
      let lc ← lastC
      if sp || !(lc == some '(' || lc == some '*') then ensureSpace
      wr "("
    innerPrefixes f (← get).stack.length []
    if pa then wr ")"
    wr "("
    match ps with
    | [.base "void"] => wr ")"
    | _ => do
      prList f ps
      wr ")"
      inners f (← get).stack.length
end

end CppPr

open CppPr

/-- The printer's fuel. -/
def prFuel : Nat := 100000

/-- Print a type on an empty inner stack: the text and the pack flag after it. -/
def CTy.render (t : CTy) (pack : Bool := false) (prev : Option Char := none) : String × Bool :=
  let (_, st) := (pr prFuel t).run { pack, prev }
  (st.out, st.pack)

/-- A type printed alone (no pack printed before it). -/
def CTy.show (t : CTy) : String := (t.render).1

/-- The text of a type used as a prefix or a name: a leaf as it is (its pop points kept),
anything else printed. -/
def CTy.raw : CTy → String
  | .base s => s
  | .tparam t => t.raw
  | t => t.show

/-- `TemplateArgs::demangle` after the text `before`: `<`, the arguments on a fresh inner stack
(`inner_barrier!`), `>`, with a space after a `<` and before the `>` after a `>`. -/
def tArgsText (before : String) (args : List CTy) (pack : Bool) : String × Bool :=
  let pre := if before.endsWith "<" then " <" else "<"
  let (_, st) := (prList prFuel args).run { pack, prev := some '<' }
  let body := st.out
  (pre ++ body ++ (if body.endsWith ">" then " >" else ">"), st.pack)

/-- A lambda signature: its types separated by `, `, a pop of the empty stack marking the point
where the enclosing function's parameters get printed (`\x01`). -/
def lambdaSigText (ps : List CTy) (pack : Bool) : String × Bool :=
  let (_, st) := (prList prFuel ps).run { pack, mark := true }
  (st.out, st.pack)

/-- The parameter list of a function encoding, printed after the name (`(…)`, `()` for a lone
`void`). -/
def paramsText (ps : List CTy) (pack : Bool) (prev : Option Char) : String × Bool :=
  let (_, st) := (prArgs prFuel ps).run { pack, prev }
  (st.out, st.pack)

/-- A substitution table entry: the type, and the last unqualified name (for constructors). -/
structure SubE where
  ty : CTy
  last : String
  deriving Inhabited

/-- The parser state: input, position, substitutions, the current template arguments. -/
structure CSt where
  s : Array Char
  pos : Nat := 0
  subs : Array SubE := #[]
  targs : List CTy := []
  /-- Inside a lambda signature: template parameters print as `auto:N`. -/
  inLambda : Bool := false
  /-- cpp_demangle's `is_template_argument_pack`: a pack has been printed. -/
  pack : Bool := false
  /-- Reading the type of a conversion operator (`ctx.in_conversion()`). -/
  inConv : Bool := false
  /-- The nesting of template argument lists being read, and the index of the argument read
  in the outermost one (`ArgScopeStack::in_arg`: a reference from it to itself or a later
  argument is an error). -/
  tdepth : Nat := 0
  tpos : Nat := 0
  deriving Inhabited

abbrev CM := StateT CSt (Except Unit)

def fail {α : Type} : CM α := throw ()
def peek : CM (Option Char) := do let st ← get; pure st.s[st.pos]?
def peek2 : CM (Option Char) := do let st ← get; pure st.s[st.pos + 1]?
def adv (n : Nat := 1) : CM Unit := modify fun st => { st with pos := st.pos + n }
def eat (c : Char) : CM Bool := do
  if (← peek) == some c then adv; pure true else pure false
def expect (c : Char) : CM Unit := do if !(← eat c) then fail
def addSub (t : CTy) (last : String) : CM Unit := modify fun st => { st with subs := st.subs.push ⟨t, last⟩ }
def atEnd : CM Bool := do pure (← peek).isNone

/-- A type printed now, with the pack flag of the output so far. -/
def strT (t : CTy) : CM String := do
  let (x, pk) := t.render (← get).pack
  modify fun st => { st with pack := pk }
  pure (stripMarks x)

/-- Template arguments printed after the text `before`. -/
def tArgs (before : String) (args : List CTy) : CM String := do
  let (x, pk) := tArgsText before args (← get).pack
  modify fun st => { st with pack := pk }
  pure x

/-- A decimal number (`n` prefix for negative when `neg`). -/
def number (neg : Bool) : CM String := do
  let mut sign := ""
  if neg then
    if (← eat 'n') then sign := "-"
  let st ← get
  let ds := (st.s.toList.drop st.pos).takeWhile Char.isDigit
  if ds.isEmpty then fail
  if ds.length > 1 && ds.head? == some '0' then fail
  adv ds.length
  pure (sign ++ String.ofList ds)

/-- An optional non-negative number. -/
def optNumber : CM (Option Nat) := do
  let st ← get
  let ds := (st.s.toList.drop st.pos).takeWhile Char.isDigit
  if ds.isEmpty then return none
  if ds.length > 1 && ds.head? == some '0' then fail
  adv ds.length
  pure (some (String.ofList ds).toNat!)

/-- `<CV-qualifiers>`: `[r] [V] [K]`, in this order (`CvQualifiers::parse`), printed
` const volatile restrict`. -/
def cvQuals : CM String := do
  let r ← eat 'r'
  let v ← eat 'V'
  let k ← eat 'K'
  pure ((if k then " const" else "") ++ (if v then " volatile" else "") ++ (if r then " restrict" else ""))

/-- `<source-name>`. -/
def sourceName : CM String := do
  let n ← number false
  let st ← get
  let len := n.toNat!
  if st.pos + len > st.s.size || len == 0 then fail
  let id := String.ofList ((st.s.toList.drop st.pos).take len)
  adv len
  pure (if id.startsWith "_GLOBAL__N" then "(anonymous namespace)" else id)

/-- The `<seq-id>` of a substitution after `S` or `T`, up to `_`: `none` for `_` alone. -/
def seqId : CM (Option Nat) := do
  if (← eat '_') then return none
  let st ← get
  let ds := (st.s.toList.drop st.pos).takeWhile fun c => c.isDigit || c.isUpper
  if ds.isEmpty then fail
  if ds.length > 1 && ds.head? == some '0' then fail
  adv ds.length
  expect '_'
  pure (some (ds.foldl (fun n c => 36 * n + (if c.isDigit then c.toNat - 48 else c.toNat - 55)) 0))

/-- ABI tags `B <source-name>`, printed `[abi:…]`. -/
def abiTags : CM String := do
  let mut out := ""
  for _ in List.range ((← get).s.size) do
    if (← peek) != some 'B' then break
    adv
    let n ← sourceName
    out := out ++ "[abi:" ++ n ++ "]"
  pure out

/-- The builtin types. -/
def builtin (c : Char) : Option String :=
  match c with
  | 'v' => "void" | 'w' => "wchar_t" | 'b' => "bool" | 'c' => "char" | 'a' => "signed char"
  | 'h' => "unsigned char" | 's' => "short" | 't' => "unsigned short" | 'i' => "int"
  | 'j' => "unsigned int" | 'l' => "long" | 'm' => "unsigned long" | 'x' => "long long"
  | 'y' => "unsigned long long" | 'n' => "__int128" | 'o' => "unsigned __int128" | 'f' => "float"
  | 'd' => "double" | 'e' => "long double" | 'g' => "__float128" | 'z' => "..."
  | _ => none

def builtinD (c : Char) : Option String :=
  match c with
  | 'd' => "decimal64" | 'e' => "decimal128" | 'f' => "decimal32" | 'h' => "half"
  | 'i' => "char32_t" | 's' => "char16_t" | 'u' => "char8_t" | 'a' => "auto"
  | 'c' => "decltype(auto)" | 'n' => "std::nullptr_t"
  | _ => none

/-- The two-letter operator names. -/
def opName (a b : Char) : Option String :=
  match a, b with
  | 'n', 'w' => " new" | 'n', 'a' => " new[]" | 'd', 'l' => " delete" | 'd', 'a' => " delete[]"
  | 'p', 's' => "+" | 'n', 'g' => "-" | 'a', 'd' => "&" | 'd', 'e' => "*" | 'c', 'o' => "~"
  | 'p', 'l' => "+" | 'm', 'i' => "-" | 'm', 'l' => "*" | 'd', 'v' => "/" | 'r', 'm' => "%"
  | 'a', 'n' => "&" | 'o', 'r' => "|" | 'e', 'o' => "^" | 'a', 'S' => "=" | 'p', 'L' => "+="
  | 'm', 'I' => "-=" | 'm', 'L' => "*=" | 'd', 'V' => "/=" | 'r', 'M' => "%=" | 'a', 'N' => "&="
  | 'o', 'R' => "|=" | 'e', 'O' => "^=" | 'l', 's' => "<<" | 'r', 's' => ">>" | 'l', 'S' => "<<="
  | 'r', 'S' => ">>=" | 'e', 'q' => "==" | 'n', 'e' => "!=" | 'l', 't' => "<" | 'g', 't' => ">"
  | 'l', 'e' => "<=" | 'g', 'e' => ">=" | 's', 's' => "<=>" | 'n', 't' => "!" | 'a', 'a' => "&&"
  | 'o', 'o' => "||" | 'p', 'p' => "++" | 'm', 'm' => "--" | 'c', 'm' => "," | 'p', 'm' => "->*"
  | 'p', 't' => "->" | 'c', 'l' => "()" | 'i', 'x' => "[]" | 'q', 'u' => "?"
  | _, _ => none

/-- The standard abbreviations: printed name, and whether it is a full type (not a prefix). -/
def stdAbbrev (c : Char) : Option String :=
  match c with
  | 'a' => "std::allocator" | 'b' => "std::basic_string" | 's' => "std::string"
  | 'i' => "std::basic_istream<char, std::char_traits<char> >"
  | 'o' => "std::ostream"
  | 'd' => "std::basic_iostream<char, std::char_traits<char> >"
  | _ => none

/-- What a parsed name is: its text, its last unqualified name, whether it ends in template
arguments, whether it is a constructor, destructor or conversion operator, and the member
function qualifiers. -/
structure NameR where
  text : String
  last : String
  tmpl : Bool := false
  noRet : Bool := false
  quals : String := ""
  /-- The last component is a substitution alone (it cannot end a nested name). -/
  bareSub : Bool := false
  /-- The template arguments of the last component, if it has some. -/
  targs : Option (List CTy) := none
  /-- A conversion operator to a template parameter (`cv T_`) not yet known: its index. -/
  convParam : Option Nat := none
  deriving Inhabited

/-- The literal text of `L <type> <value> E`. -/
def literal (c : Char) (v : String) : Option String :=
  if c == 'b' then (if v == "0" then some "false" else if v == "1" then some "true" else none)
  else if c == 'i' then some v
  else (builtin c).map fun t => "(" ++ t ++ ")" ++ v

/-- The recursion budget. -/
def cppFuel : Nat := 256

/-- A substitution `S…`: an abbreviation or a table entry. -/
def pSubst : CM SubE := do
  expect 'S'
  let some c ← peek | fail
  if let some a := stdAbbrev c then
    adv
    return ⟨.base a, (a.splitOn "::").getLast!⟩
  let i := ((← seqId).map (· + 1)).getD 0
  let some e := (← get).subs[i]? | fail
  -- a template parameter of a lambda signature: resolved now
  if e.last.startsWith "\x00T" then
    let k := (e.last.drop 2).toString.toNat!
    let some t := (← get).targs[k]? | fail
    return ⟨t, ""⟩
  pure e

/-- A `<call-offset>`: `h n _` or `v n _ n _`. -/
def callOffset : CM String := do
  let some c ← peek | fail
  adv
  if c == 'h' then
    let n ← number true
    expect '_'
    pure ("{offset(" ++ n ++ ")}")
  else if c == 'v' then
    let a ← number true
    expect '_'
    let b ← number true
    expect '_'
    pure ("{virtual offset(" ++ a ++ ", " ++ b ++ ")}")
  else fail

/-- The operators of expressions (`SimpleOperatorName`): their spelling and arity. -/
def exprOp (a b : Char) : Option (String × Nat) :=
  match a, b with
  | 'p', 's' => some ("+", 1) | 'n', 'g' => some ("-", 1) | 'a', 'd' => some ("&", 1)
  | 'd', 'e' => some ("*", 1) | 'c', 'o' => some ("~", 1) | 'n', 't' => some ("!", 1)
  | 'p', 'p' => some ("++", 1) | 'm', 'm' => some ("--", 1)
  | 'q', 'u' => some ("?", 3)
  | 'n', 'w' | 'n', 'a' | 'd', 'l' | 'd', 'a' => none
  | _, _ => (opName a b).bind fun o => if o.startsWith " " then none else some (o, 2)

/-- `<simple-id>`-style lookahead: whether the input at the position starts with a digit. -/
def atDigit : CM Bool := do pure (((← peek).map Char.isDigit).getD false)

/-- Try a parser; on failure, restore the state and return `none` (cpp_demangle's
`try_recurse!`). -/
def attempt {α : Type} (x : CM α) : CM (Option α) :=
  tryCatch (some <$> x) (fun _ => pure none)

/-- The literal text of an `<expr-primary>` of type `t` (printed `ts`): cpp_demangle's
`ExprPrimary::Literal` (the text up to `E`, a leading `n` printed `-`). -/
def literalOf (t : CTy) (ts lit : String) : String :=
  let neg := lit.startsWith "n"
  let body := if neg then (lit.drop 1).toString else lit
  let w := (if neg then "-" else "") ++ body
  match t with
  | .base "bool" => if lit == "0" then "false" else if lit == "1" then "true" else "(bool)" ++ w
  | .base "std::nullptr_t" => "nullptr"
  | .base "double" | .base "float" => "(" ++ ts ++ ")" ++ (if neg then "-[" else "[") ++ body ++ "]"
  | .base "int" => w
  | _ => "(" ++ ts ++ ")" ++ w

/-- A `<template-param>` in an expression (`T_`, `T n _`): the template argument, printed (no
substitution candidate, unlike a type). -/
def pTParam : CM String := do
  expect 'T'
  let i := ((← seqId).map (· + 1)).getD 0
  let st ← get
  match st.targs[i]? with
  | some t => strT t
  | none =>
    if st.tdepth == 1 && st.tpos ≤ i then fail
    pure ("\x03" ++ toString i ++ "\x04")

/-- A `<function-param>`: `fp [cv] [n] _`, `fL n p [cv] [n] _`, `fpT` (`this`). -/
def pFunParam : CM String := do
  expect 'f'
  if (← eat 'L') then let _ ← number false
  expect 'p'
  let _ ← cvQuals
  if (← eat 'T') then return "this"
  let n ← optNumber
  expect '_'
  pure ("{parm#" ++ toString ((n.map (· + 2)).getD 1) ++ "}")

/-- A discriminator `_n` or `__n_` (not printed). -/
def pDiscr : CM Unit := do
  if (← peek) == some '_' then
    adv
    if (← eat '_') then let _ ← number false; expect '_'
    else
      -- `_ <digit>`: a single digit
      let some c ← peek | fail
      if !c.isDigit then fail
      adv

mutual
/-- `<type>`. -/
def pType (f : Nat) : CM CTy :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    if let some b := builtin c then adv; return .base b
    -- a vendor extended builtin type `u <source-name>`
    if c == 'u' then adv; return .base (← sourceName)
    match c with
    | 'r' | 'V' | 'K' =>
      let q ← cvQuals
      if (← peek) == some 'F' then
        let t ← pFunType f q
        return t
      let t ← pType f
      let r := CTy.cv q t
      addSub r ""; pure r
    | 'P' => adv; let t ← pType f; let r := CTy.ptr t; addSub r ""; pure r
    | 'R' => adv; let t ← pType f; let r := CTy.lref t; addSub r ""; pure r
    | 'O' => adv; let t ← pType f; let r := CTy.rref t; addSub r ""; pure r
    | 'F' => pFunType f ""
    | 'A' =>
      adv
      let dim ← if (← peek) == some '_' then pure ""
        else if ((← peek).map Char.isDigit).getD false then number false
        else do let e ← pExpr f; pure e.1
      expect '_'
      let t ← pType f
      let r := CTy.arr dim t
      addSub r ""; pure r
    | 'M' =>
      adv
      let cls ← pType f
      let mem ← pType f
      let r := CTy.memptr cls mem
      addSub r ""; pure r
    | 'T' =>
      if let some kw := (match (← peek2) with
          | some 's' => some "class " | some 'u' => some "union " | some 'e' => some "enum "
          | _ => none) then
        adv 2
        let n ← pName f
        let t := CTy.base (kw ++ n.text)
        addSub t n.last
        return t
      adv
      let i := ((← seqId).map (· + 1)).getD 0
      if (← get).inLambda then
        -- printed `auto:N` here; a later substitution of it is the template argument
        modify fun st => { st with subs := st.subs.push ⟨.base "", "\x00T" ++ toString i⟩ }
        return CTy.base ("auto:" ++ toString (i + 1))
      let st ← get
      let t ← match st.targs[i]? with
        | some t => pure (CTy.tparam t)
        | none => if st.tdepth == 1 && st.tpos ≤ i then fail else pure (CTy.fwd i)
      addSub t ""
      -- in a conversion operator's type, `T_ <args>` not followed by more arguments is the
      -- parameter alone (the arguments are the operator's)
      let convPlain ← if (← get).inConv && (← peek) == some 'I' then do
          let save ← get
          let more ← (do let _ ← pTArgs f; pure ((← peek) == some 'I'))
          set save
          pure !more
        else pure false
      if convPlain then return t
      if (← peek) == some 'I' then
        let args ← pTArgs f
        let r := CTy.base (t.raw ++ (← tArgs t.raw args))
        addSub r ""; pure r
      else pure t
    | 'D' =>
      let some d ← peek2 | fail
      if let some b := builtinD d then adv 2; return .base b
      -- fixed-point types (N1169): `DA`/`DR` with an integer type, `DS` for `_Sat`
      let st ← get
      let fx (i : Nat) : Option String :=
        let kind := st.s[i]?
        let base := match st.s[i + 1]? with
          | some 's' => some "short " | some 't' => some "unsigned short " | some 'i' => some ""
          | some 'j' => some "unsigned " | some 'l' => some "long " | some 'm' => some "unsigned long "
          | _ => none
        match kind, base with
        | some 'A', some b => some (b ++ "_Accum")
        | some 'R', some b => some (b ++ "_Fract")
        | _, _ => none
      if let some x := fx (st.pos + 1) then adv 3; return .base x
      if d == 'S' && st.s[st.pos + 2]? == some 'D' then
        if let some x := fx (st.pos + 3) then adv 5; return .base ("_Sat " ++ x)
      if d.isDigit then
        let n ← pUnscoped f
        let t := CTy.base n.text
        addSub t n.last
        return t
      if d == 'p' then
        adv 2
        let t ← pType f
        let r := CTy.expn t
        addSub r ""
        return r
      if d == 'T' || d == 't' then
        adv 2
        let e ← pExpr f
        expect 'E'
        let r := CTy.base ("decltype (" ++ e.1 ++ ")")
        addSub r ""
        return r
      if d == 'v' then
        adv 2
        let n ← number false
        expect '_'
        let t ← pType f
        let r := CTy.vec n t
        addSub r ""
        return r
      fail
    | 'U' =>
      let some d ← peek2 | fail
      -- `U` starts a vendor qualifier only (`TypeHandle::parse` commits to it)
      if !d.isDigit then fail
      adv
      let n ← sourceName
      let args ← if (← peek) == some 'I' then some <$> pTArgs f else pure none
      let t ← pType f
      let a ← match args with
        | some args => tArgs n args
        | none => pure ""
      let r := CTy.vendor t (n ++ a)
      addSub r ""
      pure r
    | 'S' =>
      let some d ← peek2 | fail
      if d == 't' then
        match ← attempt (pUnscoped f) with
        | some n =>
          let t := CTy.base n.text
          addSub t n.last
          pure t
        | none => adv 2; pure (.base "std")
      else
        let base ← pSubst
        if (← peek) == some 'I' then
          let args ← pTArgs f
          let r := CTy.base (base.ty.raw ++ (← tArgs base.ty.raw args))
          addSub r base.last; pure r
        else pure base.ty
    | 'N' | 'Z' =>
      let n ← pName f
      -- a `<nested-name>` pops the inner stack where it ends
      let t := CTy.base (if c == 'N' then n.text ++ "\x01" ++ n.quals else n.text)
      addSub t n.last; pure t
    | 'C' | 'G' =>
      if c == 'C' && (((← peek2).map Char.isDigit).getD false) then
        let n ← pUnscoped f
        let t := CTy.base n.text
        addSub t n.last; pure t
      else
        adv
        let t ← pType f
        let r := CTy.vendor t (if c == 'C' then "complex" else "imaginary")
        addSub r ""; pure r
    | _ =>
      -- `ClassEnumType`: an unscoped name (a source name, an operator name, an internal-linkage
      -- name, a constructor or destructor)
      let n ← pUnscoped f
      let t := CTy.base n.text
      addSub t n.last; pure t

  termination_by (f, 0)
/-- A function type `F [Y] ret params [R|O] E` (cv-qualifiers `cvq` already read). -/
def pFunType (f : Nat) (cvq : String) : CM CTy :=
  match f with
  | 0 => fail
  | f + 1 => do
    expect 'F'
    let _ ← eat 'Y'
    let r ← pType f
    let ps ← pParams f (← get).s.size
    let mut q := ""
    if (← eat 'R') then q := "&" else if (← eat 'O') then q := "&&"
    expect 'E'
    let t := CTy.fn r ps cvq q
    addSub t ""; pure t
  termination_by (f, 0)
/-- Function parameters up to `E`, the end, or a clone suffix; `v` alone is no parameter. -/
def pParams (f : Nat) (k : Nat) : CM (List CTy) :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    let c ← peek
    if c.isNone || c == some 'E' || c == some '.' then return []
    -- `one_or_more`: the list ends at the first type that does not parse
    let some t ← attempt (pType f) | return []
    let rest ← pParams (f + 1) k
    pure (t :: rest)
  termination_by (f, k)

/-- `<template-args>`: `I … E`. -/
def pTArgs (f : Nat) : CM (List CTy) :=
  match f with
  | 0 => fail
  | f + 1 => do
    expect 'I'
    if (← peek) == some 'E' then fail
    modify fun st => { st with tdepth := st.tdepth + 1 }
    let r ← pTArgList f (← get).s.size ((← get).tdepth == 1) 0
    modify fun st => { st with tdepth := st.tdepth - 1 }
    pure r
  termination_by (f, 0)

/-- Template arguments up to `E`. -/
def pTArgList (f : Nat) (k : Nat) (top : Bool) (idx : Nat) : CM (List CTy) :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    if (← eat 'E') then return []
    if top then modify fun st => { st with tpos := idx }
    let a ← pTArg f
    let rest ← pTArgList (f + 1) k top (idx + 1)
    pure (a :: rest)
  termination_by (f, k)

/-- One template argument. -/
def pTArg (f : Nat) : CM CTy :=
  match f with
  | 0 => fail
  | f + 1 => do
    -- `TemplateArg::parse`: an expression, a literal, a type, then a pack `J … E` (or `I … E`)
    if (← eat 'X') then
      let (e, _) ← pExpr f
      expect 'E'
      return .base e
    if (← peek) == some 'L' then
      if let some l ← attempt (pLiteral f) then return .base l
    if let some t ← attempt (pType f) then return t
    let c ← peek
    if c == some 'J' || c == some 'I' then
      adv
      let args ← pTArgList f (← get).s.size false 0
      return .pack args
    fail

  termination_by (f, 0)
/-- An `<expr-primary>` `L … E`: a literal of a type (the text up to `E`, printed as
cpp_demangle's `ExprPrimary::Literal` does), or an external name `L_Z encoding E`. -/
def pLiteral (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    expect 'L'
    let some c ← peek | fail
    if c == '_' then
      adv
      -- `MangledName`: `_Z` or `__Z`
      let _ ← eat '_'
      expect 'Z'
      let e ← pEncoding f
      expect 'E'
      return e
    let t ← pType f
    let st ← get
    let lit := (st.s.toList.drop st.pos).takeWhile (· != 'E')
    adv lit.length
    expect 'E'
    pure (literalOf t (← strT t) (String.ofList lit))
  termination_by (f, 0)

/-- An `<expression>`, as cpp_demangle 0.5.1 parses and prints it (`Expression::parse`, in its
order): its text and whether it needs no parentheses as a subexpression (function parameters
and external names). -/
def pExpr (f : Nat) : CM (String × Bool) :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    let d := (← peek2).getD ' '
    let sub (x : String × Bool) : String := if x.2 then x.1 else "(" ++ x.1 ++ ")"
    let st0 ← get
    let third := st0.s[st0.pos + 2]?
    if c == 'p' && d == 'p' && third == some '_' then
      adv 3; let e ← pExpr f; return ("++" ++ e.1, false)
    if c == 'm' && d == 'm' && third == some '_' then
      adv 3; let e ← pExpr f; return ("--" ++ e.1, false)
    let tyE (pre : String) : CM (String × Bool) := do
      adv 2
      let t ← pType f
      let e ← pExpr f
      pure (pre ++ "<" ++ (← strT t) ++ ">(" ++ e.1 ++ ")", false)
    let paren (pre : String) (x : String) : String × Bool := (pre ++ " (" ++ x ++ ")", false)
    match c, d with
    | 'c', 'l' =>
      adv 2
      let fn ← pExpr f
      let args ← pExprList f (← get).s.size
      return (sub fn ++ "(" ++ ", ".intercalate args ++ ")", false)
    | 'c', 'v' =>
      adv 2
      let t ← pType f
      if (← eat '_') then
        let es ← pExprList f (← get).s.size
        return ((← strT t) ++ "(" ++ ", ".intercalate es ++ ")", false)
      let e ← pExpr f
      return ("(" ++ (← strT t) ++ ")(" ++ e.1 ++ ")", false)
    | 't', 'l' =>
      adv 2
      let t ← pType f
      let es ← pExprList f (← get).s.size
      return ((← strT t) ++ "{" ++ ", ".intercalate es ++ "}", false)
    | 'i', 'l' =>
      adv 2
      let es ← pExprList f (← get).s.size
      return ("{" ++ ", ".intercalate es ++ "}", false)
    | 'd', 'c' => tyE "dynamic_cast"
    | 's', 'c' => tyE "static_cast"
    | 'c', 'c' => tyE "const_cast"
    | 'r', 'c' => tyE "reinterpret_cast"
    | 't', 'i' => adv 2; return paren "typeid" (← strT (← pType f))
    | 't', 'e' => adv 2; return paren "typeid" (← pExpr f).1
    | 's', 't' => adv 2; return paren "sizeof" (← strT (← pType f))
    | 's', 'z' => adv 2; return paren "sizeof" (← pExpr f).1
    | 'a', 't' => adv 2; return paren "alignof" (← strT (← pType f))
    | 'a', 'z' => adv 2; return paren "alignof" (← pExpr f).1
    | 'n', 'x' => adv 2; return paren "noexcept" (← pExpr f).1
    | 'd', 't' =>
      adv 2
      let e ← pExpr f
      let m ← pMemberName f
      return (sub e ++ "." ++ m, false)
    | 'p', 't' =>
      adv 2
      let e ← pExpr f
      let m ← pMemberName f
      return (e.1 ++ "->" ++ m, false)
    | 'd', 's' =>
      adv 2
      let a ← pExpr f
      let b ← pExpr f
      return (a.1 ++ ".*" ++ b.1, false)
    | 's', 'Z' =>
      adv 2
      if (← peek) == some 'T' then
        let t ← pTParam
        return ("sizeof...(" ++ t ++ ")", false)
      let p ← pFunParam
      return ("sizeof...(" ++ p ++ ")", false)
    | 's', 'P' =>
      adv 2
      let args ← pTArgList f (← get).s.size false 0
      let a ← strT (.pack args)
      return ("sizeof...(" ++ a ++ ")", false)
    | 's', 'p' =>
      adv 2
      let e ← pExpr f
      return (sub e ++ "...", false)
    | 'f', 'l' | 'f', 'r' | 'f', 'R' => pFold f
    | 'f', 'L' =>
      if ((st0.s[st0.pos + 2]?).map Char.isDigit).getD true then pPrimaryExpr f
      else pFold f
    | 't', 'w' => adv 2; let e ← pExpr f; return ("throw " ++ e.1, false)
    | 't', 'r' => adv 2; return ("throw", false)
    | 'g', 's' =>
      adv 2
      match ← attempt (pGlobalable f "::") with
      | some r => return r
      | none => set st0; pPrimaryExpr f
    | _, _ =>
      match ← attempt (pGlobalable f "") with
      | some r => return r
      | none => set st0; pPrimaryExpr f
  termination_by (f, 0)

/-- `nw`, `na`, `dl`, `da` (after an optional `gs`, printed `pre`). -/
def pGlobalable (f : Nat) (pre : String) : CM (String × Bool) :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    let some d ← peek2 | fail
    if c == 'n' && (d == 'w' || d == 'a') then
      adv 2
      let es ← pExprsTo f '_' (← get).s.size
      let t ← pType f
      let kw := if d == 'w' then "new" else "new[]"
      let head := pre ++ kw ++ " (" ++ ", ".intercalate es ++ ") " ++ (← strT t)
      if (← eat 'E') then return (head, false)
      expect 'p'; expect 'i'
      let is ← pExprList f (← get).s.size
      return (head ++ "(" ++ ", ".intercalate is ++ ")", false)
    if c == 'd' && (d == 'l' || d == 'a') then
      adv 2
      let e ← pExpr f
      return (pre ++ (if d == 'l' then "delete " else "delete[] ") ++ e.1, false)
    fail
  termination_by (f, 0)

/-- The productions cpp_demangle tries after the operator codes: a template parameter, a
function parameter, an unresolved name, a literal, then an operator expression. -/
def pPrimaryExpr (f : Nat) : CM (String × Bool) :=
  match f with
  | 0 => fail
  | f + 1 => do
    let st0 ← get
    let some c ← peek | fail
    let sub (x : String × Bool) : String := if x.2 then x.1 else "(" ++ x.1 ++ ")"
    if c == 'T' then
      if let some t ← attempt pTParam then return (t, false)
    if c == 'f' then
      if let some p ← attempt pFunParam then return (p, true)
    if let some n ← attempt (pUnresolved f) then return (n, false)
    set st0
    if c == 'L' then return (← pLiteral f, st0.s[st0.pos + 1]? == some '_')
    let some d ← peek2 | fail
    match exprOp c d with
    | some (o, 1) =>
      adv 2
      let e ← pExpr f
      if o == "++" || o == "--" then pure (sub e ++ o, false) else pure (o ++ sub e, false)
    | some (o, 2) =>
      adv 2
      let l ← pExpr f
      let r ← pExpr f
      if o == ">" then pure ("((" ++ l.1 ++ ")>(" ++ r.1 ++ "))", false)
      else pure (sub l ++ o ++ sub r, false)
    | some (_, _) =>
      adv 2
      let a ← pExpr f
      let b ← pExpr f
      let e ← pExpr f
      pure (sub a ++ "?" ++ sub b ++ " : " ++ sub e, false)
    | none => fail
  termination_by (f, 0)

/-- A fold expression `fl`, `fr`, `fL`, `fR` with a binary operator. -/
def pFold (f : Nat) : CM (String × Bool) :=
  match f with
  | 0 => fail
  | f + 1 => do
    expect 'f'
    let some k ← peek | fail
    adv
    let some a ← peek | fail
    let some b ← peek2 | fail
    let some (o, 2) := exprOp a b | fail
    adv 2
    let sub (x : String × Bool) : String := if x.2 then x.1 else "(" ++ x.1 ++ ")"
    let e ← pExpr f
    match k with
    | 'l' => pure ("(..." ++ o ++ sub e ++ ")", false)
    | 'r' => pure ("(" ++ sub e ++ o ++ "...)", false)
    | 'L' | 'R' =>
      let e2 ← pExpr f
      pure ("(" ++ sub e ++ o ++ "..." ++ o ++ sub e2 ++ ")", false)
    | _ => fail
  termination_by (f, 0)

/-- `<simple-id>`: a source name and optional template arguments. -/
def pSimpleId (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    let n ← sourceName
    if (← peek) == some 'I' then
      let args ← pTArgs f
      return n ++ (← tArgs n args)
    pure n
  termination_by (f, 0)

/-- `<unresolved-type>`: a template parameter with optional arguments or a `decltype` (both
substitution candidates), or a substitution. -/
def pUnresType (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    if c == 'T' then
      let t ← pTParam
      let t ← if (← peek) == some 'I' then do
          let args ← pTArgs f
          pure (t ++ (← tArgs t args))
        else pure t
      addSub (.base t) ""
      return t
    if c == 'D' && ((← peek2) == some 'T' || (← peek2) == some 't') then
      adv 2
      let e ← pExpr f
      expect 'E'
      let t := "decltype (" ++ e.1 ++ ")"
      addSub (.base t) ""
      return t
    if c == 'S' then
      if (← peek2) == some 't' then adv 2; return "std"
      let e ← pSubst
      return ← strT e.ty
    fail
  termination_by (f, 0)

/-- `<base-unresolved-name>`: a simple id, `on` an operator, or `dn` a destructor. -/
def pBaseUnres (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    if ← atDigit then return ← pSimpleId f
    let some c ← peek | fail
    let some d ← peek2 | fail
    if c == 'o' && d == 'n' then
      adv 2
      let some a ← peek | fail
      let some b ← peek2 | fail
      let some (o, _) := exprOp a b | fail
      adv 2
      if (← peek) == some 'I' then
        let args ← pTArgs f
        return o ++ (← tArgs o args)
      return o
    if c == 'd' && d == 'n' then
      adv 2
      if let some t ← attempt (pUnresType f) then return "~" ++ t
      return "~" ++ (← pSimpleId f)
    fail
  termination_by (f, 0)

/-- One or more `<unresolved-qualifier-level>`s, each followed by `::`, then `E`. -/
def pLevels (f : Nat) (k : Nat) : CM String :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    let l ← pSimpleId f
    if ← atDigit then return l ++ "::" ++ (← pLevels (f + 1) k)
    expect 'E'
    pure (l ++ "::")
  termination_by (f, k)

/-- `<unresolved-name>`. -/
def pUnresolved (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    let some d ← peek2 | fail
    if c == 'g' && d == 's' then
      adv 2
      if let some b ← attempt (pBaseUnres f) then return "::" ++ b
      expect 's'; expect 'r'
      let ls ← pLevels f (← get).s.size
      return "::" ++ ls ++ (← pBaseUnres f)
    if let some b ← attempt (pBaseUnres f) then return b
    expect 's'; expect 'r'
    if (← eat 'N') then
      let t ← pUnresType f
      let ls ← pLevels f (← get).s.size
      return t ++ "::" ++ ls ++ (← pBaseUnres f)
    if let some r ← attempt (do let t ← pUnresType f; let b ← pBaseUnres f; pure (t ++ "::" ++ b)) then
      return r
    let ls ← pLevels f (← get).s.size
    return ls ++ (← pBaseUnres f)
  termination_by (f, 0)

/-- A `<member-name>` after `dt`/`pt`: an unqualified name, parenthesised with its template
arguments if it has some. -/
def pMemberName (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    let n ← pUnqual f ""
    if (← peek) == some 'I' then
      let args ← pTArgs f
      return "(" ++ n.text ++ (← tArgs n.text args) ++ ")"
    pure n.text
  termination_by (f, 0)

/-- Expressions up to the character `stop`. -/
def pExprsTo (f : Nat) (stop : Char) (k : Nat) : CM (List String) :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    if (← eat stop) then return []
    let e ← pExpr f
    let rest ← pExprsTo (f + 1) stop k
    pure (e.1 :: rest)
  termination_by (f, k)

/-- Expressions up to `E`. -/
def pExprList (f : Nat) (k : Nat) : CM (List String) :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    if (← eat 'E') then return []
    let e ← pExpr f
    let rest ← pExprList (f + 1) k
    pure (e.1 :: rest)
  termination_by (f, k)

/-- `<unqualified-name>` (`L` internal linkage allowed). -/
def pUnqual (f : Nat) (prefixLast : String) : CM NameR :=
  match f with
  | 0 => fail
  | f + 1 => do
    let internal ← eat 'L'
    let some c ← peek | fail
    if internal && !c.isDigit then fail
    if c.isDigit then
      let n ← sourceName
      let tags ← abiTags
      return { text := n ++ tags, last := n }
    -- outside a nested name a constructor or destructor names the enclosing encoding's leaf
    -- (`scope.leaf_name()`), resolved when the encoding is complete (`leafMark`)
    -- (`scope.leaf_name()`: the leaf of the whole name, also inside a nested name)
    let prefixLast := (fun (_ : String) => String.singleton leafMark) prefixLast
    if c == 'C' then
      let some d ← peek2 | fail
      if d ∈ ['1', '2', '3', '4'] then
        adv 2
        let tags ← abiTags
        return { text := prefixLast ++ tags, last := "", noRet := true }
      if d == 'I' then
        -- an inheriting constructor `CI n <type>`: named after the inherited class
        adv 2
        let some k ← peek | fail
        if k ∉ ['1', '2', '3', '4'] then fail
        adv
        if let some c ← peek then if (builtin c).isSome then fail
        let t ← pType f
        -- the inherited type's leaf name: a class type only
        let .base _ := t | fail
        let x := stripMarks t.raw
        let x := match x.splitOn "<" with | h :: _ => h | [] => x
        let x := ((x.splitOn "::").getLast?).getD x
        let tags ← abiTags
        return { text := x ++ tags, last := "", noRet := true }
      fail
    if c == 'D' then
      let some d ← peek2 | fail
      if d ∈ ['0', '1', '2', '4'] then
        adv 2
        let tags ← abiTags
        return { text := "~" ++ prefixLast ++ tags, last := "", noRet := true }
      fail
    if c == 'U' then
      let some d ← peek2 | fail
      if d == 'l' then
        adv 2
        let saved := (← get).inLambda
        modify fun st => { st with inLambda := true }
        let ps ← if (← peek) == some 'v' then adv; pure [] else pParams f (← get).s.size
        if ps.isEmpty && (← get).s[(← get).pos - 1]? != some 'v' then fail
        modify fun st => { st with inLambda := saved }
        expect 'E'
        let n ← optNumber
        expect '_'
        let (sig, pk) := lambdaSigText ps (← get).pack
        modify fun st => { st with pack := pk }
        let s := "{lambda(" ++ sig ++ ")#" ++ toString ((n.map (· + 2)).getD 1) ++ "}"
        return { text := s, last := s }
      if d == 't' then
        adv 2
        let n ← optNumber
        expect '_'
        let s := "{unnamed type#" ++ toString ((n.map (· + 1)).getD 1) ++ "}"
        return { text := s, last := s }
      fail
    let some d ← peek2 | fail
    -- `on <operator-name>` (an operator in an unresolved or member name)
    let (c, d) ← if c == 'o' && d == 'n' then do
        let st ← get
        match st.s[st.pos + 2]?, st.s[st.pos + 3]? with
        | some a, some b => adv 2; pure (a, b)
        | _, _ => pure (c, d)
      else pure (c, d)
    if c == 'c' && d == 'v' then
      adv 2
      -- a conversion to a template parameter whose arguments follow the name: resolved when
      -- they are read (`pUnscoped`)
      if (← peek) == some 'T' && (← get).targs.isEmpty then
        let save ← get
        adv
        let i := ((← seqId).map (· + 1)).getD 0
        if (← peek) == some 'I' then
          return { text := "operator ", last := "operator ", convParam := some i }
        set save
      let saved := (← get).inConv
      modify fun st => { st with inConv := true }
      let t ← pType f
      modify fun st => { st with inConv := saved }
      let s := "operator " ++ (← strT t)
      return { text := s, last := "" }
    match opName c d with
    | some o =>
      adv 2
      let s := "operator" ++ o
      let tags ← abiTags
      pure { text := s ++ tags, last := "" }
    | none => fail

  termination_by (f, 0)
/-- `<unscoped-name>` (with `St`), possibly followed by template arguments. -/
def pUnscoped (f : Nat) : CM NameR :=
  match f with
  | 0 => fail
  | f + 1 => do
    let mut pre := ""
    if (← peek) == some 'S' && (← peek2) == some 't' then adv 2; pre := "std::"
    let n ← pUnqual f ""
    let n := { n with text := pre ++ n.text }
    if (← peek) == some 'I' then
      addSub (.base n.text) n.last
      let args ← pTArgs f
      let n ← match n.convParam with
        | some i => match args[i]? with
          | some t => do pure { n with text := n.text ++ (← strT t), convParam := none }
          | none => pure n
        | none => pure n
      if n.convParam.isSome then fail
      pure { n with text := n.text ++ (← tArgs n.text args), tmpl := true, targs := some args }
    else if n.convParam.isSome then fail
    else pure n

  termination_by (f, 0)
/-- The components of a nested name after `N` and its qualifiers. -/
def pNestedGo (f : Nat) (k : Nat) (acc : Option NameR) : CM NameR :=
  match f, k with
  | 0, _ => fail
  | _, 0 => fail
  | f + 1, k + 1 => do
    if (← eat 'E') then
      match acc with
      | some n => if n.bareSub then fail else return n
      | none => fail
    let some c ← peek | fail
    let d ← peek2
    -- `PrefixHandle::parse`: a substitution or a template parameter replaces the prefix so far
    let keepLast (n : NameR) : NameR :=
      if n.last.isEmpty then { n with last := (acc.map (·.last)).getD "" } else n
    let (n, isSubst, isSrc) ← if c == 'S' && d != some 't' then do
        let e ← pSubst
        pure ({ text := e.ty.raw, last := e.last, bareSub := true : NameR }, true, false)
      else if c == 'S' && acc.isSome then do
        -- `St` inside a nested name: the well-known `std` replaces the prefix
        adv 2
        pure ({ text := "std", last := "std", bareSub := true : NameR }, true, false)
      else if c == 'S' && acc.isNone then do
        adv 2
        let u ← pUnqual f ""
        pure ({ u with text := "std::" ++ u.text }, false, true)
      else if c == 'I' then do
        let some a := acc | fail
        let args ← pTArgs f
        let txt := a.text ++ (← tArgs a.text args)
        let r : NameR := { a with text := txt, tmpl := true, targs := some args, bareSub := false }
        pure (r, false, false)
      else if c == 'T' then do
        -- `Prefix::TemplateParam`: one substitution candidate, added below
        adv
        let i := ((← seqId).map (· + 1)).getD 0
        let some t := (← get).targs[i]? | fail
        pure ({ text := t.raw, last := "" : NameR }, false, false)
      else if c == 'D' && (d == some 'T' || d == some 't') then do
        let t ← pType f
        pure ({ text := t.raw, last := "" : NameR }, false, false)
      else do
        let pl := (acc.map (·.last)).getD ""
        let isSrc := c.isDigit || c == 'L'
        let u ← pUnqual f pl
        pure (keepLast (match acc with
          | some a => { u with text := a.text ++ "::" ++ u.text }
          | none => u), false, isSrc)
    -- `<data-member-prefix>`: `M` after a source name (not printed; not the last component)
    let isUnq := !isSubst && c != 'I' && c != 'T' && !(c == 'D' && (d == some 'T' || d == some 't'))
    if (← peek) == some 'M' then
      if !isUnq || (acc.isSome && !isSrc) then fail
      adv
      if (← peek) == some 'E' then fail
    if (← peek) != some 'E' && !isSubst then addSub (.base n.text) n.last
    pNestedGo (f + 1) k (some n)
  termination_by (f, k)

/-- `<nested-name>`: `N [quals] [ref] components E`. -/
def pNested (f : Nat) : CM NameR :=
  match f with
  | 0 => fail
  | f + 1 => do
    expect 'N'
    let mut q ← cvQuals
    if (← eat 'R') then q := q ++ " &" else if (← eat 'O') then q := q ++ " &&"
    let n ← pNestedGo f (← get).s.size none
    pure { n with quals := q }

  termination_by (f, 0)
/-- `<name>`. -/
def pName (f : Nat) : CM NameR :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    if c == 'N' then pNested f
    else if c == 'Z' then
      adv
      let e ← pEncoding f
      expect 'E'
      if (← eat 's') then
        pDiscr
        return { text := e ++ "::string literal", last := "string literal" }
      let n ← pName f
      pDiscr
      pure { n with text := e ++ "::" ++ n.text }
    else if c == 'S' && (← peek2) != some 't' then
      let e ← pSubst
      if (← peek) == some 'I' then
        let args ← pTArgs f
        pure { text := e.ty.raw ++ (← tArgs e.ty.raw args), last := e.last, tmpl := true, targs := some args }
      -- a substitution names something only with template arguments (`UnscopedTemplateName`)
      else fail
    else pUnscoped f

  termination_by (f, 0)
/-- `<encoding>`, printed. -/
def pEncoding (f : Nat) : CM String :=
  match f with
  | 0 => fail
  | f + 1 => do
    let some c ← peek | fail
    let some d ← peek2 | fail
    if c == 'T' then
      adv 2
      match d with
      | 'V' => let t ← pType f; return "{vtable(" ++ (← strT t) ++ ")}"
      | 'T' => let t ← pType f; return "{vtt(" ++ (← strT t) ++ ")}"
      | 'I' => let t ← pType f; return "typeinfo for " ++ (← strT t)
      | 'S' => let t ← pType f; return "typeinfo name for " ++ (← strT t)
      | 'h' | 'v' =>
        modify fun st => { st with pos := st.pos - 1 }
        let o ← callOffset
        let e ← pEncoding f
        return "{virtual override thunk(" ++ o ++ ", " ++ e ++ ")}"
      | 'c' =>
        let o1 ← callOffset
        let o2 ← callOffset
        let e ← pEncoding f
        return "{virtual override thunk(" ++ o1 ++ ", " ++ o2 ++ ", " ++ e ++ ")}"
      | 'C' =>
        let t1 ← pType f
        let _ ← number false
        expect '_'
        let t2 ← pType f
        return "construction vtable for " ++ (← strT t1) ++ "-in-" ++ (← strT t2)
      | 'F' => let t ← pType f; return "typeinfo fn for " ++ (← strT t)
      | 'H' => let n ← pName f; return "TLS init function for " ++ stripMarks n.text ++ n.quals
      | 'W' => let n ← pName f; return "TLS wrapper function for " ++ stripMarks n.text ++ n.quals
      | _ => fail
    if c == 'G' && d == 'V' then
      adv 2
      let n ← pName f
      return "guard variable for " ++ stripMarks n.text ++ n.quals
    if c == 'G' && d == 'R' then
      adv 2
      let n ← pName f
      let i := ((← seqId).map (· + 1)).getD 0
      return "reference temporary #" ++ toString i ++ " for " ++ stripMarks n.text ++ n.quals
    if c == 'G' && d == 'T' then
      adv 2
      let some k ← peek | fail
      adv
      let e ← pEncoding f
      return (if k == 'n' then "non-transaction clone for " else "transaction clone for ") ++ e
    let n ← pName f
    if let some a := n.targs then modify fun st => { st with targs := a }
    let c ← peek
    let leaf := stripMarks n.last
    if c.isNone || c == some 'E' || c == some '.' then
      -- a data name; a constructor or destructor needs its parameters
      if n.noRet then fail
      -- no template arguments are in scope for a data name's own arguments
      if n.text.contains '\x03' then fail
      return fillLeaf leaf (stripMarks n.text ++ n.quals)
    -- cpp_demangle reads a return type for every template function, constructors and
    -- destructors included, and does not print it for those
    let ret ← if n.tmpl then some <$> pType f else pure none
    let ret := if n.noRet then none else ret
    let ps ← pParams f (← get).s.size
    let r ← match ret with
      | some r => do pure ((← strT r) ++ " ")
      | none => pure ""
    -- the parameters are printed where the name first pops the inner stack (`Encoding` is on
    -- it while the name prints): a pop point inside the name, or its end
    let (first, rest) := match n.text.splitOn "\x01" with
      | first :: rest@(_ :: _) => (first, some (String.join rest))
      | _ => (n.text, none)
    let lc := if first.isEmpty then none else some first.back
    let (pt, pk) := paramsText ps (← get).pack lc
    modify fun st => { st with pack := pk }
    match rest with
    | some rest => pure (fillLeaf leaf (r ++ first ++ pt ++ stripMarks rest ++ n.quals))
    | none => pure (fillLeaf leaf (r ++ first ++ pt ++ n.quals))
  termination_by (f, 0)
end

/-- A `<number>` at the front: its digits (no leading zero but `0` itself) and the rest. -/
def numberPrefix (cs : List Char) : Option (List Char × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty || (ds.length > 1 && ds.head? == some '0') then none else some (ds, cs.drop ds.length)

/-- Clone suffixes (`CloneSuffix`): `.` an identifier (`$`, `_`, letters and digits), then
`.number`s, each printed ` [clone .ident.n…]`. -/
def cloneSuffixes (cs : List Char) : Option String :=
  let rec nums : Nat → List Char → String × List Char
    | 0, r => ("", r)
    | g + 1, '.' :: r =>
      match numberPrefix r with
      | some (ds, r') => let (more, r'') := nums g r'; ("." ++ String.ofList ds ++ more, r'')
      | none => ("", '.' :: r)
    | _, r => ("", r)
  let rec go : Nat → List Char → Option String
    | 0, _ => none
    | _, [] => some ""
    | f + 1, '.' :: r =>
      let w := r.takeWhile fun c => c == '$' || c == '_' || (c.toNat < 128 && c.isAlphanum)
      if w.isEmpty then none else
      let (ns, r) := nums r.length (r.drop w.length)
      (go f r).map (" [clone ." ++ String.ofList w ++ ns ++ "]" ++ ·)
    | _, _ :: _ => none
  go (cs.length + 1) cs

/-- Resolve the forward template references `\x03 i \x04` with the template arguments `targs`
(`none` when one is out of range). -/
def resolveFwd (targs : List CTy) (s : String) : Option String :=
  if !s.contains '\x03' then some s else
  let rec go : Nat → List Char → Option (List Char)
    | 0, _ => none
    | _, [] => some []
    | f + 1, '\x03' :: r =>
      let ds := r.takeWhile (· != '\x04')
      let r := (r.drop ds.length).drop 1
      match targs[(String.ofList ds).toNat!]? with
      | some t =>
        -- an argument referring to itself does not resolve (cpp_demangle's recursion limit)
        let x := stripMarks t.show
        if x.contains '\x03' then none else (go f r).map (x.toList ++ ·)
      | none => none
    | f + 1, c :: r => (go f r).map (c :: ·)
  (go (s.length + 1) s.toList).map String.ofList

/-- **`cpp_demangle::Symbol::new(s)?.demangle()`** on the subset. -/
def cppDemangle (s : String) : Option String :=
  if !s.toList.all (fun c => c.toNat < 128) then none else
  let cs := s.toList
  let (body, isEnc) := match cs with
    | '_' :: 'Z' :: r => (r, true)
    | '_' :: '_' :: 'Z' :: r => (r, true)
    | r => (r, false)
  if isEnc then
    match (pEncoding cppFuel).run { s := body.toArray } with
    | .ok (t, st) =>
      match cloneSuffixes (body.drop st.pos), resolveFwd st.targs t with
      | some suf, some t => if t.contains leafMark then none else some (stripMarks t ++ suf)
      | _, _ => none
    | .error _ => none
  else if body == ['S', 't'] then some "std"
  else
    match (pType cppFuel).run { s := body.toArray } with
    | .ok (t, st) =>
      let x := stripMarks t.show
      if st.pos == body.length && !x.contains leafMark && !x.contains '\x03' then some x else none
    | .error _ => none

end Silmaril.Wasm.Tools.Meta.Demangle

end
