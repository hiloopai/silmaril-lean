module

public import Silmaril.Formats.SExp.Encoding

/-!
# The `.wast` script grammar

The abstract syntax of WebAssembly script files (`.wast`) as `wasm-tools` 1.262.0 reads
them (`crates/wast/src/wast.rs`: `Wast`, `WastDirective`, `QuoteWat`, `WastExecute`,
`WastInvoke`; values: `core/wast.rs` `WastArgCore`/`WastRetCore`, `component/wast.rs`
`WastVal`), over the S-expressions of the WAT lexical grammar
(`Silmaril.Formats.SExpEncoding.SExp`).

The grammar is given by a **printer** (`Script.toSExps`, `Directive.toSExp`, …): a syntax
tree denotes the S-expressions it prints to. The **reader** (`Script.ofSExps?`, …) inverts
it; the round-trip laws are in `Silmaril.Wasm.Tools.Wast.Syntax.Thms`:

* `ofSExp? (toSExp d) = some d` for every well-formed `d` (`WF`: the side conditions that
  make printing injective, such as "an anonymous module's first field is not an
  identifier");
* `ofSExp? x = some d → toSExp d = x`: everything the reader accepts is the print of what
  it returns.

Two levels are kept apart:

* **structure** (this module): directives, modules, actions and values down to their
  tokens. Numeric literals stay as their token text, module bodies stay S-expressions (the
  module grammar is the WAT text format's, `Silmaril.Wasm.Text`; component bodies the
  component text format's);
* **meaning** (`Silmaril.Wasm.Tools.Wast.Json`): literal values (by silmaril-lean's literal
  relations `Text.IN`/`Text.FN`), the arity of each value form, module encoding.

Values: `wast` has two value grammars (core `i32.const`… and component `u8.const`…); they
share a shape, a head keyword followed by atoms (`Val.lit`) or by strings and nested
values (`Val.mixed`). A record field `(field "n" v)` is a `Val.mixed "field" ["n"] [v]`.
Which heads are literal-shaped is `litHeads`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast

open Silmaril.Formats Silmaril.Formats.SExpEncoding

/-! ## Atoms -/

/-- A bare token. -/
abbrev sym (s : String) : SExp := .atom (.sym s)
/-- An identifier `$n`. -/
abbrev ident (n : String) : SExp := .atom (.id n)
/-- A string literal. -/
abbrev strA (b : List UInt8) : SExp := .atom (.str b)

/-- A proper list (as `listOf`, by structural recursion). -/
def lst : List SExp → SExp
  | [] => .nil
  | x :: xs => .cons x (lst xs)

/-- An optional identifier. -/
def idOpt : Option String → List SExp
  | none => []
  | some n => [ident n]

/-- The elements of a proper list. -/
def elems? : SExp → Option (List SExp)
  | .nil => some []
  | .cons x r => (elems? r).map (x :: ·)
  | .atom _ => none

/-- A bare token's text. -/
def sym? : SExp → Option String
  | .atom (.sym s) => some s
  | _ => none

/-- A string literal's bytes. -/
def str? : SExp → Option (List UInt8)
  | .atom (.str b) => some b
  | _ => none

/-- Leading identifier. -/
def takeId : List SExp → Option String × List SExp
  | .atom (.id n) :: xs => (some n, xs)
  | xs => (none, xs)

/-- All elements are string literals. -/
def strs? : List SExp → Option (List (List UInt8))
  | [] => some []
  | x :: xs => do let b ← str? x; let bs ← strs? xs; pure (b :: bs)

/-- All elements are bare tokens. -/
def syms? : List SExp → Option (List String)
  | [] => some []
  | x :: xs => do let b ← sym? x; let bs ← syms? xs; pure (b :: bs)

/-- The longest prefix of string literals, and the rest. -/
def spanStrs : List SExp → List (List UInt8) × List SExp
  | .atom (.str b) :: xs => let r := spanStrs xs; (b :: r.1, r.2)
  | xs => ([], xs)

/-! ## Modules -/

/-- `module` or `component`. -/
inductive ModKind where
  | core
  | component
  deriving DecidableEq, Repr, Inhabited

def ModKind.kw : ModKind → String
  | .core => "module"
  | .component => "component"

def ModKind.ofKw? : String → Option ModKind
  | "module" => some .core
  | "component" => some .component
  | _ => none

/-- The body of a module after its identifier: text fields, or `binary` strings. -/
inductive Body where
  | fields (xs : List SExp)
  | binary (strs : List (List UInt8))
  deriving DecidableEq, Repr, Inhabited

/-- `QuoteWat`: a module in text, in binary, or quoted. -/
inductive QuoteWat where
  | wat (k : ModKind) (id : Option String) (b : Body)
  | quote (k : ModKind) (strs : List (List UInt8))
  deriving DecidableEq, Repr, Inhabited

def Body.toSExps : Body → List SExp
  | .fields xs => xs
  | .binary ss => sym "binary" :: ss.map strA

/-- Read a body: `binary "…"*`, or fields. -/
def Body.ofSExps? (xs : List SExp) : Option Body :=
  if xs.head? = some (sym "binary") then (strs? xs.tail).map .binary
  else some (.fields xs)

/-- The elements of `(module …)`. -/
def QuoteWat.toSExps : QuoteWat → List SExp
  | .wat k id b => sym k.kw :: (idOpt id ++ b.toSExps)
  | .quote k ss => sym k.kw :: sym "quote" :: ss.map strA

def QuoteWat.toSExp (m : QuoteWat) : SExp := lst m.toSExps

/-- Read the rest of `(module …)` after the keyword. -/
def QuoteWat.ofRest? (k : ModKind) (xs : List SExp) : Option QuoteWat :=
  if xs.head? = some (sym "quote") then (strs? xs.tail).map (.quote k)
  else
    let (id, rest) := takeId xs
    (Body.ofSExps? rest).map (.wat k id)

/-- Read the elements of `(module …)`. -/
def QuoteWat.ofSExps? : List SExp → Option QuoteWat
  | .atom (.sym k) :: xs => do QuoteWat.ofRest? (← ModKind.ofKw? k) xs
  | _ => none

def QuoteWat.ofSExp? (x : SExp) : Option QuoteWat := elems? x >>= QuoteWat.ofSExps?

/-- Keywords that may not start the fields of an anonymous text module (they would be read
as another form). -/
def reservedHead : SExp → Bool
  | .atom (.id _) => true
  | .atom (.sym "binary") | .atom (.sym "quote") | .atom (.sym "definition")
  | .atom (.sym "instance") => true
  | _ => false

/-- Well-formed bodies: printing is injective. -/
def Body.WF (id : Option String) : Body → Prop
  | .fields xs => match id with
    | none => ∀ x ∈ xs.head?, reservedHead x = false
    | some _ => xs.head? ≠ some (sym "binary")
  | .binary _ => True

def QuoteWat.WF : QuoteWat → Prop
  | .wat _ id b => b.WF id
  | .quote _ _ => True

/-! ## Values -/

/-- A value: core argument/result or component value. -/
inductive Val where
  /-- `(head atom*)`: numbers, `v128.const`, `ref.*`, `bool.const`, `option.none`. -/
  | lit (head : String) (args : List String)
  /-- `(head "s"* v*)`: strings and nested values (`either`, `list.const`, `record.const`,
  `field`, `variant.const`, `str.const`, …). -/
  | mixed (head : String) (strs : List (List UInt8)) (vs : List Val)
  deriving Repr, Inhabited

/-- Heads whose arguments are bare tokens. -/
def litHeads : List String :=
  ["i32.const", "i64.const", "f32.const", "f64.const", "v128.const", "ref.null",
   "ref.extern", "ref.host", "ref.func", "ref.any", "ref.eq", "ref.array", "ref.struct",
   "ref.i31", "ref.i31_shared", "bool.const", "u8.const", "s8.const", "u16.const",
   "s16.const", "u32.const", "s32.const", "u64.const", "s64.const", "option.none"]

mutual
  def Val.toSExp : Val → SExp
    | .lit h as => .cons (sym h) (lst (as.map sym))
    | .mixed h ss vs => .cons (sym h) (lst (ss.map strA ++ Val.listToSExps vs))

  def Val.listToSExps : List Val → List SExp
    | [] => []
    | v :: vs => v.toSExp :: Val.listToSExps vs
end

mutual
  /-- Read a value. -/
  def Val.ofSExp? : SExp → Option Val
    | .cons (.atom (.sym h)) r =>
      if h ∈ litHeads then do
        let xs ← elems? r
        let as ← syms? xs
        pure (.lit h as)
      else (Val.mixedTail? r).map fun p => .mixed h p.1 p.2
    | _ => none

  /-- Read `"s"* v*` after a head. -/
  def Val.mixedTail? : SExp → Option (List (List UInt8) × List Val)
    | .nil => some ([], [])
    | .cons (.atom (.str b)) r => (Val.mixedTail? r).map fun p => (b :: p.1, p.2)
    | .cons x r => do
      let v ← Val.ofSExp? x
      let vs ← Val.valsOf? r
      pure ([], v :: vs)
    | .atom _ => none

  /-- Read the values of a proper list. -/
  def Val.valsOf? : SExp → Option (List Val)
    | .nil => some []
    | .cons x r => do
      let v ← Val.ofSExp? x
      let vs ← Val.valsOf? r
      pure (v :: vs)
    | .atom _ => none
end

/-- Read a list of values. -/
def Val.listOf? : List SExp → Option (List Val)
  | [] => some []
  | x :: xs => do let v ← Val.ofSExp? x; let vs ← Val.listOf? xs; pure (v :: vs)

mutual
  /-- Well-formed values: the head decides the form. -/
  def Val.WF : Val → Prop
    | .lit h _ => h ∈ litHeads
    | .mixed h _ vs => h ∉ litHeads ∧ Val.listWF vs

  def Val.listWF : List Val → Prop
    | [] => True
    | v :: vs => v.WF ∧ Val.listWF vs
end

/-! ## Actions -/

/-- `(invoke $m? "name" arg*)`. -/
structure Invoke where
  module : Option String
  name : List UInt8
  args : List Val
  deriving Repr, Inhabited

def Invoke.toSExps (i : Invoke) : List SExp :=
  sym "invoke" :: (idOpt i.module ++ strA i.name :: Val.listToSExps i.args)

def Invoke.ofSExps? : List SExp → Option Invoke
  | .atom (.sym k) :: xs =>
    if k = "invoke" then
      match takeId xs with
      | (m, .atom (.str n) :: args) => (Val.listOf? args).map (⟨m, n, ·⟩)
      | _ => none
    else none
  | _ => none

/-- `WastExecute`: an invocation, a module instantiation, or a global read. -/
inductive Exec where
  | invoke (i : Invoke)
  | wat (m : QuoteWat)
  | get (module : Option String) (name : List UInt8)
  deriving Repr, Inhabited

def Exec.toSExp : Exec → SExp
  | .invoke i => lst i.toSExps
  | .wat m => m.toSExp
  | .get m n => lst (sym "get" :: (idOpt m ++ [strA n]))

def Exec.ofSExp? (x : SExp) : Option Exec := do
  let xs ← elems? x
  match xs with
  | .atom (.sym k) :: rest =>
    if k = "invoke" then (Invoke.ofSExps? xs).map .invoke
    else if k = "get" then
      match takeId rest with
      | (m, [.atom (.str n)]) => some (.get m n)
      | _ => none
    else
      match ModKind.ofKw? k with
      | some mk =>
        match QuoteWat.ofRest? mk rest with
        | some (.wat k id b) => some (.wat (.wat k id b))
        | _ => none
      | none => none
  | _ => none

/-! ## Directives -/

/-- `WastDirective`. -/
inductive Directive where
  | module (m : QuoteWat)
  /-- `(module definition $id? …)`. -/
  | moduleDefinition (k : ModKind) (id : Option String) (b : Body)
  /-- `(module instance $instance? $module?)`. -/
  | moduleInstance (k : ModKind) (inst mod : Option String)
  | assertMalformed (m : QuoteWat) (msg : List UInt8)
  | assertMalformedCustom (m : QuoteWat) (msg : List UInt8)
  | assertInvalid (m : QuoteWat) (msg : List UInt8)
  | assertInvalidCustom (m : QuoteWat) (msg : List UInt8)
  | register (name : List UInt8) (mod : Option String)
  | invoke (i : Invoke)
  | assertTrap (e : Exec) (msg : List UInt8)
  | assertReturn (e : Exec) (results : List Val)
  | assertExhaustion (i : Invoke) (msg : List UInt8)
  | assertUnlinkable (m : QuoteWat) (msg : List UInt8)
  | assertException (e : Exec)
  | assertSuspension (e : Exec) (msg : List UInt8)
  /-- `(thread $name (shared (module $m))? directive*)`. -/
  | thread (name : String) (shared : Option String) (ds : List Directive)
  | wait (thread : String)
  deriving Repr, Inhabited

/-- The keyword of an assertion over a module. -/
def assertModKw : Nat → String
  | 0 => "assert_malformed"
  | 1 => "assert_malformed_custom"
  | 2 => "assert_invalid"
  | 3 => "assert_invalid_custom"
  | _ => "assert_unlinkable"

mutual
  def Directive.toSExp : Directive → SExp
    | .module m => m.toSExp
    | .moduleDefinition k id b => lst (sym k.kw :: sym "definition" :: (idOpt id ++ b.toSExps))
    | .moduleInstance k i m => lst (sym k.kw :: sym "instance" :: (idOpt i ++ idOpt m))
    | .assertMalformed m s => lst [sym "assert_malformed", m.toSExp, strA s]
    | .assertMalformedCustom m s => lst [sym "assert_malformed_custom", m.toSExp, strA s]
    | .assertInvalid m s => lst [sym "assert_invalid", m.toSExp, strA s]
    | .assertInvalidCustom m s => lst [sym "assert_invalid_custom", m.toSExp, strA s]
    | .register n m => lst (sym "register" :: strA n :: idOpt m)
    | .invoke i => lst i.toSExps
    | .assertTrap e s => lst [sym "assert_trap", e.toSExp, strA s]
    | .assertReturn e rs => lst (sym "assert_return" :: e.toSExp :: Val.listToSExps rs)
    | .assertExhaustion i s => lst [sym "assert_exhaustion", lst i.toSExps, strA s]
    | .assertUnlinkable m s => lst [sym "assert_unlinkable", m.toSExp, strA s]
    | .assertException e => lst [sym "assert_exception", e.toSExp]
    | .assertSuspension e s => lst [sym "assert_suspension", e.toSExp, strA s]
    | .thread n sh ds =>
      lst (sym "thread" :: ident n ::
        ((match sh with
          | none => []
          | some m => [lst [sym "shared", lst [sym "module", ident m]]]) ++
          Directive.listToSExps ds))
    | .wait n => lst [sym "wait", ident n]

  def Directive.listToSExps : List Directive → List SExp
    | [] => []
    | d :: ds => d.toSExp :: Directive.listToSExps ds
end

/-- An assertion `(kw (module …) "msg")`. -/
def modAssert? (mk : QuoteWat → List UInt8 → Directive) (noQuote : Bool) :
    List SExp → Option Directive
  | [m, .atom (.str s)] => do
    let q ← QuoteWat.ofSExp? m
    match q, noQuote with
    | .quote .., true => none
    | q, _ => pure (mk q s)
  | _ => none

/-- An assertion `(kw exec "msg")`. -/
def execAssert? (mk : Exec → List UInt8 → Directive) : List SExp → Option Directive
  | [e, .atom (.str s)] => do pure (mk (← Exec.ofSExp? e) s)
  | _ => none

/-- The rest of `(module …)`/`(component …)`: a definition, an instance or a module. -/
def moduleForm? (k : ModKind) (rest : List SExp) : Option Directive :=
  if rest.head? = some (sym "definition") then
    let (id, r) := takeId rest.tail
    (Body.ofSExps? r).map (.moduleDefinition k id)
  else if rest.head? = some (sym "instance") then
    match rest.tail with
    | [] => some (.moduleInstance k none none)
    | [.atom (.id i)] => some (.moduleInstance k (some i) none)
    | [.atom (.id i), .atom (.id m)] => some (.moduleInstance k (some i) (some m))
    | _ => none
  else (QuoteWat.ofRest? k rest).map .module

/-- `register "name" $m?`. -/
def registerOf? : List SExp → Option Directive
  | [.atom (.str n)] => some (.register n none)
  | [.atom (.str n), .atom (.id m)] => some (.register n (some m))
  | _ => none

/-- `assert_return exec result*`. -/
def assertReturnOf? : List SExp → Option Directive
  | e :: rs => do
    let e ← Exec.ofSExp? e
    let vs ← Val.listOf? rs
    pure (.assertReturn e vs)
  | [] => none

/-- `assert_exhaustion (invoke …) "msg"`. -/
def assertExhaustionOf? : List SExp → Option Directive
  | [i, .atom (.str s)] => do
    let is ← elems? i
    let i ← Invoke.ofSExps? is
    pure (.assertExhaustion i s)
  | _ => none

/-- Read a directive with keyword `k` (other than `thread`) from the rest of its elements. -/
def Directive.ofKw? (k : String) (rest : List SExp) : Option Directive :=
  match k with
  | "module" => moduleForm? .core rest
  | "component" => moduleForm? .component rest
  | "assert_malformed" => modAssert? .assertMalformed false rest
  | "assert_malformed_custom" => modAssert? .assertMalformedCustom false rest
  | "assert_invalid" => modAssert? .assertInvalid false rest
  | "assert_invalid_custom" => modAssert? .assertInvalidCustom false rest
  | "assert_unlinkable" => modAssert? .assertUnlinkable true rest
  | "register" => registerOf? rest
  | "invoke" => (Invoke.ofSExps? (sym "invoke" :: rest)).map .invoke
  | "assert_trap" => execAssert? .assertTrap rest
  | "assert_return" => assertReturnOf? rest
  | "assert_exhaustion" => assertExhaustionOf? rest
  | "assert_exception" =>
    match rest with
    | [e] => (Exec.ofSExp? e).map .assertException
    | _ => none
  | "assert_suspension" => execAssert? .assertSuspension rest
  | "wait" =>
    match rest with
    | [.atom (.id n)] => some (.wait n)
    | _ => none
  | _ => none

/-- Read a directive that has no nested directives, from its elements. -/
def Directive.ofElems? : List SExp → Option Directive
  | .atom (.sym k) :: rest => Directive.ofKw? k rest
  | _ => none

mutual
  /-- Read a directive. -/
  def Directive.ofSExp? : SExp → Option Directive
    | .cons (.atom (.sym "thread")) (.cons (.atom (.id n))
        (.cons (.cons (.atom (.sym "shared")) (.cons (.cons (.atom (.sym "module"))
          (.cons (.atom (.id m)) .nil)) .nil)) ds)) =>
      (Directive.dirsOf? ds).map (.thread n (some m))
    | .cons (.atom (.sym "thread")) (.cons (.atom (.id n)) ds) =>
      (Directive.dirsOf? ds).map (.thread n none)
    | x => elems? x >>= Directive.ofElems?

  /-- Read the directives of a proper list. -/
  def Directive.dirsOf? : SExp → Option (List Directive)
    | .nil => some []
    | .cons x r => do
      let d ← Directive.ofSExp? x
      let ds ← Directive.dirsOf? r
      pure (d :: ds)
    | .atom _ => none
end

/-- Read a list of directives. -/
def Directive.listOf? : List SExp → Option (List Directive)
  | [] => some []
  | x :: xs => do
    let d ← Directive.ofSExp? x
    let ds ← Directive.listOf? xs
    pure (d :: ds)

/-! ## Well-formedness -/

def Invoke.WF (i : Invoke) : Prop := Val.listWF i.args

def Exec.WF : Exec → Prop
  | .invoke i => i.WF
  | .wat (.wat _ id b) => b.WF id
  | .wat (.quote ..) => False
  | .get _ _ => True

/-- The keyword of a directive's S-expression. -/
def Directive.kw : Directive → String
  | .module (.wat k ..) | .module (.quote k ..) => k.kw
  | .moduleDefinition k .. | .moduleInstance k .. => k.kw
  | .assertMalformed .. => "assert_malformed"
  | .assertMalformedCustom .. => "assert_malformed_custom"
  | .assertInvalid .. => "assert_invalid"
  | .assertInvalidCustom .. => "assert_invalid_custom"
  | .assertUnlinkable .. => "assert_unlinkable"
  | .register .. => "register"
  | .invoke _ => "invoke"
  | .assertTrap .. => "assert_trap"
  | .assertReturn .. => "assert_return"
  | .assertExhaustion .. => "assert_exhaustion"
  | .assertException .. => "assert_exception"
  | .assertSuspension .. => "assert_suspension"
  | .thread .. => "thread"
  | .wait _ => "wait"

mutual
  /-- Well-formed directives: printing is injective on them. -/
  def Directive.WF : Directive → Prop
    | .module m => m.WF
    | .moduleDefinition _ id b => b.WF id
    | .moduleInstance _ i m => i = none → m = none
    | .assertMalformed m _ | .assertMalformedCustom m _ | .assertInvalid m _
    | .assertInvalidCustom m _ => m.WF
    | .assertUnlinkable m _ => m.WF ∧ ∀ k ss, m ≠ .quote k ss
    | .register _ _ => True
    | .invoke i => i.WF
    | .assertTrap e _ | .assertException e | .assertSuspension e _ => e.WF
    | .assertReturn e rs => e.WF ∧ Val.listWF rs
    | .assertExhaustion i _ => i.WF
    | .thread _ _ ds => Directive.listWF ds
    | .wait _ => True

  def Directive.listWF : List Directive → Prop
    | [] => True
    | d :: ds => d.WF ∧ Directive.listWF ds
end

/-! ## Scripts -/

/-- A script: a list of directives, or (when the file does not start with a directive
keyword) a single module given by its fields (`wast`'s inline module). -/
inductive Script where
  | directives (ds : List Directive)
  | inline (fields : List SExp)
  deriving Repr, Inhabited

/-- `WastDirectiveToken`: the keywords that make a file a list of directives. -/
def directiveStart : SExp → Bool
  | .cons (.atom (.sym k)) _ =>
    k.toList.take 7 == "assert_".toList || k == "module" || k == "component" || k == "register" ||
      k == "invoke"
  | _ => false

/-- Well-formed scripts: a directive list starts with a directive keyword `wast` recognizes
(not `thread` or `wait`) and is not empty; an inline module does not. -/
def Script.WF : Script → Prop
  | .directives [] => False
  | .directives (d :: ds) => d.kw ≠ "thread" ∧ d.kw ≠ "wait" ∧ Directive.listWF (d :: ds)
  | .inline [] => True
  | .inline (x :: _) => directiveStart x = false

def Script.toSExps : Script → List SExp
  | .directives ds => Directive.listToSExps ds
  | .inline xs => xs

/-- Read a script: directives when the first element starts with a directive keyword. -/
def Script.ofSExps? (xs : List SExp) : Option Script :=
  match xs with
  | x :: _ => if directiveStart x then (Directive.listOf? xs).map .directives
    else some (.inline xs)
  | [] => some (.inline [])

end Silmaril.Wasm.Tools.Wast
