module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Tools.Component.Wat.Defs
public import Silmaril.Wasm.Wit.Binary.NameSec.Defs
public import Silmaril.Wasm.Wit.Binary.Custom.Defs

/-!
# `wasm-tools print` in wasmprinter's layout

`Wat.print` writes component WAT with `Sexp.pp`'s layout (a list on one line when it fits in
100 columns). wasmprinter 1.262.0 (`crates/wasmprinter/src/{lib,component}.rs`) writes the
same tokens (checked on the test suites: after removing comments and identifiers the token
streams agree) with a different layout:

* every item of a component, of an instance or component type and of a core module type
  starts a new line, indented by two spaces per open parenthesis (at most 50 levels,
  `MAX_NESTING_TO_PRINT`); so do the arguments of `instantiate` and the exports of an
  instance built from exports; the body of an instance, component or module type starts on a
  new line after `(type (;i;)`;
* a list whose text spans several lines ends with `)` on its own line, indented to the list's
  level (wasmprinter's `end_group`);
* every definition carries its index as a block comment `(;i;)`, at the place
  wasmprinter's `print_name` writes it: after `type`, `core type`, `core module`,
  `core instance`, `instance`, `component`, `func` (a `canon lift`), `core func`, `export`
  (of a component, instance type or component type), inside the kind of an import
  (`(func (;i;) (type 0))`), of an alias (`(func (;i;))`) and of a `start` result, and on
  every type of a `rec` group; one counter per index space and per scope (component, instance
  type, component type, module type), as wasmprinter's `State`.

The layout is a function of the S-expression (`lay`, with the scopes' counters threaded
through `layScope`) to a laid-out tree `L` (the S-expression with line breaks and comments),
and `render` writes it; `renderF` writes it into a `String` accumulator (the fast path, equal
to `render` by `Layout.Thms.renderF_eq`). `Layout.Thms` proves that the layout keeps the
tokens (`tk_lay`) and that the lexer reads the rendered text as those tokens (`lex_render`),
so `Wat.read (printW c) = some (Wat.norm c)` (`read_printW`).

Not wasmprinter's: `$name`s from the `component-name` section (indices are printed; the
section itself is printed as `(@custom "component-name" …)`), core modules (printed as
`(core module (;i;) binary "…")`; the core printer belongs to the wasm-tools-core
workflow), `(@producers …)` and other known custom sections (printed as `(@custom …)`), and
strings with non-ASCII characters (`\hh` bytes instead of `\u{…}`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Layout

open Silmaril.Wasm.Component.Wat (Sexp Tok)

/-! ## Laid-out trees -/

/-- A laid-out S-expression: atoms, strings, index comments and lists whose items carry a
line-break flag (a new line before the item). -/
inductive L where
  | atom (s : String)
  | str (bs : List UInt8)
  | cmt (n : Nat)
  | list (xs : List (Bool × L))
  deriving Repr, Inhabited

/-! ## Scopes and counters -/

/-- The kind of a sequence of items. -/
inductive Scope where
  | comp
  | itype
  | ctype
  | mtype
  deriving Repr, DecidableEq

/-- The index counters of a scope, by index space (`func`, `core func`, `type`, …). -/
abbrev St := List (String × Nat)

/-- The next index of a space. -/
def St.get (st : St) (k : String) : Nat := (st.lookup k).getD 0

/-- Count `n` new indices of a space. -/
def St.bump (st : St) (k : String) (n : Nat := 1) : St := (k, st.get k + n) :: st

/-- The index space and the number of keyword atoms at the head of a list
(`(core func …)`: `core func`, 2; `(func …)`: `func`, 1). -/
def kindKey : List Sexp → Option (String × Nat)
  | .atom "core" :: .atom b :: _ => some ("core " ++ b, 2)
  | .atom a :: _ => some (a, 1)
  | _ => none

/-- The kind key of a list. -/
def kindOf : Sexp → Option (String × Nat)
  | .list xs => kindKey xs
  | _ => none

/-- Name attributes, which come between a name and the kind in imports and exports. -/
def isAttr (s : Sexp) : Bool :=
  match kindOf s with
  | some (k, _) => k == "implements" || k == "version-suffix" || k == "external-id"
  | none => false

/-- The first list child that is not an attribute (the kind of an export or import). -/
def descOf : List Sexp → Option Sexp
  | [] => none
  | x@(.list _) :: xs => if isAttr x then descOf xs else some x
  | _ :: xs => descOf xs

/-- The number of items of a list. -/
def lenOf : Sexp → Nat
  | .list xs => xs.length
  | _ => 0

/-! ## Names

wasmprinter prints the names of the `component-name` section (`register_component_names`,
`Naming::new`): a definition gets `$name` before its `(;i;)` comment, a reference `$name`
instead of its index. A name of `idchar`s is `$name`; another non-empty name not starting
with `#` is `$"name"` (`print_str_contents`: `\u{…}` escapes); an empty name, a name
starting with `#`, or one already used in its index space is synthetic, `$"#sort<i> name"`,
followed at the definition by `(@name "name")`. The `component-name` section itself is not
printed. Names apply in components only (type declarations have their own, unnamed,
scopes); `alias outer` names the outer component. -/

/-- Our index-space key of a name-section sort. -/
def sortKey : Silmaril.Wasm.Component.Binary.ItemSort → String
  | .core .func => "core func"
  | .core .table => "core table"
  | .core .memory => "core memory"
  | .core .global => "core global"
  | .core .tag => "core tag"
  | .core .type => "core type"
  | .core .module => "core module"
  | .core .instance => "core instance"
  | .func => "func"
  | .value => "value"
  | .type => "type"
  | .component => "component"
  | .instance => "instance"

/-- wasmprinter's group word of an index space (`#func0`, `#core-type1`, …). -/
def groupWord (k : String) : String := (k.toList.map fun c => if c == ' ' then '-' else c) |> String.ofList

/-- The names of one scope: the component's own name and the names by index space. -/
structure Names where
  comp : Option String := none
  maps : List (String × List (Nat × String)) := []
  deriving Repr, Inhabited

/-- The names of a `component-name` section's contents (none when it does not parse).
Core module and core tag names are left out: core modules are printed in binary form here
(never as wasmprinter does), and `Wac.WatX` reads neither a named `(core module $m binary …)`
nor tag names, so the text keeps their indices and `parse` reads it back. -/
def namesOf (data : List UInt8) : Names :=
  match Silmaril.Wasm.Wit.Binary.parseNameSec ⟨data.toArray⟩ with
  | .ok subs => subs.foldl (fun n s => match s with
      | .component c => { n with comp := some c }
      | .sort srt ns =>
        if sortKey srt == "core module" || sortKey srt == "core tag" then n
        else { n with maps := (sortKey srt, ns) :: n.maps }) {}
  | .error _ => {}

/-- Is an item the `component-name` custom section? -/
def nameSecData? : Sexp → Option (List UInt8)
  | .list [.atom "@custom", .str n, .str d] =>
    if n == "component-name".toUTF8.toList then some d else none
  | _ => none

/-- The names of a component's items. -/
def namesIn (xs : List Sexp) : Names :=
  match xs.findSome? nameSecData? with
  | some d => namesOf d
  | none => {}

/-- `idchar` (the text format's identifier characters, as wasmprinter's `is_idchar`). -/
def idchar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-./:<=>?@\\^_`|~".toList.contains c

/-- `print_str_contents`. -/
def strContents (s : String) : String :=
  String.join (s.toList.map fun c =>
    let v := c.toNat
    if 0x20 ≤ v && v < 0x7f && c != '"' && c != '\\' then String.singleton c
    else "\\u{" ++ String.ofList (Nat.toDigits 16 v) ++ "}")

/-- How a name is written: the identifier, and whether the definition needs `(@name …)`. -/
def nameText (k : String) (i : Nat) (ns : List (Nat × String)) (name : String) : String × Bool :=
  let dup := (ns.takeWhile (·.1 != i)).any (·.2 == name)
  if name.isEmpty || name.startsWith "#" || dup then
    ("$\"#" ++ groupWord k ++ toString i ++ " " ++ strContents name ++ "\"", true)
  else if name.toList.all idchar then ("$" ++ name, false)
  else ("$\"" ++ strContents name ++ "\"", false)

/-- The name of index `i` of space `k`, if any. -/
def Names.get? (n : Names) (k : String) (i : Nat) : Option (String × Bool) :=
  match n.maps.lookup k with
  | some ns => (ns.lookup i).map (nameText k i ns)
  | none => none

/-- The naming context: whether names are printed, and the names of the enclosing scopes,
innermost first. -/
structure Ctx where
  on : Bool := false
  scopes : List Names := []
  deriving Repr, Inhabited

/-- Enter a scope. -/
def Ctx.enter (E : Ctx) (n : Names) : Ctx := { E with scopes := n :: E.scopes }

/-- A reference: the name of index `a` of space `k` in the scope `up` levels out, or `a`. -/
def Ctx.ref (E : Ctx) (up : Nat) (k : String) (a : String) : String :=
  if E.on then
    match a.toNat?, E.scopes[up]? with
    | some i, some n => ((n.get? k i).map (·.1)).getD a
    | _, _ => a
  else a

/-- The binder items of a definition: `$name` (and `(@name "…")` for a synthetic name). -/
def Ctx.binder (E : Ctx) (k : String) (i : Nat) : List (Bool × L) :=
  if E.on then
    match E.scopes.head? >>= (·.get? k i) with
    | some (t, false) => [(false, .atom t)]
    | some (t, true) =>
      let raw := match E.scopes.head? >>= fun n => n.maps.lookup k >>= (·.lookup i) with
        | some r => r
        | none => ""
      [(false, .atom t), (false, .list [(false, .atom "@name"),
        (false, .atom ("\"" ++ strContents raw ++ "\""))])]
    | none => []
  else []

/-! ## Layout modes -/

/-- How to lay out a node.

* `plain`: as is, on one line (unless a child breaks);
* `item cmt brk child`: a comment `(;n;)` of index space `k` before the child at position
  `p` (`cmt = (p, k, n)`; `p` may be the length, at the end; with names, the definition's
  `$name` comes first), a line break before every child from position `brk` on, and the modes
  of the children by position;
* `scope k hd`: `hd` keyword atoms, then items of a scope `k` with fresh counters, each on a
  new line;
* `compDef n`: a nested component definition `(component (;n;) …)`;
* `recG hd n`: a `rec` group (`hd` keyword atoms) whose types are numbered from `n`;
* `ref up k`: an atom that is an index of space `k` in the scope `up` levels out;
* `outer`: the count of an `alias outer` (the outer component's name, if any);
* `vt`: a value type (numbers are type indices). -/
inductive Mode where
  | plain
  | item (cmt : Option (Nat × String × Nat)) (brk : Nat) (child : List (Nat × Mode))
  | scope (k : Scope) (hd : Nat)
  | compDef (n : Nat)
  | recG (hd : Nat) (n : Nat)
  | ref (up : Nat) (k : String)
  | outer
  | vt
  deriving Repr, Inhabited

/-- No line break. -/
def never : Nat := 1000000000

/-- A comment of space `k` at position `p`, no line breaks. -/
def mark (p : Nat) (k : String) (n : Nat) : Mode := .item (some (p, k, n)) never []

/-- The mode of a child by position. -/
def childMode (cs : List (Nat × Mode)) (i : Nat) : Mode := (cs.lookup i).getD .plain

/-- The scope of a type body (`(instance …)`, `(component …)`, `(module …)`). -/
def bodyScope (x : Sexp) : Option Scope :=
  match kindOf x with
  | some ("instance", _) => some .itype
  | some ("component", _) => some .ctype
  | some ("module", _) => some .mtype
  | _ => none

/-- The index space of a kind keyword in a core context (`func` of a core instance export is
a core function). -/
def coreKey (k : String) : String :=
  if k == "func" || k == "table" || k == "memory" || k == "global" || k == "tag" ||
    k == "type" || k == "module" || k == "instance" then "core " ++ k else k

/-- `(K N)`: the index `N` of space `K` (`core`: in a core context). -/
def kindRef (core : Bool) (x : Sexp) : Mode :=
  match kindOf x with
  | some (k, h) => .item none never [(h, .ref 0 (if core then coreKey k else k))]
  | none => .plain

/-- Modes of the children of a value type: numbers are type indices (but the length of a
fixed-length `list`), lists are value types. -/
def vtModes (xs : List Sexp) : List (Nat × Mode) :=
  let fixed := match xs with | [.atom "list", _, _] => true | _ => false
  (List.range xs.length).zip xs |>.filterMap fun (i, x) =>
    if i = 0 then none else
    match x with
    | .atom a => if (a.toNat?).isSome && !(fixed && i = 2) then some (i, .ref 0 "type") else none
    | .list _ => some (i, .vt)
    | _ => none

/-- Modes of canonical options and of the other children of a `canon` built-in. The core
type and table immediates of `thread.*` built-ins keep their indices (wasmprinter names them;
`Wac.WatX`'s resolver does not read names there, so `parse` could not read the text back). -/
def canonModes (xs : List Sexp) : List (Nat × Mode) :=
  let name := match xs with | _ :: .atom n :: _ => n | _ => ""
  let rec go : Nat → Nat → List Sexp → List (Nat × Mode)
    | _, _, [] => []
    | i, j, x :: rest =>
      match x with
      | .atom a =>
        if i < 2 || (a.toNat?).isNone then go (i + 1) j rest
        else if name == "context.get" || name == "context.set" then go (i + 1) j rest
        else if name.startsWith "thread." then go (i + 1) (j + 1) rest
        else (i, .ref 0 "type") :: go (i + 1) (j + 1) rest
      | .list _ =>
        let m := match kindOf x with
          | some ("memory", _) => .item none never [(1, .ref 0 "core memory")]
          | some ("realloc", _) | some ("post-return", _) | some ("callback", _) =>
            .item none never [(1, .ref 0 "core func")]
          | some ("core-type", _) => .item none never [(1, .ref 0 "core type")]
          | some ("result", _) => .vt
          | some ("func", _) => kindRef false x
          | some ("core func", _) => kindRef false x
          | _ => .plain
        (i, m) :: go (i + 1) j rest
      | _ => go (i + 1) j rest
  go 0 0 xs

/-- The mode of a type definition's body (`(func …)`, a value type, `(resource …)`). -/
def defMode (x : Sexp) : Mode :=
  match kindOf x with
  | some ("resource", _) =>
    match x with
    | .list xs => .item none never ((List.range xs.length).zip xs |>.filterMap fun (i, c) =>
        match kindOf c with
        | some ("dtor", _) => some (i, Mode.item none never [(1, .ref 0 "core func")])
        | _ => none)
    | _ => .plain
  | _ => .vt

/-- The mode of an extern descriptor `(func (type T))`, `(value VT)`, `(type (eq T))`, …,
with the binder comment at `cmt`. -/
def descMode (cmt : Option (Nat × String × Nat)) (x : Sexp) : Mode :=
  match x with
  | .list xs =>
    match kindKey xs with
    | some (k, h) =>
      let after := (List.range xs.length).zip xs |>.filterMap fun (i, c) =>
        if i < h then none else
        match kindOf c, c with
        | some ("type", _), _ => some (i, Mode.item none never [(1, .ref 0 "type")])
        | some ("core type", _), _ => some (i, Mode.item none never [(2, .ref 0 "core type")])
        | some ("eq", _), _ => some (i, Mode.item none never [(1, .ref 0 "type")])
        | _, .atom a => if k == "value" && (a.toNat?).isSome then some (i, .ref 0 "type") else none
        | _, .list _ => if k == "value" then some (i, .vt) else none
        | _, _ => none
      .item cmt never after
    | none => .plain
  | _ => .plain

/-- The counters of the results of `start`: the `(result (value))` children get the value
indices from `n` on; `(value V)` arguments are value references. -/
def startModes : Nat → Nat → List Sexp → List (Nat × Mode)
  | _, _, [] => []
  | i, n, x :: xs =>
    match kindOf x with
    | some ("result", _) =>
      (i, .item none never [(1, mark 1 "value" n)]) :: startModes (i + 1) (n + 1) xs
    | some ("value", _) => (i, kindRef false x) :: startModes (i + 1) n xs
    | _ =>
      match x with
      | .atom a => if i = 1 && (a.toNat?).isSome then (i, .ref 0 "func") :: startModes (i + 1) n xs
        else startModes (i + 1) n xs
      | _ => startModes (i + 1) n xs

/-- The number of `(result …)` children. -/
def countResults (xs : List Sexp) : Nat :=
  (xs.filter fun x => match kindOf x with | some ("result", _) => true | _ => false).length

/-- Modes of `instantiate`'s children: the instantiated module or component, the `with`
arguments (each on a new line). -/
def instMode (core : Bool) (x : Sexp) : Mode :=
  match x with
  | .list xs =>
    let args := (List.range xs.length).zip xs |>.filterMap fun (i, c) =>
      if i < 2 then none else
      match c with
      | .list ys => some (i, Mode.item none never [(ys.length - 1, kindRef core (ys.getLastD c))])
      | _ => none
    .item none 2 ((1, .ref 0 (if core then "core module" else "component")) :: args)
  | _ => .plain

/-- The positions of an export's kind and ascription (after the name and attributes). -/
def exportModes (core : Bool) (xs : List Sexp) : List (Nat × Mode) :=
  let rec go : Nat → Bool → List Sexp → List (Nat × Mode)
    | _, _, [] => []
    | i, seen, x :: rest =>
      match x with
      | .list _ =>
        if isAttr x then go (i + 1) seen rest
        else if !seen then (i, kindRef core x) :: go (i + 1) true rest
        else (i, descMode none x) :: go (i + 1) true rest
      | _ => go (i + 1) seen rest
  go 0 false xs

/-- Exports of a bag-of-exports instance: each on a new line, with its references. -/
def bagModes (core : Bool) (from_ : Nat) (xs : List Sexp) : List (Nat × Mode) :=
  (List.range xs.length).zip xs |>.filterMap fun (i, c) =>
    if i < from_ then none else
    match c with
    | .list ys => some (i, Mode.item none never (exportModes core ys))
    | _ => none

/-- **The plan of one item** of a scope `k` with counters `st`: its mode and the counters
after it (wasmprinter's `print_*` functions, `component.rs`). -/
def plan (k : Scope) (st : St) (x : Sexp) : Mode × St :=
  match x with
  | .list xs =>
    match kindKey xs with
    | some ("type", _) =>
      let n := st.get "type"
      let key := if k == .mtype then "core type" else "type"
      match xs[1]? with
      | some d =>
        match bodyScope d with
        | some s => (.item (some (1, key, n)) 1 [(1, Mode.scope s 1)], st.bump "type")
        | none => (.item (some (1, key, n)) never [(1, defMode d)], st.bump "type")
      | none => (.item (some (1, key, n)) never [], st.bump "type")
    | some ("core type", _) =>
      let n := st.get "core type"
      let body := match xs[2]? >>= bodyScope with
        | some .mtype => [(2, Mode.scope .mtype 1)]
        | _ => []
      (.item (some (2, "core type", n)) (if body.isEmpty then never else 2) body,
        st.bump "core type")
    | some ("core rec", _) =>
      let n := st.get "core type"
      (.recG 2 n, st.bump "core type" (xs.length - 2))
    | some ("rec", _) =>
      let n := st.get "type"
      (.recG 1 n, st.bump "type" (xs.length - 1))
    | some ("import", _) =>
      if k == .mtype then (.plain, st) else
      match xs.getLast? with
      | some d =>
        match kindOf d with
        | some (s, h) =>
          (.item none never [(xs.length - 1, descMode (some (h, s, st.get s)) d)], st.bump s)
        | none => (.plain, st)
      | none => (.plain, st)
    | some ("export", _) =>
      if k == .mtype then (.plain, st) else
      match descOf (xs.drop 2) >>= kindOf with
      | some (s, _) =>
        let cs := if k == .comp then exportModes false xs
          else (exportModes false xs).map fun (i, _) => (i, descMode none (xs.getD i (.atom "")))
        (.item (some (1, s, st.get s)) never cs, st.bump s)
      | none => (.plain, st)
    | some ("core module", _) =>
      (mark 2 "core module" (st.get "core module"), st.bump "core module")
    | some ("core instance", _) =>
      let n := st.get "core instance"
      match xs[2]? with
      | some d =>
        match kindOf d with
        | some ("instantiate", _) =>
          (.item (some (2, "core instance", n)) never [(2, instMode true d)],
            st.bump "core instance")
        | _ => (.item (some (2, "core instance", n)) 2 (bagModes true 2 xs),
            st.bump "core instance")
      | none => (.item (some (2, "core instance", n)) 2 [], st.bump "core instance")
    | some ("instance", _) =>
      let n := st.get "instance"
      match xs[1]? with
      | some d =>
        match kindOf d with
        | some ("instantiate", _) =>
          (.item (some (1, "instance", n)) never [(1, instMode false d)], st.bump "instance")
        | _ => (.item (some (1, "instance", n)) 1 (bagModes false 1 xs), st.bump "instance")
      | none => (.item (some (1, "instance", n)) 1 [], st.bump "instance")
    | some ("component", _) =>
      if k == .comp then (.compDef (st.get "component"), st.bump "component") else (.plain, st)
    | some ("alias", _) =>
      match xs.getLast? with
      | some d =>
        match kindOf d with
        | some (s, h) =>
          let refs : List (Nat × Mode) := match xs with
            | _ :: .atom "export" :: _ => [(2, .ref 0 "instance")]
            | _ :: .atom "core" :: .atom "export" :: _ => [(3, .ref 0 "core instance")]
            -- `alias outer C N`: wasmprinter names `C` (the outer component) and `N`;
            -- `Wac.WatX` resolves neither, so both stay numbers (`Mode.outer`, `ref` unused).
            | _ => []
          (.item none never ((xs.length - 1, mark h s (st.get s)) :: refs), st.bump s)
        | none => (.plain, st)
      | none => (.plain, st)
    | some ("func", _) =>
      (.item (some (1, "func", st.get "func")) never
        [(1, .item none never [(1, .ref 0 "type")]),
         (2, .item none never (canonModes ((xs.getD 2 (.atom "")) |> fun c =>
            match c with | .list ys => ys | _ => [])))],
        st.bump "func")
    | some ("core func", _) =>
      (.item (some (2, "core func", st.get "core func")) never
        [(2, match xs.getD 2 (.atom "") with
          | .list ys => .item none never (canonModes ys)
          | _ => .plain)], st.bump "core func")
    | some ("value", _) => (mark 1 "value" (st.get "value"), st.bump "value")
    | some ("start", _) =>
      let n := st.get "value"
      (.item none never (startModes 0 n xs), st.bump "value" (countResults xs))
    | _ => (.plain, st)
  | _ => (.plain, st)

/-! ## The layout -/

/-- The comment item at position `i`, if any, after the definition's name. -/
def cmtAt (E : Ctx) (cmt : Option (Nat × String × Nat)) (i : Nat) : List (Bool × L) :=
  match cmt with
  | some (p, k, n) => if p = i then E.binder k n ++ [(false, .cmt n)] else []
  | none => []

/-- With names on, the `component-name` section is not printed. -/
def skipItem (E : Ctx) (x : Sexp) : Bool := E.on && (nameSecData? x).isSome

/-- With names on (the presentation layer), the `producers` section as wasmprinter prints it
(`print_producers_section`): `(@producers (FIELD "name" "version")…)`, one value per line;
`Wat.R` reads this form back into the section. Only for field names of `idchar`s. -/
def prodItem (E : Ctx) (x : Sexp) : Option L :=
  if !E.on then none else
  match x with
  | .list [.atom "@custom", .str n, .str d] =>
    if n != "producers".toUTF8.toList then none else
    match Silmaril.Wasm.Wit.Binary.Producers.parse ⟨d.toArray⟩ with
    | .ok p =>
      if p.all (fun f => !f.1.isEmpty && f.1.toList.all idchar) then
        some (.list ((false, .atom "@producers") :: p.flatMap fun (f, vs) =>
          vs.map fun (nm, ver) =>
            (true, .list [(false, .atom f), (false, .str nm.toUTF8.toList),
              (false, .str ver.toUTF8.toList)])))
      else none
    | .error _ => none
  | _ => none

mutual
/-- Lay out an S-expression in a mode. -/
def lay (E : Ctx) : Mode → Sexp → L
  | .ref up k, .atom a => .atom (E.ref up k a)
  | .outer, .atom a =>
    if E.on then
      match a.toNat? >>= fun c => E.scopes[c]? >>= (·.comp) with
      | some n => .atom ((nameText "component" 0 [] n).1)
      | none => .atom a
    else .atom a
  | _, .atom a => .atom a
  | _, .str b => .str b
  | .plain, .list xs => .list (layIdx E none never [] 0 xs)
  | .item cmt brk cs, .list xs => .list (layIdx E cmt brk cs 0 xs)
  | .scope k hd, .list xs => .list (layHead (E.enter {}) k hd xs)
  | .compDef n, .list xs => .list (layHeadC E n xs)
  | .recG hd n, .list xs => .list (layRec E hd n 0 xs)
  | .ref _ _, .list xs => .list (layIdx E none never [] 0 xs)
  | .outer, .list xs => .list (layIdx E none never [] 0 xs)
  | .vt, .list xs => .list (layIdx E none never (vtModes xs) 0 xs)

/-- Children by position: the comment, line breaks from `brk`, the children's modes. -/
def layIdx (E : Ctx) (cmt : Option (Nat × String × Nat)) (brk : Nat) (cs : List (Nat × Mode))
    (i : Nat) : List Sexp → List (Bool × L)
  | [] => cmtAt E cmt i
  | x :: xs =>
    cmtAt E cmt i ++ (decide (brk ≤ i), lay E (childMode cs i) x) :: layIdx E cmt brk cs (i + 1) xs

/-- `hd` head atoms on the first line, then the items of a scope `k` with fresh counters
(the scope's names: none in type declarations). -/
def layHead (E : Ctx) (k : Scope) : Nat → List Sexp → List (Bool × L)
  | _, [] => []
  | 0, x :: xs =>
    let p := plan k [] x
    (true, lay E p.1 x) :: layScope E k p.2 xs
  | hd + 1, x :: xs => (false, lay E .plain x) :: layHead E k hd xs

/-- Items of a scope `k` with counters `st`, each on a new line. -/
def layScope (E : Ctx) (k : Scope) (st : St) : List Sexp → List (Bool × L)
  | [] => []
  | x :: xs =>
    if skipItem E x then layScope E k st xs else
    match prodItem E x with
    | some l => (true, l) :: layScope E k st xs
    | none =>
      let p := plan k st x
      (true, lay E p.1 x) :: layScope E k p.2 xs

/-- A nested component definition: `component`, its name and comment, its items (in a new
naming scope). -/
def layHeadC (E : Ctx) (n : Nat) : List Sexp → List (Bool × L)
  | [] => []
  | x :: xs =>
    (false, lay E .plain x) :: (E.binder "component" n ++
      (false, .cmt n) :: layScope (E.enter (namesIn xs)) .comp [] xs)

/-- A `rec` group: `hd` keyword atoms, then each type on a new line with its comment. -/
def layRec (E : Ctx) (hd n i : Nat) : List Sexp → List (Bool × L)
  | [] => []
  | x :: xs =>
    if i < hd then (false, lay E .plain x) :: layRec E hd n (i + 1) xs
    else (true, lay E (mark 1 "core type" (n + (i - hd))) x) :: layRec E hd n (i + 1) xs
end

/-! ## Rendering -/

/-- The decimal digits of `n`. -/
def digits (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (48 + n)] else digits (n / 10) ++ [Char.ofNat (48 + n % 10)]
termination_by n
decreasing_by omega

/-- A new line indented for nesting level `d` (two spaces per level, at most 50 levels). -/
def nl (d : Nat) : List Char := '\n' :: Sexp.spaces (2 * min d 50)

mutual
/-- **The text of a laid-out tree** at nesting level `d` (the number of open lists). -/
def render (d : Nat) : L → List Char
  | .atom a => a.toList
  | .str b => Sexp.quote b
  | .cmt n => '(' :: ';' :: (digits n ++ [';', ')'])
  | .list xs =>
    let body := renderItems (d + 1) true xs
    '(' :: (body ++ ((if body.contains '\n' then nl d else []) ++ [')']))

/-- The items of a list (`first`: no separator before the first item). -/
def renderItems (d : Nat) (first : Bool) : List (Bool × L) → List Char
  | [] => []
  | (b, x) :: xs =>
    (if first then [] else if b then nl d else [' ']) ++ (render d x ++ renderItems d false xs)
end

/-! ## The fast path -/

/-- `n` spaces onto a string. -/
def spacesF (acc : String) : Nat → String
  | 0 => acc
  | n + 1 => spacesF (acc.push ' ') n

/-- `nl d` onto a string. -/
def nlF (acc : String) (d : Nat) : String := spacesF (acc.push '\n') (2 * min d 50)

/-- A string literal's bytes onto a string (`Sexp.escByte`). -/
def escF (acc : String) (b : UInt8) : String :=
  if 0x20 ≤ b.toNat ∧ b.toNat < 0x7f ∧ b.toNat ≠ 0x22 ∧ b.toNat ≠ 0x5c then
    acc.push (Char.ofNat b.toNat)
  else ((acc.push '\\').push (Sexp.hexDigit (b.toNat / 16))).push (Sexp.hexDigit (b.toNat % 16))

/-- A string literal onto a string. -/
def quoteF (acc : String) (bs : List UInt8) : String :=
  (bs.foldl escF (acc.push '"')).push '"'

mutual
/-- **The fast renderer**: `render d l` appended to `acc`, and whether it contains a new
line (`renderF_eq`). -/
def renderF (d : Nat) (acc : String) : L → String × Bool
  | .atom a => (acc ++ a, false)
  | .str b => (quoteF acc b, false)
  | .cmt n => ((acc ++ String.ofList ('(' :: ';' :: digits n)).push ';' |>.push ')', false)
  | .list xs =>
    let (s, nlIn) := renderItemsF (d + 1) true (acc.push '(') xs
    ((if nlIn then nlF s d else s).push ')', nlIn)

/-- The items of a list onto a string, and whether they contain a new line. -/
def renderItemsF (d : Nat) (first : Bool) (acc : String) : List (Bool × L) → String × Bool
  | [] => (acc, false)
  | (b, x) :: xs =>
    let acc1 := if first then acc else if b then nlF acc d else acc.push ' '
    let (acc2, n2) := renderF d acc1 x
    let (acc3, n3) := renderItemsF d false acc2 xs
    (acc3, (!first && b) || n2 || n3)
end

/-! ## Entry points -/

/-- The laid-out tree of a component, without names (the verified layout). -/
def layComponent (c : Silmaril.Wasm.Component.BinaryP3.Ast) : L := lay {} (.scope .comp 1) (Wat.toSexp c)

/-- The top-level scope with names: the component's own name after `component`, and its
`component-name` section dropped. -/
def layNamed : Sexp → L
  | .list (x :: xs) =>
    let N := namesIn xs
    let E : Ctx := { on := true, scopes := [N] }
    let nm : List (Bool × L) := match N.comp with
      | some c => [(false, .atom (nameText "component" 0 [] c).1)]
      | none => []
    .list ((false, lay E .plain x) :: nm ++ layScope E .comp [] xs)
  | s => lay {} .plain s

/-- **`wasm-tools print`** of a component in wasmprinter's layout, with names (the text the
tool writes). -/
def printWN (c : Silmaril.Wasm.Component.BinaryP3.Ast) : String :=
  (renderF 0 "" (layNamed (Wat.toSexp c))).1.push '\n'


/-- **`wasm-tools print`** of a component in wasmprinter's layout (with the final newline). -/
def printW (c : Silmaril.Wasm.Component.BinaryP3.Ast) : String := (renderF 0 "" (layComponent c)).1.push '\n'

/-- The specification text: `render`'s characters. -/
def printWSpec (c : Silmaril.Wasm.Component.BinaryP3.Ast) : String := String.ofList (render 0 (layComponent c) ++ ['\n'])

/-- wasmparser's reader limits on `start` (`MAX_WASM_START_ARGS`,
`MAX_WASM_FUNCTION_RETURNS`: 1000 each), which `BinaryP3` does not have: the first
violation, as wasmparser words it. -/
partial def startLimit : Silmaril.Wasm.Component.BinaryP3.Ast → Option String
  | .mk ss => ss.findSome? fun
    | .start st =>
      if st.args.length > 1000 then some "start function arguments size is out of bounds"
      else if st.results > 1000 then some "start function results size is out of bounds"
      else none
    | .component c => startLimit c
    | _ => none

/-- `wasm-tools print` on a component binary. -/
def printBytesW (b : ByteArray) : Except String String :=
  match Silmaril.Wasm.Component.Codec.decodeLax b with
  | .ok c =>
    match startLimit c with
    | some e => .error e
    | none => .ok (printWN c)
  | .error e => .error s!"failed to parse component: {repr e}"

end Silmaril.Wasm.Tools.Component.Layout
