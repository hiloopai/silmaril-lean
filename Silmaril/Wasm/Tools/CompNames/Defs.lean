module

public import Silmaril.Wasm.Tools.Features.Defs

/-!
# Component import and export names (wasmparser's `names.rs`)

A transcription of the name grammar wasmparser 1.262.0 enforces on component import and export
names (`crates/wasmparser/src/validator/names.rs`, `ComponentNameParser`):

```
name      ::= interfacename | plainname
plainname ::= ('[constructor]' | '[method]' kebab '.' | '[static]' kebab '.')?
              ('[get]' | '[set]')? kebab
interfacename ::= lkebab ':' lkebab (':' lkebab)* ('/' kebab)+ ('@' rest)?
kebab     ::= word ('-' word)*        word: [a-z][a-z0-9]* | [A-Z][A-Z0-9]* (digits not first
                                      in the first word)
```

(the repeated `:` and `/` only with `cm-nested-names`; `[get]`/`[set]` only with
`cm-accessors`), and the uniqueness key of a name (`ComponentNameKind`'s `Ord`): plain names
compare lowercased with hyphens removed, `[x]a.a` as `a`, keeping only the `[constructor]` and
`[set]` annotations; interface names compare by their components (lowercased, hyphens
removed) and the raw version string.

This is a tested transcription (`tools/wasm-tools/tests/comp-diff.sh`), not a theorem.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.CompNames

open Silmaril.Wasm.Tools.Features

/-- `KebabStr::is_kebab_case`, as a state machine over the characters. -/
def isKebabAux : List Char → Bool → Bool → Bool → Bool → Bool
  | [], _, _, _, _ => true
  | c :: cs, lower, upper, first, digit =>
    if 'a' ≤ c && c ≤ 'z' && !lower && !upper then isKebabAux cs true false first digit
    else if 'A' ≤ c && c ≤ 'Z' && !lower && !upper then isKebabAux cs false true first digit
    else if '0' ≤ c && c ≤ '9' && !lower && !upper && !first then
      isKebabAux cs lower upper first true
    else if 'a' ≤ c && c ≤ 'z' && lower then isKebabAux cs lower upper first digit
    else if 'A' ≤ c && c ≤ 'Z' && upper then isKebabAux cs lower upper first digit
    else if '0' ≤ c && c ≤ '9' && (lower || upper) then isKebabAux cs lower upper first true
    else if c = '-' && (lower || upper || digit) then isKebabAux cs false false false false
    else false

/-- `KebabStr::new`: non-empty, kebab case, not ending in `-`. -/
def isKebab (s : String) : Bool :=
  !s.isEmpty && isKebabAux s.toList false false true false && !s.endsWith "-"

/-- The canonical characters of a kebab string: lowercased, hyphens removed. -/
def canonChars (s : String) : String :=
  String.ofList ((s.toList.filter (· ≠ '-')).map Char.toLower)

/-- Strip a prefix. -/
def eatStr (pre s : String) : Option String :=
  if s.startsWith pre then some (s.drop pre.length).toString else none

/-- The longest prefix of kebab characters, and the rest. -/
def spanKebab (s : String) : String × String :=
  let cs := s.toList
  let k := cs.takeWhile fun c => c.isAlphanum || c = '-'
  (String.ofList k, String.ofList (cs.drop k.length))

/-- `take_kebab`. -/
def takeKebab (s : String) : Except String (String × String) :=
  let (k, r) := spanKebab s
  if isKebab k then .ok (k, r) else .error s!"`{k}` is not in kebab case"

/-- `take_lowercase_kebab`. -/
def takeLowerKebab (s : String) : Except String (String × String) := do
  let (k, r) ← takeKebab s
  match k.toList.find? (fun c => c.isAlpha && !c.isLower) with
  | some c => .error s!"character `{c}` is not lowercase in package name/namespace"
  | none => .ok (k, r)

/-- `expect_str`. -/
def expectStr (pre s : String) : Except String String :=
  match eatStr pre s with
  | some r => .ok r
  | none => .error s!"expected `{pre}` at `{s}`"

/-- Repeat `p` while the input starts with `sep` (at most `fuel` times). -/
def manySep (fuel : Nat) (sep : String) (p : String → Except String (String × String))
    (s : String) : Except String String :=
  match fuel with
  | 0 => .ok s
  | f + 1 =>
    if s.startsWith sep then do
      let s ← expectStr sep s
      let (_, r) ← p s
      manySep f sep p r
    else .ok s

/-- The kind of a parsed name. -/
inductive NameKind where
  | plain
  | interface
  deriving Repr, DecidableEq

/-- `ComponentNameParser::parse` and the trailing check of `ComponentName::new_with_features`. -/
def parseName (F : WFeatures) (n : String) : Except String NameKind := do
  let nested := F.hasFlag "cm-nested-names"
  if n.contains ':' then
    -- interface name
    let (_, r) ← takeLowerKebab n
    let r ← expectStr ":" r
    let (_, r) ← takeLowerKebab r
    let r ← if nested then manySep r.length ":" takeLowerKebab r else pure r
    if !r.startsWith "/" then throw "expected `/` after package name"
    let r ← expectStr "/" r
    let (_, r) ← takeKebab r
    let r ← if nested then manySep r.length "/" takeKebab r else pure r
    let r := if r.startsWith "@" then "" else r
    if !r.isEmpty then throw s!"trailing characters found: `{r}`"
    return .interface
  let (rk, s) : Option Nat × String :=
    match eatStr "[constructor]" n with
    | some r => (some 0, r)
    | none => match eatStr "[method]" n with
      | some r => (some 1, r)
      | none => match eatStr "[static]" n with
        | some r => (some 2, r)
        | none => (none, n)
  let (acc, s) : Option Nat × String :=
    match eatStr "[get]" s with
    | some r => (some 0, r)
    | none => match eatStr "[set]" s with
      | some r => (some 1, r)
      | none => (none, s)
  if acc.isSome && !F.hasFlag "cm-accessors" then
    throw "`[get]` and `[set]` names require the component model accessors feature"
  let s ← match rk with
    | some 0 =>
      if acc.isSome then throw "names with [constructor] cannot contain [get] or [set]"
      pure s
    | some _ =>
      match s.splitOn "." with
      | [] | [_] => throw "failed to find `.` character"
      | res :: rest =>
        if !isKebab res then throw s!"`{res}` is not in kebab case"
        pure (String.intercalate "." rest)
    | none => pure s
  if !isKebab s then throw s!"`{s}` is not in kebab case"
  return .plain

/-- **The uniqueness key of a name** (`ComponentNameKind`'s ordering). -/
def nameKey (n : String) : String :=
  if n.contains ':' then
    match n.splitOn "@" with
    | [base, ver] => "I" ++ canonChars base ++ "@" ++ ver
    | _ => "I" ++ canonChars n
  else
    let (keep, s) : String × String :=
      match eatStr "[constructor]" n with
      | some r => ("[constructor]", r)
      | none => match eatStr "[method]" n with
        | some r => ("", r)
        | none => match eatStr "[static]" n with
          | some r => ("", r)
          | none => ("", n)
    let (keep, s) : String × String :=
      match eatStr "[get]" s with
      | some r => (keep, r)
      | none => match eatStr "[set]" s with
        | some r => (keep ++ "[set]", r)
        | none => (keep, s)
    let lower := canonChars s
    match lower.splitOn "." with
    | [a, b] => if a == b then "P" ++ a else "P" ++ keep ++ lower
    | _ => "P" ++ keep ++ lower

end Silmaril.Wasm.Tools.CompNames
