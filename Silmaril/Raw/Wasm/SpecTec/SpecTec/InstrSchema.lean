module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast
public import Silmaril.Raw.Wasm.SpecTec.Basic

/-!
# Instruction constructor shapes, read from an imported script

`sil spectec` (`tools/sil/src/spectec.rs`) decodes the pinned wasm-3.0 stream
with the third-party Rust `spectec_ast` crate and writes
`Silmaril/Wasm/SpecTec/Generated.lean`.  The functions here recompute the same
shapes from a script imported by `Silmaril/SpecTec/Import.lean`, so the Lean
decoder and the Rust one can be checked against each other
(`spectec_crosscheck`, and `Silmaril/SpecTec/Specs.lean`).

The correspondence is exact up to the SHA-256 fingerprint, which `sil` takes
over the Rust decoder's `Debug` rendering of a whole case and which nothing in
Lean can reproduce; `sil spectec --check` is what pins that.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

open Silmaril.Wasm.SpecTecEnc (FieldType)

/-- `bound.iter().rposition(|name| name == id)` (`tools/sil/src/spectec.rs:135`):
the index of the *last* earlier field named `id`. -/
def rposition (bound : List Id) (x : Id) : Option Nat :=
  (bound.reverse.findIdx? (· == x)).map fun k => bound.length - 1 - k

/-- `field_type` (`tools/sil/src/spectec.rs:118`): the shape of one payload
field, with references to earlier fields resolved to their positions. -/
def fieldType? (bound : List Id) : Typ → Option FieldType
  | .varT "list" args =>
      -- `tools/sil/src/spectec.rs:119-122` guards on the *name* and then bails
      -- if the arguments are not exactly one type argument; `list` applied to
      -- anything else is an error, not an ordinary dependent family.
      match args with
      | [.typA t] => (fieldType? bound t).map .namedList
      | _ => none
  | .varT x args => do
      let ps ← args.mapM fun a =>
        match a with
        | .expA (.varE y) => rposition bound y
        | _ => none
      pure (.named x ps)
  | .iterT t .opt => (fieldType? bound t).map .optional
  | .iterT t .list => (fieldType? bound t).map .sequence
  | _ => none

/-- The payload fields of a tuple type, threading the names bound so far. -/
def tupFields? : List TypBind → List Id → Option (List FieldType)
  | [], _ => some []
  | .mk x t :: bs, bound => do
      let f ← fieldType? bound t
      let fs ← tupFields? bs (bound ++ [x])
      pure (f :: fs)

/-- `fields` (`tools/sil/src/spectec.rs:156`). -/
def fieldsOf? : Typ → Option (List FieldType)
  | .tupT binds => tupFields? binds []
  | t => (fieldType? [] t).map ([·])

/-- The cases of every `typ "instr"` declaration of a definition list, looking
inside recursive groups: `visit` (`tools/sil/src/spectec.rs:87-108`).

A declaration named `instr` whose shape is not the expected one makes the
whole collection fail, exactly as the Rust's `bail!`s abort `instruction_cases`
rather than skipping the declaration: it must have no type parameters and
exactly one instance (`spectec.rs:92-94`), that instance must have no
quantifiers and no arguments (`spectec.rs:96-98`), and its `deftyp` must be a
variant (`spectec.rs:99-101`). -/
def instrDecls? : List Def → Option (List (List TypCase))
  | [] => some []
  | .recD ds :: rest => do
      let inner ← instrDecls? ds
      let outer ← instrDecls? rest
      pure (inner ++ outer)
  | .typD "instr" ps insts :: rest => do
      let cases ← match ps, insts with
        | [], [.instD [] [] (.variantT cases)] => some cases
        | _, _ => none
      let outer ← instrDecls? rest
      pure (cases :: outer)
  | _ :: rest => instrDecls? rest

/-- The single `typ "instr"` declaration of a script: `instruction_cases`
(`tools/sil/src/spectec.rs:86-115`).  `none` unless the whole tree holds
exactly one well-shaped `instr` declaration (`spectec.rs:111-113`). -/
def instrCases? (s : Script) : Option (List TypCase) :=
  match instrDecls? s with
  | some [cases] => some cases
  | _ => none

/-- The constructor tag and payload shape of each instruction, in declaration
order: the pair that `Silmaril/Wasm/SpecTec/Generated.lean` records (minus the
fingerprint).  The order is *produced* but not *checked* —
`Silmaril/SpecTec/Crosscheck.lean` sorts both sides by tag before comparing,
because `sil spectec` splits the Rust side into `instructionSchemas` and
`administrativeSchemas`. -/
def instrSchemas? (s : Script) : Option (List (String × List FieldType)) := do
  let cases ← instrCases? s
  cases.mapM fun c =>
    match c with
    | .mk op t [] _ => (fieldsOf? t).map fun fs => (op, fs)
    | .mk _ _ (_ :: _) _ => none

/-! ## The shapes the Rust rejects

Each `example` below is one of `instruction_cases`'s and `field_type`'s
`bail!`s (`tools/sil/src/spectec.rs:86-154`).  `instrCases?` returns `none`
where the Rust aborts, rather than skipping the declaration and reporting a
later one. -/

/-- The expected shape: one plain `instr` variant declaration. -/
example :
    instrCases? [.typD "instr" [] [.instD [] [] (.variantT [])]] = some [] := by
  simp [instrCases?, instrDecls?]

/-- `visit` looks inside recursive groups (`tools/sil/src/spectec.rs:90`). -/
example :
    instrCases? [.recD [.typD "instr" [] [.instD [] [] (.variantT [])]]] = some [] := by
  simp [instrCases?, instrDecls?]

/-- "expected one instr declaration, found 0" (`tools/sil/src/spectec.rs:113`). -/
example : instrCases? [.typD "admininstr" [] [.instD [] [] (.variantT [])]] = none := by
  simp [instrCases?, instrDecls?]

/-- "expected one instr declaration, found 2" (`tools/sil/src/spectec.rs:113`):
a second declaration is an error, not something to skip past. -/
example :
    instrCases? [.typD "instr" [] [.instD [] [] (.variantT [])],
      .recD [.typD "instr" [] [.instD [] [] (.variantT [])]]] = none := by
  simp [instrCases?, instrDecls?]

/-- "instr changed its type parameters or instances"
(`tools/sil/src/spectec.rs:92-93`): type parameters. -/
example :
    instrCases? [.typD "instr" [.typP "x"] [.instD [] [] (.variantT [])]] = none := by
  simp [instrCases?, instrDecls?]

/-- "instr changed its type parameters or instances"
(`tools/sil/src/spectec.rs:92-93`): not exactly one instance. -/
example : instrCases? [.typD "instr" [] []] = none := by
  simp [instrCases?, instrDecls?]

/-- "instr instance unexpectedly parameterized"
(`tools/sil/src/spectec.rs:96-97`): the instance has quantifiers. -/
example :
    instrCases? [.typD "instr" [] [.instD [.typP "x"] [] (.variantT [])]] = none := by
  simp [instrCases?, instrDecls?]

/-- "instr instance unexpectedly parameterized"
(`tools/sil/src/spectec.rs:96-97`): the instance has arguments. -/
example :
    instrCases? [.typD "instr" [] [.instD [] [.typA .boolT] (.variantT [])]] = none := by
  simp [instrCases?, instrDecls?]

/-- "instr is not a variant" (`tools/sil/src/spectec.rs:99-100`). -/
example :
    instrCases? [.typD "instr" [] [.instD [] [] (.aliasT .boolT)]] = none := by
  simp [instrCases?, instrDecls?]

/-- "unexpected list type arguments" (`tools/sil/src/spectec.rs:120-121`): no
argument.  The name alone selects the branch, so this is *not* read as a
dependent family named `list`. -/
example : fieldType? [] (.varT "list" []) = none := rfl

/-- "unexpected list type arguments" (`tools/sil/src/spectec.rs:120-121`): two
arguments. -/
example : fieldType? [] (.varT "list" [.typA .boolT, .typA .boolT]) = none := rfl

/-- "unexpected list type arguments" (`tools/sil/src/spectec.rs:120-121`): an
expression argument, which for any other name would be a family parameter. -/
example : fieldType? ["x"] (.varT "list" [.expA (.varE "x")]) = none := rfl

/-- One type argument is the accepted shape (`tools/sil/src/spectec.rs:123`). -/
example :
    fieldType? ["x"] (.varT "list" [.typA (.varT "y" [.expA (.varE "x")])])
      = some (.namedList (.named "y" [0])) := rfl

end Silmaril.SpecTec.IL
