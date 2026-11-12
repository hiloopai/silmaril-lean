module

public meta import Lean
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm20
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Wasm10
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
meta import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Re-checking the corrected specifications

Each corrected script is re-checked with the *scope, kind, arity, shape and
declaration* half of phase 2's well-formedness predicate, so a patch cannot
break the invariants that half expresses.  This file is that re-check.  The
command

```
spectec_revalidate Text6x.wasm30text6x
  by Text6x.text6x on Specs.wasm30 from "specs/spectec/wasm-3.0.ast"
  tying Text6x.applyErrata_text6x
```

rebuilds a corrected script at elaboration time and runs
`Silmaril/SpecTec/Sem/Valid.lean`'s checker over it, failing the build if any
definition is rejected.  All four corrected scripts are checked at the bottom:
`Binary51.wasm30binary51`, `Text6x.wasm30text6x`, `Wasm20.wasm20corrected` and
`Wasm10.wasm10corrected`.

## What is checked, and what is not

`Silmaril/SpecTec/Sem/Valid.lean` transcribes `spectec/src/il/valid.ml` only as
far as the judgments that survive the `--ast` erasure and need no type: scope
and kind resolution, argument/parameter arities, mixop and field-atom shape,
iterator well-formedness, and declaration uniqueness.  Its own "What is
deliberately left out" section says so.  Running it here therefore establishes
that every patched script still

* resolves every `VarT`/`CallE`/`RulePr`/`VarG` identifier and every expression
  variable,
* gives every call and every type use the declared number of arguments, with
  the parameter sorts agreeing constructor by constructor,
* uses only mixops and field atoms that some variant or record in the script
  declares,
* keeps `RecD` groups homogeneous and iterations non-vacuous, and
* declares every identifier exactly once.

**Typing proper is *not* checked.**  `checkExp` takes no expected type:
`equiv_typ`, `sub_typ` and the `as_*_typ` accessors (`valid.ml:68-123`) need
`Eval.reduce_typ` and a `Subst.t`, none of which is transcribed.  So an
erratum that replaced a sub-expression by a well-scoped one *of the wrong
type* would pass this re-check.  That is not a hypothetical class for the
§5.1 errata: `#654` changes `BuN(32)` to `BiN(32)` and with it the declared
type of the implicit production result from `uN(32)` to `iN(32)`
(`docs/projects/spectec-divergences.md`, "New findings, from writing the patches", item 2).
What rules that particular change in or out is the equivalence layer —
`Silmaril/SpecTec/Equiv/BinaryValues.lean` — not this file.

Two further checks `valid.ml` itself makes are unavailable rather than
omitted: `valid_atom`'s `Atom.def` note and `valid_typcase`'s mixop arity are
both erased by the printer.  `Sem/Valid.lean` documents both.

## The `meta import all` lines

`spectec_import` and `spectec_erratum` add their constants with
`Lean.addDecl`, which bypasses the `@[expose]` of the section they sit in, so
the *values* of `Specs.wasmNN` and of every `Erratum` are invisible to an
importing module without them.  The elaborator below reads exactly those
values back, so it needs each of the five modules at the `meta` phase.

## Why the script has to be rebuilt

`Sem.wellFormed` is far too expensive for the kernel on a script of this size —
`Silmaril/SpecTec/Sem/Valid.lean` says why, and runs the three *pinned* streams
in compiled code for the same reason.  The corrected scripts cannot simply be
`#eval`uated instead: `spectec_import` adds `Specs.wasmNN` and its definitions
with `Lean.addDecl`, which does not compile them, and the corrected scripts
are `noncomputable` on top of that.  So the value the checker sees is rebuilt
here, in compiled meta code, out of the same three ingredients the Lean
definition is made of:

1. the base script, re-read from the `--ast` file with `SExp.parseStream` and
   `IL.decodeScript?` — exactly what `spectec_import` does;
2. the `Erratum` constants, read back out of the environment with
   `Import.lean`'s `unqDef`, the same traversal `spectec_erratum` uses to
   check the term it emitted;
3. `IL.applyErrata`, which is the function the Lean definition is stated with.

Step 1 is cross-checked against the environment: the elaborator also reads
`Specs.wasmNN` back with `IL.erratumScript` and requires the two to agree
definition by definition through `IL.defS`.  So the script the checker runs on
is the one `applyErrata <errata> Specs.wasmNN` denotes, and the module's
`applyErrata_*` theorem — a `rfl` the kernel checks, named in the command's
`tying` clause and verified there to have exactly that statement — says that
is the corrected script the module names.

## What a failure would mean

A rejection here is a **finding**, not a build inconvenience: it would say that
a `spectec_erratum` edit, which is only checked for being an unambiguous
textual substitution that re-decodes, produces a script `spectec` itself would
have refused to print.  The error names the offending definition and the
check it failed, and nothing swallows it.

## The sensitivity checks

Accepting is cheap to do by accident, so two negative controls run alongside.
Both are statements about the **checker**, not about the corrections; neither
is evidence that an erratum is right.

1. *Reverse order.*  Each corrected script is also checked with its
   definitions reversed, which a SpecTec script — declaring before it uses —
   must fail.  This is satisfied by essentially any script of this size, so
   all it certifies is that the validator is not constantly accepting.
   `Silmaril/SpecTec/Sem/Valid.lean`'s `checkStreamFile` makes the same check
   on the pinned streams.
2. *Per-patch displacement.*  For **each** erratum, the one top-level
   definition that patch rewrites is moved to the front of the otherwise
   unchanged corrected script, and that script must be rejected.  This is
   finer than (1): it says the verdict depends on where *that* definition
   sits, hence that the checker is reading the patched definition's own free
   identifiers rather than only the bulk of the script around it.  It still
   says nothing about whether the patch's content is correct — no check in
   this file does, and typing (above) is the gap that would have to be closed
   first.

## The tie to the constant this file reports on

The `tying` argument is the module's `applyErrata_*` theorem.  The command
requires a constant of that name whose type is exactly

```lean
IL.applyErrata <errata> <base> = some <corrected>
```

for the three identifiers the command was given, proved without axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.  Without it the command would
only have checked that `<corrected>` exists and has type `IL.Script`, and
would have validated a script it rebuilt itself with nothing connecting the
two.
-/

public meta section

namespace Silmaril.SpecTec.IL.Revalidate

open Lean Elab Command
open Silmaril.SpecTec Silmaril.SpecTec.IL

/-! ## Reading the errata back out of the environment -/

/-- Read a reflected `IL.Erratum`, the term `spectec_erratum` emits with
`Lean.addDecl` (`Silmaril/SpecTec/Errata.lean`, `elabSpectecErratum`). -/
def unqErratum (e : Expr) : Option Erratum :=
  match e.getAppFnArgs with
  | (``Erratum.mk, #[i, s, t, c]) => do
      return { issue := ← unqNat i, summary := ← unqStr s,
               target := ← unqStr t, corrected := ← unqDef c }
  | _ => none

/-- Read a `List IL.Erratum` constant.  Its elements are themselves constants —
`wasm10errata` is a list of names, not of literals — so each is unfolded once,
exactly as `IL.erratumScript` unfolds a script's definitions. -/
def erratumListOf (n : Name) : CommandElabM (List Erratum) := do
  let value ← constValue n
  let some elems := unqList (fun e => some e) value
    | throwError "spectec_revalidate: the term for {n} is not a list of `IL.Erratum`"
  elems.mapM fun e => do
    match unqErratum e with
    | some er => pure er
    | none =>
      let some c := e.constName?
        | throwError "spectec_revalidate: {n} has an element that is neither a \
            reflected `IL.Erratum` nor a constant"
      let some er := unqErratum (← constValue c)
        | throwError "spectec_revalidate: {c} is not a reflected `IL.Erratum`"
      pure er

/-! ## Running the checker -/

/-- `Sem.checkDefs` with the first failing definition named.  `Sem.checkDef`
already prefixes its message with the definition's sort and identifier
(`Sem.Check.within`); this adds the top-level name, which for a `recD` group
is the name of its first member. -/
def firstRejection : Sem.Scope → List Def → Option String
  | _, [] => none
  | sc, d :: ds =>
      match Sem.checkDef sc d with
      | .error msg => some s!"at top-level definition `{Sem.defName d}`: {msg}"
      | .ok sc' => firstRejection sc' ds

/-- `Sem.checkScript` with a located message: `none` when the script is
well-formed, otherwise the reason the first definition to fail gives. -/
def validationError? (s : Script) : Option String :=
  match Sem.checkDeclarations s with
  | .error msg => some msg
  | .ok () => firstRejection (Sem.Scope.initial s) s

/-! ## The tie between the command and the constant it reports on -/

/-- The axioms a `tying` theorem is allowed to depend on: the three this
tree's `#print axioms` policy permits. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Check that `thm` is a theorem of type `applyErrata errata base = some
corrected`, for the three constants the command was given, proved without
axioms outside `allowedAxioms`.  This is what ties the script the checker runs
on to the constant the command reports on; without it the command would be
validating a value it rebuilt itself and naming an unrelated one. -/
def checkApplyErrataThm (thm corrected errata base : Name) : CommandElabM Unit := do
  let some info := (← getEnv).find? thm
    | throwError "spectec_revalidate: {thm} is not in the environment"
  unless info matches .thmInfo _ do
    throwError "spectec_revalidate: {thm} is not a theorem"
  let expected ← liftTermElabM do
    let stx ← `(Silmaril.SpecTec.IL.applyErrata $(mkCIdent errata) $(mkCIdent base)
      = some $(mkCIdent corrected))
    let e ← Term.elabTerm stx (some (mkSort Level.zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  -- `withReducible`, so that a mismatch is reported rather than sending the
  -- unifier off to unfold `applyErrata` on a thousand-definition script.
  unless ← liftTermElabM (Meta.withReducible (Meta.isDefEq info.type expected)) do
    throwError "spectec_revalidate: {thm} does not say \
      `applyErrata {errata} {base} = some {corrected}`; it says {info.type}"
  for ax in ← liftCoreM (collectAxioms thm) do
    unless allowedAxioms.contains ax do
      throwError "spectec_revalidate: {thm} depends on the axiom {ax}"

/-! ## The command -/

/-- `spectec_revalidate corrected by errata on base from "path" tying thm` —
see the module documentation. -/
syntax (name := spectecRevalidate)
  "spectec_revalidate " ident " by " ident " on " ident " from " str
    " tying " ident : command

/-- Elaborate `spectec_revalidate`. -/
@[command_elab spectecRevalidate]
def elabSpectecRevalidate : CommandElab := fun stx => do
  let `(command| spectec_revalidate $correctedStx:ident by $errataStx:ident
      on $baseStx:ident from $pathStx:str tying $thmStx:ident) := stx
    | throwUnsupportedSyntax
  let correctedName ← liftCoreM <| realizeGlobalConstNoOverload correctedStx
  let errataName ← liftCoreM <| realizeGlobalConstNoOverload errataStx
  let baseName ← liftCoreM <| realizeGlobalConstNoOverload baseStx
  let thmName ← liftCoreM <| realizeGlobalConstNoOverload thmStx
  let path := pathStx.getString
  -- The corrected script this re-check stands for must exist and be a script.
  let some info := (← getEnv).find? correctedName
    | throwError "spectec_revalidate: {correctedName} is not in the environment"
  unless ← liftTermElabM (Meta.isDefEq info.type (mkConst ``Script)) do
    throwError "spectec_revalidate: {correctedName} is not an `IL.Script`"
  -- …and the `applyErrata` theorem must tie it to what is checked below.
  checkApplyErrataThm thmName correctedName errataName baseName
  -- Ingredient 1: the base script, re-read from the `--ast` stream.
  let (_, base) ← readScript path
  -- …cross-checked against the imported constant, definition by definition.
  let envBase ← erratumScript baseName
  unless base.map defS == envBase.map defS do
    throwError "spectec_revalidate: {path} does not decode to {baseName}; \
      the file and the imported script have diverged"
  -- Ingredient 2: the errata, read back out of the environment.
  let errata ← erratumListOf errataName
  -- Ingredient 3: the splice.
  let some corrected := applyErrata errata base
    | throwError "spectec_revalidate: {errataName} does not apply to {baseName}"
  -- The re-check `docs/projects/spectec-divergences.md` promises.
  if let some msg := validationError? corrected then
    throwError "spectec_revalidate: {correctedName} IS REJECTED by \
      `Silmaril/SpecTec/Sem/Valid.lean` — {msg}.  This is a finding: a \
      `spectec_erratum` edit has produced a script the IL validator would \
      not accept."
  -- Sensitivity (1): the same definitions in the opposite order must be
  -- rejected.  This only says the validator is not constantly accepting.
  if (validationError? corrected.reverse).isNone then
    throwError "spectec_revalidate: {correctedName} was accepted in reverse \
      order as well, so the check above is not testing anything"
  -- Sensitivity (2), per patch: the top-level definition each erratum
  -- rewrites, moved to the front, must be rejected.  This says the verdict
  -- depends on that definition's own free identifiers.
  for e in errata do
    let some i := corrected.findIdx? (fun d => (findDef? e.corrected d).isSome)
      | throwError "spectec_revalidate: no top-level definition of \
          {correctedName} contains `{e.target}`, the target of #{e.issue}"
    let some d := corrected[i]?
      | throwError "spectec_revalidate: internal error indexing {correctedName}"
    if (validationError? (d :: corrected.eraseIdx i)).isNone then
      throwError "spectec_revalidate: {correctedName} is still accepted with \
        the definition patched by #{e.issue} (`{e.target}`) moved to the \
        front, so nothing here tests that that definition is checked"
  logInfo m!"spectec_revalidate {correctedName}: {corrected.length} definitions \
    are well-formed after {errata.length} patches \
    ({(errata.map Erratum.issue).eraseDups.length} issues), tied to \
    {thmName}; rejected when reversed, and with any one patched definition \
    moved to the front"

end Silmaril.SpecTec.IL.Revalidate

/-! ## The four corrected scripts

Each command throws, and so fails the build, if the checker rejects the
corrected script. -/

spectec_revalidate Silmaril.SpecTec.IL.Binary51.wasm30binary51
  by Silmaril.SpecTec.IL.Binary51.binary51
  on Silmaril.SpecTec.Specs.wasm30 from "specs/spectec/wasm-3.0.ast"
  tying Silmaril.SpecTec.IL.Binary51.applyErrata_binary51

spectec_revalidate Silmaril.SpecTec.IL.Text6x.wasm30text6x
  by Silmaril.SpecTec.IL.Text6x.text6x
  on Silmaril.SpecTec.Specs.wasm30 from "specs/spectec/wasm-3.0.ast"
  tying Silmaril.SpecTec.IL.Text6x.applyErrata_text6x

spectec_revalidate Silmaril.SpecTec.IL.Wasm20.wasm20corrected
  by Silmaril.SpecTec.IL.Wasm20.wasm20errata
  on Silmaril.SpecTec.Specs.wasm20 from "specs/spectec/wasm-2.0.ast"
  tying Silmaril.SpecTec.IL.Wasm20.applyErrata_wasm20errata

spectec_revalidate Silmaril.SpecTec.IL.Wasm10.wasm10corrected
  by Silmaril.SpecTec.IL.Wasm10.wasm10errata
  on Silmaril.SpecTec.Specs.wasm10 from "specs/spectec/wasm-1.0.ast"
  tying Silmaril.SpecTec.IL.Wasm10.applyErrata_wasm10errata
