module

public meta import Lean
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.InstrSchema
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.InstrSchema
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public import Silmaril.Raw.Wasm.SpecTec.Generated
public meta import Silmaril.Raw.Wasm.SpecTec.Generated

/-!
# Checking the Lean decoder against the Rust one

`sil spectec` decodes the pinned wasm-3.0 stream with the third-party Rust
`spectec_ast` crate and writes `Silmaril/Wasm/SpecTec/Generated.lean`.  The
command

```
spectec_crosscheck "specs/spectec/wasm-3.0.ast"
  with Silmaril.Wasm.SpecTecEnc.instructionSchemas
  and Silmaril.Wasm.SpecTecEnc.administrativeSchemas
```

reads the same file with the Lean reader and decoder, recomputes the
instruction constructor shapes with `IL.instrSchemas?`, and fails elaboration
unless the two agree on every constructor tag and payload shape.

What is compared is the *set* of `(tag, fields)` pairs, and the number of
them: `IL.instrSchemas?` produces the constructors in declaration order, but
that order is not checked, because `sil spectec` splits the Rust side in two
along the manifest's `administrativeCases` and the elaborator has to
concatenate `instructionSchemas` with `administrativeSchemas` to get them all
back.  Both sides are therefore sorted by tag (`sortByTag`) first.

This is a *build-time* check, like `sil spectec --check`, not a theorem: the
Rust decoder is not a Lean object, so there is nothing to state about it.  The
theorem that the Lean side is faithful to the stream is
`IL.decodeScript?_scriptS` together with `IL.scriptS_of_decodeScript?`.
-/

public meta section

namespace Silmaril.SpecTec.IL

open Lean Elab Command Meta
open Silmaril.Wasm.SpecTecEnc (FieldType ConstructorSchema)

/-- Read back a reflected `FieldType`. -/
partial def evalFieldType (e : Expr) : MetaM FieldType := do
  match_expr ← whnf e with
  | Silmaril.Wasm.SpecTecEnc.FieldType.named n ps => return .named (← reduceEval n) (← reduceEval ps)
  | Silmaril.Wasm.SpecTecEnc.FieldType.optional t => return .optional (← evalFieldType t)
  | Silmaril.Wasm.SpecTecEnc.FieldType.sequence t => return .sequence (← evalFieldType t)
  | Silmaril.Wasm.SpecTecEnc.FieldType.namedList t => return .namedList (← evalFieldType t)
  | _ => throwError "not a FieldType: {e}"

instance : ReduceEval FieldType where
  reduceEval e := evalFieldType e

instance : ReduceEval ConstructorSchema where
  reduceEval e := do
    match_expr ← whnf e with
    | Silmaril.Wasm.SpecTecEnc.ConstructorSchema.mk tag fields digest =>
        return ⟨← reduceEval tag, ← reduceEval fields, ← reduceEval digest⟩
    | _ => throwError "not a ConstructorSchema: {e}"

/-- The `(tag, fields)` pairs of a `List ConstructorSchema` constant. -/
def schemaPairs (n : Name) : CommandElabM (List (String × List FieldType)) := do
  let schemas : List ConstructorSchema ← liftTermElabM <| reduceEval (mkConst n)
  pure (schemas.map fun s => (s.tag, s.fields))

/-- Order constructor shapes by tag; `sil spectec` rejects duplicate tags, so
this is a total order on either side. -/
def sortByTag (xs : List (String × List FieldType)) : Array (String × List FieldType) :=
  xs.toArray.qsort fun a b => a.1 < b.1

/-- `spectec_crosscheck "file" with c₁ and c₂` — see the module documentation. -/
syntax (name := spectecCrosscheck)
  "spectec_crosscheck " str " with " ident " and " ident : command

/-- Elaborate `spectec_crosscheck`. -/
@[command_elab spectecCrosscheck]
def elabSpectecCrosscheck : CommandElab := fun stx => do
  let `(command| spectec_crosscheck $path:str with $a:ident and $b:ident) := stx
    | throwUnsupportedSyntax
  let path := path.getString
  let (_, script) ← readScript path
  let some ours := instrSchemas? script
    | throwError "spectec_crosscheck: {path} has no single plain `instr` variant declaration"
  let expected ← (· ++ ·) <$> schemaPairs (← liftCoreM <| realizeGlobalConstNoOverload a)
    <*> schemaPairs (← liftCoreM <| realizeGlobalConstNoOverload b)
  unless ours.length == expected.length do
    throwError "spectec_crosscheck: {path} has {ours.length} instruction constructors, \
      {a.getId} and {b.getId} have {expected.length}"
  let ours := sortByTag ours
  let expected := sortByTag expected
  for h : i in [0:ours.size] do
    let o := ours[i]
    let e := expected[i]!
    unless o == e do
      throwError "spectec_crosscheck: {path} disagrees with {a.getId}/{b.getId} at {o.1}: \
        Lean has {repr o.2}, the Rust decoder has {repr e.2}"
    let _ := h
  logInfo m!"spectec_crosscheck {path}: {ours.size} instruction constructors agree with \
    {a.getId} and {b.getId}"

end Silmaril.SpecTec.IL
