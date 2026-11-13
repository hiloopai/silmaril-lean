module

public import Silmaril.Cerberus.Ail.Syntax.Defs
public meta import Silmaril.Cerberus.Ail.Codec.Defs
public meta import Lean
public meta import Lean.Elab.Deriving.ToExpr

/-!
# Elaboration-time typed-Ail literals

`ail_function% text` and `ail_program% text` run the existing typed-Ail codec
while elaborating, then quote its result into ordinary constructor terms.
The resulting value has no `Except` wrapper and performs no runtime parsing.
Malformed input is an elaboration error; there is no fallback syntax tree.

`text` must reduce to a string literal. Core's `include_str` is supported, for
example `ail_function% (include_str "Fn_example.ail")`. As with `include_str`
itself, Lake does not automatically track the included file: regenerate/check
the wrapper with its source hash after editing an external Ail input.

Large quotations contain deep constructor lists. Scope `set_option maxRecDepth
100000 in` to their enclosing declaration when needed: increasing the option
inside the elaborator cannot cover the declaration's later kernel check.

The kernel checks the resulting constructor term's type. This does not prove
that the quotation equals a codec invocation, nor validate C lowering or C
semantics. A theorem connecting a particular quotation to its source text is
a separate optional artifact.
-/

public meta section

namespace Silmaril.Cerberus.Ail.Quote

open Lean Elab Command Term Meta

deriving instance Lean.ToExpr for ByteArray

/-- Reuse Lean's standard nested/mutual `ToExpr` deriving handler for the
reachable Cerberus syntax. Existing container and scalar instances are reused.
Following constructor types also reaches through local type abbreviations. -/
private partial def deriveSyntax (name : Name) (seen : NameSet) : CommandElabM NameSet := do
  if !(`Silmaril.Cerberus).isPrefixOf name || seen.contains name then return seen
  let seen := seen.insert name
  let some declaration := (← getEnv).find? name | return seen
  match declaration with
  | .defnInfo info =>
    info.value.getUsedConstants.foldlM (fun seen n => deriveSyntax n seen) seen
  | .inductInfo info =>
    let mut seen := info.all.foldl (fun seen n => seen.insert n) seen
    for member in info.all do
      let memberInfo ← getConstInfoInduct member
      for ctor in memberInfo.ctors do
        let ctorInfo ← getConstInfoCtor ctor
        seen ← ctorInfo.type.getUsedConstants.foldlM (fun seen n => deriveSyntax n seen) seen
    let types := info.all.toArray.map mkIdent
    elabCommand (← `(deriving instance Lean.ToExpr for $[$types],*))
    return seen
  | _ => return seen

run_cmd do
  let seen ← deriveSyntax ``Sigma {}
  let _ ← deriveSyntax ``GenTypeCategory seen

private def readText (text : Syntax) : TermElabM String := do
  let e ← elabTermEnsuringType text (mkConst ``String)
  reduceEval e

elab "ail_function%" text:term : term => do
  let text ← readText text
  let decoded := Cabs.Wire.read text.toByteArray >>= Codec.decodeFunctionDefinition Codec.decodeGenTypeCategory
  match decoded with
  | .error error => throwError "typed-Ail function literal rejected: {error}"
  | .ok function => return toExpr function

elab "ail_program%" text:term : term => do
  let text ← readText text
  let decoded := Cabs.Wire.read text.toByteArray >>= Codec.decodeProgram Codec.decodeGenTypeCategory
  match decoded with
  | .error error => throwError "typed-Ail program literal rejected: {error}"
  | .ok program => return toExpr program

end Silmaril.Cerberus.Ail.Quote
