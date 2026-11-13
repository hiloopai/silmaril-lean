module

public import Silmaril.Cerberus.Codec.File.Defs
public meta import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Cerberus.Codec.WellFormed.Defs
public meta import Lean
public meta import Lean.Elab.Deriving.ToExpr

/-!
# Elaboration-time literals for exported Core

`core_document% text` accepts an actual, canonical `cerb-export` document and
returns `Codec.Document`. `core_function% text` accepts the canonical encoding
of a `(Sym × Core.FunDecl Codec.wireModel Unit Unit)` binding. Both run codecs
only during elaboration. The generated values contain syntax constructors,
not a runtime parser, source string or `Except` fallback.

Documents quote the retained ordered `FileBindings`; their semantic file is
constructed with `FileBindings.toFile`, and `file_eq` is `rfl`. This preserves
the full wire symbols and every document field, including enum registrations,
without trying to quote quotient-based semantic maps or equality proofs.

`include_str` works as for the typed-Ail literals. Its external file is not an
automatic Lake dependency: regenerate/check hash-pinned wrappers after edits.
For large literals scope `set_option maxRecDepth 100000 in` to the declaration.
Kernel checking verifies the generated term's type, not a theorem relating it
to the codec invocation. Importing syntax establishes neither C-to-Core
translation correctness nor a semantic verification of the imported program.
-/

public meta section

namespace Silmaril.Cerberus.Core.Quote

open Lean Elab Command Term Meta Parser.Term
open Silmaril.TaggedCodec Codec

/- The standard ToExpr deriver cannot quote the value parameter `M :
MemoryModel` (its fields are types). Generate only the concrete wire-model
instances needed here. Type parameters are the exporter's Unit annotations
and Sym identifiers. Recursive instances use Lean's usual local-instance
scheme; no generic or fabricated ToExpr MemoryModel instance is introduced. -/

private def coreParameters (info : InductiveVal) : TermElabM (Array Term × Array Term) := do
  forallTelescopeReducing info.type fun xs _ => do
    let mut params := #[]
    let mut quoted := #[]
    for x in xs[:info.numParams] do
      let decl ← x.fvarId!.getDecl
      if (← inferType x).isConstOf ``MemoryModel then
        params := params.push (← `(_root_.Silmaril.Cerberus.Codec.wireModel))
        quoted := quoted.push (← `(mkConst ``Codec.wireModel))
      else if ← isType x then
        if decl.userName == `sym then
          params := params.push (← `(_root_.Silmaril.Cerberus.Sym))
          quoted := quoted.push (← `(toTypeExpr Sym))
        else
          params := params.push (← `(Unit))
          quoted := quoted.push (← `(toTypeExpr Unit))
      else
        throwError "unsupported Core quotation parameter {x} of {info.name}"
    return (params, quoted)

private def deriveCore (info : InductiveVal) : CommandElabM Unit := do
  let members ← info.all.toArray.mapM getConstInfoInduct
  let names ← members.mapM fun member => liftTermElabM do
    mkFreshUserName (.str .anonymous s!"quote_{member.name.getString!}")
  let types ← members.mapM fun member => liftTermElabM do
    let (params, _) ← coreParameters member
    `(@$(mkIdent member.name) $params*)
  let typeExprs ← members.mapM fun member => liftTermElabM do
    let (_, quoted) ← coreParameters member
    `(mkAppN (mkConst $(quote member.name)) #[$quoted,*])
  let defs ← members.mapIdxM fun i member => liftTermElabM do
    let (_, quoted) ← coreParameters member
    let alts ← member.ctors.toArray.mapM fun ctor => do
      let ci ← getConstInfoCtor ctor
      let mut patterns : Array Term := #[]
      for _ in [:ci.numParams] do patterns := patterns.push (← `(_))
      let mut args := quoted
      for _ in [:ci.numFields] do
        let id := mkIdent (← mkFreshUserName `field)
        patterns := patterns.push id
        args := args.push (← `(toExpr $id))
      `(matchAltExpr| | @$(mkIdent ctor) $patterns* => mkAppN (mkConst $(quote ctor)) #[$args,*])
    let mut body ← `(match value with $alts:matchAlt*)
    for j in [:members.size] do
      body ← `(let _ : ToExpr $(types[j]!) :=
                 { toExpr := $(mkIdent names[j]!), toTypeExpr := $(typeExprs[j]!) }; $body)
    `(private partial def $(mkIdent names[i]!) (value : $(types[i]!)) : Lean.Expr := $body)
  elabCommand (← `(mutual $defs:command* end))
  for i in [:members.size] do
    elabCommand (← `(private instance : ToExpr $(types[i]!) where
      toExpr := $(mkIdent names[i]!)
      toTypeExpr := $(typeExprs[i]!)))

private partial def deriveSyntax (name : Lean.Name) (seen : NameSet) : CommandElabM NameSet := do
  if name == ``MemoryModel || !(`Silmaril.Cerberus).isPrefixOf name || seen.contains name then
    return seen
  let seen := seen.insert name
  let some declaration := (← getEnv).find? name | return seen
  match declaration with
  | .defnInfo info => info.value.getUsedConstants.foldlM (fun seen n => deriveSyntax n seen) seen
  | .inductInfo info =>
    let mut seen := info.all.foldl (fun seen n => seen.insert n) seen
    for member in info.all do
      let mi ← getConstInfoInduct member
      for ctor in mi.ctors do
        let ci ← getConstInfoCtor ctor
        seen ← ci.type.getUsedConstants.foldlM (fun seen n => deriveSyntax n seen) seen
    if (`Silmaril.Cerberus.Core).isPrefixOf name then
      deriveCore info
    else
      let already ← liftTermElabM do
        if info.numParams != 0 then return false
        return (← synthInstance? (mkApp (mkConst ``ToExpr [1]) (mkConst name))).isSome
      unless already do
        elabCommand (← `(deriving instance Lean.ToExpr for $[$(info.all.toArray.map mkIdent)],*))
    return seen
  | _ => return seen

deriving instance Lean.ToExpr for Silmaril.Numeric.Ieee754.F64
deriving instance Lean.ToExpr for Empty

run_cmd do
  let seen ← deriveSyntax ``Codec.WirePointer {}
  let _ ← deriveSyntax ``Codec.FileBindings seen

private def readText (text : Syntax) : TermElabM String := do
  let e ← elabTermEnsuringType text (mkConst ``String)
  reduceEval e

elab "core_document%" text:term : term => do
  let text ← readText text
  let doc ← match Codec.WellFormed.parseDocument text with
    | .ok doc => pure doc
    | .error e => throwError "Core document literal rejected: {repr e}"
  let bindings := toExpr doc.bindings
  let commit := toExpr doc.commit
  let implementation := toExpr doc.implementation
  let enums := toExpr doc.enumBindings
  withLetDecl `bindings (mkConst ``Codec.FileBindings) bindings fun bindings => do
    let file := mkApp (mkConst ``Codec.FileBindings.toFile) bindings
    let proof ← mkEqRefl file
    mkLetFVars #[bindings] (mkAppN (mkConst ``Codec.Document.mk)
      #[commit, implementation, bindings, file, proof, enums])

elab "core_function%" text:term : term => do
  let text ← readText text
  let some s := Silmaril.Formats.SExpEncoding.parseDoc? text
    | throwError "Core function literal rejected: invalid S-expression syntax"
  let some tree := Silmaril.Formats.SExpEncoding.taggedDoc? s
    | throwError "Core function literal rejected: invalid tagged S-expression syntax"
  unless Silmaril.Formats.SExpEncoding.printTagged tree ++ "\n" == text do
    throwError "Core function literal rejected: noncanonical binding layout"
  let codec := tuple (Codec.sym ⊗ Codec.funDecl)
  let function ← match codec.decode tree with
    | .ok f => pure f
    | .error e => throwError "Core function literal rejected: {repr e}"
  unless (Codec.WellFormed.digestProblems [] tree).isEmpty do
    throwError "Core function literal rejected: invalid symbol digest"
  return toExpr function

end Silmaril.Cerberus.Core.Quote
