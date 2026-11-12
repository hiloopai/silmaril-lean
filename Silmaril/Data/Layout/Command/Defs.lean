module

public import Silmaril.Data.Layout.Source.Thms
public import Silmaril.Data.Layout.Record.Thms
public import Silmaril.Data.Layout.Interchange.Thms
public meta import Lean.Elab.Command
public meta import Silmaril.Data.Layout.Source.Defs
public meta import Silmaril.Data.Layout.Record.Thms
public meta import Silmaril.Data.Layout.Interchange.Defs

/-!
# `c_layout` and `c_layout_import`: named declarations and certificates from C text

```
@[expose] public section

c_layout Msg for Target.x86_64 Target.i386 := "struct P { short x; short y; };"
c_layout_import Msg.x86_64 from "clang/msg.x86_64.json"
```

`c_layout N for t₁ … := src` parses `src` (any term evaluating to a `String`, such as a
literal or `include_str "file.c"`) at elaboration time and adds:

| declaration | meaning |
|---|---|
| `N.source : String` | the C text, as a literal |
| `N.<tag>.decl : Decl` | each record's source description |
| `N.ast : Env` | the list of those, in order |
| `N.parses : Source.Parses N.source N.ast` | kernel-checked: `parse` by `decide +kernel` |
| `N.<t>.target : Target` | each target, named by `Target.name` |
| `N.<t>.<tag> : RecordLayout` | each record's ABI-resolved layout, as a literal |
| `N.<t>.layout : List RecordLayout` | the list of those |
| `N.<t>.resolves : resolveEnv N.<t>.target.model N.ast = .ok N.<t>.layout` | kernel-checked |
| `N.<t>.wf : ∀ R ∈ N.<t>.layout, R.WF` | from `resolveEnv_wf` and the target's `wf` |

`c_layout_import N.<t> from "file.json"` reads a `silmaril.c-record-layout` v1 report
(path relative to the current file) and adds:

| declaration | meaning |
|---|---|
| `N.<t>.observed.json : String` | the file, as a literal |
| `N.<t>.observed.report : Report` | its decoding, as a literal |
| `N.<t>.observed.matches : report.Matches N.source N.<t>.target N.<t>.layout` | kernel-checked |
| `N.<t>.observed.crossChecked : CrossChecked N.source N.<t>.target report` | the chain |

**Trust boundary.** Everything above is checked by the kernel except one step: that
`report` is the decoding of `json`. The command runs the compiled `decodeText` (the
`Silmaril.Formats.JsonWire` reader and `decode`) and fails if its result is not `report`, but
does not prove it, because reducing the JSON reader in the kernel takes minutes and tens of
gigabytes for a two-kilobyte file. `decode_encode` is proved for all reports; the agreement
itself (`matches`) is always a kernel proof. Whether the report reflects what Clang printed
is the adapter's responsibility (`tools/c-layout/clang_record_layouts.py`).

Declarations are added without visibility modifiers; in a `module`, put the commands in an
`@[expose] public section` so other modules can reduce them.
-/

public section

namespace Silmaril.Data.Layout.Command

open Lean Elab Command Term Meta
open Silmaril.Data.Layout Silmaril.Data.Layout.Record Silmaril.Data.Layout.Interchange

/-! ## Values as terms -/

meta def qStr (s : String) : Term := ⟨Syntax.mkStrLit s⟩
meta def qNat (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩
meta def qList (xs : List Term) : CommandElabM Term := `([$(xs.toArray),*])
meta def qOptNat : Option Nat → CommandElabM Term
  | none => `(none)
  | some n => `(some $(qNat n))

meta def qIntKind : IntKind → Term
  | .char => mkCIdent ``IntKind.char | .short => mkCIdent ``IntKind.short
  | .int => mkCIdent ``IntKind.int | .long => mkCIdent ``IntKind.long
  | .longLong => mkCIdent ``IntKind.longLong | .int128 => mkCIdent ``IntKind.int128
  | .size => mkCIdent ``IntKind.size | .ptrdiff => mkCIdent ``IntKind.ptrdiff
  | .intptr => mkCIdent ``IntKind.intptr | .wchar => mkCIdent ``IntKind.wchar
  | .exact n => Syntax.mkCApp ``IntKind.exact #[qNat n]

meta def qSign : Sign → Term
  | .signed => mkCIdent ``Sign.signed | .unsigned => mkCIdent ``Sign.unsigned
  | .plain => mkCIdent ``Sign.plain

meta def qFloatKind : FloatKind → Term
  | .float => mkCIdent ``FloatKind.float | .double => mkCIdent ``FloatKind.double
  | .longDouble => mkCIdent ``FloatKind.longDouble | .float128 => mkCIdent ``FloatKind.float128

meta def qKind : Kind → Term
  | .struct => mkCIdent ``Kind.struct | .union => mkCIdent ``Kind.union

meta def qCTy : CTy → CommandElabM Term
  | .void => pure (mkCIdent ``CTy.void)
  | .bool => pure (mkCIdent ``CTy.bool)
  | .int k s => pure (Syntax.mkCApp ``CTy.int #[qIntKind k, qSign s])
  | .float k => pure (Syntax.mkCApp ``CTy.float #[qFloatKind k])
  | .ptr t => return Syntax.mkCApp ``CTy.ptr #[← qCTy t]
  | .enum tag none => return Syntax.mkCApp ``CTy.enum #[qStr tag, ← `(none)]
  | .enum tag (some (k, s)) =>
    return Syntax.mkCApp ``CTy.enum #[qStr tag, ← `(some ($(qIntKind k), $(qSign s)))]
  | .array e n => return Syntax.mkCApp ``CTy.array #[← qCTy e, qNat n]
  | .struct tag => pure (Syntax.mkCApp ``CTy.struct #[qStr tag])
  | .union tag => pure (Syntax.mkCApp ``CTy.union #[qStr tag])
  | .typedef n t => return Syntax.mkCApp ``CTy.typedef #[qStr n, ← qCTy t]

meta def qField (f : Field) : CommandElabM Term := do
  `(({ name := $(qStr f.name), ty := $(← qCTy f.ty), alignas := $(← qOptNat f.alignas),
       bits := $(← qOptNat f.bits) } : Field))

meta def qDecl (d : Decl) : CommandElabM Term := do
  `(({ kind := $(qKind d.kind), tag := $(qStr d.tag),
       fields := $(← qList (← d.fields.mapM qField)) } : Decl))

meta def qEntry (e : Entry) : CommandElabM Term :=
  `(({ name := $(qStr e.name), offset := $(qNat e.offset), size := $(qNat e.size),
       align := $(qNat e.align) } : Entry))

meta def qRecordLayout (R : RecordLayout) : CommandElabM Term := do
  `(({ kind := $(qKind R.kind), name := $(qStr R.name), size := $(qNat R.size),
       align := $(qNat R.align),
       entries := $(← qList (← R.entries.mapM qEntry)) } : RecordLayout))

meta def qObservedRecord (o : ObservedRecord) : CommandElabM Term := do
  let fs ← o.fields.mapM fun f =>
    `(({ name := $(qStr f.name), offset := $(qNat f.offset) } : ObservedField))
  `(({ kind := $(qKind o.kind), name := $(qStr o.name), size := $(qNat o.size),
       dataSize := $(qNat o.dataSize), align := $(qNat o.align),
       fields := $(← qList fs) } : ObservedRecord))

meta def qProvenance (p : Provenance) : CommandElabM Term :=
  `(({ producer := $(qStr p.producer), producerVersion := $(qStr p.producerVersion),
       method := $(qStr p.method), target := $(qStr p.target), adapter := $(qStr p.adapter),
       source := $(qStr p.source) } : Provenance))

meta def qReport (r : Report) : CommandElabM Term := do
  `(({ provenance := $(← qProvenance r.provenance),
       records := $(← qList (← r.records.mapM qObservedRecord)) } : Report))

/-! ## Evaluation at elaboration time -/

meta def evalString (stx : Term) : CommandElabM String :=
  liftTermElabM do unsafe evalTerm String (mkConst ``String) stx

meta def evalTarget (stx : Term) : CommandElabM Target :=
  liftTermElabM do unsafe evalTerm Target (mkConst ``Target) stx

meta def readRelative (path : String) : CommandElabM String := do
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  IO.FS.readFile (dir / path)

/-! ## Diagnostics -/

/-- The first difference between predicted and observed records, for error messages. -/
meta def firstDiff : List ObservedRecord → List ObservedRecord → Option String
  | [], [] => none
  | p :: _, [] => some s!"record `{p.name}` is missing from the report"
  | [], o :: _ => some s!"the report has an extra record `{o.name}`"
  | p :: ps, o :: os =>
    if p.kind != o.kind || p.name != o.name then
      some s!"expected record `{p.name}`, the report has `{o.name}` (records are compared in order)"
    else if p.size != o.size then
      some s!"`{p.name}`: predicted size {p.size} bits, observed {o.size}"
    else if p.dataSize != o.dataSize then
      some s!"`{p.name}`: predicted data size {p.dataSize} bits, observed {o.dataSize}"
    else if p.align != o.align then
      some s!"`{p.name}`: predicted alignment {p.align} bits, observed {o.align}"
    else match (p.fields.zip o.fields).find? (fun (a, b) => a != b) with
      | some (a, b) => some s!"`{p.name}.{a.name}`: predicted offset {a.offset} bits, \
          observed `{b.name}` at {b.offset}"
      | none => if p.fields.length != o.fields.length then
          some s!"`{p.name}`: {p.fields.length} members predicted, {o.fields.length} observed"
        else firstDiff ps os

meta def mismatch? (src : String) (t : Target) (Ls : List RecordLayout) (r : Report) :
    Option String :=
  if r.provenance.source != src then some "the report is about a different source text"
  else if r.provenance.target != t.triple then
    some s!"the report is for `{r.provenance.target}`, the target `{t.name}` is `{t.triple}`"
  else firstDiff (Ls.map RecordLayout.observe) r.records

/-! ## The commands -/

/-- See the module documentation. -/
syntax (name := cLayout) "c_layout " ident " for " term:max+ " := " term : command

/-- See the module documentation. -/
syntax (name := cLayoutImport) "c_layout_import " ident " from " str : command

meta def declId (n : Name) : Ident := mkIdent n

/-- The value of `pre.field`, a declaration `c_layout` made. -/
meta def evalDefined {α : Type} (pre field : Name) (type : Expr) : CommandElabM α := do
  let n := pre ++ field
  let ns ← getCurrNamespace
  let n ← if (← getEnv).contains (ns ++ n) then pure (ns ++ n)
    else if (← getEnv).contains n then pure n
    else throwError "c_layout_import: `{n}` is not defined; run `c_layout` first"
  liftTermElabM do unsafe evalExpr α type (mkConst n)

@[command_elab cLayout] meta def elabCLayout : CommandElab := fun stx => do
  let base := stx[1].getId
  let targetStxs : Array Term := stx[3].getArgs.map (⟨·⟩)
  let src ← evalString ⟨stx[5]⟩
  let env ← match Source.parse src with
    | .ok env => pure env
    | .error e => throwErrorAt stx[5] "c_layout: {e}"
  let n (s : String) : Ident := declId (base ++ s.toName)
  let source := declId (base ++ `source)
  let ast := declId (base ++ `ast)
  elabCommand (← `(def $source : String := $(qStr src)))
  for d in env do
    let name := declId (base ++ Name.mkSimple d.tag ++ `decl)
    elabCommand (← `(def $name : Decl := $(← qDecl d)))
  let declRefs := env.map fun d => (declId (base ++ Name.mkSimple d.tag ++ `decl) : Term)
  elabCommand (← `(def $ast : Env := $(← qList declRefs)))
  elabCommand (← `(theorem $(n "parses") : Source.Parses $source $ast :=
    Source.parses_of_toOption (by decide +kernel)))
  for tStx in targetStxs do
    let t ← evalTarget tStx
    let pre := base ++ Name.mkSimple t.name
    let Ls ← match resolveEnv t.model env with
      | .ok Ls => pure Ls
      | .error e => throwErrorAt tStx "c_layout: no layout on {t.name}: {e}"
    let target := declId (pre ++ `target)
    let layout := declId (pre ++ `layout)
    let resolves := declId (pre ++ `resolves)
    elabCommand (← `(def $target : Target := $tStx))
    for R in Ls do
      elabCommand (← `(def $(declId (pre ++ Name.mkSimple R.name)) : RecordLayout :=
        $(← qRecordLayout R)))
    let refs := Ls.map fun R => (declId (pre ++ Name.mkSimple R.name) : Term)
    elabCommand (← `(def $layout : List RecordLayout := $(← qList refs)))
    elabCommand (← `(theorem $resolves : resolveEnv ($target).model $ast = .ok $layout :=
      resolveEnv_of_toOption (by decide +kernel)))
    elabCommand (← `(theorem $(declId (pre ++ `wf)) : ∀ R ∈ $layout, RecordLayout.WF R :=
      resolveEnv_wf ($target).wf $resolves))

@[command_elab cLayoutImport] meta def elabCLayoutImport : CommandElab := fun stx => do
  let pre := stx[1].getId
  let base := pre.getPrefix
  let path := stx[3].isStrLit?.getD ""
  let text ← readRelative path
  let r ← match decodeText text with
    | .ok r => pure r
    | .error e => throwErrorAt stx[3] "c_layout_import: {path}: {e}"
  let src ← evalDefined base `source (mkConst ``String) (α := String)
  let t ← evalDefined pre `target (mkConst ``Target) (α := Target)
  let Ls ← evalDefined pre `layout (mkApp (mkConst ``List [0]) (mkConst ``RecordLayout))
    (α := List RecordLayout)
  if let some why := mismatch? src t Ls r then
    throwErrorAt stx[3] "c_layout_import: {path} disagrees with the model: {why}"
  let obs := pre ++ `observed
  let report := declId (obs ++ `report)
  let source := declId (base ++ `source)
  let target := declId (pre ++ `target)
  let layout := declId (pre ++ `layout)
  elabCommand (← `(def $(declId (obs ++ `json)) : String := $(qStr text)))
  elabCommand (← `(def $report : Report := $(← qReport r)))
  elabCommand (← `(theorem $(declId (obs ++ `matches)) :
      Report.Matches $report $source $target $layout := by decide +kernel))
  elabCommand (← `(theorem $(declId (obs ++ `crossChecked)) :
      CrossChecked $source $target $report :=
    ⟨_, $(declId (base ++ `parses)), _, $(declId (pre ++ `resolves)), $(declId (pre ++ `wf)),
      $(declId (obs ++ `matches))⟩))

end Silmaril.Data.Layout.Command

end
