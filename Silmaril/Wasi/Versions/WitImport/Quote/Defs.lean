module

public import Silmaril.Wasi.Versions.WitImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.Defs
public meta import Lean.Elab.Term
public meta import Lean.ToExpr

/-!
# `wit_table%`: signature tables computed by the WIT importer

`wit_table% ver "a.wit" "b.wit" …` reads the WIT files (paths relative to the Lean source,
as for `include_str`), runs `WitImport.importPkg` on them **during elaboration** (the first
file's package is elaborated in the universe of all files) and quotes `WitImport.table ver P`
as a constructor term of type `WitImport.Table`. `wit_drops% ver …` quotes
`WitImport.drops ver P`. A file without a `package` header gets the header of a `.wit` file
of its directory.

The term is the importer's output as computed by Lean's evaluator; the kernel only sees the
quoted constructors. The trust is that of `#guard`: the evaluator runs the verified front end
(`Silmaril.Wasm.Wit`) and the unverified glue of `WitImport`. Lake does not track the files:
editing a `.wit` file does not rebuild the importing module (as for `include_str`).
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Lean Elab Term
open Silmaril.Wasm.Wit

private meta def exprList (type : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x rest => mkApp3 (Lean.mkConst ``List.cons [0]) type x rest)
    (mkApp (Lean.mkConst ``List.nil [0]) type)

private meta def exprOpt (type : Expr) : Option Expr → Expr
  | none => mkApp (Lean.mkConst ``Option.none [0]) type
  | some x => mkApp2 (Lean.mkConst ``Option.some [0]) type x

private meta def exprPair (a b : Expr) (x y : Expr) : Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) a b x y

private meta def strOpt (o : Option String) : Expr := exprOpt (Lean.mkConst ``String) (o.map toExpr)

private meta def quotePrim : Silmaril.Wasm.Component.Binary.PrimValType → Expr
  | .bool => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.bool
  | .s8 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.s8
  | .u8 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.u8
  | .s16 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.s16
  | .u16 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.u16
  | .s32 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.s32
  | .u32 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.u32
  | .s64 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.s64
  | .u64 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.u64
  | .f32 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.f32
  | .f64 => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.f64
  | .char => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.char
  | .string => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.string
  | .errorContext => Lean.mkConst ``Silmaril.Wasm.Component.Binary.PrimValType.errorContext

private meta def quotePkgName (p : Binary.PackageName) : Expr :=
  mkApp3 (Lean.mkConst ``Binary.PackageName.mk) (toExpr p.ns) (toExpr p.name) (strOpt p.version)

private meta def quoteTyRef (r : Binary.TyRef) : Expr :=
  let o := match r.owner with
    | .local => Lean.mkConst ``Binary.Owner.local
    | .iface i => mkApp (Lean.mkConst ``Binary.Owner.iface)
        (mkApp2 (Lean.mkConst ``Binary.IfaceName.mk) (quotePkgName i.pkg) (toExpr i.name))
  mkApp2 (Lean.mkConst ``Binary.TyRef.mk) o (toExpr r.name)

private meta def tyE : Expr := Lean.mkConst ``Binary.Ty

private meta partial def quoteTy : Binary.Ty → Expr
  | .prim p => mkApp (Lean.mkConst ``Binary.Ty.prim) (quotePrim p)
  | .ref r => mkApp (Lean.mkConst ``Binary.Ty.ref) (quoteTyRef r)
  | .list t => mkApp (Lean.mkConst ``Binary.Ty.list) (quoteTy t)
  | .fixedList t n => mkApp2 (Lean.mkConst ``Binary.Ty.fixedList) (quoteTy t) (toExpr n)
  | .map k v => mkApp2 (Lean.mkConst ``Binary.Ty.map) (quoteTy k) (quoteTy v)
  | .option t => mkApp (Lean.mkConst ``Binary.Ty.option) (quoteTy t)
  | .result a b => mkApp2 (Lean.mkConst ``Binary.Ty.result)
      (exprOpt tyE (a.map quoteTy)) (exprOpt tyE (b.map quoteTy))
  | .tuple ts => mkApp (Lean.mkConst ``Binary.Ty.tuple) (exprList tyE (ts.map quoteTy))
  | .own r => mkApp (Lean.mkConst ``Binary.Ty.own) (quoteTyRef r)
  | .borrow r => mkApp (Lean.mkConst ``Binary.Ty.borrow) (quoteTyRef r)
  | .future t => mkApp (Lean.mkConst ``Binary.Ty.future) (exprOpt tyE (t.map quoteTy))
  | .stream t => mkApp (Lean.mkConst ``Binary.Ty.stream) (exprOpt tyE (t.map quoteTy))

private meta def quoteSig (s : Binary.Sig) : Expr :=
  let pE := mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``String) tyE
  mkApp3 (Lean.mkConst ``Binary.Sig.mk) (toExpr s.async)
    (exprList pE (s.params.map fun (n, t) => exprPair (Lean.mkConst ``String) tyE (toExpr n) (quoteTy t)))
    (exprOpt tyE (s.result.map quoteTy))

private meta def quoteFnName (f : Silmaril.Wasi.FnName) : Expr :=
  mkApp2 (Lean.mkConst ``Silmaril.Wasi.FnName.mk) (toExpr f.iface) (toExpr f.fn)

private meta def readSrc (path : TSyntax `str) : TermElabM Src := do
  let source := System.FilePath.mk (← readThe Core.Context).fileName
  let some directory := source.parent | throwError "cannot find source directory for {source}"
  let file := directory / path.getString
  let text ← try IO.FS.readFile file catch e => throwError "cannot read {file}: {e.toMessageData}"
  let some dir := file.parent | throwError "no directory for {file}"
  let mut hdr := (headerOf text).getD ""
  if hdr.isEmpty then
    let es ← dir.readDir
    for e in es.qsort (·.fileName < ·.fileName) do
      if hdr.isEmpty && e.fileName.endsWith ".wit" then
        if let some h := headerOf (← IO.FS.readFile e.path) then hdr := h
  if hdr.isEmpty then throwError "no package header for {file}"
  return (hdr, path.getString, text)

private meta def importAt (paths : Array (TSyntax `str)) : TermElabM Binary.Package := do
  let srcs ← paths.toList.mapM readSrc
  match importPkg srcs with
  | .ok P => return P
  | .error e => throwError "WIT importer: {e}"

/-- `wit_table% ver "a.wit" …`: the signature table of the first file's package. -/
syntax (name := witTable) "wit_table% " ident (ppSpace str)+ : term
/-- `wit_drops% ver "a.wit" …`: the resource drops of the first file's package. -/
syntax (name := witDrops) "wit_drops% " ident (ppSpace str)+ : term

private meta def getVer (stx : Syntax) : TermElabM Bool := do
  match stx.getId with
  | `versioned => return true
  | `unversioned => return false
  | _ => throwErrorAt stx "expected versioned or unversioned"

@[term_elab witTable] meta def elabWitTable : TermElab := fun stx _ => do
  let `(wit_table% $v:ident $ps:str*) := stx | throwUnsupportedSyntax
  let P ← importAt ps
  let ver ← getVer v
  let fnE := Lean.mkConst ``Silmaril.Wasi.FnName
  let sigE := Lean.mkConst ``Binary.Sig
  return exprList (mkApp2 (Lean.mkConst ``Prod [0, 0]) fnE sigE)
    ((table ver P).map fun (f, s) => exprPair fnE sigE (quoteFnName f) (quoteSig s))

@[term_elab witDrops] meta def elabWitDrops : TermElab := fun stx _ => do
  let `(wit_drops% $v:ident $ps:str*) := stx | throwUnsupportedSyntax
  let P ← importAt ps
  let ver ← getVer v
  return exprList (Lean.mkConst ``Silmaril.Wasi.FnName) ((drops ver P).map quoteFnName)

end Silmaril.Wasi.Versions.WitImport
