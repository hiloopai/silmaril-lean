module

public import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Silmaril.Wasi.Versions.WitImport.RImport.Defs
public meta import Lean.Elab.Term
public meta import Lean.ToExpr

/-!
# `wit_rpkg%`: resolved tables and type environments computed by the WIT importer

`wit_rpkg% ver sel "a.wit" …` runs `importRPkg sel ver` (`Silmaril.Wasi.Versions.WitImport.RImport`)
on the files during elaboration and quotes the result as a constructor term of type `RPkg`: the
resolved table of the first file's package and the type environment of it and its dependencies.
`sel` is `ifaces` (worlds dropped, as `wit_iface_table%`) or `all`.

The quoting helpers are a copy of `Silmaril.Wasi.Versions.WitImport.Quote` (private there), extended
to type kinds and interface names. The trust is that of `wit_table%`: Lean's evaluator runs the
front end and the glue; the kernel sees the quoted constructors.
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

private meta def quoteIface (i : Binary.IfaceName) : Expr :=
  mkApp2 (Lean.mkConst ``Binary.IfaceName.mk) (quotePkgName i.pkg) (toExpr i.name)

private meta def quoteLabeled {α : Type} (a : Expr) (q : α → Expr) (l : Binary.Labeled α) : Expr :=
  mkApp4 (Lean.mkConst ``Binary.Labeled.mk) a (toExpr l.name) (q l.ty) (strOpt l.docs)

private meta def unitE : Expr := Lean.mkConst ``Unit
private meta def unitV : Expr := Lean.mkConst ``Unit.unit

private meta def quoteKind : Binary.TyDefKind → Expr
  | .record fs => mkApp (Lean.mkConst ``Binary.TyDefKind.record)
      (exprList (mkApp (Lean.mkConst ``Binary.Labeled) tyE) (fs.map (quoteLabeled tyE quoteTy)))
  | .variant cs =>
    let oT := mkApp (Lean.mkConst ``Option [0]) tyE
    mkApp (Lean.mkConst ``Binary.TyDefKind.variant)
      (exprList (mkApp (Lean.mkConst ``Binary.Labeled) oT)
        (cs.map (quoteLabeled oT fun o => exprOpt tyE (o.map quoteTy))))
  | .enum cs => mkApp (Lean.mkConst ``Binary.TyDefKind.enum)
      (exprList (mkApp (Lean.mkConst ``Binary.Labeled) unitE)
        (cs.map (quoteLabeled unitE fun _ => unitV)))
  | .flags cs => mkApp (Lean.mkConst ``Binary.TyDefKind.flags)
      (exprList (mkApp (Lean.mkConst ``Binary.Labeled) unitE)
        (cs.map (quoteLabeled unitE fun _ => unitV)))
  | .resource => Lean.mkConst ``Binary.TyDefKind.resource
  | .type t => mkApp (Lean.mkConst ``Binary.TyDefKind.type) (quoteTy t)

private meta def readSrcR (path : TSyntax `str) : TermElabM Src := do
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

/-- `wit_rpkg% ver sel "a.wit" …`: the resolved table and type environment of the first file's
package. -/
syntax (name := witRPkg) "wit_rpkg% " ident ident (ppSpace str)+ : term

@[term_elab witRPkg] meta def elabWitRPkg : TermElab := fun stx _ => do
  let `(wit_rpkg% $v:ident $s:ident $ps:str*) := stx | throwUnsupportedSyntax
  let ver ← match v.getId with
    | `versioned => pure true
    | `unversioned => pure false
    | _ => throwErrorAt v "expected versioned or unversioned"
  let sel ← match s.getId with
    | `ifaces => pure true
    | `all => pure false
    | _ => throwErrorAt s "expected ifaces or all"
  let srcs ← ps.toList.mapM readSrcR
  let (R, E) ← match importRPkg sel ver srcs with
    | .ok r => pure r
    | .error e => throwError "WIT importer: {e}"
  let fnE := Lean.mkConst ``Silmaril.Wasi.FnName
  let ifE := Lean.mkConst ``Binary.IfaceName
  let sigE := Lean.mkConst ``Binary.Sig
  let isE := mkApp2 (Lean.mkConst ``Prod [0, 0]) ifE sigE
  let rE := exprList (mkApp2 (Lean.mkConst ``Prod [0, 0]) fnE isE)
    (R.map fun (f, i, s) =>
      exprPair fnE isE (quoteFnName f) (exprPair ifE sigE (quoteIface i) (quoteSig s)))
  let strE := Lean.mkConst ``String
  let kdE := Lean.mkConst ``Binary.TyDefKind
  let kE := mkApp2 (Lean.mkConst ``Prod [0, 0]) strE kdE
  let tsE := mkApp (Lean.mkConst ``List [0]) kE
  let eE := exprList (mkApp2 (Lean.mkConst ``Prod [0, 0]) ifE tsE)
    (E.map fun (i, ts) => exprPair ifE tsE (quoteIface i)
      (exprList kE (ts.map fun (n, k) => exprPair strE kdE (toExpr n) (quoteKind k))))
  let rT := mkApp (Lean.mkConst ``List [0]) (mkApp2 (Lean.mkConst ``Prod [0, 0]) fnE isE)
  let eT := mkApp (Lean.mkConst ``List [0]) (mkApp2 (Lean.mkConst ``Prod [0, 0]) ifE tsE)
  return exprPair rT eT rE eE

end Silmaril.Wasi.Versions.WitImport
