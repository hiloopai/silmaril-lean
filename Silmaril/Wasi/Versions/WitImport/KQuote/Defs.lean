module

public import Silmaril.Wasi.Versions.WitImport.KSplit.Thms
public import Silmaril.Wasi.Versions.WitImport.KFast.Defs
public import Silmaril.Wasi.Versions.WitImport.KRfl.Defs
public import Silmaril.Wasi.Versions.WitImport.KSrcNd.Defs
public import Silmaril.Wasi.Versions.WitImport.KTokens.Defs
public import Silmaril.Wasi.Versions.WitImport.KNoDoc.Thms
public meta import Silmaril.Wasi.Versions.WitImport.KSplit.Thms
public meta import Silmaril.Wasi.Versions.WitImport.KNoDoc.Defs
public meta import Silmaril.Wasi.Versions.WitImport.KFast.Defs
public meta import Lean.Elab.Deriving.ToExpr
public meta import Lean.Elab.Command
public meta import Lean.ToExpr

@[expose] public section

/-!
# `wit_kfile`, `wit_kcert`: certificates for the kernel importer

`wit_kfile F "a.wit"` and `wit_kcert K part … from ver sel [F₀, …] "a.wit" …` run the importer's
steps on the files (without doc comments, as `wit_srcnd%` gives them) in Lean's evaluator, as
`wit_table%` does, and add declarations under the prefixes `F` and `K`: quoted intermediate
results and theorems, checked by the kernel, that the importer evaluated in the kernel
(`importKD`, `Silmaril.Wasi.Versions.WitImport.KSplit`) produces them. The quoted values are only
certificates: each is tied to the kernel evaluation by a checked theorem, so neither the
evaluator nor the quoting is trusted.

Quoted values are functions of the string constructor (`F.d : (List Char → String) → Document`,
…), with every string `mk [c₁, …]` (characters as `Char.ofNat` codes, never a string literal):
with `String.ofList` they are compared with the parser's output character by character
(`kernel_rfl`), with `fastStr` the kernel computes on them (`Silmaril.Wasi.Versions.WitImport.KFast`).

* `wit_kfile F "a.wit"`: `F.src` (`wit_srcnd%` of the file), `F.d` its document, and
  `F.parse : parseCharsK F.src = some (F.d String.ofList)`.
* `wit_klex F "a.wit"` (after `wit_kfile F`): `F.full` (`wit_src%` of the file, with its doc
  comments), `F.toks` the tokens of `F.src`, `F.lexSrc` and `F.lexFull` (the tokens of
  `F.full` without doc-comment tokens are `F.toks`), hence `F.lexNd` and
  `F.parseNd : parseCharsK F.src = parseTokK F.full` (`parseCharsK_of_lex`): `demoteDocs` only
  removed the doc-comment tokens.

Parts of `wit_kcert` (the files `F₀, …` must have `wit_kfile` certificates):

* `univ`: the gated universe `K.Ugen` (interfaces `K.I<k>`, packages `K.P<j>`, worlds of the
  first package `K.W<w>`), `K.U := K.Ugen fastStr`, and `K.univ`, `K.head`, `K.lookup`,
  `K.items`, `K.ifaces`, `K.worlds`;
* `check`: `K.check : check K.U = true`;
* `body k…` (all interfaces when no `k` is given): `K.B<k>` and `K.body<k>`, the
  `Elab.elabBody` equation of interface `k`: **`Elab.elaborate` split per interface**;
* `env`: `K.env` and `K.envEq`, the `Elab.elabEnv` equation (`elabEnv_eq`);
* `world w…`: `K.Wb<w>` and `K.world<w>`, the `Elab.elabWorld` equation of world `w`;
* `final`: `K.out`, `K.deps`, `K.pkg` (`elabPackage_eq`), `K.valid`, `K.unique`, `K.elab`
  (`elaborate_eq`) and `K.importKD : importKD sel [F₀.src, …] = .ok (K.out, K.deps)`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Lean Elab Command Term
open Silmaril.Wasm.Wit

/-- The string constructor in quoted terms, before it is abstracted (`String.ofList`). -/
def kHole : List Char → String := String.ofList

meta section

/-- The characters of a string, as a list literal of `Char.ofNat` codes. -/
def charsE (s : String) : Expr :=
  s.toList.foldr
    (fun c r => mkApp3 (Lean.mkConst ``List.cons [0]) (Lean.mkConst ``Char)
      (mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) r)
    (mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``Char))

/-- Strings are quoted as `kHole [c₁, …]`. -/
instance (priority := high) kStrToExpr : ToExpr String :=
  ⟨fun s => mkApp (Lean.mkConst ``kHole) (charsE s), Lean.mkConst ``String⟩

deriving instance ToExpr for Silmaril.Wasm.Component.Binary.PrimValType
deriving instance ToExpr for Silmaril.Wasm.Wit.Version
deriving instance ToExpr for Silmaril.Wasm.Wit.PackageName
deriving instance ToExpr for Silmaril.Wasm.Wit.Docs
deriving instance ToExpr for Silmaril.Wasm.Wit.Gate
deriving instance ToExpr for Silmaril.Wasm.Wit.Ty
deriving instance ToExpr for Silmaril.Wasm.Wit.Field
deriving instance ToExpr for Silmaril.Wasm.Wit.Case
deriving instance ToExpr for Silmaril.Wasm.Wit.Label
deriving instance ToExpr for Silmaril.Wasm.Wit.Func
deriving instance ToExpr for Silmaril.Wasm.Wit.ResourceFuncKind
deriving instance ToExpr for Silmaril.Wasm.Wit.ResourceFunc
deriving instance ToExpr for Silmaril.Wasm.Wit.TypeDefKind
deriving instance ToExpr for Silmaril.Wasm.Wit.TypeDef
deriving instance ToExpr for Silmaril.Wasm.Wit.UsePath
deriving instance ToExpr for Silmaril.Wasm.Wit.UseName
deriving instance ToExpr for Silmaril.Wasm.Wit.Use
deriving instance ToExpr for Silmaril.Wasm.Wit.FuncDef
deriving instance ToExpr for Silmaril.Wasm.Wit.IfaceItem
deriving instance ToExpr for Silmaril.Wasm.Wit.Interface
deriving instance ToExpr for Silmaril.Wasm.Wit.Extern
deriving instance ToExpr for Silmaril.Wasm.Wit.WorldExtern
deriving instance ToExpr for Silmaril.Wasm.Wit.IncludeName
deriving instance ToExpr for Silmaril.Wasm.Wit.Include
deriving instance ToExpr for Silmaril.Wasm.Wit.WorldItem
deriving instance ToExpr for Silmaril.Wasm.Wit.World
deriving instance ToExpr for Silmaril.Wasm.Wit.TopUse
deriving instance ToExpr for Silmaril.Wasm.Wit.PackageItem
deriving instance ToExpr for Silmaril.Wasm.Wit.Package
deriving instance ToExpr for Silmaril.Wasm.Wit.Document
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Stability
deriving instance ToExpr for Silmaril.Wasm.Wit.Text.Kw
deriving instance ToExpr for Silmaril.Wasm.Wit.Text.Tok
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.PackageName
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.IfaceName
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Owner
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.TyRef
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Ty
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Labeled
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.TyDefKind
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.TypeDef
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.FuncKind
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Func
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Sig
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.Interface
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.WorldItem
deriving instance ToExpr for Silmaril.Wasm.Wit.Binary.World

/-- A non-dependent function type. -/
def arrE (a b : Expr) : Expr := .forallE `x a b .default

/-- The type of the string constructor. -/
def mkTy : Expr := arrE (mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Char)) (Lean.mkConst ``String)

/-- `fun mk => e`, with `kHole` replaced by `mk`. -/
def genE (e : Expr) : Expr :=
  .lam `mk mkTy (e.replace fun x => if x.isConstOf ``kHole then some (.bvar 0) else none) .default

/-- `K.n applied to kHole` (a generated constant inside a quoted term). -/
def holeApp (n : Lean.Name) : Expr := mkApp (Lean.mkConst n) (Lean.mkConst ``kHole)

/-- A list literal. -/
def listE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x r => mkApp3 (Lean.mkConst ``List.cons [0]) ty x r) (mkApp (Lean.mkConst ``List.nil [0]) ty)

/-- The importer's state on the files: sources, documents, the gated universe and the
elaborated interfaces, environment and package. -/
structure KState where
  srcs : List Src
  docs : List Document
  U : Universe
  items : List (Nat × PackageName × Interface)
  bodies : List Binary.Interface
  env : Binary.Env
  P : Package
  worldsB : List Binary.World

/-- Read the sources of WIT files (paths relative to the Lean source), as `wit_src%`. -/
def readSrcsK (paths : List String) : CommandElabM (List Src) := do
  let source := System.FilePath.mk (← getFileName)
  let some directory := source.parent | throwError "cannot find source directory for {source}"
  paths.mapM fun (p : String) => do
    let file := directory / p
    let text ← try IO.FS.readFile file catch e => throwError "cannot read {file}: {e.toMessageData}"
    let some dir := file.parent | throwError "no directory for {file}"
    let mut hdr := (headerOf text).getD ""
    if hdr.isEmpty then
      let es ← dir.readDir
      for e in es.qsort (·.fileName < ·.fileName) do
        if hdr.isEmpty && e.fileName.endsWith ".wit" then
          if let some h := headerOf (← IO.FS.readFile e.path) then hdr := h
    if hdr.isEmpty then throwError "no package header for {file}"
    return ((hdr, p, text) : Src)

/-- The demoted, glued text of a source, as `wit_srcnd%` gives it. -/
def srcText (s : Src) : String := demoteDocs (withHeader s.1 (demoteParamDocs s.2.2))

/-- The documents of the files (demoted docs). -/
def kstateDocs (paths : List String) : CommandElabM (List Document) := do
  let srcs ← readSrcsK paths
  match srcs.mapM (fun s => Tool.parseText s.2.1 (srcText s)) with
  | .ok ds => pure ds
  | .error e => throwError "WIT importer: {e}"

/-- Run the importer's steps in the evaluator. -/
def kstate (sel : Bool) (paths : List String) : CommandElabM KState := do
  let srcs ← readSrcsK paths
  let ds ← match srcs.mapM (fun s => Tool.parseText s.2.1 (srcText s)) with
    | .ok ds => pure ds
    | .error e => throwError "WIT importer: {e}"
  let U0 := kUniv sel ds
  let U := Universe.gate [] U0
  let c := Elab.Ctx.ofUniverse U
  let some P := U.head? | throwError "no package"
  let items : List (Nat × PackageName × Interface) :=
    (U.zipIdx.flatMap fun (Q, j) => Q.items.filterMap fun | .iface I => some (j, Q.name, I) | _ => none)
  let bodies ← items.mapM fun (_, p, I) =>
    match Elab.elabBody c (.iface ⟨p, I.name⟩) I.items I.docs I.gates with
    | some b => pure b
    | none => throwError "interface {I.name}: no body"
  let env := envOfBodies (items.map (·.2)) bodies
  let worldsB ← P.worlds.mapM fun W =>
    match Elab.elabWorld c env (U.worldIds.length + 1) ⟨P.name, W.name⟩ with
    | .ok w => pure w
    | .error e => throwError "world {W.name}: {e}"
  return { srcs, docs := ds, U, items, bodies, env, P, worldsB }

/-- Add a definition (body exported). -/
def addDefK (n : Lean.Name) (type value : Expr) : CommandElabM Unit := liftTermElabM do
  let decl ← mkDefinitionValInferringUnsafe n [] type value .abbrev
  addDecl (.defnDecl decl) (forceExpose := true)

/-- `K ++ s`. -/
def kn (K : Lean.Name) (s : String) : Lean.Name := K ++ Name.mkSimple s

/-- The identifier of `K ++ s`. -/
def kid (K : Lean.Name) (s : String) : Ident := mkIdent (kn K s)

/-- `.cons a (.cons b … .nil)` for a `List.Forall₂` proof. -/
def forall₂Stx (hs : List Ident) : CommandElabM Term := do
  hs.foldrM (fun h r => `(List.Forall₂.cons $h $r)) (← `(List.Forall₂.nil))

/-- A list literal of terms. -/
def listStx (xs : List Term) : CommandElabM Term := `([$(xs.toArray),*])

/-- The interfaces of the first package, as indices into the interface list. -/
def firstIfaces (st : KState) : List Nat :=
  (st.items.zipIdx.filter fun ((j, _, _), _) => j = 0).map (·.2)

/-- The generated universe, interfaces and packages. -/
def univDecls (K : Lean.Name) (st : KState) : CommandElabM Unit := do
  let ifaceT := Lean.mkConst ``Silmaril.Wasm.Wit.Interface
  for ((_, _, I), k) in st.items.zipIdx do
    addDefK (kn K s!"I{k}") (arrE mkTy ifaceT) (genE (toExpr I))
  let worldT := Lean.mkConst ``Silmaril.Wasm.Wit.World
  for (W, w) in st.P.worlds.zipIdx do
    addDefK (kn K s!"W{w}") (arrE mkTy worldT) (genE (toExpr W))
  let pkgT := Lean.mkConst ``Silmaril.Wasm.Wit.Package
  let itemT := Lean.mkConst ``Silmaril.Wasm.Wit.PackageItem
  let mut k := 0
  for (Q, j) in st.U.zipIdx do
    let mut its : List Expr := []
    let mut w := 0
    for it in Q.items do
      match it with
      | .iface _ =>
        its := its ++ [mkApp (Lean.mkConst ``Silmaril.Wasm.Wit.PackageItem.iface) (holeApp (kn K s!"I{k}"))]
        k := k + 1
      | .world W =>
        if j = 0 then
          its := its ++ [mkApp (Lean.mkConst ``Silmaril.Wasm.Wit.PackageItem.world) (holeApp (kn K s!"W{w}"))]
          w := w + 1
        else its := its ++ [toExpr (PackageItem.world W)]
      | it => its := its ++ [toExpr it]
    let v := mkApp3 (Lean.mkConst ``Silmaril.Wasm.Wit.Package.mk) (toExpr Q.name) (listE itemT its) (toExpr Q.docs)
    addDefK (kn K s!"P{j}") (arrE mkTy pkgT) (genE v)
  let univT := mkApp (Lean.mkConst ``List [0]) pkgT
  addDefK (kn K "Ugen") (arrE mkTy univT)
    (genE (listE pkgT ((List.range st.U.length).map fun j => holeApp (kn K s!"P{j}"))))
  addDefK (kn K "U") (Lean.mkConst ``Silmaril.Wasm.Wit.Universe)
    (mkApp (Lean.mkConst (kn K "Ugen")) (Lean.mkConst ``fastStr))

end

/-- `wit_kfile F "a.wit"`: the parse certificate of one file (see the module documentation). -/
syntax (name := witKFile) "wit_kfile " ident ppSpace str : command

@[command_elab witKFile] meta def elabWitKFile : CommandElab := fun stx => do
  let `(wit_kfile $f:ident $p:str) := stx | throwUnsupportedSyntax
  let F := f.getId
  let st ← kstateDocs [p.getString]
  let some d := st.head? | throwError "no document"
  elabCommand (← `(noncomputable def $(kid F "src") : List Char := wit_srcnd% $p))
  addDefK (kn F "d") (arrE mkTy (Lean.mkConst ``Silmaril.Wasm.Wit.Document)) (genE (toExpr d))
  elabCommand (← `(theorem $(kid F "parse") :
    parseCharsK $(kid F "src") = some ($(kid F "d") String.ofList) := by kernel_rfl))

/-- `wit_kcert K part n… from ver sel [F₀, …] "a.wit" …`: see the module documentation. -/
syntax (name := witKCert) "wit_kcert " ident ident (ppSpace num)* " from " ident ident
  " [" ident,* "]" (ppSpace str)+ : command

@[command_elab witKCert] meta def elabWitKCert : CommandElab := fun stx => do
  let `(wit_kcert $k:ident $part:ident $ns:num* from $_v:ident $s:ident [$fs:ident,*] $ps:str*) := stx
    | throwUnsupportedSyntax
  let K := k.getId
  let sel := s.getId == `ifaces
  let selS : Term ← if sel then `(true) else `(false)
  let paths := ps.toList.map (·.getString)
  let files := fs.getElems.toList.map (·.getId)
  if files.length != paths.length then throwError "one file certificate per file"
  let st ← kstate sel paths
  let nums := ns.toList.map (·.getNat)
  let ds ← listStx (← (files.mapM fun F => `($(kid F "d") String.ofList)))
  let srcs ← listStx (files.map fun F => (kid F "src" : Term))
  let P0 : Term ← `($(kid K "P0") fastStr)
  let itemsStx : CommandElabM Term := do
    listStx (← (st.items.zipIdx.mapM fun ((j, _, _), k) =>
      `((($(kid K s!"P{j}") fastStr).name, $(kid K s!"I{k}") fastStr))))
  match part.getId with
  | `univ =>
    univDecls K st
    elabCommand (← `(theorem $(kid K "univ0") :
      Universe.gate [] (kUniv $selS $ds) = $(kid K "Ugen") String.ofList := by kernel_rfl))
    elabCommand (← `(theorem $(kid K "univ") : Universe.gate [] (kUniv $selS $ds) = $(kid K "U") :=
      ($(kid K "univ0")).trans (congrArg $(kid K "Ugen") fastStr_eq.symm)))
    elabCommand (← `(theorem $(kid K "head0") :
      (kUniv $selS $ds).head?.map Package.name = some ($(kid K "P0") String.ofList).name := by
        kernel_rfl))
    elabCommand (← `(theorem $(kid K "head") :
      (kUniv $selS $ds).head?.map Package.name = some ($P0).name := by
        rw [$(kid K "head0"):ident, fastStr_eq]))
    elabCommand (← `(theorem $(kid K "lookup") :
      Elab.lookupPkg $(kid K "U") ($P0).name = .ok $P0 := by kernel_rfl))
    elabCommand (← `(theorem $(kid K "items") : envItems $(kid K "U") = $(← itemsStx) := by kernel_rfl))
    let fi ← listStx (← ((firstIfaces st).mapM fun k => `($(kid K s!"I{k}") fastStr)))
    elabCommand (← `(theorem $(kid K "ifaces") : ($P0).ifaces = $fi := by kernel_rfl))
    let fw ← listStx (← ((List.range st.P.worlds.length).mapM fun w => `($(kid K s!"W{w}") fastStr)))
    elabCommand (← `(theorem $(kid K "worlds") : ($P0).worlds = $fw := by kernel_rfl))
  | `check =>
    elabCommand (← `(theorem $(kid K "check") : check $(kid K "U") = true := by decide +kernel))
  | `body =>
    let bT := Lean.mkConst ``Silmaril.Wasm.Wit.Binary.Interface
    let ks := if nums.isEmpty then List.range st.items.length else nums
    for k in ks do
      let some (j, _, _) := st.items[k]? | throwError "no interface {k}"
      let some b := st.bodies[k]? | throwError "no body {k}"
      addDefK (kn K s!"B{k}") (arrE mkTy bT) (genE (toExpr b))
      let I := kid K s!"I{k}"
      elabCommand (← `(theorem $(kid K s!"body{k}") :
        Elab.elabBody (Elab.Ctx.ofUniverse $(kid K "U"))
          (.iface ⟨($(kid K s!"P{j}") fastStr).name, ($I fastStr).name⟩) ($I fastStr).items
          ($I fastStr).docs ($I fastStr).gates = some ($(kid K s!"B{k}") fastStr) := by decide +kernel))
  | `env =>
    let bs ← listStx (← ((List.range st.items.length).mapM fun k => `($(kid K s!"B{k}") fastStr)))
    elabCommand (← `(noncomputable def $(kid K "env") : Silmaril.Wasm.Wit.Binary.Env :=
      envOfBodies $(← itemsStx) $bs))
    let hs ← forall₂Stx ((List.range st.items.length).map fun k => kid K s!"body{k}")
    elabCommand (← `(theorem $(kid K "envEq") :
      Elab.elabEnv (Elab.Ctx.ofUniverse $(kid K "U")) = .ok $(kid K "env") :=
        elabEnv_eq $(kid K "items") $hs))
  | `world =>
    let wT := Lean.mkConst ``Silmaril.Wasm.Wit.Binary.World
    let ws := if nums.isEmpty then List.range st.worldsB.length else nums
    for w in ws do
      let some b := st.worldsB[w]? | throwError "no world {w}"
      addDefK (kn K s!"Wb{w}") (arrE mkTy wT) (genE (toExpr b))
      elabCommand (← `(theorem $(kid K s!"world{w}") :
        Elab.elabWorld (Elab.Ctx.ofUniverse $(kid K "U")) $(kid K "env")
          ((Elab.Ctx.ofUniverse $(kid K "U")).U.worldIds.length + 1)
          ⟨($P0).name, ($(kid K s!"W{w}") fastStr).name⟩ =
          .ok ($(kid K s!"Wb{w}") fastStr) := by decide +kernel))
  | `final =>
    let fis := firstIfaces st
    let bs ← listStx (← (fis.mapM fun k => `($(kid K s!"B{k}") fastStr)))
    let fi ← listStx (← (fis.mapM fun k => `($(kid K s!"I{k}") fastStr)))
    let fw ← listStx (← ((List.range st.P.worlds.length).mapM fun w => `($(kid K s!"W{w}") fastStr)))
    let wbs ← listStx (← ((List.range st.P.worlds.length).mapM fun w => `($(kid K s!"Wb{w}") fastStr)))
    elabCommand (← `(noncomputable def $(kid K "out") : Silmaril.Wasm.Wit.Binary.Package :=
      ⟨Elab.pkgName ($P0).name, ($P0).docs.contents,
        List.zipWith (fun (I : Silmaril.Wasm.Wit.Interface) b => (I.name, b)) $fi $bs,
        List.zipWith (fun (W : Silmaril.Wasm.Wit.World) w => (W.name, w)) $fw $wbs⟩))
    elabCommand (← `(noncomputable def $(kid K "deps") : Silmaril.Wasm.Wit.Binary.Env :=
      depsOf $(kid K "env") ($P0).name))
    let hb ← forall₂Stx (fis.map fun k => kid K s!"body{k}")
    let hw ← forall₂Stx ((List.range st.P.worlds.length).map fun w => kid K s!"world{w}")
    elabCommand (← `(theorem $(kid K "pkg") :
      Elab.elabPackage (Elab.Ctx.ofUniverse $(kid K "U")) $(kid K "env") $P0 = .ok $(kid K "out") :=
        elabPackage_eq $(kid K "ifaces") $(kid K "worlds") $hb $hw))
    elabCommand (← `(theorem $(kid K "valid") :
      Elab.Package.validB $(kid K "out") (depsOf $(kid K "env") ($P0).name) = true := by decide +kernel))
    elabCommand (← `(theorem $(kid K "unique") :
      Elab.Package.namesUniqueB $(kid K "out") = true := by decide +kernel))
    elabCommand (← `(theorem $(kid K "elab") :
      Elab.elaborate (kUniv $selS $ds) ($P0).name [] = .ok ($(kid K "out"), $(kid K "deps")) :=
        elaborate_eq $(kid K "univ") $(kid K "check") $(kid K "lookup") $(kid K "envEq") $(kid K "pkg")
          $(kid K "valid") $(kid K "unique")))
    let hp ← forall₂Stx (files.map fun F => kid F "parse")
    elabCommand (← `(theorem $(kid K "importKD") :
      importKD $selS $srcs = .ok ($(kid K "out"), $(kid K "deps")) :=
        importKD_eq $hp $(kid K "head") $(kid K "elab")))
  | p => throwError "unknown part {p}"

/-- `wit_klex F "a.wit"`: the tokens of the demoted text are those of the text with its docs
without the doc-comment tokens (see the module documentation). Needs `wit_kfile F`. -/
syntax (name := witKLex) "wit_klex " ident ppSpace str : command

@[command_elab witKLex] meta def elabWitKLex : CommandElab := fun stx => do
  let `(wit_klex $f:ident $p:str) := stx | throwUnsupportedSyntax
  let F := f.getId
  let some s := (← readSrcsK [p.getString]).head? | throwError "no source"
  let some toks := Text.lex (srcText s).toList | throwError "not WIT text the lexer accepts"
  let tokT := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Silmaril.Wasm.Wit.Text.Tok)
  elabCommand (← `(noncomputable def $(kid F "full") : List Char := wit_src% $p))
  addDefK (kn F "toks") (arrE mkTy tokT) (genE (toExpr toks))
  elabCommand (← `(theorem $(kid F "lexSrc") :
    lexK ($(kid F "src").length + 1) $(kid F "src") = some ($(kid F "toks") String.ofList) := by
      kernel_rfl))
  elabCommand (← `(theorem $(kid F "lexFull") :
    (lexK ($(kid F "full").length + 1) $(kid F "full")).map (List.filter notDoc) =
      some ($(kid F "toks") String.ofList) := by kernel_rfl))
  elabCommand (← `(theorem $(kid F "lexNd") :
    (lexK ($(kid F "full").length + 1) $(kid F "full")).map (List.filter notDoc) =
      lexK ($(kid F "src").length + 1) $(kid F "src") :=
    ($(kid F "lexFull")).trans ($(kid F "lexSrc")).symm))
  elabCommand (← `(theorem $(kid F "parseNd") : parseCharsK $(kid F "src") = parseTokK $(kid F "full") :=
    parseCharsK_of_lex $(kid F "lexNd")))

end Silmaril.Wasi.Versions.WitImport
