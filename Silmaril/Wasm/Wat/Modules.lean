module

public meta import Silmaril.Wasm.Wat.Instructions

/-! # WAT module declarations

A first pass records the separate index spaces and explicit types, allowing
forward references. A second pass expands bodies and interns implicit types.
Only the documented scalar Wasm1/Lime1 text subset is accepted.
-/

public meta section

open Lean
namespace Silmaril.Wasm.Wat

def declared (origin : Node) (kind : String) (args : List Node) : Build Unit := do
  let (name, _) ← takeName args
  let t ← get
  match kind with
  | "func" => do
      let names ← addName origin t.funcs name
      modify fun t => { t with funcs := names }
  | "global" => do
      let names ← addName origin t.globals name
      modify fun t => { t with globals := names }
  | "memory" => do
      let names ← addName origin t.memories name
      modify fun t => { t with memories := names }
  | "table" => do
      let names ← addName origin t.tables name
      modify fun t => { t with tables := names }
  | _ => watError origin s!"unsupported declaration kind '{kind}'"

def collect (fields : List Node) : Build Unit := do
  let mut definitions := false
  for n in fields do
    let (kind, args) ← field n
    if kind == "type" then
      let (name, args) ← takeName args
      let [.list _ (.atom _ "func" :: args)] := args |
        watError n "type declaration requires one function type"
      let (sig, _, rest) ← signature args false
      unless rest.isEmpty do watError n "unsupported function type syntax"
      checkSignature n sig
      let names ← addName n (← get).typeNames name
      modify fun t => { t with types := t.types ++ [sig], typeNames := names }
    else if kind == "import" then
      if definitions then watError n "imports must precede definitions"
      let [mod, name, desc] := args | watError n "import requires module/name strings and a descriptor"
      discard <| nameString mod
      discard <| nameString name
      let (kind, args) ← field desc
      declared desc kind args
    else if ["func", "global", "memory", "table"].contains kind then
      definitions := true
      declared n kind args
    else if !["export", "start", "elem", "data"].contains kind then
      watError n s!"unsupported module field '{kind}'"

def limits (origin : Node) (nodes : List Node) : MacroM (Term × List Node) := do
  let first :: rest := nodes | watError origin "limits require a minimum"
  let lo ← checked first (unsigned (← atom first))
  unless lo < Nat.pow 2 32 do watError first "limit exceeds unsigned 32-bit range"
  let mut rest := rest
  let mut hi : Term ← `(none)
  if let next :: tail := rest then
    if next.atom?.any (fun s => s.toList.head?.any Char.isDigit) then
      let value ← checked next (unsigned (← atom next))
      unless value < Nat.pow 2 32 do watError next "limit exceeds unsigned 32-bit range"
      hi ← `(some $(natTerm value))
      rest := tail
  return (← `(Silmaril.Wasm.V1.Limits.mk $(natTerm lo) $hi), rest)

def globalType (n : Node) : MacroM Term := do
  let (mutability, value) ← match n with
    | .list _ [.atom _ "mut", ty] => pure ("var", ← valType ty)
    | _ => pure ("const", ← valType n)
  let m ← coreTerm "Mutability" mutability
  let v ← valTerm value
  `(Silmaril.Wasm.V1.GlobalType.mk $m $v)

def memoryType (origin : Node) (nodes : List Node) : MacroM Term := do
  let (lim, rest) ← limits origin nodes
  unless rest.isEmpty do watError origin "unsupported memory declaration syntax"
  `(Silmaril.Wasm.V1.MemoryType.mk $lim)

def tableType (origin : Node) (nodes : List Node) : MacroM Term := do
  let (lim, rest) ← limits origin nodes
  unless rest.length == 1 && rest.head!.atom? == some "funcref" do
    watError origin "table declaration requires limits followed by funcref"
  `(Silmaril.Wasm.V1.TableType.mk $lim)

def localGroups (nodes : List Node) (params : Names) : MacroM (Names × List Term × List Node) := do
  let mut names := params
  let mut types := []
  let mut rest := nodes
  while let n :: tail := rest do
    if n.head? != some "local" then break
    let .list _ (_ :: args) := n | watError n "invalid local group"
    let (name, args) ← takeName args
    if name.isSome && args.length != 1 then watError n "named local must have exactly one type"
    for arg in args do
      names ← addName n names name
      types := types ++ [← valTerm (← valType arg)]
    rest := tail
  return (names, types, rest)

def exportTerm (kind : String) (i : Nat) (name : String) : MacroM Term := do
  let index ← applyTerm ("Silmaril.Wasm.V1.ExternIdx." ++ kind) #[← indexTerm i]
  `(Silmaril.Wasm.V1.Export.mk $(quote name) $index)

def addExport (origin : Node) (f : Fields) (kind : String) (i : Nat) (name : String) :
    MacroM Fields :=
  addExportWith exportTerm origin f kind i name

def exportIndex (origin : Node) (kind : String) (ref : Node) : Build Nat := do
  let t ← get
  match kind with
  | "func" => index t.funcs "function" ref
  | "global" => index t.globals "global" ref
  | "memory" => index t.memories "memory" ref
  | "table" => index t.tables "table" ref
  | _ => watError origin "unsupported export kind"

def offset (origin : Node) (nodes : List Node) (kind : String) :
    Build (Nat × List Term × List Node) := do
  let mut rest := nodes
  let mut i := 0
  if let n :: tail := rest then
    if n.atom?.isSome then
      i ← exportIndex origin kind n
      rest := tail
  let n :: remaining := rest | watError origin "active segment requires an offset expression"
  let expr := match n with
    | .list _ (.atom _ "offset" :: expr) => expr
    | .list .. => [n]
    | _ => []
  if expr.isEmpty then watError n "active segment requires a folded offset expression"
  let (body, _) ← instructions {} expr
  return (i, body, remaining)

def elaborateFields (fields : List Node) : Build Fields := do
  let mut f : Fields := {}
  for n in fields do
    let (kind, args) ← field n
    let p := (← get).profile
    if kind == "type" then continue
    if kind == "import" then
      let [mod, name, desc] := args | watError n "invalid import"
      let (kind, args) ← field desc
      let (_, args) ← takeName args
      let term ← match kind with
        | "func" => do
          let (i, _, _, rest) ← typeUse desc args
          unless rest.isEmpty do watError desc "imported function cannot have locals or a body"
          f := { f with funcCount := f.funcCount + 1 }
          applyTerm "Silmaril.Wasm.V1.ImportDesc.func" #[← indexTerm i]
        | "global" => do
          let [ty] := args | watError desc "global import requires one global type"
          f := { f with globalCount := f.globalCount + 1 }
          applyTerm "Silmaril.Wasm.V1.ImportDesc.global" #[← globalType ty]
        | "memory" => do
          f := { f with memoryCount := f.memoryCount + 1 }
          applyTerm "Silmaril.Wasm.V1.ImportDesc.memory" #[← memoryType desc args]
        | "table" => do
          f := { f with tableCount := f.tableCount + 1 }
          applyTerm "Silmaril.Wasm.V1.ImportDesc.table" #[← tableType desc args]
        | _ => watError desc "unsupported import"
      let mod ← nameString mod
      let name ← nameString name
      let term ← `(Silmaril.Wasm.V1.Import.mk $(quote mod) $(quote name) $term)
      f := { f with imports := f.imports ++ [term] }
    else if ["func", "global", "memory", "table"].contains kind then
      let (_, args) ← takeName args
      let (exports, args) ← exportsPrefix args
      let i := match kind with
        | "func" => f.funcCount | "global" => f.globalCount
        | "memory" => f.memoryCount | _ => f.tableCount
      for name in exports do f ← addExport n f kind i name
      if kind == "func" then
        let (ty, _, params, args) ← typeUse n args
        let (locals, types, body) ← localGroups args params
        let (body, _) ← instructions ⟨locals, [none]⟩ body
        let term ← applyTerm (p.ns ++ ".Func.mk") #[← indexTerm ty, ← listTerm types, ← listTerm body]
        f := { f with funcs := f.funcs ++ [term], funcCount := f.funcCount + 1 }
      else if kind == "global" then
        let ty :: body := args | watError n "global requires a type and initializer"
        let (body, _) ← instructions {} body
        let term ← applyTerm (p.ns ++ ".Global.mk") #[← globalType ty, ← listTerm body]
        f := { f with globals := f.globals ++ [term], globalCount := f.globalCount + 1 }
      else if kind == "memory" then
        f := { f with memories := f.memories ++ [← memoryType n args], memoryCount := f.memoryCount + 1 }
      else
        f := { f with tables := f.tables ++ [← tableType n args], tableCount := f.tableCount + 1 }
    else if kind == "export" then
      let [name, .list _ [kind, ref]] := args | watError n "export requires a name and (kind index)"
      let kind ← atom kind
      let i ← exportIndex n kind ref
      f ← addExport n f kind i (← nameString name)
    else if kind == "start" then
      if f.start.isSome then watError n "duplicate start declaration"
      let [ref] := args | watError n "start requires one function index"
      f := { f with start := some (← indexTerm (← exportIndex n "func" ref)) }
    else if kind == "elem" then
      let (i, body, refs) ← offset n args "table"
      let refs ← refs.mapM (fun ref => do indexTerm (← exportIndex n "func" ref))
      let term ← applyTerm (p.ns ++ ".Elem.mk") #[← indexTerm i, ← listTerm body, ← listTerm refs]
      f := { f with elems := f.elems ++ [term] }
    else if kind == "data" then
      let (i, body, strings) ← offset n args "memory"
      let mut bytes := ByteArray.empty
      for s in strings do
        let .string _ bs := s | watError s "data segment requires byte strings"
        bytes := bytes ++ bs
      let bs := bytes.data.map (fun b => natTerm b.toNat)
      let data ← `(ByteArray.mk #[$bs,*])
      let term ← applyTerm (p.ns ++ ".Data.mk") #[← indexTerm i, ← listTerm body, data]
      f := { f with data := f.data ++ [term] }
    else watError n s!"unsupported module field '{kind}'"
  return f

def parsed (text : String) : MacroM (List Node) :=
  match parse text with
  | .ok nodes => pure nodes
  | .error message => Macro.throwError message

def moduleTerm (p : Profile) (text : String) : MacroM Term := do
  let nodes ← parsed text
  let [.list _ (.atom _ "module" :: args)] := nodes |
    Macro.throwError "WAT quotation requires exactly one (module ...)"
  let (_, fields) ← takeName args
  let build : Build Fields := do collect fields; elaborateFields fields
  let (f, t) ← build.run { profile := p }
  let tys ← listTerm (← t.types.mapM Signature.term)
  let imports ← listTerm f.imports
  let funcs ← listTerm f.funcs
  let globals ← listTerm f.globals
  let tables ← listTerm f.tables
  let memories ← listTerm f.memories
  let elems ← listTerm f.elems
  let data ← listTerm f.data
  let start ← match f.start with | none => `(none) | some s => `(some $s)
  let exports ← listTerm f.exports
  let ty := termName (p.ns ++ ".Module")
  `(show $ty from {
    types := $tys
    imports := $imports
    funcs := $funcs
    globals := $globals
    tables := $tables
    memories := $memories
    elems := $elems
    data := $data
    start := $start
    exports := $exports })

def expressionTerm (p : Profile) (text : String) : MacroM Term := do
  let nodes ← parsed text
  let ((terms, _), t) ← (instructions {} nodes).run { profile := p }
  unless t.types.isEmpty do Macro.throwError "WAT expression quotation cannot synthesize module types"
  let result ← listTerm terms
  let ty := termName (p.ns ++ ".Expr")
  `(show $ty from $result)

end Silmaril.Wasm.Wat
