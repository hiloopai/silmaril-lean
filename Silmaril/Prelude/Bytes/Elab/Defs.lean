module

public import Silmaril.Prelude.Bytes.Thms
public meta import Lean.Elab.Command
public meta import Lean.Compiler.NoncomputableAttr
public meta import Silmaril.Prelude.Bytes.Defs

/-! # Kernel bytes from files and chunk literals

```
kbytes_def hello from_file "../../examples/dyn/pinned/hello-gcc"
-- def hello.chunks : List Nat := [c₀, c₁, …]         -- 4 KiB little-endian literals
-- def hello : Silmaril.KBytes := node 15960 (node …) …  -- the canonical tree, written out
-- theorem hello.eq_ofChunks : hello = KBytes.ofChunks 4096 15960 hello.chunks
-- theorem hello.wf : hello.wf = true
-- theorem hello.len_eq : hello.len = 15960
```

The path is relative to the directory of the current source file, as for `include_bytes`. Lake
does not track the file (see `Silmaril.Data.IncludeBytes`). Reading the file is trusted
elaboration, as for `include_bytes`: the definitions *are* the literals, and every theorem about
`hello` is about them. The definitions are `noncomputable` unless `computable` is given. A
native run (`edge_decide`) needs compiled code, and compiling 4 KiB literals costs about 14 s per
MiB (`Silmaril.Data.IncludeBytes`).

`eq_ofChunks` is checked by the kernel, which evaluates `ofChunks` on the literal list (no byte
is decoded) and compares the result with the written-out tree. `wf` follows from it without
evaluation. `kbytes_def x of_chunks c n cs` does the same for the literals `c n cs` of an
existing term (`Silmaril.Data.IncludeBytes.Kernel` uses it for `include_bytes` definitions).
-/

@[expose] public meta section

namespace Silmaril.KBytes.Elab

open Lean Elab Command Meta

/-- The chunk size of canonical files. -/
def chunkSize : Nat := 4096

/-- `leVal` of the bytes `b[lo:hi]`, by divide and conquer. -/
partial def encodeRange (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi - lo ≤ 64 then
    (List.range (hi - lo)).foldr (fun i acc => (b.get! (lo + i)).toNat + 256 * acc) 0
  else
    let mid := (lo + hi) / 2
    encodeRange b lo mid + (encodeRange b mid hi <<< (8 * (mid - lo)))

/-- The chunk literals of `b`. -/
def chunksOf (b : ByteArray) (c : Nat) : Array Nat :=
  (Array.range ((b.size + c - 1) / c)).map fun i => encodeRange b (i * c) (min b.size ((i + 1) * c))

/-- The canonical tree over chunks `[i, i + k)` holding `n` bytes, mirroring `ofChunksAux`.
Returns the term and its length. -/
partial def treeExpr (c : Nat) (lits : Array Expr) (i k n : Nat) : Expr × Nat :=
  if k ≤ 1 then
    if k == 0 then (mkApp2 (mkConst ``KBytes.leaf) (mkNatLit 0) (mkNatLit 0), 0)
    else
      let m := min c n
      (mkApp2 (mkConst ``KBytes.leaf) (mkNatLit m) lits[i]!, m)
  else
    let p := KBytes.leftLeaves k
    let (l, nl) := treeExpr c lits i p (min n (p * c))
    let (r, nr) := treeExpr c lits (i + p) (k - p) (n - p * c)
    (mkApp3 (mkConst ``KBytes.node) (mkNatLit (nl + nr)) l r, nl + nr)

def listExpr (lits : Array Expr) : Expr :=
  lits.foldr (init := mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))
    fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) x acc

def addDefn (name : Name) (type value : Expr) (computable : Bool) : CoreM Unit := do
  let decl := Declaration.defnDecl
    { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  if computable then addAndCompile decl
  else
    addDecl decl
    modifyEnv (addNoncomputable · name)

def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name, levelParams := [], type, value })

def eqExpr (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) ty a b

/-- Define `name`, `name.chunks`, `name.eq_ofChunks`, `name.wf` and `name.len_eq` for `n`
bytes in the chunk literals `lits` (chunk size `c`). -/
def defineKBytes (name : Name) (c n : Nat) (lits : Array Nat) (computable : Bool) :
    CoreM Unit := do
  if c == 0 then throwError "kbytes_def: chunk size 0"
  unless (n + c - 1) / c == lits.size do
    throwError "kbytes_def: {lits.size} chunks cannot hold exactly {n} bytes of {c}"
  let litEs := lits.map mkNatLit
  let kb := mkConst ``KBytes
  let listNat := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  addDefn (name ++ `chunks) listNat (listExpr litEs) computable
  let (tree, len) := treeExpr c litEs 0 lits.size n
  unless len == n do throwError "kbytes_def: internal error: tree length {len} ≠ {n}"
  addDefn name kb tree computable
  let ofC := mkApp3 (mkConst ``KBytes.ofChunks) (mkNatLit c) (mkNatLit n) (mkConst (name ++ `chunks))
  let hEq := name ++ `eq_ofChunks
  addThm hEq (eqExpr kb (mkConst name) ofC) (mkApp2 (mkConst ``Eq.refl [1]) kb (mkConst name))
  let boolT := mkConst ``Bool
  addThm (name ++ `wf) (eqExpr boolT (mkApp (mkConst ``KBytes.wf) (mkConst name)) (mkConst ``Bool.true))
    (mkApp4 (mkConst ``KBytes.wf_of_eq_ofChunks) (mkConst name) (mkNatLit c) (mkNatLit n)
      (mkConst (name ++ `chunks)) |>.app (mkConst hEq))
  addThm (name ++ `len_eq) (eqExpr (mkConst ``Nat) (mkApp (mkConst ``KBytes.len) (mkConst name)) (mkNatLit n))
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit n))

/-- Read `path` relative to the directory of the current source file. -/
def readRelative (path : String) : CoreM ByteArray := do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "cannot locate the current source file"
  IO.FS.readBinFile (dir / path)

/-- `kbytes_def x from_file "path" [computable]`: the canonical kernel bytes of a file. -/
syntax (name := kbytesFromFile) "kbytes_def " ident &" from_file " str (&" computable")? : command

/-- `kbytes_def x of_chunks c n cs [computable]`: the canonical tree of chunk literals. -/
syntax (name := kbytesOfChunks) "kbytes_def " ident &" of_chunks " num num term
  (&" computable")? : command

@[command_elab kbytesFromFile] def elabFromFile : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let b ← liftCoreM <| readRelative (stx[3].isStrLit?.getD "")
  liftCoreM <| defineKBytes name chunkSize b.size (chunksOf b chunkSize) (!stx[4].isNone)

/-- The natural-number literals of a list literal. -/
partial def natLits? (e : Expr) : Option (Array Nat) :=
  go e #[]
where
  go (e : Expr) (acc : Array Nat) : Option (Array Nat) :=
    if e.isAppOfArity ``List.nil 1 then some acc
    else if e.isAppOfArity ``List.cons 3 then
      match e.appFn!.appArg!.rawNatLit? <|> e.appFn!.appArg!.nat? with
      | some n => go e.appArg! (acc.push n)
      | none => none
    else none

@[command_elab kbytesOfChunks] def elabOfChunks : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let c := stx[3].isNatLit?.getD 0
  let n := stx[4].isNatLit?.getD 0
  let cs ← liftTermElabM do
    let e ← Term.elabTerm stx[5] (some (mkApp (mkConst ``List [0]) (mkConst ``Nat)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- Follow constant definitions to the literal list.
    let mut e := e
    for _ in [0:16] do
      if let some lits := natLits? e then return lits
      match e.getAppFn.constName? with
      | some c =>
        let some info := (← getEnv).find? c | break
        let some v := info.value? (allowOpaque := true) | break
        e := v.beta e.getAppArgs
      | none => break
    throwError "kbytes_def: {stx[5]} is not a list of natural-number literals"
  liftCoreM <| defineKBytes name c n cs (!stx[6].isNone)

end Silmaril.KBytes.Elab
