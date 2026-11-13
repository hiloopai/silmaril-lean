module

public import Silmaril.Prelude.Trust.Elab.Defs
public meta import Lake.Toml

/-! # The trust dump for the project database (`silmaril.trust-dump.v0.1`)

`#trust_export "path"` writes one JSON document that `sil project sqlite --trust PATH` reads
(default path `.lake/silmaril/trust.json`; `scripts/trust-export.sh` drives it). It is built
from the registry, the recorded uses and the loaded policy. Nothing in it is hard-coded about
native-evaluation axioms: their names come from the proofs.

```
{ "schema": "silmaril.trust-dump.v0.1", "toolchain": …, "producer": …,
  "procedures": [{ "name", "kind", "implemented", "doc", "backends": [{ "role", … }] }],
  "sets":       [{ "name", "doc", "all", "members": [{ "kind": "procedure" | "set", "name" }] }],
  "policies":   [{ "scope": "root" | "region" | "module-prefix", "name", "allow", "max",
                   "deps", "axioms", "origin" }],
  "modules":    [{ "name", "region", "source", "source_sha256", "imports" }],
  "uses":       [{ "module", "decl", "procedure", "backend", "profile", "axiom", "verified" }],
  "excluded":   [{ "module", "coverage": "excluded" | "unsupported", "reason" }] }
```

A procedure's identity is its name, independent of its backends. `kind` is `decider`
(`native_decider`), `declared` (`ProcDecl`, two backends), `tactic` (`native_tactic`), or
`named` (named by a trust set but not registered in this environment; `implemented` is
false). `uses.verified` applies the audit's provenance rule (`verifiedNative`). Modules are
those imported by the exporting file whose names start with `Silmaril`; a module listed in
`scripts/trust-profile-exclude.txt` for the current profile is reported under `excluded`.
-/

public meta section

namespace Silmaril.Trust.Export

open Lean Elab Command Meta

def sha256 (data : ByteArray) : ByteArray := Id.run do
  let k : Array UInt32 := #[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
  let rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
  -- Padding (FIPS 180-4 §5.1.1).
  let bitLen := data.size * 8
  let mut msg := data.push 0x80
  while msg.size % 64 != 56 do
    msg := msg.push 0
  for i in [0:8] do
    msg := msg.push (UInt8.ofNat (bitLen >>> (8 * (7 - i))))
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  let mut w : Array UInt32 := Array.replicate 64 0
  for blk in [0:msg.size / 64] do
    let base := blk * 64
    for t in [0:16] do
      let o := base + 4 * t
      w := w.set! t ((msg.get! o).toUInt32 <<< 24 ||| (msg.get! (o+1)).toUInt32 <<< 16 |||
        (msg.get! (o+2)).toUInt32 <<< 8 ||| (msg.get! (o+3)).toUInt32)
    for t in [16:64] do
      let x := w[t-15]!
      let y := w[t-2]!
      let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
      let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
      w := w.set! t (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for t in [0:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let t1 := hh + S1 + ch + k[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + mj
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let mut out := ByteArray.empty
  for x in h do
    out := out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8
  return out
def hex (b : ByteArray) : String :=
  b.foldl (init := "") fun s x =>
    let d := Nat.toDigits 16 x.toNat
    s ++ (if d.length == 1 then "0" else "") ++ String.ofList d

def schema : String := "silmaril.trust-dump.v0.1"

def nameJ (n : Name) : Json := toJson (toString n)

/-- The regions of `regions.toml` (for classifying modules and policy scopes). -/
def regions (root : System.FilePath) : IO (Array String) := do
  let text ← IO.FS.readFile (root / "regions.toml")
  let ictx := Parser.mkInputContext text "regions.toml"
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .error _ => return #[]
  | .ok t =>
    let mut out := #[]
    for key in [`region, `view] do
      if let some (.array _ rs) := t.find? key then
        for r in rs do
          if let .table _ rt := r then
            if let some (.string _ n) := rt.find? `name then out := out.push n
    return out

def regionOf (regs : Array String) (mod : Name) : Json :=
  match mod.components with
  | `Silmaril :: `Proofs :: r :: _ | `Silmaril :: `Raw :: r :: _ | `Silmaril :: r :: _ =>
    if regs.contains r.toString then toJson r.toString else Json.null
  | _ => Json.null

def procedureJ (p : Procedure) : Json :=
  let backend (role : String) (fields : List (String × Json)) : Json :=
    Json.mkObj ([("role", toJson role)] ++ fields)
  let (kind, backends) : String × List Json := match p.axiomTag with
    | some tag =>
      ("tactic", [backend "native" [("evaluated_constant", nameJ p.fn),
        ("axiom_pattern", toJson s!"<decl>._native.{tag}.ax_<n>"),
        ("components", toJson p.components), ("toolchain", toJson p.toolchain),
        ("fallback_coverage", toJson p.fallbackCoverage)]])
    | none =>
      let native := match p.native with
        | some (nf, eq) => backend "native" [("function", nameJ nf), ("equation", nameJ eq),
            ("axiom_pattern", toJson s!"<decl>._native.edge.{p.name}.ax_<n>")]
        | none => backend "native" [("function", nameJ p.fn),
            ("axiom_pattern", toJson s!"<decl>._native.edge.{p.name}.ax_<n>")]
      let kernel := if p.kernel then [backend "kernel" [("function", nameJ p.fn)]] else []
      ("decider", native :: kernel)
  Json.mkObj [("name", nameJ p.name), ("kind", toJson kind), ("implemented", toJson true),
    ("doc", toJson p.doc), ("module", nameJ p.module), ("format", nameJson p.format),
    ("sound", nameJson p.sound), ("backends", toJson backends)]

def declaredJ (d : DeclView) : Json :=
  let b (role : String) : Option (Name × Name) → List Json
    | some (c, s) => [Json.mkObj [("role", toJson role), ("check", nameJ c), ("sound", nameJ s)]]
    | none => []
  Json.mkObj [("name", nameJ d.name), ("kind", toJson "declared"), ("implemented", toJson true),
    ("doc", toJson d.doc), ("constant", nameJ d.const), ("format", nameJson d.format),
    ("backends", toJson (b "native" d.native ++ b "kernel" d.kernel))]

def setJ (s : TrustSet) : Json :=
  let members := s.members.map (fun n => Json.mkObj [("kind", toJson "procedure"), ("name", nameJ n)]) ++
    s.includes.map (fun n => Json.mkObj [("kind", toJson "set"), ("name", nameJ n)])
  Json.mkObj [("name", nameJ s.name), ("doc", toJson s.doc),
    ("all", toJson s.all), ("members", toJson members)]

def policyJ (regs : Array String) (p : Policy) (s : Scope) : Json :=
  let scope := if s.module == `Silmaril then "root"
    else match s.module.components with
      | [`Silmaril, r] => if regs.contains r.toString then "region" else "module-prefix"
      | _ => "module-prefix"
  let setList : Option Name → Json
    | some n => toJson [toString n]
    | none => Json.null
  Json.mkObj [("scope", toJson scope), ("name", nameJ s.module), ("allow", setList s.dflt),
    ("max", setList s.max), ("deps", setList s.deps), ("axioms", setList s.axiomSet),
    ("origin", Json.mkObj [("file", toJson p.file), ("pin", toJson (hex64 p.hash))])]

/-- `#trust_export ["path"]`: write the `silmaril.trust-dump.v0.1` document. -/
syntax (name := trustExport) "#trust_export" (ppSpace str)? : command

@[command_elab trustExport] def elabTrustExport : CommandElab := fun stx => do
  let path := (stx[1].getOptional?.bind (·.isStrLit?)).getD ".lake/silmaril/trust.json"
  let env ← getEnv
  let root : System.FilePath := "."
  let regs ← regions root
  let prof ← liftCoreM profile
  let ceil ← liftCoreM ceiling
  -- Procedures: registered, declared, and named by sets only.
  let procs := allEntries procExt env
  let decls ← liftTermElabM allDecls
  let known : NameSet := (procs.map (·.name) ++ decls.map (·.name)).foldl (·.insert ·) {}
  let sets := allEntries setExt env
  let named := sets.foldl (init := ({} : NameSet)) fun acc s =>
    s.members.foldl (fun acc n => if known.contains n then acc else acc.insert n) acc
  let procedures := procs.map procedureJ ++ decls.map declaredJ ++
    named.toArray.map fun n => Json.mkObj [("name", nameJ n), ("kind", toJson "named"),
      ("implemented", toJson false), ("doc", toJson ""), ("backends", toJson ([] : List Json))]
  -- Sets must resolve (this also rejects include cycles).
  for s in sets do
    if let .error e := resolve env s.name then throwError "#trust_export: {e}"
  let policies := match policyExt.getState env with
    | some p => p.scopes.map (policyJ regs p)
    | none => #[]
  -- Exclusions for the current ceiling profile.
  let exclText ← (IO.FS.readFile "scripts/trust-profile-exclude.txt").toBaseIO
  let mut excludedNames : NameSet := {}
  let mut excluded : Array Json := #[]
  if let .ok text := exclText then
    for line in text.splitOn "\n" do
      let body := (line.splitOn "#")[0]!.trimAscii.toString
      let reason := ((line.splitOn "#").drop 1 |> String.intercalate "#").trimAscii.toString
      match body.splitOn " " |>.filter (· ≠ "") with
      | [p, m] =>
        if p == ceil || p == "*" then
          excludedNames := excludedNames.insert m.toName
          excluded := excluded.push (Json.mkObj [("module", toJson m),
            ("coverage", toJson "excluded"), ("profile", toJson p), ("reason", toJson reason)])
      | _ => pure ()
  -- Modules.
  let mut modules : Array Json := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`Silmaril).isPrefixOf m do continue
    let rel := (System.mkFilePath (m.components.map toString)).addExtension "lean"
    let sha ← match ← (IO.FS.readBinFile rel).toBaseIO with
      | .ok b => pure (toJson (hex (sha256 b)))
      | .error _ => pure Json.null
    let imports := env.header.moduleData[i]!.imports.map (toString ·.module)
    modules := modules.push (Json.mkObj [("name", nameJ m), ("region", regionOf regs m),
      ("source", toJson rel.toString), ("source_sha256", sha),
      ("imports", toJson imports.toList.eraseDups)])
  -- Uses, with provenance verification.
  let uses := allEntries useExt env
  let declared : NameMap Name := decls.foldl (init := {}) fun acc d =>
    match d.native with | some (c, _) => acc.insert d.name c | none => acc
  let usesJ := uses.map fun u =>
    let verified : Json := match u.mode, u.ax with
      | .native, some a =>
        let p? := match (procExt.getState env).find? u.proc, declared.find? u.proc with
          | some p, _ => some p
          | none, some c => some { name := u.proc, fn := c, kernel := false, doc := "", module := .anonymous }
          | none, none => none
        toJson (p?.map (verifiedNative env uses · a) |>.getD false)
      | _, _ => Json.null
    Json.mkObj [("module", nameJ u.module), ("decl", nameJ u.decl), ("procedure", nameJ u.proc),
      ("backend", toJson (match u.mode with | .native => "native" | .kernel => "kernel")),
      ("profile", toJson u.profile), ("axiom", nameJson u.ax), ("verified", verified)]
  let doc := Json.mkObj [("schema", toJson schema), ("toolchain", toJson Lean.toolchain),
    ("producer", Json.mkObj [("tool", toJson "Silmaril.Prelude.Trust.Export (#trust_export)"),
      ("profile", toJson prof), ("ceiling", toJson ceil),
      ("main_module", nameJ env.mainModule)]),
    ("procedures", toJson procedures), ("sets", toJson (sets.map setJ)),
    ("policies", toJson policies), ("modules", toJson modules), ("uses", toJson usesJ),
    ("excluded", toJson excluded)]
  if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (doc.pretty ++ "\n")
  logInfo m!"wrote {path}: {procedures.size} procedures, {sets.size} sets, {policies.size} \
    policies, {modules.size} modules, {usesJ.size} uses, {excluded.size} excluded"

end Silmaril.Trust.Export
