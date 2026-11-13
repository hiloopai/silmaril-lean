module

public import Silmaril.Prelude.Trust.Export.Defs

/-! # The project database's trust dump (`silmaril.trust-dump.v0.1`)

`#trust_export_db "path" M₁ M₂ …` writes the dump that `sil project sqlite --trust PATH` reads,
in exactly the contract of `docs/projects/trust-db.md` (#124): every field it emits is one the
database accepts. (`#trust_export` keeps writing the core's own `silmaril.trust-core.v1`.)

How the registry maps onto the contract:

* **Procedures** (`kind: decision`) are the registered procedures, the declared `ProcDecl`s, the
  registered native tactics, and every name a trust set lists without an implementation here.
  The three standard axioms are the database's built-ins and are not restated.
* **Implementations** are `(procedure, backend, profile)` with profile `kernel` for the kernel
  backend and `compiled` for the native one. A set name without a registered procedure gets
  one native implementation with `implemented: false`.
* **Sets.** Each `trust_set` lists its procedures as native grants
  (`{procedure, backend: native, profile: compiled}`) and its included sets. A set of `all` is
  expanded to every native implementation. `kernel.all` grants every kernel implementation;
  kernel runs need no trust beyond the kernel, so every scope's `allow` includes it.
* **Policies** are the `[native]` scopes of `policy.toml`, resolved for the dumping run's
  profile. `allow` is `standard`, `kernel.all` and the native set the profile allows there;
  `max` is `standard`, `kernel.all` and the scope's `max`. `Silmaril` is the root, `Silmaril.R`
  for a region `R` of `regions.toml` is a `region` scope, and anything else is a `prefix`
  `P.*`. Every scope states both sets, so nothing relies on inheritance rules.
* **Uses** are the recorded uses whose native axioms pass the audit's provenance check
  (`verifiedNative`), plus one `axiom` use per standard axiom of each declaration of the listed
  modules. A recorded native use that fails the check is left out, so its axiom stays
  unattributed and the database reports it.
* **Decls** are the declarations of the listed modules with their axioms (`collectAxioms`,
  transitive). A declaration that depends on another declaration's native run carries that
  native result without a direct use of its own; the database's `unattributed-axiom` check
  reports it.
-/

public meta section

namespace Silmaril.Trust.ExportDb

open Lean Elab Command Meta Silmaril.Trust Silmaril.Trust.Export

def nativeProfile : String := "compiled"
def kernelProfile : String := "kernel"
def kernelAll : String := "kernel.all"

def str (s : String) : Json := toJson s
def obj (fields : List (String × Option Json)) : Json :=
  Json.mkObj (fields.filterMap fun (k, v) => v.map (k, ·))

/-- The line of `policy.toml` that declares the scope for `mod`. -/
def originOf (text : String) (file : String) (mod : Name) : Option String := Id.run do
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    if line.trimAscii.toString == s!"module = \"{mod}\"" then
      return some s!"{file}:{n}"
  return none

syntax (name := trustExportDb) "#trust_export_db" (ppSpace str)? (ppSpace ident)* : command

@[command_elab trustExportDb] def elabTrustExportDb : CommandElab := fun stx => do
  let path := (stx[1].getOptional?.bind (·.isStrLit?)).getD ".lake/silmaril/trust.json"
  let env ← getEnv
  let regs ← regions "."
  let prof ← liftCoreM profile
  let ceil ← liftCoreM ceiling
  let procs := allEntries procExt env
  let decls ← liftTermElabM allDecls
  let sets := allEntries setExt env
  -- Procedures and implementations.
  let mut procedures : Array Json := #[]
  let mut impls : Array Json := #[]
  let mut nativeImpl : NameSet := {}
  let mut kernelImpl : NameSet := {}
  for p in procs do
    let prop := match p.axiomTag with
      | some _ => s!"what {p.name} decides (native evaluation of {p.fn})"
      | none => s!"{p.fn} … = true"
    procedures := procedures.push (obj [("name", str (toString p.name)), ("kind", str "decision"),
      ("proposition", str prop), ("doc", if p.doc.isEmpty then none else str p.doc)])
    let surface := match p.axiomTag with
      | some _ => s!"the Lean compiler and runtime, for: {String.intercalate ", " p.components.toList}"
      | none => match p.native with
        | some (nf, _) => s!"the Lean compiler and runtime, running {nf} (proved equal to {p.fn})"
        | none => s!"the Lean compiler and runtime, running {p.fn}"
    let nfn := (p.native.map (·.1)).getD p.fn
    impls := impls.push (obj [("procedure", str (toString p.name)), ("backend", str "native"),
      ("profile", str nativeProfile), ("decl", str (toString nfn)), ("implemented", toJson true),
      ("surface", str surface)])
    nativeImpl := nativeImpl.insert p.name
    if p.kernel then
      impls := impls.push (obj [("procedure", str (toString p.name)), ("backend", str "kernel"),
        ("profile", str kernelProfile), ("decl", str (toString p.fn)), ("implemented", toJson true)])
      kernelImpl := kernelImpl.insert p.name
  for d in decls do
    procedures := procedures.push (obj [("name", str (toString d.name)), ("kind", str "decision"),
      ("proposition", d.native.map (fun (_, s) => str s!"the conclusion of {s}") <|>
        d.kernel.map (fun (_, s) => str s!"the conclusion of {s}")),
      ("doc", if d.doc.isEmpty then none else str d.doc)])
    if let some (c, _) := d.native then
      impls := impls.push (obj [("procedure", str (toString d.name)), ("backend", str "native"),
        ("profile", str nativeProfile), ("decl", str (toString c)), ("implemented", toJson true),
        ("surface", str s!"the Lean compiler and runtime, running {c}")])
      nativeImpl := nativeImpl.insert d.name
    if let some (c, _) := d.kernel then
      impls := impls.push (obj [("procedure", str (toString d.name)), ("backend", str "kernel"),
        ("profile", str kernelProfile), ("decl", str (toString c)), ("implemented", toJson true)])
      kernelImpl := kernelImpl.insert d.name
  -- Names that sets list without an implementation here.
  for s in sets do
    for n in s.members do
      unless nativeImpl.contains n || kernelImpl.contains n do
        procedures := procedures.push (obj [("name", str (toString n)), ("kind", str "decision"),
          ("doc", str "Named by a trust set; not implemented in this environment.")])
        impls := impls.push (obj [("procedure", str (toString n)), ("backend", str "native"),
          ("profile", str nativeProfile), ("implemented", toJson false)])
        nativeImpl := nativeImpl.insert n
  -- Sets.
  let nativeMember (n : Name) : Json := obj [("procedure", str (toString n)),
    ("backend", str "native"), ("profile", str nativeProfile)]
  let mut setsJ : Array Json := #[]
  setsJ := setsJ.push (obj [("name", str kernelAll),
    ("doc", str "Every kernel implementation: kernel checks need no trust beyond the kernel."),
    ("members", toJson (kernelImpl.toList.map fun n => obj [("procedure", str (toString n)),
      ("backend", str "kernel"), ("profile", str kernelProfile)]))])
  for s in sets do
    let members := if s.all then nativeImpl.toList.map nativeMember
      else s.members.toList.map nativeMember ++ s.includes.toList.map fun i => obj [("set", str (toString i))]
    setsJ := setsJ.push (obj [("name", str (toString s.name)),
      ("doc", if s.doc.isEmpty then none else str s.doc), ("members", toJson members)])
  -- Policies, resolved for the profile, every scope stating both sets.
  let policyText ← (IO.FS.readFile "policy.toml").toBaseIO
  let text := match policyText with | .ok t => t | .error _ => ""
  let mut policies : Array Json := #[]
  let mut extraSets : Array Json := #[]
  if let some pol := policyExt.getState env then
    for sc in pol.scopes do
      let eff ← match effectiveIn env pol sc.module with
        | .ok e => pure e
        | .error e => throwError "#trust_export_db: {e}"
      let allowed ← match allowed env sc.module prof ceil with
        | .ok a => pure a
        | .error e => throwError "#trust_export_db: {e}"
      -- A set holding exactly the given native grants, named after the scope.
      let named (role : String) (m : Members) : Array String × Array Json :=
        match m with
        | .all => (#["all"], #[])
        | .some ns =>
          if ns.isEmpty then (#[], #[]) else
          let n := s!"native.{role}.{sc.module}"
          (#[n], #[obj [("name", str n), ("doc", str s!"Native grants of {sc.module} ({role})."),
            ("members", toJson (ns.toList.map nativeMember))]])
      let (allowNative, s1) := named "allow" allowed
      let (maxNative, s2) := named "max" eff.max
      extraSets := extraSets ++ s1 ++ s2
      let base := #["standard", kernelAll]
      let (scope, name) :=
        if sc.module == `Silmaril then ("root", "")
        else match sc.module.components with
          | [`Silmaril, r] => if regs.contains r.toString then ("region", r.toString)
              else ("prefix", s!"{sc.module}.*")
          | _ => ("prefix", s!"{sc.module}.*")
      policies := policies.push (obj [("scope", str scope),
        ("name", if name.isEmpty then none else str name),
        ("allow", toJson (base ++ allowNative)), ("max", toJson (base ++ maxNative)),
        ("origin", (originOf text "policy.toml" sc.module).map str)])
  -- `all` used as a set name: every native implementation.
  if policies.any (fun p => (p.getObjValD "allow").compress.contains "\"all\"" ||
      (p.getObjValD "max").compress.contains "\"all\"") then
    setsJ := setsJ.push (obj [("name", str "all"), ("doc", str "Every native implementation."),
      ("members", toJson (nativeImpl.toList.map nativeMember))])
  setsJ := setsJ ++ extraSets
  -- Modules.
  let mut modules : Array Json := #[]
  let mut described : NameSet := {}
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless (`Silmaril).isPrefixOf m do continue
    described := described.insert m
    let rel := (System.mkFilePath (m.components.map toString)).addExtension "lean"
    let sha ← match ← (IO.FS.readBinFile rel).toBaseIO with
      | .ok b => pure (some (str (hex (sha256 b))))
      | .error _ => pure none
    let imports := env.header.moduleData[i]!.imports.map (toString ·.module)
    modules := modules.push (obj [("name", str (toString m)), ("region", (regionOf regs m).getStr?.toOption.map str),
      ("source", str rel.toString), ("source_sha256", sha),
      ("imports", toJson imports.toList.eraseDups)])
  -- Uses: verified recorded uses, merged by key.
  let recorded := allEntries useExt env
  let declared : NameMap (Name × Option Name) := decls.foldl (init := {}) fun acc d =>
    match d.native with | some (c, _) => acc.insert d.name (c, d.bound) | none => acc
  let mut useMap : Std.HashMap (String × String × String × String) (Array String) := {}
  let mut useOrder : Array (String × String × String × String) := #[]
  for u in recorded do
    unless described.contains u.module do continue
    -- The use's backend and axioms, or none when it should not be emitted.
    let entry : Option (String × Array String) := match u.mode, u.ax with
      | .kernel, _ => some ("kernel", #[])
      | .native, some a =>
        let p? : Option Procedure := match (procExt.getState env).find? u.proc, declared.find? u.proc with
          | some p, _ => some p
          | none, some (c, b) => some { name := u.proc, fn := c, kernel := false, doc := "",
                                        module := .anonymous, bound := b }
          | none, none => none
        match p? with
        | some p => if verifiedNative env recorded p a then some ("native", #[toString a]) else none
        | none => none
      | .native, none => none
    let some (backend, axs) := entry | continue
    let key := (toString u.module, toString u.decl, toString u.proc, backend)
    match useMap[key]? with
    | some prev => useMap := useMap.insert key (prev ++ axs.filter (!prev.contains ·))
    | none =>
      useMap := useMap.insert key axs
      useOrder := useOrder.push key
  let mut uses : Array Json := useOrder.map fun k =>
    let (m, d, p, b) := k
    obj [("module", str m), ("decl", str d), ("procedure", str p), ("backend", str b),
      ("profile", str (if b == "kernel" then kernelProfile else nativeProfile)),
      ("axioms", toJson (useMap[k]?.getD #[]))]
  -- Decls of the listed modules, and their standard-axiom uses.
  let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut declsJ : Array Json := #[]
  for mstx in stx[2].getArgs do
    let m := mstx.getId
    for d in ← liftCoreM (declsOf m) do
      let axs ← liftCoreM (collectAxioms d)
      declsJ := declsJ.push (obj [("module", str (toString m)), ("decl", str (toString d)),
        ("axioms", toJson (axs.map toString))])
      for a in axs do
        if standard.contains a then
          uses := uses.push (obj [("module", str (toString m)), ("decl", str (toString d)),
            ("procedure", str (toString a)), ("backend", str "axiom"), ("axioms", toJson [toString a])])
  -- Exclusions for the build's ceiling.
  let mut excluded : Array Json := #[]
  if let .ok t ← (IO.FS.readFile "scripts/trust-profile-exclude.txt").toBaseIO then
    for line in t.splitOn "\n" do
      let body := (line.splitOn "#")[0]!.trimAscii.toString
      let reason := ((line.splitOn "#").drop 1 |> String.intercalate "#").trimAscii.toString
      match body.splitOn " " |>.filter (· ≠ "") with
      | [p, m] => if p == ceil || p == "*" then
          excluded := excluded.push (obj [("module", str m), ("coverage", str "excluded"),
            ("reason", str reason)])
      | _ => pure ()
  -- Inputs.
  let mut inputs : Array Json := #[]
  for f in ["policy.toml", "regions.toml", "scripts/trust-profile-exclude.txt"] do
    if let .ok b ← (IO.FS.readBinFile f).toBaseIO then
      inputs := inputs.push (obj [("path", str f), ("sha256", str (hex (sha256 b)))])
  let doc := obj [("schema", str "silmaril.trust-dump.v0.1"), ("toolchain", str Lean.toolchain),
    ("producer", str s!"silmaril-lean Silmaril.Prelude.Trust.ExportDb (profile {prof}, ceiling {ceil})"),
    ("inputs", toJson inputs), ("procedures", toJson procedures),
    ("implementations", toJson impls), ("sets", toJson setsJ), ("policies", toJson policies),
    ("modules", toJson modules), ("uses", toJson uses), ("decls", toJson declsJ),
    ("excluded", toJson excluded)]
  if let some dir := (System.FilePath.mk path).parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (doc.pretty ++ "\n")
  logInfo m!"wrote {path} (silmaril.trust-dump.v0.1): {procedures.size} procedures, \
    {impls.size} implementations, {setsJ.size} sets, {policies.size} policies, \
    {modules.size} modules, {uses.size} uses, {declsJ.size} decls, {excluded.size} excluded"

end Silmaril.Trust.ExportDb
