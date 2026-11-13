/- The trust driver of `sil project trust-dump` for the core's v1 API (generated: do not commit).

The core's `#trust_dump` writes its lines (`silmaril.trust.v1`: procedures, declared procedures,
uses, `trust_set`s and scopes). This driver adds what that dump does not carry, as
`silmaril.trust-adapter.v0.1` lines: the header (toolchain, profile, ceiling), the policy file and
pin, the sets of the policy file (`standard`), per module its imports and effective sets, and per
theorem its axioms split as `trust_audit` splits them. Core names it reads that are not part of
the declared stable interface: `policyExt`, `effective`, `allowed`, `axiomReport`, `hex64`,
`profile`, `ceiling`, `Members`. -/
__IMPORTS__
import Silmaril.Prelude.Trust.Elab.Defs

open Lean Elab Command Silmaril.Trust

#trust_dump __CORE_OUT__

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : List Name := __ROOTS__
  let under (m : Name) := roots.any (·.isPrefixOf m)
  let out ← IO.FS.Handle.mk __OUT__ .write
  let adapter := "silmaril.trust-adapter.v0.1"
  let line (fields : List (String × Json)) : IO Unit :=
    out.putStrLn (Json.mkObj (("schema", toJson adapter) :: fields)).compress
  let mem : Members → Json
    | .all => Json.mkObj [("all", true)]
    | .some s => Json.mkObj [("all", false),
        ("names", toJson ((s.toList.map toString).toArray.qsort (· < ·)))]
  let prof ← liftCoreM profile
  let ceil ← liftCoreM ceiling
  line [("kind", "header"), ("core_api", "v1"), ("toolchain", Lean.versionString),
    ("profile", prof), ("ceiling", ceil)]
  if let some p := policyExt.getState env then
    line [("kind", "policy"), ("file", p.file), ("pin", hex64 p.hash)]
    for s in p.sets do
      line [("kind", "set"), ("name", s.name.toString), ("all", s.all), ("origin", "policy"),
        ("members", toJson (s.members.map toString)), ("includes", toJson (s.includes.map toString))]
  let mut decls : Array (Name × Name) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless under m do continue
    let imps := env.header.moduleData[i]!.imports.map (·.module.toString)
    line [("kind", "module"), ("name", m.toString), ("imports", toJson imps)]
    match effective env m, allowed env m prof ceil with
    | .ok e, .ok a =>
      line [("kind", "effective"), ("module", m.toString), ("max", mem e.max),
        ("default", mem e.dflt), ("deps", mem e.deps), ("axioms", mem e.axiomSet),
        ("allowed", mem a), ("trace", toJson e.trace)]
    | .error msg, _ | _, .error msg =>
      line [("kind", "effective"), ("module", m.toString), ("error", msg)]
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n | continue
      unless ci matches ConstantInfo.thmInfo _ do continue
      if n.isInternalDetail then continue
      -- Realized constants (`eq_def`, …) can be listed by several modules; keep their owner.
      unless env.getModuleIdxFor? n == some i do continue
      decls := decls.push (m, n)
  for (m, n) in decls.qsort (fun a b => a.2.toString < b.2.toString) do
    let r ← liftCoreM (axiomReport n)
    let names (xs : Array Name) : Json := toJson (xs.map toString)
    line [("kind", "decl"), ("decl", n.toString), ("module", m.toString),
      ("own_native", names r.ownNative), ("dep_native", names r.depNative),
      ("plain_native", names r.plainNative), ("axioms", names r.other),
      ("native_axioms", names r.nativeAxioms)]
  out.flush
