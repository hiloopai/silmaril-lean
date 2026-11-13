/- The trust driver of `sil project trust-dump` (generated: do not commit).

It imports the modules to audit and writes `silmaril.trust-lines.v0.1` over the core trust API
(`Silmaril.Prelude.Trust`): the policy, its scopes and sets, the registered procedures and
recorded uses, per module its imports and effective sets, and per theorem its axioms as
`trust_audit` splits them. `sil project trust-dump` then adds the producer, the inputs and the
source digests. Names it reads that are not yet a declared stable interface of the core:
`policyExt`, `setExt`, `procExt`, `useExt`, `allEntries`, `effective`, `allowed`,
`axiomReport`, `procJson`, `useJson`, `hex64`, `profile`, `ceiling`. -/
__IMPORTS__
import Silmaril.Prelude.Trust.Elab.Defs

open Lean Elab Command Silmaril.Trust

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : List Name := __ROOTS__
  let under (m : Name) := roots.any (·.isPrefixOf m)
  let out ← IO.FS.Handle.mk __OUT__ .write
  let line (j : Json) : IO Unit := out.putStrLn j.compress
  let mem : Members → Json
    | .all => Json.mkObj [("all", true)]
    | .some s => Json.mkObj [("all", false),
        ("names", toJson ((s.toList.map toString).toArray.qsort (· < ·)))]
  let prof ← liftCoreM profile
  let ceil ← liftCoreM ceiling
  line <| Json.mkObj [("kind", "header"), ("schema", "silmaril.trust-lines.v0.1"),
    ("toolchain", Lean.versionString), ("profile", prof), ("ceiling", ceil)]
  if let some p := policyExt.getState env then
    line <| Json.mkObj [("kind", "policy"), ("file", p.file), ("pin", hex64 p.hash)]
    for s in p.scopes do
      let o (x : Option Name) : Json := match x with | some n => toJson n.toString | none => Json.null
      line <| Json.mkObj [("kind", "scope"), ("module", s.module.toString), ("max", o s.max),
        ("default", o s.dflt), ("deps", o s.deps), ("axioms", o s.axiomSet)]
    for s in p.sets do
      line <| Json.mkObj [("kind", "set"), ("name", s.name.toString), ("all", s.all),
        ("origin", "policy"), ("members", toJson (s.members.map toString)),
        ("includes", toJson (s.includes.map toString))]
  for s in allEntries setExt env do
    line <| Json.mkObj [("kind", "set"), ("name", s.name.toString), ("all", s.all),
      ("origin", "trust_set"), ("members", toJson (s.members.map toString)),
      ("includes", toJson (s.includes.map toString))]
  for p in allEntries procExt env do line (procJson p)
  for u in allEntries useExt env do line (useJson u)
  let mut decls : Array (Name × Name) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless under m do continue
    let imps := env.header.moduleData[i]!.imports.map (·.module.toString)
    line <| Json.mkObj [("kind", "module"), ("name", m.toString), ("imports", toJson imps)]
    match effective env m, allowed env m prof ceil with
    | .ok e, .ok a =>
      line <| Json.mkObj [("kind", "effective"), ("module", m.toString), ("max", mem e.max),
        ("default", mem e.dflt), ("deps", mem e.deps), ("axioms", mem e.axiomSet),
        ("allowed", mem a), ("trace", toJson e.trace)]
    | .error msg, _ | _, .error msg =>
      line <| Json.mkObj [("kind", "effective"), ("module", m.toString), ("error", msg)]
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
    line <| Json.mkObj [("kind", "decl"), ("decl", n.toString), ("module", m.toString),
      ("own_native", names r.ownNative), ("dep_native", names r.depNative),
      ("plain_native", names r.plainNative), ("axioms", names r.other),
      ("native_axioms", names r.nativeAxioms)]
  out.flush
