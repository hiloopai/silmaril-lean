/- The trust driver of `sil project trust-dump` (generated: do not commit).

It calls the core's stable dump hooks (`docs/trust.md`, #125): `dumpLines` (procedures, uses,
`trust_set`s, scopes), `allDecls'` (declared procedures), and per module under the roots
`moduleLine` and `auditLine` over `declsOf`, the same lines `#trust_dump path M₁ …` writes
(schema `silmaril.trust.v1`). The module list is computed here, which `#trust_dump`'s syntax cannot
do. The adapter adds what those lines lack (schema `silmaril.trust-adapter.v0.2`): the header
(toolchain) and the sets of the policy file itself (`standard`), read from `policyExt`, which is
not a declared stable hook. -/
__IMPORTS__
import Silmaril.Prelude.Trust.Elab.Defs

open Lean Elab Command Silmaril.Trust

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots : List Name := __ROOTS__
  let under (m : Name) := roots.any (·.isPrefixOf m)
  let mods := env.header.moduleNames.filter under
  -- The core's lines, from its stable hooks.
  let decls ← liftTermElabM allDecls'
  let mut core : Array Json := dumpLines env ++ decls
  for m in mods do
    core := core.push (← liftCoreM (moduleLine m))
    for d in ← liftCoreM (declsOf m) do
      core := core.push (← liftCoreM (auditLine d)).1
  IO.FS.writeFile __CORE_OUT__ (String.intercalate "\n" (core.map (·.compress)).toList ++ "\n")
  -- The adapter's lines.
  let adapter := "silmaril.trust-adapter.v0.2"
  let line (fields : List (String × Json)) : Json := Json.mkObj (("schema", toJson adapter) :: fields)
  let mut out : Array Json := #[line [("kind", "header"), ("core_api", "v1-hooks"),
    ("toolchain", Lean.versionString)]]
  if let some p := policyExt.getState env then
    for s in p.sets do
      out := out.push <| line [("kind", "set"), ("name", s.name.toString), ("all", s.all),
        ("origin", "policy"), ("members", toJson (s.members.map toString)),
        ("includes", toJson (s.includes.map toString))]
  IO.FS.writeFile __OUT__ (String.intercalate "\n" (out.map (·.compress)).toList ++ "\n")
