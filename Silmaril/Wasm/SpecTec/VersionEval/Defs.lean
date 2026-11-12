module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Valid
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.InstrSchema
public import Silmaril.Raw.Wasm.SpecTec.Generated

/-!
# Evaluating the defect predicates on a new `WebAssembly/spec` revision

`spectec-gen version lean` (tools/spectec-gen) runs `VersionEval.run` on the streams of a new
revision, read at run time.  For each stream it runs the build-time checks of
`Silmaril.Proofs.Wasm.SpecTec.Versions.Checks` (`Sem.checkStreamFile`, and for wasm-3.0 the
instruction-shape crosscheck against `Silmaril.Wasm.SpecTec.{instruction,administrative}Schemas`),
and for every defect predicate of `Silmaril.Wasm.SpecTec.Broken`/`Versions` that is decided by a
single evaluation it runs that evaluation at fuel `fuel` and prints the verdict.

The evaluations are the ones the kernel proofs at `e7a9df7c` use (`callDef`/`premsHold` at
fuel 100, `findDef?` for `NoClauses`), here compiled and run, not proved:

* a call or premise list that evaluates to `.ok` is a witness for `CallIs`/`PremsHold`;
* one that is `.error .undef` at some fuel is undefined at every fuel (`Broken/Fuel.lean`,
  `callUndef_of_undef`), so a witness for `CallUndef`/`PremsFail`;
* `.error .outOfFuel` decides nothing and prints `unknown`.

Predicates stated with `gramRelSup` (#654, #803) or `RuleFires` (the dead `Step` rules) are not
decided by an evaluation and are printed as `unknown`.  Output lines (`spectec-gen` parses them):

```
CHECK <stream> <check> ok|fail <message>
DEFECT <theorem> present|fixed|unknown <note>
```
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.VersionEval

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Broken
open Silmaril.Wasm.SpecTec.Versions

/-- The fuel of every evaluation (the kernel proofs at `e7a9df7c` use 100). -/
def fuel : Nat := 100

/-- What an evaluation says about a defect predicate. -/
inductive Verdict where
  | present
  | fixed
  | unknown (why : String)

def Verdict.render : Verdict → String
  | .present => "present"
  | .fixed => "fixed"
  | .unknown why => s!"unknown {why}"

/-- A predicate that holds when the evaluation is undefined (`CallUndef`, `PremsFail`). -/
def presentIfUndef {α : Type} : Res α → Verdict
  | .ok _ => .fixed
  | .error .undef => .present
  | .error .outOfFuel => .unknown s!"out of fuel at {fuel}"

/-- A predicate that holds when the evaluation succeeds (`PremsHold`). -/
def presentIfOk {α : Type} : Res α → Verdict
  | .ok _ => .present
  | .error .undef => .fixed
  | .error .outOfFuel => .unknown s!"out of fuel at {fuel}"

/-- `CallUndef s f args`. -/
def callUndef (s : Script) (f : IL.Id) (args : List Arg) : Verdict :=
  presentIfUndef (callDef fuel (envOfScript s) VarEnv.empty f args)

/-- `PremsFail s ps ρ` (present) against `PremsHold s ps ρ` (fixed). -/
def premsFail (s : Script) (ps : Option (List Prem)) (ρ : VarEnv) (what : String) : Verdict :=
  match ps with
  | none => .unknown s!"{what} not found"
  | some prems => presentIfUndef (premsHold fuel (envOfScript s) ρ prems)

/-- `PremsHold s ps ρ` (present) against `PremsFail s ps ρ` (fixed). -/
def premsHoldV (s : Script) (ps : Option (List Prem)) (ρ : VarEnv) (what : String) : Verdict :=
  match ps with
  | none => .unknown s!"{what} not found"
  | some prems => presentIfOk (premsHold fuel (envOfScript s) ρ prems)

/-- `NoClauses s f` (present) against a declaration with clauses (fixed). -/
def noClauses (s : Script) (f : IL.Id) : Verdict :=
  match (envOfScript s).findDef? f with
  | some (_, _, []) => .present
  | some _ => .fixed
  | none => .unknown s!"no `def {f}`"

/-- `DataidxMissesNested s`: `$dataidx_instrs` of a nested `memory.init` is `[]`. -/
def dataidxMissesNested (s : Script) : Verdict :=
  match callDef fuel (envOfScript s) VarEnv.empty "dataidx_instrs"
      [.expA IL.Wasm20.nestedMemoryInit] with
  | .ok (.list []) => .present
  | .ok _ => .fixed
  | .error .undef => .unknown "undefined (neither present nor fixed as stated)"
  | .error .outOfFuel => .unknown s!"out of fuel at {fuel}"

/-- One defect: the stream module it is about, the theorem name `spectec-gen`'s `KNOWN` table
uses for it, and its evaluation. -/
structure Row where
  module : String
  thm : String
  verdict : Script → Verdict

/-- The defects of `spectec-gen`'s `KNOWN` table, keyed by its theorem names. -/
def rows : List Row :=
  [ ⟨"Wasm30", "not_bi32Unsigned_main", fun _ => Verdict.unknown "grammar predicate (gramRelSup)"⟩,
    ⟨"Wasm30", "not_contUndefAt80_main", fun s => callUndef s "cont" [.expA (numCaseE 0x80)]⟩,
    ⟨"Wasm30", "utf8singleAcceptsGrin_main",
      fun s => premsFail s (clausePrems s "utf8single" 3) grinScope "clause 3 of `$utf8single`"⟩,
    ⟨"Wasm30", "not_escapeRejectsE000_main",
      fun s => premsFail s (prodPrems s "Tstringchar" 7) escapeE000Scope
        "production 7 of `Tstringchar`"⟩,
    ⟨"Wasm30", "bsnLosesFF7E_main", fun _ => Verdict.unknown "grammar predicate (gramRelSup)"⟩,
    ⟨"Wasm30", "not_sxUndefAtRef_main", fun s => callUndef s "sx" [.expA refFuncE]⟩,
    ⟨"Wasm30", "s33ToU32Undefined_main", fun s => noClauses s "s33_to_u32"⟩,
    ⟨"Wasm30", "ieeeUndefined_main", fun s => noClauses s "ieee_"⟩,
    ⟨"Wasm30", "ruleDead_*_main", fun _ => Verdict.unknown "rule predicate (RuleFires)"⟩,
    ⟨"Wasm10", "not_utf8RejectsGrin10_main",
      fun s => premsFail s (clausePrems s "utf8" 3) grinScope "clause 3 of `$utf8`"⟩,
    ⟨"Wasm10", "utf8AcceptsC2C0_main",
      fun s => premsHoldV s (clausePrems s "utf8" 1) c2c0Scope "clause 1 of `$utf8`"⟩,
    ⟨"Wasm20", "utf8AcceptsGrin20_main",
      fun s => premsFail s (clausePrems s "utf8" 3) grinScope "clause 3 of `$utf8`"⟩,
    ⟨"Wasm20", "utf8AcceptsC2C0_20_main",
      fun s => premsHoldV s (clausePrems s "utf8" 1) c2c0Scope "clause 1 of `$utf8`"⟩,
    ⟨"Wasm20", "dataidxMissesNested_main", dataidxMissesNested⟩ ]

/-- The instruction shapes of a script against the Rust decoder's, as `spectec_crosscheck`
compares them (sorted by tag). -/
def crosscheck (s : Script) : Except String Nat := do
  let some ours := instrSchemas? s
    | throw "no single plain `instr` variant declaration"
  let expected := (Silmaril.Wasm.SpecTec.instructionSchemas ++
    Silmaril.Wasm.SpecTec.administrativeSchemas).map fun c => (c.tag, c.fields)
  let sort (xs : List (String × List Silmaril.Wasm.SpecTec.FieldType)) :=
    xs.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  unless ours.length == expected.length do
    throw s!"{ours.length} instruction constructors, the schemas have {expected.length}"
  for (o, e) in (sort ours).zip (sort expected) do
    unless o == e do
      throw s!"disagrees at {o.1}"
  return ours.length

/-- Read and decode a stream. -/
def readStream (path : String) : IO Script := do
  let contents ← IO.FS.readFile path
  match SExp.parseStream contents with
  | .error msg => throw (IO.userError s!"{path} is not an S-expression stream: {msg}")
  | .ok forms =>
    match IL.decodeScript? forms with
    | some s => pure s
    | none => throw (IO.userError s!"{path} is not a printed SpecTec IL script")

/-- Print one `CHECK` line; never throws. -/
def check (stream what : String) (act : IO String) : IO Unit := do
  try
    let msg ← act
    IO.println s!"CHECK {stream} {what} ok {msg}"
  catch e =>
    IO.println s!"CHECK {stream} {what} fail {(toString e).replace "\n" " "}"

/-- Run every check and defect evaluation on the streams `module=path;…` (the value of
`SPECTEC_VERSION_STREAMS`).  Defect rows whose module has no stream are skipped. -/
def run (spec : String) : IO Unit := do
  let streams := (spec.splitOn ";").filterMap fun kv =>
    match kv.splitOn "=" with
    | [m, p] => if m.isEmpty then none else some (m, p)
    | _ => none
  for (m, path) in streams do
    check m "checkStreamFile" (do Sem.checkStreamFile path; pure path)
    let script? ← try pure (some (← readStream path)) catch _ => pure none
    let some s := script? | continue
    if m == "Wasm30" then
      check m "crosscheck" do
        match crosscheck s with
        | .ok n => pure s!"{n} instruction constructors agree with the schemas"
        | .error msg => throw (IO.userError msg)
    for r in rows.filter (·.module == m) do
      IO.println s!"DEFECT {r.thm} {(r.verdict s).render}"

end Silmaril.Wasm.SpecTec.VersionEval
