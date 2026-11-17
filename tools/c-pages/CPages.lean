import Lean
import Silmaril.Project.Shapes.CTV.Thms

/-!
# `c-pages`: the explorer's C programs tab data (docs/projects/c-tv.md)

```
lake env .lake/build/bin/c-pages OUTDIR     write OUTDIR/c/{theorems.json, profiles.json, programs/…}
```

1. **Imports the checked modules** `Silmaril.Project.Shapes.CTV.Thms` and `CTvRows`
   (built by `lake build --wfail`) and lists every theorem whose **statement** is a shape of
   `Silmaril.Project.Shapes.CTV` (`CRefines`, `CRefinesUBFree`, `CNotRefines`, `CEquivalent`,
   `ProfileCoherentAt`, or the negation of one): the shape, the arguments and the statement as
   Lean prints them, the axioms (`Lean.collectAxioms`), the module and the line. A theorem is listed
   because of its type, never because of its name; other theorems of those modules are not listed.
2. Evaluates `Profile.issues` on the profiles `linuxX86_64` and `legacyPinnedApple` for every scalar
   type (compiled evaluation), and pairs each row with the theorems whose statement is that row's
   coherence or incoherence.
3. Copies `examples/c-programs` (the corpus and its provenance, `scripts/c-tv/corpus.py`) to
   `OUTDIR/c/programs`, and the GCC torture report (`benchmarks/gcc-torture/tv-report.json.gz`) to
   `OUTDIR/c/torture`. The corpus's verdicts are compiled evidence; no theorem is about a corpus
   program, and the page says so.
-/

open Lean Meta
open Silmaril.Cerberus.TV Silmaril.Project.Shapes.CTV

def shapes : List (Name × String) := [
  (``CRefines, "silmaril.shapes.c.tv.refines"),
  (``CRefinesUBFree, "silmaril.shapes.c.tv.refines_ub_free"),
  (``CNotRefines, "silmaril.shapes.c.tv.not_refines"),
  (``CEquivalent, "silmaril.shapes.c.tv.equivalent"),
  (``ProfileCoherentAt, "silmaril.shapes.c.tv.profile_coherent_at"),
  (``ProfileApplies, "silmaril.shapes.c.tv.profile_applies"),
  (``CRefinesOn, "silmaril.shapes.c.tv.refines_on"),
  (``CContextRefines, "silmaril.shapes.c.tv.context_refines"),
  (``CModuleRefines, "silmaril.shapes.c.tv.module_refines")]

def modules : List Name := [`Silmaril.Project.Shapes.CTV.Thms, `CTvRows]

def runCore {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  let (a, _) ← x.toIO { fileName := "<c-pages>", fileMap := default, maxHeartbeats := 0 } { env }
  pure a

/-- The shape a statement is an instance of, whether it is negated, its arguments, and the
registered row it states (when the statement is a row constant of the records, `silmaril.…`,
whose definition is the shape's application: unfolded once). -/
def shapeOf? (env : Environment) (ty : Expr) : Option (String × Bool × Array Expr × Option Name) :=
  let (neg, body) := match ty.not? with
    | some b => (true, b)
    | none => (false, ty)
  let direct (e : Expr) := match e.getAppFn with
    | .const c _ => (shapes.lookup c).map fun s => (s, e.getAppArgs)
    | _ => none
  match direct body with
  | some (s, args) => some (s, neg, args, none)
  | none => match body with
    | .const row _ =>
        if (`silmaril).isPrefixOf row then
          match env.find? row with
          | some (.defnInfo d) => (direct d.value).map fun (s, args) => (s, neg, args, some row)
          | _ => none
        else none
    | _ => none

structure Thm where
  name : Name
  module : Name
  shape : String
  negated : Bool
  args : Array String
  statement : String
  axioms : Array Name
  line : Option Nat
  row : Option Name

def Thm.json (t : Thm) : Json := Json.mkObj [("name", t.name.toString), ("module", t.module.toString),
  ("shape", t.shape), ("negated", t.negated), ("args", Json.arr (t.args.map Json.str)),
  ("statement", t.statement), ("axioms", Json.arr (t.axioms.map (Json.str ·.toString))),
  ("line", match t.line with | some l => Json.num l | none => Json.null),
  ("row", match t.row with | some r => Json.str r.toString | none => Json.null)]

def theorems (env : Environment) : IO (Array Thm) := do
  let mods := modules.filterMap env.getModuleIdx?
  unless mods.length == modules.length do throw (IO.userError "c-pages: a checked module is not imported")
  let mut out : Array Thm := #[]
  for (n, ci) in env.constants.toList do
    unless (env.getModuleIdxFor? n).any mods.contains do continue
    let .thmInfo ti := ci | continue
    if n.isInternal then continue
    let some (shape, negated, args, row) := shapeOf? env ti.type | continue
    let head := (shapes.find? (·.2 == shape)).map (·.1) |>.getD .anonymous
    let explicit : Array Bool ← runCore env <| MetaM.run' do
      let fty ← inferType (mkConst head (← mkFreshLevelMVarsFor (← getConstInfo head)))
      forallTelescope fty fun xs _ => xs.mapM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    let args := (args.zip explicit).filterMap fun (a, e) => if e then some a else none
    let pp ← runCore env do
      let a ← args.mapM fun a => return toString (← (ppExpr a).run')
      let s := toString (← (ppExpr ti.type).run')
      pure (a, s)
    let axioms := (← runCore env (Lean.collectAxioms n)).qsort Name.lt
    let line ← runCore env do return (← findDeclarationRanges? n).map (·.range.pos.line)
    let module := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => .anonymous
    out := out.push ⟨n, module, shape, negated, pp.1, pp.2, axioms, line, row⟩
  return out.qsort fun a b => a.name.toString < b.name.toString

def scalarName (s : Scalar) : String :=
  (reprStr s).replace "Silmaril.Cerberus.TV.Scalar." ""

def issueJson : Issue → Json
  | .differs w => Json.mkObj [("kind", "differs"), ("what", w)]
  | .unknown w => Json.mkObj [("kind", "unknown"), ("what", w)]

def profiles (thms : Array Thm) : Json :=
  let one (decl : String) (p : Profile) : Json :=
    let rows := Scalar.all.map fun s =>
      let is := p.issues s
      let sc := "Silmaril.Cerberus.TV.Scalar." ++ scalarName s
      let backing := thms.filter fun t => t.shape == "silmaril.shapes.c.tv.profile_coherent_at" &&
        t.args.size == 2 && t.args[0]! == "Silmaril.Project.Shapes.CTV." ++ decl && t.args[1]! == sc
      Json.mkObj [("scalar", scalarName s), ("coherent", is.isEmpty), ("issues", Json.arr (is.map issueJson).toArray),
        ("theorems", Json.arr (backing.map fun t => Json.mkObj [("name", t.name.toString), ("negated", t.negated)]))]
    Json.mkObj [("decl", decl), ("name", p.name), ("scalars", Json.arr rows.toArray)]
  Json.arr #[one "linuxX86_64" linuxX86_64, one "legacyPinnedApple" legacyPinnedApple]

partial def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if ← e.path.isDir then copyTree e.path (dst / e.fileName)
    else IO.FS.writeBinFile (dst / e.fileName) (← IO.FS.readBinFile e.path)

def main (args : List String) : IO UInt32 := do
  let [outDir] := args | IO.eprintln "usage: c-pages OUTDIR"; return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules (modules.toArray.map fun m => { module := m }) {}
  let thms ← theorems env
  let dir := System.FilePath.mk outDir / "c"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "theorems.json") ((Json.mkObj [("schema", "silmaril.c-pages.theorems.v1"),
    ("modules", Json.arr (modules.toArray.map (Json.str ·.toString))),
    ("theorems", Json.arr (thms.map Thm.json))]).pretty ++ "\n")
  IO.FS.writeFile (dir / "profiles.json") ((profiles thms).pretty ++ "\n")
  copyTree "examples/c-programs" (dir / "programs")
  IO.FS.createDirAll (dir / "torture")
  IO.FS.writeBinFile (dir / "torture" / "tv-report.json.gz")
    (← IO.FS.readBinFile "benchmarks/gcc-torture/tv-report.json.gz")
  IO.println s!"c-pages: {thms.size} theorems, 2 profiles, the corpus -> {dir}"
  return 0
