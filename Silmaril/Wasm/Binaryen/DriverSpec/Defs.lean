module

public import Silmaril.Wasm.Binaryen.Driver.Defs
public import Silmaril.Cli.Spec.WasmOpt.Defs

/-!
# `wasm-opt`: the driver's reading against its surface

`Silmaril.Cli.Spec.WasmOpt.surface` is the clap view of `wasm-opt`'s grammar; the driver reads
the verified-stages path with `Driver.parseArgs`. This module gives

* `render`: the normal form of a `Plan` as an argument vector (flags, `-o OUT`,
  `--rounds N` when not 1, one `--passes NAME` per stage and the preset word per preset, in
  selection order, then the input);
* `toPlan`: the meaning of a surface invocation as a plan (the specification's reading,
  independent of the token syntax);
* `compare`/`disagreements`: the two readings side by side on an argument vector, and the
  list of corpus vectors (`Command.corpus` of the surface, each after `--verified-stages`) on which
  they differ.

The theorems are in `Silmaril.Wasm.Binaryen.DriverSpec.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.DriverSpec

open Silmaril.Wasm.Binaryen.Driver Silmaril.Wasm.Binaryen.Pipeline Silmaril.Cli.Surface
open Silmaril.Wasm.Binaryen.Exe

/-- The tokens of one selection item. -/
def Item.render : Item → List String
  | .stage s => ["--passes", s.name]
  | .preset q => [q.name]

/-- `-o OUT`, if there is an output. -/
def outputArgs : Option String → List String
  | some o => ["-o", o]
  | none => []

/-- The input path, if there is one. -/
def inputArgs : Option String → List String
  | some i => [i]
  | none => []

/-- The normal form of a plan (verified-stages path). -/
def render (p : Plan) : List String :=
  (if p.verifiedStages then ["--verified-stages"] else []) ++
  (if p.stats then ["--stats"] else []) ++
  (if p.kind = .component then ["--component"] else []) ++
  (if p.printPipeline then ["--print-pipeline"] else []) ++
  outputArgs p.output ++
  (if p.rounds = 1 then [] else ["--rounds", toString p.rounds]) ++
  p.itemsRev.reverse.flatMap Item.render ++
  inputArgs p.input

/-- A path the normal form can carry: nonempty, and `-` or not starting with `-`. -/
def PlainPath (s : String) : Prop := s ≠ "" ∧ (s = "-" ∨ s.startsWith "-" = false)

/-- Plans with a normal form: plain input, nonempty output. -/
structure NormalForm (p : Plan) : Prop where
  input : ∀ i, p.input = some i → PlainPath i
  output : ∀ o, p.output = some o → o ≠ ""

/-- The preset of a preset token. -/
def presetOf? (t : String) : Option CleanupPreset := parseOptCompatPreset t

/-- The meaning of a surface invocation of `wasm-opt` on the verified-stages path: the
occurrences in order, the positional as input. Errors are the driver's value checks
(unknown pass names, a non-numeric `--rounds`, an empty path), which the surface does not
model. -/
def toPlan (inv : Invocation) : Except String Plan := do
  let plan ← inv.opts.foldlM (init := ({} : Plan)) fun plan (k, v) =>
    match k, v with
    | "verified-stages", _ => pure { plan with verifiedStages := true }
    | "stats", _ => pure { plan with stats := true }
    | "component", _ => pure { plan with kind := .component }
    | "print-pipeline", _ => pure { plan with printPipeline := true }
    | "all-features", _ => pure plan
    | "output", some o => setOutput plan o
    | "rounds", some n => match n.toNat? with
      | some r => pure { plan with rounds := r }
      | none => throw "--rounds requires a nonnegative integer"
    | "passes", some names => do
      let stages ← parsePasses names
      pure { plan with itemsRev := (stages.map Item.stage).reverse ++ plan.itemsRev }
    | k, _ =>
      match presetOf? k with
      | some q => pure { plan with itemsRev := .preset q :: plan.itemsRev }
      | none => match namedFlag? ("--" ++ k) with
        | some s => pure { plan with itemsRev := .stage s :: plan.itemsRev }
        | none => throw ("not an option of the verified-stages path: " ++ k)
  inv.args.foldlM setInput plan

/-- A plan, as text (plans have no decidable equality: they are compared by this). -/
def planText (p : Plan) : String :=
  s!"{repr p.input} {repr p.output} {repr p.itemsRev} {p.rounds} {p.verifiedStages} {p.stats} " ++
    s!"{p.printPipeline} {repr p.kind}"

/-- How the two readings of one argument vector compare. -/
inductive Verdict where
  /-- Both accept, with the same plan. -/
  | same
  /-- Both reject (the surface with a usage error, help or version). -/
  | bothReject
  /-- The driver rejects what the surface accepts (with the driver's message). -/
  | driverStricter (msg : String)
  /-- The driver accepts what the surface rejects. -/
  | driverLaxer
  /-- Both accept with different plans. -/
  | differ
  /-- The surface prints help or the version, the driver rejects: the driver reads its
  information options only as the sole argument. -/
  | infoNotAlone
  deriving DecidableEq, Repr

/-- Compare the driver's reading (`parseArgs`) with the surface's (`Command.parse`, then
`toPlan`). -/
def compare (argv : List String) : Verdict :=
  match parseArgs argv {}, Silmaril.Cli.Spec.WasmOpt.surface.parse argv with
  | .ok p, .run inv =>
    match toPlan inv with
    | .ok q => if planText p == planText q then .same else .differ
    | .error _ => .driverLaxer
  | .ok _, _ => .driverLaxer
  | .error _, .help _ | .error _, .version _ => .infoNotAlone
  | .error e, .run inv =>
    match toPlan inv with
    | .ok _ => .driverStricter e
    | .error _ => .bothReject
  | .error _, _ => .bothReject

/-- Hand-written vectors in the style of Binaryen's command lines. -/
def extraVectors : List (List String) :=
  [["--passes", "dce,vacuum", "in.wasm", "-o", "out.wasm"], ["-O2", "--ssa", "in.wasm"],
   ["--rounds=3", "--tee-form", "in.wasm"], ["--output=out.wasm", "in.wasm"],
   ["-all", "--passes=ssa,rse-line", "-"], ["-Os", "-O", "-Oz", "in.wasm", "-o", "-"],
   ["-oout.wasm", "in.wasm"], ["-o=out.wasm", "in.wasm"], ["in.wasm", "extra.wasm"],
   ["--passes", "no-such-pass", "in.wasm"], ["--rounds", "x", "in.wasm"],
   ["--print-pipeline", "-O3", "--rounds", "2"], ["--stats", "--drop-get", "in.wasm"],
   ["--component", "in.wasm"], ["--mode", "refinement", "in.wasm"], ["", "-o", "x"],
   ["in.wasm", "-o", ""], ["--output=", "in.wasm"], ["-o", "--stats", "in.wasm"]]

/-- The corpus: the surface's (`Command.corpus`, input `in.wasm`) and `extraVectors`, each
after `--verified-stages` so that the driver takes the verified-stages path. -/
def corpus : List (List String) :=
  ((Silmaril.Cli.Spec.WasmOpt.surface.corpus "in.wasm") ++ extraVectors).map ("--verified-stages" :: ·)

/-- The corpus vectors on which the readings differ, with the verdict. -/
def disagreements : List (List String × Verdict) :=
  (corpus.map fun a => (a, compare a)).filter fun (_, v) =>
    match v with
    | .same | .bothReject => false
    | _ => true

end Silmaril.Wasm.Binaryen.DriverSpec

