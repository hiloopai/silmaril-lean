module

public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Spec.Verdict.Defs
public import Silmaril.Wasm.Equiv.Module
public import Silmaril.Wasm.Auto.Bridge.Defs

@[expose] public section

/-!
# One front end for automatic Wasm checks: statements and differential testing

The front end of `docs/projects/wasm-binaryen-tooling.md`. It answers three kinds of question
about Core 3.0 modules (silmaril-lean `Module`s) and one function export `j`:

* `ModRefines R P impl spec j`: every behaviour of export `j` of `impl` is `R`-related to a
  behaviour of export `j` of `spec`, on every argument list `impl` accepts (silmaril-lean's
  `FunRefines` across two stores, `ExportRefines`);
* `ModEquiv R P m₁ m₂ j`: refinement both ways;
* `ModMeets R P m j f`: export `j` of `m` meets the **reference function** `f`
  (`f vs = some r`: on `vs` the specification allows exactly the result `r`; `none`: no
  constraint), silmaril-lean's `Equiv.Meets` with the specification `specOfFn f`.

The statements are about the instance computed by `Silmaril.Wasm.Verify.instance?` (start-free
modules with scalar function imports and exports), host-free (`noHost`), at a profile `P`. The
relation `R` is `Rel.eq` (equal behaviours) or `Rel.trap` (the implementation may trap where the
specification does something else), read through `Rel.toProp`.

## Differential testing on the verified interpreter

The first stage of the front end runs silmaril-lean's verified interpreter (`runInvoke?`,
deterministic profile `profile refOracle`, no host) on both sides for a list of argument lists
(`inputsFor`: boundary values, small exhaustive grids, and pseudo-random values from a linear
congruential generator) and looks for an input on which the results differ (`cexWith`,
`findCexWith`; for a reference function `specCexWith`, `findSpecCexWith`).

Every check is written once over the interpreter (`run`), and used twice:

* with `runInvoke?` (`cexC`, `findCexC`, …): compiled code, for the tool `wasm-check`;
* with `Silmaril.Wasm.Verify.Kernel.runInvokeK` (`cexK`, `findCexK`, …): reducible by the kernel,
  for `decide +kernel` (`runInvokeK_eq` makes the two equal).

A hit is a **refutation** (`Silmaril.Wasm.Auto.Front.Thms`): `¬ ModRefines`, `¬ ModEquiv` at the
deterministic profile, `¬ ModMeets` at every profile admitting its steps. A refutation of a
refinement needs the specification side's behaviours to be pinned down, which silmaril-lean's
`behaviours_subset_of_runInvoke?` gives (confluence of host-free reduction); a refutation of
`ModMeets` needs only soundness of the interpreter.

## The pipeline

`check` runs the stages in order and reports `proved`, `refuted` or `unknown`:

1. `identical`: the two modules are the same term (decided by the caller; the tool compares
   bytes), proved by reflexivity (`ModRefines.refl`);
2. differential testing (this file): `refuted` with a counterexample;
3. the function-level proving stage (`proveStageBase`): the exports' bodies are summarised
   by symbolic execution (`Silmaril.Wasm.Auto.Bridge.fnSum?`, on top of the equivalence checker of
   `Silmaril.Wasm.Auto.Equiv`); equal normal forms of the results, or residual goals that are all in
   the proved lemma library (`Silmaril.Wasm.Auto.Bridge.lemmaGoals`), prove `ModEquiv` (hence
   `ModRefines`) at **every** profile (`Silmaril.Wasm.Auto.Front.Thms.checkRefinesBase_proved`);
   otherwise the report counts the residual goals or lists the stages still `pending`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto.Front

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (instance? instOf refOracle)
open Silmaril.Wasm.Spec (typedB Verdict)

/-! ## Statements -/

/-- The behaviour relations of the front end. -/
inductive Rel where
  /-- Equal behaviours. -/
  | eq
  /-- Trap insertion: the implementation traps, or behaves as the specification. -/
  | trap
  deriving DecidableEq, Repr

/-- The relation as a proposition (`Eq`, silmaril-lean's `Behaviour.TrapRefines`). -/
def Rel.toProp : Rel → Behaviour Val → Behaviour Val → Prop
  | .eq => fun b b' => b = b'
  | .trap => Behaviour.TrapRefines

/-- The relation as a Boolean. -/
def Rel.holdsB : Rel → Behaviour Val → Behaviour Val → Bool
  | .eq, b, b' => decide (b = b')
  | .trap, b, b' => decide (b = .traps) || decide (b = b')

/-- **Refinement of function addresses in two stores**: every behaviour of invoking `a₁` in `s₁`
on arguments it accepts is `R`-related to a behaviour of invoking `a₂` in `s₂` on the same
arguments. With `s₁ = s₂` it is silmaril-lean's `FunRefines` (`exportRefines_iff_funRefines`). -/
def ExportRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (s₁ : Store Nat)
    (a₁ : Nat) (s₂ : Store Nat) (a₂ : Nat) : Prop :=
  ∀ vs, InvokeOk s₁ a₁ vs →
    Behaviours.Refines R (behaviours P Det.noHost s₁ a₁ vs) (behaviours P Det.noHost s₂ a₂ vs)

/-- The address of function export `j` of a module's computed instance. -/
def addrOf (m : Module) (j : Nat) : Nat := (instOf m).addrs.getD j 0

/-- **Module refinement at export `j`**: `impl` refines `spec`. -/
def ModRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (impl spec : Module)
    (j : Nat) : Prop :=
  ExportRefines R P (instOf impl).store (addrOf impl j) (instOf spec).store (addrOf spec j)

/-- **Module equivalence at export `j`**: refinement both ways (the second with the converse
relation, as in silmaril-lean's `FunEquiv`). -/
def ModEquiv (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (m₁ m₂ : Module)
    (j : Nat) : Prop :=
  ModRefines R P m₁ m₂ j ∧ ModRefines (fun x y => R y x) P m₂ m₁ j

/-- The specification of a reference function: on `vs`, the result `r` when `f vs = some r`,
anything when `f vs = none`. -/
def specOfFn (f : List Val → Option Result) : Equiv.ImportSpec Val := fun vs =>
  match f vs with
  | some r => {r.toBehaviour}
  | none => Set.univ

/-- **Export `j` of `m` meets the reference function `f`** (silmaril-lean's `Equiv.Meets`). -/
def ModMeets (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (m : Module) (j : Nat)
    (f : List Val → Option Result) : Prop :=
  Equiv.Meets (entryPoints P Det.noHost) R (instOf m).store (addrOf m j) (specOfFn f)

/-! ## Test inputs -/

/-- Boundary values of an integer type of `w` bits: small numbers, powers of two around the
sign bit, all ones, and a few patterns. -/
def boundary (w : Nat) : List Nat :=
  [0, 1, 2, 3, 7, 9, 10, 11, 100, 127, 128, 255, 256, 1000, 65535, 65536,
    2 ^ (w - 1) - 1, 2 ^ (w - 1), 2 ^ (w - 1) + 1, 2 ^ w - 1, 2 ^ w - 2, 2 ^ w - 10,
    0x12345678 % 2 ^ w, (2 ^ w - 1) / 3, 2 ^ (w / 2), 2 ^ (w / 2) - 1]

/-- A linear congruential generator on 64 bits (Knuth's MMIX constants). -/
def lcg (x : Nat) : Nat := (6364136223846793005 * x + 1442695040888963407) % 2 ^ 64

/-- The width in bits of a scalar type's test values. -/
def widthOf : ScalarType → Nat
  | .num t => match t with
    | .int .i32 => 32
    | .int .i64 => 64
    | .float .f32 => 32
    | .float .f64 => 64
  | .v128 => 128
  | .i31 _ => 31

/-- The value of a scalar type with bits `k` (`Silmaril.Wasm.Verify.candVal`, any `k`). -/
def valOf (t : ScalarType) (k : Nat) : Val := Silmaril.Wasm.Verify.candVal k t

/-- `n` pseudo-random argument lists of types `ps` from seed `x`: half of the values are
boundary values, half random bits. -/
def randInputs (ps : List ScalarType) : Nat → Nat → List (List Val)
  | 0, _ => []
  | n + 1, x =>
    let step := fun (acc : List Val × Nat) (t : ScalarType) =>
      let x' := lcg acc.2
      let w := widthOf t
      let b := boundary w
      let k := if x' / 2 ^ 40 % 2 == 0 then b.getD (x' / 2 ^ 20 % b.length) 0 else x' % 2 ^ w
      (acc.1 ++ [valOf t k], x')
    let (vs, x') := ps.foldl step ([], x)
    vs :: randInputs ps n x'

/-- All argument lists over the first `k` boundary values (`k ^ |ps|` lists). -/
def gridInputs (ps : List ScalarType) (k : Nat) : List (List Val) :=
  ps.foldr (fun t acc => ((boundary (widthOf t)).take k).flatMap fun v =>
    acc.map (valOf t v :: ·)) [[]]

/-- The extreme values of an integer type of `w` bits: `0`, `1`, the largest and smallest signed
numbers, `-1`. -/
def extremes (w : Nat) : List Nat := [0, 1, 2 ^ (w - 1) - 1, 2 ^ (w - 1), 2 ^ w - 1]

/-- All argument lists over the extreme values (`5 ^ |ps|` lists). -/
def extremeInputs (ps : List ScalarType) : List (List Val) :=
  ps.foldr (fun t acc => (extremes (widthOf t)).flatMap fun v => acc.map (valOf t v :: ·)) [[]]

/-- The test inputs for parameter types `ps`: a grid of small boundary values (at most about
300 lists), every combination of extreme values (up to five parameters), and `nRand`
pseudo-random lists. -/
def inputsFor (ps : List ScalarType) (nRand : Nat) : List (List Val) :=
  let k := match ps.length with
    | 0 => 1
    | 1 => (boundary 32).length
    | 2 => 12
    | 3 => 6
    | 4 => 4
    | _ => 2
  gridInputs ps k ++ (if ps.length ≤ 5 then extremeInputs ps else []) ++
    randInputs ps nRand (ps.length + 17)

/-! ## The checks, over an interpreter -/

/-- An interpreter of `$invoke` (`runInvoke?` or a kernel-reducible copy). -/
abbrev Runner := GrowOracle → Nat → Store Nat → Nat → List Val →
  Option (Config Nat × Bool × Option Result)

/-- The fuel of the differential tester (interpreter steps per run; a run that does not stop
within it is not a counterexample). -/
def diffFuel : Nat := 20000

/-- The result of a stopped run. -/
def outOf (run : Runner) (s : Store Nat) (a : Nat) (vs : List Val) : Option Result :=
  match run refOracle diffFuel s a vs with
  | some (_, true, some r) => some r
  | _ => none

/-- The parameter types of export `j` of an instance. -/
def paramsOf (I : ScalarInstance) (j : Nat) : Option (List ScalarType) :=
  I.exports[j]?.map (·.params)

/-- Whether the results `r₁` (implementation) and `r₂` (specification) witness a failure of
refinement: `r₁` is related neither to `r₂` nor to divergence. -/
def badPair (R : Rel) (r₁ r₂ : Result) : Bool :=
  !R.holdsB r₁.toBehaviour r₂.toBehaviour && !R.holdsB r₁.toBehaviour .diverges

/-- **One test of a refinement** `impl ⊑ spec` at export `j` on `vs`: both modules have an
instance, `vs` is typed for export `j` of both, both runs stop with results, and the results are
a bad pair. -/
def cexWith (run : Runner) (R : Rel) (impl spec : Module) (j : Nat) (vs : List Val) : Bool :=
  match instance? impl, instance? spec with
  | some (_, I₁), some (_, I₂) =>
    match paramsOf I₁ j, paramsOf I₂ j with
    | some ps₁, some ps₂ =>
      typedB ps₁ vs && typedB ps₂ vs &&
        match outOf run I₁.store (I₁.addrs.getD j 0) vs,
            outOf run I₂.store (I₂.addrs.getD j 0) vs with
        | some r₁, some r₂ => badPair R r₁ r₂
        | _, _ => false
    | _, _ => false
  | _, _ => false

/-- The test inputs of export `j` of a module (none when it has no instance). -/
def inputsOf (m : Module) (j : Nat) (nRand : Nat) : List (List Val) :=
  match instance? m with
  | some (_, I) => ((paramsOf I j).map (inputsFor · nRand)).getD []
  | none => []

/-- The first counterexample to `impl ⊑ spec` among the inputs `ins`. -/
def findCexIn (run : Runner) (R : Rel) (impl spec : Module) (j : Nat) (ins : List (List Val)) :
    Option (List Val) :=
  ins.find? (cexWith run R impl spec j)

/-- One test of `ModMeets` on `vs`: the run stops with a result that is not `R`-related to the
reference result. -/
def specCexWith (run : Runner) (R : Rel) (m : Module) (j : Nat) (f : List Val → Option Result)
    (vs : List Val) : Bool :=
  match instance? m with
  | some (_, I) =>
    match paramsOf I j with
    | some ps =>
      typedB ps vs &&
        match outOf run I.store (I.addrs.getD j 0) vs, f vs with
        | some r₁, some r₂ => !R.holdsB r₁.toBehaviour r₂.toBehaviour
        | _, _ => false
    | none => false
  | none => false

/-- The first counterexample to `ModMeets` among the inputs `ins`. -/
def findSpecCexIn (run : Runner) (R : Rel) (m : Module) (j : Nat) (f : List Val → Option Result)
    (ins : List (List Val)) : Option (List Val) :=
  ins.find? (specCexWith run R m j f)

/-! ## Compiled and kernel instances -/

/-- The compiled interpreter. -/
def runC : Runner := Silmaril.Wasm.SingleThreaded.Exec.runInvoke?

/-- The kernel-reducible interpreter. -/
noncomputable def runK : Runner := Silmaril.Wasm.Verify.Kernel.runInvokeK

/-- `cexWith` with the kernel-reducible interpreter: prove `cexK R impl spec j vs = true` by
`decide +kernel`. -/
noncomputable def cexK (R : Rel) (impl spec : Module) (j : Nat) (vs : List Val) : Bool :=
  cexWith runK R impl spec j vs

/-- `specCexWith` with the kernel-reducible interpreter. -/
noncomputable def specCexK (R : Rel) (m : Module) (j : Nat) (f : List Val → Option Result)
    (vs : List Val) : Bool :=
  specCexWith runK R m j f vs

/-! ## Reports -/

/-- Why a verdict was reached. -/
inductive Reason where
  /-- The two modules are identical (proved by reflexivity). -/
  | identical
  /-- A counterexample: on `args` the implementation gives `impl`, the specification `spec`
  (`none` for a reference function that is unconstrained). -/
  | counterexample (args : List Val) (impl : Result) (spec : Option Result)
  /-- No counterexample among `tested` inputs; the stages `pending` are not run. -/
  | untested (tested : Nat) (pending : List String)
  /-- Proved by the function-level stage `stage` (`equiv`: equal normal forms; `equiv+lemmas`:
  every residual goal is in the lemma library). -/
  | stage (stage : String)
  /-- No counterexample among `tested` inputs; both bodies are summarised, `goals` residual
  bitvector goals remain. -/
  | residual (tested : Nat) (goals : Nat)
  /-- A module has no instance (invalid, start function, non-function import) or export `j` is
  missing. -/
  | noInstance
  deriving Repr

/-- A report of the front end. -/
structure Report where
  /-- The verdict. -/
  verdict : Verdict
  /-- The reason. -/
  reason : Reason
  deriving Repr

/-- The stages of the other tracks, not run by the front end yet. -/
def pendingStages : List String := ["egraph", "vcgen"]

/-- **The function-level proving stage** (after differential testing found no counterexample
among `tested` inputs): equal normal forms of the summarised results, or residual goals all in
the lemma library, prove the equivalence. -/
def proveStageBase (m₁ m₂ : Module) (j : Nat) (tested : Nat) : Report :=
  if Bridge.fnCheck m₁ m₂ j then ⟨.proved, .stage "equiv"⟩
  else
    match Bridge.fnResiduals m₁ m₂ j with
    | some gs =>
      if Bridge.discharged gs then ⟨.proved, .stage "equiv+lemmas"⟩
      else ⟨.unknown, .residual tested gs.length⟩
    | none => ⟨.unknown, .untested tested ("equiv" :: pendingStages)⟩

/-- **The front end for a refinement** `impl ⊑ spec` at export `j`, with `nRand` random inputs.
`identical` is the caller's knowledge that the two modules are the same. -/
def checkRefinesBase (R : Rel) (impl spec : Module) (j : Nat) (nRand : Nat) (identical : Bool) :
    Report :=
  if identical then ⟨.proved, .identical⟩ else
  match instance? impl, instance? spec with
  | some (_, I₁), some (_, I₂) =>
    if (paramsOf I₁ j).isNone || (paramsOf I₂ j).isNone then ⟨.unknown, .noInstance⟩ else
    let ins := inputsOf impl j nRand
    match findCexIn runC R impl spec j ins with
    | some vs =>
      match outOf runC I₁.store (I₁.addrs.getD j 0) vs,
          outOf runC I₂.store (I₂.addrs.getD j 0) vs with
      | some r₁, some r₂ => ⟨.refuted, .counterexample vs r₁ (some r₂)⟩
      | _, _ => ⟨.unknown, .untested ins.length pendingStages⟩
    | none => proveStageBase impl spec j ins.length
  | _, _ => ⟨.unknown, .noInstance⟩

/-- **The front end for equivalence**: refinement both ways; a counterexample of either
direction refutes it (the reverse direction is tested for `Rel.eq`, whose converse is itself).
A `proved` verdict comes from the first direction, whose proving stage proves equivalence. -/
def checkEquivBase (R : Rel) (m₁ m₂ : Module) (j : Nat) (nRand : Nat) (identical : Bool) : Report :=
  let r := checkRefinesBase R m₁ m₂ j nRand identical
  if r.verdict == .unknown then
    match R with
    | .eq =>
      let r' := checkRefinesBase .eq m₂ m₁ j nRand identical
      if r'.verdict == .refuted then r' else r
    | .trap => r
  else r

/-- **The front end against a reference function.** -/
def checkMeets (R : Rel) (m : Module) (j : Nat) (f : List Val → Option Result) (nRand : Nat) :
    Report :=
  match instance? m with
  | some (_, I) =>
    if (paramsOf I j).isNone then ⟨.unknown, .noInstance⟩ else
    let ins := inputsOf m j nRand
    match findSpecCexIn runC R m j f ins with
    | some vs =>
      match outOf runC I.store (I.addrs.getD j 0) vs with
      | some r₁ => ⟨.refuted, .counterexample vs r₁ (f vs)⟩
      | none => ⟨.unknown, .untested ins.length pendingStages⟩
    | none => ⟨.unknown, .untested ins.length pendingStages⟩
  | none => ⟨.unknown, .noInstance⟩

/-! ## JSON -/

/-- A value as JSON (`{"type":…,"bits":…}`, as `Silmaril.Wasm.Verify.Report.toJson` writes it). -/
def valJson : Val → String
  | .num ⟨.int .i32, b⟩ => "{\"type\":\"i32\",\"bits\":" ++ toString b.toNat ++ "}"
  | .num ⟨.int .i64, b⟩ => "{\"type\":\"i64\",\"bits\":" ++ toString b.toNat ++ "}"
  | .num ⟨.float .f32, b⟩ => "{\"type\":\"f32\",\"bits\":" ++ toString b.toNat ++ "}"
  | .num ⟨.float .f64, b⟩ => "{\"type\":\"f64\",\"bits\":" ++ toString b.toNat ++ "}"
  | .vec b => "{\"type\":\"v128\",\"bits\":" ++ toString b.toNat ++ "}"
  | .ref _ => "{\"type\":\"ref\"}"

/-- A list of values as JSON. -/
def valsJson (vs : List Val) : String := "[" ++ ",".intercalate (vs.map valJson) ++ "]"

/-- A result as JSON. -/
def resultJson : Result → String
  | .values vs => "{\"returns\":" ++ valsJson vs ++ "}"
  | .trap => "\"trap\""
  | .throw a => "{\"throws\":" ++ toString a ++ "}"

/-- A verdict as JSON. -/
def verdictJson : Verdict → String
  | .proved => "\"proved\""
  | .refuted => "\"refuted\""
  | .unknown => "\"unknown\""

/-- A report as JSON. -/
def Report.toJson (r : Report) : String :=
  "{\"verdict\":" ++ verdictJson r.verdict ++ ",\"reason\":" ++
    (match r.reason with
    | .identical => "{\"kind\":\"identical\"}"
    | .counterexample vs r₁ r₂ =>
      "{\"kind\":\"counterexample\",\"args\":" ++ valsJson vs ++ ",\"impl\":" ++ resultJson r₁ ++
        ",\"spec\":" ++ (match r₂ with | some r => resultJson r | none => "null") ++ "}"
    | .untested n ps =>
      "{\"kind\":\"untested\",\"tested\":" ++ toString n ++ ",\"pending\":[" ++
        ",".intercalate (ps.map fun p => "\"" ++ p ++ "\"") ++ "]}"
    | .stage st => "{\"kind\":\"proved\",\"stage\":\"" ++ st ++ "\"}"
    | .residual n k =>
      "{\"kind\":\"residual\",\"tested\":" ++ toString n ++ ",\"goals\":" ++ toString k ++ "}"
    | .noInstance => "{\"kind\":\"noInstance\"}") ++ "}"

/-! ## The extended summaries

`checkRefines`, `checkEquiv`: the pipeline above, then, when no stage decided, the extended
summaries of `Silmaril.Wasm.Auto.Bridge` (`i32.wrap_i64`/`i64.extend_i32`, division with trap
guards, globals, loads and stores on memory `0`): `fnCheckX` proves the equivalence
(`stage "equivx"`). Refuted verdicts are those of `checkRefinesBase` and `checkEquivBase`. These are
the
checks of `wasm-check`. -/

/-- Turn a report without a verdict into a proof when `ok` (the extended check) holds. -/
def upgrade (r : Report) (ok : Bool) : Report :=
  if r.verdict == .unknown && ok then ⟨.proved, .stage "equivx"⟩ else r

/-- **The front end for a refinement**, with the extended summaries. -/
def checkRefines (R : Rel) (impl spec : Module) (j : Nat) (nRand : Nat) (identical : Bool) :
    Report :=
  upgrade (checkRefinesBase R impl spec j nRand identical) (Bridge.fnCheckX impl spec j)

/-- **The front end for equivalence**, with the extended summaries. -/
def checkEquiv (R : Rel) (m₁ m₂ : Module) (j : Nat) (nRand : Nat) (identical : Bool) : Report :=
  upgrade (checkEquivBase R m₁ m₂ j nRand identical) (Bridge.fnCheckX m₁ m₂ j)

/-- The proving stages alone (no differential testing): `proveStageBase` or the extended
summaries. -/
def proveStage (m₁ m₂ : Module) (j : Nat) : Report :=
  upgrade (proveStageBase m₁ m₂ j 0) (Bridge.fnCheckX m₁ m₂ j)

end Silmaril.Wasm.Auto.Front
