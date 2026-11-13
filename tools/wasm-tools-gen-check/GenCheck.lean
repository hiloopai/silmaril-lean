import Silmaril.Wasm.Tools.Gen.Core.Defs
import Silmaril.Wasm.Tools.Gen.Sem.Defs
import Silmaril.Wasm.Tools.Gen.Comp.Defs
import Silmaril.Wasm.Tools.Gen.Wit.Defs
import Silmaril.Wasm.Tools.Gen.Typed.Defs
import Silmaril.Wasm.Tools.Gen.Typed3.Defs
import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# `wasm-tools-gen-check`: measurements of the verified generator, mutator and shrinker

```
wasm-tools-gen-check [--feat v10|v20|v30|fx|lime1] [--count N] [--size N] [--seed N]
                     [--mutations K] [--out DIR] [--verbose] [--component | --wit | --typed | --typed3]
```

For seeds `seed … seed+N-1`: generate a raw module (`Raw.module`), check it (`featCheck`, the
checker the verified `featGen` uses), mutate every valid module `K` times through the raw
mutation, apply the semantics-preserving mutator `Sem.featSem` once (counting how often it
changes the encoding), (counting how often the checked mutator `featMut` keeps the raw output), shrink it
with the predicate "some function body contains an integer multiplication" (`featShrink`), and
encode it with silmaril's certified encoder. With `--out`, writes `gen-<seed>.wasm` and
`mut-<seed>.wasm` for differential tests against the pinned `wasm-tools`. Exit status 0 when
every verified output passed the checker (a theorem, re-checked here as a smoke test).

The executable runs what the verified objects compute and imports no theorem header (`mor
runtime-closure wasm-tools-gen-check`): `featGenRun S` and `featMutRun S` are
`(featGen S).run` and `(featMut S).run` (`Core.featGen_run_eq`, `Core.featMut_run_eq`, by
`rfl`), likewise `Comp.compGenRun`/`compMutRun` and `Wit.witGenRun`/`witMutRun`
(`Comp.compGen_run_eq`, `Wit.witGen_run_eq`, ...).
-/

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Tools.Gen Silmaril.Wasm.Tools.Gen.Core

structure Opts where
  feat : String := "v30"
  count : Nat := 100
  size : Nat := 20
  seed : Nat := 0
  mutations : Nat := 10
  out : Option String := none
  verbose : Bool := false
  stage : Option Nat := none
  component : Bool := false
  wit : Bool := false
  typed : Bool := false
  typed3 : Bool := false

partial def parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--feat" :: v :: r, o => parse r { o with feat := v }
  | "--count" :: v :: r, o => parse r { o with count := v.toNat! }
  | "--size" :: v :: r, o => parse r { o with size := v.toNat! }
  | "--seed" :: v :: r, o => parse r { o with seed := v.toNat! }
  | "--mutations" :: v :: r, o => parse r { o with mutations := v.toNat! }
  | "--out" :: v :: r, o => parse r { o with out := some v }
  | "--verbose" :: r, o => parse r { o with verbose := true }
  | "--component" :: r, o => parse r { o with component := true }
  | "--wit" :: r, o => parse r { o with wit := true }
  | "--typed" :: r, o => parse r { o with typed := true }
  | "--typed3" :: r, o => parse r { o with typed3 := true }
  | "--stage" :: v :: r, o => parse r { o with stage := some v.toNat! }
  | "--list-stages" :: r, o => parse r { o with stage := some 1000000 }
  | a :: _, _ => .error s!"unknown argument {a}"

/-- Encode with silmaril's certified encoder, writing a data count section only when the code
needs one (`Exe.encodeModule`; a 1.0 module must not have one). -/
def enc (m : Module) : Except String (List UInt8) :=
  (Silmaril.Wasm.Binaryen.Exe.encodeModule ByteArray.empty m).map fun b => b.data.toList

def featOf : String → Option FeatureSet
  | "v10" => some v10 | "v20" => some v20 | "v30" => some v30 | "fx" => some wasmFX
  | "lime1" => some lime1 | _ => none

mutual
def hasMul : Instr → Bool
  | .intBinOp _ .mul => true
  | .block _ b | .loop _ b | .tryTable _ _ b => hasMulL b
  | .if_ _ t e => hasMulL t || hasMulL e
  | _ => false
def hasMulL : List Instr → Bool
  | [] => false
  | i :: is => hasMul i || hasMulL is
end

def interesting (m : Module) : Bool := m.funcs.any fun f => hasMulL f.body

/-- The component measurements (`--component`). -/
def compMain (o : Opts) (S : FeatureSet) : IO UInt32 := do
  let mut rawOk := 0
  let mut bad := 0
  let mut mutKept := 0
  let mut mutTotal := 0
  let mut parsed := 0
  let mut shrunk := 0
  let mut sizeBefore := 0
  let mut sizeAfter := 0
  let t0 ← IO.monoMsNow
  for i in [0:o.count] do
    let seed := o.seed + i
    let r := Rng.ofSeed seed
    if Comp.compCheck Comp.dflt S (Rand.run (Comp.Raw.component S o.size) r) then rawOk := rawOk + 1
    let c := Comp.compGenRun S r o.size
    if !Comp.compCheck Comp.dflt S c then bad := bad + 1
    let mut cur := c
    for k in [0:o.mutations] do
      let rk := Rng.ofSeed (seed * 1000003 + k)
      mutTotal := mutTotal + 1
      if Comp.compCheck Comp.dflt S (Comp.Raw.mutate S rk cur) then mutKept := mutKept + 1
      cur := Comp.compMutRun S rk cur
      if !Comp.compCheck Comp.dflt S cur then bad := bad + 1
    match Silmaril.Wasm.Component.BinaryP3.encode c with
    | some bs =>
      if (Silmaril.Wasm.Component.BinaryP3.parse bs).toOption.isSome then parsed := parsed + 1
      if let some d := o.out then IO.FS.writeBinFile s!"{d}/comp-{seed}.wasm" bs
    | none => pure ()
    -- shrink to "has at least two core modules"
    let p : Silmaril.Wasm.Component.BinaryP3.Ast → Bool := fun x => (Comp.coreModules x).length ≥ 2
    if p c then
      let s := Comp.compShrink S p c
      shrunk := shrunk + 1
      sizeBefore := sizeBefore + Comp.Raw.size c
      sizeAfter := sizeAfter + Comp.Raw.size s
      if !(Comp.compCheck Comp.dflt S s && p s) then bad := bad + 1
  let t1 ← IO.monoMsNow
  IO.println s!"component feat {o.feat} count {o.count} size {o.size} seed {o.seed}"
  IO.println s!"raw-valid {rawOk}/{o.count}"
  IO.println s!"raw-mutations-kept {mutKept}/{mutTotal}"
  IO.println s!"encoded-and-reparsed {parsed}/{o.count}"
  IO.println s!"shrunk {shrunk} size-before {sizeBefore} size-after {sizeAfter}"
  IO.println s!"checked-output-failures {bad}"
  -- the fallback: `Validate.check` accepts the empty component (proved: `Comp.empty_compValid`;
  -- re-checked here)
  let emptyOk := Comp.compCheck Comp.dflt S (.mk [])
  IO.println s!"empty-component-accepted {emptyOk}"
  IO.println s!"time-ms {t1 - t0}"
  return if bad = 0 && emptyOk then 0 else 1

/-- The WIT instance (`Gen.Wit`), at every flag: raw validity, mutation, shrinking. -/
def witMain (o : Opts) : IO UInt32 := do
  let F := Wit.WitFeat.all
  let mut rawOk := 0
  let mut bad := 0
  let mut mutKept := 0
  let mut mutTotal := 0
  let mut shrunk := 0
  let mut sizeBefore := 0
  let mut sizeAfter := 0
  let t0 ← IO.monoMsNow
  for i in [0:o.count] do
    let seed := o.seed + i
    let r := Rng.ofSeed seed
    if Wit.witCheck F (Rand.run (Wit.Raw.univ F o.size) r) then rawOk := rawOk + 1
    let u := Wit.witGenRun F r o.size
    if !Wit.witCheck F u then bad := bad + 1
    let mut cur := u
    for k in [0:o.mutations] do
      let rk := Rng.ofSeed (seed * 1000003 + k)
      mutTotal := mutTotal + 1
      if Wit.witCheck F (Wit.Raw.mutate F rk cur) then mutKept := mutKept + 1
      cur := Wit.witMutRun F rk cur
      if !Wit.witCheck F cur then bad := bad + 1
    -- shrink to "has a function with three parameters or more"
    let p : Silmaril.Wasm.Wit.Universe → Bool := fun U => U.any fun P => P.items.any fun
      | .iface I => I.items.any fun | .func f => f.func.params.length ≥ 3 | _ => false
      | _ => false
    if p u then
      let s := Wit.witShrinker.shrink (fun x => Wit.witCheck F x && p x) u
      shrunk := shrunk + 1
      sizeBefore := sizeBefore + Wit.Raw.size u
      sizeAfter := sizeAfter + Wit.Raw.size s
      if !(Wit.witCheck F s && p s) then bad := bad + 1
  let t1 ← IO.monoMsNow
  IO.println s!"wit count {o.count} size {o.size} seed {o.seed}"
  IO.println s!"raw-valid {rawOk}/{o.count}"
  IO.println s!"raw-mutations-kept {mutKept}/{mutTotal}"
  IO.println s!"shrunk {shrunk} size-before {sizeBefore} size-after {sizeAfter}"
  IO.println s!"checked-output-failures {bad}"
  IO.println s!"time-ms {t1 - t0}"
  return if bad = 0 then 0 else 1

/-- The typed generator (`Gen.Typed`, valid by construction): re-checked here with the checker
it does not use, as a smoke test of the theorem; writes `typed-<seed>.wasm`. -/
def typedMain (o : Opts) (S : FeatureSet) (core3 : Bool := false) : IO UInt32 := do
  let pre := if core3 then "typed3" else "typed"
  let mut ok := 0
  let mut bad := 0
  let mut bytes := 0
  let mut funcs := 0
  let mut instrs := 0
  let t0 ← IO.monoMsNow
  for i in [0:o.count] do
    let seed := o.seed + i
    let m := if core3 then Rand.run (Typed3.module o.size) (Rng.ofSeed seed)
      else Rand.run (Typed.module S o.size) (Rng.ofSeed seed)
    if featCheck S m then ok := ok + 1 else
      bad := bad + 1
      if o.verbose then IO.eprintln s!"seed {seed}: valid={(Silmaril.Wasm.Perf.ValidateR.validateR m).isSome} inFeat={Module.inFeatB S m}"
    funcs := funcs + m.funcs.length
    instrs := instrs + (m.funcs.map fun f => Raw.instrsSize f.body).sum
    match enc m with
    | .ok bs =>
      bytes := bytes + bs.length
      if let some d := o.out then IO.FS.writeBinFile s!"{d}/{pre}-{seed}.wasm" ⟨bs.toArray⟩
    | .error _ => pure ()
  let t1 ← IO.monoMsNow
  IO.println s!"{pre} feat {o.feat} count {o.count} size {o.size} seed {o.seed}"
  IO.println s!"checker-accepts {ok}/{o.count} (failures {bad})"
  IO.println s!"functions {funcs} instructions {instrs} bytes {bytes}"
  IO.println s!"time-ms {t1 - t0}"
  return if bad = 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if o.stage == some 1000000 then
    for st in Sem.semStages, i in [0:Sem.semStages.length] do IO.println s!"{i} {st.name}"
    return 0
  let some S := featOf o.feat | IO.eprintln s!"unknown feature set {o.feat}"; return 2
  if let some d := o.out then IO.FS.createDirAll d
  if o.component then return ← compMain o S
  if o.wit then return ← witMain o
  if o.typed then return ← typedMain o S
  if o.typed3 then return ← typedMain o S (core3 := true)
  let mut rawOk := 0
  let mut validFail := 0
  let mut featFail := 0
  let mut mutTotal := 0
  let mut mutKept := 0
  let mut genBad := 0
  let mut encFail := 0
  let mut shrunk := 0
  let mut sizeBefore := 0
  let mut sizeAfter := 0
  let mut shrinkBad := 0
  let mut bytesTotal := 0
  let mut semChanged := 0
  let mut semKept := 0
  let mut semInSkipped := 0
  let mut semInStages := 0
  let mut semMs := 0
  let t0 ← IO.monoMsNow
  for i in [0:o.count] do
    let seed := o.seed + i
    let r := Rng.ofSeed seed
    let raw := Rand.run (Raw.module S o.size) r
    let v := (Silmaril.Wasm.Perf.ValidateR.validateR raw).isSome
    let f := Module.inFeatB S raw
    if v && f then rawOk := rawOk + 1
    if !v then validFail := validFail + 1
    if !f then featFail := featFail + 1
    if o.verbose && !(v && f) then
      IO.eprintln s!"seed {seed}: valid={v} inFeat={f}\n{repr raw}"
    let m := featGenRun S r o.size
    if !featCheck S m then genBad := genBad + 1
    -- mutation
    let mut cur := m
    for k in [0:o.mutations] do
      let rk := Rng.ofSeed (seed * 1000003 + k)
      mutTotal := mutTotal + 1
      if featCheck S (Raw.mutate S rk cur) then mutKept := mutKept + 1
      cur := featMutRun S rk cur
      if !featCheck S cur then genBad := genBad + 1
    -- shrinking
    if interesting m then
      let s := featShrink S interesting m
      shrunk := shrunk + 1
      sizeBefore := sizeBefore + Raw.size m
      sizeAfter := sizeAfter + Raw.size s
      if !(featCheck S s && interesting s) then shrinkBad := shrinkBad + 1
    -- semantics-preserving mutation (verified optimisation stages)
    let ts0 ← IO.monoMsNow
    let rs := Rng.ofSeed (seed + 77777)
    let stages := match o.stage with
      | some k => [Sem.semStages.getD k .ssa]
      | none => Rand.run Sem.pickStages rs
    let rawSem := Sem.optRun stages m
    -- `Sem.featSemIn P H S` runs `optRunIn S` (`featSemIn_run`, rfl): every output is proved
    -- valid in `S`; count the stages it skipped because their output left `S`
    let semIn := Sem.optRunIn S stages m
    if !featCheck S semIn then genBad := genBad + 1
    let mut cur' := m
    for st in stages do
      semInStages := semInStages + 1
      let m' := Sem.optRun [st] cur'
      if Module.inFeatB S m' then cur' := m' else semInSkipped := semInSkipped + 1
    -- `Sem.featSem P H S` runs exactly this (`Sem.featSem_run`, rfl); the executable does not import
    -- its proofs (`Pipeline.Thms` pulls in modules whose initialisation is huge).
    let sm := if featCheck S rawSem then rawSem else m
    if !featCheck S sm then genBad := genBad + 1
    if featCheck S rawSem then semKept := semKept + 1
    let e0 := enc m
    let e1 := enc sm
    match e0, e1 with
    | .ok a, .ok b => if a != b then semChanged := semChanged + 1
    | _, _ => pure ()
    let ts1 ← IO.monoMsNow
    semMs := semMs + (ts1 - ts0)
    if let some d := o.out then
      if let .ok b := e1 then IO.FS.writeBinFile s!"{d}/sem-{seed}.wasm" ⟨b.toArray⟩
      -- a stage output that left the feature set (diagnosis: `wasm-tools-gen-diag`)
      if !Module.inFeatB S rawSem then
        if let .ok b := Silmaril.Wasm.Binaryen.Exe.encodeModule? rawSem then
          IO.FS.writeBinFile s!"{d}/semleft-{seed}.wasm" ⟨b.toArray⟩
    -- encoding
    match enc m with
    | .error e =>
      encFail := encFail + 1
      if o.verbose then IO.eprintln s!"seed {seed}: encode: {e}"
    | .ok bs =>
      bytesTotal := bytesTotal + bs.length
      if let some d := o.out then
        IO.FS.writeBinFile s!"{d}/gen-{seed}.wasm" ⟨bs.toArray⟩
        if let .ok bs' := enc cur then
          IO.FS.writeBinFile s!"{d}/mut-{seed}.wasm" ⟨bs'.toArray⟩
  let t1 ← IO.monoMsNow
  IO.println s!"feat {o.feat} count {o.count} size {o.size} seed {o.seed}"
  IO.println s!"raw-valid {rawOk}/{o.count} (validation failures {validFail}, feature failures {featFail})"
  IO.println s!"raw-mutations-kept {mutKept}/{mutTotal}"
  IO.println s!"shrunk {shrunk} size-before {sizeBefore} size-after {sizeAfter}"
  IO.println s!"sem-mutations kept {semKept}/{o.count} changed {semChanged} time-ms {semMs}"
  IO.println s!"sem-in-feature-set stages {semInStages} skipped {semInSkipped}"
  IO.println s!"encoded {o.count - encFail}/{o.count} bytes {bytesTotal}"
  IO.println s!"checked-output-failures {genBad + shrinkBad}"
  IO.println s!"time-ms {t1 - t0}"
  return if genBad + shrinkBad = 0 then 0 else 1
