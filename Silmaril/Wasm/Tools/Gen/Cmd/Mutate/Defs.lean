module

public import Silmaril.Wasm.Tools.Gen.Cmd.Smith.Defs

/-!
# `wasm-tools mutate`: seeded mutations that keep a module valid in its model

A mutation (`Kind`) maps a module to candidate modules; `mutate S cfg opts seed m` tries the
kinds in an order drawn from `seed` (SplitMix64, `seedBytes`) and returns the first candidate
that `Core.featCheck S` accepts, or `none` (upstream's exit status 3, "There are not applicable
mutations"). The kinds:

* **extending** (`Kind.extending`): append a function type, a function (a generated body, not
  exported), or a global. The output is `extend m d` for a `Delta` `d`: every index of `m`
  keeps its meaning and nothing of `m` changes. `--preserve-semantics` selects the class
  `mutateExtend`: one appended function, when the function types of `m` take numeric
  parameters, which is proved export-equivalent to the input
  (`Silmaril.Wasm.Tools.Gen.Cmd.Equiv.Thms`);
* **reducing** (`Kind.reducing`, the class `--reduce` selects): remove an export, the last
  data or element segment, the start function, the last function, global or type, or replace a
  function body by constants of its result types;
* others: add an export of an existing item, change an integer constant of a body.

Upstream (wasm-mutate) applies other transformations (peephole rewrites, code motion, …) and
its outputs differ; the CLI contract (flags, exit statuses, messages) is the same
(`docs/projects/wasm-components.md`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Mutate

open Silmaril.Wasm Silmaril.Wasm.Models Smith

/-! ## Seeds -/

/-- One SplitMix64 step: the output and the next state. -/
def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- `8 · n` seed bytes from a 64-bit seed. -/
def seedBytes (seed : UInt64) (n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut out : ByteArray := .empty
  for _ in [0:n] do
    let (z, s') := splitmix s
    s := s'
    for k in [0:8] do
      out := out.push ((z >>> (8 * k).toUInt64).toUInt8)
  return out

/-! ## Kinds -/

/-- The mutations. -/
inductive Kind where
  | addType | addFunc | addGlobal
  | removeExport | removeData | removeElem | removeStart | removeFunc | removeGlobal
  | removeType | simplifyBody
  | addExport | changeConst
  deriving DecidableEq, Repr, Inhabited

def Kind.all : List Kind :=
  [.addType, .addFunc, .addGlobal, .removeExport, .removeData, .removeElem, .removeStart,
    .removeFunc, .removeGlobal, .removeType, .simplifyBody, .addExport, .changeConst]

/-- The extending kinds (`--preserve-semantics`). -/
def Kind.extending : Kind → Bool
  | .addType | .addFunc | .addGlobal => true
  | _ => false

/-- The reducing kinds (`--reduce`). -/
def Kind.reducing : Kind → Bool
  | .removeExport | .removeData | .removeElem | .removeStart | .removeFunc | .removeGlobal
  | .removeType | .simplifyBody => true
  | _ => false

/-- What the flags allow. -/
structure Opts where
  preserveSemantics : Bool := false
  reduce : Bool := false

def Opts.allows (o : Opts) (k : Kind) : Bool :=
  (!o.preserveSemantics || k.extending) && (!o.reduce || k.reducing)

/-! ## Extensions -/

/-- What an extending mutation appends. -/
structure Delta where
  types : List RecType := []
  funcs : List Func := []
  globals : List Global := []

/-- Append `d` to `m`. -/
def extend (m : Module) (d : Delta) : Module :=
  { m with types := m.types ++ d.types, funcs := m.funcs ++ d.funcs,
           globals := m.globals ++ d.globals }

/-- The function types of `m`, when every type is a plain function type. -/
def funcTypes? (m : Module) : Option (List FuncType) :=
  m.types.mapM fun r => match r.types with
    | [⟨true, [], .func f⟩] => some f
    | _ => none

/-- The generator context of `m` (function and global types), when its types are plain. -/
def ctxOf? (S : FeatureSet) (m : Module) : Option Ctx := do
  let tys ← funcTypes? m
  let ty (x : TypeIdx) : FuncType := tys.getD x.toNat ⟨[], []⟩
  let fimps := m.imports.filterMap fun i => match i.type with
    | .func x => some (ty x)
    | _ => none
  let gimps := m.imports.filterMap fun i => match i.type with
    | .global g => some g
    | _ => none
  let nMem := m.memories.length + (m.imports.filter Import.isMemory).length
  return { S, funcs := fimps ++ m.funcs.map (ty ·.type), globals := gimps ++ m.globals.map (·.type),
           hasMem := nMem > 0, declared := [], types := tys, nMem }

/-- The deltas an extending kind proposes. -/
def deltas (S : FeatureSet) (cfg : Config) (m : Module) : Kind → G (List Delta)
  | .addType => do
    let ft ← genFuncType S (valTypes S)
    return [{ types := [recOf ft] }]
  | .addFunc => do
    match funcTypes?  m, ctxOf? S m with
    | some tys, some c =>
      if tys.isEmpty then return []
      let ti ← G.choose tys.length
      let ft := tys.getD ti ⟨[], []⟩
      let nl ← G.choose 3
      let ls ← G.many (fun _ => G.pick .i32 (valTypes S)) nl
      let body ← genBody c cfg ft ls c.funcs.length
      return [{ funcs := [⟨ix ti, ls, body⟩] }]
    | _, _ => return []
  | .addGlobal => do
    let vts := valTypes S
    if vts.isEmpty then return []
    let t ← G.pick .i32 vts
    return [{ globals := [⟨⟨.const, t⟩, ← genInit S t⟩] }]
  | _ => return []

/-! ## Other kinds -/

/-- Drop the element at index `i`. -/
def dropAt {α : Type} (l : List α) (i : Nat) : List α := l.take i ++ l.drop (i + 1)

/-- Constants of the types `ts`. -/
def constsOf (ts : List ValType) : List Instr :=
  ts.flatMap fun t => match t with
    | .num (.int .i32) => [.intConst .i32 0]
    | .num (.int .i64) => [.intConst .i64 0]
    | .num (.float .f32) => [.floatConst .f32 0]
    | .num (.float .f64) => [.floatConst .f64 0]
    | .ref r => [.refNull r.heap]
    | .vec _ => [.vecConst 0]

/-- Change the first `i32.const` of a body (not inside blocks) to `k`. -/
def changeFirstConst (k : Nat) : List Instr → List Instr
  | [] => []
  | .intConst .i32 _ :: is => .intConst .i32 (BitVec.ofNat 32 k) :: is
  | i :: is => i :: changeFirstConst k is

/-- The candidates a non-extending kind proposes. -/
def others (m : Module) : Kind → G (List Module)
  | .removeExport => do
    if m.exports.isEmpty then return []
    return [{ m with exports := dropAt m.exports (← G.choose m.exports.length) }]
  | .removeData => return if m.data.isEmpty then [] else [{ m with data := m.data.dropLast }]
  | .removeElem => return if m.elems.isEmpty then [] else [{ m with elems := m.elems.dropLast }]
  | .removeStart => return if m.start.isNone then [] else [{ m with start := none }]
  | .removeFunc => return if m.funcs.isEmpty then [] else [{ m with funcs := m.funcs.dropLast }]
  | .removeGlobal =>
    return if m.globals.isEmpty then [] else [{ m with globals := m.globals.dropLast }]
  | .removeType => return if m.types.isEmpty then [] else [{ m with types := m.types.dropLast }]
  | .simplifyBody => do
    match funcTypes? m with
    | none => return []
    | some tys =>
      if m.funcs.isEmpty then return []
      let i ← G.choose m.funcs.length
      let f := m.funcs.getD i ⟨ix 0, [], []⟩
      let body := constsOf (tys.getD f.type.toNat ⟨[], []⟩).results
      if body.length ≥ f.body.length then return []
      return [{ m with funcs := m.funcs.set i ⟨f.type, f.locals, body⟩ }]
  | .addExport => do
    let nf := (m.imports.filter fun i => match i.type with | .func _ => true | _ => false).length +
      m.funcs.length
    if nf = 0 then return []
    let x ← G.choose nf
    let base ← genName
    let name := s!"{base}m{m.exports.length}"
    if m.exports.any (·.name == name) then return []
    return [{ m with exports := m.exports ++ [⟨name, .func (ix x)⟩] }]
  | .changeConst => do
    if m.funcs.isEmpty then return []
    let i ← G.choose m.funcs.length
    let f := m.funcs.getD i ⟨ix 0, [], []⟩
    let k ← G.bytes 4
    let body := changeFirstConst k f.body
    return [{ m with funcs := m.funcs.set i ⟨f.type, f.locals, body⟩ }]
  | _ => return []

/-- The kinds in the order `seed` draws (a seeded rotation of a seeded permutation). -/
def order (seed : UInt64) (ks : List Kind) : List Kind :=
  let keys := ks.zipIdx.map fun (k, i) => ((splitmix (seed + i.toUInt64)).1, k)
  (keys.mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)

/-- Every function type of `m` takes numeric parameters only: the side condition under which
appending an unreferenced function is an export equivalence (silmaril's
`exportEquiv_append_unreferenced_func`; without it a session could pass a reference to the new
function to an export, and the statement is false). -/
def numParamsB (m : Module) : Bool :=
  m.typeDefinitions.all fun st => match st.body with
    | .func ft => ft.params.all isNum
    | _ => true

/-- `m` with one more defined function at the end (silmaril's `InlDF.appendFunc`). -/
def appendFunc (m : Module) (f : Func) : Module := { m with funcs := m.funcs ++ [f] }

/-- **The semantics-preserving mutation** (`--preserve-semantics`): append one generated,
unexported function. Proposed only when every function type of `m` takes numeric parameters
(`numParamsB`); the first of four generated functions that keeps `m` valid in `S`.
`Equiv.Thms.mutate_preserve_equiv` proves the output export-equivalent to the input. -/
def mutateExtend (S : FeatureSet) (cfg : Config) (seed : UInt64) (m : Module) :
    Option Module :=
  if numParamsB m then
    let ds := ((List.range 4).mapM fun _ => deltas S cfg m .addFunc).run' (seedBytes seed 512)
    ((ds.flatten.flatMap (·.funcs)).map (appendFunc m)).find? (Core.featCheck S)
  else none

/-- **`wasm-tools mutate` at the model `S`**: the first valid candidate of the allowed kinds,
in seeded order. With `--preserve-semantics` it is `mutateExtend` (`Thms`). -/
def mutate (S : FeatureSet) (cfg : Config) (o : Opts) (seed : UInt64) (m : Module) :
    Option Module :=
  if o.preserveSemantics then
    if o.reduce then none else mutateExtend S cfg seed m
  else
    let ks := (order seed Kind.all).filter o.allows
    let cands := (ks.mapM fun (k : Kind) => do
        if k.extending then return (← deltas S cfg m k).map (extend m)
        else others m k).run' (seedBytes seed 512)
    cands.flatten.find? (Core.featCheck S)

end Silmaril.Wasm.Tools.Gen.Cmd.Mutate
