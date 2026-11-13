module

public import Silmaril.Wasm.Tools.Gen.Cmd.Mutate.Defs

/-!
# `wasm-tools shrink`: a terminating, predicate-preserving shrinker of valid modules

* `msize m`: a structural size of a module (definitions, instructions, data bytes);
* `rawCandidates m`: the reductions of `m` (remove an export, the start function, the last
  data or element segment, function, global, type, memory or table; replace a body by
  constants of its result types; drop a top-level instruction of a body; halve a data
  segment);
* `shrinker S seed`: the candidates that are valid in `S` and strictly smaller in `msize`,
  rotated by the seed: a `Shrinker` of the API (`Silmaril.Wasm.Tools.Gen.API`), so
  `Shrinker.shrink` keeps the interestingness predicate, never grows the size and stops at a
  local minimum (`API.Thms`), and every module it returns from a valid input is valid in `S`
  (`Thms.shrink_validIn`).

`wasm-tools shrink` runs the API's `Shrinker.shrinkM` in `IO` with the predicate script as the
predicate (`shrinkM_id`: in `Id` it is `Shrinker.shrink`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Shrink

open Silmaril.Wasm Silmaril.Wasm.Models Mutate

/-- The instructions of a body, nested ones included. -/
def instrCount : List Instr → Nat
  | [] => 0
  | .block _ b :: is => 1 + instrCount b + instrCount is
  | .loop _ b :: is => 1 + instrCount b + instrCount is
  | .if_ _ a b :: is => 1 + instrCount a + instrCount b + instrCount is
  | _ :: is => 1 + instrCount is

/-- **The size of a module**: its definitions, instructions and data bytes. -/
def msize (m : Module) : Nat :=
  m.types.length + m.imports.length + m.tags.length + m.globals.length + m.memories.length +
  m.tables.length + m.funcs.length + (m.funcs.map fun f => instrCount f.body + f.locals.length).sum +
  m.data.length + (m.data.map (·.bytes.size)).sum + m.elems.length +
  (if m.start.isSome then 1 else 0) + m.exports.length

/-- The reductions of `m`. -/
def rawCandidates (m : Module) : List Module :=
  let tys := (funcTypes? m).getD []
  (List.range m.exports.length).map (fun i => { m with exports := dropAt m.exports i }) ++
  (if m.start.isSome then [{ m with start := none }] else []) ++
  (if m.data.isEmpty then [] else [{ m with data := m.data.dropLast }]) ++
  (if m.elems.isEmpty then [] else [{ m with elems := m.elems.dropLast }]) ++
  (if m.funcs.isEmpty then [] else [{ m with funcs := m.funcs.dropLast }]) ++
  (if m.globals.isEmpty then [] else [{ m with globals := m.globals.dropLast }]) ++
  (if m.types.isEmpty then [] else [{ m with types := m.types.dropLast }]) ++
  (if m.memories.isEmpty then [] else [{ m with memories := m.memories.dropLast }]) ++
  (if m.tables.isEmpty then [] else [{ m with tables := m.tables.dropLast }]) ++
  (List.range m.funcs.length).map (fun i =>
    let f := m.funcs.getD i ⟨Smith.ix 0, [], []⟩
    let f' : Func := ⟨f.type, [], constsOf (tys.getD f.type.toNat ⟨[], []⟩).results⟩
    { m with funcs := m.funcs.set i f' }) ++
  (List.range m.funcs.length).flatMap (fun i =>
    let f := m.funcs.getD i ⟨Smith.ix 0, [], []⟩
    (List.range (min f.body.length 32)).map fun j =>
      let f' : Func := ⟨f.type, f.locals, dropAt f.body j⟩
      { m with funcs := m.funcs.set i f' }) ++
  (List.range m.data.length).filterMap (fun i =>
    let d := m.data.getD i ⟨.empty, .passive⟩
    if d.bytes.size = 0 then none else
      let d' : Data := ⟨d.bytes.extract 0 (d.bytes.size / 2), d.mode⟩
      some { m with data := m.data.set i d' })

/-- Rotate a list by `k`. -/
def rotate {α : Type} (l : List α) (k : Nat) : List α :=
  if l.isEmpty then l else l.drop (k % l.length) ++ l.take (k % l.length)

theorem mem_rotate {α : Type} {l : List α} {k : Nat} {a : α} (h : a ∈ rotate l k) : a ∈ l := by
  unfold rotate at h
  split at h
  · exact h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_of_mem_drop h
    · exact List.mem_of_mem_take h

/-- Large reductions, tried first: every export, data or element segment, global or start
removed at once, the second half of the functions removed, every body replaced by constants
of its results. -/
def bulkCandidates (m : Module) : List Module :=
  let tys := (funcTypes? m).getD []
  (if m.exports.length > 1 then [{ m with exports := [] }] else []) ++
  (if m.funcs.length > 1 then [{ m with funcs := m.funcs.take (m.funcs.length / 2) }] else []) ++
  [{ m with funcs := m.funcs.map fun f =>
      ⟨f.type, [], constsOf (tys.getD f.type.toNat ⟨[], []⟩).results⟩ }] ++
  (if m.data.length > 1 then [{ m with data := [] }] else []) ++
  (if m.elems.length > 1 then [{ m with elems := [] }] else []) ++
  (if m.globals.length > 1 then [{ m with globals := [] }] else [])

/-- The candidates: valid in `S`, strictly smaller; the large reductions first, then the
others rotated by the seed. -/
def candidates (S : FeatureSet) (seed : Nat) (m : Module) : List Module :=
  let ok (b : Module) : Bool := decide (msize b < msize m) && Core.featCheck S b
  (bulkCandidates m).filter ok ++ rotate ((rawCandidates m).filter ok) seed

theorem candidates_spec {S : FeatureSet} {seed : Nat} {m b : Module}
    (h : b ∈ candidates S seed m) : msize b < msize m ∧ Core.featCheck S b = true := by
  rcases List.mem_append.mp h with h | h
  · simpa using (List.mem_filter.mp h).2
  · simpa using (List.mem_filter.mp (mem_rotate h)).2

/-- **The shrinker of the model `S`**, a `Shrinker` of the API (`Silmaril.Wasm.Tools.Gen.API`). -/
def shrinker (S : FeatureSet) (seed : Nat) : Shrinker Module := ⟨msize, candidates S seed⟩

/-- `wasm-tools shrink` with a decidable predicate: the API's greedy loop `Shrinker.shrink`,
which terminates by well-founded recursion on `msize`. -/
def shrink (S : FeatureSet) (seed : Nat) (P : Module → Bool) (m : Module) : Module :=
  (shrinker S seed).shrink P m

end Silmaril.Wasm.Tools.Gen.Cmd.Shrink
