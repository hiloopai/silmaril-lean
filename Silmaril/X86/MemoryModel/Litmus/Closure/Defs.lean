module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.Litmus.Domain.Defs

/-!
# Value-domain closure of the litmus trace sets: definitions

The verdicts
(`Silmaril.X86.MemoryModel.Litmus.Verdicts`) are about the candidate executions over the traces
extracted with the value domain `Test.domain`: every read returns a value of that domain. A
concurrent execution of the bytes could, a priori, read some other value, and then the
verdicts would miss it. **Closure** says it cannot: every execution over traces extracted with
**any** domain, consistent under SC, TSO or XL, is already one over `Test.traces`.

## The semantics of the bytes over any domain

`AxReachAny t M f`: for **some** finite value domain `D`, extraction over `D` succeeds and `f` is
an `AxReach` final state over those traces. Every execution has finitely many reads, so taking
`D` to be the values it reads, this covers every execution whose per-thread behaviour the
extractor captures (extractor soundness, completeness `extract_complete`).

## The certificate

`Test.closureCert t` is a Boolean, checked per test by `decide`:

* every thread is **straight-line code** (`Thread.skel` succeeds, so every trace over every
  domain has the same events; `extract_skel`) with at most one event per instruction;
* `Test.dom0` (the initial values and the condition's values) is nonempty;
* the units of one representative trace per thread (`Test.reps`) are **untorn** (no unit is split
  by `units`) and pairwise in one cell or disjoint (`cellsOk`); by the skeleton this holds for
  every choice of traces over every domain;
* the initial bytes of every read unit encode a value of `dom0`;
* with `R` the number of read units and `Test.chain k` the domain after `k` rounds of "add every
  value an extracted trace writes" (no early stop), extraction over `chain k` succeeds for every
  `k < R`, and every value of `chain R` is in `Test.domain`.

The theorem (`closure_of_cert`, `Closure/Thms.lean`) is a **rank argument**: a read whose
`(po ∪ rf)⁺`-predecessors include `k` reads returns a value of `chain (k + 1)` (its source write
was computed from reads of lower rank), and no read has `R` such predecessors (no thin air). It
replaces the informal argument that `n` rounds of the domain iteration suffice, which the five
`xadd`/`inc` tests relied on.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)

/-- **The final states of model `M` over the bytes, with any value domain.** -/
def AxReachAny (t : Test) (M : Exec → Prop) (f : Final) : Prop :=
  ∃ D T, t.extractOver D = some T ∧ AxReach t T M f

/-- The initial domain of `Test.domain`: the initial values and the condition's values. -/
def Test.dom0 (t : Test) : List Nat :=
  uniq ((t.locs.map Loc.init) ++ t.cond.atoms.map Atom.value)

/-- The domain after `k` rounds of adding every value an extracted trace writes. -/
def Test.chain (t : Test) : Nat → List Nat
  | 0 => t.dom0
  | k + 1 => t.domStep (t.chain k)

/-- The shape of a unit: everything but the bytes written and the annotation. -/
def shape (u : Ev) : Ev := { u with data := [], ann := .wb }

/-- One representative trace per thread: the first trace over `Test.domain`. -/
def Test.reps (t : Test) : Option (List XTrace) :=
  t.traces.bind fun T => T.mapM List.head?

/-- Every thread is straight-line code with at most one event per instruction. -/
def Test.straight (t : Test) : Bool :=
  (t.threads.mapIdx fun k th =>
    match (t.xthread k th).skel t.fuel with
    | some S => S.all fun es => decide (es.length ≤ 1)
    | none => false).all id

/-- **The closure certificate** (see the module documentation). -/
def Test.closureCert (t : Test) : Bool :=
  t.straight &&
    match t.traces, t.reps with
    | some _, some reps =>
      let us := accUnits reps
      let R := (us.filter fun u => u.1.isR).length
      !t.dom0.isEmpty &&
        us.all (fun u => !tearAcc us u.1) &&
        cellsOk (us.map Prod.fst) &&
        us.all (fun u => !u.1.isR ||
          decide (Silmaril.X86.Litmus.InDom t.dom0 (u.1.bytes.map t.initB))) &&
        (List.range R).all (fun k => (t.extractOver (t.chain k)).isSome) &&
        (t.chain R).all (memB · t.domain)
    | _, _ => false

end Silmaril.X86.MemoryModel.Litmus
