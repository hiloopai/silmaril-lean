module

public import Silmaril.Wasm.JcoTool.KCoreRun.Thms
public import Silmaril.Wasm.JcoTool.KDrop.Thms
public import Silmaril.Wasm.Component.Algebra.StreamGame.Defs

/-!
# The game reading of the callback runtime

`KCoreRun.CRStep` runs a generated stream module on silmaril-lean's Core 3.0 `Step` (Core
invocations of its callback, the built-ins as host calls over the drop store). This module
reads such a runtime as a **strategy of the stream game** (`Algebra.StreamGame.den`), by the
Kahn principle: a deterministic stream process is the stream function it computes, and the
stream game of a transformer depends only on its outputs so far (`Tr.runP`) and its whole
outputs (`Tr.run`) (`StreamGame.den_congr`).

* `ofObs P R`: the transformer whose outputs so far are `P` and whose whole outputs are `R`
  (it remembers its input; an item emits what `P` adds, the end what `R` adds).
* **The pipe harness** `PSys`/`PStep xs k open R`: a source of `xs`, one module whose steps are
  `R` (the drop runtime `DRStep`, or the runtime on Core), and a sink, wired as the `KDrop` chain
  `kchain xs [k]` (the module reads stream `0` and writes stream `1`). With `open = true` the
  source never drops its writable end: the input has not ended.
* **The observation** `Obs`: `whole xs ys` (a run of the closed pipe on `xs` ends with the sink
  done holding `ys`) and `part xs ys` (a run of the open pipe on `xs` reaches a point after which
  the sink never changes, holding `ys`). `Obs.Reads O T`: these are exactly `T.run` and
  `T.runP`. **`Obs.game O`**: the strategy reading, `den (ofObs P R)` for the output functions
  `P`, `R` the observation determines (by choice; `KRead.Thms`: `game_eq_den`).
* **The runtime on Core, faithfully**: `CRStepU` is `CRStep` with the callback's `i32` result
  read as the unsigned number it is (`code < 2 ^ 32`). `CRStep` lets any `code` with the same
  low 32 bits through, so `modeOf code` (which reads `code / 16`) is not determined by the Core
  run; `CRStepU` is the runtime the reference machine is (it reads the `i32`).
* `coreObs`, `dropObs`: the observations of a generated module on Core (from a Core store `cs₀`
  holding the instantiated module, `InstR`/`CbAt`) and under the drop runtime.
* `UniqueVal o hb ma`: Core with the built-ins as host calls has unique value results, in the
  deterministic profile (proved for injective `hb`, `KRead.Thms.unique_val`).
* `NoTrapAt k N`: the callback of `genD k N` never traps in the pipe model. It and liveness (the
  pipe model of `genD k N` reads as `trV k`) are theorems for every kernel whose bounds hold
  (`KLive.genD_notrap_fits`, `KLive.genD_reads_fits`); round 2's frozen targets
  `Task.genD_notrap`, `Task.genD_reads` (for all kernels) are replaced by these.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KRead

open Silmaril.Games
open Silmaril.Wasm.Component (Val sigU)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop (DStore DWait)
open Silmaril.Wasm.Component.Streams.Net (NSt NStep initStore rh wh)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (BI MS Mode M32 deliver modeOf trV Prog)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD kchain initMSD wfD)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store Config ModuleInst invoke vals)
open Silmaril.Wasm.Numerics (GrowKind)

/-! ## Transformers from output functions -/

/-- **The transformer of two output functions**: outputs so far `P`, whole outputs `R`. -/
def ofObs (P R : List Val → List Val) : Tr (List Val) Val Val where
  init := []
  step s v := (s ++ [v], (P (s ++ [v])).drop (P s).length)
  flush s := (R s).drop (P s).length

/-! ## The pipe harness -/

/-- A source, one module (state `X`), a sink, and the store. -/
structure PSys (X : Type) where
  st : DStore
  src : NSt KSt
  m : X
  snk : NSt KSt

/-- The source node of the pipe on `xs` (node `0` of `kchain xs [k]`). -/
abbrev srcN (xs : List Val) (k : KM) := (kchain xs [k]).node ⟨0, by simp [kchain]⟩

/-- The sink node (node `2`). -/
abbrev snkN (xs : List Val) (k : KM) := (kchain xs [k]).node ⟨2, by simp [kchain]⟩

/-- The source's output has been closed (its writable end dropped). -/
def Closed (x : NSt KSt) : Prop := ∃ d a, x.outs = [⟨.closed d, a⟩]

/-- **One step of the pipe**: the source (which, if `open`, never closes), the module (`R`, on
the store), or the sink. -/
inductive PStep {X : Type} (xs : List Val) (k : KM) (op : Bool)
    (R : DStore → X → DStore → X → Prop) : PSys X → PSys X → Prop
  | src {c : PSys X} {st' x'} : NStep (srcN xs k) ((kchain xs [k]).ws 0) c.st c.src st' x' →
      (op = true → ¬ Closed x') → PStep xs k op R c { c with st := st', src := x' }
  | mod {c : PSys X} {st' m'} : R c.st c.m st' m' → PStep xs k op R c { c with st := st', m := m' }
  | snk {c : PSys X} {st' x'} : NStep (snkN xs k) ((kchain xs [k]).ws 2) c.st c.snk st' x' →
      PStep xs k op R c { c with st := st', snk := x' }

/-- Pipe steps, iterated. -/
abbrev PSteps {X : Type} (xs : List Val) (k : KM) (op : Bool) (R : DStore → X → DStore → X → Prop) :=
  Relation.ReflTransGen (PStep xs k op R)

/-- The start: the chain's setup store, the source and the sink initial, the module `m₀`. -/
def PSys.init {X : Type} (xs : List Val) (k : KM) (m₀ : X) : PSys X where
  st := initStore (kchain xs [k])
  src := NSt.init (srcN xs k)
  m := m₀
  snk := NSt.init (snkN xs k)

/-! ## Observations and the strategy reading -/

/-- What a runtime is observed to output: on a complete input, and on an unfinished one. -/
structure Obs where
  whole : List Val → List Val → Prop
  part : List Val → List Val → Prop

/-- **The observation of a runtime** (module steps `R`, start `m₀`): `whole xs ys`, a run of the
closed pipe on `xs` ends with the sink done holding `ys`; `part xs ys`, a run of the open pipe on
`xs` reaches a point after which the sink's output never changes, and it holds `ys`. -/
def obsOf {X : Type} (k : KM) (R : DStore → X → DStore → X → Prop) (m₀ : X) : Obs where
  whole xs ys := ∃ c, PSteps xs k false R (PSys.init xs k m₀) c ∧ (∃ b, c.snk.rd = .gone b) ∧
    c.snk.got = ys
  part xs ys := ∃ c, PSteps xs k true R (PSys.init xs k m₀) c ∧
    (∀ c', PSteps xs k true R c c' → c'.snk.got = c.snk.got) ∧ c.snk.got = ys

/-- The observation **reads as** `T`: its whole outputs are exactly `T.run`, its outputs so far
exactly `T.runP`. -/
def Obs.Reads {σ : Type} (O : Obs) (T : Tr σ Val Val) : Prop :=
  ∀ xs ys, (O.whole xs ys ↔ ys = T.run xs) ∧ (O.part xs ys ↔ ys = T.runP xs)

open Classical in
/-- The whole output the observation determines (any one, by choice; `[]` if none). -/
noncomputable def Obs.wholeF (O : Obs) (xs : List Val) : List Val :=
  if h : ∃ ys, O.whole xs ys then Classical.choose h else []

open Classical in
/-- The output so far the observation determines. -/
noncomputable def Obs.partF (O : Obs) (xs : List Val) : List Val :=
  if h : ∃ ys, O.part xs ys then Classical.choose h else []

/-- **The strategy reading of a runtime**: the stream game of the transformer of its observed
output functions. -/
noncomputable def Obs.game (O : Obs) : Strategy sigU sigU :=
  Silmaril.Wasm.Component.Algebra.StreamGame.den (ofObs O.partF O.wholeF)

/-! ## The runtime on Core, reading the callback's result as an unsigned `i32` -/

variable {H : Type}

/-- **One step of the callback runtime on Core 3.0**, as `CRStep`, with the callback's result
`code` the unsigned value of the `i32` the Core run returns (`code < 2 ^ 32`). -/
inductive CRStepU (Pf : Numerics.Profile) (hb : BI → H) (ma a : Nat) :
    DStore × Store H × Option (Nat × Nat) × Mode → DStore × Store H × Option (Nat × Nat) × Mode →
      Prop where
  | ready {st st' : DStore} {cs cs' : Store H} {rp rp' : Option (Nat × Nat)} {code : Nat} {md : Mode}
      (hc : code < M32)
      (hrun : HSteps Pf hb ma ((st, rp), invoke cs a ([0, 0, 0].map (Execution.Core.Val.i32 ∘ w)))
        ((st', rp'), ⟨cs', {}, vals [Execution.Core.Val.i32 (w code)]⟩))
      (hmd : modeOf code = some md) :
      CRStepU Pf hb ma a (st, cs, rp, .ready) (st', cs', rp', md)
  | event {st st₁ st' : DStore} {cs cs₁ cs' : Store H} {rp rp₁ rp' : Option (Nat × Nat)}
      {s h code : Nat} {e : Silmaril.Wasm.Component.Async.Event} {md : Mode}
      (hw : DWait st s h st₁ e) (hwf : wfD e = true) (hd : deliverC ma cs e rp = (cs₁, rp₁))
      (hc : code < M32)
      (hrun : HSteps Pf hb ma ((st₁, rp₁), invoke cs₁ a ([e.code.toNat, e.index, e.payload].map (Execution.Core.Val.i32 ∘ w)))
        ((st', rp'), ⟨cs', {}, vals [Execution.Core.Val.i32 (w code)]⟩))
      (hmd : modeOf code = some md) :
      CRStepU Pf hb ma a (st, cs, rp, .waiting s) (st', cs', rp', md)

/-- The module state of the runtime on Core: the Core store, the pending read, the mode. -/
abbrev CM (H : Type) := Store H × Option (Nat × Nat) × Mode

/-- `CRStepU` as a module step of the pipe harness. -/
def coreR (Pf : Numerics.Profile) (hb : BI → H) (ma a : Nat) (st : DStore) (x : CM H)
    (st' : DStore) (x' : CM H) : Prop :=
  CRStepU Pf hb ma a (st, x.1, x.2.1, x.2.2) (st', x'.1, x'.2.1, x'.2.2)

/-- The waitable set of the module of the pipe (node `1` of `kchain xs [k]`). -/
def wsM : Nat := 2 * 2 + 1 + 1

/-- The machine of `genD k N` after the lift, in the pipe. -/
def m₀ (k : KM) : MS := initMSD k (rh 0) (wh 1) wsM

/-- **The observation of a generated module on Core 3.0**, started from a Core store `cs₀`. -/
noncomputable def coreObs (Pf : Numerics.Profile) (hb : BI → H) (ma a : Nat) (k : KM)
    (cs₀ : Store H) : Obs :=
  obsOf k (coreR Pf hb ma a) (cs₀, none, .ready)

/-- The observation of a generated module under the drop runtime. -/
def dropObs (k : KM) (N : Nat) : Obs := obsOf k (DRStep (genD k N)) (m₀ k)

/-- A Core store `cs₀` holds the instantiated `genD k N` (instance `mi`, memory `ma`, callback at
`a`) with the globals of the lift and a zero memory. -/
def Inst0 (hb : BI → H) (ma a : Nat) (k : KM) (N : Nat) (mi : ModuleInst) (cs₀ : Store H) : Prop :=
  InstR hb ma cs₀ mi (m₀ k).g (m₀ k).m ∧ CbAt cs₀ mi (genD k N) a

/-! ## No trap -/

/-- A value configuration of Core with the built-ins: an empty frame and values only. -/
def ValCfg (y : HQ × Config H) : Prop := ∃ cs vs, y.2 = ⟨cs, {}, vals vs⟩

/-- Core 3.0 with the built-ins `hb` as host calls (`HStep`) has **unique value results** in the
deterministic profile: two runs from one configuration that both end in value configurations end
in the same one. Proved when `hb` is injective (`KRead.Thms`, `unique_val`). -/
def UniqueVal (o : GrowKind → Nat → Nat → Nat → Bool) (hb : BI → H) (ma : Nat) : Prop :=
  ∀ x y z : HQ × Config H, HSteps (Numerics.Profile.deterministic o) hb ma x y →
    HSteps (Numerics.Profile.deterministic o) hb ma x z → ValCfg y → ValCfg z → y = z

/-- The callback of `P` does not trap from the machine `ms` on the store `st`: after `YIELD` its
invocation returns a mode, and after `WAIT` it does for every event the store delivers. -/
def NoTrap (P : Prog) (st : DStore) (ms : MS) : Prop :=
  (ms.mode = .ready → ∃ r, Silmaril.Wasm.JcoTool.KDrop.dinvoke P.cb [0, 0, 0] st ms = some r) ∧
  ∀ s h st₁ e, ms.mode = .waiting s → DWait st s h st₁ e → wfD e = true →
    ∃ r, Silmaril.Wasm.JcoTool.KDrop.dinvoke P.cb [e.code.toNat, e.index, e.payload] st₁ (deliver e ms) = some r

/-- **No trap at a kernel**: in the pipe model (open or closed), the callback of `genD k N` never
traps (the events the store delivers at each point are those its dispatch handles). Proved for
every kernel whose bounds hold (`KLive.genD_notrap_fits`). (Round 2 stated this as a frozen
target for *all* kernels, `Task.genD_notrap`; it is not claimed for kernels whose buffer or output
can overflow the module's fixed regions: those trap by design, e.g. `kLines` on a line longer
than `CAP`, which the stream suites observe.) -/
def NoTrapAt (k : KM) (N : Nat) : Prop :=
  ∀ (xs : List Val) (op : Bool) (c : PSys MS),
    PSteps xs k op (DRStep (genD k N)) (PSys.init xs k (m₀ k)) c → NoTrap (genD k N) c.st c.m

/-- The kernel's flush is empty in its `done` states (true of `take`, `map`, `filter`, `lines`,
`rechunk`): the module flushes when it becomes done, the stream game only at the input's end. -/
def FlushNil (k : KM) : Prop := ∀ s, (trV k).done s = true → (trV k).flush s = []

end Silmaril.Wasm.JcoTool.KRead
