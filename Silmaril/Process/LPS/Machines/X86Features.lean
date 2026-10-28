module

public import Silmaril.X86.Features.Lattice.Wire
public import Silmaril.X86.Features.Ext.Avx.Extension
public import Silmaril.X86.Features.Ext.Avx.Footprint
public import Silmaril.Process.LPS.Machines.X86WireFlagOracle
public import Silmaril.Process.LPS.StepTransfer
public import Silmaril.Process.LPS.Machines.X86Launch

/-!
# The feature-parametric x86 machine under the native LPS process layer

`x86Features c : UserIsa` runs the machine of a configuration `c` of the
feature-parametric x86 ISA (`Silmaril.X86.Features.Config`: a feature set and
pairwise-disjoint extension decoders) with the interface of the native x86
instances (`x86ExtNative`, `x86Wire`, `x86WireDf0RepStosq`):

* raw native syscall numbers in the pending slot, the six argument registers,
  the native `ARCH_SET_FS` effect and the four-level x86 address space;
* `syscall` (`0F 05`) is recognised first, from two executable bytes; with an
  undefined status flag it is `unmodeled` (the deterministic instance), or the
  flags are completed by an explicit oracle (`x86FeaturesWithFlagOracle`, as
  `x86WireDf0RepStosqWithFlagOracle`);
* DF-clear `REP STOSQ` (`F3 48 AB`) is recognised next and runs as the
  microsteps of `X86RepStosq.iterate`;
* everything else is one step of `Config.step c`. Outcomes: an architectural
  fault, a missing feature (`featureUD`: #UD, SIGILL) and a fetch fault are
  deaths (`fault`); undecodable bytes, `featureAlias`, `unmodeled` and a
  condition on an undefined flag are `unmodeled` (chaos).

## Access reports

The instance reports accesses (`reportsAccesses := true`). An integer
instruction reports its consumed span and `X86Accesses.canonical`, exactly as
`x86ExtNative`. An extension instruction reports its consumed span and the data
spans of an `ExtSpans` table, which is keyed by the instruction bytes (not by
the extension), so the same table is used at every configuration. A retired
extension instruction the table does not describe is `unmodeled`: the run
fails closed instead of guessing a footprint. `defaultSpans` describes the
`X86.Ext.Wire` forms (`X86Accesses.wire`, as `x86Wire`) and the AVX lane
(register forms access no data, memory forms their operand); every other lane
is `unmodeled` when it retires, until its table is written.

The table is trusted only as far as these proofs go: `step_wireRep` shows the
`Wire` entries are `x86Wire`'s reports, and `avxSpans_footprint` shows that a
retiring `Avx.exec` of the instruction `Avx.decode` reads (non-store forms) and
writes only inside the AVX entries. Since the table is keyed by bytes, both
facts are about the extension that decodes them as `Ext.Wire` (respectively
`Avx.decode`) does: every configuration built from `wireExt` and `Avx.ext`. A
configuration whose extension decodes the same bytes differently has no such
fact, and must use its own table (`x86FeaturesWith`).

## Results

* `step_le_of_settles`, `transfer_of_settles`: for `c ≤ d`, an image that never
  reaches an unsettled instruction under `c` (a missing feature, a feature
  alias, undecodable bytes or a truncated fetch, `Settles`) has the same
  traces, errors, all-traces-error and unmodelled verdicts, and the same
  `MustExitInAt` judgments, under `d`; `transfer_of_errorFree` is the corollary
  for error-free launches, the form of `Features.lps_transfer`.
* `step_native`: on its fragment (a `syscall`, or bytes `X86.Ext` decodes whose
  feature check passes), the step is `x86NativeStep` on the integer part of
  the state; `step_wireRep`: on the fragment of `x86WireDf0RepStosq`
  (`syscall`, `REP STOSQ`, or bytes `Ext.Wire` fetches), the step of
  `wireConfig F p` is `X86RepStosq.step p`; `oracleStep_wireRep` is the same
  for the flag-oracle instances. Outside these fragments the native instances
  are `unmodeled` or a fetch fault and the feature machine may continue.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines

open Silmaril.X86 (Byte fetchWindow maxInstrLength)
open Silmaril.X86.Features (Extension extDecode FeatureSet baseFeatures baseCheck)

local notation "FConfig" => Silmaril.X86.Features.Config
local notation "FOutcome" => Silmaril.X86.Features.Outcome

/-- The extended machine state with LPS's pending-syscall slot. -/
structure X86FState where
  m : Silmaril.X86.Features.MState
  pending : Option Word

namespace X86Features

/-- The extended architectural state. -/
abbrev FState := Silmaril.X86.Features.State

/-! ## State maps -/

/-- The integer view of an extended LPS state. -/
def proj (s : X86FState) : X86State := ⟨⟨s.m.state.core, s.m.memory⟩, s.pending⟩

/-- An integer LPS state over the vector state of `v`. -/
def embed (v : FState) (t : X86State) : X86FState := ⟨⟨v.setCore t.m.core, t.m.memory⟩, t.pending⟩

@[simp] theorem proj_embed (v : FState) (t : X86State) : proj (embed v t) = t := rfl

theorem embed_proj (s : X86FState) : embed s.m.state (proj s) = s := rfl

/-- An integer machine result over the vector state of `v`. -/
def liftResult (v : FState) :
    MachineResult (AccessReport X86State) → MachineResult (AccessReport X86FState)
  | .ok r => .ok ⟨embed v r.value, r.accessed⟩
  | .fault => .fault
  | .unmodeled => .unmodeled

/-! ## Access tables -/

/-- Data spans of extension instructions, keyed by the fetch window and the
consumed length; `none` when the table does not describe the instruction. -/
abbrev ExtSpans := List Byte → Nat → FState → Option (List (Word × Nat))

/-- The empty table. -/
def ExtSpans.empty : ExtSpans := fun _ _ _ => none

/-- The first table that describes the instruction. -/
def ExtSpans.orElse (a b : ExtSpans) : ExtSpans := fun w n v =>
  match a w n v with
  | some r => some r
  | none => b w n v

/-- The `Ext.Wire` forms: `X86Accesses.wire`, as `x86Wire` reports them. -/
def wireSpans : ExtSpans := fun w n v =>
  match Silmaril.X86.Ext.Wire.decode w with
  | some d => if d.length = n then some (X86Accesses.wire v.core d) else none
  | none => none

/-- The data spans of an AVX instruction that retires: none for a register
ModRM.rm; the stored bytes for a store form; the `memBytes` source bytes for
every other form (every retiring non-store form reads its ModRM.rm source,
`Avx.exec`). -/
def avxData (x : Silmaril.X86.Features.Avx.Instr) (n : Nat) (v : FState) :
    List (Word × Nat) :=
  match x.rm with
  | .reg _ => []
  | .mem m =>
    let a := m.addr v.core (v.rip + BitVec.ofNat 64 n)
    match Silmaril.X86.Features.Avx.store? x.op with
    | some kind => [(a, if kind == .full && x.l then 32 else 16)]
    | none => [(a, Silmaril.X86.Features.Avx.memBytes x.op x.l)]

/-- The AVX lane. -/
def avxSpans : ExtSpans := fun w n v =>
  match Silmaril.X86.Features.Avx.decode w with
  | some (i, k) => if k = n then some (avxData i.1 n v) else none
  | none => none

/-- The default table: `Ext.Wire`'s forms, then the AVX lane. -/
def defaultSpans : ExtSpans := wireSpans.orElse avxSpans

/-- **The AVX entries cover the lane's accesses**: when `avxSpans` describes the
bytes that `Avx.decode` decodes as `i` with length `n`, a retiring `Avx.exec`
changes no byte outside the reported spans, and a form that is not a store
retires the same way on every memory with the same bytes inside them. -/
theorem avxSpans_footprint {w : List Byte} {n : Nat} {v : FState} {r : List (Word × Nat)}
    {i : Silmaril.X86.Features.Avx.Syntax}
    (hd : Silmaril.X86.Features.Avx.decode w = some (i, n)) (hr : avxSpans w n v = some r)
    {t : FState} {memory memory' : Silmaril.Process.Memory}
    (h : Silmaril.X86.Features.Avx.exec i n v memory = .retired t memory') :
    memory.WritesWithin memory'
        (fun location => ∃ p ∈ r, p.1.toNat ≤ location ∧ location < p.1.toNat + p.2) ∧
      (Silmaril.X86.Features.Avx.store? i.1.op = none → ∀ memory₂ : Silmaril.Process.Memory,
        (∀ p ∈ r, memory₂.readBytes p.1.toNat p.2 = memory.readBytes p.1.toNat p.2) →
        Silmaril.X86.Features.Avx.exec i n v memory₂ = .retired t memory₂) := by
  simp only [avxSpans, hd, ite_true, Option.some.injEq] at hr
  subst hr
  refine ⟨?_, fun hst memory₂ hb => ?_⟩
  · have hw := Silmaril.X86.Features.Avx.exec_writesWithin h
    refine ⟨hw.1, fun location hout => hw.2 location ?_⟩
    rintro ⟨m, kind, hrm, hst, h1, h2⟩
    exact hout ⟨(m.addr v.core (v.rip + BitVec.ofNat 64 n),
      Silmaril.X86.Features.Avx.storeBytesLen kind i.1.l),
      by simp [avxData, hrm, hst, Silmaril.X86.Features.Avx.storeBytesLen], h1, h2⟩
  · exact Silmaril.X86.Features.Avx.exec_reads hst h memory₂ fun m hrm =>
      hb (m.addr v.core (v.rip + BitVec.ofNat 64 n),
        Silmaril.X86.Features.Avx.memBytes i.1.op i.1.l) (by simp [avxData, hrm, hst])

/-- The accesses of the instruction at RIP, when known: the consumed span and
the data spans. -/
def spansAt (sp : ExtSpans) (exts : List Extension) (m : Silmaril.X86.Features.MState) :
    Option (List (Word × Nat)) :=
  match Silmaril.X86.Ext.fetch m.memory m.state.core.rip.toNat with
  | .decoded i n => some ((m.state.core.rip, n) :: X86Accesses.canonical m.state.core n i)
  | _ =>
    match extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
    | some ⟨_, _, n⟩ =>
      (sp (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) n m.state).map
        ((m.state.core.rip, n) :: ·)
    | none => none

/-! ## The step -/

/-- A retirement with its access report, `unmodeled` without one. -/
def report (spans : Option (List (Word × Nat))) (next : Silmaril.X86.Features.MState) :
    MachineResult (AccessReport X86FState) :=
  match spans with
  | some accessed => .ok ⟨⟨next, none⟩, accessed⟩
  | none => .unmodeled

/-- LPS's outcome split of a feature-machine outcome. -/
def ofOutcome (spans : Option (List (Word × Nat))) : FOutcome → MachineResult (AccessReport X86FState)
  | .retired next => report spans next
  | .returned final => report spans final
  | .featureUD _ => .fault
  | .fault _ => .fault
  | .fetchFault => .fault
  | .featureAlias _ => .unmodeled
  | .undefinedCondition _ => .unmodeled
  | .undecodable => .unmodeled
  | .unmodeled => .unmodeled

/-- One instruction of configuration `c`. -/
def step (sp : ExtSpans) (c : FConfig) (s : X86FState) : MachineResult (AccessReport X86FState) :=
  if s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05] then
    match rflagsImage s.m.state.core.flags with
    | none => .unmodeled
    | some _ =>
      .ok ⟨{ s with pending := some (s.m.state.core.read .rax) }, [(s.m.state.core.rip, 2)]⟩
  else if s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes then
    liftResult s.m.state (X86RepStosq.iterate (proj s))
  else ofOutcome (spansAt sp c.exts s.m) (c.step 0 s.m)

/-- The process interface shared by every configuration. -/
def base (sp : ExtSpans) : UserIsa where
  State := X86FState
  step _ := step sp Silmaril.X86.Features.Config.bot
  svcPending s := s.pending
  syscallArgs s := [.rdi, .rsi, .rdx, .r10, .r8, .r9].map s.m.state.core.read
  readByte _ s := viewByte s.m.memory .read
  writableByte _ s := viewByte s.m.memory .write
  applyEffect s eff := embed s.m.state (x86ApplyEffectNative (proj s) eff)
  advancePastSvc s := embed s.m.state (x86AdvancePastSvc (proj s))
  init segs pc sp stack :=
    let t := x86ExtNative.init segs pc sp stack
    embed (Silmaril.X86.Features.State.ofCore t.m.core) t
  reportsAccesses := true
  entryFetchable segs pc :=
    (initialMemory segs 0 []).fetchBytes pc 3 = some X86RepStosq.bytes ||
      x86ExtNative.entryFetchable segs pc
  addressSpace := x86ExtNative.addressSpace

end X86Features

open X86Features in
/-- Configuration `c` as a native LPS user machine, with access table `sp`. -/
def x86FeaturesWith (sp : X86Features.ExtSpans) (c : FConfig) : UserIsa :=
  (base sp).withStep fun _ => step sp c

/-- Configuration `c` as a native LPS user machine (`defaultSpans`). -/
def x86Features (c : FConfig) : UserIsa := x86FeaturesWith X86Features.defaultSpans c

namespace X86Features

/-! ## The flag-oracle instance -/

/-- The state with the private oracle counter. -/
structure OState where
  native : X86FState
  counter : Nat

/-- Complete the undefined status flags with an oracle choice. -/
def completeF (s : X86FState) (choice : X86FlagChoices.Choice) : X86FState :=
  let core := { s.m.state.core with
    flags := X86FlagChoices.completeFlags s.m.state.core.flags choice }
  { s with m := { s.m with state := s.m.state.setCore core } }

theorem proj_completeF (s : X86FState) (choice : X86FlagChoices.Choice) :
    proj (completeF s choice) = X86FlagChoices.completeState (proj s) choice := rfl

/-- Attach the counter. -/
def liftO (counter : Nat) :
    MachineResult (AccessReport X86FState) → MachineResult (AccessReport OState)
  | .ok r => .ok ⟨⟨r.value, counter⟩, r.accessed⟩
  | .fault => .fault
  | .unmodeled => .unmodeled

/-- One step with the oracle: only a fetched `syscall` completes the flags and
advances the counter (`X86FlagOracle.stepUsing`). -/
def oracleStep (sp : ExtSpans) (c : FConfig) (oracle : Nat → X86FlagChoices.Choice)
    (st : OState) : MachineResult (AccessReport OState) :=
  if st.native.m.memory.fetchBytes st.native.m.state.core.rip.toNat 2 = some [0x0f, 0x05] then
    liftO (st.counter + 1) (step sp c (completeF st.native (oracle st.counter)))
  else liftO st.counter (step sp c st.native)

/-- The oracle interface shared by every configuration. -/
def baseO (sp : ExtSpans) (oracle : Nat → X86FlagChoices.Choice) : UserIsa where
  State := OState
  step _ := oracleStep sp Silmaril.X86.Features.Config.bot oracle
  svcPending st := (base sp).svcPending st.native
  syscallArgs st := (base sp).syscallArgs st.native
  readByte segs st := (base sp).readByte segs st.native
  writableByte segs st := (base sp).writableByte segs st.native
  applyEffect st eff := ⟨(base sp).applyEffect st.native eff, st.counter⟩
  advancePastSvc st := ⟨(base sp).advancePastSvc st.native, st.counter⟩
  init segs pc sp' stack := ⟨(base sp).init segs pc sp' stack, 0⟩
  reportsAccesses := true
  entryFetchable := (base sp).entryFetchable
  addressSpace := (base sp).addressSpace

end X86Features

open X86Features in
/-- Configuration `c` with an explicit oracle for undefined syscall flags. A
claim about every completion quantifies over `oracle`. -/
def x86FeaturesWithFlagOracle (sp : X86Features.ExtSpans) (c : FConfig)
    (oracle : Nat → X86FlagChoices.Choice) : UserIsa :=
  (baseO sp oracle).withStep fun _ => oracleStep sp c oracle

namespace X86Features

/-! ## The lattice -/

/-- The step at `s` is one no larger configuration changes: a `syscall`, a
`REP STOSQ`, or a settled step of the feature machine. -/
def Settles (c : FConfig) (s : X86FState) : Prop :=
  s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05] ∨
    s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes ∨
    (c.step 0 s.m).Settled

/-- The access report of a settled step is the same in every larger configuration. -/
theorem spansAt_le {c d : FConfig} (h : c ≤ d) (sp : ExtSpans) {m : Silmaril.X86.Features.MState}
    (hs : (c.step 0 m).Settled) : spansAt sp d.exts m = spansAt sp c.exts m := by
  have hdec := Silmaril.X86.Features.decodes_of_step hs.2.2 hs.2.1
  unfold spansAt
  cases hf : Silmaril.X86.Ext.fetch m.memory m.state.core.rip.toNat with
  | decoded i n => rfl
  | truncated | undecodable =>
    simp only
    have hsome : (extDecode c.exts (fetchWindow m.memory maxInstrLength
        m.state.core.rip.toNat)).isSome := by
      rcases hdec with ⟨i, n, hi⟩ | hx
      · rw [hf] at hi; cases hi
      · exact hx
    obtain ⟨⟨e, x, n⟩, hx⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨he, hdx⟩ := Silmaril.X86.Features.extDecode_sound hx
    obtain ⟨e', he', ι, hdι, -, -⟩ := h.2 e he
    rw [hx, Silmaril.X86.Features.extDecode_of_mem d.disjoint he' (hdι _ x n hdx)]

/-- **One step**: a settling step is the same in every larger configuration. -/
theorem step_le_of_settles {c d : FConfig} (h : c ≤ d) (sp : ExtSpans) {s : X86FState}
    (hs : Settles c s) : step sp d s = step sp c s := by
  unfold step
  by_cases hsys : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05]
  · simp only [hsys, ite_true]
  · simp only [hsys, ite_false]
    by_cases hrep : s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes
    · simp only [hrep, ite_true]
    · simp only [hrep, ite_false]
      have hset : (c.step 0 s.m).Settled := (hs.resolve_left hsys).resolve_left hrep
      rw [Silmaril.X86.Features.Config.step_le h hset, spansAt_le h sp hset]

/-- A completed (`ok`) step settles. -/
theorem settles_of_ok {c : FConfig} {sp : ExtSpans} {s : X86FState}
    {r : AccessReport X86FState} (hok : step sp c s = .ok r) : Settles c s := by
  unfold step at hok
  by_cases hsys : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05]
  · exact .inl hsys
  · by_cases hrep : s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes
    · exact .inr (.inl hrep)
    · right; right
      simp only [hsys, hrep, ite_false] at hok
      cases ho : c.step 0 s.m <;> rw [ho] at hok <;>
        first
        | exact Silmaril.X86.Features.Outcome.settled_retired _
        | exact Silmaril.X86.Features.Outcome.settled_returned _
        | cases hok

/-- A completed step is the same in every larger configuration. -/
theorem step_le_of_ok {c d : FConfig} (h : c ≤ d) {sp : ExtSpans} {s : X86FState}
    {r : AccessReport X86FState} (hok : step sp c s = .ok r) : step sp d s = step sp c s :=
  step_le_of_settles h sp (settles_of_ok hok)

open Silmaril.Process.LPS.StepTransfer

/-- Every instruction-executing configuration reachable from `c₀` settles. -/
def NeverUnsettled (c : FConfig) (sp : ExtSpans) (segs : List Segment) (spec : Sys SyscallEffect)
    (refused : RefusalFilter) (c₀ : LPS.Config (x86FeaturesWith sp c)) : Prop :=
  ∀ tr cfg, Star segs spec refused c₀ tr cfg → cfg.model.halted = none →
    cfg.ms.pending = none → Settles c cfg.ms

/-- Agreement of `c` and `d ≥ c` from a start that never reaches an unsettled
instruction under `c`. -/
theorem agreesFrom_of_neverUnsettled {c d : FConfig} (h : c ≤ d) {sp : ExtSpans}
    {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
    {c₀ : LPS.Config (x86FeaturesWith sp c)} (hn : NeverUnsettled c sp segs spec refused c₀) :
    AgreesFrom (isa := base sp) (fun _ => step sp c) (fun _ => step sp d) segs spec refused c₀ :=
  fun tr cfg s h1 h2 => step_le_of_settles h sp (hn tr cfg s h1 h2)

/-- **Lattice transfer**: for `c ≤ d`, a launch that never reaches a missing
feature, a feature alias, undecodable bytes or a truncated fetch under `c` has
the same behaviour (traces, errors, all-traces-error, unmodelled) and the same
must-exit judgments under `d`. -/
theorem transfer_of_settles {c d : FConfig} (h : c ≤ d) {sp : ExtSpans} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {img : Image} {lim : Int} {en : ExecEntry} {inp : ProcInput}
    (hn : NeverUnsettled c sp img.segments spec refused
      (initConfig (x86FeaturesWith sp c) img en lim inp)) :
    ((∀ tr, (runWith (x86FeaturesWith sp d) spec refused img lim en inp).traces tr ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).traces tr) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).errors ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).errors) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).allErrors ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).allErrors) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).unmodeled ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).unmodeled)) ∧
    ∀ S : List Word,
      MustExitInAt img.segments spec refused S (initConfig (x86FeaturesWith sp d) img en lim inp) ↔
        MustExitInAt img.segments spec refused S (initConfig (x86FeaturesWith sp c) img en lim inp) :=
  ⟨runWith_iff (agreesFrom_of_neverUnsettled h hn),
    fun S => mustExitInAt_iff (agreesFrom_of_neverUnsettled h hn) S⟩

/-- The x86 SysV launch (`X86Launch.runWith`), under the same hypothesis. -/
theorem launch_transfer_of_settles {c d : FConfig} (h : c ≤ d) {sp : ExtSpans}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {snapshot : X86Launch.Snapshot}
    {lim : Int} {en : ExecEntry} {inp : ProcInput}
    (hn : NeverUnsettled c sp snapshot.image.segments spec refused
      (X86Launch.init (x86FeaturesWith sp c) snapshot en lim inp)) :
    (∀ tr, (X86Launch.runWith (x86FeaturesWith sp d) spec refused snapshot lim en inp).traces tr ↔
        (X86Launch.runWith (x86FeaturesWith sp c) spec refused snapshot lim en inp).traces tr) ∧
      ((X86Launch.runWith (x86FeaturesWith sp d) spec refused snapshot lim en inp).errors ↔
        (X86Launch.runWith (x86FeaturesWith sp c) spec refused snapshot lim en inp).errors) ∧
      ((X86Launch.runWith (x86FeaturesWith sp d) spec refused snapshot lim en inp).allErrors ↔
        (X86Launch.runWith (x86FeaturesWith sp c) spec refused snapshot lim en inp).allErrors) ∧
      ((X86Launch.runWith (x86FeaturesWith sp d) spec refused snapshot lim en inp).unmodeled ↔
        (X86Launch.runWith (x86FeaturesWith sp c) spec refused snapshot lim en inp).unmodeled) :=
  ⟨obsTrace_iff (agreesFrom_of_neverUnsettled h hn), reachesError_iff (agreesFrom_of_neverUnsettled h hn),
    allTracesError_iff (agreesFrom_of_neverUnsettled h hn),
    reachesUnmodeled_iff (agreesFrom_of_neverUnsettled h hn)⟩

/-- The error-free form (`Features.lps_transfer`): every LPS correctness
statement contains error freedom, so it transfers from `c` to every `d ≥ c`. -/
theorem transfer_of_errorFree {c d : FConfig} (h : c ≤ d) {sp : ExtSpans}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {img : Image} {lim : Int}
    {en : ExecEntry} {inp : ProcInput}
    (hne : ¬ (runWith (x86FeaturesWith sp c) spec refused img lim en inp).errors) :
    ((∀ tr, (runWith (x86FeaturesWith sp d) spec refused img lim en inp).traces tr ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).traces tr) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).errors ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).errors) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).allErrors ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).allErrors) ∧
      ((runWith (x86FeaturesWith sp d) spec refused img lim en inp).unmodeled ↔
        (runWith (x86FeaturesWith sp c) spec refused img lim en inp).unmodeled)) ∧
    ∀ S : List Word,
      MustExitInAt img.segments spec refused S (initConfig (x86FeaturesWith sp d) img en lim inp) ↔
        MustExitInAt img.segments spec refused S (initConfig (x86FeaturesWith sp c) img en lim inp) := by
  have hA : AgreesFrom (isa := base sp) (fun _ => step sp c) (fun _ => step sp d) img.segments
      spec refused (initConfig (x86FeaturesWith sp c) img en lim inp) :=
    agreesFrom_of_errorFree hne fun _ _ hr => step_le_of_ok h hr
  exact ⟨runWith_iff hA, fun S => mustExitInAt_iff hA S⟩

/-! ### The flag-oracle instance -/

/-- The oracle step settles at `st` when the step at its state does. -/
theorem oracleStep_le_of_settles {c d : FConfig} (h : c ≤ d) (sp : ExtSpans)
    (oracle : Nat → X86FlagChoices.Choice) {st : OState} (hs : Settles c st.native) :
    oracleStep sp d oracle st = oracleStep sp c oracle st := by
  unfold oracleStep
  by_cases hsys : st.native.m.memory.fetchBytes st.native.m.state.core.rip.toNat 2 =
      some [0x0f, 0x05]
  · simp only [hsys, ite_true]
    rw [step_le_of_settles h sp (s := completeF st.native (oracle st.counter)) (.inl hsys)]
  · simp only [hsys, ite_false]
    rw [step_le_of_settles h sp hs]

/-- Every instruction-executing configuration reachable from `c₀` settles. -/
def NeverUnsettledO (c : FConfig) (sp : ExtSpans) (oracle : Nat → X86FlagChoices.Choice)
    (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (c₀ : LPS.Config (x86FeaturesWithFlagOracle sp c oracle)) : Prop :=
  ∀ tr cfg, Star segs spec refused c₀ tr cfg → cfg.model.halted = none →
    cfg.ms.native.pending = none → Settles c cfg.ms.native

/-- **Lattice transfer with the oracle**, for every oracle. -/
theorem launch_transfer_of_settlesO {c d : FConfig} (h : c ≤ d) {sp : ExtSpans}
    {oracle : Nat → X86FlagChoices.Choice}
    {spec : Sys SyscallEffect} {refused : RefusalFilter} {snapshot : X86Launch.Snapshot}
    {lim : Int} {en : ExecEntry} {inp : ProcInput}
    (hn : NeverUnsettledO c sp oracle snapshot.image.segments spec refused
      (X86Launch.init (x86FeaturesWithFlagOracle sp c oracle) snapshot en lim inp)) :
    (∀ tr, (X86Launch.runWith (x86FeaturesWithFlagOracle sp d oracle) spec refused snapshot lim
        en inp).traces tr ↔
        (X86Launch.runWith (x86FeaturesWithFlagOracle sp c oracle) spec refused snapshot lim
          en inp).traces tr) ∧
      ((X86Launch.runWith (x86FeaturesWithFlagOracle sp d oracle) spec refused snapshot lim
          en inp).errors ↔
        (X86Launch.runWith (x86FeaturesWithFlagOracle sp c oracle) spec refused snapshot lim
          en inp).errors) ∧
      ((X86Launch.runWith (x86FeaturesWithFlagOracle sp d oracle) spec refused snapshot lim
          en inp).allErrors ↔
        (X86Launch.runWith (x86FeaturesWithFlagOracle sp c oracle) spec refused snapshot lim
          en inp).allErrors) ∧
      ((X86Launch.runWith (x86FeaturesWithFlagOracle sp d oracle) spec refused snapshot lim
          en inp).unmodeled ↔
        (X86Launch.runWith (x86FeaturesWithFlagOracle sp c oracle) spec refused snapshot lim
          en inp).unmodeled) := by
  have hA : AgreesFrom (isa := baseO sp oracle) (fun _ => oracleStep sp c oracle)
      (fun _ => oracleStep sp d oracle) snapshot.image.segments spec refused
      (X86Launch.init (x86FeaturesWithFlagOracle sp c oracle) snapshot en lim inp) :=
    fun tr cfg s h1 h2 => oracleStep_le_of_settles h sp oracle (hn tr cfg s h1 h2)
  exact ⟨obsTrace_iff hA, reachesError_iff hA, allTracesError_iff hA, reachesUnmodeled_iff hA⟩

/-! ## Agreement with the native instances on their fragment -/

/-- `REP STOSQ` is not a canonical integer instruction. -/
theorem ext_fetch_not_rep {memory : Silmaril.Process.Memory} {address : Nat}
    {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hf : Silmaril.X86.Ext.fetch memory address = .decoded i n)
    (hrep : memory.fetchBytes address 3 = some X86RepStosq.bytes) : False := by
  obtain ⟨rest, image⟩ := Silmaril.X86.fetchBytes_prefix_fetchWindow
    (limit := maxInstrLength) hrep (by decide)
  unfold Silmaril.X86.Ext.fetch at hf
  rw [← image] at hf
  split at hf
  · rename_i hd
    have hw := Silmaril.X86.Ext.Wire.decode_of_ext hd
    rw [X86RepStosq.wire_decode_rep_append] at hw
    cases hw
  · split at hf <;> (try split at hf) <;> cases hf

/-- **Agreement with `x86ExtNative`**: at a `syscall`, or at bytes `X86.Ext`
decodes whose feature check passes (every instruction but POPCNT, LZCNT and
TZCNT, and those too when `baseFeatures ⊆ c.features`), the step is
`x86NativeStep` on the integer part of the state, for every access table. -/
theorem step_native (c : FConfig) (sp : ExtSpans) (s : X86FState)
    (h : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05] ∨
      ∃ i n, Silmaril.X86.Ext.fetch s.m.memory s.m.state.core.rip.toNat = .decoded i n ∧
        baseCheck c.features i = none) :
    step sp c s = liftResult s.m.state (x86NativeStep (proj s)) := by
  unfold step
  by_cases hsys : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05]
  · simp only [hsys, ite_true]
    rw [x86NativeStep, ite_eq_left (show (proj s).m.memory.fetchBytes (proj s).m.core.rip.toNat 2 =
      some [0x0f, 0x05] from hsys)]
    simp only [proj]
    cases rflagsImage s.m.state.core.flags <;> rfl
  · obtain ⟨i, n, hf, hb⟩ := h.resolve_left hsys
    have hrep : ¬ s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes :=
      fun hr => ext_fetch_not_rep hf hr
    simp only [hsys, hrep, ite_false]
    have hstep : c.step 0 s.m = Silmaril.X86.Features.Outcome.ofBase s.m.state
        (Silmaril.X86.Ext.step 0 s.m.toBase) := by
      unfold Silmaril.X86.Features.Config.step
      rw [Silmaril.X86.Features.step_of_base hf, hb]
    have hspans : spansAt sp c.exts s.m =
        some ((s.m.state.core.rip, n) :: X86Accesses.canonical s.m.state.core n i) := by
      unfold spansAt; rw [hf]
    rw [hstep, hspans]
    rw [x86NativeStep, ite_eq_right (show ¬ (proj s).m.memory.fetchBytes (proj s).m.core.rip.toNat 2 =
      some [0x0f, 0x05] from hsys)]
    have hf' : Silmaril.X86.Ext.fetch (proj s).m.memory (proj s).m.core.rip.toNat =
        .decoded i n := hf
    have hn := Silmaril.X86.Ext.fetch_length hf
    simp only [hf']
    simp only [proj]
    have hbase : s.m.toBase = ⟨s.m.state.core, s.m.memory⟩ := rfl
    simp only [Silmaril.X86.Ext.step, hbase, hf]
    subst hn
    cases Silmaril.X86.Ext.exec i s.m.state.core s.m.memory with
    | ok core memory =>
      simp only
      split <;> rfl
    | _ => rfl

/-- Bytes that `Ext.Wire` fetches but `X86.Ext` does not are a `Wire` form. -/
private theorem wire_form_of_fetch {memory : Silmaril.Process.Memory} {address : Nat}
    {d : Silmaril.X86.Ext.Wire.Decoded}
    (hw : Silmaril.X86.Ext.Wire.fetch memory address = .decoded d)
    (hne : ∀ i n, Silmaril.X86.Ext.fetch memory address ≠ .decoded i n) :
    Silmaril.X86.Ext.decode (fetchWindow memory maxInstrLength address) = none ∧
      Silmaril.X86.Ext.Wire.decode (fetchWindow memory maxInstrLength address) = some d ∧
      memory.Permitted .execute address d.length := by
  unfold Silmaril.X86.Ext.Wire.fetch at hw
  dsimp only at hw
  split at hw
  · rename_i d' hd
    split at hw
    · rename_i hp
      cases hw
      refine ⟨?_, hd, hp⟩
      cases he : Silmaril.X86.Ext.decode (fetchWindow memory maxInstrLength address) with
      | none => rfl
      | some r =>
        obtain ⟨i, k⟩ := r
        exfalso
        have hcan := Silmaril.X86.Ext.Wire.decode_of_ext he
        rw [hd] at hcan
        cases hcan
        have hk := (Silmaril.X86.Ext.decode_length he).1
        apply hne i k
        unfold Silmaril.X86.Ext.fetch
        rw [he]
        have hp' : memory.Permitted .execute address k := by
          rw [hk]; exact hp
        simp only [hp', ite_true]
    · cases hw
  · split at hw <;> (try split at hw) <;> cases hw

/-- **Agreement with `x86WireDf0RepStosq`**: on its fragment (a `syscall`, a
`REP STOSQ`, or bytes `Ext.Wire` fetches), the step of `wireConfig F p` with a
table that describes `Wire`'s forms is `X86RepStosq.step p` on the integer part
of the state. -/
theorem step_wireRep {F : FeatureSet} (hF : baseFeatures ⊆ F) (p : Silmaril.X86.Ext.Wire.Platform)
    (sp : ExtSpans) (hsp : ∀ w n v r, wireSpans w n v = some r → sp w n v = some r)
    (s : X86FState)
    (h : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05] ∨
      s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes ∨
      ∃ d, Silmaril.X86.Ext.Wire.fetch s.m.memory s.m.state.core.rip.toNat = .decoded d) :
    step sp (Silmaril.X86.Features.wireConfig F p) s =
      liftResult s.m.state (X86RepStosq.step p (proj s)) := by
  by_cases hsys : s.m.memory.fetchBytes s.m.state.core.rip.toNat 2 = some [0x0f, 0x05]
  · rw [step_native _ sp s (.inl hsys)]
    rw [X86FlagOracle.rep_syscall_agreement p (proj s) hsys]
  by_cases hrep : s.m.memory.fetchBytes s.m.state.core.rip.toNat 3 = some X86RepStosq.bytes
  · unfold step
    simp only [hsys, hrep, ite_false, ite_true]
    rw [X86RepStosq.step_rep p (proj s) hrep]
  obtain ⟨d, hd⟩ := (h.resolve_left hsys).resolve_left hrep
  rw [X86RepStosq.step_eq_wire p (proj s) hrep]
  by_cases hint : ∃ i n, Silmaril.X86.Ext.fetch s.m.memory s.m.state.core.rip.toNat = .decoded i n
  · obtain ⟨i, n, hf⟩ := hint
    rw [X86Wire.common_result p (proj s) (X86Wire.canonical_common (proj s) hf)]
    exact step_native _ sp s (.inr ⟨i, n, hf,
      Silmaril.X86.Features.baseCheck_of_baseFeatures hF i⟩)
  · have hne : ∀ i n, Silmaril.X86.Ext.fetch s.m.memory s.m.state.core.rip.toNat ≠ .decoded i n :=
      fun i n e => hint ⟨i, n, e⟩
    obtain ⟨he, hw, hp⟩ := wire_form_of_fetch hd hne
    have hwd : Silmaril.X86.Features.wireDecode
        (fetchWindow s.m.memory maxInstrLength s.m.state.core.rip.toNat) =
          some (⟨d, Silmaril.X86.Features.wireForm_of he hw⟩, d.length) :=
      Silmaril.X86.Features.wireDecode_eq_some_iff.mpr ⟨he, hw, rfl⟩
    have hext : extDecode (Silmaril.X86.Features.wireConfig F p).exts
        (fetchWindow s.m.memory maxInstrLength s.m.state.core.rip.toNat) =
          some ⟨Silmaril.X86.Features.wireExt p,
            ⟨d, Silmaril.X86.Features.wireForm_of he hw⟩, d.length⟩ := by
      simp only [Silmaril.X86.Features.wireConfig, extDecode,
        Silmaril.X86.Features.wireExt_decode, hwd]
    have hstep : (Silmaril.X86.Features.wireConfig F p).step 0 s.m =
        Silmaril.X86.Features.extStep F (Silmaril.X86.Features.wireExt p)
          ⟨d, Silmaril.X86.Features.wireForm_of he hw⟩ d.length s.m :=
      Silmaril.X86.Features.step_of_ext he hext hp
    have hws : wireSpans (fetchWindow s.m.memory maxInstrLength s.m.state.core.rip.toNat)
        d.length s.m.state = some (X86Accesses.wire s.m.state.core d) := by
      simp only [wireSpans, hw, ite_true]
    have hspans : spansAt sp (Silmaril.X86.Features.wireConfig F p).exts s.m =
        some ((s.m.state.core.rip, d.length) :: X86Accesses.wire s.m.state.core d) := by
      unfold spansAt
      cases hf : Silmaril.X86.Ext.fetch s.m.memory s.m.state.core.rip.toNat with
      | decoded i n => exact absurd hf (hne i n)
      | truncated | undecodable =>
        simp only
        rw [hext]
        simp only [hsp _ _ _ _ hws, Option.map_some]
    unfold step
    simp only [hsys, hrep, ite_false]
    rw [hstep, hspans]
    rw [x86WireStep, ite_eq_right (show ¬ (proj s).m.memory.fetchBytes (proj s).m.core.rip.toNat 2 =
      some [0x0f, 0x05] from hsys)]
    have hd' : Silmaril.X86.Ext.Wire.fetch (proj s).m.memory (proj s).m.core.rip.toNat =
        .decoded d := hd
    simp only [hd']
    unfold Silmaril.X86.Features.extStep
    rw [show (Silmaril.X86.Features.wireExt p).requires
        ⟨d, Silmaril.X86.Features.wireForm_of he hw⟩ =
        Silmaril.X86.Features.wireRequires ⟨d, Silmaril.X86.Features.wireForm_of he hw⟩ from rfl]
    have hm := Silmaril.X86.Features.wireRequires_missing hF
      ⟨d, Silmaril.X86.Features.wireForm_of he hw⟩
    split
    · rename_i f hf
      exact absurd (hf.symm.trans hm) (by simp)
    · simp only [Silmaril.X86.Features.wireExt, proj]
      cases Silmaril.X86.Ext.Wire.exec p d s.m.state.core s.m.memory <;> rfl

/-- The table `defaultSpans` describes `Wire`'s forms. -/
theorem defaultSpans_wire (w : List Byte) (n : Nat) (v : FState) (r : List (Word × Nat))
    (h : wireSpans w n v = some r) : defaultSpans w n v = some r := by
  simp only [defaultSpans, ExtSpans.orElse, h]

/-- Attach the counter after the vector state. -/
def liftResultO (v : FState) :
    MachineResult (AccessReport X86FlagChoices.State) → MachineResult (AccessReport OState)
  | .ok r => .ok ⟨⟨embed v r.value.native, r.value.counter⟩, r.accessed⟩
  | .fault => .fault
  | .unmodeled => .unmodeled

theorem liftO_liftResult (v : FState) (counter : Nat)
    (r : MachineResult (AccessReport X86State)) :
    liftO counter (liftResult v r) = liftResultO v (X86FlagChoices.lift counter r) := by
  cases r <;> rfl

/-- The integer flag-oracle state of an extended one. -/
def projO (st : OState) : X86FlagChoices.State := ⟨proj st.native, st.counter⟩

/-- **Agreement with `x86WireDf0RepStosqWithFlagOracle`**, for every oracle. -/
theorem oracleStep_wireRep {F : FeatureSet} (hF : baseFeatures ⊆ F)
    (p : Silmaril.X86.Ext.Wire.Platform) (sp : ExtSpans)
    (hsp : ∀ w n v r, wireSpans w n v = some r → sp w n v = some r)
    (oracle : Nat → X86FlagChoices.Choice) (st : OState)
    (h : st.native.m.memory.fetchBytes st.native.m.state.core.rip.toNat 2 = some [0x0f, 0x05] ∨
      st.native.m.memory.fetchBytes st.native.m.state.core.rip.toNat 3 = some X86RepStosq.bytes ∨
      ∃ d, Silmaril.X86.Ext.Wire.fetch st.native.m.memory st.native.m.state.core.rip.toNat =
        .decoded d) :
    oracleStep sp (Silmaril.X86.Features.wireConfig F p) oracle st =
      liftResultO st.native.m.state
        (X86FlagOracle.stepUsing (X86RepStosq.step p) oracle (projO st)) := by
  unfold oracleStep X86FlagOracle.stepUsing
  by_cases hsys : st.native.m.memory.fetchBytes st.native.m.state.core.rip.toNat 2 =
      some [0x0f, 0x05]
  · have hsys' : (projO st).native.m.memory.fetchBytes (projO st).native.m.core.rip.toNat 2 =
        some [0x0f, 0x05] := hsys
    rw [ite_eq_left hsys, ite_eq_left hsys']
    rw [step_wireRep hF p sp hsp (completeF st.native (oracle st.counter)) (.inl hsys),
      liftO_liftResult]
    rfl
  · have hsys' : ¬ (projO st).native.m.memory.fetchBytes (projO st).native.m.core.rip.toNat 2 =
        some [0x0f, 0x05] := hsys
    rw [ite_eq_right hsys, ite_eq_right hsys', step_wireRep hF p sp hsp st.native h, liftO_liftResult]
    rfl

end X86Features

end Silmaril.Process.LPS.Machines
