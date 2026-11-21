module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Spin.Thms
public import Silmaril.X86.Litmus.Complete.Thms
import Silmaril.Proofs.X86.Concurrency.Bridge.Step
import Silmaril.Proofs.X86.Concurrency.Bridge.Pieces
import Silmaril.Proofs.X86.Concurrency.Bridge.Complete
import Silmaril.Proofs.X86.Concurrency.Bridge.Counter
import Silmaril.Proofs.X86.Concurrency.Bridge.Defined
import Silmaril.Proofs.X86.Concurrency.Bridge.Cex
import Silmaril.Proofs.X86.Concurrency.Bridge.CondInit
import Silmaril.Proofs.X86.Concurrency.Bridge.Link
import Silmaril.Proofs.X86.Concurrency.Bridge.TvRun
import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Main
import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Sb
public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs

/-!
# Bridges from the CIR front ends to the real machine: what is proved

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Bridge/{Step,Pieces}.lean`):

* **Gap 2, one step** (`xstep_of_step`): on a backed memory with the thread's regions and code,
  a real `Atomic9.step` from a core where `stepSym` is defined is a branch of `stepSym`
  (over the domain of the values it reads), whose reads the memory answers and whose writes are
  the step's. With `stepSym_dom` (being defined does not depend on the domain) and
  `stepSym_reads` (the reads of a defined step are read-permitted and at most 8 bytes), this is
  `stepSym_complete` without the domain hypothesis. **Runs**: `xrun_of_a9run`,
  `frun_of_a9frun`: a real run (`A9Run`, `A9FRun`, with interference) is an `XRun`/`FRun` when
  `stepSym` is defined at every core it reaches.
* **Gap 2, defined** (proofs in `Bridge/Defined.lean`): `tvCfgDefined_holds :
  Task.tvCfgDefined` and `tvFxDefined_holds : Task.tvFxDefined`: on code `tvCfg`/`tvFx`
  accepts, `stepSym` is defined at every reachable unfinished core where `Atomic9.step`
  succeeds. Reachable cores sit at certificate entries (`tvCfg_reach`, `tvFx_reach`), so the
  instruction there is one the checker's table accepts; the converse of the listing law
  (`Atomic9.exec_of_step_base`, `exec_of_step_new`) makes its executor `.ok` on the real memory;
  then an inert form also runs on `Thread.frame` (locality) and a memory form passes
  `memStep`'s `readOk`/`writeOk` guards (a successful `loadN`/`storeN` was permitted).
* **Gap 2, the front ends** (PROVED, unconditional): `tvCfg_real` and `tvFx_real`:
  every real run of validated code is a CIR run, step by step, with the real memories answering
  the CIR reads and taking its writes.
* **Gap 2, the checker** (proofs in `Bridge/TvRun.lean`): `tvRun_real`, every
  real run (`A9Run`, with interference) of a thread `tvRun` accepts, from its initial core to the
  end of its code, is an `XRun` whose actions the real memories answer and take, and a run of
  the certificate's CIR thread over **any** domain holding the values read (`Cir.Tv.actVals`),
  with the same actions up to `normActs` and the same final registers outside the clobber set.
  There is no bound on the values: an 8-byte read may return any 64-bit value (the checker
  `chk1` was changed so that an 8-byte read leaves the fitting set; `Cir.Tv.q_load_unfit`,
  `Cir.Tv.qCas_rejected`). `tvRunDefined_holds`: the `tvRun` counterpart of
  `Task.tvCfgDefined`. These are pieces (2) and (3) of `Task.tsoRunCir`'s plan.
* **Gap 3, the sound direction** (`pexplore_replays`): every trace of `pexplore` (the
  pieces of a spin-cut function, one after the other) replays as one trace of the whole function
  (`whole`) on `Atomic9.step`, with interference. So the x86 traces `STest.refines` quantifies
  over are real runs of the bytes; `pexplore`'s `rip` reset is the identity.
* **Gap 3, the complete direction** (PROVED; proof in
  `Silmaril/Proofs/X86/Concurrency/Bridge/Complete.lean`): `piecesComplete_holds`, every
  domain-bounded run of the whole function is a trace of the pieces for the spin bound `n` =
  the run's length (`Task.piecesComplete`, restated with `run ≠ [] ∨ length < 2 ^ 64`: the
  original is false for the empty run of a `2 ^ 64`-byte code, whose end wraps to its start:
  `piecesCompleteUnrestricted_false`).
  It uses `Atomic9.decode_append` (the listing decoder is prefix-stable). Hence `whole_refines`:
  every such run is a run of the CIR thread `c.body n`, unconditionally.
* **Gap 1** (PROVED; proofs in `Bridge/TsoRun/{Mem,Run,Cells,Main}.lean`):
  `tsoRunCir_holds : Task.tsoRunCir`. Every final state of the byte-granular TSO pool running a
  validated test's bytes (`TsoFinal`) has the witness value of a TSO behaviour of the test's CIR
  program, for a test whose accesses are cell accesses (`cellsB`, checked on the threads'
  skeletons) and whose condition observes only initialised bytes (`CondInit`). Hence
  `forbidden_tso_bytes` (unconditional): a `forbidden` CIR verdict under TSO holds for the bytes
  running concurrently. **Restated twice**: first by adding `CondInit` (without it the statement
  is false, `not_tsoRunCirAsStated`), and then by replacing the per-thread `CellsOk` by
  `cellsB`; with `CellsOk` the statement is false, `not_tsoRunCirCells`: a thread may read a
  byte no location initialises, the counterexample). `condInit_of`, `corpus_condInit`,
  `corpus_cellsB`: both hypotheses are Boolean checks that all 60 corpus tests pass.
  `sb_pool_allowed` (proof in `Bridge/TsoRun/Sb.lean`): the pool over SB's bytes
  reaches the store-buffering outcome, so the machine over the bytes is weak and `TsoFinal` of
  a two-thread corpus test is not empty.

* **Gap 4, calls** (proofs in `Bridge/Link.lean`): `callRet_holds : Task.callRet`
  (proved as stated): on the real machine a listed `call rel32` is `pushWord` and a jump
  (`call_law`), a listed `ret` whose slot holds `w` is `popWord` (`ret_law`), both by the converse
  of the listing law, and the body between them is `tvCfg_steps` on the callee's slice.
  **The caller checker** `ltv` (a caller cut at its call sites, each segment and each callee body
  validated by `tvCfg`) is sound against real runs: `ltv_real`, every real run of the caller
  (`LRun`, with interference) is a CIR run of the linked program `LCert.body` (segments, callee
  bodies and the `rsp` glue `push8`/`pop8`), with the real memories answering each machine step's
  actions, the `call` writing exactly its 8-byte slot and the `ret` writing nothing. The run
  assumes the return address is still in its slot when the callee returns (`LRun`'s `hslot`);
  that the slot is thread-owned is not derived. `Bridge/Crit` applies it to compiled bytes.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Bridge

open Silmaril.X86 (State)
open Silmaril.Process (Memory)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep Answers applyWrites stepSym DomRun Trace Act Replay)
open Silmaril.X86.MemoryModel.Litmus (XAct Test Final Verdict)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (XThread TvTest SThread SCert stvRun pexplore normActs)
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (FCert tvFx FRun Returned clob)

/-! ## Gap 2 -/

/-- Whether `stepSym` is defined does not depend on the value domain. -/
theorem stepSym_dom {t : XThread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) (dom' : List Nat) :
    ∃ outs', stepSym t dom' s = some outs' :=
  Silmaril.Proofs.X86.Concurrency.Bridge.stepSym_dom h dom'

/-- The reads of a defined symbolic step are read-permitted by the regions and at most 8
bytes. -/
theorem stepSym_reads {t : XThread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {i : Atomic9.Instr} {n : Nat} (hf : t.fetch s = some (i, n)) :
    ∀ e ∈ MemEvent.atomic9Accesses i s n, e.kind.reads = true →
      e.size ≤ 8 ∧ Silmaril.X86.Litmus.readOk t.regions e.addr e.size = true :=
  Silmaril.Proofs.X86.Concurrency.Bridge.stepSym_reads h hf

/-- **A real step where the symbolic step is defined is a symbolic step.** -/
theorem xstep_of_step {t : XThread} {dom₀ : List Nat} {s : State}
    {outs₀ : List (List Act × State)} (hsym : stepSym t dom₀ s = some outs₀) {m : Memory}
    {s' : State} {m' : Memory} (hR : m.regions = t.regions) (hl : Loaded m t.base t.code)
    (hb : Backed m) (hs : Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩) :
    ∃ dom outs acts, stepSym t dom s = some outs ∧ (acts, s') ∈ outs ∧ Answers m acts ∧
      applyWrites m acts = some m' :=
  Silmaril.Proofs.X86.Concurrency.Bridge.xstep_of_step hsym hR hl hb hs

/-- **A real run is an `XRun`** when the symbolic step is defined at every unfinished core an
`XRun` reaches (where the real step succeeds). -/
theorem xrun_of_a9run {t : XThread} {s : State} {xs : List SeqStep} {s' : State}
    (hr : A9Run t s xs s')
    (hD : ∀ acc s₁, XRun t s acc s₁ → s₁.rip ≠ t.endRip → ∀ (m : Memory) (s₂ : State)
      (m₂ : Memory), m.regions = t.regions → Loaded m t.base t.code →
      Atomic9.step ⟨s₁, m⟩ = some ⟨s₂, m₂⟩ → SymDefined t s₁) :
    ∃ acc, XRun t s acc s' ∧ List.Forall₂ ActsOk acc xs :=
  Silmaril.Proofs.X86.Concurrency.Bridge.xrun_of_a9run hr hD

/-- **A real futex-thread run is an `FRun`** when the symbolic step is defined at every core an
`FRun` reaches that has not returned and is not at a `syscall`. -/
theorem frun_of_a9frun {t : XThread} {s : State} {xs : List FObs} {s' : State}
    (hr : A9FRun t s xs s')
    (hD : ∀ acc s₁, FRun t s acc s₁ → ¬ Returned t s₁ →
      Silmaril.X86.Concurrency.Cir.TvCfg.Fx.isSysAt t (s₁.rip - t.base).toNat = false →
      ∀ (m : Memory) (s₂ : State) (m₂ : Memory), m.regions = t.regions →
      Loaded m t.base t.code → Atomic9.step ⟨s₁, m⟩ = some ⟨s₂, m₂⟩ → SymDefined t s₁) :
    ∃ acc, FRun t s acc s' ∧ List.Forall₂ FObs.Ok acc xs :=
  Silmaril.Proofs.X86.Concurrency.Bridge.frun_of_a9frun hr hD

/-- **`Task.tvCfgDefined` holds**: on code `tvCfg` accepts, the symbolic step is defined
at every reachable unfinished core where the real step succeeds. -/
theorem tvCfgDefined_holds : Task.tvCfgDefined :=
  Silmaril.Proofs.X86.Concurrency.Bridge.tvCfgDefined_holds

/-- **`Task.tvFxDefined` holds**: the same for `tvFx`, at cores that have not returned and
are not at a `syscall`. -/
theorem tvFxDefined_holds : Task.tvFxDefined :=
  Silmaril.Proofs.X86.Concurrency.Bridge.tvFxDefined_holds

/-- **The checker against the real machine**: every real run of
validated code from its start, with interference, of `k` steps is a CIR run of `c.body L` for
every `L ≥ k`, step by step (each x86 step's actions are those of at most one CIR label), with
the real memories answering the actions' reads and taking their writes, the same final registers,
and `skip` at the end of the code. -/
theorem tvCfg_real {t : XThread} {c : GCert} (hc : tvCfg t c = true)
    {s₀ s : State} (h0 : s₀.rip = t.base) {xs : List SeqStep} (hr : A9Run t s₀ xs s) {L : Nat}
    (hL : xs.length ≤ L) :
    ∃ acc : List (List XAct), List.Forall₂ ActsOk acc xs ∧
      ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s₀) (los.filterMap id) σ rs ∧
        List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
        regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  obtain ⟨acc, hx, hok⟩ := xrun_of_a9run hr fun acc s₁ hx hne m s₂ m₂ hR hl hs =>
    tvCfgDefined_holds t c hc s₀ s₁ acc h0 hx hne m s₂ m₂ hR hl hs
  have hlen : acc.length ≤ L := by rw [hok.length_eq]; exact hL
  exact ⟨acc, hok, tvCfg_steps hc h0 hx hlen⟩

/-- **The checker against the real machine**: every real run of
validated futex code (machine steps and futex calls by the convention) is a CIR run of
`c.body L`, step by step, with the real memories answering the machine steps' actions, the same
final registers outside `rax`, `rcx`, `r11`, and `skip` once the function has returned. -/
theorem tvFx_real {t : XThread} {c : FCert} (hc : tvFx t c = true)
    {s₀ s : State} (h0 : s₀.rip = t.base) {xs : List FObs} (hr : A9FRun t s₀ xs s) {L : Nat}
    (hL : xs.length ≤ L) :
    ∃ acc : List (List XAct), List.Forall₂ FObs.Ok acc xs ∧
      ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s₀) (los.filterMap id) σ rs ∧
        List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
        (∀ r, r ∉ clob → regsOf s r = rs r) ∧ (Returned t s → σ = .skip) := by
  obtain ⟨acc, hx, hok⟩ := frun_of_a9frun hr fun acc s₁ hx hne hsys m s₂ m₂ hR hl hs =>
    tvFxDefined_holds t c hc s₀ s₁ acc h0 hx hne hsys m s₂ m₂ hR hl hs
  have hlen : acc.length ≤ L := by rw [hok.length_eq]; exact hL
  exact ⟨acc, hok, Silmaril.X86.Concurrency.Cir.TvCfg.Fx.tvFx_steps hc h0 hx hlen⟩

/-! ## Gap 3 -/

/-- **The pieces replay as the whole function** (the sound direction): every trace of
`pexplore` from the thread's initial core, for every domain, fuel and spin bound, replays on
`Atomic9.step` as a trace of the whole function (`Replay`: at each step, on every memory
with the regions and the whole code that answers the step's reads, one machine step reaches the
trace's core and writes its bytes). -/
theorem pexplore_replays {th : SThread} {c : SCert} {K : List Reg} (h : stvRun th c = some K)
    {dom : List Nat} {fuel n : Nat} {trs : List Trace}
    (hx : pexplore th dom fuel n 0 c.pieces th.init = some trs) :
    ∀ tr ∈ trs, Replay (whole th) th.init tr.steps tr.final :=
  Silmaril.Proofs.X86.Concurrency.Bridge.pexplore_replays h hx

/-- **The symbolic step is defined on code `tvRun` accepts wherever the real step succeeds**
(the counterpart of `Task.tvCfgDefined` for the straight-line checker). -/
theorem tvRunDefined_holds {t : XThread} {c : Silmaril.X86.Concurrency.Cir.Tv.Cert}
    {K : List Reg} (h : Silmaril.X86.Concurrency.Cir.Tv.tvRun t c = some K) :
    ∀ (acc : List (List XAct)) (s : State), XRun t t.init acc s → s.rip ≠ t.endRip →
      ∀ (m : Memory) (s' : State) (m' : Memory), m.regions = t.regions →
        Loaded m t.base t.code → Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩ → SymDefined t s :=
  Silmaril.Proofs.X86.Concurrency.Bridge.tvRunDefined_holds h

/-- **The checker against the real machine**: every real run of a thread
`tvRun` accepts, from its initial core to the end of its code, is an `XRun` whose actions the
real memories answer and take, and a run of the certificate's CIR thread over any domain that
holds the values read (no `2 ^ 32` bound), with the same actions up to `normActs` and the same
final registers outside the clobber set. -/
theorem tvRun_real {t : XThread} {c : Silmaril.X86.Concurrency.Cir.Tv.Cert} {K : List Reg}
    (h : Silmaril.X86.Concurrency.Cir.Tv.tvRun t c = some K)
    {xs : List SeqStep} {s' : State} (hr : A9Run t t.init xs s') (he : s'.rip = t.endRip) :
    ∃ acc, XRun t t.init acc s' ∧ List.Forall₂ ActsOk acc xs ∧
      ∀ D : List Nat, (∀ v ∈ Silmaril.X86.Concurrency.Cir.Tv.actVals acc, v ∈ D) →
        ∃ p ∈ run D c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
          ∀ r, r ∉ K → s'.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Bridge.tvRun_real h hr he

/-- **`tvRun_real` is not vacuous, past `2 ^ 32`**: on a backed one-thread test
memory holding `2 ^ 32` at `0x10000`, the real run of `mov rax, qword [0x10000]` (accepted by
`tvRun`) ends with `rax = 2 ^ 32`, and `tvRun_real` makes it a CIR run with `rax = 2 ^ 32`. -/
theorem tvRun_real_qLoad : ∃ xs s', A9Run Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoad
    Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoad.init xs s' ∧
    s'.rip = Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoad.endRip ∧ (s'.read .rax).toNat = 2 ^ 32 ∧
    ∃ acc, XRun Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoad
        Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoad.init acc s' ∧ List.Forall₂ ActsOk acc xs ∧
      ∃ p ∈ run (Silmaril.X86.Concurrency.Cir.Tv.actVals acc)
          Silmaril.X86.Concurrency.Cir.Tv.RunEx.qLoadCert.body Regs.zero,
        normActs acc.flatten = p.1.flatMap Lab.acts ∧ (p.2 .rax).toNat = 2 ^ 32 :=
  Silmaril.Proofs.X86.Concurrency.Bridge.tvRun_real_qLoad

/-- **The pieces of a spin-cut function are complete**: every domain-bounded run
of the whole function is matched by a trace of `pexplore`, for the spin bound `n` = the run's
length. -/
theorem piecesComplete_holds : Task.piecesComplete :=
  fun _ _ _ h _ _ hsome _ _ hr hL => Silmaril.Proofs.X86.Concurrency.Bridge.pieces_complete h hsome hr hL

/-- **The restatement of `Task.piecesComplete` is needed**: without
`run ≠ [] ∨ th.code.length < 2 ^ 64` the statement is false, for `2 ^ 64` one-byte `nop`s cut
into `pad 1` pieces, whose end wraps to the start so that the empty run is a `DomRun` that no
trace of the pieces matches. -/
theorem piecesCompleteUnrestricted_false : ¬ PiecesCompleteUnrestricted :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Counter.piecesCompleteUnrestricted_false

/-- **A run of the whole spin-cut function is a CIR run**: every run of the bytes of the whole
function on `Atomic9.step` from its initial core to its end, with interference and reads in the
domain, is matched by an x86 trace that is a run of the CIR thread `c.body n` for some spin
bound `n`, with the same memory actions up to `normActs` and the same final registers outside
the clobber set. The run must be non-empty or the code shorter than `2 ^ 64` bytes
(`Task.piecesComplete`). -/
theorem whole_refines {th : SThread} {c : SCert} {K : List Reg}
    (h : stvRun th c = some K) {dom : List Nat} (hdom : ∀ v ∈ dom, v < 2 ^ 32) {fuel : Nat}
    (hsome : ∀ n, (pexplore th dom fuel n 0 c.pieces th.init).isSome = true)
    {xs : List SeqStep} {fin : State} (hr : DomRun (whole th) dom th.init xs fin)
    (hL : xs ≠ [] ∨ th.code.length < 2 ^ 64) :
    ∃ n, ∃ tr : Trace, tr.Matches xs fin ∧ ∃ p ∈ run dom (c.body n) Regs.zero,
      p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ q, q ∉ K → fin.read q = p.2 q := by
  obtain ⟨n, trs, hx, tr, htr, hm⟩ := piecesComplete_holds th c K h dom fuel hsome xs fin hr hL
  obtain ⟨p, hp, hacts, hregs⟩ := Silmaril.X86.Concurrency.Cir.Tv.stvRun_sound h hdom hx tr htr
  refine ⟨n, tr, hm, p, hp, hacts, fun q hq => ?_⟩
  rw [← hm.1]
  exact hregs q hq

/-! ## Gap 1 -/

/-- **Gap 1 as first stated is false**: without `CondInit`, a validated test with no
threads whose condition reads a data byte no location initialises is a counterexample. -/
theorem not_tsoRunCirAsStated : ¬ tsoRunCirAsStated :=
  Silmaril.Proofs.X86.Concurrency.Bridge.not_tsoRunCirAsStated

/-- **`CondInit` from its Boolean check**. -/
theorem condInit_of {t : Test} (h : condInitB t = true) : CondInit t :=
  Silmaril.Proofs.X86.Concurrency.Bridge.condInit_of h

/-- **Every corpus test observes only initialised bytes**: `CondInit` holds for
every test of the translation-validated corpus, including the 19 whose condition reads
memory (`R`, `S`, `2+2W` and their fenced variants, ...). -/
theorem corpus_condInit :
    ∀ c ∈ Silmaril.X86.Concurrency.Cir.Tv.Corpus.all, CondInit c.test :=
  Silmaril.Proofs.X86.Concurrency.Bridge.corpus_condInit

/-- **Gap 1 holds** (`Task.tsoRunCir` as restated): every final state of
the byte-granular TSO pool running a validated test's bytes on `Atomic9.step` has the witness
value of a TSO behaviour of the test's CIR program, when every access is a cell access
(`cellsB`) and the condition observes only initialised bytes (`CondInit`). -/
theorem tsoRunCir_holds : Task.tsoRunCir :=
  Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.tsoRunCir_holds

/-- **The statement of gap 1 is false** (formalising the counterexample): with the
per-thread `CellsOk` in place of `cellsB`, a one-thread test running `mov eax, dword [0x10004]`
with no locations and the condition `exists 0:rax = 5` passes `tvOk`, `CellsOk` and `CondInit`;
a test memory holding `5` at `0x10004` lets the TSO pool end with `rax = 5`, while every CIR
behaviour reads the uninitialised byte as `0`. -/
theorem not_tsoRunCirCells : ¬ tsoRunCirCells :=
  Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex.not_tsoRunCirCells

/-- The counterexample fails the cell check `cellsB` (its read byte is uninitialised), so it is
excluded by the restated `Task.tsoRunCir`. -/
theorem cex_not_cellsB :
    cellsB Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex.cex.test = false :=
  Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Cex.cex_not_cellsB

/-- **Every corpus test passes the cell check**: `cellsB` holds for all 60 tests of
the translation-validated corpus, so `Task.tsoRunCir`'s hypothesis is not vacuous. -/
theorem corpus_cellsB :
    ∀ c ∈ Silmaril.X86.Concurrency.Cir.Tv.Corpus.all, cellsB c.test = true :=
  Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.corpus_cellsB

/-- **The TSO pool over SB's bytes reaches the store-buffering outcome**: a
concrete run of the byte-granular TSO pool on `Atomic9.step` over the bytes of the corpus test
`SB` (both stores buffered, both loads reading `0` from memory, then both flushes) ends with
`0:rax = 0` and `1:rax = 0`, which SC forbids. The machine of `Task.tsoRunCir` is weak, and its
final states for a two-thread corpus test exist. -/
theorem sb_pool_allowed :
    Verdict.allowed.Holds Silmaril.X86.MemoryModel.Litmus.Corpus.«SB»
      (TsoFinal Silmaril.X86.MemoryModel.Litmus.Corpus.«SB») :=
  Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Sb.sb_pool_allowed

/-- **A forbidden CIR verdict holds for the bytes running concurrently** (unconditional): if no TSO
behaviour of the validated test's CIR program (over any domain) satisfies the witness,
no final state of the TSO machine over the bytes does, for a test whose accesses are
cell accesses and whose condition observes only initialised bytes. -/
theorem forbidden_tso_bytes {c : TvTest} (h : c.tvOk = true)
    (hC : cellsB c.test = true) (hI : CondInit c.test)
    (hv : Verdict.forbidden.Holds c.test (Behav c.prog Silmaril.X86.MemoryModel.Axiomatic.Exec.Tso)) :
    Verdict.forbidden.Holds c.test (TsoFinal c.test) := by
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hb, heq⟩ := tsoRunCir_holds c h hC hI f hf
  exact hv ⟨f', hb, heq.trans hw⟩

/-! ## Gap 4 -/

/-- **A listed `call rel32` on the real machine**: it pushes the return address `rip + 5`
at `rsp - 8`, lowers `rsp` by 8, keeps every other register and jumps to the target. -/
theorem call_law {t : XThread} {o fo : Nat} (hCall : CallAt t o fo) {s s₁ : State}
    {m₁ m₂ : Memory} (hrip : s.rip = t.base + BitVec.ofNat 64 o) (hl1 : Loaded m₁ t.base t.code)
    (hs : Atomic9.step ⟨s, m₁⟩ = some ⟨s₁, m₂⟩) :
    m₁.writeBytes (s.read .rsp - 8).toNat
        (Silmaril.Machine.LittleEndian.encodeWords [s.rip + 5]) = some m₂ ∧
      s₁.read .rsp = s.read .rsp - 8 ∧ s₁.rip = t.base + BitVec.ofNat 64 fo ∧
      ∀ r : Silmaril.X86.Reg, r ≠ .rsp → s₁.read r = s.read r :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Link.call_law hCall hrip hl1 hs

/-- **A listed `ret` on the real machine**: if its stack slot holds `w`, it goes to `w`,
raises `rsp` by 8, keeps every other register and leaves memory unchanged. -/
theorem ret_law {t : XThread} {k : Nat} (hC3 : t.code[k]? = some 0xC3) {s₂ s₃ : State}
    {m₃ m₄ : Memory} {w : BitVec 64} (hrip : s₂.rip = t.base + BitVec.ofNat 64 k)
    (hl : Loaded m₃ t.base t.code)
    (hread : m₃.readBytes (s₂.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [w]))
    (hs : Atomic9.step ⟨s₂, m₃⟩ = some ⟨s₃, m₄⟩) :
    s₃.rip = w ∧ s₃.read .rsp = s₂.read .rsp + 8 ∧ m₄ = m₃ ∧
      ∀ r : Silmaril.X86.Reg, r ≠ .rsp → s₃.read r = s₂.read r :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Link.ret_law hC3 hrip hl hread hs

/-- **`Task.callRet` holds** (as stated): one validated call on the real machine. -/
theorem callRet_holds : Task.callRet := Silmaril.Proofs.X86.Concurrency.Bridge.Link.callRet_holds

/-- **The caller checker against the real machine**: if `ltv` accepts the caller at
offset `o` of the image `t`, every real run of it from its start (`LRun`: its segments, calls,
callee bodies and returns, with interference, to the end of its last segment) of at most `L`
steps is a run of the linked CIR program `lc.body L` to `skip`, step for step (`LObs.Ok`: a
machine step's actions are those of its CIR label and the real step's; a `call` writes exactly
its 8-byte slot, a `ret` nothing, neither has a label), ending with the same registers. -/
theorem ltv_real {t : XThread} {o : Nat} {lc : LCert} (h : ltv t o lc = true) {s : State}
    {obs : List LObs} {s' : State} (hr : LRun t o lc.parts lc.lastLen lc.lastCert s obs s')
    (h0 : s.rip = t.base + BitVec.ofNat 64 o) {L : Nat} (hL : obs.length ≤ L) :
    ∃ rs, ∃ los : List (Option Lab), TRun (lc.body L) (regsOf s) (los.filterMap id) .skip rs ∧
      List.Forall₂ LObs.Ok obs los ∧ regsOf s' = rs :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Link.ltv_sound hr h h0 L hL

/-- **The caller checker reads only the image's code** (not its base, regions or start core). -/
theorem ltv_code {t t' : XThread} (h : t.code = t'.code) (o : Nat) (lc : LCert) :
    ltv t o lc = ltv t' o lc :=
  Silmaril.Proofs.X86.Concurrency.Bridge.Link.ltvFrom_code h o _ _ _

end Silmaril.X86.Concurrency.Bridge
