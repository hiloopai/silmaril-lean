module

public import Silmaril.X86.Concurrency.Story.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Thms
public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Thms
public import Silmaril.X86.Concurrency.Cir.C11.Corpus.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms
public import Silmaril.X86.Concurrency.Cir.Domain.Thms
public import Silmaril.X86.Concurrency.Bridge.Thms
import Silmaril.Proofs.X86.Concurrency.Story.Counter
import Silmaril.Proofs.X86.Concurrency.Story.CounterWit
import Silmaril.Proofs.X86.Concurrency.Story.C11Bytes
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Xl.Thms
public import Silmaril.X86.Concurrency.Story.Pipe.Thms

/-!
# The concurrency story: the front door (theorems)

All statements are PROVED with the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). None takes an open `Task` as a
hypothesis (the `*_pool_forbidden` theorems did until
`Bridge.Task.tsoRunCir` was proved).
Apart from the counter client (`Counter.*`, proofs in
`Silmaril/Proofs/X86/Concurrency/Story/Counter.lean`), every proof here is a few lines that
instantiate a theorem of an earlier module.

## 1. x86 litmus tests (`Bytes.*`)

Each test is a corpus test: hand-assembled x86 bytes (GNU `as`), one thread per CPU.
"On the bytes" means over the traces the extractor reads off those bytes (`Test.traces`), with
the candidate executions judged by the axiomatic model (`Allowed`, `Forbidden`,
`ForbiddenBelowXl`) or run on the store-buffer machine (`OpAllowed`, `OpForbidden`). "On CIR"
means the CIR program that the checker validated against the same bytes (`CirAllowed`,
`CirForbidden`); the two agree by `Tv.Corpus.corpus_agree`.

| theorem | test | verdict |
| --- | --- | --- |
| `Bytes.sb_allowed_tso`, `Bytes.sb_allowed_xl`, `Bytes.sb_forbidden_sc` | SB | store buffering allowed on TSO and XL, not on SC |
| `Bytes.sbMfences_forbidden` | SB+mfences | not allowed under any `M ⊑ XL` |
| `Bytes.mp_forbidden` | MP | not allowed under any `M ⊑ XL` (TSO keeps stores and loads in order) |
| `Bytes.lb_forbidden` | LB | not allowed under any `M ⊑ XL` (no load→store reordering) |
| `Bytes.iriw_forbidden` | IRIW (`amd6`) | not allowed under any `M ⊑ XL` (stores are multi-copy atomic) |
| `Bytes.w22_forbidden` | 2+2W | not allowed under any `M ⊑ XL` |
| `Bytes.n6_allowed_tso`, `Bytes.n6_allowed_xl`, `Bytes.n6_forbidden_sc` | n6 | allowed on TSO and XL (store forwarding), not on SC |
| `Bytes.xadd_counter_two` | RMW+lock-xadds-final | two `lock xadd`s always leave `2`, under any `M ⊑ XL` |
| `Bytes.mpMovnti_allowed_xl` | MP+movnti | allowed on XL (and TSO/SC, which ignore `movnti`, forbid it) |
| `Bytes.mpMovntiSfence_forbidden` | MP+movnti+sfence | not allowed under any `M ⊑ XL` |

On the concurrent TSO machine running the bytes (`Bridge.TsoFinal`), `Bytes.pool_forbidden` and
its instances `mp_pool_forbidden`, `sbMfences_pool_forbidden`, `iriw_pool_forbidden` hold
unconditionally (`Bridge.tsoRunCir_holds`, with the cell check `Bridge.cellsB` and
`Bridge.CondInit` discharged for every corpus test). In the other direction,
`sb_pool_allowed` runs SB's bytes on that machine to the store-buffering outcome,
so the machine is weak.

## 2. C11 litmus tests (`C11.*`)

Each is an object of `examples/litmus-c` compiled by gcc 13.3.0 or clang 23.1.3 and validated
into CIR with the C11 modes of its source. RC11 is judged on CIR; the x86 side on
the traces of the compiled bytes.

| theorem | test | verdict |
| --- | --- | --- |
| `C11.mpRa_forbidden` | MP, release/acquire | RC11 forbids it (race-free); the bytes forbid it under any `M ⊑ XL` |
| `C11.mpRlx_rc11_allowed_x86_forbidden` | MP, relaxed | RC11 allows it; the bytes forbid it under any `M ⊑ XL` |
| `C11.sbSc_forbidden` | SB, seq_cst | RC11 forbids it; the bytes forbid it under any `M ⊑ XL` |
| `C11.sbRa_allowed` | SB, release/acquire | RC11 allows it; so does the CIR program on TSO |
| `C11.sbRa_allowed_bytes` | SB, release/acquire | the compiled bytes show it on TSO (axiomatic and operational); SC forbids it |
| `C11.sbRa_allowed_xl` | SB, release/acquire | the compiled bytes show it on XL too |
| `C11.sbRlx_allowed` | SB, relaxed | RC11 allows it; the bytes show it on TSO (axiomatic and operational) and XL; SC forbids it |
| `C11.corpus_both_sides` | all 63 objects | the RC11 verdict on CIR, and the x86 verdict on the bytes: forbidden under every `M ⊑ XL`, or allowed on TSO (both semantics) and XL |
| `C11.compiled_correct` | all 63 objects | every tame XL behaviour of the bytes is an RC11 behaviour |

## 3. Composable primitives (`Counter.*`)

`Counter.counter_any_mutex`: the counter client of `Story.Counter` (`N` threads, each
`lock; x := x + 1; unlock`), proved **once** against the interface `Mutex.Iface`, ends with
`x = N` on CIR's native TSO and XL machines, for every mutex meeting the interface and every loop
bound; `counter_any_mutex_sc` is the SC machine. `counter_any_mutexG` is the same for the
ghost-aware interface `Mutex.IfaceG`, on TSO; `counter_any_mutexG_wb` is the same on
every buffered model (TSO and XL) for tame mutexes (`Csl.Tame.reach_tso_of_wb`). Instances:

* `counter_spin`, `counter_spinSc`, `counter_fmutex` (the spin mutex with `xchg` unlock, its
  `seq_cst` twin, Drepper's futex mutex): TSO and XL, and SC (`*_sc`);
* `counter_ticket` (the ticket lock, `N < 2 ^ 32`), `counter_spinMov` (spin lock with a plain
  `mov` unlock), `counter_fmutexDec` (Drepper's original `fetch_sub` unlock): TSO; and
  `counter_ticket_any`, `counter_spinMov_any`, `counter_fmutexDec_any`: TSO and XL.

Non-vacuity: `counter_spin_finishes` (two threads, spin mutex, a finished drained TSO run with
`x = 2`), and `racy_lost` (without the lock an increment is lost: `x = 1`).

## 4. A producer-consumer pipeline (`Pipe.*`)

Re-exported from `Story.Pipe.Thms`: a channel with `SafeR` specifications (`Pipe.send_spec`,
`Pipe.recv_spec`) and a mutex-protected result, composed in one CSL certificate.
`Pipe.pipe_any_mutexG`: for every tame mutex meeting `Mutex.IfaceG`, every finished, drained
state of CIR's TSO and XL machines has every message delivered in order and
`acc = |vs| + Σ vs`. Instances `Pipe.pipe_ticket`, `pipe_spinMov`, `pipe_fmutexDec`; non-vacuity
`Pipe.pipe_ticket_finishes`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Story

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (Test Verdict AxReach OpReach Model Cond Atom)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (TvTest)

/-! ## 1. x86 litmus tests -/

namespace Bytes

/-- **Everything a validated corpus test gives**, on the bytes and on CIR, for every model, and
on the operational machine. -/
theorem shown {c : TvTest} (hc : c ∈ Tv.Corpus.all) (ht : c.test ∈ MemoryModel.Litmus.Corpus.all)
    (hcov : c.test.coverage = .tso) :
    ∃ T, c.test.traces = some T ∧
      (∀ M : Model, (c.verdict M).Holds c.test (BehavIn c.prog c.test.domain M.Holds) ∧
        (c.verdict M).Holds c.test (AxReach c.test T M.Holds)) ∧
      ∀ v, c.test.tso = some v → v.Holds c.test (OpReach c.test T) := by
  obtain ⟨T, hT, h⟩ := Tv.Corpus.corpus_agree c hc
  obtain ⟨T', hT', hv⟩ := MemoryModel.Litmus.corpus_tso_verdicts c.test ht hcov
  rw [hT] at hT'; cases hT'
  exact ⟨T, hT, h, hv.tso_op⟩

/-- An allowed verdict, on the bytes and on CIR. -/
theorem allowed_of {c : TvTest} (hc : c ∈ Tv.Corpus.all) (ht : c.test ∈ MemoryModel.Litmus.Corpus.all)
    (hcov : c.test.coverage = .tso) (M : Model) (hv : c.verdict M = .allowed) :
    Allowed c.test M.Holds ∧ CirAllowed c M.Holds := by
  obtain ⟨T, hT, h, -⟩ := shown hc ht hcov
  have := h M
  rw [hv] at this
  exact ⟨⟨T, hT, this.2⟩, this.1⟩

/-- A forbidden verdict, on the bytes and on CIR. -/
theorem forbidden_of {c : TvTest} (hc : c ∈ Tv.Corpus.all) (ht : c.test ∈ MemoryModel.Litmus.Corpus.all)
    (hcov : c.test.coverage = .tso) (M : Model) (hv : c.verdict M = .forbidden) :
    Forbidden c.test M.Holds ∧ CirForbidden c M.Holds := by
  obtain ⟨T, hT, h, -⟩ := shown hc ht hcov
  have := h M
  rw [hv] at this
  exact ⟨⟨T, hT, this.2⟩, this.1⟩

/-- **Forbidden by XL, hence by every model `M ⊑ XL`**, on the bytes, on CIR, and on the
operational TSO machine. -/
theorem forbiddenXl_of {c : TvTest} (hc : c ∈ Tv.Corpus.all)
    (ht : c.test ∈ MemoryModel.Litmus.Corpus.all) (hcov : c.test.coverage = .tso)
    (hxl : c.test.xl = .forbidden) (htso : c.test.tso = some .forbidden) :
    ForbiddenBelowXl c.test ∧ (∀ M, M ⊑ Exec.Xl → CirForbidden c M) ∧ OpForbidden c.test := by
  obtain ⟨T, hT, h, hop⟩ := shown hc ht hcov
  have hx := h .xl
  simp only [TvTest.verdict, hxl] at hx
  refine ⟨⟨T, hT, fun M hM => ?_⟩, fun M hM => ?_, ⟨T, hT, hop _ htso⟩⟩
  · exact MemoryModel.Litmus.forbidden_anti (fun f hf => MemoryModel.Litmus.axReach_mono hM hf) hx.2
  · exact MemoryModel.Litmus.forbidden_anti (fun f hf => behavIn_mono hM hf) hx.1

set_option maxRecDepth 10000

-- The unused-tactic linter flags the `repeat (first | …)` membership search on nightly-2026-10-30.
set_option linter.unusedTactic false in
/-- **SB: store buffering is allowed on x86-TSO**: both loads may read `0`. On the bytes
(axiomatic TSO and the operational machine) and on CIR. -/
theorem sb_allowed_tso :
    Allowed MemoryModel.Litmus.Corpus.«SB» Exec.Tso ∧ OpAllowed MemoryModel.Litmus.Corpus.«SB» ∧
      CirAllowed Tv.Corpus.«SB» Exec.Tso := by
  have hc : Tv.Corpus.«SB» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«SB» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  obtain ⟨T, hT, -, hop⟩ := shown hc ht rfl
  obtain ⟨h1, h2⟩ := allowed_of hc ht rfl .tso rfl
  exact ⟨h1, ⟨T, hT, hop .allowed rfl⟩, h2⟩

-- The unused-tactic linter flags the `repeat (first | …)` membership search on nightly-2026-10-30.
set_option linter.unusedTactic false in
/-- **SB: store buffering is not allowed on SC.** -/
theorem sb_forbidden_sc :
    Forbidden MemoryModel.Litmus.Corpus.«SB» Exec.Sc ∧ CirForbidden Tv.Corpus.«SB» Exec.Sc := by
  have hc : Tv.Corpus.«SB» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«SB» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbidden_of hc ht rfl .sc rfl
  exact h

/-- **SB+mfences: with an `mfence` in each thread, store buffering is not allowed** under any
model `M ⊑ XL`. -/
theorem sbMfences_forbidden :
    ForbiddenBelowXl MemoryModel.Litmus.Corpus.«SB+mfences» ∧
      (∀ M, M ⊑ Exec.Xl → CirForbidden Tv.Corpus.«SB+mfences» M) ∧
      OpForbidden MemoryModel.Litmus.Corpus.«SB+mfences» := by
  have hc : Tv.Corpus.«SB+mfences» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«SB+mfences» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbiddenXl_of hc ht rfl rfl rfl
  exact h

/-- **MP: message passing works on x86**: a reader that sees the flag sees the data, under any
model `M ⊑ XL`. -/
theorem mp_forbidden :
    ForbiddenBelowXl MemoryModel.Litmus.Corpus.«MP» ∧
      (∀ M, M ⊑ Exec.Xl → CirForbidden Tv.Corpus.«MP» M) ∧
      OpForbidden MemoryModel.Litmus.Corpus.«MP» := by
  have hc : Tv.Corpus.«MP» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«MP» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbiddenXl_of hc ht rfl rfl rfl
  exact h

/-- **LB: load buffering is not allowed** under any model `M ⊑ XL`. -/
theorem lb_forbidden :
    ForbiddenBelowXl MemoryModel.Litmus.Corpus.«LB» ∧
      (∀ M, M ⊑ Exec.Xl → CirForbidden Tv.Corpus.«LB» M) ∧
      OpForbidden MemoryModel.Litmus.Corpus.«LB» := by
  have hc : Tv.Corpus.«LB» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«LB» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbiddenXl_of hc ht rfl rfl rfl
  exact h

/-- **IRIW (`amd6`): two readers never see two independent writes in opposite orders**, under any
model `M ⊑ XL`. -/
theorem iriw_forbidden :
    ForbiddenBelowXl MemoryModel.Litmus.Corpus.«amd6» ∧
      (∀ M, M ⊑ Exec.Xl → CirForbidden Tv.Corpus.«amd6» M) ∧
      OpForbidden MemoryModel.Litmus.Corpus.«amd6» := by
  have hc : Tv.Corpus.«amd6» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«amd6» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbiddenXl_of hc ht rfl rfl rfl
  exact h

/-- **2+2W: two pairs of writes cannot be ordered against each other in a cycle**, under any
model `M ⊑ XL`. -/
theorem w22_forbidden :
    ForbiddenBelowXl MemoryModel.Litmus.Corpus.«2+2W» ∧
      (∀ M, M ⊑ Exec.Xl → CirForbidden Tv.Corpus.«2+2W» M) ∧
      OpForbidden MemoryModel.Litmus.Corpus.«2+2W» := by
  have hc : Tv.Corpus.«2+2W» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«2+2W» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbiddenXl_of hc ht rfl rfl rfl
  exact h

/-- **An allowed TSO behaviour is allowed on XL** (on the bytes and on CIR): XL is weaker than
TSO (`Cir.tso_le_xl`). -/
theorem allowed_xl_of_tso {t : Test} {c : TvTest} (h1 : Allowed t Exec.Tso)
    (h2 : CirAllowed c Exec.Tso) : Allowed t Exec.Xl ∧ CirAllowed c Exec.Xl := by
  obtain ⟨T, hT, f, hf, hw⟩ := h1
  obtain ⟨f', hf', hw'⟩ := h2
  exact ⟨⟨T, hT, f, MemoryModel.Litmus.axReach_mono tso_le_xl hf, hw⟩,
    ⟨f', behavIn_mono tso_le_xl hf', hw'⟩⟩

/-- **SB is allowed on XL**, on the bytes and on CIR. -/
theorem sb_allowed_xl :
    Allowed MemoryModel.Litmus.Corpus.«SB» Exec.Xl ∧ CirAllowed Tv.Corpus.«SB» Exec.Xl :=
  allowed_xl_of_tso sb_allowed_tso.1 sb_allowed_tso.2.2

/-- **n6: a thread may read its own store early (store forwarding) while the other thread's
stores land in between**: allowed on x86-TSO, on the bytes (both machines) and on CIR. -/
theorem n6_allowed_tso :
    Allowed MemoryModel.Litmus.Corpus.«n6» Exec.Tso ∧ OpAllowed MemoryModel.Litmus.Corpus.«n6» ∧
      CirAllowed Tv.Corpus.«n6» Exec.Tso := by
  have hc : Tv.Corpus.«n6» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«n6» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  obtain ⟨T, hT, -, hop⟩ := shown hc ht rfl
  obtain ⟨h1, h2⟩ := allowed_of hc ht rfl .tso rfl
  exact ⟨h1, ⟨T, hT, hop .allowed rfl⟩, h2⟩

/-- **n6 is not allowed on SC.** -/
theorem n6_forbidden_sc :
    Forbidden MemoryModel.Litmus.Corpus.«n6» Exec.Sc ∧ CirForbidden Tv.Corpus.«n6» Exec.Sc := by
  have hc : Tv.Corpus.«n6» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«n6» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h := forbidden_of hc ht rfl .sc rfl
  exact h

/-- **n6 is allowed on XL**, on the bytes and on CIR. -/
theorem n6_allowed_xl :
    Allowed MemoryModel.Litmus.Corpus.«n6» Exec.Xl ∧ CirAllowed Tv.Corpus.«n6» Exec.Xl :=
  allowed_xl_of_tso n6_allowed_tso.1 n6_allowed_tso.2.2

/-- **Two `lock xadd` increments always leave `x = 2`**: under every model `M ⊑ XL`, every final
state of the bytes' executions has `[x] = 2` (`x` at `0x10000`, 4 bytes), and the same for the
CIR program; some SC execution exists, so this is not vacuous. -/
theorem xadd_counter_two :
    (∃ T, MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final».traces = some T ∧
      (∀ M, M ⊑ Exec.Xl → ∀ f, AxReach MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final» T M f →
        (Cond.atom (.mem 0x10000 4 2)).eval f = true) ∧
      ∃ f, AxReach MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final» T Exec.Sc f) ∧
    ∀ M, M ⊑ Exec.Xl → ∀ f,
      BehavIn Tv.Corpus.«RMW+lock-xadds-final».prog
        MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final».domain M f →
      (Cond.atom (.mem 0x10000 4 2)).eval f = true := by
  have hc : Tv.Corpus.«RMW+lock-xadds-final» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have ht : MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  obtain ⟨⟨T, hT, hB⟩, hC, -⟩ := forbiddenXl_of hc ht rfl rfl rfl
  obtain ⟨T', hT', hv⟩ := MemoryModel.Litmus.corpus_tso_verdicts _ ht rfl
  obtain rfl : T = T' := Option.some.inj (hT.symm.trans hT')
  have key : ∀ f, MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final».witness.eval f = false →
      (Cond.atom (.mem 0x10000 4 2)).eval f = true := by
    intro f hf
    change (Cond.not (Cond.atom (.mem 0x10000 4 2))).eval f = false at hf
    simpa [Cond.eval] using hf
  refine ⟨⟨T, hT, fun M hM f hf => key f ?_, hv.sc_some⟩, fun M hM f hf => key f ?_⟩
  · cases e : MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final».witness.eval f
    · rfl
    · exact absurd ⟨f, hf, e⟩ (hB M hM)
  · cases e : MemoryModel.Litmus.Corpus.«RMW+lock-xadds-final».witness.eval f
    · rfl
    · exact absurd ⟨f, hf, e⟩ (hC M hM)

/-- **MP+movnti: a non-temporal data store may pass the flag store**, so the reader can see the
flag and stale data: allowed on XL (over the `Weak9` traces of the bytes). x86-TSO and SC, which
treat `movnti` as a plain store, forbid it; XL is the model that is right for these bytes. -/
theorem mpMovnti_allowed_xl :
    LooseAllowed MemoryModel.Litmus.Corpus.«MP+movnti» Exec.Xl ∧
      LooseForbidden MemoryModel.Litmus.Corpus.«MP+movnti» Exec.Tso ∧
      LooseForbidden MemoryModel.Litmus.Corpus.«MP+movnti» Exec.Sc := by
  have ht : MemoryModel.Litmus.Corpus.«MP+movnti» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  obtain ⟨T, hT, hx, ht', hs, -⟩ := MemoryModel.Litmus.corpus_loose_xl _ ht rfl
  exact ⟨⟨T, hT, hx⟩, ⟨T, hT, ht'⟩, ⟨T, hT, hs⟩⟩

/-- **MP+movnti+sfence: an `sfence` after the non-temporal store restores message passing**:
not allowed under any model `M ⊑ XL` (over the `Weak9` traces of the bytes). -/
theorem mpMovntiSfence_forbidden :
    ∃ T, MemoryModel.Litmus.Corpus.«MP+movnti+sfence».looseTraces = some T ∧
      ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds MemoryModel.Litmus.Corpus.«MP+movnti+sfence»
          (AxReach MemoryModel.Litmus.Corpus.«MP+movnti+sfence» T M) := by
  have ht : MemoryModel.Litmus.Corpus.«MP+movnti+sfence» ∈ MemoryModel.Litmus.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  obtain ⟨T, hT, hx, -⟩ := MemoryModel.Litmus.corpus_loose_xl _ ht rfl
  exact ⟨T, hT, fun M hM =>
    MemoryModel.Litmus.forbidden_anti (fun f hf => MemoryModel.Litmus.axReach_mono hM hf) hx⟩

/-! ### The bytes running concurrently (gap 1, proved)

`Bridge.TsoFinal t` is the set of final states of the byte-granular TSO pool running the test's
bytes on `Atomic9.step` (instruction fetch, store buffers, flushes): a concurrent machine over
the real bytes, not a set of extracted traces. Getting a verdict there is the open gap
`Bridge.Task.tsoRunCir`, proved (`Bridge.tsoRunCir_holds`) for tests whose
accesses are cell accesses (`Bridge.cellsB`) and whose condition observes only initialised
bytes (`Bridge.CondInit`). Both checks hold for every corpus test (`Bridge.corpus_cellsB`,
`Bridge.corpus_condInit`), so the verdicts below are unconditional. -/

/-- **A forbidden TSO verdict of a validated corpus test holds for its bytes running on the
concurrent TSO machine.** -/
theorem pool_forbidden {c : TvTest} (hc : c ∈ Tv.Corpus.all)
    (hU : c.prog.uniformB = true) (hD : c.prog.preClosedB c.test.domain = true)
    (hB : c.prog.threads.all (·.body.blocks.isEmpty) = true)
    (hv : c.verdict .tso = .forbidden) :
    Verdict.forbidden.Holds c.test (Bridge.TsoFinal c.test) := by
  have hok := Tv.Corpus.corpus_all_ok c hc
  simp only [TvTest.allOk, Bool.and_eq_true] at hok
  obtain ⟨T, -, h⟩ := Tv.Corpus.corpus_agree c hc
  have hcir := (h .tso).1
  rw [hv] at hcir
  exact Bridge.forbidden_tso_bytes hok.1.1.1 (Bridge.corpus_cellsB c hc)
    (Bridge.corpus_condInit c hc)
    (forbidden_behav hU hD (blocksClosed_of_noBlocks hB _) .tso hcir)

/-- **MP on the concurrent TSO machine over its bytes**: the stale read is forbidden. -/
theorem mp_pool_forbidden :
    Verdict.forbidden.Holds MemoryModel.Litmus.Corpus.«MP» (Bridge.TsoFinal MemoryModel.Litmus.Corpus.«MP») := by
  have hc : Tv.Corpus.«MP» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  exact pool_forbidden hc (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl

/-- **SB+mfences on the concurrent TSO machine over its bytes**: with `mfence`s, both loads
cannot read `0`. -/
theorem sbMfences_pool_forbidden :
    Verdict.forbidden.Holds MemoryModel.Litmus.Corpus.«SB+mfences»
      (Bridge.TsoFinal MemoryModel.Litmus.Corpus.«SB+mfences») := by
  have hc : Tv.Corpus.«SB+mfences» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  exact pool_forbidden hc (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl

/-- **SB on the concurrent TSO machine over its bytes**: the store-buffering outcome
`0:rax = 0 ∧ 1:rax = 0` (forbidden under SC) is reached by a concrete run. -/
theorem sb_pool_allowed :
    Verdict.allowed.Holds MemoryModel.Litmus.Corpus.«SB» (Bridge.TsoFinal MemoryModel.Litmus.Corpus.«SB») :=
  Bridge.sb_pool_allowed

/-- **IRIW on the concurrent TSO machine over its bytes**: the two readers cannot see the two
writes in opposite orders. -/
theorem iriw_pool_forbidden :
    Verdict.forbidden.Holds MemoryModel.Litmus.Corpus.«amd6»
      (Bridge.TsoFinal MemoryModel.Litmus.Corpus.«amd6») := by
  have hc : Tv.Corpus.«amd6» ∈ Tv.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  exact pool_forbidden hc (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl

end Bytes

/-! ## 2. C11 litmus tests -/

namespace C11

open Silmaril.X86.Concurrency.Cir.C11 (C11Test CVerdict)

/-- **A witness XL forbids on CIR is forbidden for the compiled bytes under every `M ⊑ XL`.** -/
theorem bytes_forbidden {c : C11Test} (hc : c.Holds) (hxl : c.tv.test.xl = .forbidden) :
    ∃ T, c.tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
      Verdict.forbidden.Holds c.tv.test (AxReach c.tv.test T M) := by
  obtain ⟨T, hT, href⟩ := hc.refines
  have hx := hc.cir_xl
  rw [hxl] at hx
  refine ⟨T, hT, fun M hM => ?_⟩
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hf', hw'⟩ := href M f hf
  exact hx ⟨f', behavIn_mono hM hf', hw'.trans hw⟩

set_option maxRecDepth 10000

/-- **MP with release/acquire** (`examples/litmus-c/mp`, `MODE=2`, gcc and clang): RC11 forbids
the reader seeing the flag but not the data (and the program is race-free), and so do the
compiled bytes under every `M ⊑ XL`. -/
theorem mpRa_forbidden :
    (CVerdict.forbidden.Holds Cir.C11.Corpus.«MP+ra@gcc» ∧
      ∃ T, Cir.C11.Corpus.«MP+ra@gcc».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«MP+ra@gcc».tv.test
          (AxReach Cir.C11.Corpus.«MP+ra@gcc».tv.test T M)) ∧
    (CVerdict.forbidden.Holds Cir.C11.Corpus.«MP+ra@clang» ∧
      ∃ T, Cir.C11.Corpus.«MP+ra@clang».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«MP+ra@clang».tv.test
          (AxReach Cir.C11.Corpus.«MP+ra@clang».tv.test T M)) := by
  have h1 : Cir.C11.Corpus.«MP+ra@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«MP+ra@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have H1 := Cir.C11.Corpus.corpus_holds _ h1
  have H2 := Cir.C11.Corpus.corpus_holds _ h2
  exact ⟨⟨H1.rc11, bytes_forbidden H1 rfl⟩, ⟨H2.rc11, bytes_forbidden H2 rfl⟩⟩

/-- **MP with relaxed atomics** (`MODE=1`): RC11 allows the stale read (race-free, and some
RC11-consistent execution of the CIR program shows it), but the compiled bytes never show it
under any `M ⊑ XL`: x86 is strictly stronger here (`corpus_stronger`). -/
theorem mpRlx_rc11_allowed_x86_forbidden :
    (CVerdict.allowed.Holds Cir.C11.Corpus.«MP+rlx@gcc» ∧
      ∃ T, Cir.C11.Corpus.«MP+rlx@gcc».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«MP+rlx@gcc».tv.test
          (AxReach Cir.C11.Corpus.«MP+rlx@gcc».tv.test T M)) ∧
    (CVerdict.allowed.Holds Cir.C11.Corpus.«MP+rlx@clang» ∧
      ∃ T, Cir.C11.Corpus.«MP+rlx@clang».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«MP+rlx@clang».tv.test
          (AxReach Cir.C11.Corpus.«MP+rlx@clang».tv.test T M)) := by
  have h1 : Cir.C11.Corpus.«MP+rlx@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«MP+rlx@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have H1 := Cir.C11.Corpus.corpus_holds _ h1
  have H2 := Cir.C11.Corpus.corpus_holds _ h2
  exact ⟨⟨H1.rc11, bytes_forbidden H1 rfl⟩, ⟨H2.rc11, bytes_forbidden H2 rfl⟩⟩

/-- **SB with seq_cst** (`MODE=3`): RC11 forbids both loads reading `0`, and so do the compiled
bytes (an `mfence` or `xchg` per store) under every `M ⊑ XL`. -/
theorem sbSc_forbidden :
    (CVerdict.forbidden.Holds Cir.C11.Corpus.«SB+sc@gcc» ∧
      ∃ T, Cir.C11.Corpus.«SB+sc@gcc».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«SB+sc@gcc».tv.test
          (AxReach Cir.C11.Corpus.«SB+sc@gcc».tv.test T M)) ∧
    (CVerdict.forbidden.Holds Cir.C11.Corpus.«SB+sc@clang» ∧
      ∃ T, Cir.C11.Corpus.«SB+sc@clang».tv.test.traces = some T ∧ ∀ M, M ⊑ Exec.Xl →
        Verdict.forbidden.Holds Cir.C11.Corpus.«SB+sc@clang».tv.test
          (AxReach Cir.C11.Corpus.«SB+sc@clang».tv.test T M)) := by
  have h1 : Cir.C11.Corpus.«SB+sc@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«SB+sc@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have H1 := Cir.C11.Corpus.corpus_holds _ h1
  have H2 := Cir.C11.Corpus.corpus_holds _ h2
  exact ⟨⟨H1.rc11, bytes_forbidden H1 rfl⟩, ⟨H2.rc11, bytes_forbidden H2 rfl⟩⟩

/-- **SB with release/acquire** (`MODE=2`): RC11 allows both loads reading `0` (race-free), and
the CIR program validated from the compiled bytes shows it on TSO. (An allowed verdict does not
transfer from CIR to x86; that the bytes show it is `sbRa_allowed_bytes`, from the byte
check.) -/
theorem sbRa_allowed :
    (CVerdict.allowed.Holds Cir.C11.Corpus.«SB+ra@gcc» ∧
      Verdict.allowed.Holds Cir.C11.Corpus.«SB+ra@gcc».tv.test
        (BehavIn Cir.C11.Corpus.«SB+ra@gcc».prog Cir.C11.Corpus.«SB+ra@gcc».dom Exec.Tso)) ∧
    (CVerdict.allowed.Holds Cir.C11.Corpus.«SB+ra@clang» ∧
      Verdict.allowed.Holds Cir.C11.Corpus.«SB+ra@clang».tv.test
        (BehavIn Cir.C11.Corpus.«SB+ra@clang».prog Cir.C11.Corpus.«SB+ra@clang».dom Exec.Tso)) := by
  have h1 : Cir.C11.Corpus.«SB+ra@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«SB+ra@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have H1 := Cir.C11.Corpus.corpus_holds _ h1
  have H2 := Cir.C11.Corpus.corpus_holds _ h2
  exact ⟨⟨H1.rc11, H1.cir_tso .allowed rfl⟩, ⟨H2.rc11, H2.cir_tso .allowed rfl⟩⟩

/-- **SB with release/acquire, on the compiled bytes**: over the traces
extracted from the gcc and clang objects, x86-TSO allows both loads reading `0` (axiomatically
and on the operational machine), and SC forbids it. So the RC11-allowed behaviour of
`sbRa_allowed` is really observable on the x86 code, and TSO is not secretly SC here. The bytes
pass the byte check (`checkTsoBytes`, kernel-evaluated in `Story/C11Bytes.lean`). -/
theorem sbRa_allowed_bytes :
    (Allowed Cir.C11.Corpus.«SB+ra@gcc».tv.test Exec.Tso ∧
      OpAllowed Cir.C11.Corpus.«SB+ra@gcc».tv.test ∧
      Forbidden Cir.C11.Corpus.«SB+ra@gcc».tv.test Exec.Sc) ∧
    (Allowed Cir.C11.Corpus.«SB+ra@clang».tv.test Exec.Tso ∧
      OpAllowed Cir.C11.Corpus.«SB+ra@clang».tv.test ∧
      Forbidden Cir.C11.Corpus.«SB+ra@clang».tv.test Exec.Sc) := by
  obtain ⟨T1, hT1, v1⟩ := MemoryModel.Litmus.tsoVerdicts_of_checkBytes
    Silmaril.Proofs.X86.Concurrency.Story.sbRa_gcc_checkTsoBytes
  obtain ⟨T2, hT2, v2⟩ := MemoryModel.Litmus.tsoVerdicts_of_checkBytes
    Silmaril.Proofs.X86.Concurrency.Story.sbRa_clang_checkTsoBytes
  exact ⟨⟨⟨T1, hT1, v1.tso_ax .allowed rfl⟩, ⟨T1, hT1, v1.tso_op .allowed rfl⟩,
      ⟨T1, hT1, v1.sc_ax .forbidden rfl⟩⟩,
    ⟨⟨T2, hT2, v2.tso_ax .allowed rfl⟩, ⟨T2, hT2, v2.tso_op .allowed rfl⟩,
      ⟨T2, hT2, v2.sc_ax .forbidden rfl⟩⟩⟩

/-- **An x86-allowed C11 object is allowed on its bytes**: over the traces of the
compiled bytes, x86-TSO allows the witness axiomatically and on the operational machine, and so
does XL. This is the byte-level allowed verdict that no CIR theorem gives (an allowed verdict does
not transfer from CIR to the bytes); it comes from the byte check (`allowed_checks`). -/
theorem bytes_allowed {c : C11Test} (hc : c ∈ Cir.C11.Corpus.all)
    (hxl : c.tv.test.xl = .allowed) :
    Allowed c.tv.test Exec.Tso ∧ OpAllowed c.tv.test ∧ Allowed c.tv.test Exec.Xl := by
  have h := List.all_eq_true.mp Silmaril.Proofs.X86.Concurrency.Story.allowed_checks c hc
  simp only [hxl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨htso, hck⟩ := h
  obtain ⟨T, hT, v⟩ := MemoryModel.Litmus.tsoVerdicts_of_checkBytes hck
  have hx := v.xl_ax
  rw [hxl] at hx
  exact ⟨⟨T, hT, v.tso_ax .allowed htso⟩, ⟨T, hT, v.tso_op .allowed htso⟩, ⟨T, hT, hx⟩⟩

/-- **Every C11 object has both sides**: its RC11 verdict on CIR (`racy`, or
race-free with the witness allowed or forbidden: `CVerdict.Holds`), and its x86 verdict on the
compiled bytes. If x86 forbids the witness it is forbidden under every `M ⊑ XL`; if x86 allows it,
it is allowed on TSO (axiomatic and operational) and on XL. All 63 objects, gcc and clang. -/
theorem corpus_both_sides {c : C11Test} (hc : c ∈ Cir.C11.Corpus.all) :
    c.expected.Holds c ∧ (c.tv.test.xl = .forbidden → ForbiddenBelowXl c.tv.test) ∧
      (c.tv.test.xl = .allowed →
        Allowed c.tv.test Exec.Tso ∧ OpAllowed c.tv.test ∧ Allowed c.tv.test Exec.Xl) := by
  have H := Cir.C11.Corpus.corpus_holds _ hc
  exact ⟨H.rc11, fun hxl => bytes_forbidden H hxl, fun hxl => bytes_allowed hc hxl⟩

/-- **SB with relaxed atomics** (`MODE=1`, gcc and clang): RC11 allows both loads reading `0`
(race-free), and the compiled bytes show it on x86-TSO (axiomatic and operational) and on XL;
SC forbids it on the bytes. -/
theorem sbRlx_allowed :
    (CVerdict.allowed.Holds Cir.C11.Corpus.«SB+rlx@gcc» ∧
      Allowed Cir.C11.Corpus.«SB+rlx@gcc».tv.test Exec.Tso ∧
      OpAllowed Cir.C11.Corpus.«SB+rlx@gcc».tv.test ∧
      Allowed Cir.C11.Corpus.«SB+rlx@gcc».tv.test Exec.Xl ∧
      Forbidden Cir.C11.Corpus.«SB+rlx@gcc».tv.test Exec.Sc) ∧
    (CVerdict.allowed.Holds Cir.C11.Corpus.«SB+rlx@clang» ∧
      Allowed Cir.C11.Corpus.«SB+rlx@clang».tv.test Exec.Tso ∧
      OpAllowed Cir.C11.Corpus.«SB+rlx@clang».tv.test ∧
      Allowed Cir.C11.Corpus.«SB+rlx@clang».tv.test Exec.Xl ∧
      Forbidden Cir.C11.Corpus.«SB+rlx@clang».tv.test Exec.Sc) := by
  have h1 : Cir.C11.Corpus.«SB+rlx@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«SB+rlx@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have H1 := Cir.C11.Corpus.corpus_holds _ h1
  have H2 := Cir.C11.Corpus.corpus_holds _ h2
  have sc : ∀ c ∈ Cir.C11.Corpus.all, c.tv.test.xl = .allowed → c.tv.test.sc = some .forbidden →
      Forbidden c.tv.test Exec.Sc := fun c hc hxl hsc => by
    have h := List.all_eq_true.mp Silmaril.Proofs.X86.Concurrency.Story.allowed_checks c hc
    simp only [hxl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨T, hT, v⟩ := MemoryModel.Litmus.tsoVerdicts_of_checkBytes h.2
    exact ⟨T, hT, v.sc_ax .forbidden hsc⟩
  obtain ⟨a1, b1, c1⟩ := bytes_allowed h1 rfl
  obtain ⟨a2, b2, c2⟩ := bytes_allowed h2 rfl
  exact ⟨⟨H1.rc11, a1, b1, c1, sc _ h1 rfl rfl⟩, ⟨H2.rc11, a2, b2, c2, sc _ h2 rfl rfl⟩⟩

/-- **SB with release/acquire is allowed on XL too, on the bytes** (`sbRa_allowed_bytes`
gives TSO and SC). -/
theorem sbRa_allowed_xl :
    Allowed Cir.C11.Corpus.«SB+ra@gcc».tv.test Exec.Xl ∧
      Allowed Cir.C11.Corpus.«SB+ra@clang».tv.test Exec.Xl := by
  have h1 : Cir.C11.Corpus.«SB+ra@gcc» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  have h2 : Cir.C11.Corpus.«SB+ra@clang» ∈ Cir.C11.Corpus.all := by
    repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)
  exact ⟨(bytes_allowed h1 rfl).2.2, (bytes_allowed h2 rfl).2.2⟩

/-- **Compilation is correct on the whole corpus** (the mapping theorem, not a per-test
enumeration): every tame XL behaviour of a compiled object's bytes has the witness value of an
RC11 behaviour of its CIR program. -/
theorem compiled_correct {c : C11Test} (hc : c ∈ Cir.C11.Corpus.all)
    {T : List (List MemoryModel.Litmus.XTrace)} (hT : c.tv.test.traces = some T)
    {f : MemoryModel.Litmus.Final} (hf : AxReach c.tv.test T (fun x => x.Xl ∧ x.Tame) f) :
    ∃ f', c.Rc f' ∧ c.tv.test.witness.eval f' = c.tv.test.witness.eval f :=
  Cir.C11.Corpus.corpus_x86_rc11 hc hT hf

end C11

/-! ## 3. Composable primitives: a counter behind the mutex interface -/

namespace Counter

open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex

/-- **The counter, proved once against the interface**: linked with **any** mutex `M` meeting
`Mutex.Iface` (object at most 8 bytes), for every number of threads `0 < N < 2 ^ 64` and
every loop bound, every finished, drained state of CIR's native TSO or XL machine has `x = N`. -/
theorem counter_any_mutex (M : Iface) (hM : M.size ≤ 8) {N : Nat} (hN0 : 0 < N)
    (hN : N < 2 ^ 64) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model N ((client N).link M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Story.counter_link M hM hN0 hN L hr hd hf

/-- **The same on CIR's SC machine.** -/
theorem counter_any_mutex_sc (M : Iface) (hM : M.size ≤ 8) {N : Nat} (hN0 : 0 < N)
    (hN : N < 2 ^ 64) (L : Nat) {Cf : Cfg} (hr : ScReach N ((client N).link M L) Cf)
    (hf : Cf.Done N) : Goal N Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Story.counter_link_sc M hM hN0 hN L hr hf

/-- **The counter, proved once against the ghost-aware interface** `Mutex.IfaceG`: every
finished, drained TSO state has `x = N`, for every `IfaceG` mutex supporting `N` threads. -/
theorem counter_any_mutexG (M : IfaceG) (hM : M.size ≤ 8) {N : Nat} (hN : M.thrOk N)
    (hN0 : 0 < N) (hN64 : N < 2 ^ 64) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso N ((client N).linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  Silmaril.Proofs.X86.Concurrency.Story.counter_linkG M hM hN hN0 hN64 L hr hd hf

/-- **With the spin mutex of `mutex.c`** (`xchg` loop, `xchg` unlock), on TSO and XL. -/
theorem counter_spin {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {model : OModel}
    {Cf : OCfg} (hr : OReach model N ((client N).link spinMutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutex spinMutex (Nat.le_refl _) hN0 hN L hr hd hf

/-- With the spin mutex whose unlock is `mutex_unlock_sc` (C11 `store(seq_cst)`), on TSO and
XL. -/
theorem counter_spinSc {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {model : OModel}
    {Cf : OCfg} (hr : OReach model N ((client N).link spinMutexSc L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutex spinMutexSc (Nat.le_refl _) hN0 hN L hr hd hf

/-- **With Drepper's futex mutex** (gcc `-O2` bytes), on TSO and XL. -/
theorem counter_fmutex {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {model : OModel}
    {Cf : OCfg} (hr : OReach model N ((client N).link Futex.fmutex L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutex Futex.fmutex (Nat.le_refl _) hN0 hN L hr hd hf

/-- The spin mutex on the SC machine. -/
theorem counter_spin_sc {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {Cf : Cfg}
    (hr : ScReach N ((client N).link spinMutex L) Cf) (hf : Cf.Done N) : Goal N Cf.mem :=
  counter_any_mutex_sc spinMutex (Nat.le_refl _) hN0 hN L hr hf

/-- The futex mutex on the SC machine. -/
theorem counter_fmutex_sc {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {Cf : Cfg}
    (hr : ScReach N ((client N).link Futex.fmutex L) Cf) (hf : Cf.Done N) : Goal N Cf.mem :=
  counter_any_mutex_sc Futex.fmutex (Nat.le_refl _) hN0 hN L hr hf

/-- **With the ticket lock** (`lock xadd` ticket, plain-load wait, plain-`mov` release), for
`0 < N < 2 ^ 32`, on TSO. -/
theorem counter_ticket {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 32) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso N ((client N).linkG ticketMutexG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG ticketMutexG (Nat.le_refl _) hN hN0 (by omega) L hr hd hf

/-- With the spin lock and the plain-`mov` unlock (`spin_unlock`, C11 `store(release)`), on
TSO. -/
theorem counter_spinMov {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso N ((client N).linkG spinMovG L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG spinMovG (Nat.le_refl _) trivial hN0 hN L hr hd hf

/-- With Drepper's mutex and its original unlock (`fetch_sub`, plain-`mov` release, wake), on
TSO. -/
theorem counter_fmutexDec {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso N ((client N).linkG (Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceG.ofIfaceR Futex.fmutexDec) L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG (Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceG.ofIfaceR Futex.fmutexDec) (Nat.le_refl _) trivial hN0 hN L hr hd hf

/-- **Non-vacuity**: the counter with two threads and the spin mutex (loop bound 2) reaches a
finished, drained TSO state (the explorer), which has `x = 2` by `counter_spin`. -/
theorem counter_spin_finishes : ∃ Cf : OCfg,
    OReach .tso 2 ((client 2).link spinMutex 2).toO Cf ∧ Cf.Drained ∧
      (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Goal 2 Cf.mem := by
  obtain ⟨d, hr, hd, hf, -⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.spinC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Story.spin_fin
  rw [Silmaril.Proofs.X86.Concurrency.Story.spinC_cfg] at hr
  exact ⟨d.ocfg, hr, hd, hf, counter_spin (by decide) (by decide) 2 hr hd hf⟩

/-- **The goal needs the mutex**: with both holes empty, two increments can lose one; a
finished, drained TSO state has `x = 1`. -/
theorem racy_lost : ∃ Cf : OCfg,
    OReach .tso 2 ((client 2).startWith Mutex.Inst.noOp Mutex.Inst.noOp Heap.empty).toO Cf ∧
      Cf.Drained ∧ (∀ t < 2, (Cf.ts t).1 = .skip) ∧ Cf.mem x = some 1 := by
  obtain ⟨d, hr, hd, hf, hp⟩ := Robust.witness_of_any (N := 2) (c0 := Inst.racyC) rfl rfl
    Silmaril.Proofs.X86.Concurrency.Story.racy_lost
  rw [Silmaril.Proofs.X86.Concurrency.Story.racyC_cfg] at hr
  refine ⟨d.ocfg, hr, hd, hf, ?_⟩
  simpa [Inst.countIs, Robust.CSt.ocfg] using hp

/-! ### The release-store mutexes on every buffered model

The counter client is tame (`counter_wb`: its only store, the increment, is write-back), and so
are the ticket lock and the `mov`-release mutexes (`Mutex.ticketMutexG_wb`, `spinMovG_wb`,
`ofIfaceR_wb fmutexDec_wb`). So the TSO-only instances above hold on every buffered model, XL
included (`Csl.Tame.reach_tso_of_wb`). -/

/-- **The counter client is tame.** -/
theorem counter_wb (N : Nat) : (client N).WbIn := by
  intro lk ul hl hu t
  simp [client, body, inc, Stmt.wbStores, hl, hu]

/-- **`counter_any_mutexG` on every buffered model**, for tame `IfaceG` mutexes. -/
theorem counter_any_mutexG_wb (M : IfaceG) (hMw : M.WbCode) (hM : M.size ≤ 8) {N : Nat}
    (hN : M.thrOk N) (hN0 : 0 < N) (hN64 : N < 2 ^ 64) (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model N ((client N).linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG M hM hN hN0 hN64 L (Csl.Tame.reach_tso_of_wb
    (startWith_wb (counter_wb N) (derived_wb (hMw L).1) (derived_wb (hMw L).2) _) hr) hd hf

/-- **With the ticket lock, on every buffered model** (TSO and XL). -/
theorem counter_ticket_any {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 32) (L : Nat)
    {model : OModel} {Cf : OCfg} (hr : OReach model N ((client N).linkG ticketMutexG L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG_wb ticketMutexG ticketMutexG_wb (Nat.le_refl _) hN hN0 (by omega) L hr hd hf

/-- **With the spin lock and the plain-`mov` unlock, on every buffered model.** -/
theorem counter_spinMov_any {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat)
    {model : OModel} {Cf : OCfg} (hr : OReach model N ((client N).linkG spinMovG L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG_wb spinMovG spinMovG_wb (Nat.le_refl _) trivial hN0 hN L hr hd hf

/-- **With Drepper's mutex and its original unlock, on every buffered model.** -/
theorem counter_fmutexDec_any {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64) (L : Nat)
    {model : OModel} {Cf : OCfg}
    (hr : OReach model N ((client N).linkG
      (Silmaril.Proofs.X86.Concurrency.Cir.Mutex.IfaceG.ofIfaceR Futex.fmutexDec) L).toO Cf)
    (hd : Cf.Drained) (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem :=
  counter_any_mutexG_wb _ (ofIfaceR_wb fmutexDec_wb) (Nat.le_refl _) trivial hN0 hN L hr hd hf

end Counter

end Silmaril.X86.Concurrency.Story
