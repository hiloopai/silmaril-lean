module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Tv

/-!
# Translation validation x86 → CIR: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Tv.lean`).

* `tvRun_sound`: **trace refinement per thread.** If `tvRun t c = some K`, then for every value
  domain whose values are below `2^32` (needed only if the thread reads memory), every trace the extractor gives for the thread's bytes
  is a run of the CIR thread `c.body` over the same domain: its memory actions, up to `normActs`
  (an unlocked read-modify-write is a load then a store), are the lowered actions of the run,
  and its final registers equal the run's outside the clobber set `K`.
* `threadUnits_normActs`: `normActs` does not change the access units the axiomatic models
  read, so the refinement is exact at the level of candidate executions.
* `TvTest.refines`: **refinement per test.** For a test whose certificates check (`tvOk`) and
  whose domain fits (`domOk`), every x86 behaviour (`AxReach` over the traces of the bytes,
  under any model) is a CIR behaviour (`BehavIn`) over the same domain with the same witness
  value.
* `TvTest.forbidden_transfer` / `TvTest.allowed_transfer`: a `forbidden` CIR verdict holds for
  the bytes; an `allowed` x86 verdict is an `allowed` CIR verdict.
* `tvRun_xrun`, `tvRun_xrun_vals`: **run-level soundness, for any values
  read.** Every symbolic run (`TvCfg.XRun`: one branch of `stepSym` per step, whatever value each
  read returns, so in particular every real run by `Bridge.xrun_of_a9run`) of an accepted
  thread from its initial core to the end of the code is a run of `c.body` over any domain that
  holds the values read (`actVals`), with the same actions up to `normActs` and the same final
  registers outside `K`. No `2 ^ 32` bound: an 8-byte read may return any 64-bit value.
  `tvRun_reach`: the cores such a run reaches sit at instructions `chk1` accepted.
* `chk1_sound_vals`: **one instruction, for any read value**, the step form of
  the above (`chk1_sound` without its `2 ^ 32` bound on the domain). It needs the run-level form of
  `chk1`: an 8-byte load, `xchg` or `xadd` takes its destination out of the fitting set `Z`, and
  an 8-byte `cmpxchg` takes `rax` out (an earlier checker added it, which is unsound for values
  `≥ 2 ^ 32`: `q_load_unfit`).
* `walk_sound`, `axReach_pick`, `cond_eval_congr`, `witness_atoms` (exported for the
  marked-thread checker): the walk from any related state, and refinement of `AxReach` by a
  per-thread choice of traces with the same access units.
* `TvTest.transfer_of_allOk`: the passing Boolean check `TvTest.allOk` gives `TvTest.Transfer`:
  refinement, the recorded verdicts for the CIR program under SC, TSO and XL, a nonempty SC
  outcome set, and the `forbidden` verdicts transferred to the bytes.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv

open Silmaril.X86 (State)
open Silmaril.X86.Litmus (Trace extract)
open Silmaril.X86.MemoryModel.Litmus (XTrace XAct AxReach Verdict Model threadUnits)

/-- **Translation validation is sound** (trace refinement per thread). -/
theorem tvRun_sound {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {dom : List Nat} (hdom : c.reads = true → ∀ v ∈ dom, v < 2 ^ 32) {fuel : Nat}
    {trs : List Trace} (hx : extract t dom fuel = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom c.body Regs.zero, normActs tr.acts = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → tr.final.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.tvRun_sound h hdom hx

open Silmaril.X86.Concurrency.Cir.TvCfg (XRun) in
/-- **Translation validation is sound for runs, for any read values**. -/
theorem tvRun_xrun {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (he : s'.rip = t.endRip)
    {D : List Nat}
    (hD : ∀ acts ∈ acc, ∀ a ∈ acts, a.ev.kind.reads = true → Silmaril.X86.Ext.leValue a.rd ∈ D) :
    ∃ p ∈ run D c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → s'.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.tvRun_xrun h hx he hD

open Silmaril.X86.Concurrency.Cir.TvCfg (XRun) in
/-- `tvRun_xrun` over the values the run read. -/
theorem tvRun_xrun_vals {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (he : s'.rip = t.endRip) :
    ∃ p ∈ run (actVals acc) c.body Regs.zero, normActs acc.flatten = p.1.flatMap Lab.acts ∧
      ∀ r, r ∉ K → s'.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.tvRun_xrun_vals h hx he

open Silmaril.X86.Concurrency.Cir.TvCfg (XRun) in
/-- The cores a symbolic run of an accepted thread reaches, before the end of the code, sit at
instructions `chk1` accepted. -/
theorem tvRun_reach {t : XThread} {c : Cert} {K : List Reg} (h : tvRun t c = some K)
    {acc : List (List XAct)} {s' : State} (hx : XRun t t.init acc s') (hne : s'.rip ≠ t.endRip) :
    ∃ o i n K₁ Z₁ ops K₂ Z₂, s'.rip = t.base + BitVec.ofNat 64 o ∧ o < t.code.length ∧
      fetchAt t o = some (i, n) ∧
      chk1 K₁ Z₁ (t.base + BitVec.ofNat 64 (o + n)) i ops = some (K₂, Z₂) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.tvRun_reach h hx hne

/-- **One instruction is sound for any read value**: every branch of the symbolic
step is a run of the item's statements over any domain `D` holding the values the branch reads,
and the relation `Rel` is kept. -/
theorem chk1_sound_vals {t : XThread} {dom D : List Nat}
    {K Z K' Z' : List Reg} {i : Silmaril.X86.Atomic9.Instr} {ops : List Stmt}
    {nx : Silmaril.X86.Word} (hc : chk1 K Z nx i ops = some (K', Z')) {s : State} {n : Nat}
    (hf : t.fetch s = some (i, n)) (hnx : s.rip + BitVec.ofNat 64 n = nx)
    {rs : Regs} (hrel : Rel K Z rs s) {outs : List (List XAct × State)}
    (hs : Silmaril.X86.Litmus.stepSym t dom s = some outs) {o : List XAct × State}
    (ho : o ∈ outs)
    (hD : ∀ a ∈ o.1, a.ev.kind.reads = true → Silmaril.X86.Ext.leValue a.rd ∈ D) :
    ∃ p ∈ run D (chain ops) rs, p.1.flatMap Lab.acts = normActs o.1 ∧ Rel K' Z' p.2 o.2 ∧
      o.2.rip = s.rip + BitVec.ofNat 64 n := by
  obtain ⟨rs', ⟨p, hp, hpa, hpr⟩, hrel', hrip⟩ :=
    Silmaril.Proofs.X86.Concurrency.Cir.Tv.chk1_sound_vals hc hf hnx hrel hs ho hD
  exact ⟨p, hp, hpa, hpr ▸ hrel', hrip⟩

/-- An 8-byte load can return a value `≥ 2 ^ 32`: its branch admits no relation
with the destination in the fitting set. -/
theorem q_load_unfit : ∃ outs, Silmaril.X86.Litmus.stepSym RunEx.qLoad [2 ^ 32] RunEx.qLoad.init = some outs ∧
    ∃ o ∈ outs, ∀ K Z rs, ¬ Rel K (.rax :: Z) rs o.2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.q_load_unfit

/-- `chk1` takes an 8-byte load's destination out of the fitting set. -/
theorem q_load_chk1 : ((RunEx.qLoad.fetch RunEx.qLoad.init).bind fun p =>
    chk1 [] [.rax] (RunEx.qLoad.init.rip + BitVec.ofNat 64 p.2) p.1
      [.load .rax .rlx 8 .wb (.lit 0x10000)]) = some ([], []) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.q_load_chk1

/-- A 32-bit `lock cmpxchg` on `rax` after an 8-byte load into it is refused. -/
theorem qCas_rejected : tvRun RunEx.qCas (RunEx.casCert 8 8) = none :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.qCas_rejected

/-- After a 4-byte load it is accepted. -/
theorem dCas_accepted : tvRun RunEx.dCas (RunEx.casCert 7 4) = some [] :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.dCas_accepted

/-- The cmpxchg of `qCas` passes `chk1` exactly when `rax` is in the fitting set:
an earlier checker put `rax` there after the 8-byte load, the current checker does not. -/
theorem qCas_cas_fit :
    ((fetchAt RunEx.qCas 8).bind fun p => chk1 [] [.rax] (RunEx.qCas.base + BitVec.ofNat 64 (8 + p.2))
      p.1 [.rmw .rax .rlx 4 (.cas (.reg .rax)) (.lit 0x10008) (.reg .rcx)]) = some ([], [.rax]) ∧
    ((fetchAt RunEx.qCas 8).bind fun p => chk1 [] [] (RunEx.qCas.base + BitVec.ofNat 64 (8 + p.2))
      p.1 [.rmw .rax .rlx 4 (.cas (.reg .rax)) (.lit 0x10008) (.reg .rcx)]) = none :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.qCas_cas_fit

open Silmaril.X86.Concurrency.Cir.TvCfg (XRun) in
/-- **The certificate an earlier checker accepted is unsound**: a symbolic run of
`qCas` reading `2 ^ 32` then `0` ends with a register no run of `casCert 8 8` over `[2 ^ 32, 0]`
matches. So `tvRun_xrun` fails for any checker accepting `(qCas, casCert 8 8)`. -/
theorem qCas_cert_unsound : ∃ acc s', XRun RunEx.qCas RunEx.qCas.init acc s' ∧
    s'.rip = RunEx.qCas.endRip ∧
    (∀ acts ∈ acc, ∀ a ∈ acts, a.ev.kind.reads = true →
      Silmaril.X86.Ext.leValue a.rd ∈ [2 ^ 32, 0]) ∧
    ¬ ∃ p ∈ run [2 ^ 32, 0] (RunEx.casCert 8 8).body Regs.zero,
      normActs acc.flatten = p.1.flatMap Lab.acts ∧ ∀ r, r ∉ ([] : List Reg) → s'.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.qCas_cert_unsound

/-- `normActs` is invisible to the access units. -/
theorem threadUnits_normActs (i p : Nat) (as : List XAct) :
    threadUnits i p (normActs as) = threadUnits i p as :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.threadUnits_normActs i p as

/-- **Refinement of a validated test.** -/
theorem TvTest.refines {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : AxReach c.test T M f) :
    ∃ f', BehavIn c.prog c.test.domain M f' ∧ c.test.witness.eval f' = c.test.witness.eval f :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.TvTest.refines h hd hT hf

/-- A `forbidden` CIR verdict holds for the bytes. -/
theorem TvTest.forbidden_transfer {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    (hc : Verdict.forbidden.Holds c.test (BehavIn c.prog c.test.domain M)) :
    Verdict.forbidden.Holds c.test (AxReach c.test T M) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.TvTest.forbidden_transfer h hd hT hc

/-- An `allowed` x86 verdict is an `allowed` CIR verdict. -/
theorem TvTest.allowed_transfer {c : TvTest} (h : c.tvOk = true) (hd : c.domOk = true)
    {T : List (List XTrace)} (hT : c.test.traces = some T)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop}
    (hc : Verdict.allowed.Holds c.test (AxReach c.test T M)) :
    Verdict.allowed.Holds c.test (BehavIn c.prog c.test.domain M) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.TvTest.allowed_transfer h hd hT hc

/-- **A passing `allOk` gives everything** (`TvTest.Transfer`). -/
theorem TvTest.transfer_of_allOk {c : TvTest} (h : c.allOk = true) : c.Transfer :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.TvTest.transfer_of_allOk h

/-- **The walk is sound** from any state related to the CIR registers (`Rel`), at the start of
the code (it is used for the segments between marker calls). -/
theorem walk_sound {t : XThread} {dom : List Nat} (hlen : t.code.length < 2 ^ 64)
    {its : List Item} (hdom : its.any (fun it => it.ops.any Stmt.reads) = true → ∀ v ∈ dom, v < 2 ^ 32)
    {K Z Kf : List Reg} (hw : walk t K Z 0 its = some Kf) {fuel : Nat} {s : State} {rs : Regs}
    (hrip : s.rip = t.base) (hrel : Rel K Z rs s) {trs : List Trace}
    (hx : Silmaril.X86.Litmus.explore t dom fuel s = some trs) :
    ∀ tr ∈ trs, ∃ p ∈ run dom (chain (its.flatMap Item.ops)) rs,
      p.1.flatMap Lab.acts = normActs tr.acts ∧ ∀ r, r ∉ Kf → tr.final.read r = p.2 r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.walk_sound_run hlen hdom hw hrip hrel hx

/-- **Refinement by per-thread choice**: if every trace of thread `k` in `T` has a trace in
`U` with the same access units and the same final registers outside `Ks[k]`, every `AxReach`
final state over `T` is one over `U` with the same memory and registers outside the `Ks`. -/
theorem axReach_pick {t : Silmaril.X86.MemoryModel.Litmus.Test} {T U : List (List XTrace)}
    {Ks : List (List Reg)} (hl : T.length = U.length)
    (h : ∀ k (h₁ : k < T.length) (h₂ : k < U.length), ∀ a ∈ T[k], ∃ b ∈ U[k],
      threadUnits k 0 a.acts = threadUnits k 0 b.acts ∧
        ∀ r, r ∉ Ks.getD k [] → a.final.read r = b.final.read r)
    {M : Silmaril.X86.MemoryModel.Axiomatic.Exec → Prop} {f : Silmaril.X86.MemoryModel.Litmus.Final}
    (hf : AxReach t T M f) :
    ∃ f', AxReach t U M f' ∧ f'.mem = f.mem ∧ ∀ i r, r ∉ Ks.getD i [] → f'.regs i r = f.regs i r :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.axReach_pick hl h hf

/-- A condition only depends on the values of its atoms. -/
theorem cond_eval_congr {f f' : Silmaril.X86.MemoryModel.Litmus.Final} (p : Silmaril.X86.MemoryModel.Litmus.Cond)
    (h : ∀ a ∈ p.atoms, a.eval f = a.eval f') : p.eval f = p.eval f' :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.cond_eval_congr p h

/-- The witness has the condition's atoms. -/
theorem witness_atoms (t : Silmaril.X86.MemoryModel.Litmus.Test) : t.witness.atoms = t.cond.atoms :=
  Silmaril.Proofs.X86.Concurrency.Cir.Tv.witness_atoms t

end Silmaril.X86.Concurrency.Cir.Tv
