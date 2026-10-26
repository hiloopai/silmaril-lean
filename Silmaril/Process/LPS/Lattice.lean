module

public import Silmaril.Process.LPS.Equivalence
public import Silmaril.Compile.Category.Lattice

/-!
# The LPS process semantics in Silmaril's model lattice

The csem lattice (`Silmaril.Compile.Category.Lattice`) orders semantics of one syntax by
behaviour inclusion: `S ⊑[F] T` says that on the programs of `F` every behaviour of `S` is
one of `T`. This file puts the LPS process semantics there.

* The syntax `processSyntax`: programs are memory images; an observation is an entry draw, an
  input, and what a run from them can show: a finite trace prefix, reaching an error, or
  reaching a place where the model gives up.
* Every choice of ISA, syscall table, refusal filter and allocation limit is a point
  `procSem` of the lattice. The ISAs are `UserIsa`s: Silmaril's `RiscV.Ext` and `X86.Ext`
  (`Machines/`) and the LPS RISC-V port (branch `riscv/lps-port`).

Refinement relations proved here:

* **Readings** (`procSem_filter_mono`, `scfg_le_run`, `scfg_mono`): a stronger refusal filter
  gives fewer behaviours. In particular each `SpuriousCfg` reading refines the may-fail
  reading, and readings are monotone in `cfgLe` (LPS proves the same about `run_scfg`).
* **Tables** (`Restricts`): a table that agrees with another except on calls where it is
  `unmodeled` has fewer traces (`obsTrace_mono`), and when it never errors it has the same
  traces and its completion never errors either (`obsTrace_eq_of_errorFree`,
  `errorFree_of_restricts`); budget refusal is monotone (`budgetRefused_mono`). Hence a proof
  of an agreement statement against this translation's partial table transfers to any table
  that completes it (`agrees_transfer`), in particular to the full LPS table once the pending
  arms are translated faithfully (`Completes`).
* **Silmaril's byte-stream contract** (`Silmaril.Process.Syscall`): its events and LPS's are
  related by `cliView` and the contract table `contractSpec`; the refinement relation between
  the two process models is `procSem … specTable … ⊑[F] procSem … contractSpec …` on the
  fragment `F` of programs that use only `read` of stdin, `write` to stdout and stderr, and
  `exit` (`LPSRefinesContractOn`). It is stated, not yet proved.
* **ISAs**: `IsaRefinesOn isa₁ isa₂ F` compares two machines under one process layer, for
  instance Silmaril's RV64 model against the LPS RV64GC port on RV64IM programs.

The CLI process model of branch `process/cli-model` had no commits beyond `main` when this was
written; `cliView` is the observation map it is expected to share.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Silmaril.Compile.Category

/-! ## Step monotonicity in the refusal filter -/

section FilterMono

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {r₁ r₂ : RefusalFilter}

/-- A step allowed under a stronger filter is allowed under a weaker one. -/
theorem SStep.filter_mono (h : ∀ i m e, r₁ i m e → r₂ i m e) {c : Config isa} {evs : List Event}
    {st : StepTo isa} (s : SStep segs spec r₂ c evs st) : SStep segs spec r₁ c evs st := by
  cases s with
  | instr a b c => exact .instr a b c
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | syscall a b c d e f => exact .syscall a b c (fun x => d (h _ _ _ x)) e f
  | syscallMaterializationFault a b c d e f =>
    exact .syscallMaterializationFault a b c (fun x => d (h _ _ _ x)) e f
  | exit a b c d e => exact .exit a b c d e
  | killed a b c d => exact .killed a b c d
  | syscallUnmodeled a b c => exact .syscallUnmodeled a b c

theorem Star.filter_mono (h : ∀ i m e, r₁ i m e → r₂ i m e) {c c' : Config isa}
    {tr : List Event} (s : Star segs spec r₂ c tr c') : Star segs spec r₁ c tr c' := by
  induction s with
  | refl c => exact .refl c
  | step st _ ih => exact .step (st.filter_mono h) ih

end FilterMono

/-! ## The lattice of process semantics -/

/-- What a run from an entry draw and an input can show. -/
inductive LpsObs where
  | trace (tr : List Event)
  | error
  | unmodeled

/-- The process syntax: programs are images; observations are `(entry, input, obs)`. -/
def processSyntax : Syntax.{0} where
  Iface := Unit
  Prog := Image
  iface _ := ()
  Obs := ExecEntry × ProcInput × LpsObs

/-- The observations of one behaviour. -/
def Behavior.Shows (b : Behavior) : LpsObs → Prop
  | .trace tr => b.traces tr
  | .error => b.errors
  | .unmodeled => b.unmodeled

/-- A point of the lattice: an ISA, a syscall table, a refusal filter and an allocation
limit. Observations are taken from valid entries and valid inputs. -/
def procSem (isa : UserIsa) (spec : Sys SyscallEffect) (refused : RefusalFilter) (lim : Int) :
    processSyntax.Sem := fun img o =>
  ValidEntry img o.1 o.2.1 ∧ ValidInput o.2.1 ∧
    (runWith isa spec refused img lim o.1 o.2.1).Shows o.2.2

open Syntax in
/-- A stronger refusal filter gives fewer behaviours. -/
theorem procSem_filter_mono (isa : UserIsa) (spec : Sys SyscallEffect) {r₁ r₂ : RefusalFilter}
    (h : ∀ i m e, r₁ i m e → r₂ i m e) (lim : Int) :
    procSem isa spec r₂ lim ≤ procSem isa spec r₁ lim := by
  intro img ⟨en, inp, o⟩ ⟨he, hi, hs⟩
  refine ⟨he, hi, ?_⟩
  cases o with
  | trace tr =>
    obtain ⟨tr', c, s, pre⟩ := hs
    exact ⟨tr', c, s.filter_mono h, pre⟩
  | error =>
    obtain ⟨tr, c, evs, s, e⟩ := hs
    exact ⟨tr, c, evs, s.filter_mono h, e.filter_mono h⟩
  | unmodeled =>
    obtain ⟨tr, c, s, u⟩ := hs
    exact ⟨tr, c, s.filter_mono h, u⟩

/-- Each `SpuriousCfg` reading refines the may-fail reading (`run_scfg ⊆ run`). -/
theorem scfg_le_run (isa : UserIsa) (cfg : SpuriousCfg) (lim : Int) :
    procSem isa syscallSpec (spuriousRefusalCfg syscallSpec cfg) lim ≤
      procSem isa syscallSpec noFilter lim :=
  procSem_filter_mono isa syscallSpec (fun _ _ _ h => h.elim) lim

/-- Readings are monotone in `cfgLe`: allowing more families to fail gives more behaviours. -/
theorem scfg_mono (isa : UserIsa) {cfg₁ cfg₂ : SpuriousCfg} (le : cfgLe cfg₁ cfg₂) (lim : Int) :
    procSem isa syscallSpec (spuriousRefusalCfg syscallSpec cfg₁) lim ≤
      procSem isa syscallSpec (spuriousRefusalCfg syscallSpec cfg₂) lim := by
  refine procSem_filter_mono isa syscallSpec (fun i m e ⟨off, rest⟩ => ⟨?_, rest⟩) lim
  unfold injectedFamilyOff at off ⊢
  split at off
  · rename_i a _
    cases h₁ : familyMayFail cfg₁ a.family
    · rfl
    · simp [le a.family h₁] at off
  · exact absurd off (by decide)

/-! ## Partial tables -/

/-- `p` restricts `f`: at every input and model, `p` is `f`, or `p` only declines. This holds
between this translation's `syscallSpec` and the full LPS table (`restricts_of_completes`). -/
def Restricts (p f : Sys SyscallEffect) : Prop :=
  ∀ i m, (∀ o, p i m o ↔ f i m o) ∨ (∀ o, p i m o ↔ o = .unmodeled)

/-- A table `t` completes `specTable`: it has the same numbers, and the same specification
wherever `specTable`'s arm is translated. -/
def Completes (t : List SpecArm) : Prop :=
  ∀ n, match lookupArm specTable n, lookupArm t n with
    | some a, some a' => a.status = .translated → a.spec = a'.spec
    | none, none => True
    | _, _ => False

theorem lookupArm_mem {t : List SpecArm} {n : Nat} {a : SpecArm} (h : lookupArm t n = some a) :
    a ∈ t := by
  induction t with
  | nil => simp [lookupArm] at h
  | cons b r ih =>
    simp only [lookupArm] at h
    split at h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Every arm of `specTable` that is not translated is `unmodeled`. -/
theorem pending_spec {a : SpecArm} (mem : a ∈ specTable) (hp : a.status ≠ .translated) :
    a.spec = Sys.unmodeled :=
  absurd (beq_iff_eq.1 (List.all_eq_true.1 specTable_all_translated a mem)) hp

/-- `syscallSpec` restricts the dispatch of every table that completes `specTable`. -/
theorem restricts_of_completes {t : List SpecArm} (h : Completes t) :
    Restricts syscallSpec (dispatch t) := by
  intro i m
  have hn := h i.sysno.toNat
  unfold syscallSpec dispatch
  revert hn
  cases ha : lookupArm specTable i.sysno.toNat with
  | none =>
    cases hb : lookupArm t i.sysno.toNat with
    | none => intro _; exact .inl fun _ => Iff.rfl
    | some _ => intro hn; exact hn.elim
  | some a =>
    cases hb : lookupArm t i.sysno.toNat with
    | none => intro hn; exact hn.elim
    | some a' =>
      intro hn
      by_cases tr : a.status = .translated
      · exact .inl fun o => by simp only; rw [hn tr]
      · exact .inr fun o => by simp only; rw [pending_spec (lookupArm_mem ha) tr]; exact Iff.rfl

section Restricts

variable {isa : UserIsa} {segs : List Segment} {p f : Sys SyscallEffect}
  {rp rf : RefusalFilter}

/-- Filters that agree wherever the two tables agree, at the effects the tables answer with
(true of `noFilter`, and of `spuriousRefusalCfg _ cfg`, which reads the table only at the call it
filters). A step consults the filter only at an effect the table answers with
(`SStep.syscall`), so where the tables only decline the filters may differ. -/
def FiltersAgree (p f : Sys SyscallEffect) (rp rf : RefusalFilter) : Prop :=
  ∀ i m, (∀ o, p i m o ↔ f i m o) → ∀ e m' evs, p i m (.ok e m' evs) → (rp i m e ↔ rf i m e)

theorem filtersAgree_noFilter (p f : Sys SyscallEffect) : FiltersAgree p f noFilter noFilter :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem filtersAgree_scfg (p f : Sys SyscallEffect) (cfg : SpuriousCfg) :
    FiltersAgree p f (spuriousRefusalCfg p cfg) (spuriousRefusalCfg f cfg) := by
  intro i m same e _ _ _
  simp only [spuriousRefusalCfg, same]

theorem Restricts.ok {R : Restricts p f} {i : SyscallInput} {m : Model} {eff : SyscallEffect}
    {m' : Model} {evs : List Event} (h : p i m (.ok eff m' evs)) : f i m (.ok eff m' evs) := by
  rcases R i m with same | dec
  · exact (same _).1 h
  · cases (dec _).1 h

/-- Every successful step of the partial table is one of the full table. -/
theorem SStep.of_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf) {c c' : Config isa}
    {evs : List Event} (s : SStep segs p rp c evs (.next c')) :
    SStep segs f rf c evs (.next c') := by
  cases s with
  | instr a b c => exact .instr a b c
  | syscall a b c d e g =>
    rcases R _ _ with same | dec
    · exact .syscall a b ((same _).1 c) (fun x => d ((A _ _ same _ _ _ c).2 x)) e g
    · cases (dec _).1 c
  | exit a b c d e => exact .exit a b (Restricts.ok (R := R) c) d e
  | killed a b c d => exact .killed a b (Restricts.ok (R := R) c) d

theorem Star.of_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf) {c c' : Config isa}
    {tr : List Event} (s : Star segs p rp c tr c') : Star segs f rf c tr c' := by
  induction s with
  | refl c => exact .refl c
  | step st _ ih => exact .step (st.of_restricts R A) ih

/-- The partial table has no more traces than the full one. -/
theorem obsTrace_mono (R : Restricts p f) (A : FiltersAgree p f rp rf) {c : Config isa}
    {tr : List Event} (h : ObsTrace segs p rp c tr) : ObsTrace segs f rf c tr := by
  obtain ⟨tr', c', s, pre⟩ := h
  exact ⟨tr', c', s.of_restricts R A, pre⟩

/-- From a configuration from which the partial table never errors, a step of the full table
is one of the partial table. -/
theorem SStep.to_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf) {c c' : Config isa}
    {evs : List Event} (noErr : ¬ ReachesError segs p rp c) (s : SStep segs f rf c evs (.next c')) :
    SStep segs p rp c evs (.next c') := by
  have declines : ∀ {i m}, (∀ o, p i m o ↔ o = .unmodeled) → c.model.halted = none →
      (∃ x8, isa.svcPending c.ms = some x8 ∧ sysInput isa segs c.ms x8 = i ∧ c.model = m) →
        False := by
    rintro i m dec hh ⟨x8, hx, rfl, rfl⟩
    exact noErr ⟨[], c, [], .refl c, .syscallUnmodeled hh hx ((dec _).2 rfl)⟩
  cases s with
  | instr a b c => exact .instr a b c
  | syscall a b c d e g =>
    rcases R _ _ with same | dec
    · exact .syscall a b ((same _).2 c) (fun x => d ((A _ _ same _ _ _ ((same _).2 c)).1 x)) e g
    · exact (declines dec a ⟨_, b, rfl, rfl⟩).elim
  | exit a b c d e =>
    rcases R _ _ with same | dec
    · exact .exit a b ((same _).2 c) d e
    · exact (declines dec a ⟨_, b, rfl, rfl⟩).elim
  | killed a b c d =>
    rcases R _ _ with same | dec
    · exact .killed a b ((same _).2 c) d
    · exact (declines dec a ⟨_, b, rfl, rfl⟩).elim

theorem reachesError_of_step {c c' : Config isa} {evs : List Event}
    (s : SStep segs p rp c evs (.next c')) (h : ReachesError segs p rp c') :
    ReachesError segs p rp c := by
  obtain ⟨tr, d, e, st, err⟩ := h
  exact ⟨evs ++ tr, d, e, .step s st, err⟩

/-- When the partial table never errors, the full table reaches only configurations the
partial table reaches, along the same traces. -/
theorem Star.to_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf) {c c' : Config isa}
    {tr : List Event} (noErr : ¬ ReachesError segs p rp c) (s : Star segs f rf c tr c') :
    Star segs p rp c tr c' := by
  induction s with
  | refl c => exact .refl c
  | step st _ ih =>
    have st' := st.to_restricts R A noErr
    exact .step st' (ih fun h => noErr (reachesError_of_step st' h))

/-- An error-free partial table has exactly the traces of the full table. -/
theorem obsTrace_eq_of_errorFree (R : Restricts p f) (A : FiltersAgree p f rp rf)
    {c : Config isa} (noErr : ¬ ReachesError segs p rp c) (tr : List Event) :
    ObsTrace segs p rp c tr ↔ ObsTrace segs f rf c tr := by
  refine ⟨obsTrace_mono R A, fun ⟨tr', c', s, pre⟩ => ⟨tr', c', s.to_restricts R A noErr, pre⟩⟩

/-- When the partial table never errors, neither does the full table. -/
theorem errorFree_of_restricts (R : Restricts p f) (A : FiltersAgree p f rp rf) {c : Config isa}
    (noErr : ¬ ReachesError segs p rp c) : ¬ ReachesError segs f rf c := by
  rintro ⟨tr, d, evs, s, err⟩
  apply noErr
  refine ⟨tr, d, [], s.to_restricts R A noErr, ?_⟩
  cases err with
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | syscallMaterializationFault a b c e g k =>
    rcases R _ _ with same | dec
    · exact .syscallMaterializationFault a b ((same _).2 c)
        (fun x => e ((A _ _ same _ _ _ ((same _).2 c)).1 x)) g k
    · exact .syscallUnmodeled a b ((dec _).2 rfl)
  | syscallUnmodeled a b c =>
    rcases R _ _ with same | dec
    · exact .syscallUnmodeled a b ((same _).2 c)
    · exact .syscallUnmodeled a b ((dec _).2 rfl)

/-- Refusal for budget under the partial table is refusal under the full table. -/
theorem budgetRefusedAt_mono (R : Restricts p f) {c : Config isa}
    (h : BudgetRefusedAt isa segs p c) : BudgetRefusedAt isa segs f c := by
  obtain ⟨hh, h | ⟨x8, hx, ha | ⟨eff, m', evs, ok, hm, mat⟩⟩⟩ := h
  · exact ⟨hh, .inl h⟩
  · exact ⟨hh, .inr ⟨x8, hx, .inl ha⟩⟩
  · exact ⟨hh, .inr ⟨x8, hx, .inr ⟨eff, m', evs, Restricts.ok (R := R) ok, hm, mat⟩⟩⟩

end Restricts

/-- Refusal for budget of a run under the partial table is refusal under the full table. -/
theorem budgetRefused_mono {isa : UserIsa} {p f : Sys SyscallEffect} {rp rf : RefusalFilter}
    (R : Restricts p f) (A : FiltersAgree p f rp rf) {img : Image} {lim : Int} {en : ExecEntry}
    {inp : ProcInput} (h : RunBudgetRefusedWith isa p rp img lim en inp) :
    RunBudgetRefusedWith isa f rf img lim en inp := by
  obtain ⟨tr, c, s, b⟩ := h
  exact ⟨tr, c, s.of_restricts R A, budgetRefusedAt_mono R b⟩

/-- OSS Verify's `agrees` (`Shapes.v:123`) over an arbitrary syscall table. -/
def AgreesOver (spec : Sys SyscallEffect) (isaP isaS : UserIsa) (limPlain limSan : Int)
    (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInput inp →
    ¬ RunBudgetRefusedWith isaP spec noFilter plain limPlain enPlain inp →
    ErrorFree (runWith isaP spec noFilter plain limPlain enPlain inp) ∧
      ErrorFree (runWith isaS spec noFilter san limSan enSan inp) ∧
      TraceEquiv (runWith isaP spec noFilter plain limPlain enPlain inp).traces
        (runWith isaS spec noFilter san limSan enSan inp).traces

/-- An agreement proved against a partial table holds against every table it restricts. In
particular a proof of OSS Verify's `agrees` against this translation's `syscallSpec` is a
proof against any faithful completion of the LPS table (`restricts_of_completes`). -/
theorem agrees_transfer {p f : Sys SyscallEffect} (R : Restricts p f) {isaP isaS : UserIsa}
    {lp ls : Int} {plain san : Image} (h : AgreesOver p isaP isaS lp ls plain san) :
    AgreesOver f isaP isaS lp ls plain san := by
  intro enP enS inp vP vS vi nb
  have A := filtersAgree_noFilter p f
  obtain ⟨eP, eS, tq⟩ := h enP enS inp vP vS vi fun b => nb (budgetRefused_mono R A b)
  refine ⟨errorFree_of_restricts R A eP, errorFree_of_restricts R A eS, fun tr => ?_⟩
  exact (obsTrace_eq_of_errorFree R A eP tr).symm.trans
    ((tq tr).trans (obsTrace_eq_of_errorFree R A eS tr))

/-- OSS Verify's `agrees` is `AgreesOver syscallSpec`. -/
theorem agreesOver_syscallSpec (isaP isaS : UserIsa) (lp ls : Int) (plain san : Image) :
    AgreesOver syscallSpec isaP isaS lp ls plain san =
      strongUniversalErrorFreeTBudgets isaP isaS lp ls plain san := rfl

/-! ## Silmaril's byte-stream contract and the CLI view -/

/-- The observable bytes of a command-line process: input consumed, output produced, and how
the process ended. This is the alphabet Silmaril's `Process.Syscall` contract and LPS share
(LPS's `exitEv` also carries the final file system, which the CLI view drops). -/
inductive CliEvent where
  | input (ch : Nat) (b : Byte)
  | output (ch : Nat) (b : Byte)
  | exit (code : Nat)
  | killed (sig : Nat)
  deriving DecidableEq

/-- The CLI view of an LPS event. -/
def cliOfEvent : Event → CliEvent
  | .readEv ch b => .input ch.toNat b
  | .writeEv ch b => .output ch.toNat b
  | .exitEv code _ => .exit code.toNat
  | .killEv sig _ => .killed sig.toNat

/-- The CLI view of a `Process.Syscall` event: successful transfers become one event per
byte; errors are not observable. -/
def cliOfSyscallEvent : Silmaril.Process.Syscall.Event → List CliEvent
  | .read fd bytes => bytes.map (.input fd)
  | .write fd bytes => bytes.map (.output fd)
  | .error _ _ => []
  | .exit status => [.exit status]

/-- The CLI view of an LPS trace. -/
def cliView (tr : List Event) : List CliEvent := tr.map cliOfEvent

/-- The `exit` arm of Silmaril's contract (`Process.Syscall.Step.exit`): record `status % 256`.
It is LPS's `exit_spec`. -/
def contractExit (code : Word) : Sys SyscallEffect := exitSpec code

/-- A successful read in Silmaril's contract (`Process.Syscall.Step.readSome`): a non-empty
prefix of the remaining input, up to the count and the transfer cap. -/
def contractReadSome (m : Model) (buf count : Word) : Sys SyscallEffect := do
  let bs ← Sys.choose fun bs : List Byte =>
    1 ≤ bs.length ∧ bs.length ≤ count.toNat ∧ bs.length ≤ MAX_RW_COUNT.toNat ∧
      (m.stdin.take bs.length).1 = bs
  Sys.modify (·.withStdin (m.stdin.take bs.length).2)
  Sys.emit (bs.map (.readEv 0))
  Sys.pure (mkEffect (lenWord bs) [(buf, bs)] [])

/-- A failed read in Silmaril's contract (`Process.Syscall.Step.readError`): any errno, after
consuming up to `count` input bytes unobservably and clobbering the buffer. -/
def contractReadError (m : Model) (buf count : Word) : Sys SyscallEffect := do
  let e ← Sys.choose fun e : Int => 1 ≤ e ∧ e ≤ 4095
  let consumed ← Sys.choose fun k : Nat => k ≤ count.toNat ∧ (m.stdin.take k).1.length = k
  let junk ← Sys.choose fun junk : List Byte => junk.length = count.toNat
  Sys.modify (·.withStdin (m.stdin.take consumed).2)
  Sys.pure (mkEffect (errnoRet e) [(buf, junk)] [])

/-- The `read` arm of Silmaril's contract on stdin (`Process.Syscall.Step.readSome`,
`readEof`, `readZero`, `readError`, `readBadDescriptor`, `readBadAddress`). -/
def contractRead (fd buf count : Word) : Sys SyscallEffect := do
  let i ← Sys.input
  let m ← Sys.getModel
  if fd ≠ 0 then errRet EBADF
  else if (readBytesMap i.wmem buf count).isNone then errRet EFAULT
  else if count = 0 ∨ m.stdin.atEof then retOnly 0
  else Sys.alt (contractReadSome m buf count) (contractReadError m buf count)

/-- A successful write in Silmaril's contract (`Process.Syscall.Step.writeSome`): any prefix
of the source bytes, up to the count and the transfer cap. -/
def contractWriteSome (fd count : Word) (bytes : List Byte) : Sys SyscallEffect := do
  let n ← Sys.choose fun n : Nat => n ≤ count.toNat ∧ n ≤ MAX_RW_COUNT.toNat
  Sys.emit ((bytes.take n).map (.writeEv fd))
  retOnly (zw n)

/-- A failed write in Silmaril's contract (`Process.Syscall.Step.writeError`): any errno. -/
def contractWriteError : Sys SyscallEffect := do
  let e ← Sys.choose fun e : Int => 1 ≤ e ∧ e ≤ 4095
  errRet e

/-- The `write` arm of Silmaril's contract on stdout and stderr. -/
def contractWrite (fd buf count : Word) : Sys SyscallEffect := do
  let i ← Sys.input
  if fd ≠ 1 ∧ fd ≠ 2 then errRet EBADF
  else match readBytesMap i.mem buf count with
    | none => errRet EFAULT
    | some bytes => Sys.alt (contractWriteSome fd count bytes) contractWriteError

/-- Silmaril's byte-stream contract as an LPS syscall table: `read`, `write`, `exit` and
`exit_group`; every other call declines. -/
def contractSpec : Sys SyscallEffect :=
  dispatch
    [ arm 63 "read" fun i => contractRead (fd32 (i.arg 0)) (i.arg 1) (i.arg 2),
      arm 64 "write" fun i => contractWrite (fd32 (i.arg 0)) (i.arg 1) (i.arg 2),
      arm 93 "exit" fun i => contractExit (i.arg 0),
      arm 94 "exit_group" fun i => contractExit (i.arg 0) ]

/-- The refinement relation between the two process models: on the programs of `F`, every
behaviour LPS admits is one Silmaril's contract admits. The intended `F` is the programs that
call only `read` on stdin, `write` on stdout or stderr, and `exit`, with buffers inside
mapped memory. Not yet proved. -/
def LPSRefinesContractOn (isa : UserIsa) (F : Set Image) : Prop :=
  Syntax.RefinesOn F (procSem isa syscallSpec noFilter sourceAllocLimit)
    (procSem isa contractSpec noFilter sourceAllocLimit)

/-- The ISA relation: on the programs of `F`, under one process layer, `isa₁` shows no
behaviour `isa₂` does not (for example Silmaril's `RiscV.Ext` against the LPS RV64GC port, on
RV64IM programs). -/
def IsaRefinesOn (isa₁ isa₂ : UserIsa) (F : Set Image) : Prop :=
  Syntax.RefinesOn F (procSem isa₁ syscallSpec noFilter sourceAllocLimit)
    (procSem isa₂ syscallSpec noFilter sourceAllocLimit)

/-- The exit arms of the two models coincide. -/
theorem contractExit_eq (code : Word) : contractExit code = exitSpec code := rfl

end Silmaril.Process.LPS
