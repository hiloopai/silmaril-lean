module

public import Silmaril.Process.LPS.Run

/-!
# LPS in Lean: equivalence, error freedom, budgets and halting

Translation of the statement definitions of LPS `EquivalenceDefinition/` (upstream commit
`f1006fe8`): `Equivalence.v`, `MustExit.v` and `HaltsAllowed.v`.

LPS states each statement inside a section over a source and a target image, for its one ISA.
Here every statement takes **two** ISAs, one for the source and one for the target. LPS's
statements are the instances with the same ISA twice; the same definitions also state
cross-ISA agreement (an RV64 build against an x86-64 build of one program), which LPS cannot.

LPS writes one definition for each combination of reading (plain run or a `SpuriousCfg`),
budget premise, input restriction and conclusion. They are generated here from four
ingredients (`Reading`, `ValidInputWith`, the budget premise and the conclusion), and each
LPS name is a definition, so that `Shapes.lean` can prove its shapes equal to them by `rfl`.

* `equiv`: the source's every execution errors (vacuity escape), or the trace sets are equal
  and the target never errors;
* `strong_equiv`: the source is fully modelled, and `equiv`;
* `strong_equiv_error_free`: neither errors, and the trace sets are equal;
* `_abort`: `abort()` is the terminal SIGABRT death; `error_free_unkilled` also forbids it;
* `_budgets`: inputs on which the source is refused for budget are excluded.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `Equivalence.v:101` `trace_equiv`. -/
def TraceEquiv (T₁ T₂ : List Event → Prop) : Prop := ∀ tr, T₁ tr ↔ T₂ tr

/-- LPS `Equivalence.v:122` `equiv`. -/
def BehEquiv (source target : Behavior) : Prop :=
  source.allErrors ∨ (TraceEquiv source.traces target.traces ∧ ¬ target.errors)

/-- LPS `Equivalence.v:193` `modeled`. -/
def Modeled (b : Behavior) : Prop := ¬ b.unmodeled
/-- LPS `Equivalence.v:215` `error_free`. -/
def ErrorFree (b : Behavior) : Prop := ¬ b.errors
/-- LPS `Equivalence.v:233` `dies_by_signal`. -/
def DiesBySignal (b : Behavior) : Prop := ∃ tr sig fs, b.traces tr ∧ Event.killEv sig fs ∈ tr
/-- LPS `Equivalence.v:264` `error_free_unkilled`. -/
def ErrorFreeUnkilled (b : Behavior) : Prop := ErrorFree b ∧ ¬ DiesBySignal b

/-- How a statement reads the environment: every injected failure is possible (`none`, LPS
`run`), or only those a `SpuriousCfg` allows (LPS `run_scfg`). -/
abbrev Reading := Option SpuriousCfg

/-- The behaviour of an image under a reading. -/
def runIn (isa : UserIsa) : Reading → Image → Int → ExecEntry → ProcInput → Behavior
  | none => run isa
  | some cfg => runScfg isa cfg

/-- Refusal for budget under a reading (LPS `run_budget_refused`, `run_scfg_budget_refused`). -/
def BudgetRefusedIn (isa : UserIsa) : Reading → Image → Int → ExecEntry → ProcInput → Prop
  | none => RunBudgetRefused isa
  | some cfg => RunScfgBudgetRefused isa cfg

/-! ## The conclusions -/

section Conclusions

variable (isaS isaT : UserIsa) (r : Reading) (limS limT : Int) (S T : Image)

/-- LPS `Equivalence.v:714` `strong_equiv` (and its `_scfg`, `_budgets` forms). -/
def StrongEquiv (enS enT : ExecEntry) (inp : ProcInput) : Prop :=
  Modeled (runIn isaS r S limS enS inp) ∧
    BehEquiv (runIn isaS r S limS enS inp) (runIn isaT r T limT enT inp)

/-- LPS `Equivalence.v:776` `strong_equiv_error_free` (and its forms). -/
def StrongEquivErrorFree (enS enT : ExecEntry) (inp : ProcInput) : Prop :=
  ErrorFree (runIn isaS r S limS enS inp) ∧ ErrorFree (runIn isaT r T limT enT inp) ∧
    TraceEquiv (runIn isaS r S limS enS inp).traces (runIn isaT r T limT enT inp).traces

/-- LPS `Equivalence.v:967` `strong_equiv_error_free_abort` (and its forms). -/
def StrongEquivErrorFreeAbort (enS enT : ExecEntry) (inp : ProcInput) : Prop :=
  ErrorFreeUnkilled (runIn isaS r S limS enS inp) ∧
    ErrorFreeUnkilled (runIn isaT r T limT enT inp) ∧
    TraceEquiv (runIn isaS r S limS enS inp).traces (runIn isaT r T limT enT inp).traces

/-- The universal statement: for every independent entry draw of the two binaries and every
valid input, the conclusion holds. -/
def Universal (valid : ProcInput → Prop) (concl : ExecEntry → ExecEntry → ProcInput → Prop) :
    Prop :=
  ∀ enS enT inp, ValidEntry S enS inp → ValidEntry T enT inp → valid inp → concl enS enT inp

/-- The universal statement with the budget premise: inputs on which the source is refused for
budget (under the reading) are excluded. The premise is on the source only. -/
def UniversalBudgets (valid : ProcInput → Prop)
    (concl : ExecEntry → ExecEntry → ProcInput → Prop) : Prop :=
  ∀ enS enT inp, ValidEntry S enS inp → ValidEntry T enT inp → valid inp →
    ¬ BudgetRefusedIn isaS r S limS enS inp → concl enS enT inp

end Conclusions

/-! ## The LPS statement names

`strong_universal_T`, `strong_universal_error_free_T` and their `_abort`, `_either`, `_sv39`,
`_sv57`, `_va_any`, `_hwcap_*`, `_scfg`, `_budgets` and `_cfg` forms. -/

section Names

variable (isaS isaT : UserIsa)

/-- LPS `Equivalence.v:733` `strong_universal_T`. -/
def strongUniversalT (S T : Image) : Prop :=
  Universal S T ValidInput
    (StrongEquiv isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:807` `strong_universal_error_free_T`. -/
def strongUniversalErrorFreeT (S T : Image) : Prop :=
  Universal S T ValidInput
    (StrongEquivErrorFree isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:913` `strong_universal_T_abort`. -/
def strongUniversalTAbort (S T : Image) : Prop :=
  Universal S T ValidInputAbort
    (StrongEquiv isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:925` `strong_universal_T_either`. -/
def strongUniversalTEither (S T : Image) : Prop :=
  Universal S T ValidInputEither
    (StrongEquiv isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:975` `strong_universal_error_free_T_abort`. -/
def strongUniversalErrorFreeTAbort (S T : Image) : Prop :=
  Universal S T ValidInputAbort
    (StrongEquivErrorFreeAbort isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1017` `strong_universal_error_free_T_either`. -/
def strongUniversalErrorFreeTEither (S T : Image) : Prop :=
  strongUniversalErrorFreeT isaS isaT S T ∧ strongUniversalErrorFreeTAbort isaS isaT S T

/-- LPS `Equivalence.v:1170` `strong_equiv_va`. -/
def StrongEquivVa (S T : Image) (enS enT : ExecEntry) (inp : ProcInput) : Prop :=
  inp.vaSize = .sv48 ∧ StrongEquiv isaS isaT none sourceAllocLimit targetAllocLimit S T enS enT inp
/-- LPS `Equivalence.v:1181` `strong_universal_T_sv39`: refused (false) for a runnable image,
since the specifications compare against the Sv48 `TASK_SIZE`. -/
def strongUniversalTSv39 (S T : Image) : Prop :=
  Universal S T ValidInputSv39 (StrongEquivVa isaS isaT S T)
/-- LPS `Equivalence.v:1188` `strong_universal_T_sv57`. -/
def strongUniversalTSv57 (S T : Image) : Prop :=
  Universal S T ValidInputSv57 (StrongEquivVa isaS isaT S T)
/-- LPS `Equivalence.v:1199` `strong_universal_T_va_any`. -/
def strongUniversalTVaAny (S T : Image) : Prop :=
  Universal S T ValidInputVaAny (StrongEquivVa isaS isaT S T)

/-- LPS `Equivalence.v:1349` `strong_universal_T_hwcap_rv64gc`. -/
def strongUniversalTHwcapRv64gc (S T : Image) : Prop :=
  Universal S T ValidInputHwcapRv64gc
    (StrongEquiv isaS isaT none sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1366` `strong_universal_error_free_T_hwcap_rv64gc`. -/
def strongUniversalErrorFreeTHwcapRv64gc (S T : Image) : Prop :=
  Universal S T ValidInputHwcapRv64gc
    (StrongEquivErrorFree isaS isaT none sourceAllocLimit targetAllocLimit S T)

/-- LPS `Equivalence.v:1554` `strong_universal_T_scfg`. -/
def strongUniversalTScfg (cfg : SpuriousCfg) (S T : Image) : Prop :=
  Universal S T ValidInput
    (StrongEquiv isaS isaT (some cfg) sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1569` `strong_universal_error_free_T_scfg`. -/
def strongUniversalErrorFreeTScfg (cfg : SpuriousCfg) (S T : Image) : Prop :=
  Universal S T ValidInput
    (StrongEquivErrorFree isaS isaT (some cfg) sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1626` `strong_universal_T_scfg_abort`. -/
def strongUniversalTScfgAbort (cfg : SpuriousCfg) (S T : Image) : Prop :=
  Universal S T ValidInputAbort
    (StrongEquiv isaS isaT (some cfg) sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1687` `strong_universal_error_free_T_scfg_abort`. -/
def strongUniversalErrorFreeTScfgAbort (cfg : SpuriousCfg) (S T : Image) : Prop :=
  Universal S T ValidInputAbort
    (StrongEquivErrorFreeAbort isaS isaT (some cfg) sourceAllocLimit targetAllocLimit S T)
/-- LPS `Equivalence.v:1898` `strong_universal_error_free_T_cfg`. -/
def strongUniversalErrorFreeTCfg (allocMayFail : Bool) (S T : Image) : Prop :=
  strongUniversalErrorFreeTScfg isaS isaT (allocOnlyCfg allocMayFail) S T

/-- LPS `Equivalence.v:2160` `source_within_budget`. -/
def SourceWithinBudget (limS : Int) (S : Image) (enS : ExecEntry) (inp : ProcInput) : Prop :=
  ¬ RunBudgetRefused isaS S limS enS inp

/-- LPS `Equivalence.v:2193` `strong_universal_T_budgets`. -/
def strongUniversalTBudgets (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInput (StrongEquiv isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:2201` `strong_universal_T_budgets_abort`. -/
def strongUniversalTBudgetsAbort (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInputAbort (StrongEquiv isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:2209` `strong_universal_error_free_T_budgets`: the agreement statement
OSS Verify calls `agrees`. -/
def strongUniversalErrorFreeTBudgets (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInput (StrongEquivErrorFree isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:2217` `strong_universal_error_free_T_budgets_abort`. -/
def strongUniversalErrorFreeTBudgetsAbort (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInputAbort
    (StrongEquivErrorFreeAbort isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:2333` `strong_universal_error_free_T_budgets_hwcap_rv64gc`. -/
def strongUniversalErrorFreeTBudgetsHwcapRv64gc (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInputHwcapRv64gc
    (StrongEquivErrorFree isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:2366` `strong_universal_error_free_T_budgets_abort_hwcap_rv64gc`. -/
def strongUniversalErrorFreeTBudgetsAbortHwcapRv64gc (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS none limS S T ValidInputAbortHwcapRv64gc
    (StrongEquivErrorFreeAbort isaS isaT none limS limT S T)
/-- LPS `Equivalence.v:3177` `strong_universal_error_free_T_budgets_either`. -/
def strongUniversalErrorFreeTBudgetsEither (limS limT : Int) (S T : Image) : Prop :=
  strongUniversalErrorFreeTBudgets isaS isaT limS limT S T ∧
    strongUniversalErrorFreeTBudgetsAbort isaS isaT limS limT S T

/-- LPS `Equivalence.v:2584` `source_within_budget_scfg`. -/
def SourceWithinBudgetScfg (cfg : SpuriousCfg) (limS : Int) (S : Image) (enS : ExecEntry)
    (inp : ProcInput) : Prop :=
  ¬ RunScfgBudgetRefused isaS cfg S limS enS inp

/-- LPS `Equivalence.v:2613` `strong_universal_T_scfg_budgets`. -/
def strongUniversalTScfgBudgets (cfg : SpuriousCfg) (limS limT : Int) (S T : Image) : Prop :=
  UniversalBudgets isaS (some cfg) limS S T ValidInput
    (StrongEquiv isaS isaT (some cfg) limS limT S T)
/-- LPS `Equivalence.v:2621` `strong_universal_error_free_T_scfg_budgets`: OSS Verify's
`agrees_in`. -/
def strongUniversalErrorFreeTScfgBudgets (cfg : SpuriousCfg) (limS limT : Int) (S T : Image) :
    Prop :=
  UniversalBudgets isaS (some cfg) limS S T ValidInput
    (StrongEquivErrorFree isaS isaT (some cfg) limS limT S T)
/-- LPS `Equivalence.v:2708` `strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc`. -/
def strongUniversalErrorFreeTScfgBudgetsHwcapRv64gc (cfg : SpuriousCfg) (limS limT : Int)
    (S T : Image) : Prop :=
  UniversalBudgets isaS (some cfg) limS S T ValidInputHwcapRv64gc
    (StrongEquivErrorFree isaS isaT (some cfg) limS limT S T)
/-- LPS `Equivalence.v:2814` `strong_universal_error_free_T_scfg_budgets_abort`. -/
def strongUniversalErrorFreeTScfgBudgetsAbort (cfg : SpuriousCfg) (limS limT : Int)
    (S T : Image) : Prop :=
  UniversalBudgets isaS (some cfg) limS S T ValidInputAbort
    (StrongEquivErrorFreeAbort isaS isaT (some cfg) limS limT S T)
/-- LPS `Equivalence.v:2908` `strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc`. -/
def strongUniversalErrorFreeTScfgBudgetsAbortHwcapRv64gc (cfg : SpuriousCfg) (limS limT : Int)
    (S T : Image) : Prop :=
  UniversalBudgets isaS (some cfg) limS S T ValidInputAbortHwcapRv64gc
    (StrongEquivErrorFreeAbort isaS isaT (some cfg) limS limT S T)

end Names

/-! ### The may-fail reading is the plain run (LPS `Run.v:1938`, `Equivalence.v:3011-3038`) -/

/-- Under `may_fail_cfg` no family is switched off, so the refusal filter excludes nothing. -/
theorem spuriousRefusalCfg_mayFail (spec : Sys SyscallEffect) :
    spuriousRefusalCfg spec mayFailCfg = noFilter := by
  funext i m eff
  apply propext
  simp only [spuriousRefusalCfg, noFilter, iff_false, not_and]
  intro h
  unfold injectedFamilyOff at h
  split at h
  · rename_i a _
    revert h
    generalize a.family = fam
    cases fam <;> simp [familyMayFail, mayFailCfg]
  · simp at h

/-- LPS `Run.v:1947` `run_scfg_may_fail` (here an equality, not a `behavior_equiv`). -/
theorem runScfg_mayFail (isa : UserIsa) : runScfg isa mayFailCfg = run isa := by
  funext img lim en inp
  simp only [runScfg, run, spuriousRefusalCfg_mayFail]

/-- LPS `Equivalence.v:2982` `source_within_budget_scfg_may_fail` (here an equality). -/
theorem runScfgBudgetRefused_mayFail (isa : UserIsa) :
    RunScfgBudgetRefused isa mayFailCfg = RunBudgetRefused isa := by
  funext img lim en inp
  simp only [RunScfgBudgetRefused, RunBudgetRefused, spuriousRefusalCfg_mayFail]

/-- LPS `Equivalence.v:3027` `strong_universal_error_free_T_scfg_budgets_may_fail`. -/
theorem strongUniversalErrorFreeTScfgBudgets_mayFail (isaS isaT : UserIsa) (limS limT : Int)
    (S T : Image) :
    strongUniversalErrorFreeTScfgBudgets isaS isaT mayFailCfg limS limT S T ↔
      strongUniversalErrorFreeTBudgets isaS isaT limS limT S T := by
  simp only [strongUniversalErrorFreeTScfgBudgets, strongUniversalErrorFreeTBudgets,
    UniversalBudgets, StrongEquivErrorFree, BudgetRefusedIn, runIn, runScfg_mayFail,
    runScfgBudgetRefused_mayFail]


/-! ## Budgets (LPS `Equivalence.v:3243-3340`) -/

/-- LPS `Equivalence.v:3243` `asan_fixed_overhead`. -/
def asanFixedOverhead : Int := 261 * 1048576
/-- LPS `Equivalence.v:3252` `sanitizer_source_limit`: 2 GiB. -/
def sanitizerSourceLimit : Int := 0x80000000
/-- LPS `Equivalence.v:3257` `budget_headroom_ok`. -/
def budgetHeadroomOk (limS limT : Int) : Bool :=
  decide (pageSize ≤ limS) && decide (9 * limS + 8 * asanFixedOverhead ≤ 8 * limT)

/-- LPS `Equivalence.v:3308` `BUDGETS`. -/
structure Budgets where
  limSource : Int
  limTarget : Int
  headroom : budgetHeadroomOk limSource limTarget = true

/-- LPS `Equivalence.v:3315` `ShippedBudgets`: 16 GiB and 512 GiB. -/
def shippedBudgets : Budgets := ⟨sourceAllocLimit, targetAllocLimit, by decide⟩
/-- LPS `Equivalence.v:3335` `SanitizerBudgets`: 2 GiB and 512 GiB. -/
def sanitizerBudgets : Budgets := ⟨sanitizerSourceLimit, targetAllocLimit, by decide⟩

/-! ## Images (LPS `Equivalence.v:436-556`, `oss-verify-proofs/theories/Images.v`) -/

/-- LPS `Equivalence.v:496` `image_phdrs_readable`. -/
def imagePhdrsReadable (segs : List Segment) (ph : PhdrInfo) : Bool :=
  decide (0 < ph.num) && decide (0 < ph.ent) &&
    (memoryRead segs (zw ph.addr) (ph.num * ph.ent)).isSome

/-- LPS `Equivalence.v:551` `image_brk_witness`. -/
def imageBrkWitness (segs : List Segment) : Int :=
  pageSize * ((reservedTop (segmentsReserved segs) + (pageSize - 1)) / pageSize)

/-- LPS `Equivalence.v:555` `image_brk_satisfiable`. -/
def imageBrkSatisfiable (segs : List Segment) : Bool := decide (imageBrkWitness segs < 2 ^ 64)

/-- `oss-verify-proofs/theories/Images.v:21` `image_wf`: the anti-vacuity check on an image
(the entry point fetches, the program headers are readable, a valid break exists). The entry
check is the ISA's. -/
def ImageWf (isa : UserIsa) (i : Image) : Prop :=
  isa.entryFetchable i.segments i.initPc = true ∧ imagePhdrsReadable i.segments i.phdrs = true ∧
    imageBrkSatisfiable i.segments = true

/-! ### The break check is satisfiable (LPS `Equivalence.v:558-655`) -/

/-- LPS `Equivalence.v:558` `reserved_top_nonneg`. -/
theorem reservedTop_nonneg (maps : List (Word × Word)) : 0 ≤ reservedTop maps := by
  induction maps with
  | nil => exact le_rfl
  | cons p r ih =>
    obtain ⟨a, sz⟩ := p
    simp only [reservedTop]
    exact le_max_of_le_right ih

/-- LPS `Equivalence.v:569` `image_brk_witness_bounds`: the witness is page aligned, at or above
`reserved_top`, and less than a page above it. -/
theorem imageBrkWitness_bounds (segs : List Segment) :
    (reservedTop (segmentsReserved segs) ≤ imageBrkWitness segs ∧
      imageBrkWitness segs < reservedTop (segmentsReserved segs) + pageSize) ∧
    imageBrkWitness segs % pageSize = 0 := by
  unfold imageBrkWitness pageSize
  generalize reservedTop (segmentsReserved segs) = rt
  omega

/-- LPS `Equivalence.v:590` `image_brk_satisfiable_sound`: a `true` verdict yields a valid
break. -/
theorem imageBrkSatisfiable_sound (segs : List Segment) (h : imageBrkSatisfiable segs = true) :
    ∃ brk, ValidBrk segs brk := by
  have hlt : imageBrkWitness segs < 2 ^ 64 := of_decide_eq_true h
  obtain ⟨⟨hlo, hhi⟩, hmod⟩ := imageBrkWitness_bounds segs
  have h0 := reservedTop_nonneg (segmentsReserved segs)
  refine ⟨zw (imageBrkWitness segs), ?_⟩
  unfold ValidBrk
  rw [uns_zw (by omega) hlt]
  unfold brkAslrMax pageSize at *
  omega

/-- LPS `Equivalence.v:650` `image_brk_satisfiable_bites`: an image whose reservations reach
the top of the address space fails the check. -/
theorem imageBrkSatisfiable_bites (segs : List Segment)
    (htop : 2 ^ 64 ≤ reservedTop (segmentsReserved segs)) : imageBrkSatisfiable segs = false := by
  obtain ⟨⟨hlo, -⟩, -⟩ := imageBrkWitness_bounds segs
  unfold imageBrkSatisfiable
  exact decide_eq_false (by omega)

/-- LPS `Run.v:2580` `entry_stack_span_max`: the largest entry block `valid_argv` and
`valid_envp` allow. -/
def entryStackSpanMax : Int := 2238671

/-- LPS `Run.v:2582` `total_arg_bytes_nonneg`. -/
theorem totalArgBytes_nonneg (args : List (List Byte)) : 0 ≤ totalArgBytes args := by
  induction args with
  | nil => exact le_rfl
  | cons a r ih => simp only [totalArgBytes, List.foldr_cons] at ih ⊢; omega

/-- LPS `Run.v:2590` `entry_stack_span_bound`. -/
theorem entryStackSpan_bound {argv envp : List (List Byte)} (ha : ValidArgv argv)
    (he : ValidEnvp envp) :
    0 ≤ entryStackSpan argv envp ∧ entryStackSpan argv envp ≤ entryStackSpanMax := by
  obtain ⟨-, hla, hta, -⟩ := ha
  obtain ⟨hle, hte, -⟩ := he
  have := totalArgBytes_nonneg argv
  have := totalArgBytes_nonneg envp
  unfold entryStackSpan entryStackSpanMax auxvSize
  omega

/-- The entry `image_brk_satisfiable_entry` exhibits: the bottom of the declared size's stack
window, the witness break, the top of its mmap-base window, and a zero draw. -/
def witnessEntry (v : VaSize) (brk : Word) : ExecEntry :=
  ⟨zw (vaSpWindowLo v), brk, zw (vaMmapBaseMax v), ⟨0, fun _ => 0⟩⟩

/-- LPS `Equivalence.v:1138` `image_brk_satisfiable_entry_va`: on every input the shared
clauses accept, under every declared address-space size, an image passing the break check has
a valid entry. -/
theorem imageBrkSatisfiable_entry_va (img : Image) {inp : ProcInput} (hv : ValidInputVaAny inp)
    (h : imageBrkSatisfiable img.segments = true) : ∃ en, ValidEntry img en inp := by
  obtain ⟨⟨hargv, henvp, -⟩, -⟩ := hv
  obtain ⟨brk, hbrk⟩ := imageBrkSatisfiable_sound _ h
  obtain ⟨-, hspan⟩ := entryStackSpan_bound hargv henvp
  refine ⟨witnessEntry inp.vaSize brk, ?_⟩
  unfold ValidEntry ValidEntryVa ValidSpVa ValidMmapBaseVa EntryStackFitsVa witnessEntry
  unfold entryStackSpanMax at hspan
  refine ⟨?_, hbrk, ?_, ?_⟩ <;>
  · cases inp.vaSize <;>
    · simp only [vaSpWindowLo, vaSpWindowHi, vaMmapBaseMax, vaMmapBaseMin, vaStackTop,
        sv39TaskSize, spWindowHi, mmapBaseMin, pageSize]
      rw [uns_zw (by decide) (by decide)]
      omega

/-- LPS `Equivalence.v:612` `image_brk_satisfiable_entry`: a valid input and an image passing
the break check have a valid entry, so the entry quantifier of every statement is inhabited. -/
theorem imageBrkSatisfiable_entry (img : Image) (inp : ProcInput) (hv : ValidInput inp)
    (h : imageBrkSatisfiable img.segments = true) : ∃ en, ValidEntry img en inp := by
  obtain ⟨hcore, hhw, habort, -⟩ := hv
  exact imageBrkSatisfiable_entry_va img ⟨hcore, hhw, habort, trivial⟩ h

/-- An image satisfying `image_wf` has a valid entry on every valid input (the use
`Shapes.v:465-467` makes of `image_brk_satisfiable_entry`). -/
theorem ImageWf.entry {isa : UserIsa} {img : Image} (hwf : ImageWf isa img) {inp : ProcInput}
    (hv : ValidInput inp) : ∃ en, ValidEntry img en inp :=
  imageBrkSatisfiable_entry img inp hv hwf.2.2

/-! ## Must-exit (LPS `MustExit.v`) -/

section MustExit

variable {isa : UserIsa} (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)

/-- LPS `MustExit.v:929` `must_exit_in_at` (and `must_exit_in_at_cfg`, `MustExit.v:1275`):
every execution exits normally with a status in `S`, never errors and never stalls. With
`S = [code]` this is `must_exit_at` (`MustExit.v:233`). -/
inductive MustExitInAt (S : List Word) : Config isa → Prop where
  | halted {c code} : c.model.halted = some code → code ∈ S → c.model.killedBy = none →
      MustExitInAt S c
  | running {c} : c.model.halted = none → (∃ evs st, SStep segs spec refused c evs st) →
      (∀ evs, ¬ SStep segs spec refused c evs .error) →
      (∀ evs c', SStep segs spec refused c evs (.next c') → MustExitInAt S c') →
      MustExitInAt S c

/-- LPS `MustExit.v:697` `decided_from`: every reachable syscall has a decided refusal. -/
def DecidedFrom (cfg : SpuriousCfg) (c : Config isa) : Prop :=
  ∀ tr c' x8, Star segs spec noFilter c tr c' → isa.svcPending c'.ms = some x8 →
    RefusalDecided spec cfg (sysInput isa segs c'.ms x8) c'.model

end MustExit

/-! ### Must-exit facts (LPS `MustExit.v:152-1424`, `Run.v:1618-1700`) -/

section MustExitFacts

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- LPS `MustExit.v:152` `sstep_not_halted`. -/
theorem SStep.not_halted {c : Config isa} {evs : List Event} {st : StepTo isa}
    (h : SStep segs spec refused c evs st) : c.model.halted = none := by
  cases h <;> assumption

/-- LPS `Run.v:1674` `sstep_cfg_sub`: a filtered step is a plain step. -/
theorem SStep.toNoFilter {c : Config isa} {evs : List Event} {st : StepTo isa}
    (h : SStep segs spec refused c evs st) : SStep segs spec noFilter c evs st := by
  cases h with
  | instr a b c => exact .instr a b c
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | syscall a b c _ e f => exact .syscall a b c id e f
  | syscallMaterializationFault a b c _ e f => exact .syscallMaterializationFault a b c id e f
  | exit a b c d e => exact .exit a b c d e
  | killed a b c d => exact .killed a b c d
  | syscallUnmodeled a b c => exact .syscallUnmodeled a b c

/-- LPS `Run.v:1786` `star_cfg_sub`. -/
theorem Star.toNoFilter {c c' : Config isa} {tr : List Event}
    (h : Star segs spec refused c tr c') : Star segs spec noFilter c tr c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs.toNoFilter ih

/-- LPS `Run.v:1721` `sstep_cfg_progress`: where the plain run can step, the run under a
reading's filter can step too. A filtered outcome is a refusal at a call where the spec also
admits a non-refusal outcome, and that outcome steps. LPS uses the same third conjunct of
`spurious_refusal_cfg` for the alternative step; its `refusal_decided` premise (`Run.v:1558`)
only chooses which of the two cases applies, which is not decidable constructively. Here that
choice is a classical case split (`by_cases`, i.e. excluded middle), so the premise is dropped
and the lemma is strictly stronger. -/
theorem SStep.progress_scfg (cfg : SpuriousCfg) {c : Config isa} {evs : List Event}
    {st : StepTo isa} (h : SStep segs spec noFilter c evs st) :
    ∃ evs' st', SStep segs spec (spuriousRefusalCfg spec cfg) c evs' st' := by
  have alt : ∀ {ms model x8 eff model' evs},
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      ∃ evs' st', SStep segs spec (spuriousRefusalCfg spec cfg) ⟨ms, model⟩ evs' st' := by
    intro ms model x8 eff model' evs hh hsvc hspec
    have step_of : ∀ {eff model' evs},
        spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
        ¬ spuriousRefusalCfg spec cfg (sysInput isa segs ms x8) model eff →
        ∃ evs' st', SStep segs spec (spuriousRefusalCfg spec cfg) ⟨ms, model⟩ evs' st' := by
      intro eff model' evs hspec hnr
      cases hm : model'.halted with
      | none =>
        cases hmat : materializeModelAccesses model' (syscallEffectAccesses eff) with
        | none => exact ⟨_, _, .syscallMaterializationFault hh hsvc hspec hnr hm hmat⟩
        | some model'' => exact ⟨_, _, .syscall hh hsvc hspec hnr hm hmat⟩
      | some code =>
        cases hk : model'.killedBy with
        | none => exact ⟨_, _, .exit hh hsvc hspec hm hk⟩
        | some sig => exact ⟨_, _, .killed hh hsvc hspec hk⟩
    by_cases hr : spuriousRefusalCfg spec cfg (sysInput isa segs ms x8) model eff
    · obtain ⟨-, -, eff', m', evs', hspec', hnr'⟩ := hr
      exact step_of hspec' fun ⟨_, hr', _⟩ => by rw [hnr'] at hr'; cases hr'
    · exact step_of hspec hr
  cases h with
  | instr a b c => exact ⟨_, _, .instr a b c⟩
  | instrFault a b c => exact ⟨_, _, .instrFault a b c⟩
  | instrUnmodeled a b c => exact ⟨_, _, .instrUnmodeled a b c⟩
  | syscall a b c => exact alt a b c
  | syscallMaterializationFault a b c => exact alt a b c
  | exit a b c d e => exact ⟨_, _, .exit a b c d e⟩
  | killed a b c d => exact ⟨_, _, .killed a b c d⟩
  | syscallUnmodeled a b c => exact ⟨_, _, .syscallUnmodeled a b c⟩

/-- LPS `MustExit.v:972` `must_exit_in_at_no_error`. -/
theorem MustExitInAt.no_error {S : List Word} {c : Config isa}
    (h : MustExitInAt segs spec refused S c) : ¬ ReachesError segs spec refused c := by
  rintro ⟨tr, c', evs, hs, he⟩
  induction hs with
  | refl =>
    cases h with
    | halted hh => rw [he.not_halted] at hh; cases hh
    | running _ _ hno => exact hno _ he
  | step hss _ ih =>
    cases h with
    | halted hh => rw [hss.not_halted] at hh; cases hh
    | running _ _ _ hnext => exact ih (hnext _ _ hss) he

/-- LPS `MustExit.v:336` `must_exit_at_exclusive` (and `MustExit.v:608`
`must_exit_at_cfg_exclusive`): a run cannot be bound to exit with two codes. -/
theorem MustExitInAt.exclusive {a b : Word} {c : Config isa}
    (h₁ : MustExitInAt segs spec refused [a] c) (h₂ : MustExitInAt segs spec refused [b] c) :
    a = b := by
  induction h₁ with
  | halted hh hmem =>
    cases h₂ with
    | halted hh' hmem' =>
      rw [hh] at hh'
      cases hh'
      simp only [List.mem_singleton] at hmem hmem'
      exact hmem.symm.trans hmem'
    | running hn => rw [hh] at hn; cases hn
  | running hn hprog hno _ ih =>
    cases h₂ with
    | halted hh' => rw [hn] at hh'; cases hh'
    | running _ _ _ hnext =>
      obtain ⟨evs, st, hs⟩ := hprog
      cases st with
      | error => exact absurd hs (hno evs)
      | next c' => exact ih evs c' hs (hnext evs c' hs)

/-- LPS `MustExit.v:718` `must_exit_at_cfg_mono` at the may-fail end
(`must_exit_at_cfg_of_must_exit_at`, `MustExit.v:740`): a plain verdict is a verdict under any
reading. Every filtered step is a plain step, and progress survives the filter
(`SStep.progress_scfg`). -/
theorem MustExitInAt.scfg_of_plain (cfg : SpuriousCfg) {S : List Word} {c : Config isa}
    (h : MustExitInAt segs spec noFilter S c) :
    MustExitInAt segs spec (spuriousRefusalCfg spec cfg) S c := by
  induction h with
  | halted hh hmem hk => exact .halted hh hmem hk
  | running hn hprog hno _ ih =>
    obtain ⟨evs, st, hs⟩ := hprog
    exact .running hn (hs.progress_scfg cfg) (fun evs he => hno evs he.toNoFilter)
      fun evs c' hs' => ih evs c' hs'.toNoFilter

end MustExitFacts

section MustExitNames

variable (isa : UserIsa)

/-- The reading's syscall-outcome filter. -/
def readingFilter : Reading → RefusalFilter
  | none => noFilter
  | some cfg => spuriousRefusalCfg syscallSpec cfg

/-- LPS `MustExit.v:946` `must_exit_in` and `MustExit.v:1290` `must_exit_in_scfg`. -/
def MustExitIn (r : Reading) (S : List Word) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  MustExitInAt img.segments syscallSpec (readingFilter r) S (initConfig isa img en lim inp)

/-- LPS `MustExit.v:261` `must_exit_with` and `MustExit.v:760` `must_exit_with_scfg`. -/
def MustExitWith (r : Reading) (code : Word) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  MustExitIn isa r [code] img lim en inp

/-- LPS `MustExit.v:857` `run_decided`. -/
def RunDecided (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Prop :=
  DecidedFrom img.segments syscallSpec cfg (initConfig isa img en lim inp)

/-- LPS `MustExit.v:1384` `run_reaches_killed_cfg` (and `run_reaches_killed`). -/
def RunReachesKilled (r : Reading) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Prop :=
  ∃ tr c' sig,
    Star img.segments syscallSpec (readingFilter r) (initConfig isa img en lim inp) tr c' ∧
    c'.model.killedBy = some sig

/-- LPS `MustExit.v:297` `must_exit_with_no_error` and `MustExit.v:792`
`must_exit_with_scfg_no_error` (for the set form, `MustExit.v:986` and `MustExit.v:1322`). -/
theorem MustExitIn.errorFree {r : Reading} {S : List Word} {img : Image} {lim : Int}
    {en : ExecEntry} {inp : ProcInput} (h : MustExitIn isa r S img lim en inp) :
    ErrorFree (runIn isa r img lim en inp) := by
  cases r <;> exact MustExitInAt.no_error h

/-- LPS `MustExit.v:349` `must_exit_with_exclusive` and `MustExit.v:808`
`must_exit_with_scfg_exclusive`. -/
theorem MustExitWith.exclusive {r : Reading} {a b : Word} {img : Image} {lim : Int}
    {en : ExecEntry} {inp : ProcInput} (ha : MustExitWith isa r a img lim en inp)
    (hb : MustExitWith isa r b img lim en inp) : a = b :=
  MustExitInAt.exclusive ha hb

/-- LPS `MustExit.v:875` `must_exit_with_scfg_of_must_exit_with`: a plain verdict is a verdict
under every reading. LPS takes `run_decided cfg` as a premise; it is not needed here because
`SStep.progress_scfg` discharges the refusal question by classical case analysis. -/
theorem MustExitIn.scfg_of_plain (cfg : SpuriousCfg) {S : List Word} {img : Image} {lim : Int}
    {en : ExecEntry} {inp : ProcInput} (h : MustExitIn isa none S img lim en inp) :
    MustExitIn isa (some cfg) S img lim en inp :=
  MustExitInAt.scfg_of_plain cfg h

/-! ## Halting (LPS `HaltsAllowed.v`) -/

/-- LPS `HaltsAllowed.v:109` `halts_allowed_T` (source budget, plain reading). -/
def haltsAllowedT (S : List Word) (img : Image) : Prop :=
  ∀ en inp, ValidEntry img en inp → ValidInput inp →
    MustExitIn isa none S img sourceAllocLimit en inp

/-- LPS `HaltsAllowed.v:125` `halts_allowed_T_scfg`. -/
def haltsAllowedTScfg (cfg : SpuriousCfg) (S : List Word) (img : Image) : Prop :=
  ∀ en inp, ValidEntry img en inp → ValidInput inp →
    MustExitIn isa (some cfg) S img sourceAllocLimit en inp

/-- LPS `HaltsAllowed.v:153` `halts_allowed_T_scfg_budgets`. -/
def haltsAllowedTScfgBudgets (cfg : SpuriousCfg) (lim : Int) (S : List Word) (img : Image) :
    Prop :=
  ∀ en inp, ValidEntry img en inp → ValidInput inp →
    SourceWithinBudgetScfg isa cfg lim img en inp → MustExitIn isa (some cfg) S img lim en inp

end MustExitNames

/-- LPS `HaltsAllowed.v:338` `status_allowed`. -/
def statusAllowed (S : List Word) (code : Word) : Bool := S.any (· == code)

/-- LPS `HaltsAllowed.v:366` `byte_codes`: every exit status `0 … 255` (`AnyExit.codes`). -/
def byteCodes : List Word := (List.range 256).map fun n => zw n

end Silmaril.Process.LPS
