module

public import Silmaril.Process.LPS.Classifier

/-!
# OSS Verify's statement shapes, in Lean

Translation of `theories/Shapes.v` (`OssFuzzTheorems.Core.Shapes`) of
`theorem-labs/oss-verify-proofs` at commit `98e995d4daced70a0a4aa2c810854b88720735f1`
(release `v2026.10.0`, Theorem Labs, MIT licence; SHA-256 of the file
`82b996cbc454c87866c42e4047864730f03f1a54add5d4ec60d15d852b137d7c`, byte-identical to the
file at the historical pin `8f5f46768858af236a4270f9628e6beed9aa0e72`, see
`docs/LPSShapesParity.md`), over LPS
(`rocq-linux-process-semantics` at `f1006fe8`). Every OSS Verify statement is one of these
shapes applied to the memory images of one harness's builds. Each agreement and halting shape,
and the two classifier shapes, is written out in full and proved equal by `rfl` to the LPS
definition it stands for (the `*_is_lps` lemmas of `Shapes.v`), so a reader audits the
shapes, not 20,000 statements. The other input-set shapes (`disagrees_at_most`,
`agreement_decidable` and their `_rv64gc` forms) are built from LPS definitions only, as in
`Shapes.v`.

Every definition and lemma of the pinned `Shapes.v` is here, in its order (`Shapes.v:52-493`):
the parameters, the seven agreement shapes, `agrees_iff_agrees_in_may_fail`, the two halting
shapes and their monotonicity, the eight input-set shapes, monotonicity, and the four
classifier-to-claim lemmas. `disagrees_at_most_of_classifier` takes `image_wf C`, exactly as
upstream: the valid entry it needs comes from `Equivalence.image_brk_satisfiable_entry`
(`imageBrkSatisfiable_entry`, translated in `Equivalence.lean`).

**ISA.** The agreement and halting shapes take the ISA of each build as parameters, and the
classifier shapes the ISA the classifier runs on. OSS Verify's statements are the instances at
one ISA (riscv64, through the LPS RISC-V port or `Machines.RiscV`); `agrees isaRv isaX86` is
the cross-ISA agreement statement OSS Verify cannot state, and `agrees isaX86 isaX86` the
x86-64 analogue of a published statement. The input sets are LPS's (`valid_input` admits
exactly the two RISC-V `AT_HWCAP` values `hwcapRv64gc` and `hwcapRv64gcv`); the `_rv64gc`
shapes restrict `AT_HWCAP` to the RV64GC value whatever the ISA, as upstream does.

**Rationals.** `Shapes.v` works in Rocq's `Q`, whose equality is `Qeq`; Lean's `ℚ` is
normalised, so `Qeq` is `=` and the `Qeq` transport lemmas of `Measure.v` are not needed.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Shapes

open Silmaril.Process.LPS

/-- `Shapes.v:57` `Budgets.Standard`. -/
def Budgets.standard : Budgets := shippedBudgets
/-- `Shapes.v:61` `Budgets.Asan`. -/
def Budgets.asan : Budgets := sanitizerBudgets

theorem standard_budgets :
    Budgets.standard.limSource = 0x400000000 ∧ Budgets.standard.limTarget = 0x8000000000 :=
  ⟨rfl, rfl⟩
theorem asan_budgets :
    Budgets.asan.limSource = 0x80000000 ∧ Budgets.asan.limTarget = 0x8000000000 := ⟨rfl, rfl⟩

/-- `Shapes.v:76` `Env.may_fail`: every family may fail without cause. -/
def Env.mayFail : SpuriousCfg := mayFailCfg
/-- `Shapes.v:79` `Env.alloc_forced_only`: allocation fails only when forced. -/
def Env.allocForcedOnly : SpuriousCfg := allocOnlyCfg false
/-- `Shapes.v:81` `Env.forced_only`: nothing fails without cause. -/
def Env.forcedOnly : SpuriousCfg := forcedOnlyCfg

theorem may_fail_is : Env.mayFail = ⟨true, true, true, true, true, true⟩ := rfl
theorem alloc_forced_only_is : Env.allocForcedOnly = ⟨false, true, true, true, true, true⟩ := rfl
theorem forced_only_is : Env.forcedOnly = ⟨false, false, false, false, false, false⟩ := rfl

/-- `Shapes.v:98` `Exits.any`. -/
def Exits.any : List Word := byteCodes
/-- `Shapes.v:107` `Exits.ok_or_refused`. -/
def Exits.okOrRefused : List Word := [0, 2]

section Agreement

variable (isaP isaS : UserIsa)

/-- `Shapes.v:123` `agrees`: on every valid input on which the plain build is not refused for
budget, both builds are error free and have the same traces. -/
def agrees (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInput inp →
    ¬ RunBudgetRefused isaP plain limPlain enPlain inp →
    ErrorFree (run isaP plain limPlain enPlain inp) ∧ ErrorFree (run isaS san limSan enSan inp) ∧
      TraceEquiv (run isaP plain limPlain enPlain inp).traces (run isaS san limSan enSan inp).traces

theorem agrees_is_lps (lp ls : Int) (p s : Image) :
    agrees isaP isaS lp ls p s = strongUniversalErrorFreeTBudgets isaP isaS lp ls p s := rfl

/-- `Shapes.v:143` `agrees_in`: `agrees` under an environment reading. -/
def agreesIn (env : SpuriousCfg) (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInput inp →
    ¬ RunScfgBudgetRefused isaP env plain limPlain enPlain inp →
    ErrorFree (runScfg isaP env plain limPlain enPlain inp) ∧
      ErrorFree (runScfg isaS env san limSan enSan inp) ∧
      TraceEquiv (runScfg isaP env plain limPlain enPlain inp).traces
        (runScfg isaS env san limSan enSan inp).traces

theorem agreesIn_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agreesIn isaP isaS env lp ls p s =
      strongUniversalErrorFreeTScfgBudgets isaP isaS env lp ls p s := rfl

/-- `Shapes.v:161` `agrees_iff_agrees_in_may_fail`: `agrees` is `agrees_in Env.may_fail`, from
LPS `strong_universal_error_free_T_scfg_budgets_may_fail`. -/
theorem agrees_iff_agreesIn_mayFail (lp ls : Int) (p s : Image) :
    agrees isaP isaS lp ls p s ↔ agreesIn isaP isaS Env.mayFail lp ls p s := by
  rw [agrees_is_lps, agreesIn_is_lps]
  exact (strongUniversalErrorFreeTScfgBudgets_mayFail isaP isaS lp ls p s).symm

/-- `Shapes.v:174` `agrees_abort_modelled`: `abort()` is a SIGABRT death, which the conclusion
forbids. -/
def agreesAbortModelled (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInputAbort inp →
    ¬ RunBudgetRefused isaP plain limPlain enPlain inp →
    ErrorFreeUnkilled (run isaP plain limPlain enPlain inp) ∧
      ErrorFreeUnkilled (run isaS san limSan enSan inp) ∧
      TraceEquiv (run isaP plain limPlain enPlain inp).traces (run isaS san limSan enSan inp).traces

theorem agreesAbortModelled_is_lps (lp ls : Int) (p s : Image) :
    agreesAbortModelled isaP isaS lp ls p s =
      strongUniversalErrorFreeTBudgetsAbort isaP isaS lp ls p s := rfl

/-- `Shapes.v:189` `agrees_in_abort_modelled`. -/
def agreesInAbortModelled (env : SpuriousCfg) (limPlain limSan : Int) (plain san : Image) :
    Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInputAbort inp →
    ¬ RunScfgBudgetRefused isaP env plain limPlain enPlain inp →
    ErrorFreeUnkilled (runScfg isaP env plain limPlain enPlain inp) ∧
      ErrorFreeUnkilled (runScfg isaS env san limSan enSan inp) ∧
      TraceEquiv (runScfg isaP env plain limPlain enPlain inp).traces
        (runScfg isaS env san limSan enSan inp).traces

theorem agreesInAbortModelled_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agreesInAbortModelled isaP isaS env lp ls p s =
      strongUniversalErrorFreeTScfgBudgetsAbort isaP isaS env lp ls p s := rfl

/-- `Shapes.v:214` `agrees_rv64gc`: inputs that advertise no vector extension. -/
def agreesRv64gc (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInputHwcapRv64gc inp →
    ¬ RunBudgetRefused isaP plain limPlain enPlain inp →
    ErrorFree (run isaP plain limPlain enPlain inp) ∧ ErrorFree (run isaS san limSan enSan inp) ∧
      TraceEquiv (run isaP plain limPlain enPlain inp).traces (run isaS san limSan enSan inp).traces

theorem agreesRv64gc_is_lps (lp ls : Int) (p s : Image) :
    agreesRv64gc isaP isaS lp ls p s =
      strongUniversalErrorFreeTBudgetsHwcapRv64gc isaP isaS lp ls p s := rfl

/-- `Shapes.v:229` `agrees_abort_modelled_rv64gc`. -/
def agreesAbortModelledRv64gc (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInputAbortHwcapRv64gc inp →
    ¬ RunBudgetRefused isaP plain limPlain enPlain inp →
    ErrorFreeUnkilled (run isaP plain limPlain enPlain inp) ∧
      ErrorFreeUnkilled (run isaS san limSan enSan inp) ∧
      TraceEquiv (run isaP plain limPlain enPlain inp).traces (run isaS san limSan enSan inp).traces

theorem agreesAbortModelledRv64gc_is_lps (lp ls : Int) (p s : Image) :
    agreesAbortModelledRv64gc isaP isaS lp ls p s =
      strongUniversalErrorFreeTBudgetsAbortHwcapRv64gc isaP isaS lp ls p s := rfl

/-- `Shapes.v:245` `agrees_in_rv64gc`. -/
def agreesInRv64gc (env : SpuriousCfg) (limPlain limSan : Int) (plain san : Image) : Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    ValidEntry plain enPlain inp → ValidEntry san enSan inp → ValidInputHwcapRv64gc inp →
    ¬ RunScfgBudgetRefused isaP env plain limPlain enPlain inp →
    ErrorFree (runScfg isaP env plain limPlain enPlain inp) ∧
      ErrorFree (runScfg isaS env san limSan enSan inp) ∧
      TraceEquiv (runScfg isaP env plain limPlain enPlain inp).traces
        (runScfg isaS env san limSan enSan inp).traces

theorem agreesInRv64gc_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agreesInRv64gc isaP isaS env lp ls p s =
      strongUniversalErrorFreeTScfgBudgetsHwcapRv64gc isaP isaS env lp ls p s := rfl

end Agreement

section Halting

variable (isa : UserIsa)

/-- `Shapes.v:274` `halts_within_budget`: every execution exits with an allowed status, in
the forced-only reading, on inputs within budget. -/
def haltsWithinBudget (lim : Int) (allowed : List Word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), ValidEntry img en inp → ValidInput inp →
    ¬ RunScfgBudgetRefused isa forcedOnlyCfg img lim en inp →
    MustExitIn isa (some forcedOnlyCfg) allowed img lim en inp

theorem haltsWithinBudget_is_lps (lim : Int) (allowed : List Word) (img : Image) :
    haltsWithinBudget isa lim allowed img =
      haltsAllowedTScfgBudgets isa forcedOnlyCfg lim allowed img :=
  rfl

/-- `Shapes.v:291` `halts_may_fail`: every execution exits with an allowed status even when
every family may fail without cause, at the 16 GiB source budget. -/
def haltsMayFail (allowed : List Word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), ValidEntry img en inp → ValidInput inp →
    MustExitIn isa (some mayFailCfg) allowed img sourceAllocLimit en inp

theorem haltsMayFail_is_lps (allowed : List Word) (img : Image) :
    haltsMayFail isa allowed img = haltsAllowedTScfg isa mayFailCfg allowed img := rfl

/-- LPS `MustExit.v:1424` `must_exit_in_scfg_mono_set` (for every reading): a larger exit set
is weaker. -/
theorem mustExitInAt_mono {segs : List Segment} {spec : Sys SyscallEffect} {refused : RefusalFilter}
    {S₁ S₂ : List Word} (sub : S₁ ⊆ S₂) {c : Config isa} (h : MustExitInAt segs spec refused S₁ c) :
    MustExitInAt segs spec refused S₂ c := by
  induction h with
  | halted halted mem unkilled => exact .halted halted (sub mem) unkilled
  | running halted progress noError _ ih => exact .running halted progress noError ih

/-- LPS `HaltsAllowed.v:218` `halts_allowed_T_scfg_mono_set`. -/
theorem haltsAllowedTScfg_mono_set {cfg : SpuriousCfg} {S₁ S₂ : List Word} {img : Image}
    (sub : S₁ ⊆ S₂) (h : haltsAllowedTScfg isa cfg S₁ img) : haltsAllowedTScfg isa cfg S₂ img :=
  fun en inp he hi => mustExitInAt_mono isa sub (h en inp he hi)

/-- `Shapes.v:302` `halts_within_budget_mono`: a larger exit set is weaker. -/
theorem haltsWithinBudget_mono {lim : Int} {S₁ S₂ : List Word} {img : Image} (sub : S₁ ⊆ S₂)
    (h : haltsWithinBudget isa lim S₁ img) : haltsWithinBudget isa lim S₂ img :=
  fun en inp he hi hb => mustExitInAt_mono isa sub (h en inp he hi hb)

/-- `Shapes.v:310` `halts_may_fail_mono`, through `halts_allowed_T_scfg_mono_set` as
upstream. -/
theorem haltsMayFail_mono {S₁ S₂ : List Word} {img : Image} (sub : S₁ ⊆ S₂)
    (h : haltsMayFail isa S₁ img) : haltsMayFail isa S₂ img := by
  rw [haltsMayFail_is_lps] at *
  exact haltsAllowedTScfg_mono_set isa sub h

end Halting

section Classification

variable (isa : UserIsa)

/-- `Shapes.v:337` `disagrees_at_most`: the valid inputs on which the builds disagree weigh at
most `b · M`. Built from LPS pieces and trusted as written (no LPS counterpart). -/
def disagreesAtMost (env : SpuriousCfg) (w : FinProcInput → ℚ) (M : ℚ) (plain san : Image)
    (b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup →
    (∀ f ∈ l, ValidFinInput f ∧ ¬ GoodInputS isa env plain san f.toProcInput) →
    sumWeights w l ≤ b * M

/-- `Shapes.v:350` `classifies`: the RV64 program `C` exits 0 exactly on the inputs where the
builds agree, and 1 otherwise. -/
def classifies (env : SpuriousCfg) (plain san C : Image) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → ∀ en : ExecEntry, ValidEntry C en f.toProcInput →
    (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ↔
      GoodInputS isa env plain san f.toProcInput) ∧
    (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ∨
      MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en f.toProcInput)

theorem classifies_is_lps (env : SpuriousCfg) (plain san C : Image) :
    classifies isa env plain san C = ClassifiesGoodInputsTS isa env plain san C := rfl

/-- `Shapes.v:371` `classifier_rejects_at_most`. -/
def classifierRejectsAtMost (C : Image) (w : FinProcInput → ℚ) (M b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup → (∀ f ∈ l, RejectsFo isa C f) →
    sumWeights w l ≤ b * M

theorem classifierRejectsAtMost_is_lps (C : Image) (w : FinProcInput → ℚ) (M b : ℚ) :
    classifierRejectsAtMost isa C w M b = WeightBoundTFo isa C w M b := rfl

/-- `Shapes.v:384` `agreement_decidable`: some well-formed program classifies the inputs.
Trusted as written (no LPS counterpart). -/
def agreementDecidable (env : SpuriousCfg) (plain san : Image) : Prop :=
  ∃ C : Image, ImageWf isa C ∧ classifies isa env plain san C

/-- `Shapes.v:390` `disagrees_at_most_rv64gc`. -/
def disagreesAtMostRv64gc (env : SpuriousCfg) (w : FinProcInput → ℚ) (M : ℚ) (plain san : Image)
    (b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup →
    (∀ f ∈ l, ValidFinInput f ∧ f.toProcInput.hwcap = hwcapRv64gc ∧
      ¬ GoodInputS isa env plain san f.toProcInput) →
    sumWeights w l ≤ b * M

/-- `Shapes.v:400` `classifies_rv64gc`. -/
def classifiesRv64gc (env : SpuriousCfg) (plain san C : Image) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → f.toProcInput.hwcap = hwcapRv64gc →
    ∀ en : ExecEntry, ValidEntry C en f.toProcInput →
      (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en
          f.toProcInput ↔ GoodInputS isa env plain san f.toProcInput) ∧
      (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en
          f.toProcInput ∨
        MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en f.toProcInput)

theorem classifiesRv64gc_is_lps (env : SpuriousCfg) (plain san C : Image) :
    classifiesRv64gc isa env plain san C = ClassifiesGoodInputsTSHwcapRv64gc isa env plain san C :=
  rfl

/-- `Shapes.v:418` `agreement_decidable_rv64gc`. -/
def agreementDecidableRv64gc (env : SpuriousCfg) (plain san : Image) : Prop :=
  ∃ C : Image, ImageWf isa C ∧ classifiesRv64gc isa env plain san C

/-- `Shapes.v:422` `classifies_rv64gc_of_classifies`. -/
theorem classifiesRv64gc_of_classifies {env : SpuriousCfg} {plain san C : Image}
    (h : classifies isa env plain san C) : classifiesRv64gc isa env plain san C :=
  fun f hf _ en hen => h f hf en hen

/-- `Shapes.v:427` `disagrees_at_most_mono`: a smaller bound is stronger. -/
theorem disagreesAtMost_mono {env : SpuriousCfg} {w : FinProcInput → ℚ} {M : ℚ}
    {plain san : Image} {b b' : ℚ} (hM : 0 ≤ M) (hb : b ≤ b')
    (h : disagreesAtMost isa env w M plain san b) : disagreesAtMost isa env w M plain san b' :=
  fun l nd hin => (h l nd hin).trans (mul_le_mul_of_nonneg_right hb hM)

/-- `Shapes.v:436` `classifier_rejects_at_most_mono`. -/
theorem classifierRejectsAtMost_mono {C : Image} {w : FinProcInput → ℚ} {M b b' : ℚ}
    (hM : 0 ≤ M) (hb : b ≤ b') (h : classifierRejectsAtMost isa C w M b) :
    classifierRejectsAtMost isa C w M b' :=
  fun l nd hin => (h l nd hin).trans (mul_le_mul_of_nonneg_right hb hM)

/-- `Shapes.v:455` `disagrees_at_most_of_classifier`: a well-formed exact classifier whose
rejected inputs weigh at most `b` proves `disagrees_at_most … b`. The valid entry from which
the classifier would have to exit 0 comes from `image_wf` through
`Equivalence.image_brk_satisfiable_entry` (`Shapes.v:465-467`). -/
theorem disagreesAtMost_of_classifier {env : SpuriousCfg} {w : FinProcInput → ℚ} {M : ℚ}
    {plain san C : Image} {b : ℚ} (hwf : ImageWf isa C)
    (hcls : classifies isa env plain san C) (hrej : classifierRejectsAtMost isa C w M b) :
    disagreesAtMost isa env w M plain san b := by
  intro l nd hin
  refine hrej l nd fun f hf => ⟨(hin f hf).1, fun hacc => (hin f hf).2 ?_⟩
  obtain ⟨en, hen⟩ := imageBrkSatisfiable_entry C _ (hin f hf).1 hwf.2.2
  exact (hcls f (hin f hf).1 en hen).1.1 (hacc en hen)

/-- `Shapes.v:471` `agreement_decidable_of_classifier`. -/
theorem agreementDecidable_of_classifier {env : SpuriousCfg} {plain san C : Image}
    (hwf : ImageWf isa C) (hcls : classifies isa env plain san C) :
    agreementDecidable isa env plain san :=
  ⟨C, hwf, hcls⟩

/-- `Shapes.v:475` `disagrees_at_most_rv64gc_of_classifier`. -/
theorem disagreesAtMostRv64gc_of_classifier {env : SpuriousCfg} {w : FinProcInput → ℚ} {M : ℚ}
    {plain san C : Image} {b : ℚ} (hwf : ImageWf isa C)
    (hcls : classifiesRv64gc isa env plain san C) (hrej : classifierRejectsAtMost isa C w M b) :
    disagreesAtMostRv64gc isa env w M plain san b := by
  intro l nd hin
  refine hrej l nd fun f hf => ⟨(hin f hf).1, fun hacc => (hin f hf).2.2 ?_⟩
  obtain ⟨en, hen⟩ := imageBrkSatisfiable_entry C _ (hin f hf).1 hwf.2.2
  exact (hcls f (hin f hf).1 (hin f hf).2.1 en hen).1.1 (hacc en hen)

/-- `Shapes.v:491` `agreement_decidable_rv64gc_of_classifier`. -/
theorem agreementDecidableRv64gc_of_classifier {env : SpuriousCfg} {plain san C : Image}
    (hwf : ImageWf isa C) (hcls : classifiesRv64gc isa env plain san C) :
    agreementDecidableRv64gc isa env plain san :=
  ⟨C, hwf, hcls⟩

end Classification

end Silmaril.Process.LPS.Shapes
