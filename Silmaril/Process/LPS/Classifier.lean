module

public import Silmaril.Process.LPS.Equivalence
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum

/-!
# LPS in Lean: finite inputs, classifiers and weights

Translation of LPS `EquivalenceDefinition/FinInput.v`, `Classifier.v` and `Measure.v`
(upstream commit `f1006fe8`): the finite inputs a distribution weighs, the classifier
reduction (an RV64 program that exits 0 exactly on the inputs where two builds agree) and the
weight of a list of inputs. These are the ingredients of OSS Verify's `disagrees_at_most`,
`classifies` and `agreement_decidable` shapes.
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `FinInput.v:452` `FinProcInput`: a `ProcInput` with finite stdin and a finite
`/dev/urandom` prefix. -/
structure FinProcInput where
  argv : List (List Byte)
  envp : List (List Byte)
  imageFs : Fs.FileSystem
  stdin : List Byte
  uid : Word
  gid : Word
  groups : List Word
  net : NetQueue
  nofile : Word
  sigmask : Word
  hwcap : Word
  abortTerminal : Bool
  vaSize : VaSize
  urandom : List Byte
  tmp : Fs.FileSystem

/-- LPS `FinInput.v:496` `to_proc_input`. -/
def FinProcInput.toProcInput (f : FinProcInput) : ProcInput :=
  ⟨f.argv, f.envp, f.imageFs, InputStream.ofList f.stdin, f.uid, f.gid, f.groups, f.net,
    f.nofile, f.sigmask, f.hwcap, f.abortTerminal, f.vaSize,
    InputStream.ofListThen f.urandom InputStream.defaultUrandom, f.tmp⟩

/-- LPS `FinInput.v:527` `valid_fin_input`. -/
def ValidFinInput (f : FinProcInput) : Prop := ValidInput f.toProcInput

/-- LPS `FinInput.v:594` `FinCore`: what a distribution may depend on. -/
structure FinCore where
  argv : List (List Byte)
  envp : List (List Byte)
  fs : Fs.FileSystem
  stdin : List Byte
  deriving DecidableEq

/-- LPS `FinInput.v:601` `fin_core`. -/
def FinProcInput.core (f : FinProcInput) : FinCore := ⟨f.argv, f.envp, f.imageFs, f.stdin⟩

/-- LPS `FinInput.v:990` `inhabited_fin_input`. -/
def inhabitedFinInput : FinProcInput :=
  ⟨[[]], [], [], [], 0, 0, [], netSilent, defaultNofile, 0, hwcapRv64gc, false, .sv48, [], []⟩

/-- LPS `Measure.v:185` `sum_weights`. -/
def sumWeights (w : FinProcInput → ℚ) (l : List FinProcInput) : ℚ := l.foldr (w · + ·) 0

/-- LPS `Measure.v:287` `DISTRIBUTION`: non-negative weights that depend only on the core,
and a non-negative total mass `M`. -/
structure Distribution where
  w : FinProcInput → ℚ
  M : ℚ
  w_nonneg : ∀ f, 0 ≤ w f
  M_nonneg : 0 ≤ M
  w_core_blind : ∀ f g, f.core = g.core → w f = w g

section Classifier

variable (isa : UserIsa)

/-- LPS `Classifier.v:249` `classifier_alloc_limit`. -/
def classifierAllocLimit : Int := targetAllocLimit
/-- LPS `Classifier.v:665` `verdict_accept`. -/
def verdictAccept : Word := 0
/-- LPS `Classifier.v:666` `verdict_reject`. -/
def verdictReject : Word := 1

/-- LPS `Classifier.v:1338` `good_input_s`: under the reading, the two builds agree on this
input, from every pair of valid entries. -/
def GoodInputS (cfg : SpuriousCfg) (O₁ O₂ : Image) (inp : ProcInput) : Prop :=
  ∀ en₁ en₂, ValidEntry O₁ en₁ inp → ValidEntry O₂ en₂ inp →
    StrongEquivErrorFree isa isa (some cfg) sourceAllocLimit targetAllocLimit O₁ O₂ en₁ en₂ inp

/-- LPS `Classifier.v:1418` `decides_fo`: `C` exits `0` exactly on the inputs satisfying
`spec`, and otherwise exits `1`, in the forced-only reading. -/
def DecidesFo (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → ∀ en, ValidEntry C en f.toProcInput →
    (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ↔
      spec f.toProcInput) ∧
    (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ∨
      MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en f.toProcInput)

/-- LPS `Classifier.v:1479` `decides_fo_hwcap_rv64gc` (and `_rv64gcv`, `Classifier.v:1490`). -/
def DecidesFoHwcap (h : Word) (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → f.toProcInput.hwcap = h →
    ∀ en, ValidEntry C en f.toProcInput →
      (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ↔
        spec f.toProcInput) ∧
      (MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput ∨
        MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en f.toProcInput)

/-- LPS `Classifier.v:1448` `classifies_good_inputs_T_s`. -/
def ClassifiesGoodInputsTS (cfg : SpuriousCfg) (O₁ O₂ C : Image) : Prop :=
  DecidesFo isa C (GoodInputS isa cfg O₁ O₂)

/-- LPS `Classifier.v:1567` `classifies_good_inputs_T_s_hwcap_rv64gc`. -/
def ClassifiesGoodInputsTSHwcapRv64gc (cfg : SpuriousCfg) (O₁ O₂ C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gc C (GoodInputS isa cfg O₁ O₂)

/-- LPS `Classifier.v:1591` `accepts_fo`. -/
def AcceptsFo (C : Image) (f : FinProcInput) : Prop :=
  ∀ en, ValidEntry C en f.toProcInput →
    MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en f.toProcInput

/-- LPS `Classifier.v:1596` `rejects_fo`. -/
def RejectsFo (C : Image) (f : FinProcInput) : Prop := ValidFinInput f ∧ ¬ AcceptsFo isa C f

/-- LPS `Measure.v:407` `weight_bound_T_fo`. -/
def WeightBoundTFo (C : Image) (w : FinProcInput → ℚ) (M b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup → (∀ f ∈ l, RejectsFo isa C f) →
    sumWeights w l ≤ b * M

/-! ### The classified properties (LPS `Classifier.v:261-1990`) -/

/-- LPS `Classifier.v:261` `agree`: per-input agreement of two images at one shared budget
(trace sets at every pair of entries, and the existence of erroring, all-erroring and
unmodelled entries). -/
def Agree (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY, ValidEntry X enX inp → ValidEntry Y enY inp →
      TraceEquiv (run isa X lim enX inp).traces (run isa Y lim enY inp).traces) ∧
    ((∃ en, ValidEntry X en inp ∧ (run isa X lim en inp).errors) ↔
      ∃ en, ValidEntry Y en inp ∧ (run isa Y lim en inp).errors) ∧
    ((∃ en, ValidEntry X en inp ∧ (run isa X lim en inp).allErrors) ↔
      ∃ en, ValidEntry Y en inp ∧ (run isa Y lim en inp).allErrors) ∧
    ((∃ en, ValidEntry X en inp ∧ (run isa X lim en inp).unmodeled) ↔
      ∃ en, ValidEntry Y en inp ∧ (run isa Y lim en inp).unmodeled)

/-- LPS `Classifier.v:1326` `agree_s`: `agree` under a reading. -/
def AgreeS (cfg : SpuriousCfg) (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY, ValidEntry X enX inp → ValidEntry Y enY inp →
      TraceEquiv (runScfg isa cfg X lim enX inp).traces (runScfg isa cfg Y lim enY inp).traces) ∧
    ((∃ en, ValidEntry X en inp ∧ (runScfg isa cfg X lim en inp).errors) ↔
      ∃ en, ValidEntry Y en inp ∧ (runScfg isa cfg Y lim en inp).errors) ∧
    ((∃ en, ValidEntry X en inp ∧ (runScfg isa cfg X lim en inp).allErrors) ↔
      ∃ en, ValidEntry Y en inp ∧ (runScfg isa cfg Y lim en inp).allErrors) ∧
    ((∃ en, ValidEntry X en inp ∧ (runScfg isa cfg X lim en inp).unmodeled) ↔
      ∃ en, ValidEntry Y en inp ∧ (runScfg isa cfg Y lim en inp).unmodeled)

/-- LPS `Classifier.v:1343` `agree_s_may_fail`. -/
theorem agreeS_mayFail (X Y : Image) (lim : Int) (inp : ProcInput) :
    AgreeS isa mayFailCfg X Y lim inp ↔ Agree isa X Y lim inp := by
  simp only [AgreeS, Agree, runScfg_mayFail]

/-- LPS `Classifier.v:282` `good_input`: the two originals are error-free equivalent at every
pair of valid entries, each at its role's budget. -/
def GoodInput (O₁ O₂ : Image) (inp : ProcInput) : Prop :=
  ∀ en₁ en₂, ValidEntry O₁ en₁ inp → ValidEntry O₂ en₂ inp →
    StrongEquivErrorFree isa isa none sourceAllocLimit targetAllocLimit O₁ O₂ en₁ en₂ inp

/-- LPS `Classifier.v:1372` `good_input_s_may_fail`. -/
theorem goodInputS_mayFail (O₁ O₂ : Image) (inp : ProcInput) :
    GoodInputS isa mayFailCfg O₁ O₂ inp ↔ GoodInput isa O₁ O₂ inp := by
  simp only [GoodInputS, GoodInput, StrongEquivErrorFree, runIn, runScfg_mayFail]

/-- LPS `Classifier.v:531` `error_free_input`. -/
def ErrorFreeInput (O : Image) (inp : ProcInput) : Prop :=
  ∀ en, ValidEntry O en inp → ErrorFree (run isa O sourceAllocLimit en inp)

/-- LPS `Classifier.v:1856` `error_free_input_s`. -/
def ErrorFreeInputS (cfg : SpuriousCfg) (O : Image) (inp : ProcInput) : Prop :=
  ∀ en, ValidEntry O en inp → ErrorFree (runScfg isa cfg O sourceAllocLimit en inp)

/-- LPS `Classifier.v:1863` `error_free_input_s_may_fail`. -/
theorem errorFreeInputS_mayFail (O : Image) (inp : ProcInput) :
    ErrorFreeInputS isa mayFailCfg O inp ↔ ErrorFreeInput isa O inp := by
  simp only [ErrorFreeInputS, ErrorFreeInput, runScfg_mayFail]

/-- LPS `Classifier.v:674` `verdict_accept_neq_reject`. -/
theorem verdictAccept_ne_reject : verdictAccept ≠ verdictReject := by decide

/-- LPS `Classifier.v:744` `decides`: `C` exits 0 exactly on the inputs satisfying `spec`, and
otherwise 1, under the plain (may-fail) reading. -/
def Decides (C : Image) (spec : ProcInput → Prop) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → ∀ en, ValidEntry C en f.toProcInput →
    (MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput ↔
      spec f.toProcInput) ∧
    (MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput ∨
      MustExitWith isa none verdictReject C classifierAllocLimit en f.toProcInput)

/-- LPS `Classifier.v:779` `classifier_total_T`. -/
def ClassifierTotalT (C : Image) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → ∀ en, ValidEntry C en f.toProcInput →
    MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput ∨
      MustExitWith isa none verdictReject C classifierAllocLimit en f.toProcInput

/-- LPS `Classifier.v:790` `decides_implies_total`. -/
theorem Decides.total {C : Image} {spec : ProcInput → Prop} (h : Decides isa C spec) :
    ClassifierTotalT isa C :=
  fun f hf en hen => (h f hf en hen).2

/-- LPS `Classifier.v:1428` `classifier_total_T_fo`. -/
def ClassifierTotalTFo (C : Image) : Prop :=
  ∀ f : FinProcInput, ValidFinInput f → ∀ en, ValidEntry C en f.toProcInput →
    MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en
        f.toProcInput ∨
      MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en f.toProcInput

/-- LPS `Classifier.v:1436` `decides_fo_implies_total`. -/
theorem DecidesFo.total {C : Image} {spec : ProcInput → Prop} (h : DecidesFo isa C spec) :
    ClassifierTotalTFo isa C :=
  fun f hf en hen => (h f hf en hen).2

/-- LPS `Classifier.v:804` `classifies_patch_diff_T`. -/
def ClassifiesPatchDiffT (O₁ P₁ O₂ P₂ C : Image) : Prop :=
  Decides isa C fun inp =>
    Agree isa O₁ P₁ sourceAllocLimit inp ∧ Agree isa O₂ P₂ targetAllocLimit inp

/-- LPS `Classifier.v:811` `classifies_good_inputs_T`. -/
def ClassifiesGoodInputsT (O₁ O₂ C : Image) : Prop := Decides isa C (GoodInput isa O₁ O₂)

/-- LPS `Classifier.v:835` `classifies_error_free_inputs_T`. -/
def ClassifiesErrorFreeInputsT (O C : Image) : Prop := Decides isa C (ErrorFreeInput isa O)

/-- LPS `Classifier.v:1444` `classifies_patch_diff_T_s`. -/
def ClassifiesPatchDiffTS (cfg : SpuriousCfg) (O₁ P₁ O₂ P₂ C : Image) : Prop :=
  DecidesFo isa C fun inp =>
    AgreeS isa cfg O₁ P₁ sourceAllocLimit inp ∧ AgreeS isa cfg O₂ P₂ targetAllocLimit inp

/-- LPS `Classifier.v:1946` `classifies_error_free_inputs_T_s`. -/
def ClassifiesErrorFreeInputsTS (cfg : SpuriousCfg) (O C : Image) : Prop :=
  DecidesFo isa C (ErrorFreeInputS isa cfg O)

/-- LPS `Classifier.v:1971` `classifies_error_free_inputs_T_fo`. -/
def ClassifiesErrorFreeInputsTFo (O C : Image) : Prop := DecidesFo isa C (ErrorFreeInput isa O)

/-- LPS `Classifier.v:1571` `classifies_good_inputs_T_s_hwcap_rv64gcv`. -/
def ClassifiesGoodInputsTSHwcapRv64gcv (cfg : SpuriousCfg) (O₁ O₂ C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gcv C (GoodInputS isa cfg O₁ O₂)

/-- LPS `Classifier.v:1503` `decides_fo_hwcap_rv64gc_of_decides_fo` (and `_rv64gcv`,
`Classifier.v:1507`). -/
theorem DecidesFo.hwcap {C : Image} {spec : ProcInput → Prop} (h : Word)
    (hd : DecidesFo isa C spec) : DecidesFoHwcap isa h C spec :=
  fun f hf _ en hen => hd f hf en hen

/-- LPS `Classifier.v:1518` `decides_fo_hwcap_splits`: a valid input advertises one of the two
RISC-V hardware capabilities, so the two declared halves make up the whole. -/
theorem decidesFo_hwcap_splits {C : Image} {spec : ProcInput → Prop} :
    DecidesFo isa C spec ↔
      DecidesFoHwcap isa hwcapRv64gc C spec ∧ DecidesFoHwcap isa hwcapRv64gcv C spec := by
  refine ⟨fun h => ⟨h.hwcap isa _, h.hwcap isa _⟩, fun ⟨h₁, h₂⟩ f hf en hen => ?_⟩
  rcases hf.2.1 with hw | hw
  · exact h₁ f hf hw en hen
  · exact h₂ f hf hw en hen

/-- LPS `Classifier.v:1557` `classifies_patch_diff_T_s_hwcap_rv64gc`. -/
def ClassifiesPatchDiffTSHwcapRv64gc (cfg : SpuriousCfg) (O₁ P₁ O₂ P₂ C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gc C fun inp =>
    AgreeS isa cfg O₁ P₁ sourceAllocLimit inp ∧ AgreeS isa cfg O₂ P₂ targetAllocLimit inp

/-- LPS `Classifier.v:1562` `classifies_patch_diff_T_s_hwcap_rv64gcv`. -/
def ClassifiesPatchDiffTSHwcapRv64gcv (cfg : SpuriousCfg) (O₁ P₁ O₂ P₂ C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gcv C fun inp =>
    AgreeS isa cfg O₁ P₁ sourceAllocLimit inp ∧ AgreeS isa cfg O₂ P₂ targetAllocLimit inp

/-- LPS `Classifier.v:1575` `classifies_patch_diff_T_s_hwcap_splits`. -/
theorem classifiesPatchDiffTS_hwcap_splits (cfg : SpuriousCfg) (O₁ P₁ O₂ P₂ C : Image) :
    ClassifiesPatchDiffTS isa cfg O₁ P₁ O₂ P₂ C ↔
      ClassifiesPatchDiffTSHwcapRv64gc isa cfg O₁ P₁ O₂ P₂ C ∧
        ClassifiesPatchDiffTSHwcapRv64gcv isa cfg O₁ P₁ O₂ P₂ C :=
  decidesFo_hwcap_splits isa

/-- LPS `Classifier.v:1581` `classifies_good_inputs_T_s_hwcap_splits`. -/
theorem classifiesGoodInputsTS_hwcap_splits (cfg : SpuriousCfg) (O₁ O₂ C : Image) :
    ClassifiesGoodInputsTS isa cfg O₁ O₂ C ↔
      ClassifiesGoodInputsTSHwcapRv64gc isa cfg O₁ O₂ C ∧
        ClassifiesGoodInputsTSHwcapRv64gcv isa cfg O₁ O₂ C :=
  decidesFo_hwcap_splits isa

/-- LPS `Classifier.v:1979` `classifies_error_free_inputs_T_s_hwcap_rv64gc`. -/
def ClassifiesErrorFreeInputsTSHwcapRv64gc (cfg : SpuriousCfg) (O C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gc C (ErrorFreeInputS isa cfg O)

/-- LPS `Classifier.v:1983` `classifies_error_free_inputs_T_s_hwcap_rv64gcv`. -/
def ClassifiesErrorFreeInputsTSHwcapRv64gcv (cfg : SpuriousCfg) (O C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gcv C (ErrorFreeInputS isa cfg O)

/-- LPS `Classifier.v:1987` `classifies_error_free_inputs_T_fo_hwcap_rv64gc`. -/
def ClassifiesErrorFreeInputsTFoHwcapRv64gc (O C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gc C (ErrorFreeInput isa O)

/-- LPS `Classifier.v:1990` `classifies_error_free_inputs_T_fo_hwcap_rv64gcv`. -/
def ClassifiesErrorFreeInputsTFoHwcapRv64gcv (O C : Image) : Prop :=
  DecidesFoHwcap isa hwcapRv64gcv C (ErrorFreeInput isa O)

/-- LPS `Classifier.v:1993` `classifies_error_free_inputs_T_s_hwcap_splits`. -/
theorem classifiesErrorFreeInputsTS_hwcap_splits (cfg : SpuriousCfg) (O C : Image) :
    ClassifiesErrorFreeInputsTS isa cfg O C ↔
      ClassifiesErrorFreeInputsTSHwcapRv64gc isa cfg O C ∧
        ClassifiesErrorFreeInputsTSHwcapRv64gcv isa cfg O C :=
  decidesFo_hwcap_splits isa

/-- LPS `Classifier.v:1999` `classifies_error_free_inputs_T_fo_hwcap_splits`. -/
theorem classifiesErrorFreeInputsTFo_hwcap_splits (O C : Image) :
    ClassifiesErrorFreeInputsTFo isa O C ↔
      ClassifiesErrorFreeInputsTFoHwcapRv64gc isa O C ∧
        ClassifiesErrorFreeInputsTFoHwcapRv64gcv isa O C :=
  decidesFo_hwcap_splits isa

/-! ### Accept and reject as sets of finite inputs (LPS `Classifier.v:848-1830`) -/

/-- LPS `Classifier.v:848` `accepts`: every valid entry exits 0 (plain reading). -/
def Accepts (C : Image) (f : FinProcInput) : Prop :=
  ∀ en, ValidEntry C en f.toProcInput →
    MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput

/-- LPS `Classifier.v:861` `rejects`: a valid finite input it does not accept. -/
def Rejects (C : Image) (f : FinProcInput) : Prop := ValidFinInput f ∧ ¬ Accepts isa C f

/-- LPS `Classifier.v:883` `accepts_refuted_by_entry`. -/
theorem accepts_refuted_by_entry {C : Image} {f : FinProcInput} {en : ExecEntry}
    (hen : ValidEntry C en f.toProcInput)
    (hno : ¬ MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput) :
    ¬ Accepts isa C f :=
  fun ha => hno (ha en hen)

/-- LPS `Classifier.v:902` `rejects_by_exit1`. -/
theorem rejects_by_exit1 {C : Image} {f : FinProcInput} {en : ExecEntry} (hf : ValidFinInput f)
    (hen : ValidEntry C en f.toProcInput)
    (h1 : MustExitWith isa none verdictReject C classifierAllocLimit en f.toProcInput) :
    Rejects isa C f :=
  ⟨hf, fun ha => verdictAccept_ne_reject (MustExitWith.exclusive isa (ha en hen) h1)⟩

/-- LPS `Classifier.v:923` `accepts_vacuous_no_entries`: an image with no valid entry accepts
everything; this is why the shapes ask `image_wf`. -/
theorem accepts_vacuous_no_entries {C : Image} {f : FinProcInput}
    (h : ∀ en, ¬ ValidEntry C en f.toProcInput) : Accepts isa C f :=
  fun en hen => (h en hen).elim

/-- LPS `Classifier.v:941` `decides_exit1_iff`: exiting 1 is the rejection. -/
theorem Decides.exit1_iff {C : Image} {spec : ProcInput → Prop} (hd : Decides isa C spec)
    {f : FinProcInput} {en : ExecEntry} (hf : ValidFinInput f)
    (hen : ValidEntry C en f.toProcInput) :
    MustExitWith isa none verdictReject C classifierAllocLimit en f.toProcInput ↔
      ¬ spec f.toProcInput := by
  obtain ⟨hiff, htot⟩ := hd f hf en hen
  constructor
  · intro h1 hs
    exact verdictAccept_ne_reject (MustExitWith.exclusive isa (hiff.2 hs) h1)
  · intro hns
    exact htot.resolve_left fun h0 => hns (hiff.1 h0)

/-- LPS `Classifier.v:972` `decides_verdict_entry_uniform`: the verdict does not depend on the
entry. -/
theorem Decides.verdict_entry_uniform {C : Image} {spec : ProcInput → Prop}
    (hd : Decides isa C spec) {f : FinProcInput} {en₁ en₂ : ExecEntry} (hf : ValidFinInput f)
    (h₁ : ValidEntry C en₁ f.toProcInput) (h₂ : ValidEntry C en₂ f.toProcInput)
    (h : MustExitWith isa none verdictAccept C classifierAllocLimit en₁ f.toProcInput) :
    MustExitWith isa none verdictAccept C classifierAllocLimit en₂ f.toProcInput :=
  (hd f hf en₂ h₂).1.2 ((hd f hf en₁ h₁).1.1 h)

/-- LPS `Classifier.v:1013` `decides_accepts_iff`, given a valid entry (which `image_wf`
supplies, `imageBrkSatisfiable_entry`). -/
theorem Decides.accepts_iff {C : Image} {spec : ProcInput → Prop} (hd : Decides isa C spec)
    {f : FinProcInput} (hf : ValidFinInput f) (hen : ∃ en, ValidEntry C en f.toProcInput) :
    Accepts isa C f ↔ spec f.toProcInput := by
  obtain ⟨en, hen⟩ := hen
  exact ⟨fun ha => (hd f hf en hen).1.1 (ha en hen), fun hs en' hen' => (hd f hf en' hen').1.2 hs⟩

/-- LPS `Classifier.v:1040` `decides_rejects_iff`. -/
theorem Decides.rejects_iff {C : Image} {spec : ProcInput → Prop} (hd : Decides isa C spec)
    {f : FinProcInput} (hf : ValidFinInput f) (hen : ∃ en, ValidEntry C en f.toProcInput) :
    Rejects isa C f ↔ ¬ spec f.toProcInput := by
  rw [Rejects, hd.accepts_iff isa hf hen]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩

/-- LPS `Classifier.v:1095` `classifier_total_T_refuted_by_undecided`. -/
theorem classifierTotalT_refuted_by_undecided {C : Image} {f : FinProcInput} {en : ExecEntry}
    (hf : ValidFinInput f) (hen : ValidEntry C en f.toProcInput)
    (h0 : ¬ MustExitWith isa none verdictAccept C classifierAllocLimit en f.toProcInput)
    (h1 : ¬ MustExitWith isa none verdictReject C classifierAllocLimit en f.toProcInput) :
    ¬ ClassifierTotalT isa C :=
  fun ht => (ht f hf en hen).elim h0 h1

/-- LPS `Classifier.v:1172` `decides_vacuous_no_entries`. -/
theorem decides_vacuous_no_entries {C : Image} (spec : ProcInput → Prop)
    (h : ∀ f en, ¬ ValidEntry C en (FinProcInput.toProcInput f)) : Decides isa C spec :=
  fun f _ en hen => (h f en hen).elim

/-- LPS `Classifier.v:1614` `accepts_fo_refuted_by_entry`. -/
theorem acceptsFo_refuted_by_entry {C : Image} {f : FinProcInput} {en : ExecEntry}
    (hen : ValidEntry C en f.toProcInput)
    (hno : ¬ MustExitWith isa (some forcedOnlyCfg) verdictAccept C classifierAllocLimit en
      f.toProcInput) : ¬ AcceptsFo isa C f :=
  fun ha => hno (ha en hen)

/-- LPS `Classifier.v:1622` `rejects_fo_by_exit1`. -/
theorem rejectsFo_by_exit1 {C : Image} {f : FinProcInput} {en : ExecEntry} (hf : ValidFinInput f)
    (hen : ValidEntry C en f.toProcInput)
    (h1 : MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en
      f.toProcInput) : RejectsFo isa C f :=
  ⟨hf, fun ha => verdictAccept_ne_reject (MustExitWith.exclusive isa (ha en hen) h1)⟩

/-- LPS `Classifier.v:1635` `accepts_fo_vacuous_no_entries`. -/
theorem acceptsFo_vacuous_no_entries {C : Image} {f : FinProcInput}
    (h : ∀ en, ¬ ValidEntry C en f.toProcInput) : AcceptsFo isa C f :=
  fun en hen => (h en hen).elim

/-- LPS `Classifier.v:1645` `decides_fo_exit1_iff`. -/
theorem DecidesFo.exit1_iff {C : Image} {spec : ProcInput → Prop} (hd : DecidesFo isa C spec)
    {f : FinProcInput} {en : ExecEntry} (hf : ValidFinInput f)
    (hen : ValidEntry C en f.toProcInput) :
    MustExitWith isa (some forcedOnlyCfg) verdictReject C classifierAllocLimit en
        f.toProcInput ↔ ¬ spec f.toProcInput := by
  obtain ⟨hiff, htot⟩ := hd f hf en hen
  constructor
  · intro h1 hs
    exact verdictAccept_ne_reject (MustExitWith.exclusive isa (hiff.2 hs) h1)
  · intro hns
    exact htot.resolve_left fun h0 => hns (hiff.1 h0)

/-- LPS `Classifier.v:1686` `decides_fo_accepts_iff`, given a valid entry. -/
theorem DecidesFo.accepts_iff {C : Image} {spec : ProcInput → Prop} (hd : DecidesFo isa C spec)
    {f : FinProcInput} (hf : ValidFinInput f) (hen : ∃ en, ValidEntry C en f.toProcInput) :
    AcceptsFo isa C f ↔ spec f.toProcInput := by
  obtain ⟨en, hen⟩ := hen
  exact ⟨fun ha => (hd f hf en hen).1.1 (ha en hen), fun hs en' hen' => (hd f hf en' hen').1.2 hs⟩

/-- LPS `Classifier.v:1699` `decides_fo_rejects_iff`. -/
theorem DecidesFo.rejects_iff {C : Image} {spec : ProcInput → Prop} (hd : DecidesFo isa C spec)
    {f : FinProcInput} (hf : ValidFinInput f) (hen : ∃ en, ValidEntry C en f.toProcInput) :
    RejectsFo isa C f ↔ ¬ spec f.toProcInput := by
  rw [RejectsFo, hd.accepts_iff isa hf hen]
  exact ⟨fun h => h.2, fun h => ⟨hf, h⟩⟩

/-- LPS `Classifier.v:1777` `decides_fo_vacuous_no_entries`. -/
theorem decidesFo_vacuous_no_entries {C : Image} (spec : ProcInput → Prop)
    (h : ∀ f en, ¬ ValidEntry C en (FinProcInput.toProcInput f)) : DecidesFo isa C spec :=
  fun f _ en hen => (h f en hen).elim

/-- LPS `Classifier.v:1795` `classifier_decided`: the refusal question is answered on every run
of `C` the obligations quantify over. -/
def ClassifierDecided (C : Image) : Prop :=
  ∀ f en, ValidFinInput f → ValidEntry C en f.toProcInput →
    RunDecided isa forcedOnlyCfg C classifierAllocLimit en f.toProcInput

/-- LPS `Classifier.v:1801` `accepts_fo_of_accepts`. The `classifier_decided` premise of LPS is
not needed (see `MustExitIn.scfg_of_plain`). -/
theorem acceptsFo_of_accepts {C : Image} {f : FinProcInput} (ha : Accepts isa C f) :
    AcceptsFo isa C f :=
  fun en hen => MustExitIn.scfg_of_plain isa forcedOnlyCfg (ha en hen)

/-- LPS `Classifier.v:1810` `rejects_of_rejects_fo`. -/
theorem rejects_of_rejectsFo {C : Image} {f : FinProcInput} (h : RejectsFo isa C f) :
    Rejects isa C f :=
  ⟨h.1, fun ha => h.2 (acceptsFo_of_accepts isa ha)⟩

/-- LPS `Classifier.v:1818` `decides_fo_of_decides`. -/
theorem DecidesFo.of_decides {C : Image} {spec : ProcInput → Prop} (hd : Decides isa C spec) :
    DecidesFo isa C spec := by
  intro f hf en hen
  obtain ⟨hiff, htot⟩ := hd f hf en hen
  have hacc := MustExitIn.scfg_of_plain isa forcedOnlyCfg
    (S := [verdictAccept]) (img := C) (lim := classifierAllocLimit) (en := en)
    (inp := f.toProcInput)
  have hrej := MustExitIn.scfg_of_plain isa forcedOnlyCfg
    (S := [verdictReject]) (img := C) (lim := classifierAllocLimit) (en := en)
    (inp := f.toProcInput)
  refine ⟨⟨fun hfo => ?_, fun hs => hacc (hiff.2 hs)⟩, htot.imp hacc hrej⟩
  rcases htot with h0 | h1
  · exact hiff.1 h0
  · exact (verdictAccept_ne_reject (MustExitWith.exclusive isa hfo (hrej h1))).elim

/-! ### The weight bound (LPS `Measure.v:185-463`) -/

/-- LPS `Measure.v:192` `sum_weights_nil`. -/
@[simp] theorem sumWeights_nil (w : FinProcInput → ℚ) : sumWeights w [] = 0 := rfl

/-- LPS `Measure.v:195` `sum_weights_cons`. -/
@[simp] theorem sumWeights_cons (w : FinProcInput → ℚ) (f : FinProcInput) (l : List FinProcInput) :
    sumWeights w (f :: l) = w f + sumWeights w l := rfl

/-- LPS `Measure.v:208` `sum_weights_ext` (an equality: `ℚ` is normalised). -/
theorem sumWeights_ext {w₁ w₂ : FinProcInput → ℚ} (l : List FinProcInput)
    (h : ∀ f, w₁ f = w₂ f) : sumWeights w₁ l = sumWeights w₂ l := by
  rw [funext h]

/-- `sumWeights` is `List.sum` of the mapped weights. -/
theorem sumWeights_eq_sum (w : FinProcInput → ℚ) (l : List FinProcInput) :
    sumWeights w l = (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [ih]

/-- LPS `Measure.v:249` `weight_bound_T`. -/
def WeightBoundT (C : Image) (w : FinProcInput → ℚ) (M b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup → (∀ f ∈ l, Rejects isa C f) →
    sumWeights w l ≤ b * M

/-- LPS `Measure.v:310` `weight_bound_mono`. -/
theorem WeightBoundT.mono {C : Image} {w : FinProcInput → ℚ} {M b b' : ℚ} (hM : 0 ≤ M)
    (hb : b ≤ b') (h : WeightBoundT isa C w M b) : WeightBoundT isa C w M b' :=
  fun l nd hin => (h l nd hin).trans (mul_le_mul_of_nonneg_right hb hM)

/-- LPS `Measure.v:413` `weight_bound_fo_mono`. -/
theorem WeightBoundTFo.mono {C : Image} {w : FinProcInput → ℚ} {M b b' : ℚ} (hM : 0 ≤ M)
    (hb : b ≤ b') (h : WeightBoundTFo isa C w M b) : WeightBoundTFo isa C w M b' :=
  fun l nd hin => (h l nd hin).trans (mul_le_mul_of_nonneg_right hb hM)

/-- LPS `Measure.v:433` `weight_bound_T_fo_of_weight_bound_T` (LPS's `classifier_decided`
premise is not needed). -/
theorem WeightBoundTFo.of_weightBoundT {C : Image} {w : FinProcInput → ℚ} {M b : ℚ}
    (h : WeightBoundT isa C w M b) : WeightBoundTFo isa C w M b :=
  fun l nd hin => h l nd fun f hf => rejects_of_rejectsFo isa (hin f hf)

/-- Two inputs with distinct cores form an admissible two-element list. -/
theorem nodup_cores_pair {f₁ f₂ : FinProcInput} (hne : f₁.core ≠ f₂.core) :
    ([f₁, f₂].map (·.core)).Nodup := by
  simpa using hne

/-- LPS `Measure.v:373` `weight_bound_refutable`: the unit bound fails as soon as two inputs
with distinct cores are rejected. -/
theorem weightBound_refutable {C : Image} {f₁ f₂ : FinProcInput} (h₁ : Rejects isa C f₁)
    (h₂ : Rejects isa C f₂) (hne : f₁.core ≠ f₂.core) :
    ¬ WeightBoundT isa C (fun _ => 1) 1 1 := by
  intro h
  have := h [f₁, f₂] (nodup_cores_pair hne) (by simp [h₁, h₂])
  norm_num [sumWeights] at this

/-- LPS `Measure.v:443` `weight_bound_fo_refutable`. -/
theorem weightBoundFo_refutable {C : Image} {f₁ f₂ : FinProcInput} (h₁ : RejectsFo isa C f₁)
    (h₂ : RejectsFo isa C f₂) (hne : f₁.core ≠ f₂.core) :
    ¬ WeightBoundTFo isa C (fun _ => 1) 1 1 := by
  intro h
  have := h [f₁, f₂] (nodup_cores_pair hne) (by simp [h₁, h₂])
  norm_num [sumWeights] at this

end Classifier

end Silmaril.Process.LPS
