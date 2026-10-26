module

public import Silmaril.Process.LPS.Problems.NativeX86Complete.Semantics
public import Silmaril.Process.LPS.Problems.NativeX86Complete.LaunchEntry

/-!
# OSS Verify problems on native x86-64: the complete table and the realistic launch

`Problems.NativeX86` states each shape of `Shapes.v` on native x86-64 with the reviewed-default
table (`NativeX86.extendedSyscallSpec`: twenty-two reviewed reference arms and `arch_prctl`; every
other call, `writev`, `readv`, `lseek`, `open` and `unlink` among them, is `unmodeled`) and the
minimal launch (`X86Launch`: a fixed auxiliary vector, `AT_HWCAP` chosen freely). This file states
the same shapes over

* the **complete native system** `NativeX86.All.system` (`Semantics.complete`): all ninety
  reference slots with the families' x86-64 arms, the twenty extensions, boundary,
  configuration and version chaos, and the native refusal reading; and
* the **realistic launch domain** `Machines.X86RealisticLaunch` (#3682): the stacks Linux
  x86-64 builds for a static `ET_EXEC` (`create_elf_tables` order, `AT_MINSIGSTKSZ`, `AT_HWCAP2`,
  the vDSO and rseq entries, set-id credentials, the `execve` filename, the stack top anywhere in
  the `STACK_RND_MASK` window), with the program break and mmap base in the ASLR windows of
  `x86LaunchBounds` (#3681, `X86LaunchAslr`). Each launch is a `Choices` value and an entry. A
  launch the LPS transition system does not model exactly (a vDSO or vsyscall page, whose code is
  not modelled, or set-id credentials) runs as `X86RealisticLaunch.chaos` (every trace, possibly
  erroring): unmodelled is chaos, so such a launch can only make a statement fail, never hold
  vacuously. Budget refusal and must-exit are claimed only at exact launches (`BudgetRefusedIn`,
  `MustExitIn`).

`Problem.denote?` follows `Problems.Problem.denote?` (#3670): a statement naming a build without a
snapshot, or a bound statement of a harness without a translated distribution, is *untranslated*
(`none`), never `False` (`denote?_eq_none_iff`, `denote?_disagreesAtMost_of_none`).

## The lattice

A `Profile` is a point: the semantics (table and refusal reading), the machine, the `AT_HWCAP`
domain and the launch-choice domain. `Profile.Le P Q` says every agreement, halting and bound
statement over `P` implies the same statement over `Q` (`Problem.denote?_le`):

* the table: `P`'s restricts `Q`'s (`Lattice.Restricts`, with agreeing refusal readings,
  `Semantics.Below`). The complete system is below the families' exact arms
  (`complete_below_exact`) and below the gap-sweep variant (`complete_below_gap`);
* the inputs and launches: `Q`'s domains are inside `P`'s. The default (every `AT_HWCAP` below
  `2^32`, every realistic launch) is above the exact-launch slice (`exactChoices`) and the
  `AT_HWCAP = 0` slice (`noHwcap`).

`agreementDecidable` (a classifier exits `0` exactly on the inputs where the builds agree) is not
monotone in the table or the launch domain, since its right-hand side changes with them; it
narrows in the `AT_HWCAP` domain only (`Problem.denote?_narrowHwcap`).

## Relation to the reviewed-default statements of `Problems.NativeX86`

They are kept (`NativeX86.NativeProblem.denote?`). Neither family implies the other in general,
but both are corollaries of the statements over their meet (`NativeX86Complete.Meet`:
`JointProblem.ofImages_implies_complete`, `JointProblem.ofImages_implies_reviewedDefault`),
over the meet table `meetDefault` (the greatest lower bound of the two tables, `below_meet`) and
over both launch domains at once. Directly:

* **Table.** Neither table restricts the other (`NativeX86Complete.Census`:
  `complete_not_restricts_reviewedDefault`, `reviewedDefault_not_restricts_complete`). The
  reviewed-default table declines calls the complete one specifies (`open`, `lseek`, `readv`,
  `writev`, `unlink`, `epoll_create`, ...), and the complete one declines inputs the reviewed
  default answers (the `TASK_SIZE_MAX` window and band of `NativeX86.All.guard`).
* **Launch.** The minimal launch and the realistic one have disjoint auxiliary vectors
  (`X86RealisticLaunch.old_auxv_not_realistic`) and no behavioural refinement relates them. The
  input domains are related: the minimal launch's `X86Launch.ValidInput` is exactly the
  `AT_HWCAP = 0` slice of `X86RealisticLaunch.ValidInput` (`X86RealisticLaunch.validInput_old_iff`),
  and the reviewed-default statements also range over `AT_HWCAP` values of `2^32` and more,
  which no x86-64 kernel advertises.
* **Bounds.** Both are untranslated (`none`) without a distribution.

## Anti-vacuity

`imageWf_realistic_entry`: on a well-formed snapshot (`NativeX86.ImageWf`, the same obligation as
before) every realistic valid input has an *exact* realistic launch (no vDSO, no vsyscall page,
real credentials, the stack top at `STACK_TOP`). So no statement over a domain containing the
exact launches (`ExactIncluded`) holds because its launch quantifier is empty.

## The default profile is expected to be false

The other way round, a valid *non-exact* launch refutes the agreement and halting statements
(`not_agreement_of_inexact` and the halting forms): it runs as chaos, which errors. The default
profile ranges over vDSO launches, so its statements are expected to be false until the vDSO and
vsyscall pages are modelled; the exact-launch slice (`Profile.exactSlice`, which the default
implies) is the meaningful target until then.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86Complete

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

/-! ## Profiles -/

/-- Which realistic launches a statement ranges over. -/
abbrev ChoiceDomain := ProcInput → Choices → Prop

/-- Every realistic launch: the default. -/
def anyChoices : ChoiceDomain := fun _ _ => True

/-- The launches the LPS transition system models exactly (`X86RealisticLaunch.Exact`). -/
def exactChoices : ChoiceDomain := X86RealisticLaunch.Exact

/-- A point of the lattice. -/
structure Profile where
  sem : Semantics
  isa : UserIsa
  hwcap : HwcapDomain
  choices : ChoiceDomain

/-- The default profile on a machine: complete table, every `AT_HWCAP`, every realistic launch. -/
def Profile.default (isa : UserIsa) : Profile :=
  ⟨complete, isa, Problems.NativeX86.anyHwcap, anyChoices⟩

section Shapes

variable (P : Profile)

/-- A realistic launch of the profile: a valid realistic entry at a choice in its domain. -/
def Launch (snap : Snapshot) (c : Choices) (en : ExecEntry) (inp : ProcInput) : Prop :=
  X86RealisticLaunch.ValidEntry P.isa snap c en inp ∧ P.choices inp c

/-- The realistic valid inputs (`AT_HWCAP` a 32-bit `CPUID.1:EDX`) in the profile's
`AT_HWCAP` domain, with an `abort()` stance. -/
def ValidInput (abortModelled : Bool) (inp : ProcInput) : Prop :=
  X86RealisticLaunch.ValidInput inp ∧ P.hwcap inp.hwcap ∧ inp.abortTerminal = abortModelled

/-- The run under a reading: the LPS semantics at an exact launch, chaos elsewhere. -/
def runIn (r : Reading) (snap : Snapshot) (lim : Int) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) : Behavior :=
  X86RealisticLaunch.runWith P.isa (P.sem.spec r) (P.sem.refused r) snap lim c en inp

/-- Refusal for budget, claimed only at an exact launch (elsewhere the run is chaos and is never
excused). -/
def BudgetRefusedIn (r : Reading) (snap : Snapshot) (lim : Int) (c : Choices) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  X86RealisticLaunch.Exact inp c ∧
    NativeX86.RunBudgetRefusedWithStack P.isa (X86RealisticLaunch.entryStack c) (P.sem.spec r)
      (P.sem.refused r) snap.image lim en inp

/-- Must-exit, which only an exact launch can satisfy. -/
def MustExitIn (r : Reading) (S : List Word) (snap : Snapshot) (lim : Int) (c : Choices)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  X86RealisticLaunch.Exact inp c ∧
    MustExitInAt snap.image.segments (P.sem.spec r) (P.sem.refused r) S
      (X86RealisticLaunch.init P.isa snap c en lim inp)

/-- Error free, and for the abort-modelled shapes not killed by a signal. -/
def Good (abortModelled : Bool) (b : Behavior) : Prop :=
  if abortModelled then ErrorFreeUnkilled b else ErrorFree b

/-- The agreement conclusion of every agreement shape. -/
def agreement (r : Reading) (abortModelled : Bool) (limPlain limSan : Int) (plain san : Snapshot) :
    Prop :=
  ∀ (cPlain : Choices) (enPlain : ExecEntry) (cSan : Choices) (enSan : ExecEntry)
    (inp : ProcInput),
    Launch P plain cPlain enPlain inp → Launch P san cSan enSan inp →
    ValidInput P abortModelled inp →
    ¬ BudgetRefusedIn P r plain limPlain cPlain enPlain inp →
    Good abortModelled (runIn P r plain limPlain cPlain enPlain inp) ∧
    Good abortModelled (runIn P r san limSan cSan enSan inp) ∧
    TraceEquiv (runIn P r plain limPlain cPlain enPlain inp).traces
      (runIn P r san limSan cSan enSan inp).traces

/-- `Shapes.haltsWithinBudget`. -/
def haltsWithinBudget (lim : Int) (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (c : Choices) (en : ExecEntry) (inp : ProcInput), Launch P snap c en inp →
    ValidInput P false inp →
    ¬ BudgetRefusedIn P (some forcedOnlyCfg) snap lim c en inp →
    MustExitIn P (some forcedOnlyCfg) allowed snap lim c en inp

/-- `Shapes.haltsMayFail`. -/
def haltsMayFail (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (c : Choices) (en : ExecEntry) (inp : ProcInput), Launch P snap c en inp →
    ValidInput P false inp →
    MustExitIn P (some mayFailCfg) allowed snap sourceAllocLimit c en inp

/-- The valid finite inputs (`valid_fin_input`). -/
def ValidFinInput (f : FinProcInput) : Prop := ValidInput P false f.toProcInput

/-- `GoodInputS`: under the reading, at the shared limits, both builds are error free and
agree, for every pair of launches. -/
def GoodInputS (env : SpuriousCfg) (plain san : Snapshot) (inp : ProcInput) : Prop :=
  ∀ c₁ en₁ c₂ en₂, Launch P plain c₁ en₁ inp → Launch P san c₂ en₂ inp →
    ErrorFree (runIn P (some env) plain sourceAllocLimit c₁ en₁ inp) ∧
      ErrorFree (runIn P (some env) san targetAllocLimit c₂ en₂ inp) ∧
      TraceEquiv (runIn P (some env) plain sourceAllocLimit c₁ en₁ inp).traces
        (runIn P (some env) san targetAllocLimit c₂ en₂ inp).traces

/-- `Shapes.disagreesAtMost`. -/
def disagreesAtMost (env : SpuriousCfg) (w : FinProcInput → ℚ) (M : ℚ) (plain san : Snapshot)
    (b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup →
    (∀ f ∈ l, ValidFinInput P f ∧ ¬ GoodInputS P env plain san f.toProcInput) →
    sumWeights w l ≤ b * M

/-- `Shapes.classifies`: the x86-64 program `C` exits `0` exactly on the inputs where the builds
agree, and `1` otherwise, in the forced-only reading. -/
def classifies (env : SpuriousCfg) (plain san C : Snapshot) : Prop :=
  ∀ f : FinProcInput, ValidFinInput P f → ∀ c en,
    Launch P C c en f.toProcInput →
    (MustExitIn P (some forcedOnlyCfg) [verdictAccept] C classifierAllocLimit c en f.toProcInput ↔
      GoodInputS P env plain san f.toProcInput) ∧
    (MustExitIn P (some forcedOnlyCfg) [verdictAccept] C classifierAllocLimit c en f.toProcInput ∨
      MustExitIn P (some forcedOnlyCfg) [verdictReject] C classifierAllocLimit c en f.toProcInput)

/-- `Shapes.agreementDecidable`: some well-formed x86-64 snapshot classifies. -/
def agreementDecidable (env : SpuriousCfg) (plain san : Snapshot) : Prop :=
  ∃ C : Snapshot, Problems.NativeX86.ImageWf P.isa C ∧ classifies P env plain san C

end Shapes

/-- The meaning of an agreement shape. The `_rv64gc` shapes restrict the riscv64 hardware
capabilities to RV64GC; x86-64 has no such base value, so each is its plain form over the whole
`AT_HWCAP` domain, which is at least as strong. -/
def _root_.Silmaril.Process.LPS.Problems.AgreeShape.denoteComplete (P : Profile)
    (limP limS : Int) (plain san : Snapshot) : AgreeShape → Prop
  | .agrees | .rv64gc => agreement P none false limP limS plain san
  | .agreesIn env | .inRv64gc env => agreement P (some env.cfg) false limP limS plain san
  | .abortModelled | .abortModelledRv64gc => agreement P none true limP limS plain san
  | .inAbortModelled env => agreement P (some env.cfg) true limP limS plain san

/-! ## Transfer between profiles -/

/-- Statements over `P` imply statements over `Q`: the same machine, `P`'s table below `Q`'s,
and `Q`'s domains inside `P`'s. -/
structure Profile.Le (P Q : Profile) : Prop where
  isa : Q.isa = P.isa
  sem : P.sem.Below Q.sem
  hwcap : ∀ h, Q.hwcap h → P.hwcap h
  choices : ∀ inp c, Q.choices inp c → P.choices inp c

theorem Profile.Le.refl (P : Profile) : P.Le P :=
  ⟨rfl, Semantics.Below.refl _, fun _ h => h, fun _ _ h => h⟩

section ProfileTransfer

variable {P Q : Profile}

theorem Profile.Le.launch (h : P.Le Q) {snap : Snapshot} {c : Choices} {en : ExecEntry}
    {inp : ProcInput} (l : Launch Q snap c en inp) : Launch P snap c en inp :=
  ⟨h.isa ▸ l.1, h.choices _ _ l.2⟩

theorem Profile.Le.validInput (h : P.Le Q) {a : Bool} {inp : ProcInput}
    (v : ValidInput Q a inp) : ValidInput P a inp :=
  ⟨v.1, h.hwcap _ v.2.1, v.2.2⟩

theorem Profile.Le.budget (h : P.Le Q) {r : Reading} {snap : Snapshot} {lim : Int} {c : Choices}
    {en : ExecEntry} {inp : ProcInput} (b : BudgetRefusedIn P r snap lim c en inp) :
    BudgetRefusedIn Q r snap lim c en inp := by
  obtain ⟨ex, b⟩ := b
  refine ⟨ex, ?_⟩
  rw [h.isa]
  exact runBudgetRefusedFromUsing_mono (h.sem r).1 (h.sem r).2 b

theorem Profile.Le.mustExit (h : P.Le Q) {r : Reading} {S : List Word} {snap : Snapshot}
    {lim : Int} {c : Choices} {en : ExecEntry} {inp : ProcInput}
    (m : MustExitIn P r S snap lim c en inp) : MustExitIn Q r S snap lim c en inp := by
  obtain ⟨ex, m⟩ := m
  refine ⟨ex, ?_⟩
  rw [h.isa]
  exact mustExitInAt_of_restricts (h.sem r).1 (h.sem r).2 m

/-- An error-free run over `P` is an error-free run over `Q` with the same traces. -/
theorem Profile.Le.run (h : P.Le Q) {r : Reading} {snap : Snapshot} {lim : Int} {c : Choices}
    {en : ExecEntry} {inp : ProcInput} (ef : ErrorFree (runIn P r snap lim c en inp)) :
    ErrorFree (runIn Q r snap lim c en inp) ∧
      ∀ tr, (runIn P r snap lim c en inp).traces tr ↔ (runIn Q r snap lim c en inp).traces tr := by
  unfold runIn at ef ⊢
  rw [h.isa]
  by_cases ex : X86RealisticLaunch.Exact inp c
  · simp only [X86RealisticLaunch.runWith, ex, ↓reduceIte] at ef ⊢
    exact ⟨errorFree_of_restricts (h.sem r).1 (h.sem r).2 ef,
      fun tr => obsTrace_eq_of_errorFree (h.sem r).1 (h.sem r).2 ef tr⟩
  · simp only [X86RealisticLaunch.runWith, ex, ↓reduceIte] at ef ⊢
    exact ⟨ef, fun _ => trivial⟩

theorem Profile.Le.good (h : P.Le Q) {a : Bool} {r : Reading} {snap : Snapshot} {lim : Int}
    {c : Choices} {en : ExecEntry} {inp : ProcInput} (g : Good a (runIn P r snap lim c en inp)) :
    Good a (runIn Q r snap lim c en inp) ∧
      ∀ tr, (runIn P r snap lim c en inp).traces tr ↔ (runIn Q r snap lim c en inp).traces tr := by
  cases a with
  | false =>
    exact h.run g
  | true =>
    obtain ⟨ef, nk⟩ := g
    obtain ⟨ef', same⟩ := h.run ef
    refine ⟨⟨ef', ?_⟩, same⟩
    rintro ⟨tr, sig, fs, t, mem⟩
    exact nk ⟨tr, sig, fs, (same tr).2 t, mem⟩

theorem Profile.Le.agreement (h : P.Le Q) {r : Reading} {a : Bool} {lp ls : Int}
    {plain san : Snapshot} (ag : agreement P r a lp ls plain san) :
    agreement Q r a lp ls plain san := by
  intro c₁ e₁ c₂ e₂ inp l₁ l₂ v nb
  obtain ⟨g₁, g₂, tq⟩ := ag c₁ e₁ c₂ e₂ inp (h.launch l₁) (h.launch l₂) (h.validInput v)
    (fun b => nb (h.budget b))
  obtain ⟨g₁', s₁⟩ := h.good g₁
  obtain ⟨g₂', s₂⟩ := h.good g₂
  exact ⟨g₁', g₂', fun tr => (s₁ tr).symm.trans ((tq tr).trans (s₂ tr))⟩

theorem Profile.Le.haltsWithinBudget (h : P.Le Q) {lim : Int} {S : List Word} {snap : Snapshot}
    (hb : haltsWithinBudget P lim S snap) : haltsWithinBudget Q lim S snap :=
  fun c en inp l v nb =>
    h.mustExit (hb c en inp (h.launch l) (h.validInput v) fun b => nb (h.budget b))

theorem Profile.Le.haltsMayFail (h : P.Le Q) {S : List Word} {snap : Snapshot}
    (hm : haltsMayFail P S snap) : haltsMayFail Q S snap :=
  fun c en inp l v => h.mustExit (hm c en inp (h.launch l) (h.validInput v))

theorem Profile.Le.goodInputS (h : P.Le Q) {env : SpuriousCfg} {plain san : Snapshot}
    {inp : ProcInput} (g : GoodInputS P env plain san inp) : GoodInputS Q env plain san inp := by
  intro c₁ e₁ c₂ e₂ l₁ l₂
  obtain ⟨g₁, g₂, tq⟩ := g c₁ e₁ c₂ e₂ (h.launch l₁) (h.launch l₂)
  obtain ⟨g₁', s₁⟩ := h.run g₁
  obtain ⟨g₂', s₂⟩ := h.run g₂
  exact ⟨g₁', g₂', fun tr => (s₁ tr).symm.trans ((tq tr).trans (s₂ tr))⟩

theorem Profile.Le.disagreesAtMost (h : P.Le Q) {env : SpuriousCfg} {w : FinProcInput → ℚ}
    {M : ℚ} {plain san : Snapshot} {b : ℚ} (d : disagreesAtMost P env w M plain san b) :
    disagreesAtMost Q env w M plain san b :=
  fun l nd hl => d l nd fun f mem =>
    ⟨h.validInput (hl f mem).1, fun g => (hl f mem).2 (h.goodInputS g)⟩

theorem Profile.Le.denoteComplete (h : P.Le Q) {lp ls : Int} {plain san : Snapshot}
    (shape : AgreeShape) (d : shape.denoteComplete P lp ls plain san) :
    shape.denoteComplete Q lp ls plain san := by
  cases shape <;> exact h.agreement d

/-- Narrowing only the `AT_HWCAP` domain keeps the classification statement. -/
theorem agreementDecidable_narrowHwcap {hw : HwcapDomain} (sub : ∀ x, hw x → P.hwcap x)
    {env : SpuriousCfg} {plain san : Snapshot} (d : agreementDecidable P env plain san) :
    agreementDecidable { P with hwcap := hw } env plain san := by
  obtain ⟨C, wf, cl⟩ := d
  refine ⟨C, wf, fun f vf c en l => ?_⟩
  exact cl f ⟨vf.1, sub _ vf.2.1, vf.2.2⟩ c en l

end ProfileTransfer

/-- The choice domain contains every exact launch. -/
def ExactIncluded (dom : ChoiceDomain) : Prop := ∀ inp c, X86RealisticLaunch.Exact inp c → dom inp c

theorem anyChoices_exactIncluded : ExactIncluded anyChoices := fun _ _ _ => trivial

theorem exactChoices_exactIncluded : ExactIncluded exactChoices := fun _ _ h => h

/-- On a well-formed snapshot, the launch quantifier of every shape is inhabited on every valid
input, for a profile whose choice domain contains the exact launches. -/
theorem launch_inhabited (P : Profile) (incl : ExactIncluded P.choices) (snap : Snapshot)
    (wf : Problems.NativeX86.ImageWf P.isa snap) {a : Bool} {inp : ProcInput}
    (v : ValidInput P a inp) : ∃ c en, Launch P snap c en inp := by
  obtain ⟨c, en, ve, ex⟩ := imageWf_realistic_entry P.isa snap wf inp v.1
  exact ⟨c, en, ve, incl _ _ ex⟩

/-! ## A non-exact launch refutes a statement

Unmodelled is chaos, and chaos errors (`X86RealisticLaunch.chaos` has `errors = True`). So a
profile whose launch domain holds a valid non-exact launch (a vDSO, a vsyscall page or set-id
credentials) refutes its agreement and halting statements outright: `not_agreement_of_inexact`,
`not_haltsWithinBudget_of_inexact`, `not_haltsMayFail_of_inexact`. The default profile
(`anyChoices`) admits vDSO launches (`X86RealisticLaunch.ValidVdso`), so its statements are
expected to be false until the vDSO and vsyscall pages are modelled (that a valid vDSO launch
exists on every well-formed snapshot is not proved here). The exact-launch slice
(`Profile.exactSlice`) is the meaningful target meanwhile; the default implies it
(`default_le_exactSlice`). -/

theorem runIn_not_errorFree_of_inexact (P : Profile) {r : Reading} {snap : Snapshot} {lim : Int}
    {c : Choices} {en : ExecEntry} {inp : ProcInput} (ne : ¬ X86RealisticLaunch.Exact inp c) :
    ¬ ErrorFree (runIn P r snap lim c en inp) := by
  unfold runIn
  rw [X86RealisticLaunch.runWith_not_exact _ _ _ _ _ _ _ _ ne]
  exact fun h => h trivial

theorem not_agreement_of_inexact (P : Profile) {r : Reading} {a : Bool} {lp ls : Int}
    {plain san : Snapshot} {c c' : Choices} {en en' : ExecEntry} {inp : ProcInput}
    (l : Launch P plain c en inp) (l' : Launch P san c' en' inp) (v : ValidInput P a inp)
    (ne : ¬ X86RealisticLaunch.Exact inp c) : ¬ agreement P r a lp ls plain san := by
  intro h
  obtain ⟨g, -, -⟩ := h c en c' en' inp l l' v fun b => ne b.1
  cases a with
  | false => exact runIn_not_errorFree_of_inexact P ne g
  | true => exact runIn_not_errorFree_of_inexact P ne g.1

theorem not_haltsWithinBudget_of_inexact (P : Profile) {lim : Int} {W : List Word}
    {snap : Snapshot} {c : Choices} {en : ExecEntry} {inp : ProcInput}
    (l : Launch P snap c en inp) (v : ValidInput P false inp)
    (ne : ¬ X86RealisticLaunch.Exact inp c) : ¬ haltsWithinBudget P lim W snap :=
  fun h => ne (h c en inp l v fun b => ne b.1).1

theorem not_haltsMayFail_of_inexact (P : Profile) {W : List Word} {snap : Snapshot} {c : Choices}
    {en : ExecEntry} {inp : ProcInput} (l : Launch P snap c en inp) (v : ValidInput P false inp)
    (ne : ¬ X86RealisticLaunch.Exact inp c) : ¬ haltsMayFail P W snap :=
  fun h => ne (h c en inp l v).1

/-! ## Problems -/

/-- A harness on native x86-64 with the complete table and the realistic launch: the machine,
the snapshot of each build, and the lattice point (complete table, every `AT_HWCAP` below `2^32`,
every realistic launch by default). -/
structure Problem where
  harness : Harness
  isa : UserIsa
  images : Build → Option Snapshot
  sem : Semantics := complete
  hwcap : HwcapDomain := Problems.NativeX86.anyHwcap
  choices : ChoiceDomain := anyChoices

namespace Problem

variable (p : Problem)

def profile : Profile := ⟨p.sem, p.isa, p.hwcap, p.choices⟩

/-- `k` at the snapshot of `b`, or `none` where the build has none. -/
def withImage {α : Type _} (b : Build) (k : Snapshot → α) : Option α :=
  (p.images b).map k

/-- `k` at the plain snapshot and the snapshot of `san`, or `none` where one is missing. -/
def withImages {α : Type _} (san : Build) (k : Snapshot → Snapshot → α) : Option α :=
  (p.images .plain).bind fun plain => p.withImage san (k plain)

/-- The meaning of a statement, or `none` where it is untranslated (a build without a
snapshot, or a bound statement without a distribution), as `Problems.Problem.denote?`. -/
def denote? : (s : Statement) → Option s.Sort
  | .agrees san budgets shape =>
    p.withImages san fun plain sanImg =>
      shape.denoteComplete p.profile budgets.budgets.limSource budgets.budgets.limTarget plain
        sanImg
  | .haltsWithinBudget b budgets exits =>
    p.withImage b fun img => haltsWithinBudget p.profile budgets.budgets.limSource exits.codes img
  | .haltsMayFail b exits =>
    p.withImage b fun img => haltsMayFail p.profile exits.codes img
  | .disagreesAtMost san env _ =>
    p.harness.distribution.bind fun d =>
      p.withImages san fun plain sanImg bound =>
        disagreesAtMost p.profile env.cfg d.w d.M plain sanImg bound
  | .agreementDecidable san env _ =>
    p.withImages san fun plain sanImg => agreementDecidable p.profile env.cfg plain sanImg

/-- Whether the statement is untranslated. -/
def isUntranslated (s : Statement) : Bool :=
  (s.needsDistribution && p.harness.distribution.isNone) ||
    s.builds.any fun b => (p.images b).isNone

/-- A statement has no Lean proposition exactly when it is untranslated. -/
theorem denote?_eq_none_iff (s : Statement) :
    p.denote? s = none ↔ p.isUntranslated s = true := by
  rcases s with ⟨san, _, _⟩ | ⟨b, _, _⟩ | ⟨b, _⟩ | ⟨san, _, _⟩ | ⟨san, _, _⟩ <;>
    simp only [denote?, isUntranslated, Statement.needsDistribution, Statement.builds,
      withImages, withImage, List.any_cons, List.any_nil]
  · cases p.images .plain <;> cases p.images san <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images b <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images b <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
    (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images .plain <;> cases p.images san <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h

/-- Without a distribution, a bound statement is untranslated, whatever the snapshots. -/
theorem denote?_disagreesAtMost_of_none (h : p.harness.distribution = none) (san : Build)
    (env : EnvChoice) (rv64gc : Bool) : p.denote? (.disagreesAtMost san env rv64gc) = none := by
  simp [denote?, h]

/-- An untranslated statement denotes no proposition, in particular not `False`. -/
theorem denote?_ne_some_of_untranslated {s : Statement} (h : p.isUntranslated s = true)
    (P : s.Sort) : p.denote? s ≠ some P := by
  rw [(p.denote?_eq_none_iff s).2 h]; simp

/-- Every snapshot is well formed: with it every valid input has an exact realistic launch on
every snapshot (`imagesValid_launch`). -/
def ImagesValid : Prop := ∀ b img, p.images b = some img → Problems.NativeX86.ImageWf p.isa img

theorem imagesValid_launch (v : p.ImagesValid) (incl : ExactIncluded p.choices) {b : Build}
    {img : Snapshot} (h : p.images b = some img) {a : Bool} {inp : ProcInput}
    (vi : ValidInput p.profile a inp) : ∃ c en, Launch p.profile img c en inp :=
  launch_inhabited p.profile incl img (v b img h) vi

/-- The same problem at another lattice point. -/
def withProfile (P : Profile) : Problem :=
  { p with sem := P.sem, isa := P.isa, hwcap := P.hwcap, choices := P.choices }

theorem withProfile_profile (P : Profile) : (p.withProfile P).profile = P := rfl

@[simp] theorem withProfile_images (P : Profile) : (p.withProfile P).images = p.images := rfl

@[simp] theorem withProfile_harness (P : Profile) : (p.withProfile P).harness = p.harness := rfl

end Problem

/-- Implication between statements of one sort (`NativeX86.NativeProblem.Implies`). -/
abbrev Implies := Problems.NativeX86.NativeProblem.Implies

/-- Both untranslated, or both translated with the first implying the second. -/
abbrev ImpliesOpt := Problems.NativeX86.NativeProblem.ImpliesOpt

/-- Down the lattice: every agreement, halting and bound statement over a profile implies the
same statement over a profile above it (`Profile.Le`); untranslated statements stay
untranslated. -/
theorem Problem.denote?_le (p : Problem) {Q : Profile} (h : p.profile.Le Q) (s : Statement)
    (notDecidable : ∀ san env rv, s ≠ .agreementDecidable san env rv) :
    ImpliesOpt s (p.denote? s) ((p.withProfile Q).denote? s) := by
  cases s with
  | agrees san budgets shape =>
    simp only [Problem.denote?, Problem.withImages, Problem.withImage, Problem.withProfile_profile,
      Problem.withProfile_images]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact h.denoteComplete shape
  | haltsWithinBudget b budgets exits =>
    simp only [Problem.denote?, Problem.withImage, Problem.withProfile_profile,
      Problem.withProfile_images]
    cases p.images b <;> first | trivial | exact h.haltsWithinBudget
  | haltsMayFail b exits =>
    simp only [Problem.denote?, Problem.withImage, Problem.withProfile_profile,
      Problem.withProfile_images]
    cases p.images b <;> first | trivial | exact h.haltsMayFail
  | disagreesAtMost san env rv =>
    simp only [Problem.denote?, Problem.withImages, Problem.withImage,
      Problem.withProfile_profile,
      Problem.withProfile_images, Problem.withProfile_harness]
    cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact fun b => h.disagreesAtMost
  | agreementDecidable san env rv => exact absurd rfl (notDecidable san env rv)

/-- Narrowing the `AT_HWCAP` domain: every statement, the classification one included. -/
theorem Problem.denote?_narrowHwcap (p : Problem) {hw : HwcapDomain} (sub : ∀ x, hw x → p.hwcap x)
    (s : Statement) :
    ImpliesOpt s (p.denote? s) ((p.withProfile { p.profile with hwcap := hw }).denote? s) := by
  have le : p.profile.Le { p.profile with hwcap := hw } :=
    ⟨rfl, Semantics.Below.refl _, sub, fun _ _ h => h⟩
  cases s with
  | agreementDecidable san env rv =>
    simp only [Problem.denote?, Problem.withImages, Problem.withImage, Problem.withProfile_profile,
      Problem.withProfile_images]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact agreementDecidable_narrowHwcap sub
  | _ => exact p.denote?_le le _ (by intro _ _ _ h; cases h)

/-! ### The lattice points used by the generated modules -/

/-- The exact-launch slice of a profile. -/
def Profile.exactSlice (P : Profile) : Profile := { P with choices := exactChoices }

/-- A profile whose launch domain contains the exact launches is above its exact slice. -/
theorem Profile.le_exactSlice (P : Profile) (incl : ExactIncluded P.choices) :
    P.Le P.exactSlice :=
  ⟨rfl, Semantics.Below.refl _, fun _ h => h, fun inp c h => incl inp c h⟩

/-- The default profile is above the exact-launch slice. -/
theorem default_le_exactSlice (isa : UserIsa) :
    (Profile.default isa).Le (Profile.default isa).exactSlice :=
  ⟨rfl, Semantics.Below.refl _, fun _ h => h, fun _ _ _ => trivial⟩

/-- The default profile is above the `AT_HWCAP = 0` slice. -/
theorem default_le_noHwcap (isa : UserIsa) :
    (Profile.default isa).Le { Profile.default isa with hwcap := Problems.NativeX86.noHwcap } :=
  ⟨rfl, Semantics.Below.refl _, fun _ _ => trivial, fun _ _ h => h⟩

/-- The default profile is above the families' exact arms. -/
theorem default_le_exact (isa : UserIsa) :
    (Profile.default isa).Le { Profile.default isa with sem := exact } :=
  ⟨rfl, complete_below_exact, fun _ h => h, fun _ _ h => h⟩

/-- The default profile is above the gap-sweep variant. -/
theorem default_le_gap (isa : UserIsa) :
    (Profile.default isa).Le { Profile.default isa with sem := gap } :=
  ⟨rfl, complete_below_gap, fun _ h => h, fun _ _ h => h⟩

end Silmaril.Process.LPS.Problems.NativeX86Complete
