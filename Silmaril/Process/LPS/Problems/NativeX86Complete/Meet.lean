module

public import Silmaril.Process.LPS.Problems.NativeX86Complete

/-!
# The meet of the complete and the reviewed-default x86-64 statements

`Problems.NativeX86` states the x86-64 statements over the reviewed-default table and the minimal
launch (`X86Launch`); `Problems.NativeX86Complete` states them over the complete system and the
realistic launch (`X86RealisticLaunch`). Neither implies the other: neither table restricts the
other (`NativeX86Complete.Census`), and the launches are different. This file states them over
the meet of both:

* the table is `meetDefault` (`Semantics.meet`): the complete system where it agrees with the
  reviewed default, `unmodeled` elsewhere (the reviewed default's pending calls, the complete
  system's `TASK_SIZE_MAX` band, and any other difference). It is the greatest lower bound of the
  two for `Semantics.Below` (`below_meet`);
* the launches are both domains at once (`AnyLaunch`): a minimal launch, with the minimal
  domain's valid inputs, or a realistic one, with the realistic domain's. An agreement statement
  ranges over every pair of launches, mixed pairs included.

Both families are corollaries (`JointProblem.implies_complete`,
`JointProblem.implies_reviewedDefault`): every agreement, halting and bound statement of the meet
implies the same statement over the complete system and the realistic launch, and the same
statement over the reviewed-default table and the minimal launch; untranslated statements stay
untranslated. `agreementDecidable` (a classifier exits `0` exactly where the builds agree) is
not monotone in the table or the launches, since its right-hand side moves with them; the meet
states it as the conjunction of the two families' classification statements, so it implies both
as well.

So a proof of a meet statement proves both families' statement. The converse fails in general:
the meet statement is stronger than the conjunction of the two (mixed launch pairs, and a table
that declines more).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86Complete

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

/-! ## Minimal launches over a semantics, and transfer -/

section Minimal

variable {S T : Semantics} {isa : UserIsa} {r : Reading} {snap : Snapshot} {lim : Int}
  {en : ExecEntry} {inp : ProcInput}

theorem Semantics.Below.minimalRun (h : S.Below T)
    (ef : ErrorFree (X86Launch.runWith isa (S.spec r) (S.refused r) snap lim en inp)) :
    ErrorFree (X86Launch.runWith isa (T.spec r) (T.refused r) snap lim en inp) ∧
      ∀ tr, (X86Launch.runWith isa (S.spec r) (S.refused r) snap lim en inp).traces tr ↔
        (X86Launch.runWith isa (T.spec r) (T.refused r) snap lim en inp).traces tr := by
  simp only [X86Launch.runWith] at ef ⊢
  exact ⟨errorFree_of_restricts (h r).1 (h r).2 ef,
    fun tr => obsTrace_eq_of_errorFree (h r).1 (h r).2 ef tr⟩

theorem Semantics.Below.minimalGood (h : S.Below T) {a : Bool}
    (g : Good a (X86Launch.runWith isa (S.spec r) (S.refused r) snap lim en inp)) :
    Good a (X86Launch.runWith isa (T.spec r) (T.refused r) snap lim en inp) ∧
      ∀ tr, (X86Launch.runWith isa (S.spec r) (S.refused r) snap lim en inp).traces tr ↔
        (X86Launch.runWith isa (T.spec r) (T.refused r) snap lim en inp).traces tr := by
  cases a with
  | false => exact h.minimalRun g
  | true =>
    obtain ⟨ef, nk⟩ := g
    obtain ⟨ef', same⟩ := h.minimalRun ef
    refine ⟨⟨ef', ?_⟩, same⟩
    rintro ⟨tr, sig, fs, t, mem⟩
    exact nk ⟨tr, sig, fs, (same tr).2 t, mem⟩

theorem Semantics.Below.minimalBudget (h : S.Below T)
    (b : NativeX86.RunBudgetRefusedWithStack isa X86Launch.entryStack (S.spec r) (S.refused r)
      snap.image lim en inp) :
    NativeX86.RunBudgetRefusedWithStack isa X86Launch.entryStack (T.spec r) (T.refused r)
      snap.image lim en inp :=
  runBudgetRefusedFromUsing_mono (h r).1 (h r).2 b

theorem Semantics.Below.minimalMustExit (h : S.Below T) {W : List Word}
    (m : MustExitInAt snap.image.segments (S.spec r) (S.refused r) W
      (X86Launch.init isa snap en lim inp)) :
    MustExitInAt snap.image.segments (T.spec r) (T.refused r) W
      (X86Launch.init isa snap en lim inp) :=
  mustExitInAt_of_restricts (h r).1 (h r).2 m

end Minimal

/-! ## Joint launches -/

/-- A launch of either domain: a minimal one (`X86Launch`, an entry) or a realistic one
(`X86RealisticLaunch`, a choice and an entry). -/
inductive AnyLaunch where
  | minimal (en : ExecEntry)
  | realistic (c : Choices) (en : ExecEntry)

/-- A point for the joint statements: the semantics, the machine, the `AT_HWCAP` domain of the
minimal launches, and the `AT_HWCAP` and choice domains of the realistic ones. -/
structure JointProfile where
  sem : Semantics
  isa : UserIsa
  minimalHwcap : HwcapDomain
  hwcap : HwcapDomain
  choices : ChoiceDomain

namespace JointProfile

variable (J : JointProfile)

/-- The realistic part, a `Profile`. -/
def realistic : Profile := ⟨J.sem, J.isa, J.hwcap, J.choices⟩

/-- The launch fits the snapshot. -/
def Entry (snap : Snapshot) : AnyLaunch → ProcInput → Prop
  | .minimal en, inp => X86Launch.ValidEntry J.isa snap en inp
  | .realistic c en, inp => Launch J.realistic snap c en inp

/-- The input is valid in the launch's domain. -/
def ValidAt (a : Bool) : AnyLaunch → ProcInput → Prop
  | .minimal _, inp => NativeX86.ValidInput J.minimalHwcap a inp
  | .realistic _ _, inp => ValidInput J.realistic a inp

/-- The run of a launch. -/
def run (r : Reading) (snap : Snapshot) (lim : Int) : AnyLaunch → ProcInput → Behavior
  | .minimal en, inp => X86Launch.runWith J.isa (J.sem.spec r) (J.sem.refused r) snap lim en inp
  | .realistic c en, inp => runIn J.realistic r snap lim c en inp

/-- Refusal for budget of a launch. -/
def BudgetRefused (r : Reading) (snap : Snapshot) (lim : Int) : AnyLaunch → ProcInput → Prop
  | .minimal en, inp =>
    NativeX86.RunBudgetRefusedWithStack J.isa X86Launch.entryStack (J.sem.spec r)
      (J.sem.refused r) snap.image lim en inp
  | .realistic c en, inp => BudgetRefusedIn J.realistic r snap lim c en inp

/-- Must-exit of a launch. -/
def MustExit (r : Reading) (W : List Word) (snap : Snapshot) (lim : Int) :
    AnyLaunch → ProcInput → Prop
  | .minimal en, inp =>
    MustExitInAt snap.image.segments (J.sem.spec r) (J.sem.refused r) W
      (X86Launch.init J.isa snap en lim inp)
  | .realistic c en, inp => MustExitIn J.realistic r W snap lim c en inp

/-- The agreement conclusion, over every pair of launches. -/
def agreement (r : Reading) (a : Bool) (limPlain limSan : Int) (plain san : Snapshot) : Prop :=
  ∀ (L₁ L₂ : AnyLaunch) (inp : ProcInput),
    J.Entry plain L₁ inp → J.Entry san L₂ inp → J.ValidAt a L₁ inp → J.ValidAt a L₂ inp →
    ¬ J.BudgetRefused r plain limPlain L₁ inp →
    Good a (J.run r plain limPlain L₁ inp) ∧ Good a (J.run r san limSan L₂ inp) ∧
      TraceEquiv (J.run r plain limPlain L₁ inp).traces (J.run r san limSan L₂ inp).traces

/-- `Shapes.haltsWithinBudget`, over every launch. -/
def haltsWithinBudget (lim : Int) (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (L : AnyLaunch) (inp : ProcInput), J.Entry snap L inp → J.ValidAt false L inp →
    ¬ J.BudgetRefused (some forcedOnlyCfg) snap lim L inp →
    J.MustExit (some forcedOnlyCfg) allowed snap lim L inp

/-- `Shapes.haltsMayFail`, over every launch. -/
def haltsMayFail (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (L : AnyLaunch) (inp : ProcInput), J.Entry snap L inp → J.ValidAt false L inp →
    J.MustExit (some mayFailCfg) allowed snap sourceAllocLimit L inp

/-- The valid finite inputs of either domain. -/
def ValidFinInput (f : FinProcInput) : Prop :=
  NativeX86.ValidInput J.minimalHwcap false f.toProcInput ∨ NativeX86Complete.ValidFinInput J.realistic f

/-- `GoodInputS`, over every pair of launches. -/
def GoodInputS (env : SpuriousCfg) (plain san : Snapshot) (inp : ProcInput) : Prop :=
  ∀ L₁ L₂, J.Entry plain L₁ inp → J.Entry san L₂ inp →
    ErrorFree (J.run (some env) plain sourceAllocLimit L₁ inp) ∧
      ErrorFree (J.run (some env) san targetAllocLimit L₂ inp) ∧
      TraceEquiv (J.run (some env) plain sourceAllocLimit L₁ inp).traces
        (J.run (some env) san targetAllocLimit L₂ inp).traces

/-- `Shapes.disagreesAtMost`. -/
def disagreesAtMost (env : SpuriousCfg) (w : FinProcInput → ℚ) (M : ℚ) (plain san : Snapshot)
    (b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup →
    (∀ f ∈ l, J.ValidFinInput f ∧ ¬ J.GoodInputS env plain san f.toProcInput) →
    sumWeights w l ≤ b * M

/-- The meaning of an agreement shape (as `AgreeShape.denoteComplete`). -/
def denoteAgree (limP limS : Int) (plain san : Snapshot) : AgreeShape → Prop
  | .agrees | .rv64gc => J.agreement none false limP limS plain san
  | .agreesIn env | .inRv64gc env => J.agreement (some env.cfg) false limP limS plain san
  | .abortModelled | .abortModelledRv64gc => J.agreement none true limP limS plain san
  | .inAbortModelled env => J.agreement (some env.cfg) true limP limS plain san

/-! ### Restriction to the realistic launches -/

variable {J}

theorem agreement.realistic {r : Reading} {a : Bool} {lp ls : Int} {plain san : Snapshot}
    (h : J.agreement r a lp ls plain san) :
    NativeX86Complete.agreement J.realistic r a lp ls plain san :=
  fun c₁ e₁ c₂ e₂ inp l₁ l₂ v nb =>
    h (.realistic c₁ e₁) (.realistic c₂ e₂) inp l₁ l₂ v v nb

theorem haltsWithinBudget.realistic {lim : Int} {W : List Word} {snap : Snapshot}
    (h : J.haltsWithinBudget lim W snap) :
    NativeX86Complete.haltsWithinBudget J.realistic lim W snap :=
  fun c en inp l v nb => h (.realistic c en) inp l v nb

theorem haltsMayFail.realistic {W : List Word} {snap : Snapshot} (h : J.haltsMayFail W snap) :
    NativeX86Complete.haltsMayFail J.realistic W snap :=
  fun c en inp l v => h (.realistic c en) inp l v

theorem GoodInputS.of_realistic {env : SpuriousCfg} {plain san : Snapshot} {inp : ProcInput}
    (h : J.GoodInputS env plain san inp) :
    NativeX86Complete.GoodInputS J.realistic env plain san inp :=
  fun c₁ e₁ c₂ e₂ l₁ l₂ => h (.realistic c₁ e₁) (.realistic c₂ e₂) l₁ l₂

theorem disagreesAtMost.realistic {env : SpuriousCfg} {w : FinProcInput → ℚ} {M : ℚ}
    {plain san : Snapshot} {b : ℚ} (h : J.disagreesAtMost env w M plain san b) :
    NativeX86Complete.disagreesAtMost J.realistic env w M plain san b :=
  fun l nd hl => h l nd fun f mem =>
    ⟨.inr (hl f mem).1, fun g => (hl f mem).2 (GoodInputS.of_realistic g)⟩

theorem denoteAgree.realistic {lp ls : Int} {plain san : Snapshot} (shape : AgreeShape)
    (h : J.denoteAgree lp ls plain san shape) : shape.denoteComplete J.realistic lp ls plain san := by
  cases shape <;> exact agreement.realistic h

/-! ### Restriction to the minimal launches, and transfer to the reviewed default -/

variable (hb : J.sem.Below reviewedDefault)
include hb

theorem agreement.minimal {r : Reading} {a : Bool} {lp ls : Int} {plain san : Snapshot}
    (h : J.agreement r a lp ls plain san) :
    NativeX86.agreement J.isa J.isa J.minimalHwcap r a lp ls plain san := by
  intro e₁ e₂ inp v₁ v₂ vi nb
  obtain ⟨g₁, g₂, tq⟩ := h (.minimal e₁) (.minimal e₂) inp v₁ v₂ vi vi
    (fun b => nb (hb.minimalBudget b))
  obtain ⟨g₁', s₁⟩ := hb.minimalGood g₁
  obtain ⟨g₂', s₂⟩ := hb.minimalGood g₂
  exact ⟨g₁', g₂', fun tr => (s₁ tr).symm.trans ((tq tr).trans (s₂ tr))⟩

theorem haltsWithinBudget.minimal {lim : Int} {W : List Word} {snap : Snapshot}
    (h : J.haltsWithinBudget lim W snap) :
    NativeX86.haltsWithinBudget J.isa J.minimalHwcap lim W snap :=
  fun en inp l v nb =>
    hb.minimalMustExit (h (.minimal en) inp l v fun b => nb (hb.minimalBudget b))

theorem haltsMayFail.minimal {W : List Word} {snap : Snapshot} (h : J.haltsMayFail W snap) :
    NativeX86.haltsMayFail J.isa J.minimalHwcap W snap :=
  fun en inp l v => hb.minimalMustExit (h (.minimal en) inp l v)

theorem GoodInputS.of_minimal {env : SpuriousCfg} {plain san : Snapshot} {inp : ProcInput}
    (h : J.GoodInputS env plain san inp) : NativeX86.GoodInputS J.isa env plain san inp := by
  intro e₁ e₂ l₁ l₂
  obtain ⟨g₁, g₂, tq⟩ := h (.minimal e₁) (.minimal e₂) l₁ l₂
  obtain ⟨g₁', s₁⟩ := hb.minimalRun g₁
  obtain ⟨g₂', s₂⟩ := hb.minimalRun g₂
  exact ⟨g₁', g₂', fun tr => (s₁ tr).symm.trans ((tq tr).trans (s₂ tr))⟩

theorem disagreesAtMost.minimal {env : SpuriousCfg} {w : FinProcInput → ℚ} {M : ℚ}
    {plain san : Snapshot} {b : ℚ} (h : J.disagreesAtMost env w M plain san b) :
    NativeX86.disagreesAtMost J.isa J.minimalHwcap env w M plain san b :=
  fun l nd hl => h l nd fun f mem =>
    ⟨.inl (hl f mem).1, fun g => (hl f mem).2 (GoodInputS.of_minimal hb g)⟩

theorem denoteAgree.minimal {lp ls : Int} {plain san : Snapshot} (shape : AgreeShape)
    (h : J.denoteAgree lp ls plain san shape) :
    shape.denoteX86 J.isa J.isa J.minimalHwcap lp ls plain san := by
  cases shape <;> exact agreement.minimal hb h

end JointProfile

/-! ## Joint problems -/

/-- A harness with the statements over the meet: by default the meet table `meetDefault`, every
`AT_HWCAP` for both launch domains, and every realistic launch. -/
structure JointProblem where
  harness : Harness
  isa : UserIsa
  images : Build → Option Snapshot
  sem : Semantics := meetDefault
  minimalHwcap : HwcapDomain := Problems.NativeX86.anyHwcap
  hwcap : HwcapDomain := Problems.NativeX86.anyHwcap
  choices : ChoiceDomain := anyChoices

namespace JointProblem

variable (p : JointProblem)

def profile : JointProfile := ⟨p.sem, p.isa, p.minimalHwcap, p.hwcap, p.choices⟩

/-- The statements over the complete system and the realistic launch, with the same domains. -/
def complete : Problem where
  harness := p.harness
  isa := p.isa
  images := p.images
  sem := NativeX86Complete.complete
  hwcap := p.hwcap
  choices := p.choices

/-- The statements over the reviewed-default table and the minimal launch. -/
def reviewedDefault : Problems.NativeX86.NativeProblem where
  harness := p.harness
  isa := p.isa
  images := p.images
  hwcap := p.minimalHwcap

/-- `k` at the snapshot of `b`, or `none` where the build has none. -/
def withImage {α : Type _} (b : Build) (k : Snapshot → α) : Option α :=
  (p.images b).map k

/-- `k` at the plain snapshot and the snapshot of `san`, or `none` where one is missing. -/
def withImages {α : Type _} (san : Build) (k : Snapshot → Snapshot → α) : Option α :=
  (p.images .plain).bind fun plain => p.withImage san (k plain)

/-- The meaning of a statement over the meet, or `none` where it is untranslated (as
`Problem.denote?`). The classification statement is the conjunction of both families'. -/
def denote? : (s : Statement) → Option s.Sort
  | .agrees san budgets shape =>
    p.withImages san fun plain sanImg =>
      p.profile.denoteAgree budgets.budgets.limSource budgets.budgets.limTarget plain sanImg shape
  | .haltsWithinBudget b budgets exits =>
    p.withImage b fun img => p.profile.haltsWithinBudget budgets.budgets.limSource exits.codes img
  | .haltsMayFail b exits =>
    p.withImage b fun img => p.profile.haltsMayFail exits.codes img
  | .disagreesAtMost san env _ =>
    p.harness.distribution.bind fun d =>
      p.withImages san fun plain sanImg bound =>
        p.profile.disagreesAtMost env.cfg d.w d.M plain sanImg bound
  | .agreementDecidable san env _ =>
    p.withImages san fun plain sanImg =>
      agreementDecidable p.complete.profile env.cfg plain sanImg ∧
        Problems.NativeX86.agreementDecidable p.isa p.minimalHwcap env.cfg plain sanImg

/-- The meet statements imply the statements over the complete system and the realistic launch
(the table below the complete one; the same domains). -/
theorem implies_complete (hc : p.sem.Below NativeX86Complete.complete) (s : Statement) :
    ImpliesOpt s (p.denote? s) (p.complete.denote? s) := by
  have le : p.profile.realistic.Le p.complete.profile :=
    ⟨rfl, hc, fun _ h => h, fun _ _ h => h⟩
  cases s with
  | agrees san budgets shape =>
    simp only [denote?, Problem.denote?, withImages, withImage, Problem.withImages,
      Problem.withImage, complete]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact fun h => le.denoteComplete shape (JointProfile.denoteAgree.realistic shape h)
  | haltsWithinBudget b budgets exits =>
    simp only [denote?, Problem.denote?, withImage, Problem.withImage, complete]
    cases p.images b <;>
      first | trivial | exact fun h => le.haltsWithinBudget (JointProfile.haltsWithinBudget.realistic h)
  | haltsMayFail b exits =>
    simp only [denote?, Problem.denote?, withImage, Problem.withImage, complete]
    cases p.images b <;>
      first | trivial | exact fun h => le.haltsMayFail (JointProfile.haltsMayFail.realistic h)
  | disagreesAtMost san env rv =>
    simp only [denote?, Problem.denote?, withImages, withImage, Problem.withImages,
      Problem.withImage, complete]
    cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
      first | trivial |
        exact fun _ h => le.disagreesAtMost (JointProfile.disagreesAtMost.realistic h)
  | agreementDecidable san env rv =>
    simp only [denote?, Problem.denote?, withImages, withImage, Problem.withImages,
      Problem.withImage, complete]
    cases p.images .plain <;> cases p.images san <;> first | trivial | exact fun h => h.1

/-- The meet statements imply the reviewed-default statements over the minimal launch (the table
below the reviewed default). -/
theorem implies_reviewedDefault (hb : p.sem.Below NativeX86Complete.reviewedDefault)
    (s : Statement) :
    Problems.NativeX86.NativeProblem.ImpliesOpt s (p.denote? s) (p.reviewedDefault.denote? s) := by
  have hb' : p.profile.sem.Below NativeX86Complete.reviewedDefault := hb
  cases s with
  | agrees san budgets shape =>
    simp only [denote?, Problems.NativeX86.NativeProblem.denote?, withImages, withImage,
      Problems.NativeX86.NativeProblem.withImages, Problems.NativeX86.NativeProblem.withImage,
      reviewedDefault]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact JointProfile.denoteAgree.minimal hb' shape
  | haltsWithinBudget b budgets exits =>
    simp only [denote?, Problems.NativeX86.NativeProblem.denote?, withImage,
      Problems.NativeX86.NativeProblem.withImage, reviewedDefault]
    cases p.images b <;> first | trivial | exact JointProfile.haltsWithinBudget.minimal hb'
  | haltsMayFail b exits =>
    simp only [denote?, Problems.NativeX86.NativeProblem.denote?, withImage,
      Problems.NativeX86.NativeProblem.withImage, reviewedDefault]
    cases p.images b <;> first | trivial | exact JointProfile.haltsMayFail.minimal hb'
  | disagreesAtMost san env rv =>
    simp only [denote?, Problems.NativeX86.NativeProblem.denote?, withImages, withImage,
      Problems.NativeX86.NativeProblem.withImages, Problems.NativeX86.NativeProblem.withImage,
      reviewedDefault]
    cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact fun _ => JointProfile.disagreesAtMost.minimal hb'
  | agreementDecidable san env rv =>
    simp only [denote?, Problems.NativeX86.NativeProblem.denote?, withImages, withImage,
      Problems.NativeX86.NativeProblem.withImages, Problems.NativeX86.NativeProblem.withImage,
      reviewedDefault]
    cases p.images .plain <;> cases p.images san <;> first | trivial | exact fun h => h.2

end JointProblem

/-! ## The default meet -/

/-- The default meet problem of a harness: `meetDefault`, every `AT_HWCAP`, every launch. -/
def JointProblem.ofImages (harness : Harness) (isa : UserIsa) (images : Build → Option Snapshot) :
    JointProblem :=
  { harness, isa, images }

/-- Its complete part is the default complete problem. -/
theorem JointProblem.ofImages_complete (harness : Harness) (isa : UserIsa)
    (images : Build → Option Snapshot) :
    (JointProblem.ofImages harness isa images).complete = { harness, isa, images } := rfl

/-- Its reviewed-default part is the default reviewed-default problem. -/
theorem JointProblem.ofImages_reviewedDefault (harness : Harness) (isa : UserIsa)
    (images : Build → Option Snapshot) :
    (JointProblem.ofImages harness isa images).reviewedDefault = { harness, isa, images } := rfl

/-- Every default meet statement implies the default complete statement. -/
theorem JointProblem.ofImages_implies_complete (harness : Harness) (isa : UserIsa)
    (images : Build → Option Snapshot) (s : Statement) :
    ImpliesOpt s ((JointProblem.ofImages harness isa images).denote? s)
      (({ harness, isa, images } : Problem).denote? s) :=
  (JointProblem.ofImages harness isa images).implies_complete meetDefault_below_complete s

/-- Every default meet statement implies the default reviewed-default statement. -/
theorem JointProblem.ofImages_implies_reviewedDefault (harness : Harness) (isa : UserIsa)
    (images : Build → Option Snapshot) (s : Statement) :
    Problems.NativeX86.NativeProblem.ImpliesOpt s
      ((JointProblem.ofImages harness isa images).denote? s)
      (({ harness, isa, images } : Problems.NativeX86.NativeProblem).denote? s) :=
  (JointProblem.ofImages harness isa images).implies_reviewedDefault
    meetDefault_below_reviewedDefault s

end Silmaril.Process.LPS.Problems.NativeX86Complete
