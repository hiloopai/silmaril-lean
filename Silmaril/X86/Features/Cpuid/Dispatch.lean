module

public import Silmaril.X86.Features.Cpuid.Extension

/-!
# Verifying code that dispatches on CPUID

Code reads CPUID (and, for AVX-class features, XGETBV), tests feature bits, and
branches to an implementation that needs the features it tested. On a
*consistent* profile (`Profile.Consistent`: the features the semantics enforce
are the ones CPUID and XCR0 report) the tests are exactly membership in
`p.features`:

* `Profile.has_eq`: `p.features.has f` is the bit, the leaf being in range and,
  for features with OS-managed state, OSXSAVE and the XCR0 components.
* `Profile.leafAvailable_one`: on an x86-64 profile (`baseline64 ⊆ p.features`)
  leaf 1 is in range, so for leaf-1 features without OS state the bit alone
  decides (`mem_iff_bit_one`, `bit_one_eq_has`).
* `Profile.mem_iff_bit` (any leaf in range), `mem_iff_xcr0` (AVX class: bit,
  OSXSAVE and XCR0), `leafAvailable_of_le` (the maximum-leaf check of leaf 0).
* `and_twoPow_ne_zero`, `and_mask_ne_zero`: the `test`/`and` with the bit mask
  that compiled code performs is the bit.
* `Profile.cpuid_cases`: the case split a dispatch proof makes. Each branch
  gets the value of the tested bit *and* the membership of the feature. The
  tactic `cpuid_cases hp hb f with hbit hmem` performs it for a leaf-1 feature
  without OS state; `cpuid_cases' hp hl f with hbit hmem` for any leaf, given
  the leaf is available.

## The path lemma

`Observed p f` is what a path that tested `f` knows. On a consistent profile an
observed feature is present (`Observed.mem`), so an instruction that requires
only observed features never raises `featureUD` (`extStep_ne_featureUD`,
`baseCheck_eq_none`), and a branch that is `FeatureFree` for the observed
features (`Observed.set`) behaves the same on the profile's full feature set
(`dispatch_same_behaviour`). The proof of a branch is therefore done once, for
the features it tested, and holds on every consistent profile that passes the
test; the other branch is proved for the features of the fallback.

The headline shape of a dispatch theorem is

  `∀ p : Profile, p.Consistent → baseline64 ⊆ p.features → <program meets spec on p>`

proved by `cpuid_cases hp hb .popcnt with hbit hmem` at the branch:
`Checks.lean` in this directory and the `popcount-dispatch` problem do this.
-/

@[expose] public section

namespace Silmaril.X86.Features

open FeatureSet (leafAvailable baseline64)

/-! ## Bit tests -/

theorem and_twoPow_ne_zero {w i : Nat} (h : i < w) (v : BitVec w) :
    v &&& BitVec.twoPow w i ≠ 0 ↔ v.getLsbD i = true := by
  rw [BitVec.and_twoPow]
  split
  · rename_i hv
    simp only [hv, iff_true]
    intro h0
    have := congrArg (·.getLsbD i) h0
    simp [h] at this
  · simp_all

/-- A test against a literal one-bit mask is the bit. -/
theorem and_mask_ne_zero {w : Nat} (i : Nat) (h : i < w) (v mask : BitVec w)
    (hm : mask = BitVec.twoPow w i) : v &&& mask ≠ 0 ↔ v.getLsbD i = true := by
  subst hm; exact and_twoPow_ne_zero h v

/-! ## Membership as code observes it -/

/-- Every feature is enumerated in subleaf 0. -/
theorem Feature.subleaf_eq_zero (f : Feature) : f.cpuid.subleaf = 0 := by cases f <;> rfl

namespace Profile

variable {p : Profile}

/-- The membership of a feature in a consistent profile, as code can test it. -/
theorem has_eq (hp : p.Consistent) (f : Feature) :
    p.features.has f =
      (leafAvailable p.cpuid f.cpuid.leaf &&
        (f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit &&
        (f.xcr0 == 0 || (p.osxsave && (p.xcr0 &&& f.xcr0) == f.xcr0))) := by
  rw [← hp, ← Feature.subleaf_eq_zero f]; rfl

/-- On an x86-64 profile, CPUID leaf 1 is in range. -/
theorem leafAvailable_one (hp : p.Consistent) (hb : baseline64 ⊆ p.features) :
    leafAvailable p.cpuid 1 = true := by
  have h := hb .sse2 (by decide)
  rw [FeatureSet.mem_iff, has_eq hp] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- A basic leaf is in range when leaf 0 reports a maximum leaf at least as large. -/
theorem leafAvailable_of_le {leaf : BitVec 32} (hl : leaf < 0x80000000#32)
    (h : leaf ≤ (p.cpuid 0 0).eax) : leafAvailable p.cpuid leaf = true := by
  simp only [leafAvailable, hl, ite_true, decide_eq_true_eq]
  exact h

/-- A feature without OS-managed state, its leaf in range: present iff its bit is set. -/
theorem mem_iff_bit (hp : p.Consistent) {f : Feature}
    (hl : leafAvailable p.cpuid f.cpuid.leaf = true) (h0 : f.xcr0 = 0) :
    f ∈ p.features ↔ (f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit = true := by
  rw [FeatureSet.mem_iff, has_eq hp, hl, h0]
  simp

/-- An AVX-class feature: present iff its bit, OSXSAVE and the XCR0 components. -/
theorem mem_iff_xcr0 (hp : p.Consistent) {f : Feature}
    (hl : leafAvailable p.cpuid f.cpuid.leaf = true) (h0 : f.xcr0 ≠ 0) :
    f ∈ p.features ↔ (f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit = true ∧
      p.osxsave = true ∧ p.xcr0 &&& f.xcr0 = f.xcr0 := by
  rw [FeatureSet.mem_iff, has_eq hp, hl]
  simp only [Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, h0, false_or]

/-- A leaf-1 feature without OS state, on an x86-64 profile: the bit alone decides. -/
theorem mem_iff_bit_one (hp : p.Consistent) (hb : baseline64 ⊆ p.features) {f : Feature}
    (h1 : f.cpuid.leaf = 1) (h0 : f.xcr0 = 0) :
    f ∈ p.features ↔ (f.cpuid.reg.get (p.cpuid 1 0)).getLsbD f.cpuid.bit = true := by
  rw [mem_iff_bit hp (h1 ▸ leafAvailable_one hp hb) h0, h1]

theorem bit_one_eq_has (hp : p.Consistent) (hb : baseline64 ⊆ p.features) {f : Feature}
    (h1 : f.cpuid.leaf = 1) (h0 : f.xcr0 = 0) :
    (f.cpuid.reg.get (p.cpuid 1 0)).getLsbD f.cpuid.bit = p.features.has f := by
  have := mem_iff_bit_one hp hb h1 h0
  rw [FeatureSet.mem_iff] at this
  cases h : p.features.has f <;> simp_all

/-- The case split of a dispatch: the tested bit and the membership agree. -/
theorem cpuid_cases (hp : p.Consistent) {f : Feature}
    (hl : leafAvailable p.cpuid f.cpuid.leaf = true) (h0 : f.xcr0 = 0) :
    ((f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit = true ∧ f ∈ p.features) ∨
      ((f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit = false ∧
        f ∉ p.features) := by
  have := mem_iff_bit hp hl h0
  cases h : (f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit
  · right; exact ⟨rfl, by simp_all⟩
  · left; exact ⟨rfl, by simp_all⟩

/-- The case split for a leaf-1 feature on an x86-64 profile. -/
theorem cpuid_cases_one (hp : p.Consistent) (hb : baseline64 ⊆ p.features) {f : Feature}
    (h1 : f.cpuid.leaf = 1) (h0 : f.xcr0 = 0) :
    ((f.cpuid.reg.get (p.cpuid 1 0)).getLsbD f.cpuid.bit = true ∧ f ∈ p.features) ∨
      ((f.cpuid.reg.get (p.cpuid 1 0)).getLsbD f.cpuid.bit = false ∧ f ∉ p.features) := by
  have := cpuid_cases hp (h1 ▸ leafAvailable_one hp hb) h0
  rwa [h1] at this

/-- POPCNT: `CPUID.(EAX=1,ECX=0):ECX & 0x800000 ≠ 0` iff the profile executes POPCNT. -/
theorem popcnt_test (hp : p.Consistent) (hb : baseline64 ⊆ p.features) :
    (p.cpuid 1 0).ecx &&& 0x800000#32 ≠ 0 ↔ Feature.popcnt ∈ p.features := by
  rw [and_mask_ne_zero 23 (by decide) _ _ (by decide),
    mem_iff_bit_one hp hb (f := .popcnt) rfl rfl]
  rfl

/-! ## The path lemma -/

/-- What a path that tested feature `f` knows: its leaf is in range, its bit is
set and, for a feature with OS-managed state, OSXSAVE is set and XCR0 enables
the components. -/
def Observed (p : Profile) (f : Feature) : Prop :=
  leafAvailable p.cpuid f.cpuid.leaf = true ∧
    (f.cpuid.reg.get (p.cpuid f.cpuid.leaf 0)).getLsbD f.cpuid.bit = true ∧
    (f.xcr0 = 0 ∨ (p.osxsave = true ∧ p.xcr0 &&& f.xcr0 = f.xcr0))

/-- On a consistent profile an observed feature is executed. -/
theorem Observed.mem (hp : p.Consistent) {f : Feature} (h : p.Observed f) : f ∈ p.features := by
  obtain ⟨hl, hbit, hx⟩ := h
  rw [FeatureSet.mem_iff, has_eq hp, hl, hbit]
  rcases hx with h0 | ⟨ho, hm⟩
  · simp [h0]
  · simp [ho, hm]

/-- And conversely, every executed feature is observable. -/
theorem observed_of_mem (hp : p.Consistent) {f : Feature} (h : f ∈ p.features) : p.Observed f := by
  rw [FeatureSet.mem_iff, has_eq hp] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hl, hbit⟩, hx⟩ := h
  exact ⟨hl, hbit, hx.imp id fun h => ⟨h.1, h.2⟩⟩

theorem observed_iff (hp : p.Consistent) {f : Feature} : p.Observed f ↔ f ∈ p.features :=
  ⟨Observed.mem hp, observed_of_mem hp⟩

/-- The features a path observed, with the x86-64 baseline. -/
def Observed.set (fs : List Feature) : FeatureSet := baseline64 ∪ FeatureSet.ofList fs

theorem Observed.set_subset (hp : p.Consistent) (hb : baseline64 ⊆ p.features)
    {fs : List Feature} (hobs : ∀ f ∈ fs, p.Observed f) : Observed.set fs ⊆ p.features := by
  intro f hf
  rcases (FeatureSet.mem_union _ _ f).mp hf with h | h
  · exact hb f h
  · exact (hobs f ((FeatureSet.mem_ofList fs f).mp h)).mem hp

/-- An extension instruction requiring only observed features does not raise #UD
for a missing feature. -/
theorem extStep_ne_featureUD (hp : p.Consistent) {e : Extension} {x : e.Syntax} {n : Nat}
    {m : MState} (hobs : ∀ f ∈ e.requires x, p.Observed f) (g : Feature) :
    extStep p.features e x n m ≠ .featureUD g := by
  have hm : p.features.missing (e.requires x) = none :=
    FeatureSet.missing_eq_none_iff.mpr fun f hf => (hobs f hf).mem hp
  unfold extStep
  rw [hm]
  simp only
  split <;> nofun

/-- An integer instruction whose feature (POPCNT, LZCNT, BMI1) was observed passes
its feature check. -/
theorem baseCheck_eq_none (hp : p.Consistent) {i : Ext.Instr}
    (hobs : ∀ f a, baseRequirement i = some (f, a) → p.Observed f) :
    baseCheck p.features i = none := by
  unfold baseCheck
  split
  · rename_i f a hr
    simp [show p.features.has f = true from (hobs f a hr).mem hp]
  · rfl

/-- **Dispatch transfer.** A branch that is feature-free for the features its path
observed (with the baseline) behaves the same on the profile's full feature set:
same runs, same outcome at every reachable state, same returns. -/
theorem dispatch_same_behaviour (hp : p.Consistent) (hb : baseline64 ⊆ p.features)
    {fs : List Feature} (hobs : ∀ f ∈ fs, p.Observed f) {exts : List Extension} {exit : X86.Word}
    {m : MState} (hfree : FeatureFree (Observed.set fs) exts exit m) :
    (∀ n, run p.features exts exit n m = run (Observed.set fs) exts exit n m) ∧
    (∀ n m', run (Observed.set fs) exts exit n m = some m' →
      step p.features exts exit m' = step (Observed.set fs) exts exit m') ∧
    (∀ final, Returns p.features exts exit m final ↔ Returns (Observed.set fs) exts exit m final) ∧
    FeatureFree p.features exts exit m :=
  hfree.same_behaviour (Observed.set_subset hp hb hobs)

end Profile

/-! ## The tactic -/

/-- `cpuid_cases hp hb f with hbit hmem` splits on the CPUID bit of the leaf-1
feature `f` (with no OS-managed state) on a consistent (`hp`) x86-64 (`hb`)
profile: one goal with `hbit : bit = true` and `hmem : f ∈ p.features`, one with
`hbit : bit = false` and `hmem : f ∉ p.features`. -/
syntax (name := cpuidCases) "cpuid_cases " term:max ppSpace term:max ppSpace term:max
  " with " ident ppSpace ident : tactic

macro_rules
  | `(tactic| cpuid_cases $hp $hb $f with $hbit $hmem) =>
    `(tactic| rcases Profile.cpuid_cases_one (f := $f) $hp $hb (by decide) (by decide) with
        ⟨$hbit, $hmem⟩ | ⟨$hbit, $hmem⟩)

/-- `cpuid_cases' hp hl f with hbit hmem`: the same for a feature of any leaf,
given `hl` that its leaf is available. -/
syntax (name := cpuidCases') "cpuid_cases' " term:max ppSpace term:max ppSpace term:max
  " with " ident ppSpace ident : tactic

macro_rules
  | `(tactic| cpuid_cases' $hp $hl $f with $hbit $hmem) =>
    `(tactic| rcases Profile.cpuid_cases (f := $f) $hp $hl (by decide) with
        ⟨$hbit, $hmem⟩ | ⟨$hbit, $hmem⟩)

end Silmaril.X86.Features
