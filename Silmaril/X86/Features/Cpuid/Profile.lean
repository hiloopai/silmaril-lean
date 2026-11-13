module

public import Silmaril.X86.Features.Feature
public import Batteries.Data.BitVec.Lemmas

/-!
# Processor profiles

A `Profile` is a concrete x86-64 processor model as user-mode code observes it:

* `cpuid`: the CPUID oracle, leaf and subleaf to the four reply registers;
* `xcr0`: the value of XCR0 that XGETBV reads, i.e. the state components the
  operating system enabled;
* `features`: the feature set the semantics enforce (`Features.step` raises
  `featureUD` for an instruction whose feature is not in it).

`Consistent p` says that what code can observe is what the semantics enforce:
`FeatureSet.ofCpuid p.cpuid p.xcr0 = p.features`. Every profile built with
`Profile.ofCpuid` is consistent by definition; the named models of
`Cpuid/Models.lean` are built that way from real CPUID dumps.

## Maps between profiles

* `p ≤ q` (`Profile.Le`) when `p.features ⊆ q.features`: code proved on `p`'s
  feature set without executing CPUID or XGETBV transfers to `q` (the
  configuration lattice: `Config.base p.features ≤ Config.base q.features`).
  It is a preorder (`instance : Preorder Profile`).
* `p.mask G` keeps only the features in `G`: every CPUID bit of a feature outside
  `G` is cleared, everything else (vendor, family, maximum leaves, OSXSAVE,
  XCR0) is kept. This is what a hypervisor or `qemu -cpu host,-avx2` does.
  `mask_features` says that a consistent profile stays consistent and that its
  features become `p.features ∩ G`, so `p.mask G ≤ p` (`mask_le`).
* `p.withXcr0 x` changes the OS-enabled state (`withXcr0_consistent`).

## What CPUID depends on

Leaves `0`, `1`, `80000000H` and `80000001H` ignore the subleaf on real
processors. The model does not assume it: `Feature.cpuid` names subleaf 0 for
every feature, so code that tests a feature bit is verified under a CPUID
executed with ECX = 0 (`SubleafFree` states the hardware fact for the leaves
that ignore ECX, for code that does not clear it).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86.Ext.Wire (CpuidReply Platform)

/-- A processor model: its CPUID oracle, its XCR0, and the feature set its
instructions are gated by. -/
structure Profile where
  /-- A name for documentation and diagnostics. -/
  name : String
  cpuid : BitVec 32 → BitVec 32 → CpuidReply
  xcr0 : BitVec 64
  features : FeatureSet

namespace Profile

/-- What code observes (CPUID and XGETBV) is the gating the semantics enforce. -/
def Consistent (p : Profile) : Prop := FeatureSet.ofCpuid p.cpuid p.xcr0 = p.features

/-- The consistent profile of a CPUID oracle and an XCR0 value. -/
def ofCpuid (name : String) (cpuid : BitVec 32 → BitVec 32 → CpuidReply) (xcr0 : BitVec 64) :
    Profile :=
  ⟨name, cpuid, xcr0, FeatureSet.ofCpuid cpuid xcr0⟩

theorem ofCpuid_consistent (name : String) (cpuid : BitVec 32 → BitVec 32 → CpuidReply)
    (xcr0 : BitVec 64) : (ofCpuid name cpuid xcr0).Consistent := rfl

/-- The `Ext.Wire` platform contract of a profile (its CPUID oracle). -/
def platform (p : Profile) : Platform := ⟨p.cpuid⟩

/-- CPUID.1:ECX.OSXSAVE[bit 27]: the OS has set CR4.OSXSAVE, so XGETBV executes. -/
def osxsave (p : Profile) : Bool := (p.cpuid 1 0).ecx.getLsbD 27

/-- The leaves that ignore ECX on real processors return the same reply for
every subleaf. -/
def SubleafFree (p : Profile) : Prop :=
  ∀ leaf ∈ [(0 : BitVec 32), 1, 0x80000000, 0x80000001], ∀ sub, p.cpuid leaf sub = p.cpuid leaf 0

/-! ## The preorder -/

/-- `p ≤ q`: `q` executes every feature `p` does. -/
def Le (p q : Profile) : Prop := p.features ⊆ q.features

instance : Preorder Profile where
  le := Le
  le_refl p := FeatureSet.subset_refl p.features
  le_trans _ _ _ h₁ h₂ := FeatureSet.subset_trans h₁ h₂

theorem le_def {p q : Profile} : p ≤ q ↔ p.features ⊆ q.features := Iff.rfl

instance (p q : Profile) : Decidable (p ≤ q) :=
  inferInstanceAs (Decidable (p.features ⊆ q.features))

/-! ## Changing XCR0 -/

/-- The same processor with another OS-enabled state. -/
def withXcr0 (p : Profile) (x : BitVec 64) : Profile :=
  ofCpuid p.name p.cpuid x

theorem withXcr0_consistent (p : Profile) (x : BitVec 64) : (p.withXcr0 x).Consistent := rfl

/-! ## Masking features -/

/-- Clear the bits of register `r` of leaf `leaf`, subleaf `sub`, that enumerate a
feature outside `G`. -/
def maskReg (G : FeatureSet) (leaf sub : BitVec 32) (r : Feature.CpuidReg) (v : BitVec 32) :
    BitVec 32 :=
  BitVec.ofFnLE fun i => v.getLsbD i &&
    Feature.all.all fun f => G.has f || !(f.cpuid.leaf == leaf && f.cpuid.subleaf == sub &&
      f.cpuid.reg == r && f.cpuid.bit == i.val)

/-- The CPUID oracle with every feature outside `G` cleared. -/
def maskCpuid (G : FeatureSet) (cpuid : BitVec 32 → BitVec 32 → CpuidReply) :
    BitVec 32 → BitVec 32 → CpuidReply := fun leaf sub =>
  let r := cpuid leaf sub
  ⟨maskReg G leaf sub .eax r.eax, maskReg G leaf sub .ebx r.ebx, maskReg G leaf sub .ecx r.ecx,
    maskReg G leaf sub .edx r.edx⟩

/-- The intersection of feature sets. -/
def _root_.Silmaril.X86.Features.FeatureSet.inter (F G : FeatureSet) : FeatureSet :=
  ⟨fun f => F.has f && G.has f⟩

/-- `p` with only the features of `G` enumerated (and so executed). -/
def mask (p : Profile) (G : FeatureSet) : Profile :=
  ⟨p.name ++ " masked", maskCpuid G p.cpuid, p.xcr0, p.features.inter G⟩

@[simp] theorem _root_.Silmaril.X86.Features.FeatureSet.mem_inter (F G : FeatureSet) (f : Feature) :
    f ∈ F.inter G ↔ f ∈ F ∧ f ∈ G := by
  simp [FeatureSet.inter, FeatureSet.mem_iff]

theorem _root_.Silmaril.X86.Features.FeatureSet.inter_subset_left (F G : FeatureSet) :
    F.inter G ⊆ F := fun f h => ((FeatureSet.mem_inter F G f).mp h).1

theorem _root_.Silmaril.X86.Features.FeatureSet.inter_subset_right (F G : FeatureSet) :
    F.inter G ⊆ G := fun f h => ((FeatureSet.mem_inter F G f).mp h).2

/-- No two features share a CPUID bit. -/
theorem _root_.Silmaril.X86.Features.Feature.cpuid_injective :
    ∀ f g : Feature, f.cpuid = g.cpuid → f = g := by decide

/-- Whether some feature is enumerated at register `r`, bit `i` of the leaf. -/
def bitClear (G : FeatureSet) (leaf sub : BitVec 32) (r : Feature.CpuidReg) (i : Nat) : Bool :=
  Feature.all.all fun f => G.has f || !(f.cpuid.leaf == leaf && f.cpuid.subleaf == sub &&
    f.cpuid.reg == r && f.cpuid.bit == i)

theorem getLsbD_maskReg (G : FeatureSet) (leaf sub : BitVec 32) (r : Feature.CpuidReg)
    (v : BitVec 32) (i : Nat) :
    (maskReg G leaf sub r v).getLsbD i = (v.getLsbD i && bitClear G leaf sub r i) := by
  unfold maskReg bitClear
  rw [BitVec.getLsbD_ofFnLE]
  split
  · rfl
  · rename_i h; simp [BitVec.getLsbD_of_ge v i (by omega)]

/-- A bit that enumerates no feature is kept. -/
theorem bitClear_of_none {G : FeatureSet} {leaf sub : BitVec 32} {r : Feature.CpuidReg} {i : Nat}
    (h : ∀ f : Feature, f.cpuid.leaf = leaf → f.cpuid.subleaf = sub → f.cpuid.reg = r →
      f.cpuid.bit ≠ i) : bitClear G leaf sub r i = true := by
  unfold bitClear
  rw [List.all_eq_true]
  intro f _
  have := h f
  cases h1 : (f.cpuid.leaf == leaf) <;> cases h2 : (f.cpuid.subleaf == sub) <;>
    cases h3 : (f.cpuid.reg == r) <;> cases h4 : (f.cpuid.bit == i) <;> simp_all

/-- The bit that enumerates feature `f` is kept exactly when `f ∈ G`. -/
theorem bitClear_feature (G : FeatureSet) (f : Feature) :
    bitClear G f.cpuid.leaf f.cpuid.subleaf f.cpuid.reg f.cpuid.bit = G.has f := by
  unfold bitClear
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true]
  constructor
  · intro h
    simpa using h f (Feature.mem_all f)
  · intro hf g _
    by_cases hg : g.cpuid = f.cpuid
    · rw [Feature.cpuid_injective g f hg]; simp [hf]
    · have hne : ¬ (g.cpuid.leaf = f.cpuid.leaf ∧ g.cpuid.subleaf = f.cpuid.subleaf ∧
          g.cpuid.reg = f.cpuid.reg ∧ g.cpuid.bit = f.cpuid.bit) := by
        rintro ⟨h1, h2, h3, h4⟩
        apply hg
        cases hgc : g.cpuid; cases hfc : f.cpuid
        simp_all
      cases h1 : (g.cpuid.leaf == f.cpuid.leaf) <;> cases h2 : (g.cpuid.subleaf == f.cpuid.subleaf) <;>
        cases h3 : (g.cpuid.reg == f.cpuid.reg) <;> cases h4 : (g.cpuid.bit == f.cpuid.bit) <;>
        simp_all

/-- A register with no feature bits is unchanged. -/
theorem maskReg_eq_self {G : FeatureSet} {leaf sub : BitVec 32} {r : Feature.CpuidReg}
    (h : ∀ f : Feature, f.cpuid.leaf = leaf → f.cpuid.subleaf = sub → f.cpuid.reg ≠ r)
    (v : BitVec 32) : maskReg G leaf sub r v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [getLsbD_maskReg, bitClear_of_none (fun f h1 h2 h3 => absurd h3 (h f h1 h2)), Bool.and_true]

theorem reg_get_maskCpuid (G : FeatureSet) (cpuid : BitVec 32 → BitVec 32 → CpuidReply)
    (leaf sub : BitVec 32) (r : Feature.CpuidReg) :
    r.get (maskCpuid G cpuid leaf sub) = maskReg G leaf sub r (r.get (cpuid leaf sub)) := by
  cases r <;> rfl

private theorem no_eax : ∀ f : Feature, ∀ leaf sub : BitVec 32, f.cpuid.leaf = leaf →
    f.cpuid.subleaf = sub → f.cpuid.reg ≠ .eax := by
  intro f; cases f <;> simp [Feature.cpuid]

/-- Masking keeps the maximum leaves. -/
theorem leafAvailable_maskCpuid (G : FeatureSet) (cpuid : BitVec 32 → BitVec 32 → CpuidReply)
    (leaf : BitVec 32) :
    FeatureSet.leafAvailable (maskCpuid G cpuid) leaf = FeatureSet.leafAvailable cpuid leaf := by
  simp only [FeatureSet.leafAvailable, maskCpuid,
    maskReg_eq_self (no_eax · 0 0), maskReg_eq_self (no_eax · 0x80000000#32 0)]

/-- Masking keeps OSXSAVE. -/
theorem osxsave_maskCpuid (G : FeatureSet) (cpuid : BitVec 32 → BitVec 32 → CpuidReply) :
    (maskCpuid G cpuid 1 0).ecx.getLsbD 27 = (cpuid 1 0).ecx.getLsbD 27 := by
  show (maskReg G 1 0 .ecx _).getLsbD 27 = _
  rw [getLsbD_maskReg, bitClear_of_none, Bool.and_true]
  intro f; cases f <;> simp [Feature.cpuid]

/-- Masking a consistent profile keeps it consistent, with the features in `G`. -/
theorem mask_consistent {p : Profile} (hp : p.Consistent) (G : FeatureSet) :
    (p.mask G).Consistent := by
  unfold Consistent mask
  simp only
  rw [← hp]
  ext f
  simp only [FeatureSet.ofCpuid, FeatureSet.inter, leafAvailable_maskCpuid, reg_get_maskCpuid,
    getLsbD_maskReg, bitClear_feature, osxsave_maskCpuid]
  cases FeatureSet.leafAvailable p.cpuid f.cpuid.leaf <;>
    cases (f.cpuid.reg.get (p.cpuid f.cpuid.leaf f.cpuid.subleaf)).getLsbD f.cpuid.bit <;>
    cases G.has f <;> simp

theorem mask_features (p : Profile) (G : FeatureSet) : (p.mask G).features = p.features.inter G :=
  rfl

theorem mask_le (p : Profile) (G : FeatureSet) : p.mask G ≤ p :=
  FeatureSet.inter_subset_left _ _

theorem mask_le_of_subset (p : Profile) {G : FeatureSet} (h : G ⊆ p.features) : ∀ f ∈ G,
    f ∈ (p.mask G).features :=
  fun f hf => (FeatureSet.mem_inter _ _ f).mpr ⟨h f hf, hf⟩

end Profile

end Silmaril.X86.Features
