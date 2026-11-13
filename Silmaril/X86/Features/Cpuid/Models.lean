module

public import Silmaril.X86.Features.Cpuid.Extension
public import Silmaril.X86.Features.Vectors.Cpuid
public import Silmaril.X86.Model.Profile

/-!
# Named processor models, and the hub's `Cpu`

## `Cpu` and `Profile`

The hub's `X86.Cpu` (`Model/Profile.lean`) is a CPUID oracle and an XCR0 whose
features are *defined* as `ofPlatform`; a `Features.Profile` carries its feature
set separately and `Consistent` relates them. They are the same thing on
consistent profiles: `Cpu.toProfile` is consistent (`Cpu.toProfile_consistent`)
with the same features, `Profile.toCpu` inverts it on consistent profiles
(`Profile.toProfile_toCpu`), so "for every consistent profile" and "for every
`Cpu`" are interchangeable (`Profile.forall_consistent_iff`).

`Profile.config p` is the configuration with CPUID and XGETBV (`sysExt p`). The
hub's `Cpu.config c` (CPUID only, `X86.cpuidExt`) is below it
(`Cpu.config_le`), so every judgment the lattice transfers that is proved for a
hub processor holds with XGETBV added.

## The models

The thirteen CPUID dumps of `Vectors/Cpuid.lean` (`scripts/x86-features/cpuid_dump.c`,
run natively on the i7-8700 host and under `qemu-x86_64` TCG with each `-cpu`
model) as consistent `Profile`s: `Profile.ofCase k` is the profile of the hub's
`Cpu.ofCase k` (the same dumps), so every model is consistent by construction
(`models_consistent`), and its features are the ones libgcc's
`__builtin_cpu_supports` reported for the same dump (`models_features`, the
check of the generated vectors, restated on the profiles).

## Maps between the models

The models are ordered by their features (`Profile.Le`): the Intel line
`qemu64 ≤ core2duo ≤ nehalem ≤ westmere ≤ sandyBridge ≤ haswell ≤ broadwell ≤
skylakeClient ≤ skylakeServer ≤ icelakeServer` and `broadwell ≤ native`, with
`haswell` and `epyc` incomparable to some (`not_haswell_le_nehalem`,
`not_epyc_le_icelakeServer`). Everything proved for a configuration over a
smaller model's features without executing CPUID transfers to the larger ones
(`Config.base_mono`, and the transfer theorems of `Lattice.lean`).

`haswell.mask nehalem.features` is a Haswell that reports (and executes) only
Nehalem's features (`haswell_mask_nehalem`), consistent by `mask_consistent`.

## Observed by the instructions

Executing CPUID on a model's profile returns the dumped rows
(`cpuid_rows`), and XGETBV is enabled exactly on the models whose OS enabled
some XSAVE state (`osxsave_iff`).
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86.Ext.Wire (CpuidReply)

/-! ## `Cpu` and `Profile` -/

/-- The profile of a hub processor: consistent by construction. -/
def _root_.Silmaril.X86.Cpu.toProfile (c : Cpu) : Profile :=
  Profile.ofCpuid c.name c.platform.cpuid c.xcr0

theorem _root_.Silmaril.X86.Cpu.toProfile_consistent (c : Cpu) : c.toProfile.Consistent := rfl

theorem _root_.Silmaril.X86.Cpu.toProfile_features (c : Cpu) :
    c.toProfile.features = c.features := rfl

theorem _root_.Silmaril.X86.Cpu.toProfile_platform (c : Cpu) :
    c.toProfile.platform = c.platform := rfl

namespace Profile

/-- The hub processor of a profile (its CPUID and XCR0). -/
def toCpu (p : Profile) : Cpu := ⟨p.name, p.platform, p.xcr0⟩

theorem toCpu_features {p : Profile} (hp : p.Consistent) : p.toCpu.features = p.features := hp

theorem toProfile_toCpu {p : Profile} (hp : p.Consistent) : p.toCpu.toProfile = p := by
  obtain ⟨name, cpuid, xcr0, features⟩ := p
  unfold Consistent at hp
  simp only at hp
  subst hp
  rfl

/-- Quantifying over consistent profiles is quantifying over hub processors. -/
theorem forall_consistent_iff {P : Profile → Prop} :
    (∀ p : Profile, p.Consistent → P p) ↔ ∀ c : Cpu, P c.toProfile :=
  ⟨fun h c => h _ c.toProfile_consistent, fun h p hp => toProfile_toCpu hp ▸ h p.toCpu⟩

/-- The configuration of a profile: its features, CPUID and XGETBV. -/
def config (p : Profile) : Config := ⟨p.features, [sysExt p], List.pairwise_singleton _ _⟩

/-- The configuration without CPUID and XGETBV is below it. -/
theorem base_le_config (p : Profile) : Config.base p.features ≤ p.config :=
  Config.base_le (FeatureSet.subset_refl _)

end Profile

/-- **The hub's processor configuration (CPUID only) is below the profile's
(CPUID and XGETBV).** -/
theorem _root_.Silmaril.X86.Cpu.config_le (c : Cpu) : c.config ≤ c.toProfile.config :=
  ⟨FeatureSet.subset_refl _, fun e he => by
    simp only [Cpu.config, List.mem_singleton] at he
    subst he
    exact ⟨sysExt c.toProfile, List.mem_singleton_self _, cpuidExt_embeds_sys c.toProfile⟩⟩

namespace Profile

/-- The profile of a CPUID dump: rows `(leaf, subleaf, eax, ebx, ecx, edx)` and XCR0. -/
def ofDump (name : String) (rows : List (Nat × Nat × Nat × Nat × Nat × Nat)) (xcr0 : Nat) :
    Profile :=
  (Cpu.ofRows name rows xcr0).toProfile

/-- The `k`th dump of `Vectors.Cpuid.cases`: the hub's `Cpu.ofCase k`. -/
def ofCase (k : Nat) : Profile := (Cpu.ofCase k).toProfile

def native : Profile := ofCase 0
def qemuMax : Profile := ofCase 1
def qemu64 : Profile := ofCase 2
def core2duo : Profile := ofCase 3
def nehalem : Profile := ofCase 4
def westmere : Profile := ofCase 5
def sandyBridge : Profile := ofCase 6
def haswell : Profile := ofCase 7
def broadwell : Profile := ofCase 8
def skylakeClient : Profile := ofCase 9
def skylakeServer : Profile := ofCase 10
def icelakeServer : Profile := ofCase 11
def epyc : Profile := ofCase 12

/-- Every model, in the order of the dumps. -/
def models : List Profile :=
  [native, qemuMax, qemu64, core2duo, nehalem, westmere, sandyBridge, haswell, broadwell,
    skylakeClient, skylakeServer, icelakeServer, epyc]

theorem ofCase_consistent (k : Nat) : (ofCase k).Consistent := rfl

theorem models_consistent : ∀ p ∈ models, p.Consistent := by
  simp only [models, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact ofCase_consistent _

/-- Each model's features are the expected (`__builtin_cpu_supports`) features of its dump. -/
theorem models_features :
    (models.zip Vectors.Cpuid.cases).all (fun (p, _, _, _, expected) =>
      Feature.all.all fun f => p.features.has f == expected.contains f) = true := by
  decide

/-- The names are the dump names. -/
theorem models_names :
    models.map Profile.name = Vectors.Cpuid.cases.map (·.1) := by decide

/-! ## The order -/

theorem qemu64_le_core2duo : qemu64 ≤ core2duo := by decide
theorem core2duo_le_nehalem : core2duo ≤ nehalem := by decide
theorem nehalem_le_westmere : nehalem ≤ westmere := by decide
theorem westmere_le_sandyBridge : westmere ≤ sandyBridge := by decide
theorem sandyBridge_le_haswell : sandyBridge ≤ haswell := by decide
theorem haswell_le_broadwell : haswell ≤ broadwell := by decide
theorem broadwell_le_skylakeClient : broadwell ≤ skylakeClient := by decide
theorem skylakeClient_le_skylakeServer : skylakeClient ≤ skylakeServer := by decide
theorem skylakeServer_le_icelakeServer : skylakeServer ≤ icelakeServer := by decide
theorem broadwell_le_native : broadwell ≤ native := by decide
theorem haswell_le_epyc : haswell ≤ epyc := by decide
theorem not_haswell_le_nehalem : ¬ haswell ≤ nehalem := by decide
theorem not_epyc_le_icelakeServer : ¬ epyc ≤ icelakeServer := by decide
theorem not_icelakeServer_le_epyc : ¬ icelakeServer ≤ epyc := by decide

/-- Every model has the x86-64 baseline. -/
theorem baseline64_le_models : ∀ p ∈ models, FeatureSet.baseline64 ⊆ p.features := by
  decide

/-- Every model's features are closed under dependencies. -/
theorem models_closed : ∀ p ∈ models, p.features.Closed := by
  decide

/-- A Haswell masked to Nehalem's features executes exactly Nehalem's features. -/
theorem haswell_mask_nehalem : (haswell.mask nehalem.features).features = nehalem.features := by
  decide

theorem haswell_mask_nehalem_consistent : (haswell.mask nehalem.features).Consistent :=
  mask_consistent (ofCase_consistent 7) _

/-! ## What the instructions observe -/

/-- CPUID on a model returns the dumped row. -/
theorem cpuid_rows :
    Vectors.Cpuid.cases.all (fun (name, rows, xcr0, _) =>
      rows.all fun (leaf, sub, a, b, c, d) =>
        (ofDump name rows xcr0).cpuid (BitVec.ofNat 32 leaf) (BitVec.ofNat 32 sub) ==
          ⟨BitVec.ofNat 32 a, BitVec.ofNat 32 b, BitVec.ofNat 32 c, BitVec.ofNat 32 d⟩) = true := by
  decide

/-- XGETBV executes exactly on the models whose OS enabled XSAVE state. -/
theorem osxsave_iff : models.all (fun p => p.osxsave == (p.xcr0 != 0)) = true := by
  decide

end Profile

end Silmaril.X86.Features
