module

public import Silmaril.X86.Model.Basic
public import Silmaril.X86.Features.Checks
public import Silmaril.X86.Features.Vectors.Cpuid

/-!
# Profiles: psABI levels, concrete processors, and CPUID

A `Profile` is a named configuration of the feature-parametric machine (its
feature set, its extension decoders) together with its flag policy. Profiles
are preordered by their configurations (`Profile.Le`, `p ≤ q`), and every
profile is a `Model` (`Profile.model`), so the maps and transfer theorems of
`Model/Basic.lean` and `Features/Lattice.lean` apply to it.

## psABI microarchitecture levels

`Level.v1` … `Level.v4` are the x86-64 psABI levels (x86-64-v1 … v4) as
feature sets, restricted to the features `Feature` enumerates:

* v1: x87, SSE, SSE2;
* v2: v1 and SSE3, SSSE3, SSE4.1, SSE4.2, POPCNT;
* v3: v2 and AVX, AVX2, BMI1, BMI2, F16C, FMA, LZCNT, MOVBE;
* v4: v3 and AVX512F, AVX512BW, AVX512CD, AVX512DQ, AVX512VL.

The psABI also requires CMOV, CX8, FXSR, MMX, SCE and OSFXSR (v1),
CMPXCHG16B and LAHF/SAHF (v2) and OSXSAVE (v3); none of them is a `Feature`
(the integer machine executes CMOV unconditionally, and the others are not
modelled), so they are not part of these sets. `Profile.level v` is the
integer decoder on a level-`v` processor. A level fixes no CPUID values: under
`Profile.level v` the bytes of CPUID are undecodable (chaos), so a program
stable at a level never executes CPUID, and everything stable at level `v`
holds on every processor of that level (`Cpu.level_le`).

## Processors

A `Cpu` is a CPUID oracle (`Ext.Wire.Platform`) and the XCR0 the operating
system set; its features are `FeatureSet.ofPlatform` (`Cpu.features`).
`Profile.cpu c` executes CPUID (`cpuidExt`, `0F A2`) with the oracle's reply,
so code that branches on CPUID can be verified at a concrete processor:

* `Cpu.step_cpuid`: CPUID retires, writing EAX, EBX, ECX, EDX from the oracle;
* `Cpu.cpuid_bit_iff`: after CPUID with EAX and ECX naming a feature's leaf and
  subleaf, the feature's bit in the result register is set **iff the feature
  is in the processor's feature set** (for features that need no OS-enabled
  state, and when the leaf is in range).

Named processors: `Cpu.i7_8700` (the host, `Features.hostRows`) and the qemu
TCG models `Cpu.qemu64`, `Cpu.qemuNehalem`, `Cpu.qemuHaswell`,
`Cpu.qemuSkylakeServer`, `Cpu.qemuIcelakeServer`, `Cpu.qemuEPYC`,
`Cpu.qemuMax`, from the CPUID dumps of `Features.Vectors.Cpuid`. Their levels
are checked by `decide` (`i7_8700_v3`, `i7_8700_not_v4`, …).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.X86.Features (Config FeatureSet Feature Extension baseFeatures)
open Silmaril.X86.Ext.Wire (Platform CpuidReply cpuidState)
open Silmaril.X86.Ext (Sz)
open Silmaril.Process (Memory)

/-! ## Profiles -/

/-- A named configuration of the feature machine. -/
structure Profile extends Config where
  name : String
  flags : Model.FlagPolicy := .sdm

namespace Profile

/-- `p ≤ q`: the configuration of `p` is below that of `q`. -/
instance : Preorder Profile where
  le p q := p.toConfig ≤ q.toConfig
  le_refl p := le_refl p.toConfig
  le_trans _ _ _ h₁ h₂ := le_trans (α := Config) h₁ h₂

theorem le_def {p q : Profile} : p ≤ q ↔ p.toConfig ≤ q.toConfig := Iff.rfl

/-- A profile as a model. -/
def model (p : Profile) : Model := { Model.ofConfig p.toConfig with name := p.name, flags := p.flags }

/-- The map between the models of profiles `p ≤ q`. -/
def hom {p q : Profile} (h : p ≤ q) : Model.Hom p.model q.model := Model.Hom.ofLe (c := p.toConfig) h

theorem model_le {p q : Profile} (h : p ≤ q) : p.model ≤ q.model := (hom h).le

/-- The integer decoder on a processor with features `F`. -/
def base (F : FeatureSet) (name : String := "X86.Ext") : Profile :=
  { Config.base F with name }

/-- `X86.Ext`'s profile: the integer decoder with exactly the features its
bit-count instructions need. -/
def ext : Profile := base baseFeatures

/-- `X86.Float`'s scalar SSE. -/
def float (F : FeatureSet) : Profile := { Config.floatConfig F with name := "X86.Float" }

/-- `X86.Ext.Wire` with platform `p`. -/
def wire (F : FeatureSet) (p : Platform) : Profile :=
  { Features.wireConfig F p with name := "X86.Ext.Wire" }

theorem base_le {F : FeatureSet} {q : Profile} (h : F ⊆ q.features) (name : String) :
    base F name ≤ q := Config.base_le h

theorem ext_le_wire {F : FeatureSet} (hF : baseFeatures ⊆ F) (p : Platform) : ext ≤ wire F p :=
  Config.base_le hF

theorem ext_le_float {F : FeatureSet} (hF : baseFeatures ⊆ F) : ext ≤ float F :=
  Config.base_le hF

end Profile

/-! ## psABI levels -/

/-- The x86-64 psABI microarchitecture levels. -/
inductive Level where
  | v1 | v2 | v3 | v4
  deriving DecidableEq, Repr

namespace Level

/-- The features of a level (see the module docstring for what is omitted). -/
def features : Level → FeatureSet
  | v1 => .ofList [.x87, .sse, .sse2]
  | v2 => .ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt]
  | v3 => .ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt,
      .avx, .avx2, .bmi1, .bmi2, .f16c, .fma, .lzcnt, .movbe]
  | v4 => .ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .popcnt,
      .avx, .avx2, .bmi1, .bmi2, .f16c, .fma, .lzcnt, .movbe,
      .avx512f, .avx512bw, .avx512cd, .avx512dq, .avx512vl]

/-- The level order. -/
def toNat : Level → Nat
  | v1 => 1 | v2 => 2 | v3 => 3 | v4 => 4

instance : LE Level := ⟨fun a b => a.toNat ≤ b.toNat⟩

instance (a b : Level) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

theorem features_mono : ∀ {a b : Level}, a ≤ b → a.features ⊆ b.features := by
  intro a b h
  cases a <;> cases b <;> first | decide | exact absurd h (by decide)

theorem features_closed (l : Level) : l.features.Closed := by cases l <;> decide

theorem v1_eq_baseline64 : v1.features = FeatureSet.baseline64 := by decide

/-- LZCNT, BMI1 and POPCNT: from level v3 on. -/
theorem baseFeatures_subset_v3 : baseFeatures ⊆ v3.features := by decide

theorem not_baseFeatures_subset_v2 : ¬ baseFeatures ⊆ v2.features := by decide

end Level

/-- The integer decoder on a processor of level `l`. -/
def Profile.level (l : Level) : Profile := Profile.base l.features s!"x86-64-{repr l}"

theorem Profile.level_mono {a b : Level} (h : a ≤ b) : Profile.level a ≤ Profile.level b :=
  Config.base_mono (Level.features_mono h)

theorem Profile.ext_le_level_v3 : Profile.ext ≤ Profile.level .v3 :=
  Config.base_mono Level.baseFeatures_subset_v3

/-! ## CPUID as an extension -/

/-- The CPUID instruction, `0F A2`. -/
def cpuidDecode (bytes : List Byte) : Option (Unit × Nat) :=
  if bytes.take 2 = [0x0F, 0xA2] then some ((), 2) else none

theorem cpuidDecode_eq_some {bytes : List Byte} {x : Unit} {n : Nat}
    (h : cpuidDecode bytes = some (x, n)) : bytes.take 2 = [0x0F, 0xA2] ∧ n = 2 := by
  unfold cpuidDecode at h
  split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

theorem length_of_take_two {bytes : List Byte} (h : bytes.take 2 = [0x0F, 0xA2]) :
    2 ≤ bytes.length := by
  have := congrArg List.length h
  simp only [List.length_take, List.length_cons, List.length_nil] at this
  omega

/-- CPUID as a prefix-code decoder. -/
def cpuidDecoder : Machine.Decoder Unit where
  decode := cpuidDecode
  encode _ := [0x0F, 0xA2]
  decode_length_pos h := by obtain ⟨-, rfl⟩ := cpuidDecode_eq_some h; omega
  decode_length_le h := by
    obtain ⟨ht, rfl⟩ := cpuidDecode_eq_some h
    exact length_of_take_two ht
  decode_append extra h := by
    obtain ⟨ht, rfl⟩ := cpuidDecode_eq_some h
    unfold cpuidDecode
    rw [List.take_append_of_le_length (length_of_take_two ht), ht]
    rfl
  decode_take h := by
    obtain ⟨ht, rfl⟩ := cpuidDecode_eq_some h
    unfold cpuidDecode
    rw [List.take_take, Nat.min_self, ht]
    rfl
  decode_encode_append _ rest := by
    unfold cpuidDecode
    simp

/-- CPUID with the reply of platform `p`. Every x86-64 processor has CPUID, so
it requires no feature. -/
def cpuidExt (p : Platform) : Extension where
  name := "CPUID"
  Syntax := Unit
  decoder := cpuidDecoder
  requires _ := []
  exec _ n s memory := Features.Result.pure (fun s => s.setCore (cpuidState p s.core)) n s memory

/-- An extension that never decodes bytes starting `0F A2` is disjoint from CPUID. -/
theorem cpuidExt_disjoint {e : Extension} (p : Platform)
    (h : ∀ rest, e.decoder.decode (0x0F :: 0xA2 :: rest) = none) : e.Disjoint (cpuidExt p) := by
  intro bytes
  by_cases ht : bytes.take 2 = [0x0F, 0xA2]
  · left
    have hb : bytes = 0x0F :: 0xA2 :: bytes.drop 2 := by
      conv => lhs; rw [← List.take_append_drop 2 bytes, ht]
      rfl
    rw [hb]; exact h _
  · right
    change cpuidDecode bytes = none
    unfold cpuidDecode
    rw [ite_eq_right_iff.mpr fun h => absurd h ht]

/-- The integer decoder rejects every byte string that starts with CPUID. -/
theorem ext_decode_cpuid (rest : List Byte) : Ext.decode (0x0F :: 0xA2 :: rest) = none := by
  have : Ext.parseRaw [0x0F, 0xA2] = .bad := rfl
  have h := Ext.good_parseRaw.bad this rest
  unfold Ext.decode
  rw [show (0x0F :: 0xA2 :: rest : List Byte) = [0x0F, 0xA2] ++ rest from rfl, h]

theorem ext_parseRaw_cpuid (rest : List Byte) : Ext.parseRaw (0x0F :: 0xA2 :: rest) = .bad :=
  Ext.good_parseRaw.bad (xs := [0x0F, 0xA2]) rfl rest

/-! ## Processors -/

/-- A processor: its CPUID oracle and the XCR0 its operating system set. -/
structure Cpu where
  name : String
  platform : Platform
  xcr0 : BitVec 64

namespace Cpu

/-- The features the processor executes. -/
def features (c : Cpu) : FeatureSet := FeatureSet.ofPlatform c.platform c.xcr0

/-- A processor from CPUID rows `(leaf, subleaf, eax, ebx, ecx, edx)`. -/
def ofRows (name : String) (rows : List (Nat × Nat × Nat × Nat × Nat × Nat)) (xcr0 : Nat) : Cpu :=
  ⟨name, ⟨Features.cpuidOfRows rows⟩, BitVec.ofNat 64 xcr0⟩

/-- A processor from the `n`-th dump of `Features.Vectors.Cpuid.cases`. -/
def ofCase (n : Nat) : Cpu :=
  match Features.Vectors.Cpuid.cases[n]? with
  | some (name, rows, xcr0, _) => ofRows name rows xcr0
  | none => ofRows "none" [] 0

/-- The host, an Intel Core i7-8700 (Coffee Lake), with AVX state enabled. -/
def i7_8700 : Cpu := ofRows "Intel Core i7-8700" Features.hostRows 0x1f

def qemuMax : Cpu := ofCase 1
def qemu64 : Cpu := ofCase 2
def qemuNehalem : Cpu := ofCase 4
def qemuHaswell : Cpu := ofCase 7
def qemuSkylakeServer : Cpu := ofCase 10
def qemuIcelakeServer : Cpu := ofCase 11
def qemuEPYC : Cpu := ofCase 12

example : qemuMax.name = "qemu -cpu max" := rfl
example : qemu64.name = "qemu -cpu qemu64" := rfl
example : qemuNehalem.name = "qemu -cpu Nehalem" := rfl
example : qemuHaswell.name = "qemu -cpu Haswell" := rfl
example : qemuSkylakeServer.name = "qemu -cpu Skylake-Server" := rfl
example : qemuIcelakeServer.name = "qemu -cpu Icelake-Server" := rfl
example : qemuEPYC.name = "qemu -cpu EPYC" := rfl

/-- The processor's profile: its features, and CPUID with its own reply. -/
def config (c : Cpu) : Config := ⟨c.features, [cpuidExt c.platform], List.pairwise_singleton _ _⟩

/-- The profile of a processor. -/
def profile (c : Cpu) : Profile := { c.config with name := c.name }

/-- The processor has (at least) the features of level `l`. -/
def AtLevel (c : Cpu) (l : Level) : Prop := l.features ⊆ c.features

instance (c : Cpu) (l : Level) : Decidable (c.AtLevel l) :=
  inferInstanceAs (Decidable (l.features ⊆ c.features))

/-- **A level is below every processor of that level.** -/
theorem level_le {c : Cpu} {l : Level} (h : c.AtLevel l) : Profile.level l ≤ c.profile :=
  Config.base_le h

theorem ext_le {c : Cpu} (h : baseFeatures ⊆ c.features) : Profile.ext ≤ c.profile :=
  Config.base_le h

theorem i7_8700_features :
    i7_8700.features = FeatureSet.ofList [.x87, .sse, .sse2, .sse3, .ssse3, .sse41, .sse42,
      .popcnt, .lzcnt, .bmi1, .bmi2, .adx, .movbe, .rdrand, .rdseed, .aes, .pclmulqdq, .avx,
      .avx2, .fma, .f16c] :=
  Features.host_features

theorem i7_8700_v3 : i7_8700.AtLevel .v3 := by decide
theorem i7_8700_not_v4 : ¬ i7_8700.AtLevel .v4 := by decide
theorem qemu64_v1 : qemu64.AtLevel .v1 := by decide
theorem qemu64_not_v2 : ¬ qemu64.AtLevel .v2 := by decide
theorem qemuNehalem_v2 : qemuNehalem.AtLevel .v2 := by decide
theorem qemuNehalem_not_v3 : ¬ qemuNehalem.AtLevel .v3 := by decide
theorem qemuHaswell_v3 : qemuHaswell.AtLevel .v3 := by decide
/-- qemu's TCG does not enumerate AVX-512 for `Skylake-Server`, so it is not v4. -/
theorem qemuSkylakeServer_not_v4 : ¬ qemuSkylakeServer.AtLevel .v4 := by decide
theorem qemuEPYC_v3 : qemuEPYC.AtLevel .v3 := by decide
theorem qemuMax_v3 : qemuMax.AtLevel .v3 := by decide

theorem i7_8700_baseFeatures : baseFeatures ⊆ i7_8700.features := by decide

/-! ### CPUID -/

/-- **CPUID retires** in a processor's profile, writing the oracle's reply. -/
theorem step_cpuid (c : Cpu) {exit : Word} {m : Features.MState} {rest : List Byte}
    (hw : fetchWindow m.memory maxInstrLength m.state.core.rip.toNat = 0x0F :: 0xA2 :: rest)
    (hx : m.memory.Permitted .execute m.state.core.rip.toNat 2) :
    c.config.step exit m =
      .retired ⟨(m.state.setCore (cpuidState c.platform m.state.core)).advance 2, m.memory⟩ := by
  have hf : Ext.fetch m.memory m.state.core.rip.toNat = .undecodable := by
    unfold Ext.fetch
    rw [hw, ext_decode_cpuid, ext_parseRaw_cpuid]
  have hd : Features.extDecode [cpuidExt c.platform] (0x0F :: 0xA2 :: rest) =
      some ⟨cpuidExt c.platform, (), 2⟩ := by
    simp [Features.extDecode, cpuidExt, cpuidDecoder, cpuidDecode]
  unfold Config.step Features.step
  rw [hf]
  simp only
  rw [hw, show c.config.exts = [cpuidExt c.platform] from rfl, hd]
  simp only [hx, ite_true, Features.extStep, cpuidExt, FeatureSet.missing]
  rfl

/-- The 64-bit register a CPUID output register is written to. -/
def _root_.Silmaril.X86.Features.Feature.CpuidReg.toReg : Feature.CpuidReg → Reg
  | .eax => .rax
  | .ebx => .rbx
  | .ecx => .rcx
  | .edx => .rdx

theorem cpuidState_read (p : Platform) (s : X86.State) (r : Feature.CpuidReg) :
    (cpuidState p s).read r.toReg =
      (r.get (p.cpuid (Sz.d.read s .rax) (Sz.d.read s .rcx))).setWidth 64 := by
  cases r <;> simp [cpuidState, Sz.write, Feature.CpuidReg.toReg, Feature.CpuidReg.get]

theorem cpuid_bit_lt (f : Feature) : f.cpuid.bit < 32 := by cases f <;> decide

/-- **CPUID reports the feature set.** After CPUID with EAX = the leaf and
ECX = the subleaf of feature `f` (one that needs no OS-enabled state, with the
leaf in range), bit `f.cpuid.bit` of the result register is set iff `f` is a
feature of the processor. -/
theorem cpuid_bit_iff (c : Cpu) {f : Feature} (h0 : f.xcr0 = 0)
    (hl : FeatureSet.leafAvailable c.platform.cpuid f.cpuid.leaf = true) {s : X86.State}
    (hax : Sz.d.read s .rax = f.cpuid.leaf) (hcx : Sz.d.read s .rcx = f.cpuid.subleaf) :
    ((cpuidState c.platform s).read f.cpuid.reg.toReg).getLsbD f.cpuid.bit = true ↔
      f ∈ c.features := by
  rw [cpuidState_read, hax, hcx, BitVec.getLsbD_setWidth]
  have hb : f.cpuid.bit < 64 := by have := cpuid_bit_lt f; omega
  simp only [hb, decide_true, Bool.true_and]
  unfold features FeatureSet.ofPlatform
  rw [FeatureSet.mem_ofCpuid_of_xcr0 h0]
  simp [hl]

end Cpu

end Silmaril.X86
