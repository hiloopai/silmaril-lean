module

public import Silmaril.X86.Ext.Wire.Semantics

/-!
# x86 CPU features, feature sets and CPUID

`Feature` names the CPUID-enumerated instruction-set extensions the
feature-parametric machine (`Features.Machine`) can require of an instruction.
Each feature carries the CPUID leaf, subleaf, output register and bit that
enumerate it (`Feature.cpuid`, Intel SDM Vol. 2A, CPUID, Tables 3-8 and 3-10,
and Table 3-17 for the extended leaf `80000001H`) and the XCR0 state
components the operating system must enable before its instructions execute
(`Feature.xcr0`, SDM Vol. 1, §13.3 and §14.3/§15.2: AVX needs SSE and AVX state,
`XCR0[2:1] = 11b`; AVX-512 additionally the opmask, ZMM_Hi256 and Hi16_ZMM
state, `XCR0[7:5] = 111b`).

A `FeatureSet` is a decidable set of features (a Boolean predicate, compared on
the finite enumeration `Feature.all`). It is the set of features a processor
*runs*: `ofCpuid` computes it from a CPUID oracle (`Wire.Platform.cpuid`) and
the XCR0 value, requiring the leaf to be within the reported maximum leaf, the
feature bit to be set and, for AVX and AVX-512 features, CPUID.1:ECX.OSXSAVE
and the XCR0 components.

## Dependencies

`Feature.deps` is the direct-dependency table of Linux's
`arch/x86/kernel/cpu/cpuid-deps.c`, with the unmodelled FXSR and XSAVE folded
into what they themselves depend on (FXSR on the x87 FPU), plus `avx → sse2`
(VEX-encoded instructions operate on the XMM state SSE introduced; Linux
reaches the same through XSAVE → FXSR). `Feature.ancestors` is its reflexive
transitive closure (`ancestors_spec`). `FeatureSet.closure` adds every
dependency (`closure_closed`, `subset_closure`, `closure_least`), and
`FeatureSet.interior` drops every feature with a missing dependency, which is
what Linux does to an inconsistent CPUID (`interior_closed`,
`interior_subset`, `interior_greatest`).

`baseline64` is the x86-64 baseline: x87, SSE and SSE2 are architecturally
present on every processor that supports 64-bit mode (AMD64 APM Vol. 1, §1.1;
Intel SDM Vol. 1, §11.6.1 and §2.2.7), so long-mode code may use them without
CPUID checks.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86.Ext.Wire (CpuidReply Platform)

/-! ## Features -/

/-- A CPUID-enumerated x86 feature. -/
inductive Feature where
  | x87 | sse | sse2 | sse3 | ssse3 | sse41 | sse42
  | popcnt | lzcnt | bmi1 | bmi2 | adx | movbe | rdrand | rdseed
  | aes | pclmulqdq | sha | gfni
  | avx | avx2 | fma | f16c | vaes | vpclmulqdq
  | avx512f | avx512cd | avx512bw | avx512dq | avx512vl | avx512ifma | avx512vbmi
  | avx512vbmi2 | avx512vnni | avx512bitalg | avx512vpopcntdq
  deriving DecidableEq, Repr, Inhabited

namespace Feature

/-- Every feature, once. -/
def all : List Feature :=
  [x87, sse, sse2, sse3, ssse3, sse41, sse42,
    popcnt, lzcnt, bmi1, bmi2, adx, movbe, rdrand, rdseed,
    aes, pclmulqdq, sha, gfni,
    avx, avx2, fma, f16c, vaes, vpclmulqdq,
    avx512f, avx512cd, avx512bw, avx512dq, avx512vl, avx512ifma, avx512vbmi,
    avx512vbmi2, avx512vnni, avx512bitalg, avx512vpopcntdq]

theorem mem_all (f : Feature) : f ∈ all := by cases f <;> decide

theorem all_nodup : all.Nodup := by decide

/-- A predicate on features holds everywhere iff it holds on `all`. -/
theorem forall_iff_all (p : Feature → Bool) : (∀ f, p f = true) ↔ all.all p = true := by
  rw [List.all_eq_true]
  exact ⟨fun h f _ => h f, fun h f => h f (mem_all f)⟩

instance (p : Feature → Prop) [DecidablePred p] : Decidable (∀ f, p f) :=
  decidable_of_iff (all.all fun f => decide (p f)) (by
    rw [← forall_iff_all]; simp)

/-- A CPUID output register. -/
inductive CpuidReg where
  | eax | ebx | ecx | edx
  deriving DecidableEq, Repr

/-- The register of a reply. -/
def CpuidReg.get : CpuidReg → CpuidReply → BitVec 32
  | .eax, r => r.eax
  | .ebx, r => r.ebx
  | .ecx, r => r.ecx
  | .edx, r => r.edx

/-- Where CPUID enumerates a feature: `CPUID.(EAX=leaf, ECX=subleaf):reg[bit]`. -/
structure CpuidBit where
  leaf : BitVec 32
  subleaf : BitVec 32
  reg : CpuidReg
  bit : Nat
  deriving DecidableEq, Repr

/-- The CPUID enumeration of each feature (SDM Vol. 2A, CPUID: Table 3-8 for
leaf 01H, Table 3-8/"Structured Extended Feature Flags" for leaf 07H subleaf 0,
and leaf 80000001H for LZCNT, reported as ABM/LZCNT in ECX bit 5). -/
def cpuid : Feature → CpuidBit
  | x87 => ⟨0x1, 0, .edx, 0⟩
  | sse => ⟨0x1, 0, .edx, 25⟩
  | sse2 => ⟨0x1, 0, .edx, 26⟩
  | sse3 => ⟨0x1, 0, .ecx, 0⟩
  | pclmulqdq => ⟨0x1, 0, .ecx, 1⟩
  | ssse3 => ⟨0x1, 0, .ecx, 9⟩
  | fma => ⟨0x1, 0, .ecx, 12⟩
  | sse41 => ⟨0x1, 0, .ecx, 19⟩
  | sse42 => ⟨0x1, 0, .ecx, 20⟩
  | movbe => ⟨0x1, 0, .ecx, 22⟩
  | popcnt => ⟨0x1, 0, .ecx, 23⟩
  | aes => ⟨0x1, 0, .ecx, 25⟩
  | avx => ⟨0x1, 0, .ecx, 28⟩
  | f16c => ⟨0x1, 0, .ecx, 29⟩
  | rdrand => ⟨0x1, 0, .ecx, 30⟩
  | bmi1 => ⟨0x7, 0, .ebx, 3⟩
  | avx2 => ⟨0x7, 0, .ebx, 5⟩
  | bmi2 => ⟨0x7, 0, .ebx, 8⟩
  | avx512f => ⟨0x7, 0, .ebx, 16⟩
  | avx512dq => ⟨0x7, 0, .ebx, 17⟩
  | rdseed => ⟨0x7, 0, .ebx, 18⟩
  | adx => ⟨0x7, 0, .ebx, 19⟩
  | avx512ifma => ⟨0x7, 0, .ebx, 21⟩
  | avx512cd => ⟨0x7, 0, .ebx, 28⟩
  | sha => ⟨0x7, 0, .ebx, 29⟩
  | avx512bw => ⟨0x7, 0, .ebx, 30⟩
  | avx512vl => ⟨0x7, 0, .ebx, 31⟩
  | avx512vbmi => ⟨0x7, 0, .ecx, 1⟩
  | avx512vbmi2 => ⟨0x7, 0, .ecx, 6⟩
  | gfni => ⟨0x7, 0, .ecx, 8⟩
  | vaes => ⟨0x7, 0, .ecx, 9⟩
  | vpclmulqdq => ⟨0x7, 0, .ecx, 10⟩
  | avx512vnni => ⟨0x7, 0, .ecx, 11⟩
  | avx512bitalg => ⟨0x7, 0, .ecx, 12⟩
  | avx512vpopcntdq => ⟨0x7, 0, .ecx, 14⟩
  | lzcnt => ⟨0x80000001, 0, .ecx, 5⟩

/-- XCR0 bit 1 (SSE state), bit 2 (AVX state). -/
def xcr0Avx : BitVec 64 := 0x6

/-- XCR0 bits 1, 2 and 5–7 (SSE, AVX, opmask, ZMM_Hi256, Hi16_ZMM). -/
def xcr0Avx512 : BitVec 64 := 0xE6

/-- Whether a feature is an AVX-512 feature (EVEX-only state). -/
def isAvx512 : Feature → Bool
  | avx512f | avx512cd | avx512bw | avx512dq | avx512vl | avx512ifma | avx512vbmi
  | avx512vbmi2 | avx512vnni | avx512bitalg | avx512vpopcntdq => true
  | _ => false

/-- The XCR0 state components the OS must enable for the feature's
instructions (SDM Vol. 1, §14.3 "Detection of AVX instructions" and §15.2
"Detection of AVX-512 Foundation instructions"). Features with legacy-SSE or
integer encodings need none; GFNI has a legacy SSE encoding, and its VEX/EVEX
forms additionally require `avx`/`avx512f`. -/
def xcr0 : Feature → BitVec 64
  | avx | avx2 | fma | f16c | vaes | vpclmulqdq => xcr0Avx
  | f => if f.isAvx512 then xcr0Avx512 else 0

/-- Direct dependencies (Linux `cpuid-deps.c`, FXSR/XSAVE folded; see the
module docstring). -/
def deps : Feature → List Feature
  | sse => [x87]
  | sse2 => [sse]
  | sse3 | ssse3 | sse41 | sse42 | aes | pclmulqdq | sha | gfni | f16c | avx => [sse2]
  | avx2 | fma | vaes | vpclmulqdq | avx512f => [avx]
  | f => if f.isAvx512 then [avx512f] else []

/-- Breadth-first reachability along `deps`, with fuel. -/
def reach : Nat → List Feature → List Feature
  | 0, acc => acc
  | n + 1, acc =>
    reach n (acc ++ (acc.flatMap deps).filter (fun g => !acc.contains g))

/-- The reflexive transitive closure of `deps` from one feature. -/
def ancestors (f : Feature) : List Feature := reach 8 [f]

theorem self_mem_ancestors (f : Feature) : f ∈ ancestors f := by cases f <;> decide

theorem deps_subset_ancestors (f : Feature) : ∀ g ∈ deps f, g ∈ ancestors f := by
  cases f <;> decide

theorem ancestors_trans (f : Feature) :
    ∀ g ∈ ancestors f, ∀ h ∈ ancestors g, h ∈ ancestors f := by
  cases f <;> decide

/-- The ancestors are reached by finitely many dependency steps. -/
theorem ancestors_spec (f : Feature) :
    ∀ g ∈ ancestors f, g = f ∨ ∃ h ∈ ancestors f, g ∈ deps h := by
  cases f <;> decide

end Feature

/-! ## Feature sets -/

/-- A decidable set of features. -/
@[ext] structure FeatureSet where
  has : Feature → Bool

namespace FeatureSet

open Feature

instance : Membership Feature FeatureSet := ⟨fun F f => F.has f = true⟩

theorem mem_iff (F : FeatureSet) (f : Feature) : f ∈ F ↔ F.has f = true := Iff.rfl

instance (F : FeatureSet) (f : Feature) : Decidable (f ∈ F) :=
  inferInstanceAs (Decidable (F.has f = true))

instance : HasSubset FeatureSet := ⟨fun F G => ∀ f, f ∈ F → f ∈ G⟩

instance (F G : FeatureSet) : Decidable (F ⊆ G) :=
  inferInstanceAs (Decidable (∀ f, f ∈ F → f ∈ G))

instance : DecidableEq FeatureSet := fun F G =>
  decidable_of_iff (∀ f, F.has f = G.has f) (by
    constructor
    · intro h; ext f; exact h f
    · rintro rfl _; rfl)

theorem subset_refl (F : FeatureSet) : F ⊆ F := fun _ h => h

theorem subset_trans {F G H : FeatureSet} (h₁ : F ⊆ G) (h₂ : G ⊆ H) : F ⊆ H :=
  fun f hf => h₂ f (h₁ f hf)

/-- The empty set. -/
def empty : FeatureSet := ⟨fun _ => false⟩

/-- Every feature. -/
def univ : FeatureSet := ⟨fun _ => true⟩

/-- The features of a list. -/
def ofList (fs : List Feature) : FeatureSet := ⟨fun f => fs.contains f⟩

@[simp] theorem mem_ofList (fs : List Feature) (f : Feature) : f ∈ ofList fs ↔ f ∈ fs := by
  simp [ofList, mem_iff]

instance : Union FeatureSet := ⟨fun F G => ⟨fun f => F.has f || G.has f⟩⟩

@[simp] theorem mem_union (F G : FeatureSet) (f : Feature) : f ∈ F ∪ G ↔ f ∈ F ∨ f ∈ G := by
  show (F.has f || G.has f) = true ↔ _
  simp [mem_iff]

instance : Insert Feature FeatureSet := ⟨fun f F => ⟨fun g => g == f || F.has g⟩⟩

@[simp] theorem mem_insert (F : FeatureSet) (f g : Feature) : g ∈ insert f F ↔ g = f ∨ g ∈ F := by
  show (g == f || F.has g) = true ↔ _
  simp [mem_iff]

theorem subset_union_left (F G : FeatureSet) : F ⊆ F ∪ G := fun f h => (mem_union F G f).mpr (.inl h)

theorem subset_union_right (F G : FeatureSet) : G ⊆ F ∪ G := fun f h => (mem_union F G f).mpr (.inr h)

theorem subset_insert (F : FeatureSet) (f : Feature) : F ⊆ insert f F :=
  fun g h => (mem_insert F f g).mpr (.inr h)

/-- The x86-64 baseline: x87, SSE and SSE2. -/
def baseline64 : FeatureSet := ofList [.x87, .sse, .sse2]

/-- A set is closed when it contains the dependencies of its members. -/
def Closed (F : FeatureSet) : Prop := ∀ f, f ∈ F → ∀ g ∈ f.deps, g ∈ F

instance (F : FeatureSet) : Decidable F.Closed :=
  inferInstanceAs (Decidable (∀ f, f ∈ F → ∀ g ∈ f.deps, g ∈ F))

theorem baseline64_closed : baseline64.Closed := by decide

theorem univ_closed : univ.Closed := by decide

theorem empty_closed : empty.Closed := by decide

/-- Every feature together with all of its ancestors. -/
def closure (F : FeatureSet) : FeatureSet :=
  ⟨fun f => Feature.all.any fun g => F.has g && (ancestors g).contains f⟩

theorem mem_closure {F : FeatureSet} {f : Feature} :
    f ∈ closure F ↔ ∃ g, g ∈ F ∧ f ∈ ancestors g := by
  simp only [closure, mem_iff, List.any_eq_true, Bool.and_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨g, -, hg, hf⟩; exact ⟨g, hg, hf⟩
  · rintro ⟨g, hg, hf⟩; exact ⟨g, mem_all g, hg, hf⟩

theorem subset_closure (F : FeatureSet) : F ⊆ closure F :=
  fun f h => mem_closure.mpr ⟨f, h, self_mem_ancestors f⟩

theorem closure_closed (F : FeatureSet) : (closure F).Closed := by
  intro f hf g hg
  obtain ⟨h, hh, hfh⟩ := mem_closure.mp hf
  exact mem_closure.mpr
    ⟨h, hh, ancestors_trans h f hfh g (deps_subset_ancestors f g hg)⟩

/-- A closed set contains everything `reach` adds to a subset of it. -/
theorem Closed.reach_mem {G : FeatureSet} (hG : G.Closed) :
    ∀ n (acc : List Feature), (∀ f ∈ acc, f ∈ G) → ∀ f ∈ Feature.reach n acc, f ∈ G := by
  intro n
  induction n with
  | zero => intro acc hacc; exact hacc
  | succ n ih =>
    intro acc hacc
    apply ih
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hacc f hf
    · obtain ⟨hf, -⟩ := List.mem_filter.mp hf
      obtain ⟨h, hh, hfh⟩ := List.mem_flatMap.mp hf
      exact hG h (hacc h hh) f hfh

/-- A closed set contains every ancestor of its members. -/
theorem Closed.ancestors_mem {G : FeatureSet} (hG : G.Closed) {g : Feature} (hg : g ∈ G) :
    ∀ f ∈ ancestors g, f ∈ G :=
  hG.reach_mem 8 [g] (by simpa using hg)

theorem closure_least {F G : FeatureSet} (hG : G.Closed) (h : F ⊆ G) : closure F ⊆ G := by
  intro f hf
  obtain ⟨g, hg, hfg⟩ := mem_closure.mp hf
  exact hG.ancestors_mem (h g hg) f hfg

theorem closure_mono {F G : FeatureSet} (h : F ⊆ G) : closure F ⊆ closure G :=
  closure_least (closure_closed G) (subset_trans h (subset_closure G))

theorem closure_of_closed {F : FeatureSet} (hF : F.Closed) : closure F = F := by
  ext f
  have h₁ := closure_least hF (subset_refl F) f
  have h₂ := subset_closure F f
  simp only [mem_iff] at h₁ h₂
  cases hc : (closure F).has f <;> cases hf : F.has f <;> simp_all

theorem closure_closure (F : FeatureSet) : closure (closure F) = closure F :=
  closure_of_closed (closure_closed F)

/-- The features all of whose ancestors are present: the largest closed subset. -/
def interior (F : FeatureSet) : FeatureSet :=
  ⟨fun f => (ancestors f).all F.has⟩

theorem mem_interior {F : FeatureSet} {f : Feature} :
    f ∈ interior F ↔ ∀ g ∈ ancestors f, g ∈ F := by
  simp [interior, mem_iff]

theorem interior_subset (F : FeatureSet) : interior F ⊆ F :=
  fun f h => mem_interior.mp h f (self_mem_ancestors f)

theorem interior_closed (F : FeatureSet) : (interior F).Closed := by
  intro f hf g hg
  refine mem_interior.mpr fun h hh => mem_interior.mp hf h ?_
  exact ancestors_trans f g (deps_subset_ancestors f g hg) h hh

theorem interior_greatest {F G : FeatureSet} (hG : G.Closed) (h : G ⊆ F) : G ⊆ interior F :=
  fun _ hf => mem_interior.mpr fun g hg => h g (hG.ancestors_mem hf g hg)

/-! ## From CPUID -/

/-- The CPUID leaf is within the maximum leaf the processor reports: leaf 0's
EAX for basic leaves, leaf `80000000H`'s EAX for extended leaves. -/
def leafAvailable (cpuid : BitVec 32 → BitVec 32 → CpuidReply) (leaf : BitVec 32) : Bool :=
  if leaf < 0x80000000#32 then decide (leaf ≤ (cpuid 0 0).eax)
  else decide (leaf ≤ (cpuid 0x80000000#32 0).eax)

/-- The features a processor executes, given its CPUID oracle and XCR0
(read with XGETBV): the leaf is in range, the bit is set and, when the feature
needs OS-managed state, CPUID.1:ECX.OSXSAVE[bit 27] is set and XCR0 enables
the state components (SDM Vol. 1, §14.3 and §15.2). -/
def ofCpuid (cpuid : BitVec 32 → BitVec 32 → CpuidReply) (xcr0 : BitVec 64) : FeatureSet :=
  ⟨fun f =>
    let b := f.cpuid
    leafAvailable cpuid b.leaf && (b.reg.get (cpuid b.leaf b.subleaf)).getLsbD b.bit &&
      (f.xcr0 == 0 || ((cpuid 1 0).ecx.getLsbD 27 && (xcr0 &&& f.xcr0) == f.xcr0))⟩

/-- `ofCpuid` from an explicit platform contract. -/
def ofPlatform (platform : Platform) (xcr0 : BitVec 64) : FeatureSet :=
  ofCpuid platform.cpuid xcr0

/-- A feature reported by CPUID that needs no OS-managed state is present. -/
theorem mem_ofCpuid_of_xcr0 {cpuid : BitVec 32 → BitVec 32 → CpuidReply} {xcr0 : BitVec 64}
    {f : Feature} (h0 : f.xcr0 = 0) :
    f ∈ ofCpuid cpuid xcr0 ↔ leafAvailable cpuid f.cpuid.leaf = true ∧
      (f.cpuid.reg.get (cpuid f.cpuid.leaf f.cpuid.subleaf)).getLsbD f.cpuid.bit = true := by
  simp [ofCpuid, h0, mem_iff]

/-- Without the OS enabling AVX state in XCR0, no AVX or AVX-512 feature is
present, whatever CPUID says. -/
theorem not_mem_ofCpuid_of_xcr0 {cpuid : BitVec 32 → BitVec 32 → CpuidReply} {xcr0 : BitVec 64}
    {f : Feature} (hf : f.xcr0 ≠ 0) (hx : xcr0 &&& f.xcr0 ≠ f.xcr0) :
    f ∉ ofCpuid cpuid xcr0 := by
  simp [ofCpuid, hx, mem_iff]
  intro _ _; exact hf

end FeatureSet

end Silmaril.X86.Features
