module

public import Silmaril.Process.LPS.NativeX86Families
public import Silmaril.Process.LPS.X86Legacy
public import Silmaril.Process.LPS.Machines.X86NativeLaunch

/-! # Composing native reference families and legacy x86 extensions

The explicit system bundles the chosen dispatch and refusal policy. Legacy
aliases use their paired backend for both; other calls use the supplied native
filter. This is an additional option, leaving the previous native defaults
unchanged. The ten legacy adapters and ARCH_SET_FS are outside the ninety
reference slots. The builder checks duplicate numbers and family keys, not
the semantic adequacy of the supplied specs or refusal policy.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86

def tableWithLegacy (reference families : List SpecArm) (backend : Legacy.Backend) : List SpecArm :=
  Legacy.arms backend ++ archPrctlArm :: tableWithFamilies reference families

/-- Route aliases before the ordinary native-number refusal adapter, using
the same legacy selection as the alias specification. -/
def refusalWithLegacy (backend : Legacy.Backend) (native : RefusalFilter) : RefusalFilter :=
  fun input model effect =>
    if input.sysno.toNat ∈ armNumbers (Legacy.arms backend) then
      Legacy.refused backend input model effect
    else native input model effect

structure System where
  arms : List SpecArm
  uniqueNumbers : (armNumbers arms).Nodup
  refused : RefusalFilter

def System.spec (system : System) : Sys SyscallEffect := dispatch system.arms

def systemWithLegacy (reference families : List SpecArm) (backend : Legacy.Backend)
    (nativeRefused : RefusalFilter) : Option System :=
  if valid : FamiliesWfFor reference families ∧ (armNumbers (tableWithLegacy reference families backend)).Nodup then
    some ⟨tableWithLegacy reference families backend, valid.2,
      refusalWithLegacy backend nativeRefused⟩
  else none

/-- The same explicit system can initialize canonical, Wire or oracle machines.
The existing checked x86 snapshot/entry API supplies the launch premises. -/
def System.run (system : System) (isa : UserIsa) (snapshot : Machines.X86Launch.Snapshot)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Behavior :=
  Machines.X86Launch.runWith isa system.spec system.refused snapshot limit entry input

def System.RunBudgetRefused (system : System) (isa : UserIsa)
    (snapshot : Machines.X86Launch.Snapshot) (limit : Int) (entry : ExecEntry)
    (input : ProcInput) : Prop :=
  NativeX86.RunBudgetRefusedWithStack isa Machines.X86Launch.entryStack
    system.spec system.refused snapshot.image limit entry input

/-- The base catalogue and the architecture-only entries have disjoint numbers. -/
theorem legacy_disjoint_reference (backend : Legacy.Backend) :
    ∀ number ∈ armNumbers (Legacy.arms backend),
      number ∉ numbers.map NativeNumber.nativeNo := by
  rw [Legacy.arm_numbers]
  decide

theorem legacy_and_archPrctl_disjoint (backend : Legacy.Backend) :
    archPrctlArm.no ∉ armNumbers (Legacy.arms backend) := by
  rw [Legacy.arm_numbers]
  decide

theorem systemWithLegacy_numbers (reference families : List SpecArm) (backend : Legacy.Backend) :
    armNumbers (tableWithLegacy reference families backend) =
      [2, 4, 6, 7, 21, 22, 33, 87, 89, 97, 158] ++ armNumbers (table reference) := by
  simp [tableWithLegacy, armNumbers, Legacy.arms, archPrctlArm, arm,
    tableWithFamilies, List.map_map, Function.comp_def]

theorem systemWithLegacy_length (families : List SpecArm) (backend : Legacy.Backend) :
    (tableWithLegacy specTable families backend).length = 101 := by
  simp [tableWithLegacy, Legacy.arms, nativeFamilies_length]

theorem refusalWithLegacy_alias (backend : Legacy.Backend) (native : RefusalFilter)
    (input : SyscallInput) (model : Model) (effect : SyscallEffect)
    (aliasNumber : input.sysno.toNat ∈ armNumbers (Legacy.arms backend)) :
    refusalWithLegacy backend native input model effect ↔ Legacy.refused backend input model effect := by
  simp [refusalWithLegacy, aliasNumber]

theorem refusalWithLegacy_native (backend : Legacy.Backend) (native : RefusalFilter)
    (input : SyscallInput) (model : Model) (effect : SyscallEffect)
    (nativeNumber : input.sysno.toNat ∉ armNumbers (Legacy.arms backend)) :
    refusalWithLegacy backend native input model effect ↔ native input model effect := by
  simp [refusalWithLegacy, nativeNumber]

end Silmaril.Process.LPS.NativeX86
