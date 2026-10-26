module

public import Silmaril.Process.LPS.Machines.X86Launch
public import Silmaril.Process.LPS.Machines.X86ArchPrctl
public import Silmaril.Process.LPS.Machines.X86Wire
public import Silmaril.Process.LPS.NativeX86Budget

/-! # Native x86 launch defaults

The fixed static x86 loader, native syscall table (including ARCH_SET_FS),
native refusal filter and native allocation-budget classifier are selected
together here. The literal reference-numbered launch and diagnostic remain
available independently. Both canonical and Wire machines report instruction
fetches and data accesses to the same actual LPS materializer.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines.X86NativeLaunch

def runWith (isa : UserIsa) (refusals : SpuriousCfg) (snapshot : X86Launch.Snapshot)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Behavior :=
  X86Launch.runWith isa NativeX86.extendedSyscallSpec
    (NativeX86.defaultRefusalFilter refusals) snapshot limit entry input

/-- Native budget exclusion uses the same stack initializer, syscall spec and
refusal filter as `runWith`, including native brk/mmap allocation refusals. -/
def RunBudgetRefused (isa : UserIsa) (refusals : SpuriousCfg) (snapshot : X86Launch.Snapshot)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  NativeX86.RunBudgetRefusedWithStack isa X86Launch.entryStack NativeX86.extendedSyscallSpec
    (NativeX86.defaultRefusalFilter refusals) snapshot.image limit entry input

def BudgetSafe (isa : UserIsa) (refusals : SpuriousCfg) (snapshot : X86Launch.Snapshot)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Prop :=
  ¬ RunBudgetRefused isa refusals snapshot limit entry input

def canonical (refusals : SpuriousCfg) (snapshot : X86Launch.Snapshot)
    (limit : Int) (entry : ExecEntry) (input : ProcInput) : Behavior :=
  runWith x86ExtNative refusals snapshot limit entry input

def wire (platform : Silmaril.X86.Ext.Wire.Platform) (refusals : SpuriousCfg)
    (snapshot : X86Launch.Snapshot) (limit : Int) (entry : ExecEntry) (input : ProcInput) : Behavior :=
  runWith (x86Wire platform) refusals snapshot limit entry input

theorem RunBudgetRefused_start (isa : UserIsa) (refusals : SpuriousCfg)
    (snapshot : X86Launch.Snapshot) (limit : Int) (entry : ExecEntry) (input : ProcInput) :
    RunBudgetRefused isa refusals snapshot limit entry input ↔
      NativeX86.RunBudgetRefusedFrom isa snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter refusals) (X86Launch.init isa snapshot entry limit input) :=
  Iff.rfl

/-- A safe-budget assumption excludes a refusal already at the initial state;
the zero-step path is included, rather than requiring the program to advance. -/
theorem BudgetSafe_initial (isa : UserIsa) (refusals : SpuriousCfg)
    (snapshot : X86Launch.Snapshot) (limit : Int) (entry : ExecEntry) (input : ProcInput)
    (safe : BudgetSafe isa refusals snapshot limit entry input) :
    ¬ NativeX86.BudgetRefusedAt isa snapshot.image.segments NativeX86.extendedSyscallSpec
      (X86Launch.init isa snapshot entry limit input) := by
  intro refused
  exact safe ⟨[], X86Launch.init isa snapshot entry limit input, .refl _, refused⟩

end Silmaril.Process.LPS.Machines.X86NativeLaunch
