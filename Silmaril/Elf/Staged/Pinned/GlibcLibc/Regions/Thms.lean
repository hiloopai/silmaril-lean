module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibc.Bytes
public import Silmaril.Elf.Region.CFG.Function.Thms
import Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.Regions

@[expose] public section
namespace Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions

theorem updwtmpx_complete : updwtmpxFunction.Valid F := Proofs.updwtmpx_complete

def updwtmpxCertified : Silmaril.Elf.Region.CFG.CertifiedFunction F :=
  ⟨updwtmpxFunction, updwtmpx_complete⟩

/-- Every normal first exit reaches the external tail target, conditional on
the explicit executable-loading and thread/interference invariant contract. -/
theorem updwtmpx_first_exit {Ambient : Type*}
    (c : Silmaril.Machine.Region.X86.CFG.ExecutionContract updwtmpxRow Ambient)
    {A : Ambient → Prop} (admit : ∀ s, A s → c.invariant s) :
    Silmaril.Semantics.Region.Sound c.interleaving A updwtmpxRow.Support
      (fun l => l = 0x182f40) := by
  simpa only [updwtmpxFunction, updwtmpxRow, List.mem_singleton] using updwtmpx_complete.first_exit c admit

/-- A sound partial byte row is not a complete function-extent certificate. -/
theorem prefix_cfg_valid : prefixOnly.cfg.Valid := by decide +kernel

theorem prefix_not_complete : ¬ prefixOnly.Valid F := by
  intro h
  have : 4 = 9 := h.size
  contradiction

end Silmaril.Elf.Staged.Pinned.GlibcLibc.Regions
