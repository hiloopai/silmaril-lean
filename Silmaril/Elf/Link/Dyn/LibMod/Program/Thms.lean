module

public import Silmaril.Elf.Link.Dyn.LibMod.Program.Defs
public import Silmaril.Elf.Link.Dyn.LibMod.Thms

/-!
# A program on the C-runtime machine: from `main` to real execution

PROVED (standard axioms), names in `Silmaril.Elf.Link.Dyn.LibMod`:

* `VerifiedCrt.verified`: the claim on the C-runtime machine implies the Program API's claim;
* `realisesWorld_program`: the realisation of a program's process world follows from the
  per-entry-point Tasks (the gate, `__libc_start_main`, `__cxa_finalize`, each import); the lazy
  resolver is unused (the Program API's worlds bind eagerly);
* **`realVerified_of`**: the claim on the C-runtime machine, initialisation and the realisation
  of the library give the claim about real execution.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.LibMod

open Silmaril.X86 (Word)
open Silmaril.Elf.Link.Dyn.Proc (PState)
open Silmaril.Elf.Link.Dyn.Program (Bin LibPin Spec Tier LibTable Std World Placed AtStart Observed world lib)

/-- **The C-runtime claim implies the process-model claim.** -/
theorem VerifiedCrt.verified {M : Mod} {B : Bin} {libc ld : LibPin} {spec : Spec} {tier : Tier}
    {L : LibTable} {env : Std → Prop} (h : VerifiedCrt M B libc ld spec tier L env) :
    Program.Verified B libc ld spec tier L env := by
  intro w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P hs
  exact must_proc (h w hw Fc Fl hc hl S hfs henv b lb ldb res gate ifn args s hload P hs)

/-- **The library realises a program's process world** once each entry point does. -/
theorem realisesWorld_program {X : Real} {M : Mod} {B : Bin} {L : LibTable}
    (hg : Task.crtGate X M B L) (hs : Task.crtStartMain X M B L) (hc : Task.crtCxaFinalize X M B L)
    (hn : ∀ i ∈ B.imports, Task.crtNamed X M B L i.name i.off) :
    ∀ S w b lb gate args fs, Placed B b lb gate →
      RealisesWorld X (M S lb) (runWorld B L S w b lb gate args fs) := by
  intro S w b lb gate args fs P
  refine ⟨hg S w b lb gate args fs P, fun e f hm _ => ?_, fun res slots hl _ => ?_⟩
  · simp only [runWorld, world, Program.world0, List.cons_append, List.nil_append, List.mem_cons,
      Prod.mk.injEq, List.mem_map] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, hi, he⟩
    · exact hs S w b lb gate args fs P
    · exact hc S w b lb gate args fs P
    · obtain ⟨rfl, rfl⟩ := he
      exact hn i hi S w b lb gate args fs P
  · simp [runWorld, world, Program.world0] at hl

/-- **From `main` on the C-runtime machine to real execution** (`LibMod.crt_sound`). -/
theorem realVerified_of {X : Real} {M : Mod} {B : Bin} {libc ld : LibPin} {spec : Spec} {tier : Tier}
    {L : LibTable} {env : Std → Prop} {start : World → X.τ → Prop}
    (hv : VerifiedCrt M B libc ld spec tier L env) (hi : Task.crtInit X M B libc ld L env start)
    (hr : ∀ S w b lb gate args fs, Placed B b lb gate →
      RealisesWorld X (M S lb) (runWorld B L S w b lb gate args fs)) :
    RealVerified X M spec tier start := by
  intro w hw c hc
  obtain ⟨Fc, Fl, S, b, lb, ldb, res, gate, ifn, args, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hi w c hc
  have hm := hv w hw Fc Fl h1 h2 S h3 h4 b lb ldb res gate ifn args s h5 h6 h7
  obtain ⟨c', hr', a', hrel, hq⟩ := crt_sound (hr S w b lb gate args s.m.core.fsBase h6) hm h8
  exact ⟨c', hr', S, lb, a', hrel, hq⟩

end Silmaril.Elf.Link.Dyn.LibMod
