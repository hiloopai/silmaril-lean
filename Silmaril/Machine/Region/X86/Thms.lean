module

public import Silmaril.Machine.Region.X86.Defs
public import Silmaril.Semantics.Region.Semantic.Thms
public import Silmaril.Semantics.Region.Simulation.Defs
import Silmaril.Proofs.Machine.Region.X86

@[expose] public section
namespace Silmaril.Machine.Region.X86
open Silmaril.Semantics.Region
open Silmaril.X86 (MState Word)
open Silmaril.X86.Decompile

theorem system_step_unique {ret : Word} {s t u : MState} {es fs : List Empty}
    (step : (system ret).step s es t) (other : (system ret).step s fs u) : es = fs ∧ t = u :=
  ⟨step.1.trans other.1.symm, Silmaril.X86.Ext.Outcome.retired.inj (step.2.symm.trans other.2)⟩

theorem system_determinate (ret : Word) : Determinate (system ret) :=
  ⟨system_step_unique, fun step halt => halt.2 _ (halt.1.symm.trans step.2)⟩

/-- Reuse the actual fetch/execute boundary for instructions that are not RET. -/
theorem system_retire {ret : Word} {s t : MState} {instr : Silmaril.X86.Ext.Instr} {size : Nat}
    (fetch : Silmaril.X86.Ext.fetch s.memory s.core.rip.toNat = .decoded instr size)
    (exec : Silmaril.X86.Ext.exec instr s.core s.memory = .ok t.core t.memory)
    (nonreturn : instr ≠ .ret) : (system ret).step s [] t := by
  refine ⟨rfl, ?_⟩
  simp [Silmaril.X86.Ext.step, fetch, exec, nonreturn]

theorem instruction_sound {d : Decoded} {s core : Silmaril.X86.State}
    {memory memory' : Silmaril.Process.Memory}
    (hrip : s.rip.toNat = d.addr) (hlen : d.size = (Silmaril.X86.Ext.encode d.instr).length)
    (exec : Silmaril.X86.Ext.exec d.instr s memory = .ok core memory') :
    (instructionTargets d).Allows core.rip.toNat := Proofs.instruction_sound hrip hlen exec

theorem listing_step {r : Silmaril.X86.Decompile.Region} {fuel : Nat} {ds : List Decoded}
    {d : Decoded} {ret : Word} {s t : MState}
    (decoded : r.decode? fuel = some ds) (loaded : r.LoadedIn s.memory)
    (hd : d ∈ ds) (hrip : s.core.rip.toNat = d.addr)
    (step : (system ret).step s [] t) : (instructionTargets d).Allows t.core.rip.toNat :=
  Proofs.listing_step decoded loaded hd hrip step

theorem listing_sound {r : Silmaril.X86.Decompile.Region} {fuel : Nat} {ds : List Decoded}
    {ret : Word} {U X : Nat → Prop} {A D : MState → Prop}
    (decoded : r.decode? fuel = some ds) (admit : ∀ s, A s → D s)
    (covered : ∀ s, D s → U s.core.rip.toNat →
      r.LoadedIn s.memory ∧ ∃ d ∈ ds, s.core.rip.toNat = d.addr)
    (preserve : ∀ s es t, D s → U s.core.rip.toNat → (system ret).step s es t →
      U t.core.rip.toNat → D t)
    (targets : ∀ d ∈ ds, ∀ l, (instructionTargets d).Allows l → ¬ U l → X l) :
    Sound (system ret) A U X := Proofs.listing_sound decoded admit covered preserve targets

theorem greatest_iff (iface : Interface) (ss : Finset Range) (entry : Nat) (exits : Finset Nat) :
    greatestRows iface ss entry exits ↔
      Valid (system iface.returnAddress) iface.wellFormed (iface.admit entry) (labels ss) entry exits :=
  Iff.rfl
end Silmaril.Machine.Region.X86
