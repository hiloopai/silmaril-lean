module

public import Silmaril.Wasm.Det.CompIR.Defs
public import Silmaril.Wasm.Det.Game.Thms
import Silmaril.Proofs.Wasm.Det.CompIR.Den

/-!
# Determinism and statelessness of the component IR: closure under components

For an arbitrary core semantics `C` (`Silmaril.Wasm.Component.CoreSem`) and every component `c`
of the IR, with the trap answer `none` (`noneTraps`):

* `den_detMod`: if every core module is deterministic modulo traps and trap-strict
  (`CoreDet C`), so is the component (`Comp.den C c`), and so is every sub-structure it is built
  from: nested instances, wiring, adapters, `ext`;
* `den_statelessMod`: the same for statelessness (`CoreStateless C`);
* `denU_detMod`, `denU_statelessMod`, `program_detMod`: the same over `sigU` and for programs;
* `den_detMod_single`, `den_statelessMod_single`: a component with one core instance, with the
  hypothesis on that module only.

The wiring and adapter handlers are deterministic, stateless and trap-strict
(`Silmaril.Proofs.Wasm.Det.Game.{detMod_ofHandler, statelessMod_ofHandler, strict_ofHandler}`);
composition and pairing preserve the properties (`DetMod.comp`, `DetMod.pair`,
`StatelessMod.comp`, `StatelessMod.pair`, with strictness of the consumer). One mutual
induction over components, nodes and node lists proves the closure for any such property
(`Silmaril.Proofs.Wasm.Det.CompIR.den_good`).

Proofs: `Silmaril.Proofs.Wasm.Det.CompIR.Den`, `Silmaril.Proofs.Wasm.Det.Game.{Handler,
PairStateless}`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.CompIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Det.Game

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Components of deterministic core modules are deterministic** (modulo traps), and
trap-strict, over `sigU`. -/
theorem denU_detMod (hC : CoreDet C) (c : Comp M) :
    DetMod (noneTraps _) (c.denU C) ∧ Strict (noneTraps _) (noneTraps _) (c.denU C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.good_denU (fun t σ => DetMod t σ)
    (fun hσ hτ hst => DetMod.comp hσ hτ hst) (fun h₁ h₂ => DetMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.detMod_ofHandler t h) C hC c

/-- **Components of deterministic core modules are deterministic** (modulo traps), and
trap-strict, at their interface sizes. -/
theorem den_detMod (hC : CoreDet C) (c : Comp M) :
    DetMod (noneTraps _) (c.den C) ∧ Strict (noneTraps _) (noneTraps _) (c.den C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.den_good (fun t σ => DetMod t σ)
    (fun hσ hτ hst => DetMod.comp hσ hτ hst) (fun h₁ h₂ => DetMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.detMod_ofHandler t h) C hC c

/-- **Components of stateless core modules are stateless** (modulo traps), and trap-strict,
over `sigU`. -/
theorem denU_statelessMod (hC : CoreStateless C) (c : Comp M) :
    StatelessMod (noneTraps _) (c.denU C) ∧ Strict (noneTraps _) (noneTraps _) (c.denU C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.good_denU (fun t σ => StatelessMod t σ)
    (fun hσ hτ hst => StatelessMod.comp hσ hτ hst) (fun h₁ h₂ => StatelessMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.statelessMod_ofHandler t h) C hC c

/-- **Components of stateless core modules are stateless** (modulo traps), and trap-strict, at
their interface sizes. -/
theorem den_statelessMod (hC : CoreStateless C) (c : Comp M) :
    StatelessMod (noneTraps _) (c.den C) ∧ Strict (noneTraps _) (noneTraps _) (c.den C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.den_good (fun t σ => StatelessMod t σ)
    (fun hσ hτ hst => StatelessMod.comp hσ hτ hst) (fun h₁ h₂ => StatelessMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.statelessMod_ofHandler t h) C hC c

/-- **A component with one core instance is deterministic** (modulo traps) and trap-strict when
its core module is (no hypothesis on other modules). -/
theorem den_detMod_single {m : M}
    (hm : DetMod (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m))
    (I : Iface) (args : List Impl) (xs : List Export) :
    DetMod (noneTraps _) ((Comp.mk I [.core m args] xs).den C) ∧
      Strict (noneTraps _) (noneTraps _) ((Comp.mk I [.core m args] xs).den C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.den_good_single (fun t σ => DetMod t σ)
    (fun hσ hτ hst => DetMod.comp hσ hτ hst) (fun h₁ h₂ => DetMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.detMod_ofHandler t h) C hm I args xs

/-- **A component with one core instance is stateless** (modulo traps) and trap-strict when its
core module is. -/
theorem den_statelessMod_single {m : M}
    (hm : StatelessMod (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m))
    (I : Iface) (args : List Impl) (xs : List Export) :
    StatelessMod (noneTraps _) ((Comp.mk I [.core m args] xs).den C) ∧
      Strict (noneTraps _) (noneTraps _) ((Comp.mk I [.core m args] xs).den C) :=
  Silmaril.Proofs.Wasm.Det.CompIR.den_good_single (fun t σ => StatelessMod t σ)
    (fun hσ hτ hst => StatelessMod.comp hσ hτ hst) (fun h₁ h₂ => StatelessMod.pair h₁ h₂)
    (fun t h => Silmaril.Proofs.Wasm.Det.Game.statelessMod_ofHandler t h) C hm I args xs

/-- **Programs of deterministic core modules are deterministic** (modulo traps). -/
theorem program_detMod (hC : CoreDet C) (p : Program M) :
    DetMod (noneTraps _) (p.denU C) := by
  unfold Program.denU
  split
  · exact (denU_detMod C hC p.comp).1
  · exact DetMod.comp (denU_detMod C hC p.comp).1
      (Silmaril.Proofs.Wasm.Det.Game.detMod_ofHandler _ _)
      (Silmaril.Proofs.Wasm.Det.Game.strict_ofHandler
        (Silmaril.Proofs.Wasm.Det.CompIR.selectH_strict _))

end Silmaril.Wasm.Det.CompIR
