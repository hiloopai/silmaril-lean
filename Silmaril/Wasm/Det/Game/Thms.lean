module

public import Silmaril.Wasm.Det.Game.Defs
public import Silmaril.Games.Composition.Thms
import Silmaril.Proofs.Wasm.Det.Game.Comp
import Silmaril.Proofs.Wasm.Det.Game.Pair
import Silmaril.Proofs.Wasm.Det.Game.PairStateless
import Silmaril.Proofs.Wasm.Det.Game.Handler
public import Silmaril.Games.Handler.Thms
import Silmaril.Proofs.Wasm.Det.Game.Copycat

/-!
# Determinism and statelessness of strategies, modulo traps: theorems

* `DetMod.comp`, `StatelessMod.comp`: composition `σ.comp τ` preserves determinism and
  statelessness modulo traps when the consumer `τ` is trap-strict; `Strict.comp`: composition
  preserves strictness. The proof compares two interactions at their first difference
  (`Silmaril.Proofs.Wasm.Det.Game.agree_comp`).
* `DetMod.pair`, `StatelessMod.pair`: pairing preserves determinism and statelessness modulo
  traps.
* `Strict.pair`: pairing preserves trap strictness.
* `detMod_ofHandler`, `statelessMod_ofHandler`: handler strategies are deterministic and
  stateless (for every trap predicate); `strict_ofHandler`: a handler with strict programs
  (`ProgStrict`) is trap-strict; `statelessMod_id`: copycat is stateless.
* `detMod_id`, `strict_id`: copycat is deterministic and strict.
* `comp_nondet` (**litmus**): the deterministic, strict copycat composed with the
  nondeterministic environment `ndBool` is not deterministic. Determinism of a composite needs
  determinism of the environment it is composed with.

Proofs: `Silmaril.Proofs.Wasm.Det.Game.{Inter,Comp,Pair,PairStateless,Handler,Copycat}`.
-/

public section

namespace Silmaril.Wasm.Det.Game

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- Determinism is agreement after empty histories. -/
theorem detMod_iff_agreeAfter {tF : Traps F} {σ : Strategy E F} :
    DetMod tF σ ↔ AgreeAfter tF σ [] [] :=
  Silmaril.Proofs.Wasm.Det.Game.agreeAfter_nil.symm

/-- A stateless strategy is deterministic. -/
theorem StatelessMod.detMod {tF : Traps F} {σ : Strategy E F} (h : StatelessMod tF σ) :
    DetMod tF σ :=
  detMod_iff_agreeAfter.2 (h [] [] σ.nil_mem σ.nil_mem (.nil _) (.nil _))

/-- **Composition preserves determinism modulo traps** (the consumer is strict). -/
theorem DetMod.comp {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    (hσ : DetMod tF σ) (hτ : DetMod tG τ) (hst : Strict tF tG τ) : DetMod tG (σ.comp τ) :=
  Silmaril.Proofs.Wasm.Det.Game.detMod_comp hσ hτ hst

/-- **Composition preserves statelessness modulo traps** (the consumer is strict). -/
theorem StatelessMod.comp {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    (hσ : StatelessMod tF σ) (hτ : StatelessMod tG τ) (hst : Strict tF tG τ) :
    StatelessMod tG (σ.comp τ) :=
  Silmaril.Proofs.Wasm.Det.Game.statelessMod_comp hσ hτ hst

/-- **Composition preserves strictness.** -/
theorem Strict.comp {tE : Traps E} {tF : Traps F} {tG : Traps G} {σ : Strategy E F}
    {τ : Strategy F G} (hσ : Strict tE tF σ) (hτ : Strict tF tG τ) : Strict tE tG (σ.comp τ) :=
  Silmaril.Proofs.Wasm.Det.Game.strict_comp hσ hτ

/-- **Pairing preserves determinism modulo traps.** -/
theorem DetMod.pair {F₁ F₂ : Sig.{u}} {t₁ : Traps F₁} {t₂ : Traps F₂} {σ₁ : Strategy E F₁}
    {σ₂ : Strategy E F₂} (h₁ : DetMod t₁ σ₁) (h₂ : DetMod t₂ σ₂) :
    DetMod (sumTraps t₁ t₂) (σ₁.pair σ₂) :=
  Silmaril.Proofs.Wasm.Det.Game.detMod_pair h₁ h₂

/-- **Pairing preserves statelessness modulo traps.** -/
theorem StatelessMod.pair {F₁ F₂ : Sig.{u}} {t₁ : Traps F₁} {t₂ : Traps F₂}
    {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} (h₁ : StatelessMod t₁ σ₁)
    (h₂ : StatelessMod t₂ σ₂) : StatelessMod (sumTraps t₁ t₂) (σ₁.pair σ₂) :=
  Silmaril.Proofs.Wasm.Det.Game.statelessMod_pair h₁ h₂

/-- **Pairing preserves trap strictness.** -/
theorem Strict.pair {F₁ F₂ : Sig.{u}} {tE : Traps E} {t₁ : Traps F₁} {t₂ : Traps F₂}
    {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂} (h₁ : Strict tE t₁ σ₁) (h₂ : Strict tE t₂ σ₂) :
    Strict tE (sumTraps t₁ t₂) (σ₁.pair σ₂) :=
  Silmaril.Proofs.Wasm.Det.Game.strict_pair h₁ h₂

/-- **Handler strategies are deterministic** (every trap predicate). -/
theorem detMod_ofHandler (t : Traps F) (h : Handler E F) : DetMod t (Strategy.ofHandler h) :=
  Silmaril.Proofs.Wasm.Det.Game.detMod_ofHandler t h

/-- **Handler strategies are stateless** (every trap predicate). -/
theorem statelessMod_ofHandler (t : Traps F) (h : Handler E F) :
    StatelessMod t (Strategy.ofHandler h) :=
  Silmaril.Proofs.Wasm.Det.Game.statelessMod_ofHandler t h

/-- **A handler with strict programs is trap-strict.** -/
theorem strict_ofHandler {tE : Traps E} {tF : Traps F} {h : Handler E F}
    (hh : ∀ q, ProgStrict tE (tF q) (h q)) : Strict tE tF (Strategy.ofHandler h) :=
  Silmaril.Proofs.Wasm.Det.Game.strict_ofHandler hh

/-- Copycat is stateless. -/
theorem statelessMod_id (t : Traps E) : StatelessMod t (Strategy.id E) := by
  rw [← Strategy.ofHandler_id]
  exact statelessMod_ofHandler t _

/-- Copycat is deterministic. -/
theorem detMod_id (t : Traps E) : DetMod t (Strategy.id E) :=
  Silmaril.Proofs.Wasm.Det.Game.detMod_id t

/-- Copycat is strict. -/
theorem strict_id (t : Traps E) : Strict t t (Strategy.id E) :=
  Silmaril.Proofs.Wasm.Det.Game.strict_id t

/-- `ndBool` is not deterministic. -/
theorem ndBool_not_detMod : ¬ DetMod (noTraps boolSig) ndBool :=
  Silmaril.Proofs.Wasm.Det.Game.ndBool_not_detMod

/-- **Litmus: a deterministic, strict strategy composed with a nondeterministic environment is
not deterministic.** -/
theorem comp_nondet :
    DetMod (noTraps boolSig) (Strategy.id boolSig) ∧
      Strict (noTraps boolSig) (noTraps boolSig) (Strategy.id boolSig) ∧
      ¬ DetMod (noTraps boolSig) (ndBool.comp (Strategy.id boolSig)) :=
  Silmaril.Proofs.Wasm.Det.Game.comp_nondet

end Silmaril.Wasm.Det.Game
