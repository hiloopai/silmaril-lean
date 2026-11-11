module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs

/-!
# Composite transition systems and divergence-observing composition

`DStrategy.ofLTS` reads finite plays, divergence and infinite plays off a
transition system; `DStrategy.comp` composes divergence-observing strategies,
creating divergence from infinite hidden chatter. `Silmaril.Games.DivLTSComp.Thms`
shows that the two agree on the parallel composition `L₁.comp L₂`: the
divergence-observing strategy of the composite system is the composite of the
components' divergence-observing strategies (`DStrategy.ofLTS_comp`),
generalising `LTS.Denotes.comp` to divergence and infinite plays.

`LTS.DivRunning L`: `L` diverges only in running positions, i.e. a silent
infinite run never starts after a trace that leaves `L` idle or waiting for an
answer. `DStrategy.ofLTS` records divergence only after running plays, so a
component that diverges while idle or waiting would make the composite diverge
(its partner running) without contributing a divergent play of its own; the
hypothesis excludes this. `LTS.SilentRunning L` (silent steps happen only in
running positions) implies it (`LTS.SilentRunning.divRunning`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace LTS

variable {E F : Sig.{u}}

/-- `L` may diverge only after traces ending in a running position. -/
def DivRunning (L : LTS E F) : Prop :=
  ∀ {s : List (Move E F)} {x : L.State}, L.Run L.init s x → L.Diverges x →
    ∃ q, Path .idle s (.run q)

/-- `L` takes silent steps only after traces ending in a running position. -/
def SilentRunning (L : LTS E F) : Prop :=
  ∀ {s : List (Move E F)} {x y : L.State}, L.Run L.init s x → L.step x none y →
    ∃ q, Path .idle s (.run q)

/-- Silent steps only when running: divergence only when running. -/
theorem SilentRunning.divRunning {L : LTS E F} (h : L.SilentRunning) : L.DivRunning :=
  fun hr hd => by
    obtain ⟨y, hy, -⟩ := hd.unfold
    exact h hr hy

end LTS

end Silmaril.Games
