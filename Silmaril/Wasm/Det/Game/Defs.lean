module

public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.Handler.Defs

/-!
# Determinism and statelessness of strategies, modulo traps

Game-level counterparts of `Silmaril.Wasm.Det.Core`, for any strategy `σ : Strategy E F` of
Silmaril's game category (`Silmaril.Games`). Imports are Opponent moves: two plays are compared only
when they agree on everything Opponent did (the environment's questions and answers), which is
the oracle reading of `Silmaril.Wasm.Det.Core.Runs` in game form.

## Traps

`tF : Traps F` says which answers of the upper interface `F` are traps (for a Wasm instance:
the answer `Answer.trap`). `PTrap tF m` holds of a Proponent answer `m` to an `F`-question that
is a trap. A play is `TrapFree tF` when Proponent has not trapped in it. Traps of the lower
interface play no role in determinism: they are Opponent moves.

## Notions

* `DetMod tF σ` (**determinism modulo traps**): after a trap-free play, Proponent's next
  move is unique, unless one of the candidates is a trap. Plays after a Proponent trap are
  not constrained: the hidden state left by a trap may depend on choices.
* `AgreeAfter tF σ h₁ h₂`: the plays of `σ` after the histories `h₁` and `h₂` agree modulo
  traps: after `h₁ ++ c` and `h₂ ++ c`, for a trap-free `c`, Proponent's next moves are equal
  or one of them is a trap. `DetMod tF σ` is `AgreeAfter tF σ [] []` (`detMod_iff_agreeAfter`).
* `StatelessMod tF σ` (**statelessness modulo traps**): any two plays of `σ` that end idle
  (every question answered; traps allowed in them) are histories after which `σ` agrees. Taking
  both histories empty, a stateless strategy is deterministic.
* `Strict tE tF σ` (**trap strictness**): after Opponent answers a lower question with a trap,
  Proponent's next move, if any, is a trap. Wasm code cannot catch a trap, so instance
  strategies are strict; strictness of the consumer is what makes composition preserve
  determinism modulo traps (a hidden trap of the provider becomes a visible trap).

`ProgStrict tE tA p` (**strict programs** of a handler): after every trap answer to one of its
calls, the program returns at once a result satisfying `tA`; handlers with strict programs have
trap-strict strategies.

`ndBool` (answering `true` or `false`) is the nondeterministic environment of the litmus
`comp_nondet`.

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Game

open Silmaril.Games

universe u

/-- Which answers of a signature are traps. -/
abbrev Traps (F : Sig.{u}) : Type u := ∀ q : F.Op, F.Ar q → Prop

/-- No answer is a trap. -/
def noTraps (F : Sig.{u}) : Traps F := fun _ _ => False

/-- The traps of a sum of signatures. -/
def sumTraps {F₁ F₂ : Sig.{u}} (t₁ : Traps F₁) (t₂ : Traps F₂) : Traps (F₁ ⊕ₛ F₂)
  | .inl q => t₁ q
  | .inr q => t₂ q

variable {E F : Sig.{u}}

/-- A Proponent answer to an upper question that is a trap. -/
def PTrap (tF : Traps F) : Move E F → Prop
  | .inr (.ans q r) => tF q r
  | _ => False

/-- Proponent has not trapped in the play `s`. -/
def TrapFree (tF : Traps F) (s : List (Move E F)) : Prop := ∀ m ∈ s, ¬ PTrap tF m

/-- **Determinism modulo traps**: after a trap-free play, two next Proponent moves are equal,
or one of them is a trap. -/
def DetMod (tF : Traps F) (σ : Strategy E F) : Prop :=
  ∀ s m₁ m₂, s ++ [m₁] ∈ σ → s ++ [m₂] ∈ σ → m₁.IsP → m₂.IsP → TrapFree tF s →
    m₁ = m₂ ∨ PTrap tF m₁ ∨ PTrap tF m₂

/-- After the histories `h₁` and `h₂`, `σ` behaves the same modulo traps: after `h₁ ++ c` and
`h₂ ++ c` with `c` trap-free, two next Proponent moves are equal or one of them is a trap. -/
def AgreeAfter (tF : Traps F) (σ : Strategy E F) (h₁ h₂ : List (Move E F)) : Prop :=
  ∀ c m₁ m₂, h₁ ++ c ++ [m₁] ∈ σ → h₂ ++ c ++ [m₂] ∈ σ → m₁.IsP → m₂.IsP → TrapFree tF c →
    m₁ = m₂ ∨ PTrap tF m₁ ∨ PTrap tF m₂

/-- **Statelessness modulo traps**: after any two plays that end idle, `σ` behaves the same
modulo traps. -/
def StatelessMod (tF : Traps F) (σ : Strategy E F) : Prop :=
  ∀ h₁ h₂, h₁ ∈ σ → h₂ ∈ σ → Path .idle h₁ .idle → Path .idle h₂ .idle → AgreeAfter tF σ h₁ h₂

/-- **Trap strictness**: after Opponent answers a lower question with a trap, the next
Proponent move is a trap. -/
def Strict (tE : Traps E) (tF : Traps F) (σ : Strategy E F) : Prop :=
  ∀ s (m : E.Op) (n : E.Ar m) b, s ++ [.inl (.ans m n), b] ∈ σ → tE m n → PTrap tF b

/-! ## Strict programs -/

/-- After every trap answer of a call, the program returns at once a result satisfying `tA`. -/
inductive ProgStrict (tE : Traps E) {A : Type u} (tA : A → Prop) : Prog E A → Prop
  | pure (a : A) : ProgStrict tE tA (.pure a)
  | call {m : E.Op} {k : E.Ar m → Prog E A}
      (ht : ∀ n, tE m n → ∃ r, k n = .pure r ∧ tA r) (hk : ∀ n, ProgStrict tE tA (k n)) :
      ProgStrict tE tA (.call m k)

/-! ## A nondeterministic environment (litmus) -/

/-- One operation answered by a boolean. -/
def boolSig : Sig.{0} := ⟨Unit, fun _ => Bool⟩

/-- Answer `true` or `false`, nondeterministically. -/
def ndBool : Strategy boolSig boolSig :=
  Strategy.generate {[.inr (.ask ()), .inr (.ans () true)], [.inr (.ask ()), .inr (.ans () false)]}

end Silmaril.Wasm.Det.Game
