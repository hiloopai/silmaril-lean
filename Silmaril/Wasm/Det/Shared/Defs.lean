module

public import Silmaril.Wasm.Det.Game.Instance.Defs
public import Silmaril.Wasm.Game.Shared.Defs

/-!
# Determinism under store-writing hosts: definitions

`Silmaril.Wasm.Det.Core` reads imports as a shared oracle whose answers are Core results only: the
host never writes the store. Core 3.0's host interface is more general (`host h s vs
(.returned s' r)` continues in `s'`), and the store-passing game of `Silmaril.Wasm.Game.Shared`
puts the store in every question and answer. This module extends the oracle by stores.

* `SCall`: an answered import call together with the **store returned by the host**.
* `RunsS P A c tr d`: host-free steps at `P`, interrupted by the calls of `tr`, each resumed with
  its answer **in the returned store** (`resumeIn`), which must be admissible (`A s s'`: `s` the
  store at the call, `s'` the returned one). With `A` the identity relation this is
  `Silmaril.Wasm.Det.Core.Runs`.
* `DetCfgS P A c`: two such runs from `c` with the same calls, answers and returned stores that
  both reach a non-trapping stop have the same output and the same store.
* `DetModuleS P A S Entry`: every entry function is `DetCfgS` at every call state of `S` (the
  stores questions may carry), on any arguments.
* `KeepFuncs s s'`: the host keeps the function instances (it may write memories, tables,
  globals, the heap and allocate exceptions; in Core it may also only extend the store).
* `ClosedS P A Inv`: `Inv` is closed under host-free steps and under resuming an import call
  with any answer in any admissible store.
* `ShOk I A S`: the Opponent moves of the store-passing game the hypotheses talk about: export
  questions carry stores of `S`, import answers carry stores admissible for the store of the
  question.
* `DetModOn ok tF σ`: `Silmaril.Wasm.Det.Game.DetMod` restricted to plays whose moves satisfy `ok`.
* `shTraps ts`: the trap answers of the shared interface (`Answer.trap`, any store).

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- An answered import call with the store the host returned. -/
structure SCall where
  host : Nat
  args : List Val
  ans : Result
  store : Store Nat

/-- Resume the import call at context `E` of `d` with the answer `r` in the store `s'`. -/
def resumeIn (d : Config Nat) (E : Ctx) (r : Result) (s' : Store Nat) : Config Nat :=
  ⟨s', d.frame, E.fill r.toAdmin⟩

/-- **Runs against an oracle that writes the store**: host-free steps at `P`, interrupted by
the calls of `tr`, each resumed with its answer in the returned store, which is admissible
(`A`) for the store at the call. -/
inductive RunsS (P : Profile) (A : Store Nat → Store Nat → Prop) :
    Config Nat → List SCall → Config Nat → Prop where
  | stop {c d : Config Nat} (hs : Steps P (Det.noHost (H := Nat)) c d) : RunsS P A c [] d
  | call {c d e : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} {r : Result}
      {s' : Store Nat} {tr : List SCall} (hs : Steps P (Det.noHost (H := Nat)) c d)
      (hd : decompose? d.store d.code = some (E, a, h, args)) (hA : A d.store s')
      (hk : RunsS P A (resumeIn d E r s') tr e) : RunsS P A c (⟨h, args, r, s'⟩ :: tr) e

/-- **Determinism modulo traps and store-writing imports**: two runs from `c` with the same
calls, answers and returned stores that both reach a non-trapping stop have the same output and
the same store. -/
def DetCfgS (P : Profile) (A : Store Nat → Store Nat → Prop) (c : Config Nat) : Prop :=
  ∀ tr d₁ d₂ o₁ o₂, RunsS P A c tr d₁ → RunsS P A c tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ →
    o₁ = o₂ ∧ d₁.store = d₂.store

/-- **Per module, store-writing hosts**: every entry function is `DetCfgS` at every call state
of `S`, on any arguments. -/
def DetModuleS (P : Profile) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop)
    (Entry : Nat → Prop) : Prop :=
  ∀ s, S s → ∀ a, Entry a → ∀ vs, DetCfgS P A (invoke s a vs)

/-- The host keeps the function instances. -/
def KeepFuncs (s s' : Store Nat) : Prop := s'.funcs = s.funcs

/-- `Inv` is closed under host-free steps and under resuming an import call with any answer in
any admissible store. -/
structure ClosedS (P : Profile) (A : Store Nat → Store Nat → Prop) (Inv : Config Nat → Prop) :
    Prop where
  step : ∀ c d, Inv c → Step P (Det.noHost (H := Nat)) c d → Inv d
  resume : ∀ c (E : Ctx) (a h : Nat) (args : List Val) (r : Result) (s' : Store Nat), Inv c →
    decompose? c.store c.code = some (E, a, h, args) → A c.store s' → Inv (resumeIn c E r s')

/-- The trap answers of the shared interface. -/
def shTraps (ts : List FnType) : Traps (sharedSig ts) := fun _ a => a.2 = .trap

/-- The admissible moves of the store-passing game: export questions in stores of `S`, import
answers in stores admissible for the store of the question. -/
def ShOk (I : ScalarInstance) (A : Store Nat → Store Nat → Prop) (S : Store Nat → Prop) :
    Move I.shE I.shF → Prop
  | .inr (.ask f) => S f.2.1
  | .inl (.ans e a) => A e.2.1 a.1
  | _ => True

universe u

/-- **Determinism modulo traps on admissible plays**: after a trap-free play whose moves satisfy
`ok`, two next Proponent moves are equal or one of them is a trap. -/
def DetModOn {E F : Sig.{u}} (ok : Move E F → Prop) (tF : Traps F) (σ : Strategy E F) : Prop :=
  ∀ s m₁ m₂, s ++ [m₁] ∈ σ → s ++ [m₂] ∈ σ → m₁.IsP → m₂.IsP → TrapFree tF s → (∀ m ∈ s, ok m) →
    m₁ = m₂ ∨ PTrap tF m₁ ∨ PTrap tF m₂

end Silmaril.Wasm.Det.Shared
