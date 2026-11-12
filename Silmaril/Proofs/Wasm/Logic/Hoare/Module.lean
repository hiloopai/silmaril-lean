module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Control

/-!
# The every-run logic: guarded validity of specification contexts

`CtxSat P host Γi Γe` says: for every step index `n`, whenever all
specifications of `Γi` and `Γe` hold for `n` steps, those of `Γe` hold for
`n + 1` steps. It is a statement about two specification contexts over the
**closed-world** store semantics `Step P host`: every function a specification
calls, including those of `Γi`, runs the code the store holds, and `Γi` must be
shown valid (`Ctx.Valid`) against the same semantics before anything follows.
It splits a proof over one store into guarded pieces (mutual recursion, including
across groups of functions); it is **not** modular reasoning about unknown import
code and mentions no module. Open modules, whose imports are calls into the
environment, are `Silmaril.Wasm.Logic.Open` (`Open.ModuleSat`).

* `CtxSat.valid`: valid imports give valid exports (Löb induction);
* `CtxSat.link`: two contexts whose imports are provided by each other's exports
  or by common imports `Γi` give their joint exports under `Γi`, including when
  they call each other (mutual recursion);
* `CtxSat.weaken`: weaker exports, stronger imports.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Every specification of `Γ` is in `Γ'`. -/
def Ctx.Le (Γ Γ' : Ctx H) : Prop := ∀ a S, Γ a = some S → Γ' a = some S

/-- Two contexts side by side (the first wins where both specify). -/
def Ctx.union (Γ Γ' : Ctx H) : Ctx H := fun a => (Γ a).orElse fun _ => Γ' a

/-- The context with no specification. -/
def Ctx.empty : Ctx H := fun _ => none

theorem Ctx.ValidAt.of_le {n : Nat} {Γ Γ' : Ctx H} (hle : Ctx.Le Γ Γ')
    (h : Ctx.ValidAt P host n Γ') : Ctx.ValidAt P host n Γ :=
  fun a S hS => h a S (hle a S hS)

theorem Ctx.union_some {Γ Γ' : Ctx H} {a : Nat} {S : FSpec H} (h : Ctx.union Γ Γ' a = some S) :
    Γ a = some S ∨ Γ' a = some S := by
  unfold Ctx.union at h
  cases hg : Γ a with
  | none => rw [hg] at h; exact .inr h
  | some S' => rw [hg] at h; exact .inl h

theorem Ctx.ValidAt.union {n : Nat} {Γ Γ' : Ctx H} (h : Ctx.ValidAt P host n Γ)
    (h' : Ctx.ValidAt P host n Γ') : Ctx.ValidAt P host n (Ctx.union Γ Γ') := fun a S hS =>
  (Ctx.union_some hS).elim (h a S) (h' a S)

theorem Ctx.ValidAt.union_left {n : Nat} {Γ Γ' : Ctx H}
    (h : Ctx.ValidAt P host n (Ctx.union Γ Γ')) : Ctx.ValidAt P host n Γ := fun a S hS =>
  h a S (by simp [Ctx.union, hS])

theorem Ctx.ValidAt.union_right {n : Nat} {Γ Γ' : Ctx H} (hd : ∀ a, Γ a = none ∨ Γ' a = none)
    (h : Ctx.ValidAt P host n (Ctx.union Γ Γ')) : Ctx.ValidAt P host n Γ' := fun a S hS => by
  rcases hd a with hn | hn
  · exact h a S (by simp [Ctx.union, hn, hS])
  · rw [hn] at hS; cases hS

/-- **Guarded validity of `Γe` relative to `Γi`** over the closed-world semantics. -/
def CtxSat (P : Profile) (host : HostSemantics H) (Γi Γe : Ctx H) : Prop :=
  ∀ n, Ctx.ValidAt P host n Γi → Ctx.ValidAt P host n Γe → Ctx.ValidAt P host (n + 1) Γe

/-- Valid imports give valid exports. -/
theorem CtxSat.valid {Γi Γe : Ctx H} (hm : CtxSat P host Γi Γe)
    (hi : Ctx.Valid P host Γi) : Ctx.Valid P host Γe :=
  Ctx.valid_of_step fun n h => hm n (hi n) h

/-- Weaker exports and stronger imports. -/
theorem CtxSat.weaken {Γi Γi' Γe Γe' : Ctx H} (hm : CtxSat P host Γi Γe)
    (hi : Ctx.Le Γi Γi') (he : Ctx.Le Γe' Γe) (hall : ∀ n, Ctx.ValidAt P host n Γe' →
      Ctx.ValidAt P host n Γe) : CtxSat P host Γi' Γe' :=
  fun n hvi hve => (hm n (hvi.of_le hi) (hall n hve)).of_le he

/-- **Joining contexts.** Two contexts whose imports are provided by the common
imports `Γi` or by each other's exports give their joint exports under `Γi`. The
exports are disjoint. -/
theorem CtxSat.link {Γi Γi₁ Γi₂ Γe₁ Γe₂ : Ctx H} (h₁ : CtxSat P host Γi₁ Γe₁)
    (h₂ : CtxSat P host Γi₂ Γe₂) (hd : ∀ a, Γe₁ a = none ∨ Γe₂ a = none)
    (hi₁ : ∀ n, Ctx.ValidAt P host n Γi → Ctx.ValidAt P host n Γe₂ → Ctx.ValidAt P host n Γi₁)
    (hi₂ : ∀ n, Ctx.ValidAt P host n Γi → Ctx.ValidAt P host n Γe₁ → Ctx.ValidAt P host n Γi₂) :
    CtxSat P host Γi (Ctx.union Γe₁ Γe₂) := by
  intro n hi he
  have he₁ : Ctx.ValidAt P host n Γe₁ := he.union_left
  have he₂ : Ctx.ValidAt P host n Γe₂ := he.union_right hd
  exact (h₁ n (hi₁ n hi he₂) he₁).union (h₂ n (hi₂ n hi he₁) he₂)

/-- A context of specifications each proved from its body for `n + 1` steps,
assuming the contexts for `n` steps. -/
theorem CtxSat.of_bodies {Γi Γe : Ctx H}
    (h : ∀ n, Ctx.ValidAt P host n Γi → Ctx.ValidAt P host n Γe → ∀ a S, Γe a = some S →
      FSpecAt P host (n + 1) a S) : CtxSat P host Γi Γe :=
  fun n hi he a S hS => h n hi he a S hS

end Silmaril.Wasm.Logic.Hoare
