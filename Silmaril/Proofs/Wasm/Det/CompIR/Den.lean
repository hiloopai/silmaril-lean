module

public import Silmaril.Wasm.Det.CompIR.Defs
public import Silmaril.Proofs.Wasm.Det.Game.Handler
public import Silmaril.Proofs.Wasm.Det.Game.PairStateless
public import Silmaril.Proofs.Wasm.Det.Game.Comp

/-!
# Determinism and statelessness of the component IR: closure under the combinators

`Comp.denU` is built from handler strategies (the wiring `implsH`/`implsN`, `maskH`, `widenH`,
`narrowH`, `splitH`), copycat, pairing (`ext`) and composition. For any property `Good` of
strategies (with a trap predicate on the upper interface) closed under composition with a
strict consumer, under pairing, and holding of handler strategies, `Good` together with trap
strictness passes from the core semantics to every component (`den_good`). The trap answer of
the IR is `none` (`noneTraps`); every wiring program is trap-strict (`implsH_strict`, …): a trap
answer to a call makes the adapters return `none`.

Instances: `DetMod` (`DetMod.comp`, `DetMod.pair`, `detMod_ofHandler`) and `StatelessMod`
(`StatelessMod.comp`, `statelessMod_pair`, `statelessMod_ofHandler`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.CompIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Det.Game Silmaril.Wasm.Det.CompIR
open Silmaril.Proofs.Wasm.Det.Game

/-! ## The wiring programs are trap-strict -/

theorem target_strict (e : Nat) (tg : Target) (a : Payload) :
    ProgStrict (noneTraps _) (fun r : Option Payload => r = none) (tg.prog e a) := by
  cases tg with
  | call r =>
    by_cases h : r < e
    · simp only [Target.prog, h, ↓reduceIte]
      exact .call (fun n hn => ⟨n, rfl, hn⟩) fun _ => .pure _
    · simp only [Target.prog, h, ↓reduceIte]
      exact .pure _
  | const res => exact .pure _

theorem runChain_strict {k : Payload → Prog sigU (Option Payload)}
    (hk : ∀ a, ProgStrict (noneTraps _) (fun r : Option Payload => r = none) (k a)) :
    ∀ (c : List Adapter) (a : Payload),
      ProgStrict (noneTraps _) (fun r : Option Payload => r = none) (runChain c k a)
  | [], a => hk a
  | ad :: c, a => by
    unfold runChain
    split
    · exact .pure _
    · exact (runChain_strict hk c _).bind_pure fun r hr => by rw [hr]; rfl

theorem impl_strict (e : Nat) (im : Impl) (a : Payload) :
    ProgStrict (noneTraps _) (fun r : Option Payload => r = none) (im.prog e a) :=
  runChain_strict (target_strict e im.target) im.chain a

theorem implsH_strict (e : Nat) (ims : List Impl) (q : sigU.Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (implsH e ims q) := by
  unfold implsH
  split
  · exact impl_strict e _ _
  · exact .pure _

theorem implsN_strict (e : Nat) (ims : List Impl) (t : Nat) (q : (sigN t).Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (implsN e ims t q) :=
  implsH_strict e ims (q.1.val, q.2)

theorem maskH_strict (e : Nat) (q : sigU.Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (maskH e q) :=
  target_strict e (.call q.1) q.2

theorem widenH_strict (n : Nat) (q : sigU.Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (widenH n q) := by
  unfold widenH
  split
  · exact .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _
  · exact .pure _

theorem narrowH_strict (k : Nat) (q : (sigN k).Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (narrowH k q) :=
  .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _

theorem splitH_strict (e : Nat) (q : sigU.Op) :
    ProgStrict (sumTraps (noneTraps _) (noneTraps _)) (noneTraps _ q) (splitH e q) := by
  unfold splitH
  split
  · exact .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _
  · exact .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _

theorem selectH_strict (obs : List Nat) (q : sigU.Op) :
    ProgStrict (noneTraps _) (noneTraps _ q) (selectH obs q) := by
  unfold selectH
  split
  · exact .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _
  · exact .pure _

/-! ## The generic closure -/

section Closure

variable (Good : ∀ {E F : Silmaril.Games.Sig.{0}}, Traps F → Strategy E F → Prop)
  (hcomp : ∀ {E F G : Silmaril.Games.Sig.{0}} {tF : Traps F} {tG : Traps G} {σ : Strategy E F}
    {τ : Strategy F G}, Good tF σ → Good tG τ → Strict tF tG τ → Good tG (σ.comp τ))
  (hpair : ∀ {E F₁ F₂ : Silmaril.Games.Sig.{0}} {t₁ : Traps F₁} {t₂ : Traps F₂}
    {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}, Good t₁ σ₁ → Good t₂ σ₂ →
      Good (sumTraps t₁ t₂) (σ₁.pair σ₂))
  (hhand : ∀ {E F : Silmaril.Games.Sig.{0}} (t : Traps F) (h : Handler E F),
    Good t (Strategy.ofHandler h))

include hcomp in
/-- Composition of good strict strategies. -/
theorem good_comp {E F G : Silmaril.Games.Sig.{0}} {tE : Traps E} {tF : Traps F} {tG : Traps G}
    {σ : Strategy E F} {τ : Strategy F G} (hσ : Good tF σ ∧ Strict tE tF σ)
    (hτ : Good tG τ ∧ Strict tF tG τ) : Good tG (σ.comp τ) ∧ Strict tE tG (σ.comp τ) :=
  ⟨hcomp hσ.1 hτ.1 hτ.2, Silmaril.Proofs.Wasm.Det.Game.strict_comp hσ.2 hτ.2⟩

include hhand in
/-- A handler with strict programs. -/
theorem good_handler {E F : Silmaril.Games.Sig.{0}} {tE : Traps E} {tF : Traps F} {h : Handler E F}
    (hh : ∀ q, ProgStrict tE (tF q) (h q)) :
    Good tF (Strategy.ofHandler h) ∧ Strict tE tF (Strategy.ofHandler h) :=
  ⟨hhand tF h, strict_ofHandler hh⟩

include hcomp hpair hhand in
/-- Extending a good environment by a good instance. -/
theorem good_ext {X : Silmaril.Games.Sig.{0}} {tX : Traps X} (e : Nat) {D : Strategy X sigU}
    {N : Strategy sigU sigU} (hD : Good (noneTraps _) D ∧ Strict tX (noneTraps _) D)
    (hN : Good (noneTraps _) N ∧ Strict (noneTraps _) (noneTraps _) N) :
    Good (noneTraps _) (ext e D N) ∧ Strict tX (noneTraps _) (ext e D N) := by
  have hid : Good (noneTraps _) (Strategy.id sigU) ∧
      Strict (noneTraps _) (noneTraps _) (Strategy.id sigU) := by
    rw [← Strategy.ofHandler_id]
    exact good_handler Good hhand fun q => .call (fun r hr => ⟨r, rfl, hr⟩) fun _ => .pure _
  have hp : Good (sumTraps (noneTraps _) (noneTraps _)) ((Strategy.id sigU).pair N) ∧
      Strict (noneTraps _) (sumTraps (noneTraps _) (noneTraps _))
        ((Strategy.id sigU).pair N) :=
    ⟨hpair hid.1 hN.1, strict_pair hid.2 hN.2⟩
  exact good_comp Good hcomp hD
    (good_comp Good hcomp hp (good_handler Good hhand (splitH_strict e)))

variable {M : Type} [CoreModule M] (C : CoreSem M)
  (hC : ∀ m : M, Good (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m))

include hcomp hhand hC in
/-- A core instance with its wiring. -/
theorem good_coreNode (e : Nat) (m : M) (args : List Impl) :
    Good (noneTraps _) (coreNode C e m args) ∧
      Strict (noneTraps _) (noneTraps _) (coreNode C e m args) :=
  good_comp Good hcomp (good_handler Good hhand (implsN_strict e args _))
    (good_comp Good hcomp (hC m) (good_handler Good hhand (widenH_strict _)))

set_option linter.unusedSectionVars false in
include hcomp hpair hhand hC in
mutual
/-- **Every component is good and strict over `sigU`.** -/
theorem good_denU : ∀ c : Comp M, Good (noneTraps _) (c.denU C) ∧
    Strict (noneTraps _) (noneTraps _) (c.denU C)
  | .mk I ns xs => by
    rw [Comp.denU]
    exact good_comp Good hcomp
      (good_denNodes I.length ns (good_handler Good hhand (maskH_strict I.length)))
      (good_handler Good hhand (implsH_strict _ _))

/-- Extending a good environment by good nodes. -/
theorem good_denNodes {X : Silmaril.Games.Sig.{0}} {tX : Traps X} :
    ∀ (e : Nat) (ns : List (Node M)) {D : Strategy X sigU},
      Good (noneTraps _) D ∧ Strict tX (noneTraps _) D →
      Good (noneTraps _) (denNodes C e ns D) ∧ Strict tX (noneTraps _) (denNodes C e ns D)
  | _, [], _, hD => by rw [denNodes]; exact hD
  | e, n :: ns, _, hD => by
    rw [denNodes]
    exact good_denNodes (e + n.width) ns (good_ext Good hcomp hpair hhand e hD (good_node e n))

/-- Every node is good and strict. -/
theorem good_node : ∀ (e : Nat) (n : Node M), Good (noneTraps _) (Node.den C e n) ∧
    Strict (noneTraps _) (noneTraps _) (Node.den C e n)
  | e, .core m args => by
    rw [Node.den]
    exact good_coreNode Good hcomp hhand C hC e m args
  | e, .inst c args => by
    rw [Node.den]
    exact good_comp Good hcomp (good_handler Good hhand (implsH_strict e args)) (good_denU c)
end

include hcomp hpair hhand hC in
/-- **Every component is good and strict at its interface sizes.** -/
theorem den_good (c : Comp M) :
    Good (noneTraps _) (c.den C) ∧ Strict (noneTraps _) (noneTraps _) (c.den C) :=
  good_comp Good hcomp
    (good_comp Good hcomp (good_handler Good hhand (widenH_strict _)) (good_denU Good hcomp hpair
      hhand C hC c))
    (good_handler Good hhand (narrowH_strict _))

include hcomp hpair hhand in
/-- **A component with one core instance is good and strict** when its core module is (no
hypothesis on other modules). -/
theorem den_good_single {M : Type} [CoreModule M] (C : CoreSem M) {m : M}
    (hm : Good (noneTraps _) (C.sem m) ∧ Strict (noneTraps _) (noneTraps _) (C.sem m))
    (I : Iface) (args : List Impl) (xs : List Export) :
    Good (noneTraps _) ((Comp.mk I [.core m args] xs).den C) ∧
      Strict (noneTraps _) (noneTraps _) ((Comp.mk I [.core m args] xs).den C) := by
  have hn : Good (noneTraps _) (coreNode C I.length m args) ∧
      Strict (noneTraps _) (noneTraps _) (coreNode C I.length m args) :=
    good_comp Good hcomp (good_handler Good hhand (implsN_strict _ args _))
      (good_comp Good hcomp hm (good_handler Good hhand (widenH_strict _)))
  unfold Comp.den atSizes
  rw [Comp.denU, denNodes, denNodes, Node.den]
  exact good_comp Good hcomp
    (good_comp Good hcomp (good_handler Good hhand (widenH_strict _))
      (good_comp Good hcomp
        (good_ext Good hcomp hpair hhand _ (good_handler Good hhand (maskH_strict _)) hn)
        (good_handler Good hhand (implsH_strict _ _))))
    (good_handler Good hhand (narrowH_strict _))

end Closure

end Silmaril.Proofs.Wasm.Det.CompIR
