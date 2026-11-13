module

public import Silmaril.Wasi.Host.Defs
public import Silmaril.Games.Zip.Defs

@[expose] public section

/-!
# WASI hosts: linking theorems

* `htrace_zip`, `xtrace_zip`: in an interaction of a host and a component, the host's answers
  are the host view of the component's events, and the export events of the linked system are
  the export view of the component's events.
* **`link_sat`**: if a component satisfies `ag (A ∘ hostView) (G ∘ expView)` and a host
  satisfies the theory `A`, the linked system satisfies `G` on its export events. With
  `forall_hosts`: a component proved under the theory `A` with uninterpreted imports is correct
  over **every** host satisfying `A`, whatever its lower interface. `link_satP` is the protocol
  form (`agP T (onExp G)`).
* `ofPred_sat`, `le_ofPred`: `ofPred P` satisfies `P` and is the largest host that does (the
  loose host); `loose_sat`; `concrete_sat`: a concrete host satisfies every theory its
  implementation's answer sequences satisfy.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

variable {Y : Sig.{0}} {I X : Set FnName}

/-- The host's answers are the host view of the component's events. -/
theorem htrace_zip {s : List (Move Y (nsig I))} {t : List (Move (nsig I) (nsig X))}
    {p : List (Move Y (nsig X))} (hz : Zip s t p) : htrace s = hostView (wtrace t) := by
  induction hz with
  | nil => rfl
  | left _ _ ih => exact ih
  | right c _ ih => cases c <;> exact ih
  | sync b _ ih =>
    cases b with
    | ask m => exact ih
    | ans m n => exact congrArg (List.cons _) ih

/-- The export events of the linked system are the export view of the component's events. -/
theorem xtrace_zip {s : List (Move Y (nsig I))} {t : List (Move (nsig I) (nsig X))}
    {p : List (Move Y (nsig X))} (hz : Zip s t p) : xtrace p = expView (wtrace t) := by
  induction hz with
  | nil => rfl
  | left _ _ ih => exact ih
  | right c _ ih =>
    cases c with
    | ask q => exact congrArg (List.cons _) ih
    | ans q n => exact congrArg (List.cons _) ih
  | sync b _ ih => cases b <;> exact ih

/-- **Linking**: a component correct under the theory `A` is correct over a host satisfying
`A`. -/
theorem link_sat {A G : List WEv → Prop} {η : Host Y I} {σ : Strategy (nsig I) (nsig X)}
    (hσ : (ag (fun t => A (hostView t)) (fun t => G (expView t))).holds σ)
    (hη : (hostSat A).holds η) : ∀ p ∈ link η σ, G (xtrace p) := by
  rintro p ⟨s, hs, t, ht, hz⟩
  have hA : A (hostView (wtrace t)) := htrace_zip hz ▸ hη s hs
  exact (xtrace_zip hz).symm ▸ hσ t ht hA

/-- **Correct over every host**: the same for all hosts satisfying `A` at once. -/
theorem forall_hosts {A G : List WEv → Prop} {σ : Strategy (nsig I) (nsig X)}
    (hσ : (ag (fun t => A (hostView t)) (fun t => G (expView t))).holds σ) :
    ∀ (Y : Sig.{0}) (η : Host Y I), (hostSat A).holds η → ∀ p ∈ link η σ, G (xtrace p) :=
  fun _ _ hη => link_sat hσ hη

/-- Runs of `onExp G` are runs of `G` on the export view. -/
theorem run_onExp {S : Type} (G : Protocol S WEv) (q : S) (t : List WEv) :
    (onExp G).run q t = G.run q (expView t) := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih =>
    cases he : e.isExp with
    | true =>
      show ((if e.isExp then G.step q e else some q).bind fun q' => (onExp G).run q' t) =
        G.run q (List.filter WEv.isExp (e :: t))
      rw [he, List.filter_cons_of_pos he]
      exact congrArg (Option.bind _) (funext ih)
    | false =>
      show ((if e.isExp then G.step q e else some q).bind fun q' => (onExp G).run q' t) =
        G.run q (List.filter WEv.isExp (e :: t))
      rw [he, List.filter_cons_of_neg (by simp [he])]
      exact ih q

/-- `onExp G` accepts iff `G` accepts the export view. -/
theorem accepts_onExp {S : Type} (G : Protocol S WEv) (t : List WEv) :
    (onExp G).Accepts t ↔ G.Accepts (expView t) := by
  unfold Protocol.Accepts
  rw [show (onExp G).init = G.init from rfl, run_onExp]

/-- **Linking**, protocol form. -/
theorem link_satP {S S' : Type} {T : Protocol S WEv} {G : Protocol S' WEv} {η : Host Y I}
    {σ : Strategy (nsig I) (nsig X)} (hσ : (agP T (onExp G)).holds σ)
    (hη : (hostSat T.Accepts).holds η) : ∀ p ∈ link η σ, G.Accepts (xtrace p) :=
  link_sat (A := T.Accepts) (G := G.Accepts)
    (fun s hs hA => (accepts_onExp G _).1 (hσ s hs hA)) hη

/-- The host of `P` satisfies `P`. -/
theorem ofPred_sat (P : List WEv → Prop) (hP : PrefixClosed P) :
    (hostSat P).holds (ofPred (Y := Y) (I := I) P hP) :=
  fun _ hs => hs.2

/-- **The loose host is the largest host satisfying the theory.** -/
theorem le_ofPred {P : List WEv → Prop} (hP : PrefixClosed P) {η : Host Y I}
    (hη : (hostSat P).holds η) : η ≤ ofPred P hP :=
  fun s hs => ⟨η.legal hs, hη s hs⟩

/-- The loose host of a protocol satisfies it. -/
theorem loose_sat {S : Type} (T : Protocol S WEv) :
    (hostSat T.Accepts).holds (loose (Y := Y) (I := I) T) :=
  ofPred_sat _ _

/-- **A concrete host satisfies every theory satisfied by its answer sequences.** -/
theorem concrete_sat (impl : Impl) {P : List WEv → Prop} (h : ∀ t, Follows impl t → P t) :
    (hostSat P).holds (concrete (Y := Y) (I := I) impl) :=
  fun _ hs => h _ hs.2

end Silmaril.Wasi
