module

public import Silmaril.Wasi.Converse.Defs
public import Silmaril.Wasi.Host.Thms

@[expose] public section

/-!
# The converse of WASI linking, through the loose host

* `zip_split`: a component play `t` and its host half `hplay t` interact to the export part
  `xplay t`; `path_hplay`, `legal_hplay`: the host half of a legal play is legal (the host
  automaton tracks the component's pending import call).
* `hplay_mem_ofPred`: the host half of a play whose import answers satisfy `A` is a play of the
  loose host `ofPred A`.
* **`ag_of_link_loose`** (the converse of `link_sat`): a component whose link over the loose host
  of `A` satisfies `G` on its export events satisfies `ag (A ∘ hostView) (G ∘ expView)`.
  **`link_loose_iff`**: the two are equivalent; **`every_host_iff`**: correctness over every
  host satisfying `A` (any fixed lower interface `Y`) is equivalent to the sentence;
  `link_looseP_iff`: the protocol form with `agP T (onExp G)` and `loose T`.

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)

variable {Y : Sig.{0}} {I X : Set FnName}

/-- A component play and its host half interact to the export part of the play. -/
theorem zip_split (t : List (Move (nsig I) (nsig X))) :
    Zip (hplay (Y := Y) t) t (xplay t) := by
  induction t with
  | nil => exact .nil
  | cons o t ih =>
    rcases o with e | e
    · exact .sync e ih
    · exact .right e ih

/-- The host half follows the host automaton, at the host positions of the component's. -/
theorem path_hplay {x y : Pos (nsig I) (nsig X)} {t : List (Move (nsig I) (nsig X))}
    (h : Path x t y) : Path (hpos (Y := Y) x) (hplay t) (hpos y) := by
  induction h with
  | nil x => exact .nil _
  | cons st _ ih =>
    cases st with
    | ask q => exact ih
    | call q m => exact .cons (Step.ask m) ih
    | reply q m n => exact .cons (Step.ret m n) ih
    | ret q r => exact ih

/-- **The host half of a legal play is legal.** -/
theorem legal_hplay {t : List (Move (nsig I) (nsig X))} (ht : Legal t) :
    Legal (hplay (Y := Y) t) :=
  let ⟨_, hp⟩ := ht
  ⟨_, path_hplay hp⟩

/-- The host half of a play whose import answers satisfy `A` is a play of the loose host. -/
theorem hplay_mem_ofPred {A : List WEv → Prop} (hA : PrefixClosed A)
    {σ : Strategy (nsig I) (nsig X)} {t : List (Move (nsig I) (nsig X))} (ht : t ∈ σ)
    (hAt : A (hostView (wtrace t))) : hplay (Y := Y) t ∈ ofPred (Y := Y) (I := I) A hA :=
  ⟨legal_hplay (σ.legal ht), (htrace_zip (zip_split (Y := Y) t)).symm ▸ hAt⟩

/-- **The converse of `link_sat`**: a component correct over the loose host of `A` satisfies the
assume–guarantee sentence. -/
theorem ag_of_link_loose {A G : List WEv → Prop} (hA : PrefixClosed A)
    {σ : Strategy (nsig I) (nsig X)}
    (h : ∀ p ∈ link (ofPred (Y := Y) A hA) σ, G (xtrace p)) :
    (ag (fun t => A (hostView t)) (fun t => G (expView t))).holds σ := fun t ht hAt => by
  have hG := h (xplay t) ⟨hplay t, hplay_mem_ofPred hA ht hAt, t, ht, zip_split t⟩
  rw [xtrace_zip (zip_split (Y := Y) t)] at hG
  exact hG

/-- **Linking over the loose host characterises the assume–guarantee sentence.** -/
theorem link_loose_iff {A G : List WEv → Prop} (hA : PrefixClosed A)
    {σ : Strategy (nsig I) (nsig X)} :
    (∀ p ∈ link (ofPred (Y := Y) A hA) σ, G (xtrace p)) ↔
      (ag (fun t => A (hostView t)) (fun t => G (expView t))).holds σ :=
  ⟨ag_of_link_loose hA, fun hσ => link_sat hσ (ofPred_sat A hA)⟩

/-- **Correct over every host iff the sentence holds** (for any fixed lower interface `Y`). -/
theorem every_host_iff {A G : List WEv → Prop} (hA : PrefixClosed A)
    {σ : Strategy (nsig I) (nsig X)} :
    (∀ η : Host Y I, (hostSat A).holds η → ∀ p ∈ link η σ, G (xtrace p)) ↔
      (ag (fun t => A (hostView t)) (fun t => G (expView t))).holds σ :=
  ⟨fun h => ag_of_link_loose hA (h _ (ofPred_sat A hA)), fun hσ _ hη => link_sat hσ hη⟩

/-- **The protocol form**: `agP T (onExp G)` holds iff the link over `loose T` satisfies `G`. -/
theorem link_looseP_iff {S S' : Type} {T : Protocol S WEv} {G : Protocol S' WEv}
    {σ : Strategy (nsig I) (nsig X)} :
    (∀ p ∈ link (loose (Y := Y) T) σ, G.Accepts (xtrace p)) ↔ (agP T (onExp G)).holds σ := by
  rw [show (loose (Y := Y) (I := I) T) = ofPred T.Accepts (prefixClosed_accepts T) from rfl,
    link_loose_iff (prefixClosed_accepts T)]
  exact forall₂_congr fun t _ => imp_congr_right fun _ => (accepts_onExp G _).symm

end Silmaril.Wasi
