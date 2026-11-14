module

public import Silmaril.Servers.Hosts.Defs
public import Silmaril.Servers.Observe.Thms
import Silmaril.Proofs.Servers.Hosts.Basic

/-!
# Host interpretations: theorems

* **Universal and existential properties of the merged behaviour** are the per-host ones:
  `mustAll_iff_under`, `maySome_iff_under`.
* **Per-host refinement implies refinement of the merged behaviours** (`RefinesAt.under`), and
  transfers `MustAll` down and `MaySome` up (`mustAll_of_refinesAt`, `maySome_of_refinesAt`).
  **The converse fails** (`under_not_refinesAt`): merging hosts forgets which host produced
  which observation.
* **Changing the set of hosts**: a `MustAll` over more hosts gives one over fewer
  (`MustAll.anti`), a `MaySome` over fewer gives one over more (`MaySome.mono`).
* **A witness refutes**: one observation, under one host of `Hs`, that violates `φ` refutes
  `MustAll Hs C φ` (`not_mustAll_of_witness`). This is how a failing test under a host in `Hs`
  is a counterexample; a passing test is not a proof.
* **Replay**: the answers of pure hosts and oracles (`pure_answers`, `oracle_answers`), and of a
  stateful host to a concatenation of call sequences (`Stateful.answers_append`).
-/

@[expose] public section

namespace Silmaril.Servers.Hosts

open Silmaril.Servers Silmaril.Servers.Observe

variable {H : Type} {A : Sig}

theorem mem_under {Hs : Set H} {C : Open H A} {o : Obs A} :
    o ∈ under Hs C ↔ ∃ η ∈ Hs, o ∈ C η := by simp [under]

theorem mustAll_iff_under {Hs : Set H} {C : Open H A} {φ : Obs A → Prop} :
    MustAll Hs C φ ↔ (under Hs C).Must φ := by
  simp only [MustAll, Beh.Must, mem_under]; aesop

theorem maySome_iff_under {Hs : Set H} {C : Open H A} {φ : Obs A → Prop} :
    MaySome Hs C φ ↔ (under Hs C).May φ := by
  simp only [MaySome, Beh.May, mem_under]; aesop

theorem RefinesAt.under {Hs : Set H} {C D : Open H A} (h : RefinesAt Hs C D) :
    (Hosts.under Hs C).Refines (Hosts.under Hs D) := fun _ ho =>
  let ⟨η, hη, ho⟩ := mem_under.1 ho; mem_under.2 ⟨η, hη, h η hη ho⟩

theorem mustAll_of_refinesAt {Hs : Set H} {C D : Open H A} (h : RefinesAt Hs C D)
    {φ : Obs A → Prop} (hD : MustAll Hs D φ) : MustAll Hs C φ := fun η hη =>
  Beh.must_of_refines (h η hη) (hD η hη)

theorem maySome_of_refinesAt {Hs : Set H} {C D : Open H A} (h : RefinesAt Hs C D)
    {φ : Obs A → Prop} (hC : MaySome Hs C φ) : MaySome Hs D φ :=
  let ⟨η, hη, hm⟩ := hC; ⟨η, hη, Beh.may_of_refines (h η hη) hm⟩

theorem MustAll.anti {Hs Hs' : Set H} (hs : Hs ⊆ Hs') {C : Open H A} {φ : Obs A → Prop}
    (h : MustAll Hs' C φ) : MustAll Hs C φ := fun η hη => h η (hs hη)

theorem MaySome.mono {Hs Hs' : Set H} (hs : Hs ⊆ Hs') {C : Open H A} {φ : Obs A → Prop}
    (h : MaySome Hs C φ) : MaySome Hs' C φ := let ⟨η, hη, hm⟩ := h; ⟨η, hs hη, hm⟩

theorem not_mustAll_of_witness {Hs : Set H} {C : Open H A} {φ : Obs A → Prop} {η : H}
    (hη : η ∈ Hs) {o : Obs A} (ho : o ∈ C η) (hφ : ¬ φ o) : ¬ MustAll Hs C φ :=
  fun h => hφ (h η hη o ho)

/-- **Merging hosts loses refinement**: two open servers with the same merged behaviour where
neither refines the other host by host. -/
theorem under_not_refinesAt (A : Sig) :
    ∃ C D : Open Bool A, under Set.univ C = under Set.univ D ∧ ¬ RefinesAt Set.univ C D :=
  Proofs.Servers.Hosts.under_not_refinesAt A

theorem pure_answers {Q R : Type} (f : Pure Q R) (qs : List Q) :
    (Pure.toStateful f).answers () qs = qs.map f :=
  Proofs.Servers.Hosts.pure_answers f qs

theorem oracle_answers {Q R : Type} (o : Oracle R) (qs : List Q) (k : Nat) :
    (Oracle.toStateful (Q := Q) o).answers k qs = (List.range' k qs.length).map o :=
  Proofs.Servers.Hosts.oracle_answers o qs k

theorem Stateful.answers_append {σ Q R : Type} (h : Stateful σ Q R) (s : σ) (qs qs' : List Q) :
    h.answers s (qs ++ qs') =
      h.answers s qs ++ h.answers ((qs.foldl (fun s q => (h.step s q).2) s)) qs' :=
  Proofs.Servers.Hosts.answers_append h s qs qs'

end Silmaril.Servers.Hosts
