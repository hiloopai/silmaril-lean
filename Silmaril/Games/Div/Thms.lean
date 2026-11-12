module

public import Silmaril.Games.Div.Defs
import Silmaril.Proofs.Games.Div.Chain

/-!
# Chains and infinite plays: theorems

* Increasing chains: `Chain.Mono.le`, `Chain.Mono.unbounded_ge`; the limit of
  an increasing unbounded chain is an infinite play (`Chain.isInfPlay_lim`);
  a bounded increasing chain is eventually constant
  (`Chain.Mono.eventually_const`).
* Every infinite play is the limit of the canonical chain of its prefixes
  (`IsInfPlay.seq`, `IsInfPlay.lim_seq`).

Proofs are in `Silmaril.Proofs.Games.Div.Chain`.
-/

public section

namespace Silmaril.Games

universe v

variable {α : Type v}

namespace Chain

/-- An increasing chain is increasing between any two indices. -/
theorem Mono.le {c : Chain α} (hm : c.Mono) {n m : ℕ} (h : n ≤ m) : c n <+: c m :=
  Silmaril.Proofs.Games.Div.mono_le hm h

/-- An increasing unbounded chain gets long beyond any index. -/
theorem Mono.unbounded_ge {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (k n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ k ≤ (c n).length :=
  Silmaril.Proofs.Games.Div.unbounded_ge hm hu k n₀

/-- A bounded increasing chain is eventually constant. -/
theorem Mono.eventually_const {c : Chain α} (hm : c.Mono) (hb : ¬ c.Unbounded) :
    ∃ N, ∀ n, N ≤ n → c n = c N :=
  Silmaril.Proofs.Games.Div.eventually_const hm hb

/-- The limit of an increasing unbounded chain is an infinite play. -/
theorem isInfPlay_lim {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) : IsInfPlay c.lim :=
  Silmaril.Proofs.Games.Div.isInfPlay_lim hm hu

/-- Members of a chain belong to its limit. -/
theorem mem_lim_self (c : Chain α) (n : ℕ) : c n ∈ c.lim := ⟨n, List.prefix_refl _⟩

/-- Chains whose members are mutually bounded have the same limit. -/
theorem lim_eq_of {c d : Chain α} (h₁ : ∀ n, ∃ m, c n <+: d m) (h₂ : ∀ n, ∃ m, d n <+: c m) :
    c.lim = d.lim :=
  Silmaril.Proofs.Games.Div.lim_eq_of h₁ h₂

end Chain

namespace IsInfPlay

/-- In an infinite play, a shorter member is a prefix of a longer one. -/
theorem prefix_of_length_le {I : Set (List α)} (h : IsInfPlay I) {s t : List α} (hs : s ∈ I)
    (ht : t ∈ I) (hl : s.length ≤ t.length) : s <+: t :=
  Silmaril.Proofs.Games.Div.prefix_of_length_le h hs ht hl

/-- The canonical chain of an infinite play: its member of each length. -/
noncomputable def seq {I : Set (List α)} (h : IsInfPlay I) : Chain α :=
  Silmaril.Proofs.Games.Div.seq h

theorem seq_mem {I : Set (List α)} (h : IsInfPlay I) (n : ℕ) : h.seq n ∈ I :=
  Silmaril.Proofs.Games.Div.seq_mem h n

theorem seq_length {I : Set (List α)} (h : IsInfPlay I) (n : ℕ) : (h.seq n).length = n :=
  Silmaril.Proofs.Games.Div.seq_length h n

theorem seq_mono {I : Set (List α)} (h : IsInfPlay I) : h.seq.Mono :=
  Silmaril.Proofs.Games.Div.seq_mono h

theorem seq_unbounded {I : Set (List α)} (h : IsInfPlay I) : h.seq.Unbounded :=
  Silmaril.Proofs.Games.Div.seq_unbounded h

/-- An infinite play is the limit of its canonical chain. -/
theorem lim_seq {I : Set (List α)} (h : IsInfPlay I) : h.seq.lim = I :=
  Silmaril.Proofs.Games.Div.lim_seq h

end IsInfPlay

end Silmaril.Games
