module

public import Silmaril.Wasm.Spec.Live.Defs
public import Silmaril.Games.Div.Thms

@[expose] public section

/-!
# Liveness: infinite words from increasing chains of traces

An increasing, unbounded chain of finite traces (the presentation of infinite plays in
`Silmaril.Games.Div`) determines an infinite word, `chainWord`, whose prefixes are exactly the
members of the chain's limit (`prefixList_chainWord`, `exists_prefixList_chainWord`).
-/

namespace Silmaril.Wasm.Spec.Live

open Silmaril.Games

variable {α : Type}

/-- The infinite word of an increasing unbounded chain: its letter `k` is letter `k` of the
member of length `k + 1` of the limit. -/
noncomputable def chainWord {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) : ℕ → α :=
  fun k => ((Chain.isInfPlay_lim hm hu).seq (k + 1))[k]'(by
    rw [IsInfPlay.seq_length]
    exact Nat.lt_succ_self k)

/-- The prefixes of the word of a chain are the canonical members of its limit. -/
theorem prefixList_chainWord {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (n : ℕ) :
    prefixList (chainWord hm hu) n = (Chain.isInfPlay_lim hm hu).seq n := by
  have hI : IsInfPlay c.lim := Chain.isInfPlay_lim hm hu
  have hlen : (hI.seq n).length = n := IsInfPlay.seq_length hI n
  refine List.ext_getElem (by rw [length_prefixList, hlen]) fun i h₁ h₂ => ?_
  have hi : i < n := by simpa using h₁
  have hpre : hI.seq (i + 1) <+: hI.seq n := (IsInfPlay.seq_mono hI).le (Nat.succ_le_of_lt hi)
  have hi' : i < (hI.seq (i + 1)).length := by rw [IsInfPlay.seq_length]; exact Nat.lt_succ_self i
  have hl : (prefixList (chainWord hm hu) n)[i] = chainWord hm hu i := by
    simp only [prefixList, List.getElem_ofFn]
  rw [hl]
  exact hpre.getElem hi'

/-- Every prefix of the word of a chain is a prefix of a member of the chain. -/
theorem prefixList_chainWord_prefix {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (n : ℕ) :
    ∃ m, prefixList (chainWord hm hu) n <+: c m := by
  rw [prefixList_chainWord]
  exact IsInfPlay.seq_mem (Chain.isInfPlay_lim hm hu) n

/-- Every member of the chain is a prefix of the word. -/
theorem exists_prefixList_chainWord {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (m : ℕ) :
    prefixList (chainWord hm hu) (c m).length = c m := by
  have hI : IsInfPlay c.lim := Chain.isInfPlay_lim hm hu
  have hmem : c m ∈ c.lim := Chain.mem_lim_self c m
  have hseq : hI.seq (c m).length ∈ c.lim := IsInfPlay.seq_mem hI _
  have hpre : hI.seq (c m).length <+: c m :=
    IsInfPlay.prefix_of_length_le hI hseq hmem (by rw [IsInfPlay.seq_length])
  rw [prefixList_chainWord]
  exact hpre.eq_of_length (IsInfPlay.seq_length hI _)

/-- Every letter of the word of a chain occurs in some member of the chain. -/
theorem chainWord_mem {c : Chain α} (hm : c.Mono) (hu : c.Unbounded) (k : ℕ) :
    ∃ m, chainWord hm hu k ∈ c m := by
  obtain ⟨m, hm'⟩ := prefixList_chainWord_prefix hm hu (k + 1)
  refine ⟨m, hm'.subset ?_⟩
  rw [prefixList_succ]
  exact List.mem_append_right _ (List.mem_singleton_self _)

end Silmaril.Wasm.Spec.Live
