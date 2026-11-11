module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.Composition.Thms
import Silmaril.Proofs.Games.DivComp.Pos
import Silmaril.Proofs.Games.DivComp.ZipChain

/-!
# Associativity of divergence-observing composition: proofs

The finite plays are `Strategy.comp_assoc`. For divergence and infinite
plays, every observation of `(σ ; τ) ; ρ` comes from an outer interaction
whose `σ ; τ` side is covered by *source* interactions of `σ` and `τ` (a
single finite one, or an infinite one witnessing an infinite play of
`σ ; τ`). `mergeA` (`Silmaril.Proofs.Games.DivComp.ZipChain`) re-associates
them into increasing chains `s'`, `t'`, `v'` with
`Zip (t' n) (r n) (v' n)` and `Zip (s' n) (v' n) (p n)`. `assembleA` then
reads off the observation of `σ ; (τ ; ρ)`: an infinite interaction of `σ`
with `τ ; ρ` if those sides keep moving, and otherwise a divergence of
`τ ; ρ` after a finite play (hidden chatter between `τ` and `ρ`). The other
inclusion is symmetric (`mergeB`, `assembleB`).
-/

public section

namespace Silmaril.Proofs.Games.DivComp

open Silmaril.Games Silmaril.Games.DStrategy

universe u v

/-! ## Chains -/

section Chains

variable {α : Type v}

theorem not_unbounded_of_le {c : Chain α} {B : ℕ} (h : ∀ n, (c n).length ≤ B) :
    ¬ c.Unbounded := fun hu => by
  obtain ⟨n, hn⟩ := hu (B + 1)
  have := h n
  omega

theorem lim_eq_of_sub {c d : Chain α} (_hc : c.Mono) (hcu : c.Unbounded) (hd : d.Mono)
    (hsub : ∀ n, ∃ m, c n <+: d m) : c.lim = d.lim ∧ d.Unbounded := by
  have hdu : d.Unbounded := fun k => by
    obtain ⟨n, hn⟩ := hcu k
    obtain ⟨m, hm⟩ := hsub n
    exact ⟨m, hn.trans hm.length_le⟩
  refine ⟨Chain.lim_eq_of hsub (fun m => ?_), hdu⟩
  obtain ⟨n, hn⟩ := hcu (d m).length
  obtain ⟨m', hm'⟩ := hsub n
  exact ⟨n, List.prefix_of_prefix_length_le (hd.le (le_max_left m m'))
    (hm'.trans (hd.le (le_max_right m m'))) hn⟩

theorem lim_index {d : Chain α} (hd : d.Mono) {M : ℕ → ℕ} (hM : ∀ n, n ≤ M n) :
    Chain.lim (fun n => d (M n)) = d.lim :=
  Chain.lim_eq_of (fun n => ⟨M n, List.prefix_refl _⟩) (fun n => ⟨n, hd.le (hM n)⟩)

theorem lim_tail {d : Chain α} (hd : d.Mono) (N : ℕ) :
    Chain.lim (fun n => d (n + N)) = d.lim :=
  lim_index hd (M := fun n => n + N) (fun n => Nat.le_add_right n N)

theorem tail_mono {d : Chain α} (hd : d.Mono) (N : ℕ) : Chain.Mono (fun n => d (n + N)) :=
  fun n => hd.le (by omega)

theorem prefix_eventually {c : Chain α} (hm : c.Mono) (hb : ¬ c.Unbounded) :
    ∃ N, ∀ n, c n <+: c N ∧ (N ≤ n → c n = c N) := by
  obtain ⟨N, hN⟩ := hm.eventually_const hb
  refine ⟨N, fun n => ⟨?_, hN n⟩⟩
  rcases le_total n N with h | h
  · exact hm.le h
  · rw [hN n h]; exact List.prefix_refl _

end Chains

theorem zip_length_le {α : Type u} {β : Type u} {γ : Type u} {s : List (α ⊕ β)}
    {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.length ≤ s.length + t.length := by
  rw [zip_length h]
  exact Nat.add_le_add (List.length_filterMap_le _ _) (List.length_filterMap_le _ _)

variable {E F G H : Sig.{u}}

/-- An infinite interaction from stage `N` on. -/
def InfInteraction.shift {σ : DStrategy E F} {τ : DStrategy F G} (i : InfInteraction σ τ)
    (N : ℕ) : InfInteraction σ τ where
  s n := i.s (n + N)
  t n := i.t (n + N)
  p n := i.p (n + N)
  zip n := i.zip _
  mem_s n := i.mem_s _
  mem_t n := i.mem_t _
  mono_s := tail_mono i.mono_s N
  mono_t := tail_mono i.mono_t N
  mono_p := tail_mono i.mono_p N
  unbounded k := by
    obtain ⟨n, hn⟩ := i.unbounded k
    exact ⟨n, hn.trans (Nat.add_le_add (i.mono_s.le (Nat.le_add_right n N)).length_le
      (i.mono_t.le (Nat.le_add_right n N)).length_le)⟩
  lim_s h := by
    have : i.s.Unbounded := fun k => let ⟨n, hn⟩ := h k; ⟨n + N, hn⟩
    show Chain.lim (fun n => i.s (n + N)) ∈ σ.inf
    rw [lim_tail i.mono_s]; exact i.lim_s this
  lim_t h := by
    have : i.t.Unbounded := fun k => let ⟨n, hn⟩ := h k; ⟨n + N, hn⟩
    show Chain.lim (fun n => i.t (n + N)) ∈ τ.inf
    rw [lim_tail i.mono_t]; exact i.lim_t this

/-- Infinite hidden chatter moves forever on both sides. -/
theorem chatter_unbounded {σ : DStrategy E F} {τ : DStrategy F G} (i : InfInteraction σ τ)
    {p : List (Move E G)} (hp : ∀ n, i.p n = p) : i.s.Unbounded ∧ i.t.Unbounded := by
  have key : ∀ n, (i.s n).length + (i.t n).length ≤ p.length +
      2 * ((i.s n).filterMap Sum.getRight?).length ∧
      ((i.s n).filterMap Sum.getRight?).length ≤ (i.s n).length ∧
      ((i.s n).filterMap Sum.getRight?).length ≤ (i.t n).length := by
    intro n
    have hz := hp n ▸ i.zip n
    have hl := congrArg List.length (zip_lefts hz)
    have hr := congrArg List.length (zip_rights hz)
    have hy := congrArg List.length (zip_sync hz)
    have e₁ := length_split (i.s n)
    have e₂ := length_split (i.t n)
    have e₃ := length_split p
    omega
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨n, hn⟩ := i.unbounded (2 * k + p.length)
    exact ⟨n, by have := key n; omega⟩
  · obtain ⟨n, hn⟩ := i.unbounded (2 * k + p.length)
    exact ⟨n, by have := key n; omega⟩

/-! ## Assembling re-associated chains -/

section A

variable {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}

theorem assembleA {s' : Chain (Move E F)} {t' : Chain (Move F G)} {r : Chain (Move G H)}
    {v' : Chain (Move F H)} {p : Chain (Move E H)}
    (htr : ∀ n, Zip (t' n) (r n) (v' n)) (hsv : ∀ n, Zip (s' n) (v' n) (p n))
    (hs : ∀ n, s' n ∈ σ.toStrategy) (ht : ∀ n, t' n ∈ τ.toStrategy) (hr : ∀ n, r n ∈ ρ.toStrategy)
    (hms : s'.Mono) (hmt : t'.Mono) (hmr : r.Mono) (hmv : v'.Mono) (hmp : p.Mono)
    (hls : s'.Unbounded → s'.lim ∈ σ.inf) (hlt : t'.Unbounded → t'.lim ∈ τ.inf)
    (hlr : r.Unbounded → r.lim ∈ ρ.inf)
    (htot : ∀ k, ∃ n, k ≤ (s' n).length + (t' n).length + (r n).length) :
    (p.Unbounded → p.lim ∈ (σ.comp (τ.comp ρ)).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ (σ.comp (τ.comp ρ)).div := by
  have hv : ∀ n, v' n ∈ (τ.comp ρ).toStrategy := fun n => ⟨_, ht n, _, hr n, htr n⟩
  let iI : (∀ k, ∃ n, k ≤ (t' n).length + (r n).length) → InfInteraction τ ρ := fun h =>
    ⟨t', r, v', htr, ht, hr, hmt, hmr, hmv, h, hlt, hlr⟩
  have hvl : v'.Unbounded → v'.lim ∈ (τ.comp ρ).inf := fun hu => by
    have h : ∀ k, ∃ n, k ≤ (t' n).length + (r n).length := fun k => by
      obtain ⟨n, hn⟩ := hu k
      exact ⟨n, hn.trans (zip_length_le (htr n))⟩
    exact ⟨iI h, hu, rfl⟩
  by_cases hout : ∀ k, ∃ n, k ≤ (s' n).length + (v' n).length
  · let oI : InfInteraction σ (τ.comp ρ) := ⟨s', v', p, hsv, hs, hv, hms, hmv, hmp, hout, hls, hvl⟩
    exact ⟨fun hp => ⟨oI, hp, rfl⟩, fun q hq => .inr ⟨oI, hq⟩⟩
  · show (p.Unbounded → p.lim ∈ (σ.comp (τ.comp ρ)).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ (σ.comp (τ.comp ρ)).div
    obtain ⟨k, hk⟩ : ∃ k, ∀ n, (s' n).length + (v' n).length < k := by
      push Not at hout; exact hout
    have hsb : ¬ s'.Unbounded := not_unbounded_of_le (B := k) fun n => by have := hk n; omega
    have hvb : ¬ v'.Unbounded := not_unbounded_of_le (B := k) fun n => by have := hk n; omega
    refine ⟨fun hp => ?_, fun q hq => ?_⟩
    · obtain ⟨n, hn⟩ := hp k
      have := zip_length_le (hsv n)
      have := hk n
      omega
    · show q ∈ (σ.comp (τ.comp ρ)).div
      obtain ⟨N₁, hN₁⟩ := prefix_eventually hms hsb
      obtain ⟨N₂, hN₂⟩ := prefix_eventually hmv hvb
      have hinner : ∀ k, ∃ n, k ≤ (t' n).length + (r n).length := fun j => by
        obtain ⟨n, hn⟩ := htot (j + k)
        exact ⟨n, by have := hk n; omega⟩
      let N := max N₁ N₂
      have hvN : ∀ n, (InfInteraction.shift (iI hinner) N).p n = v' N := fun n =>
        ((hN₂ (n + N)).2 (by omega)).trans ((hN₂ N).2 (le_max_right _ _)).symm
      have hdiv : v' N ∈ (τ.comp ρ).div := .inr ⟨InfInteraction.shift (iI hinner) N, hvN⟩
      exact .inl ⟨s' N, v' N, hq N ▸ hsv N, .inr ⟨hs N, hdiv⟩⟩

/-- Assembly from a source covering the `σ ; τ` side of the outer interaction. -/
theorem fromSourceA {u : Chain (Move E G)} {r : Chain (Move G H)} {p : Chain (Move E H)}
    (hz : ∀ n, Zip (u n) (r n) (p n)) (hmu : u.Mono) (hmr : r.Mono) (hmp : p.Mono)
    (hr : ∀ n, r n ∈ ρ.toStrategy) (hlr : r.Unbounded → r.lim ∈ ρ.inf)
    {S : Chain (Move E F)} {T : Chain (Move F G)} {W : Chain (Move E G)}
    (hZ : ∀ m, Zip (S m) (T m) (W m)) (hmS : S.Mono) (hmT : T.Mono) (hmW : W.Mono)
    (hS : ∀ m, S m ∈ σ.toStrategy) (hT : ∀ m, T m ∈ τ.toStrategy)
    (hlS : S.Unbounded → S.lim ∈ σ.inf) (hlT : T.Unbounded → T.lim ∈ τ.inf)
    (hcov : ∀ n, ∃ m, u n <+: W m)
    (hgrow : (∀ k, ∃ n, k ≤ (u n).length + (r n).length) ∨ (S.Unbounded ∧ ∀ n m, u n = W m)) :
    (p.Unbounded → p.lim ∈ (σ.comp (τ.comp ρ)).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ (σ.comp (τ.comp ρ)).div := by
  obtain ⟨s', t', v', M, hms, hmt, hmv, h⟩ := mergeA hz hmu hmr hmp hZ hmS hmT hmW hcov
  have hls : s'.Unbounded → s'.lim ∈ σ.inf := fun hu => by
    obtain ⟨he, hSu⟩ := lim_eq_of_sub hms hu hmS fun n => ⟨M n, (h n).2.2.2.1⟩
    rw [he]; exact hlS hSu
  have hlt : t'.Unbounded → t'.lim ∈ τ.inf := fun hu => by
    obtain ⟨he, hTu⟩ := lim_eq_of_sub hmt hu hmT fun n => ⟨M n, (h n).2.2.2.2.1⟩
    rw [he]; exact hlT hTu
  refine assembleA (fun n => (h n).2.1) (fun n => (h n).2.2.1)
    (fun n => σ.toStrategy.of_prefix (hS _) (h n).2.2.2.1)
    (fun n => τ.toStrategy.of_prefix (hT _) (h n).2.2.2.2.1) hr hms hmt hmr hmv hmp hls hlt hlr ?_
  rcases hgrow with hg | ⟨hSu, hW⟩
  · intro k
    obtain ⟨n, hn⟩ := hg k
    exact ⟨n, by have := zip_length_le (h n).1; omega⟩
  · intro k
    obtain ⟨n, hn⟩ := hSu k
    refine ⟨n, ?_⟩
    obtain ⟨-, -, -, -, -, hMn, hmax⟩ := h n
    rw [(hmax (hW n (M n))).1]
    have := (hmS.le hMn).length_le
    omega

end A

section B

variable {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}

theorem assembleB {s : Chain (Move E F)} {t' : Chain (Move F G)} {r' : Chain (Move G H)}
    {u' : Chain (Move E G)} {p : Chain (Move E H)}
    (hst : ∀ n, Zip (s n) (t' n) (u' n)) (hur : ∀ n, Zip (u' n) (r' n) (p n))
    (hs : ∀ n, s n ∈ σ.toStrategy) (ht : ∀ n, t' n ∈ τ.toStrategy) (hr : ∀ n, r' n ∈ ρ.toStrategy)
    (hms : s.Mono) (hmt : t'.Mono) (hmr : r'.Mono) (hmu : u'.Mono) (hmp : p.Mono)
    (hls : s.Unbounded → s.lim ∈ σ.inf) (hlt : t'.Unbounded → t'.lim ∈ τ.inf)
    (hlr : r'.Unbounded → r'.lim ∈ ρ.inf)
    (htot : ∀ k, ∃ n, k ≤ (s n).length + (t' n).length + (r' n).length) :
    (p.Unbounded → p.lim ∈ ((σ.comp τ).comp ρ).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ ((σ.comp τ).comp ρ).div := by
  have hu : ∀ n, u' n ∈ (σ.comp τ).toStrategy := fun n => ⟨_, hs n, _, ht n, hst n⟩
  let iI : (∀ k, ∃ n, k ≤ (s n).length + (t' n).length) → InfInteraction σ τ := fun h =>
    ⟨s, t', u', hst, hs, ht, hms, hmt, hmu, h, hls, hlt⟩
  have hul : u'.Unbounded → u'.lim ∈ (σ.comp τ).inf := fun huu => by
    have h : ∀ k, ∃ n, k ≤ (s n).length + (t' n).length := fun k => by
      obtain ⟨n, hn⟩ := huu k
      exact ⟨n, hn.trans (zip_length_le (hst n))⟩
    exact ⟨iI h, huu, rfl⟩
  by_cases hout : ∀ k, ∃ n, k ≤ (u' n).length + (r' n).length
  · let oI : InfInteraction (σ.comp τ) ρ := ⟨u', r', p, hur, hu, hr, hmu, hmr, hmp, hout, hul, hlr⟩
    exact ⟨fun hp => ⟨oI, hp, rfl⟩, fun q hq => .inr ⟨oI, hq⟩⟩
  · show (p.Unbounded → p.lim ∈ ((σ.comp τ).comp ρ).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ ((σ.comp τ).comp ρ).div
    obtain ⟨k, hk⟩ : ∃ k, ∀ n, (u' n).length + (r' n).length < k := by
      push Not at hout; exact hout
    have hub : ¬ u'.Unbounded := not_unbounded_of_le (B := k) fun n => by have := hk n; omega
    have hrb : ¬ r'.Unbounded := not_unbounded_of_le (B := k) fun n => by have := hk n; omega
    refine ⟨fun hp => ?_, fun q hq => ?_⟩
    · obtain ⟨n, hn⟩ := hp k
      have := zip_length_le (hur n)
      have := hk n
      omega
    · show q ∈ ((σ.comp τ).comp ρ).div
      obtain ⟨N₁, hN₁⟩ := prefix_eventually hmu hub
      obtain ⟨N₂, hN₂⟩ := prefix_eventually hmr hrb
      have hinner : ∀ k, ∃ n, k ≤ (s n).length + (t' n).length := fun j => by
        obtain ⟨n, hn⟩ := htot (j + k)
        exact ⟨n, by have := hk n; omega⟩
      let N := max N₁ N₂
      have huN : ∀ n, (InfInteraction.shift (iI hinner) N).p n = u' N := fun n =>
        ((hN₁ (n + N)).2 (by omega)).trans ((hN₁ N).2 (le_max_left _ _)).symm
      have hdiv : u' N ∈ (σ.comp τ).div := .inr ⟨InfInteraction.shift (iI hinner) N, huN⟩
      exact .inl ⟨u' N, r' N, hq N ▸ hur N, .inl ⟨hdiv, hr N⟩⟩

/-- Assembly from a source covering the `τ ; ρ` side of the outer interaction. -/
theorem fromSourceB {s : Chain (Move E F)} {v : Chain (Move F H)} {p : Chain (Move E H)}
    (hz : ∀ n, Zip (s n) (v n) (p n)) (hms : s.Mono) (hmv : v.Mono) (hmp : p.Mono)
    (hs : ∀ n, s n ∈ σ.toStrategy) (hls : s.Unbounded → s.lim ∈ σ.inf)
    {T : Chain (Move F G)} {R : Chain (Move G H)} {Y : Chain (Move F H)}
    (hZ : ∀ m, Zip (T m) (R m) (Y m)) (hmT : T.Mono) (hmR : R.Mono) (hmY : Y.Mono)
    (hT : ∀ m, T m ∈ τ.toStrategy) (hR : ∀ m, R m ∈ ρ.toStrategy)
    (hlT : T.Unbounded → T.lim ∈ τ.inf) (hlR : R.Unbounded → R.lim ∈ ρ.inf)
    (hcov : ∀ n, ∃ m, v n <+: Y m)
    (hgrow : (∀ k, ∃ n, k ≤ (s n).length + (v n).length) ∨ (T.Unbounded ∧ ∀ n m, v n = Y m)) :
    (p.Unbounded → p.lim ∈ ((σ.comp τ).comp ρ).inf) ∧
      ∀ q, (∀ n, p n = q) → q ∈ ((σ.comp τ).comp ρ).div := by
  obtain ⟨t', r', u', M, hmt, hmr, hmu, h⟩ := mergeB hz hms hmv hmp hZ hmT hmR hmY hcov
  have hlt : t'.Unbounded → t'.lim ∈ τ.inf := fun hu => by
    obtain ⟨he, hTu⟩ := lim_eq_of_sub hmt hu hmT fun n => ⟨M n, (h n).2.2.2.1⟩
    rw [he]; exact hlT hTu
  have hlr : r'.Unbounded → r'.lim ∈ ρ.inf := fun hu => by
    obtain ⟨he, hRu⟩ := lim_eq_of_sub hmr hu hmR fun n => ⟨M n, (h n).2.2.2.2.1⟩
    rw [he]; exact hlR hRu
  refine assembleB (fun n => (h n).2.1) (fun n => (h n).2.2.1) hs
    (fun n => τ.toStrategy.of_prefix (hT _) (h n).2.2.2.1)
    (fun n => ρ.toStrategy.of_prefix (hR _) (h n).2.2.2.2.1) hms hmt hmr hmu hmp hls hlt hlr ?_
  rcases hgrow with hg | ⟨hTu, hY⟩
  · intro k
    obtain ⟨n, hn⟩ := hg k
    exact ⟨n, by have := zip_length_le (h n).1; omega⟩
  · intro k
    obtain ⟨n, hn⟩ := hTu k
    refine ⟨n, ?_⟩
    obtain ⟨-, -, -, -, -, hMn, hmax⟩ := h n
    rw [(hmax (hY n (M n))).1]
    have := (hmT.le hMn).length_le
    omega

end B

/-! ## The four inclusions -/

variable {σ : DStrategy E F} {τ : DStrategy F G} {ρ : DStrategy G H}

private theorem const_mono {α : Type u} (x : List α) : Chain.Mono (fun _ => x) :=
  fun _ => List.prefix_refl _

private theorem const_not_unbounded {α : Type u} (x : List α) :
    ¬ Chain.Unbounded (fun _ => x) :=
  not_unbounded_of_le (B := x.length) fun _ => le_rfl

private theorem divA_inner {u : List (Move E G)} {r : List (Move G H)} {q : List (Move E H)}
    (hz : Zip u r q) (hr : r ∈ ρ.toStrategy) (j : InfInteraction σ τ) (hj : ∀ n, j.p n = u) :
    q ∈ (σ.comp (τ.comp ρ)).div := by
  have hsu : j.s.Unbounded := (chatter_unbounded j hj).1
  exact (fromSourceA (u := fun _ => u) (r := fun _ => r) (p := fun _ => q) (fun _ => hz)
    (const_mono _) (const_mono _) (const_mono _) (fun _ => hr)
    (fun h => (const_not_unbounded _ h).elim) j.zip j.mono_s j.mono_t j.mono_p j.mem_s j.mem_t
    j.lim_s j.lim_t (fun _ => ⟨0, (hj 0).symm ▸ List.prefix_refl _⟩)
    (.inr ⟨hsu, fun _ m => (hj m).symm⟩)).2 q fun _ => rfl

private theorem divA_left {u : List (Move E G)} {r : List (Move G H)} {q : List (Move E H)}
    (hz : Zip u r q) (hu : u ∈ (σ.comp τ).div) (hr : r ∈ ρ.toStrategy) :
    q ∈ (σ.comp (τ.comp ρ)).div := by
  rcases hu with ⟨s, t, hz', ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ | ⟨j, hj⟩
  · obtain ⟨v, h₁, h₂⟩ : ∃ v, Zip t r v ∧ Zip s v q := Zip.assoc.1 ⟨u, hz', hz⟩
    exact .inl ⟨s, v, h₂, .inl ⟨hs, ⟨t, ht, r, hr, h₁⟩⟩⟩
  · obtain ⟨v, h₁, h₂⟩ : ∃ v, Zip t r v ∧ Zip s v q := Zip.assoc.1 ⟨u, hz', hz⟩
    exact .inl ⟨s, v, h₂, .inr ⟨hs, .inl ⟨t, r, h₁, .inl ⟨ht, hr⟩⟩⟩⟩
  · exact divA_inner hz hr j hj

private theorem divA_right {u : List (Move E G)} {r : List (Move G H)} {q : List (Move E H)}
    (hz : Zip u r q) (hu : u ∈ (σ.comp τ).toStrategy) (hr : r ∈ ρ.div) :
    q ∈ (σ.comp (τ.comp ρ)).div := by
  obtain ⟨s, hs, t, ht, hz'⟩ := hu
  obtain ⟨v, h₁, h₂⟩ : ∃ v, Zip t r v ∧ Zip s v q := Zip.assoc.1 ⟨u, hz', hz⟩
  exact .inl ⟨s, v, h₂, .inr ⟨hs, .inl ⟨t, r, h₁, .inr ⟨ht, hr⟩⟩⟩⟩

private theorem divA_chatter (i : InfInteraction (σ.comp τ) ρ) {q : List (Move E H)}
    (hi : ∀ n, i.p n = q) : q ∈ (σ.comp (τ.comp ρ)).div := by
  have hsu : i.s.Unbounded := (chatter_unbounded i hi).1
  obtain ⟨j, -, hj⟩ : ∃ j : InfInteraction σ τ, j.p.Unbounded ∧ i.s.lim = j.p.lim := i.lim_s hsu
  have hcov : ∀ n, ∃ m, i.s n <+: j.p m := fun n => by
    have h : i.s n ∈ i.s.lim := ⟨n, List.prefix_refl _⟩
    rw [hj] at h
    exact h
  exact (fromSourceA i.zip i.mono_s i.mono_t i.mono_p i.mem_t i.lim_t j.zip j.mono_s j.mono_t
    j.mono_p j.mem_s j.mem_t j.lim_s j.lim_t hcov (.inl i.unbounded)).2 q hi

theorem div_assoc_le : ((σ.comp τ).comp ρ).div ⊆ (σ.comp (τ.comp ρ)).div := by
  rintro q (⟨u, r, hz, ⟨hu, hr⟩ | ⟨hu, hr⟩⟩ | ⟨i, hi⟩)
  · exact divA_left hz hu hr
  · exact divA_right hz hu hr
  · exact divA_chatter i hi

theorem inf_assoc_le : ((σ.comp τ).comp ρ).inf ⊆ (σ.comp (τ.comp ρ)).inf := by
  rintro _ ⟨i, hpu, rfl⟩
  by_cases hsu : i.s.Unbounded
  · obtain ⟨j, -, hj⟩ := i.lim_s hsu
    exact (fromSourceA i.zip i.mono_s i.mono_t i.mono_p i.mem_t i.lim_t j.zip j.mono_s j.mono_t
      j.mono_p j.mem_s j.mem_t j.lim_s j.lim_t
      (fun n => by have : i.s n ∈ i.s.lim := ⟨n, List.prefix_refl _⟩; rw [hj] at this; exact this)
      (.inl i.unbounded)).1 hpu
  · obtain ⟨N, hN⟩ := prefix_eventually i.mono_s hsu
    obtain ⟨s₀, hs₀, t₀, ht₀, hz₀⟩ := i.mem_s N
    exact (fromSourceA (S := fun _ => s₀) (T := fun _ => t₀) (W := fun _ => i.s N) i.zip i.mono_s
      i.mono_t i.mono_p i.mem_t i.lim_t (fun _ => hz₀) (const_mono _) (const_mono _)
      (const_mono _) (fun _ => hs₀) (fun _ => ht₀) (fun h => (const_not_unbounded _ h).elim)
      (fun h => (const_not_unbounded _ h).elim) (fun n => ⟨0, (hN n).1⟩) (.inl i.unbounded)).1 hpu

private theorem divB_inner {s : List (Move E F)} {v : List (Move F H)} {q : List (Move E H)}
    (hz : Zip s v q) (hs : s ∈ σ.toStrategy) (j : InfInteraction τ ρ) (hj : ∀ n, j.p n = v) :
    q ∈ ((σ.comp τ).comp ρ).div := by
  have htu : j.s.Unbounded := (chatter_unbounded j hj).1
  exact (fromSourceB (s := fun _ => s) (v := fun _ => v) (p := fun _ => q) (fun _ => hz)
    (const_mono _) (const_mono _) (const_mono _) (fun _ => hs)
    (fun h => (const_not_unbounded _ h).elim) j.zip j.mono_s j.mono_t j.mono_p j.mem_s j.mem_t
    j.lim_s j.lim_t (fun _ => ⟨0, (hj 0).symm ▸ List.prefix_refl _⟩)
    (.inr ⟨htu, fun _ m => (hj m).symm⟩)).2 q fun _ => rfl

private theorem divB_right {s : List (Move E F)} {v : List (Move F H)} {q : List (Move E H)}
    (hz : Zip s v q) (hs : s ∈ σ.toStrategy) (hv : v ∈ (τ.comp ρ).div) :
    q ∈ ((σ.comp τ).comp ρ).div := by
  rcases hv with ⟨t, r, hz', ⟨ht, hr⟩ | ⟨ht, hr⟩⟩ | ⟨j, hj⟩
  · obtain ⟨u, h₁, h₂⟩ : ∃ u, Zip s t u ∧ Zip u r q := Zip.assoc.2 ⟨v, hz', hz⟩
    exact .inl ⟨u, r, h₂, .inl ⟨.inl ⟨s, t, h₁, .inr ⟨hs, ht⟩⟩, hr⟩⟩
  · obtain ⟨u, h₁, h₂⟩ : ∃ u, Zip s t u ∧ Zip u r q := Zip.assoc.2 ⟨v, hz', hz⟩
    exact .inl ⟨u, r, h₂, .inr ⟨⟨s, hs, t, ht, h₁⟩, hr⟩⟩
  · exact divB_inner hz hs j hj

private theorem divB_left {s : List (Move E F)} {v : List (Move F H)} {q : List (Move E H)}
    (hz : Zip s v q) (hs : s ∈ σ.div) (hv : v ∈ (τ.comp ρ).toStrategy) :
    q ∈ ((σ.comp τ).comp ρ).div := by
  obtain ⟨t, ht, r, hr, hz'⟩ := hv
  obtain ⟨u, h₁, h₂⟩ : ∃ u, Zip s t u ∧ Zip u r q := Zip.assoc.2 ⟨v, hz', hz⟩
  exact .inl ⟨u, r, h₂, .inl ⟨.inl ⟨s, t, h₁, .inl ⟨hs, ht⟩⟩, hr⟩⟩

private theorem divB_chatter (i : InfInteraction σ (τ.comp ρ)) {q : List (Move E H)}
    (hi : ∀ n, i.p n = q) : q ∈ ((σ.comp τ).comp ρ).div := by
  have htu : i.t.Unbounded := (chatter_unbounded i hi).2
  obtain ⟨j, -, hj⟩ : ∃ j : InfInteraction τ ρ, j.p.Unbounded ∧ i.t.lim = j.p.lim := i.lim_t htu
  have hcov : ∀ n, ∃ m, i.t n <+: j.p m := fun n => by
    have h : i.t n ∈ i.t.lim := ⟨n, List.prefix_refl _⟩
    rw [hj] at h
    exact h
  exact (fromSourceB i.zip i.mono_s i.mono_t i.mono_p i.mem_s i.lim_s j.zip j.mono_s j.mono_t
    j.mono_p j.mem_s j.mem_t j.lim_s j.lim_t hcov (.inl i.unbounded)).2 q hi

theorem div_le_assoc : (σ.comp (τ.comp ρ)).div ⊆ ((σ.comp τ).comp ρ).div := by
  rintro q (⟨s, v, hz, ⟨hs, hv⟩ | ⟨hs, hv⟩⟩ | ⟨i, hi⟩)
  · exact divB_left hz hs hv
  · exact divB_right hz hs hv
  · exact divB_chatter i hi

theorem inf_le_assoc : (σ.comp (τ.comp ρ)).inf ⊆ ((σ.comp τ).comp ρ).inf := by
  rintro _ ⟨i, hpu, rfl⟩
  by_cases htu : i.t.Unbounded
  · obtain ⟨j, -, hj⟩ := i.lim_t htu
    exact (fromSourceB i.zip i.mono_s i.mono_t i.mono_p i.mem_s i.lim_s j.zip j.mono_s j.mono_t
      j.mono_p j.mem_s j.mem_t j.lim_s j.lim_t
      (fun n => by have : i.t n ∈ i.t.lim := ⟨n, List.prefix_refl _⟩; rw [hj] at this; exact this)
      (.inl i.unbounded)).1 hpu
  · obtain ⟨N, hN⟩ := prefix_eventually i.mono_t htu
    obtain ⟨t₀, ht₀, r₀, hr₀, hz₀⟩ := i.mem_t N
    exact (fromSourceB (T := fun _ => t₀) (R := fun _ => r₀) (Y := fun _ => i.t N) i.zip i.mono_s
      i.mono_t i.mono_p i.mem_s i.lim_s (fun _ => hz₀) (const_mono _) (const_mono _)
      (const_mono _) (fun _ => ht₀) (fun _ => hr₀) (fun h => (const_not_unbounded _ h).elim)
      (fun h => (const_not_unbounded _ h).elim) (fun n => ⟨0, (hN n).1⟩) (.inl i.unbounded)).1 hpu

end Silmaril.Proofs.Games.DivComp
