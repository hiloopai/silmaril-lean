module

public import Silmaril.Proofs.Wasm.Game.ULink.Backward
public import Silmaril.Games.Div.Thms
public import Silmaril.Games.DivLTS.Thms

/-!
# Infinite plays of the linked module and of the composite

* `infRun_of_chain`: an infinite run whose stages can each be matched, from any related state,
  by a run along the next segment of a chain `c` is matched by an infinite run with traces `c`
  (dependent choice through `choose!`, as `Silmaril.Proofs.Games.DivLTS.infRun_of_simulation`).
* `map_stubUp_inj`: `stubUp` is injective on plays with the layout.
* `link_inf_le_comp`: an infinite play of the linked module is, read through `stubUp`, one of the
  composite (the backward simulation `BRel` of `Silmaril.Proofs.Wasm.Game.ULink.Backward`, stage by
  stage); `comp_inf_le_link`: conversely (the forward simulation `FRel`, stage by stage, the
  stages of the linked play read back through the injectivity of `stubUp`).

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril

universe u

/-! ### Infinite runs along a chain -/

/-- **Infinite runs along a chain.** If every stage of the infinite run `r` of `L₁` can be
matched, from every state related to its start, by a run of `L₂` along the next segment of the
chain `c`, then `L₂` has an infinite run with traces `c`. -/
theorem infRun_of_chain {E F E' F' : Sig.{u}} {L₁ : LTS E F} {L₂ : LTS E' F'} (r : L₁.InfRun)
    (c : Chain (Move E' F')) (hc : c 0 = []) (R : L₁.State → L₂.State → Prop)
    (h0 : R L₁.init L₂.init)
    (hstep : ∀ n y, R (r.st n) y → ∃ y', R (r.st (n + 1)) y' ∧
      ∃ w, c (n + 1) = c n ++ w ∧ L₂.Run y w y') :
    ∃ r' : L₂.InfRun, r'.tr = c := by
  choose! nxt hnxt using hstep
  let g : ℕ → L₂.State := fun n => Nat.rec L₂.init (fun k y => nxt k y) n
  have hg : ∀ n, R (r.st n) (g n) := by
    intro n
    induction n with
    | zero => rw [r.st_zero]; exact h0
    | succ n ih => exact (hnxt n (g n) ih).1
  exact ⟨⟨g, c, rfl, hc, fun n => (hnxt n (g n) (hg n)).2⟩, rfl⟩

/-! ### Limits of mapped chains -/

/-- The limit of a mapped chain is the image of the limit. -/
theorem lim_map {α β : Type} (φ : α → β) (c : Chain α) :
    Chain.lim (fun n => (c n).map φ) = List.map φ '' c.lim := by
  ext q
  constructor
  · rintro ⟨n, hn⟩
    have hq : q = ((c n).map φ).take q.length := (List.prefix_iff_eq_take.1 hn)
    have hq' : q = ((c n).take q.length).map φ := by rw [List.map_take]; exact hq
    exact ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, hq'.symm⟩
  · rintro ⟨p, ⟨n, hn⟩, rfl⟩
    exact ⟨n, hn.map φ⟩

/-! ### `stubUp` is injective on plays with the layout -/

variable {L : ULink} {P : Profile}

/-- `stubUp` is injective on moves with the layout. -/
theorem stubUp_inj {m m' : Move UImp L.U.F} (hm : L.MoveLayout m) (hm' : L.MoveLayout m')
    (h : L.stubUp m = L.stubUp m') : m = m' := by
  rcases m with e | (⟨f⟩ | ⟨f, a⟩) <;> rcases m' with e' | (⟨f'⟩ | ⟨f', a'⟩) <;>
    simp only [ULink.stubUp, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
  · rw [h]
  · simp only [Ev.ask.injEq] at h
    rw [stubQ_inj hm hm' h]
  · simp only [Ev.ans.injEq] at h
    obtain ⟨hf, ha⟩ := h
    have hff : f = f' := stubQ_inj hm.1 hm'.1 hf
    subst hff
    obtain ⟨as, ar⟩ := a
    obtain ⟨as', ar'⟩ := a'
    obtain ⟨hs, hr⟩ : L.stubS as = L.stubS as' ∧ ar = ar' := by
      simpa [ULink.stubR] using (eq_of_heq ha)
    have has : as = as' := stubS_inj hm.2 hm'.2 hs
    rw [has, hr]

/-- `stubUp` is injective on plays with the layout. -/
theorem map_stubUp_inj {p q : List (Move UImp L.U.F)} (hp : L.LayoutPlay p) (hq : L.LayoutPlay q)
    (h : p.map L.stubUp = q.map L.stubUp) : p = q := by
  induction p generalizing q with
  | nil => exact (List.map_eq_nil_iff.1 h.symm).symm
  | cons m p ih =>
    cases q with
    | nil => cases h
    | cons m' q =>
      obtain ⟨hm, hp'⟩ := List.cons.inj h
      have hmm : m = m' := stubUp_inj (hp m (by simp)) (hq m' (by simp)) hm
      have hpq : p = q :=
        ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (fun x hx => hq x (List.mem_cons_of_mem _ hx)) hp'
      rw [hmm, hpq]

/-- The layout of a play holds on its prefixes. -/
theorem LayoutPlay.of_prefix {p q : List (Move UImp L.U.F)} (hq : L.LayoutPlay q) (h : p <+: q) :
    L.LayoutPlay p :=
  fun m hm => hq m (h.subset hm)

/-- A play with the layout whose stubbed form is a prefix of a stubbed play with the layout is a
prefix of it. -/
theorem prefix_of_map_prefix {p q : List (Move UImp L.U.F)} (hp : L.LayoutPlay p)
    (hq : L.LayoutPlay q) (h : p.map L.stubUp <+: q.map L.stubUp) : p <+: q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨A, B, hAB, hA, -⟩ := List.map_eq_append_iff.1 hu.symm
  have hAl : L.LayoutPlay A := LayoutPlay.of_prefix hq ⟨B, hAB.symm⟩
  have hAp : A = p := map_stubUp_inj hAl hp hA
  exact ⟨B, by rw [hAB, hAp]⟩

/-! ### Linked infinite plays are composite infinite plays -/

/-- **Infinite plays: the linked module's are the composite's**, read through `stubUp`. -/
theorem link_inf_le_comp {I : Set (List (Move UImp L.U.F))} (hl : ∀ p ∈ I, L.LayoutPlay p)
    (h : I ∈ (L.U.dstrategy P).inf) : List.map L.stubUp '' I ∈ (L.compDStrategy P).inf := by
  obtain ⟨⟨r, hu, rfl⟩, hleg⟩ := h
  have hlay : ∀ n, L.LayoutPlay (r.tr n) := fun n => hl _ (Chain.mem_lim_self r.tr n)
  have hstep : ∀ n x, BRel L (r.st n) x → ∃ x', BRel L (r.st (n + 1)) x' ∧
      ∃ w, (r.tr (n + 1)).map L.stubUp = (r.tr n).map L.stubUp ++ w ∧ (Cmp L P).Run x w x' := by
    intro n x hR
    obtain ⟨w, hw, hrun⟩ := r.step n
    have hwl : L.LayoutPlay w := fun m hm => hlay (n + 1) m (by rw [hw]; exact List.mem_append_right _ hm)
    obtain ⟨x', hx', hR'⟩ := run_bsim hrun x hR hwl
    exact ⟨x', hR', w.map L.stubUp, by rw [hw, List.map_append], hx'⟩
  obtain ⟨r', hr'⟩ := infRun_of_chain (L₂ := Cmp L P) r (fun n => (r.tr n).map L.stubUp)
    (by simp only [r.tr_zero, List.map_nil]) (BRel L) BRel.idle hstep
  have hu' : r'.tr.Unbounded := by
    intro k
    obtain ⟨n, hn⟩ := hu k
    exact ⟨n, by rw [hr', List.length_map]; exact hn⟩
  have hlim : List.map L.stubUp '' r.tr.lim = r'.tr.lim := by rw [hr', lim_map]
  have hleg' : ∀ s ∈ List.map L.stubUp '' r.tr.lim, Legal s := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ := hleg p hp
    exact ⟨posUp L z, path_stubUp (L := L) hz⟩
  rw [compD_eq_ofLTS]
  exact ⟨⟨r', hu', hlim⟩, hleg'⟩

/-! ### Composite infinite plays are linked infinite plays -/

/-- **Infinite plays: the composite's are the linked module's**, for infinite plays with the
layout. -/
theorem comp_inf_le_link {I : Set (List (Move UImp L.U.F))} (hl : ∀ p ∈ I, L.LayoutPlay p)
    (h : List.map L.stubUp '' I ∈ (L.compDStrategy P).inf) : I ∈ (L.U.dstrategy P).inf := by
  rw [compD_eq_ofLTS] at h
  obtain ⟨⟨r, hu, hI⟩, -⟩ := h
  have hmem : ∀ n, r.tr n ∈ List.map L.stubUp '' I := fun n => hI ▸ Chain.mem_lim_self r.tr n
  choose p hpI hpeq using hmem
  have hpl : ∀ n, L.LayoutPlay (p n) := fun n => hl _ (hpI n)
  have hp0 : p 0 = [] := by
    have h0 : (p 0).map L.stubUp = [] := by rw [hpeq 0, r.tr_zero]
    exact List.map_eq_nil_iff.1 h0
  have hstep : ∀ n y, FRel L (r.st n) y → ∃ y', FRel L (r.st (n + 1)) y' ∧
      ∃ v, p (n + 1) = p n ++ v ∧ (L.U.lts P).Run y v y' := by
    intro n y hR
    obtain ⟨w, hw, hrun⟩ := r.step n
    have hmap : (p (n + 1)).map L.stubUp = (p n).map L.stubUp ++ w := by rw [hpeq, hpeq, hw]
    obtain ⟨A, B, hAB, hA, hB⟩ := List.map_eq_append_iff.1 hmap
    have hAl : L.LayoutPlay A := LayoutPlay.of_prefix (hpl (n + 1)) ⟨B, hAB.symm⟩
    have hBl : L.LayoutPlay B :=
      fun m hm => hpl (n + 1) m (by rw [hAB]; exact List.mem_append_right _ hm)
    have hAp : A = p n := map_stubUp_inj hAl (hpl n) hA
    obtain ⟨y', hy', hR'⟩ := run_sim hrun y B hR hB.symm hBl
    exact ⟨y', hR', B, by rw [hAB, hAp], hy'⟩
  obtain ⟨r', hr'⟩ := infRun_of_chain (L₂ := L.U.lts P) r p hp0 (FRel L) FRel.idle hstep
  have hlim : I = r'.tr.lim := by
    rw [hr']
    ext q
    constructor
    · intro hq
      have hq' : q.map L.stubUp ∈ r.tr.lim := hI ▸ ⟨q, hq, rfl⟩
      obtain ⟨n, hn⟩ := hq'
      have hn' : q.map L.stubUp <+: (p n).map L.stubUp := by rw [hpeq]; exact hn
      exact ⟨n, prefix_of_map_prefix (hl q hq) (hpl n) hn'⟩
    · rintro ⟨n, hn⟩
      have hq' : q.map L.stubUp ∈ r.tr.lim := ⟨n, by rw [← hpeq]; exact hn.map _⟩
      obtain ⟨q', hq'I, hqq⟩ : q.map L.stubUp ∈ List.map L.stubUp '' I := hI ▸ hq'
      have hqq' : q' = q :=
        map_stubUp_inj (hl q' hq'I) (LayoutPlay.of_prefix (hpl n) hn) hqq
      exact hqq' ▸ hq'I
  have hu' : r'.tr.Unbounded := by
    intro k
    obtain ⟨n, hn⟩ := hu k
    refine ⟨n, ?_⟩
    have hlen : (r.tr n).length = (p n).length := by rw [← hpeq, List.length_map]
    rw [hr', ← hlen]
    exact hn
  have hleg : ∀ s ∈ I, Legal s := by
    intro s hs
    rw [hlim] at hs
    obtain ⟨n, hn⟩ := hs
    have hrun : (L.U.lts P).Run .idle (r'.tr n) (r'.st n) := r'.run n
    exact Legal.of_prefix ⟨_, Untyped.run_pos hrun⟩ hn
  exact ⟨⟨r', hu', hlim⟩, hleg⟩

/-- **M3 in the untyped game, infinite plays, every profile.** -/
theorem link_inf_eq_comp {I : Set (List (Move UImp L.U.F))} (hl : ∀ p ∈ I, L.LayoutPlay p) :
    I ∈ (L.U.dstrategy P).inf ↔ List.map L.stubUp '' I ∈ (L.compDStrategy P).inf :=
  ⟨link_inf_le_comp hl, comp_inf_le_link hl⟩

end Silmaril.Proofs.Wasm.Game.ULink
