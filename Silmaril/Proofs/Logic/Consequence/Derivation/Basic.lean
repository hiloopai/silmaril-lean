module

public import Silmaril.Logic.Consequence.Derivation.Defs
public import Silmaril.Logic.Consequence.Structural.Defs

/-!
# Proofs for derivation systems

Inversion of validity, the checkers, grafting (for cut), soundness from local soundness, and the
agreement of proof trees with indexed lines.
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.Derivation

open Silmaril.Consequence

universe u v w

variable {J : Type u} {D : DerivationSystem.{u, v} J}

theorem valid_assume_iff {Γ : List J} {j : J} :
    D.Valid Γ (.assume j) ↔ j ∈ Γ :=
  ⟨fun h => by cases h; assumption, .assume⟩

theorem valid_infer_iff {Γ : List J} {r : D.Rule} {c : J} {ts : List D.Proof} :
    D.Valid Γ (.infer r c ts) ↔
      D.Instance r (ts.map ProofTree.concl) c ∧ ∀ t ∈ ts, D.Valid Γ t :=
  ⟨fun h => by cases h; constructor <;> assumption, fun h => .infer h.1 h.2⟩

section Check

variable [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)]

mutual

theorem check_iff (Γ : List J) : ∀ t : D.Proof, D.check Γ t = true ↔ D.Valid Γ t
  | .assume j => by simp [DerivationSystem.check, valid_assume_iff]
  | .infer r c ts => by
    simp only [DerivationSystem.check, Bool.and_eq_true, decide_eq_true_eq, valid_infer_iff,
      checkAll_iff Γ ts]

theorem checkAll_iff (Γ : List J) :
    ∀ ts : List D.Proof, D.checkAll Γ ts = true ↔ ∀ t ∈ ts, D.Valid Γ t
  | [] => by simp [DerivationSystem.checkAll]
  | t :: ts => by
    simp only [DerivationSystem.checkAll, Bool.and_eq_true, check_iff Γ t, checkAll_iff Γ ts,
      List.forall_mem_cons]

end

theorem checkLines_iff (Γ : List J) :
    ∀ (prev : List J) (ls : List (Line D.Rule J)),
      D.checkLines Γ prev ls = true ↔ D.LinesValid Γ prev ls
  | _, [] => by simp [DerivationSystem.checkLines, DerivationSystem.LinesValid]
  | prev, .assume j :: ls => by
    simp only [DerivationSystem.checkLines, DerivationSystem.LinesValid, Bool.and_eq_true,
      decide_eq_true_eq, checkLines_iff Γ (prev ++ [j]) ls]
  | prev, .infer r c ixs :: ls => by
    simp only [DerivationSystem.checkLines, DerivationSystem.LinesValid, Bool.and_eq_true,
      checkLines_iff Γ (prev ++ [c]) ls]
    cases h : DerivationSystem.cite prev ixs <;> simp

end Check

/-! ## Weakening and grafting -/

theorem Valid.mono {Γ Δ : List J} (hΓ : Γ ⊆ Δ) {t : D.Proof} (h : D.Valid Γ t) : D.Valid Δ t := by
  induction h with
  | assume hj => exact .assume (hΓ hj)
  | infer hr _ ih => exact .infer hr ih

theorem graft_concl (g : J → D.Proof) (hg : ∀ j, (g j).concl = j) :
    ∀ t : D.Proof, (ProofTree.graft g t).concl = t.concl
  | .assume j => by simp only [ProofTree.graft]; exact hg j
  | .infer _ _ _ => rfl

theorem graftAll_map_concl (g : J → D.Proof) (hg : ∀ j, (g j).concl = j) :
    ∀ ts : List D.Proof, (ProofTree.graftAll g ts).map ProofTree.concl = ts.map ProofTree.concl
  | [] => rfl
  | t :: ts => by
    simp only [ProofTree.graftAll, List.map_cons, graft_concl g hg t, graftAll_map_concl g hg ts]


theorem mem_graftAll {g : J → D.Proof} :
    ∀ {ts : List D.Proof} {s : D.Proof}, s ∈ ProofTree.graftAll g ts →
      ∃ t ∈ ts, s = ProofTree.graft g t
  | [], _, h => by simp [ProofTree.graftAll] at h
  | t :: ts, s, h => by
    simp only [ProofTree.graftAll, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨t, List.mem_cons_self, rfl⟩
    · obtain ⟨t', ht', rfl⟩ := mem_graftAll h
      exact ⟨t', List.mem_cons_of_mem _ ht', rfl⟩

/-- Grafting valid proofs of the assumptions keeps a proof valid. -/
theorem Valid.graft {Γ Δ : List J} {g : J → D.Proof} (hg : ∀ j, (g j).concl = j)
    (hΓ : ∀ j ∈ Γ, D.Valid Δ (g j)) {t : D.Proof} (h : D.Valid Γ t) :
    D.Valid Δ (ProofTree.graft g t) := by
  induction h with
  | assume hj => exact hΓ _ hj
  | @infer r c ts hr _ ih =>
    refine .infer ?_ ?_
    · rw [graftAll_map_concl g hg]; exact hr
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_graftAll hs
      exact ih t ht

/-! ## Structural closure -/

theorem exists_proofs {Γ : List J} :
    ∀ {ps : List J}, (∀ p ∈ ps, D.derives Γ p) →
      ∃ ts : List D.Proof, (∀ t ∈ ts, D.Valid Γ t) ∧ ts.map ProofTree.concl = ps
  | [], _ => ⟨[], by simp, rfl⟩
  | p :: ps, h => by
    obtain ⟨t, ht, rfl⟩ := h p List.mem_cons_self
    obtain ⟨ts, hts, hmap⟩ := exists_proofs (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact ⟨t :: ts, by simpa [ht] using hts, by simp [hmap]⟩

theorem derives_closed : Structural.Closed Structural.tarskiRules D.derives where
  refl _ _ c hc := ⟨.assume c, .assume hc, rfl⟩
  weak _ _ _ hΓ := fun ⟨t, ht, hc⟩ => ⟨t, Valid.mono hΓ ht, hc⟩
  cut _ ps c hps hc := by
    classical
    obtain ⟨t, ht, rfl⟩ := hc
    let g : J → D.Proof := fun j =>
      if h : ∃ s : D.Proof, D.Valid (ps.flatMap Prod.fst) s ∧ s.concl = j then h.choose
      else .assume j
    have hg : ∀ j, (g j).concl = j := by
      intro j; simp only [g]; split
      · next h => exact h.choose_spec.2
      · rfl
    refine ⟨ProofTree.graft g t, Valid.graft hg ?_ ht, graft_concl g hg t⟩
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    obtain ⟨s, hs, hsc⟩ := hps p hp
    have hex : ∃ s : D.Proof, D.Valid (ps.flatMap Prod.fst) s ∧ s.concl = p.2 :=
      ⟨s, Valid.mono (fun x hx => List.mem_flatMap.2 ⟨p, hp, hx⟩) hs, hsc⟩
    simp only [g, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec.1

/-! ## Soundness -/

theorem Valid.sound {M : Type w} {sat : M → J → Prop} (hD : D.LocallySound sat) (m : M)
    {Γ : List J} (hΓ : ∀ j ∈ Γ, sat m j) {t : D.Proof} (h : D.Valid Γ t) : sat m t.concl := by
  induction h with
  | assume hj => exact hΓ _ hj
  | @infer r c ts hr _ ih =>
    exact hD m r _ c hr (fun p hp => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
      exact ih t ht)

/-! ## Indexed lines -/

theorem cite_sub {prev : List J} :
    ∀ {ixs : List ℕ} {ps : List J}, DerivationSystem.cite prev ixs = some ps → ∀ p ∈ ps, p ∈ prev
  | [], ps, h => by
    intro p hp; simp only [DerivationSystem.cite, Option.some.injEq] at h; subst h; simp at hp
  | i :: ixs, ps, h => by
    simp only [DerivationSystem.cite] at h
    split at h
    · next p ps' hp hps =>
      cases h
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_of_getElem? hp
      · exact cite_sub hps q hq
    · cases h

theorem lines_sound {Γ : List J} :
    ∀ {prev : List J} {ls : List (Line D.Rule J)}, (∀ p ∈ prev, D.derives Γ p) →
      D.LinesValid Γ prev ls → ∀ l ∈ ls, D.derives Γ l.concl
  | _, [], _, _ => by simp
  | prev, .assume j :: ls, hprev, ⟨hj, hls⟩ => by
    have hj' : D.derives Γ j := ⟨.assume j, .assume hj, rfl⟩
    have := lines_sound (prev := prev ++ [j]) (ls := ls)
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hprev p hp
        · rw [List.mem_singleton.1 hp]; exact hj') hls
    simpa [Line.concl, hj'] using this
  | prev, .infer r c ixs :: ls, hprev, ⟨⟨ps, hps, hr⟩, hls⟩ => by
    obtain ⟨ts, hts, hmap⟩ := exists_proofs (D := D) (Γ := Γ)
      (fun p hp => hprev p (cite_sub hps p hp))
    have hc : D.derives Γ c := ⟨.infer r c ts, .infer (by rw [hmap]; exact hr) hts, rfl⟩
    have := lines_sound (prev := prev ++ [c]) (ls := ls)
      (fun p hp => by
        rcases List.mem_append.1 hp with hp | hp
        · exact hprev p hp
        · rw [List.mem_singleton.1 hp]; exact hc) hls
    simpa [Line.concl, hc] using this

theorem linearDerives_le : D.linearDerives ≤ D.derives := fun Γ c ⟨ls, hls, hlast⟩ => by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hlast
  exact lines_sound (by simp) hls l (List.mem_of_getLast? hl)

theorem linesValid_append {Γ : List J} :
    ∀ {prev : List J} {ls₁ ls₂ : List (Line D.Rule J)},
      D.LinesValid Γ prev (ls₁ ++ ls₂) ↔
        D.LinesValid Γ prev ls₁ ∧ D.LinesValid Γ (prev ++ ls₁.map Line.concl) ls₂
  | _, [], _ => by simp [DerivationSystem.LinesValid]
  | prev, .assume j :: ls₁, ls₂ => by
    simp only [List.cons_append, DerivationSystem.LinesValid, linesValid_append, and_assoc,
      List.map_cons, Line.concl, List.append_assoc, List.nil_append]
  | prev, .infer r c ixs :: ls₁, ls₂ => by
    simp only [List.cons_append, DerivationSystem.LinesValid, linesValid_append, and_assoc,
      List.map_cons, Line.concl, List.append_assoc, List.nil_append]

theorem cite_append {prev more : List J} :
    ∀ {ixs : List ℕ} {ps : List J}, DerivationSystem.cite prev ixs = some ps →
      DerivationSystem.cite (prev ++ more) ixs = some ps
  | [], _, h => h
  | i :: ixs, ps, h => by
    simp only [DerivationSystem.cite] at h ⊢
    split at h
    · next p ps' hp hps =>
      cases h
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hp).1, hp, cite_append hps]
    · cases h

mutual

theorem lines_spec {Γ : List J} :
    ∀ (t : D.Proof) (prev : List J), D.Valid Γ t →
      D.LinesValid Γ prev (t.lines prev.length) ∧
        ((t.lines prev.length).getLast?).map Line.concl = some t.concl
  | .assume j, prev, h => by
    simp [ProofTree.lines, DerivationSystem.LinesValid, Line.concl, ProofTree.concl,
      valid_assume_iff.1 h]
  | .infer r c ts, prev, h => by
    obtain ⟨hr, hts⟩ := valid_infer_iff.1 h
    obtain ⟨h1, h2⟩ := linesAll_spec ts prev hts
    simp only [ProofTree.lines]
    refine ⟨linesValid_append.2 ⟨h1, ?_⟩, by simp [Line.concl, ProofTree.concl]⟩
    exact ⟨⟨_, h2, hr⟩, trivial⟩

theorem linesAll_spec {Γ : List J} :
    ∀ (ts : List D.Proof) (prev : List J), (∀ t ∈ ts, D.Valid Γ t) →
      D.LinesValid Γ prev (ProofTree.linesAll prev.length ts).1 ∧
        DerivationSystem.cite (prev ++ (ProofTree.linesAll prev.length ts).1.map Line.concl)
          (ProofTree.linesAll prev.length ts).2 = some (ts.map ProofTree.concl)
  | [], prev, _ => by simp [ProofTree.linesAll, DerivationSystem.LinesValid, DerivationSystem.cite]
  | t :: ts, prev, h => by
    have ht := h t List.mem_cons_self
    obtain ⟨h1, h2⟩ := lines_spec t prev ht
    set l := t.lines prev.length with hl
    have hlen : (prev ++ l.map Line.concl).length = prev.length + l.length := by simp
    obtain ⟨h3, h4⟩ := linesAll_spec ts (prev ++ l.map Line.concl)
      (fun s hs => h s (List.mem_cons_of_mem _ hs))
    rw [hlen] at h3 h4
    simp only [ProofTree.linesAll]
    refine ⟨linesValid_append.2 ⟨h1, h3⟩, ?_⟩
    have hne : l ≠ [] := by intro h0; simp [h0] at h2
    have hidx : (prev ++ l.map Line.concl)[prev.length + l.length - 1]? = some t.concl := by
      obtain ⟨x, hx, hxc⟩ := Option.map_eq_some_iff.1 h2
      rw [List.getLast?_eq_getElem?] at hx
      have hpos : 0 < l.length := List.length_pos_iff.2 hne
      rw [List.getElem?_append_right (by omega), List.getElem?_map]
      rw [show prev.length + l.length - 1 - prev.length = l.length - 1 by omega, hx]
      simpa using hxc
    have e : prev ++ (l ++ (ProofTree.linesAll (prev.length + l.length) ts).1).map Line.concl =
        (prev ++ l.map Line.concl) ++
          (ProofTree.linesAll (prev.length + l.length) ts).1.map Line.concl := by simp
    simp only [DerivationSystem.cite, List.map_cons]
    rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hidx).1, hidx, h4]

end

theorem derives_le_linear : D.derives ≤ D.linearDerives := fun Γ c ⟨t, ht, hc⟩ =>
  ⟨t.lines 0, by simpa using (lines_spec t [] ht).1, by simpa [hc] using (lines_spec t [] ht).2⟩

/-! ## Elaboration -/

mutual

theorem elaborate_concl {R : Type w} (f : R → List J → J → Option D.Rule) :
    ∀ {t : ProofTree R J} {t' : D.Proof}, ProofTree.elaborate f t = some t' → t'.concl = t.concl
  | .assume j, t', h => by simp [ProofTree.elaborate] at h; simp [← h, ProofTree.concl]
  | .infer r c ts, t', h => by
    simp only [ProofTree.elaborate] at h
    split at h
    · cases h; rfl
    · cases h

end

theorem elaborateLines_concl {R : Type w} (f : R → List J → J → Option D.Rule) :
    ∀ {prev : List J} {ls : List (Line R J)} {ls' : List (Line D.Rule J)},
      Line.elaborate f prev ls = some ls' → ls'.map Line.concl = ls.map Line.concl
  | _, [], ls', h => by simp [Line.elaborate] at h; simp [← h]
  | prev, .assume j :: ls, ls', h => by
    simp only [Line.elaborate, Option.map_eq_some_iff] at h
    obtain ⟨ls'', h', rfl⟩ := h
    simp [Line.concl, elaborateLines_concl f h']
  | prev, .infer r c ixs :: ls, ls', h => by
    simp only [Line.elaborate] at h
    split at h
    · next r' ls'' _ h' => cases h; simp [Line.concl, elaborateLines_concl f h']
    · cases h

end Silmaril.Proofs.Logic.Consequence.Derivation
