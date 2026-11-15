module

public import Silmaril.Wasm.Abstract.FullObs.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Games.Abstract.FullFun.Thms
public import Silmaril.Games.Abstract.ModuleInf.Thms

/-!
# Productive runs of iterated bodies (proofs)

`toInf_iter`: the productive runs of `iter F` are those of `FullFun.iter (toFull F)`:

* one iteration is unfolded by the Elgot fixpoint law and `toInf_comp`
  (`mem_toInf_iter_step`);
* a run that never reaches a productive run of a single iteration gives, by choice, an
  infinite chain of finished continuing iterations. Its logs have unbounded total length,
  since otherwise the chain is eventually silent and the loop diverges there
  (`AFun.IterBeh.spin`, `toAFun_iter`), which no productive run does;
* conversely an infinite chain is a run because every finite prefix of the stream is pending
  (`mem_toInf_iff_streamPrefix`): determinism of bodies given the answers.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObs

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Abstract.FullObs Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-! ## Trees -/

theorem not_infPath_ret {Y : Type (u + 1)} {v : Y} {ω : Nat → Call E} :
    ¬ InfPath (ret v : Tree (SigEv E) Y) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h, -⟩ := hτ 0
  rw [h0] at h
  exact ret_ne_vis _ _ _ h

theorem not_infPath_diverge {Y : Type (u + 1)} {ω : Nat → Call E} :
    ¬ InfPath (diverge : Tree (SigEv E) Y) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h, -⟩ := hτ 0
  rw [h0] at h
  exact vis_ne_diverge _ _ h.symm

theorem path_nil_div {Y : Type (u + 1)} {t : Tree (SigEv E) Y} (h : Path t [] .div) :
    t = diverge := by
  cases h with
  | div h => exact h

theorem pend_bind_left {Y Z : Type (u + 1)} {t : Tree (SigEv E) Y} {k : Y → Tree (SigEv E) Z}
    {cs : List (Call E)} {m : E.Op} (h : Pend t cs m) : Pend (t >>= k) cs m := by
  induction h with
  | here ht => rw [ht, vis_bind]; exact .here rfl
  | vis ht _ ih => rw [ht, vis_bind]; exact .vis rfl ih

theorem pend_bind_path_aux {Y Z : Type (u + 1)} {t : Tree (SigEv E) Y}
    {k : Y → Tree (SigEv E) Z} {cs : List (Call E)} {r : PathEnd Y} (hp : Path t cs r)
    {cs' : List (Call E)} {m : E.Op} :
    ∀ v, r = .val v → Pend (k v) cs' m → Pend (t >>= k) (cs ++ cs') m := by
  induction hp with
  | ret ht =>
    intro v hv hk
    cases hv
    rw [ht, List.nil_append]
    exact (pure_bind (m := Tree (SigEv E)) _ k).symm ▸ hk
  | div _ => intro v hv; cases hv
  | vis ht _ ih =>
    intro v hv hk
    rw [ht, vis_bind, List.cons_append]
    exact .vis rfl (ih v hv hk)

theorem pend_bind_path {Y Z : Type (u + 1)} {t : Tree (SigEv E) Y} {k : Y → Tree (SigEv E) Z}
    {cs : List (Call E)} {v : Y} (hp : Path t cs (.val v)) {cs' : List (Call E)} {m : E.Op}
    (hk : Pend (k v) cs' m) : Pend (t >>= k) (cs ++ cs') m :=
  pend_bind_path_aux hp v rfl hk

theorem pend_of_path {Y : Type (u + 1)} {t : Tree (SigEv E) Y} {L : List (Call E)}
    {r : PathEnd Y} (hp : Path t L r) :
    ∀ (p : List (Call E)) (c : Call E) (q : List (Call E)), L = p ++ c :: q → Pend t p c.1 := by
  induction hp with
  | ret _ => intro p c q h; simp at h
  | div _ => intro p c q h; simp at h
  | vis ht _ ih =>
    intro p c q h
    cases p with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj (h.trans (List.nil_append _))
      exact .here ht
    | cons x p =>
      obtain ⟨rfl, h₂⟩ := List.cons.inj (h.trans (List.cons_append ..))
      exact .vis ht (ih p c q h₂)

/-! ## Bodies -/

theorem endOf_eq_ret {r : PathEnd (Except T (B × S))} {b : B} {s : S}
    (h : endOf r = .ret b s) : r = .val (.ok (b, s)) := by
  rcases r with (_ | ⟨b', s'⟩) | _
  · simp [endOf] at h
  · simp only [endOf, End.ret.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp [endOf] at h

theorem endOf_eq_div {r : PathEnd (Except T (B × S))} (h : endOf r = .div) : r = .div := by
  rcases r with (_ | ⟨b', s'⟩) | _
  · simp [endOf] at h
  · simp [endOf] at h
  · rfl

/-- A silent divergence and a productive run exclude each other. -/
theorem not_div_inf {f : Hom E S T A B} {s : S} {a : A} {ω : Nat → Call (liftSig E)}
    (hd : ([], End.div) ∈ toAFun f s a) (hω : ω ∈ toInf f s a) : False := by
  obtain ⟨cs, r, hp, he⟩ := hd
  obtain ⟨ω', hω', -⟩ := hω
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
  obtain rfl : cs = [] := List.map_eq_nil_iff.1 h₁.symm
  rw [endOf_eq_div h₂.symm] at hp
  rw [path_nil_div hp] at hω'
  exact not_infPath_diverge hω'

/-- The run of an iterated body, one iteration unfolded. -/
theorem run_iter_unfold (F : Hom E S T A (B ⊕ A)) (a : A) (s : S) :
    ∃ K : Except T ((B ⊕ A) × S) → Tree (SigEv E) (Except T (B × S)),
      ((Silmaril.Elgot.iter F a).run s).run = ((F a).run s).run >>= K ∧
        ∀ a' s', K (.ok (.inr a', s')) = ((Silmaril.Elgot.iter F a').run s').run := by
  have h : ((Silmaril.Elgot.iter F a).run s).run =
      ((F a >>= Sum.elim pure (Silmaril.Elgot.iter F)).run s).run := by
    conv_lhs => rw [Silmaril.Elgot.LawfulElgotMonad.fixpoint F]
  rw [StateT.run_bind, ExceptT.run_bind] at h
  exact ⟨_, h, fun _ _ => rfl⟩

/-- **One iteration unfolded**, for productive runs. -/
theorem mem_toInf_iter_step (F : Hom E S T A (B ⊕ A)) (s : S) (a : A)
    (ω : Nat → Call (liftSig E)) :
    ω ∈ toInf (Silmaril.Elgot.iter F) s a ↔ ω ∈ toInf F s a ∨
      ∃ (c : List (Call (liftSig E))) (a' : A) (s' : S) (ω' : Nat → Call (liftSig E)),
        (c, End.ret (.inr a') s') ∈ toAFun F s a ∧ ω' ∈ toInf (Silmaril.Elgot.iter F) s' a' ∧
          ω = c ++ₛ ω' := by
  have h : toInf (Silmaril.Elgot.iter F) =
      toInf (fun a => F a >>= Sum.elim pure (Silmaril.Elgot.iter F)) :=
    congrArg toInf (Silmaril.Elgot.LawfulElgotMonad.fixpoint F)
  have h' : ω ∈ toInf (Silmaril.Elgot.iter F) s a ↔
      ω ∈ toInf (fun a => F a >>= Sum.elim pure (Silmaril.Elgot.iter F)) s a := by
    rw [h]
  rw [h', toInf_comp, Set.mem_union, Set.mem_ofPred_eq]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨c, b | a', s₁, ω', hc, hω', rfl⟩
    · obtain ⟨ω'', hω'', -⟩ := hω'
      exact absurd hω'' not_infPath_ret
    · exact ⟨c, a', s₁, ω', hc, hω', rfl⟩
  · rintro ⟨c, a', s₁, ω', hc, hω', rfl⟩
    exact ⟨c, .inr a', s₁, ω', hc, hω', rfl⟩

/-! ## From an iterated run to a chain -/

/-- Case (a) of `FullFun.iter`: a finite continuing chain, then a productive run of the next
iteration. -/
def CaseA (F : Hom E S T A (B ⊕ A)) (s : S) (a : A) (ω : Nat → Call (liftSig E)) : Prop :=
  ∃ (c : List (Call (liftSig E))) (s' : S) (a' : A) (ω' : Nat → Call (liftSig E)),
    FullFun.ContChain (toAFun F) s a c s' a' ∧ ω' ∈ toInf F s' a' ∧ ω = c ++ₛ ω'

theorem caseA_of_contChain {F : Hom E S T A (B ⊕ A)} {s s' : S} {a a' : A}
    {c : List (Call (liftSig E))} (hc : FullFun.ContChain (toAFun F) s a c s' a')
    {ω' : Nat → Call (liftSig E)} (hω : ω' ∈ toInf F s' a') :
    c ++ₛ ω' ∈ toInf (Silmaril.Elgot.iter F) s a := by
  induction hc with
  | refl => exact (mem_toInf_iter_step F _ _ _).2 (.inl hω)
  | step h₁ _ ih =>
    refine cast (congrArg (· ∈ toInf (Silmaril.Elgot.iter F) _ _)
      (Stream'.append_append_stream _ _ ω').symm) ?_
    exact (mem_toInf_iter_step F _ _ _).2 (.inr ⟨_, _, _, _, h₁, ih hω, rfl⟩)

theorem next_of_not_caseA {F : Hom E S T A (B ⊕ A)} {s : S} {a : A}
    {ω : Nat → Call (liftSig E)} (hω : ω ∈ toInf (Silmaril.Elgot.iter F) s a)
    (hA : ¬ CaseA F s a ω) :
    ∃ (c : List (Call (liftSig E))) (a' : A) (s' : S) (ω' : Nat → Call (liftSig E)),
      (c, End.ret (.inr a') s') ∈ toAFun F s a ∧ ω' ∈ toInf (Silmaril.Elgot.iter F) s' a' ∧
        ¬ CaseA F s' a' ω' ∧ ω = c ++ₛ ω' := by
  rcases (mem_toInf_iter_step F s a ω).1 hω with h | ⟨c, a', s', ω', hc, hω', rfl⟩
  · exact absurd ⟨[], s, a, ω, .refl, h, rfl⟩ hA
  · refine ⟨c, a', s', ω', hc, hω', ?_, rfl⟩
    rintro ⟨c₂, s'', a'', ω'', hc₂, hω'', rfl⟩
    exact hA ⟨c ++ c₂, s'', a'', ω'', .step hc hc₂, hω'', (Stream'.append_append_stream _ _ _).symm⟩

/-- **An iterated run is of the form (a) or (b).** -/
theorem toInf_iter_subset (F : Hom E S T A (B ⊕ A)) (s : S) (a : A) :
    toInf (Silmaril.Elgot.iter F) s a ⊆ (FullFun.iter (toFull F)).2 s a := by
  intro ω hω
  by_cases hA : CaseA F s a ω
  · exact .inl hA
  refine .inr ?_
  classical
  let St := (S × A) × (Nat → Call (liftSig E))
  let P : St → Prop := fun p => p.2 ∈ toInf (Silmaril.Elgot.iter F) p.1.1 p.1.2 ∧
    ¬ CaseA F p.1.1 p.1.2 p.2
  have H : ∀ p : St, P p → ∃ q : List (Call (liftSig E)) × St,
      (q.1, End.ret (.inr q.2.1.2) q.2.1.1) ∈ toAFun F p.1.1 p.1.2 ∧ P q.2 ∧
        p.2 = q.1 ++ₛ q.2.2 := by
    intro p hp
    obtain ⟨c, a', s', ω', hc, hω', hA', he⟩ := next_of_not_caseA hp.1 hp.2
    exact ⟨(c, (s', a'), ω'), hc, ⟨hω', hA'⟩, he⟩
  let nxt : St → List (Call (liftSig E)) × St := fun p =>
    if h : P p then Classical.choose (H p h) else ([], p)
  let st : Nat → St := fun n => Nat.rec ((s, a), ω) (fun _ p => (nxt p).2) n
  have hst : ∀ n, st (n + 1) = (nxt (st n)).2 := fun _ => rfl
  have hP : ∀ n, P (st n) ∧ (nxt (st n)).1 ++ₛ (st (n + 1)).2 = (st n).2 ∧
      ((nxt (st n)).1, End.ret (.inr (st (n + 1)).1.2) (st (n + 1)).1.1) ∈
        toAFun F (st n).1.1 (st n).1.2 := by
    intro n
    induction n with
    | zero =>
      have h0 : P (st 0) := ⟨hω, hA⟩
      have hn : nxt (st 0) = Classical.choose (H _ h0) := dite_eq_left_of_eq_true (eq_true h0)
      obtain ⟨h₁, -, h₃⟩ := Classical.choose_spec (H _ h0)
      refine ⟨h0, ?_, ?_⟩
      · rw [hst, hn]; exact h₃.symm
      · rw [hst, hn]; exact h₁
    | succ n ih =>
      have hn0 : nxt (st n) = Classical.choose (H _ ih.1) := dite_eq_left_of_eq_true (eq_true ih.1)
      have h0 : P (st (n + 1)) := by
        rw [hst, hn0]; exact (Classical.choose_spec (H _ ih.1)).2.1
      have hn : nxt (st (n + 1)) = Classical.choose (H _ h0) := dite_eq_left_of_eq_true (eq_true h0)
      obtain ⟨h₁, -, h₃⟩ := Classical.choose_spec (H _ h0)
      refine ⟨h0, ?_, ?_⟩
      · rw [hst (n + 1), hn]; exact h₃.symm
      · rw [hst (n + 1), hn]; exact h₁
  let σ : Nat → S × A := fun n => (st n).1
  let l : Nat → List (Call (liftSig E)) := fun n => (nxt (st n)).1
  refine ⟨σ, l, rfl, fun n => (hP n).2.2, ?_⟩
  have hchain : ∀ n, (st n).2 = l n ++ₛ (st (n + 1)).2 := fun n => (hP n).2.1.symm
  refine streamConcat_of_appendChain (w := fun n => (st n).2) hchain ?_
  by_contra hu
  have hfr : ¬ ∀ N, ∃ n, N ≤ n ∧ l n ≠ [] := fun h => hu (Shape.unbounded_of_frequently l h)
  simp only [not_forall, not_exists, not_and, not_not] at hfr
  obtain ⟨N, hN⟩ := hfr
  have hd : ([], End.div) ∈ AFun.iter (toAFun F) (σ N).1 (σ N).2 := by
    refine AFun.IterBeh.spin (fun k => σ (N + k)) rfl fun k => ?_
    have := (hP (N + k)).2.2
    rwa [show (nxt (st (N + k))).1 = [] from hN (N + k) (Nat.le_add_right N k)] at this
  rw [← toAFun_iter] at hd
  exact not_div_inf hd (hP N).1.1

/-! ## From a chain to an iterated run -/

theorem chain_pend (F : Hom E S T A (B ⊕ A)) (k : Nat) :
    ∀ (σ : Nat → S × A) (l : Nat → List (Call (liftSig E))),
      (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ toAFun F (σ n).1 (σ n).2) →
      ∀ p q, p ++ q = (List.range k).flatMap l → q ≠ [] →
        ∃ cs m, Pend ((Silmaril.Elgot.iter F (σ 0).2).run (σ 0).1).run cs m ∧
          p = cs.map liftCall := by
  induction k with
  | zero =>
    intro σ l _ p q h hq
    simp only [List.range_zero, List.flatMap_nil, List.append_eq_nil_iff] at h
    exact absurd h.2 hq
  | succ k ih =>
    intro σ l hσ p q h hq
    have hsplit : (List.range (k + 1)).flatMap l =
        l 0 ++ (List.range k).flatMap (fun n => l (n + 1)) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [hsplit] at h
    obtain ⟨cs₀, r₀, hp₀, he₀⟩ := hσ 0
    obtain ⟨hl₀, hr₀⟩ := Prod.mk.inj he₀
    have hr₀' := endOf_eq_ret hr₀.symm
    subst hr₀'
    obtain ⟨K, hK, hKv⟩ := run_iter_unfold F (σ 0).2 (σ 0).1
    rw [hK]
    have later : ∀ c', p = l 0 ++ c' → (List.range k).flatMap (fun n => l (n + 1)) = c' ++ q →
        ∃ cs m, Pend (((F (σ 0).2).run (σ 0).1).run >>= K) cs m ∧ p = cs.map liftCall := by
      intro c' hp hrest
      obtain ⟨cs', m, hm, hc'⟩ := ih (fun n => σ (n + 1)) (fun n => l (n + 1))
        (fun n => hσ (n + 1)) c' q hrest.symm hq
      rw [← hKv] at hm
      exact ⟨cs₀ ++ cs', m, pend_bind_path hp₀ hm, by rw [hp, hl₀, hc', List.map_append]⟩
    rcases List.append_eq_append_iff.1 h with ⟨a', ha, hq'⟩ | ⟨c', hp, hrest⟩
    · cases a' with
      | nil =>
        rw [List.append_nil] at ha
        rw [List.nil_append] at hq'
        exact later [] (by rw [ha, List.append_nil]) (by rw [hq', List.nil_append])
      | cons x a'' =>
        rw [hl₀] at ha
        obtain ⟨L₁, L₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 ha
        obtain ⟨y, L₂', rfl, -, -⟩ := List.map_eq_cons_iff.1 h₂
        exact ⟨L₁, y.1, pend_bind_left (pend_of_path hp₀ L₁ y L₂' rfl), h₁.symm⟩
    · exact later c' hp hrest

/-- **A chain is an iterated run.** -/
theorem toInf_iter_supset (F : Hom E S T A (B ⊕ A)) (s : S) (a : A) :
    (FullFun.iter (toFull F)).2 s a ⊆ toInf (Silmaril.Elgot.iter F) s a := by
  rintro ω (⟨c, s', a', ω', hc, hω', rfl⟩ | ⟨σ, l, h0, hσ, hcat⟩)
  · exact caseA_of_contChain hc hω'
  refine (mem_toInf_iff_streamPrefix _ s a ω).2 fun L hL => ?_
  obtain ⟨k, hk⟩ := hcat.2 (L.length + 1)
  have hM := hcat.1 k
  set M := (List.range k).flatMap l
  have hLM : L = M.take L.length := by
    refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
    rw [List.getElem_take, ← hL i h₁, hM i (by omega)]
  obtain ⟨cs, m, hm, hcs⟩ := chain_pend F k σ l hσ L (M.drop L.length)
    (by rw [hLM, List.length_take_of_le (by omega), List.take_append_drop])
    (by simp; omega)
  rw [h0] at hm
  exact ⟨ULift.up m, cs, m, hm, by rw [hcs]; rfl⟩

/-- **Productive runs of an iterated body.** -/
theorem toInf_iter (F : Hom E S T A (B ⊕ A)) (s : S) (a : A) :
    toInf (Silmaril.Elgot.iter F) s a = (FullFun.iter (toFull F)).2 s a :=
  Set.Subset.antisymm (toInf_iter_subset F s a) (toInf_iter_supset F s a)

end Silmaril.Proofs.Wasm.Abstract.FullObs
