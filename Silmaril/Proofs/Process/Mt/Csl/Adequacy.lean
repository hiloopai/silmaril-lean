module

public import Silmaril.Process.Mt.Csl.Defs

/-!
# Adequacy of the thread-modular decomposition (proofs)

`GInv` is preserved by every step of the multi-threaded system (`ginv_step`, `ginv_reach`), and
implies the global property `Good` (`good_of_ginv`): no fault (`no_fault`), no race (`no_race`),
the invariant, and the postconditions of finished threads.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Csl

open Silmaril.Process.Mt.Csl

variable {M A V : Type} {S : Store M A V}

/-! ## Heaps -/

namespace HeapL

variable {h h₁ h₂ g k : Heap A V} {m m' : M}

theorem disjoint_symm (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_left {a : A} {v : V} (e : h₁ a = some v) : Heap.union h₁ h₂ a = some v := by
  simp [Heap.union, e]

theorem union_right (d : Heap.Disjoint h₁ h₂) {a : A} {v : V} (e : h₂ a = some v) :
    Heap.union h₁ h₂ a = some v := by
  rcases d a with d | d
  · simp [Heap.union, d, e]
  · rw [d] at e; cases e

theorem union_cases {a : A} {v : V} (e : Heap.union h₁ h₂ a = some v) :
    h₁ a = some v ∨ (h₁ a = none ∧ h₂ a = some v) := by
  unfold Heap.union at e
  cases e₁ : h₁ a with
  | none => rw [e₁] at e; simp at e; exact Or.inr ⟨rfl, e⟩
  | some w => rw [e₁] at e; simp at e; exact Or.inl (by rw [e])

theorem agrees_union (a₁ : S.Agrees h₁ m) (a₂ : S.Agrees h₂ m) : S.Agrees (Heap.union h₁ h₂) m :=
  fun a v e => (union_cases e).elim (a₁ a v) (fun ⟨_, e⟩ => a₂ a v e)

theorem agrees_left (ag : S.Agrees (Heap.union h₁ h₂) m) : S.Agrees h₁ m :=
  fun a v e => ag a v (union_left e)

theorem agrees_right (d : Heap.Disjoint h₁ h₂) (ag : S.Agrees (Heap.union h₁ h₂) m) :
    S.Agrees h₂ m :=
  fun a v e => ag a v (union_right d e)

theorem domle_refl : Heap.DomLe h h := fun _ e => e

theorem domle_trans (d₁ : Heap.DomLe h g) (d₂ : Heap.DomLe g k) : Heap.DomLe h k :=
  fun a e => d₂ a (d₁ a e)

theorem domle_union_left : Heap.DomLe h₁ (Heap.union h₁ h₂) := by
  intro a e
  cases e₁ : h₁ a with
  | none => rw [e₁] at e; cases e
  | some v => simp [union_left e₁]

theorem domle_union_right : Heap.DomLe h₂ (Heap.union h₁ h₂) := by
  intro a e
  unfold Heap.union
  cases e₁ : h₁ a with
  | none => simpa using e
  | some v => simp

theorem domle_union {h₁ h₂ g : Heap A V} (d₁ : Heap.DomLe h₁ g) (d₂ : Heap.DomLe h₂ g) :
    Heap.DomLe (Heap.union h₁ h₂) g := by
  intro a e
  unfold Heap.union at e
  cases e₁ : h₁ a with
  | none => rw [e₁] at e; exact d₂ a (by simpa using e)
  | some v => exact d₁ a (by simp [e₁])

theorem disjoint_of_domle (d : Heap.DomLe g h) (dj : Heap.Disjoint h k) : Heap.Disjoint g k := by
  intro a
  rcases dj a with e | e
  · left
    cases eg : g a with
    | none => rfl
    | some v => have := d a (by simp [eg]); rw [e] at this; cases this
  · exact Or.inr e

theorem disjoint_union (d₁ : Heap.Disjoint h₁ k) (d₂ : Heap.Disjoint h₂ k) :
    Heap.Disjoint (Heap.union h₁ h₂) k := by
  intro a
  rcases d₁ a with e₁ | e₁
  · rcases d₂ a with e₂ | e₂
    · left; simp [Heap.union, e₁, e₂]
    · exact Or.inr e₂
  · exact Or.inr e₁

theorem cut_domle : Heap.DomLe (S.cut h m) h := by
  intro a e
  unfold Store.cut at e
  cases e₁ : h a with
  | none => rw [e₁] at e; cases e
  | some v => simp

theorem cut_agrees : S.Agrees (S.cut h m) m := by
  intro a v e
  unfold Store.cut at e
  cases e₁ : h a with
  | none => rw [e₁] at e; cases e
  | some w => rw [e₁] at e; simpa using e

theorem keeps_agrees (kp : S.Keeps h m m') (d : Heap.Disjoint h g) (ag : S.Agrees g m) :
    S.Agrees g m' := by
  intro a v e
  rcases d a with e' | e'
  · rw [kp a e']; exact ag a v e
  · rw [e'] at e; cases e

theorem isSome_of_eq {o : Option V} {v : V} (e : o = some v) : o.isSome := by simp [e]

end HeapL

open HeapL

/-! ## Unfolding `Safe` -/

section

variable {U : TIsa S} {I : HProp A V} {Q : Nat → U.St → Heap A V → Prop}

theorem atomicOk_mono {O : Type} {bad : M → Prop} {act : M → O → M → Prop}
    {K K' : O → Heap A V → Prop} (hK : ∀ o h, K o h → K' o h) {h : Heap A V}
    (ha : AtomicOk (S := S) I bad act K h) : AtomicOk (S := S) I bad act K' h := by
  intro hI iI dj m ag
  obtain ⟨h1, h2⟩ := ha hI iI dj m ag
  refine ⟨h1, fun o m' st => ?_⟩
  obtain ⟨k, h', hI', a, b, c, d, e⟩ := h2 o m' st
  exact ⟨k, h', hI', a, b, c, d, hK _ _ e⟩

theorem safeF_mono {R R' : Nat → U.St → Heap A V → Prop} (hR : ∀ t s h, R t s h → R' t s h)
    {t : Nat} {s : U.St} {h : Heap A V} (hf : SafeF U I Q R t s h) :
    SafeF U I Q R' t s h := by
  obtain ⟨hd, hl, hp, hsp⟩ := hf
  refine ⟨hd, ?_, atomicOk_mono (fun _ _ r => hR _ _ _ r) hp,
    fun u => atomicOk_mono ?_ (hsp u)⟩
  · intro m ag
    obtain ⟨h1, h2, h3⟩ := hl m ag
    exact ⟨h1, h2, fun s' m' st => let ⟨k, r⟩ := h3 s' m' st; ⟨k, hR _ _ _ r⟩⟩
  · rintro o h' ⟨h₁, h₂, a, b, c, d⟩
    exact ⟨h₁, h₂, a, b, hR _ _ _ c, hR _ _ _ d⟩

theorem safe_unfold {t : Nat} {s : U.St} {h : Heap A V} (hs : Safe U I Q t s h) :
    SafeF U I Q (Safe U I Q) t s h := by
  obtain ⟨R, hR, hpost⟩ := hs
  exact safeF_mono (fun t s h r => ⟨R, r, hpost⟩) (hpost t s h hR)

theorem safe_fold {t : Nat} {s : U.St} {h : Heap A V} (hs : SafeF U I Q (Safe U I Q) t s h) :
    Safe U I Q t s h :=
  ⟨fun t s h => SafeF U I Q (Safe U I Q) t s h, hs,
    fun _ _ _ hf => safeF_mono (fun _ _ _ r => safe_unfold r) hf⟩

/-! ## Preservation -/

theorem upd_eq {α : Type} (f : Nat → α) (t : Nat) (x : α) : Heap.upd f t x t = x := by
  simp [Heap.upd]

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : Heap.upd f t x u = f u := by
  simp [Heap.upd, h]

/-- **Rebuilding the compatibility conditions** after a step of thread `t`: the threads in `ch`
(including `t`) take new heaps `hs'`, and the invariant heap becomes `hI'`, all within the old
domain of `hs t ∪ hI`; the memory changed only there. -/
theorem ginv_rebuild {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI)
    {t : Nat} {ch : Nat → Prop} {C' : Cfg U} {hs' : Nat → Heap A V} {hI' : Heap A V}
    (cht : ch t) (same : ∀ w, ¬ ch w → hs' w = hs w)
    (kp : S.Keeps (Heap.union (hs t) hI) C.mem C'.mem)
    (dom : ∀ w, ch w → Heap.DomLe (hs' w) (Heap.union (hs t) hI))
    (domI : Heap.DomLe hI' (Heap.union (hs t) hI))
    (dj : ∀ w x, ch w → ch x → w ≠ x → Heap.Disjoint (hs' w) (hs' x))
    (djI : ∀ w, ch w → Heap.Disjoint (hs' w) hI')
    (ag : ∀ w, ch w → S.Agrees (hs' w) C'.mem) (agI : S.Agrees hI' C'.mem) (hI'p : I hI')
    (habs' : ∀ w, C'.th w = none → hs' w = Heap.empty)
    (hsafe' : ∀ w s, C'.th w = some s → Safe U I Q w s (hs' w)) :
    GInv U I Q C' hs' hI' := by
  obtain ⟨hdj, hdjI, hag, hagI, hIp, habs, hsafe⟩ := g
  have hne : ∀ w, ¬ ch w → w ≠ t := fun w hw e => hw (e ▸ cht)
  have hfree : ∀ w, w ≠ t → Heap.Disjoint (Heap.union (hs t) hI) (hs w) := fun w hw =>
    disjoint_union (hdj _ _ (Ne.symm hw)) (disjoint_symm (hdjI w))
  refine ⟨?_, ?_, ?_, agI, hI'p, habs', hsafe'⟩
  · intro w x hwx
    by_cases hw : ch w
    · by_cases hx : ch x
      · exact dj w x hw hx hwx
      · rw [same x hx]; exact disjoint_of_domle (dom w hw) (hfree x (hne x hx))
    · by_cases hx : ch x
      · rw [same w hw]
        exact disjoint_symm (disjoint_of_domle (dom x hx) (hfree w (hne w hw)))
      · rw [same w hw, same x hx]; exact hdj w x hwx
  · intro w
    by_cases hw : ch w
    · exact djI w hw
    · rw [same w hw]; exact disjoint_symm (disjoint_of_domle domI (hfree w (hne w hw)))
  · intro w
    by_cases hw : ch w
    · exact ag w hw
    · rw [same w hw]; exact keeps_agrees kp (hfree w (hne w hw)) (hag w)

theorem ginv_step {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C hs hI) (st : Step U C C') :
    ∃ hs' hI', GInv U I Q C' hs' hI' := by
  have g0 := g
  obtain ⟨hdj, hdjI, hag, hagI, hIp, habs, hsafe⟩ := g
  cases st with
  | @loc t s s' m' hth hstep =>
    obtain ⟨-, hl, -, -⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨-, -, h3⟩ := hl C.mem (hag t)
    obtain ⟨kp, sf⟩ := h3 s' m' hstep
    have kp' : S.Keeps (Heap.union (hs t) hI) C.mem m' := by
      intro a e
      apply kp a
      unfold Heap.union at e
      cases e₁ : hs t a with
      | none => rfl
      | some v => rw [e₁] at e; cases e
    refine ⟨Heap.upd hs t (S.cut (hs t) m'), hI, ginv_rebuild g0 (ch := (· = t)) rfl
      (fun w hw => upd_ne _ _ hw) kp' ?_ domle_union_right ?_ ?_ ?_
      (keeps_agrees kp (hdjI t) hagI) hIp ?_ ?_⟩
    · rintro w rfl; rw [upd_eq]; exact domle_trans cut_domle domle_union_left
    · rintro w x rfl rfl h; exact absurd rfl h
    · rintro w rfl; rw [upd_eq]; exact disjoint_of_domle cut_domle (hdjI _)
    · rintro w rfl; rw [upd_eq]; exact cut_agrees
    · intro w hn
      by_cases hw : w = t
      · subst hw; simp [Heap.upd] at hn
      · rw [upd_ne _ _ hw]; exact habs w (by simpa [Heap.upd, hw] using hn)
    · intro w s₀ hw₀
      by_cases hw : w = t
      · subst hw; simp [Heap.upd] at hw₀; subst hw₀; rw [upd_eq]; exact sf
      · rw [upd_ne _ _ hw]; exact hsafe w s₀ (by simpa [Heap.upd, hw] using hw₀)
  | @atom t s s' m' hth hstep =>
    obtain ⟨-, -, hp, -⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨-, h2⟩ := hp hI hIp (hdjI t) C.mem (agrees_union (hag t) hagI)
    obtain ⟨kp, h', hI', d', dom', ag', hI'p, sf⟩ := h2 s' m' hstep
    refine ⟨Heap.upd hs t h', hI', ginv_rebuild g0 (ch := (· = t)) rfl
      (fun w hw => upd_ne _ _ hw) kp ?_ (domle_trans domle_union_right dom') ?_ ?_ ?_
      (agrees_right d' ag') hI'p ?_ ?_⟩
    · rintro w rfl; rw [upd_eq]; exact domle_trans domle_union_left dom'
    · rintro w x rfl rfl h; exact absurd rfl h
    · rintro w rfl; rw [upd_eq]; exact d'
    · rintro w rfl; rw [upd_eq]; exact agrees_left ag'
    · intro w hn
      by_cases hw : w = t
      · subst hw; simp [Heap.upd] at hn
      · rw [upd_ne _ _ hw]; exact habs w (by simpa [Heap.upd, hw] using hn)
    · intro w s₀ hw₀
      by_cases hw : w = t
      · subst hw; simp [Heap.upd] at hw₀; subst hw₀; rw [upd_eq]; exact sf
      · rw [upd_ne _ _ hw]; exact hsafe w s₀ (by simpa [Heap.upd, hw] using hw₀)
  | @spawn t u s s₁ s₂ m' hth hun hsp =>
    obtain ⟨-, -, -, hspf⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨-, h2⟩ := hspf u hI hIp (hdjI t) C.mem (agrees_union (hag t) hagI)
    obtain ⟨kp, h', hI', d', dom', ag', hI'p, h₁, h₂, d12, hun12, sf₁, sf₂⟩ := h2 (s₁, s₂) m' hsp
    have hut : u ≠ t := by intro e; subst e; rw [hth] at hun; cases hun
    have dh' : Heap.DomLe h' (Heap.union (hs t) hI) := domle_trans domle_union_left dom'
    have d1 : Heap.DomLe h₁ h' := hun12 ▸ domle_union_left
    have d2 : Heap.DomLe h₂ h' := hun12 ▸ domle_union_right
    have ag1 : S.Agrees h₁ m' := agrees_left (hun12 ▸ agrees_left ag')
    have ag2 : S.Agrees h₂ m' := agrees_right d12 (hun12 ▸ agrees_left ag')
    let hs' := Heap.upd (Heap.upd hs t h₁) u h₂
    have hs'u : hs' u = h₂ := upd_eq _ _ _
    have hs't : hs' t = h₁ := by simp [hs', Heap.upd, Ne.symm hut]
    have hs'w : ∀ w, w ≠ t → w ≠ u → hs' w = hs w := fun w h1 h2 => by
      simp [hs', Heap.upd, h1, h2]
    refine ⟨hs', hI', ginv_rebuild g0 (ch := fun w => w = t ∨ w = u) (Or.inl rfl)
      (fun w hw => hs'w w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e))) kp ?_
      (domle_trans domle_union_right dom') ?_ ?_ ?_ (agrees_right d' ag') hI'p ?_ ?_⟩
    · rintro w (rfl | rfl)
      · rw [hs't]; exact domle_trans d1 dh'
      · rw [hs'u]; exact domle_trans d2 dh'
    · rintro w x (rfl | rfl) (rfl | rfl) hwx
      · exact absurd rfl hwx
      · rw [hs't, hs'u]; exact d12
      · rw [hs't, hs'u]; exact disjoint_symm d12
      · exact absurd rfl hwx
    · rintro w (rfl | rfl)
      · rw [hs't]; exact disjoint_of_domle d1 d'
      · rw [hs'u]; exact disjoint_of_domle d2 d'
    · rintro w (rfl | rfl)
      · rw [hs't]; exact ag1
      · rw [hs'u]; exact ag2
    · intro w hn
      by_cases hwu : w = u
      · subst hwu; simp [Heap.upd] at hn
      · by_cases hwt : w = t
        · subst hwt; simp [Heap.upd, hwu] at hn
        · rw [hs'w w hwt hwu]; exact habs w (by simpa [Heap.upd, hwu, hwt] using hn)
    · intro w s₀ hw₀
      by_cases hwu : w = u
      · subst hwu; rw [hs'u]; simp [Heap.upd] at hw₀; subst hw₀; exact sf₂
      · by_cases hwt : w = t
        · subst hwt; rw [hs't]; simp [Heap.upd, hwu] at hw₀; subst hw₀; exact sf₁
        · rw [hs'w w hwt hwu]; exact hsafe w s₀ (by simpa [Heap.upd, hwu, hwt] using hw₀)

theorem ginv_reach {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C hs hI) (r : Reach U C C') : ∃ hs' hI', GInv U I Q C' hs' hI' := by
  induction r generalizing hs hI with
  | refl => exact ⟨hs, hI, g⟩
  | step st _ ih =>
    obtain ⟨hs', hI', g'⟩ := ginv_step g st
    exact ih g'

/-! ## Consequences -/

theorem no_fault {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI) :
    ¬ Fault U C := by
  obtain ⟨-, hdjI, hag, hagI, hIp, -, hsafe⟩ := g
  rintro ⟨t, s, hth, hf | hf⟩
  · obtain ⟨-, hl, -, -⟩ := safe_unfold (hsafe t s hth)
    exact (hl C.mem (hag t)).1 hf
  · obtain ⟨-, -, hp, -⟩ := safe_unfold (hsafe t s hth)
    exact (hp hI hIp (hdjI t) C.mem (agrees_union (hag t) hagI)).1 hf

theorem no_race {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI) :
    ¬ Race U C := by
  obtain ⟨hdj, -, hag, -, -, -, hsafe⟩ := g
  rintro ⟨t, u, s, s', a, htu, ht, hu, ft, fu⟩
  obtain ⟨-, hlt, -, -⟩ := safe_unfold (hsafe t s ht)
  obtain ⟨-, hlu, -, -⟩ := safe_unfold (hsafe u s' hu)
  have e1 := (hlt C.mem (hag t)).2.1 a ft
  have e2 := (hlu C.mem (hag u)).2.1 a fu
  rcases hdj t u htu a with e | e
  · rw [e] at e1; cases e1
  · rw [e] at e2; cases e2

theorem post {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C hs hI)
    {t : Nat} {s : U.St} (ht : C.th t = some s) (hd : U.done s) : Q t s (hs t) :=
  (safe_unfold (g.2.2.2.2.2.2 t s ht)).1 hd

theorem good_of_ginv {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C hs hI) : Good U I Q C :=
  ⟨no_fault g, no_race g, hs, hI, g.2.2.2.2.1, g.2.2.2.1, g.2.2.1, g.1, g.2.1,
    fun _ _ ht hd => post g ht hd⟩

theorem adequacy {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U I Q C₀ hs hI) (r : Reach U C₀ C) : Good U I Q C :=
  let ⟨_, _, g'⟩ := ginv_reach g r
  good_of_ginv g'

theorem ginv_single {t₀ : Nat} {s₀ : U.St} {m₀ : M} {h₀ hI : Heap A V}
    (hs : Safe U I Q t₀ s₀ h₀) (hIp : I hI) (d : Heap.Disjoint h₀ hI) (ag : S.Agrees h₀ m₀)
    (agI : S.Agrees hI m₀) :
    GInv U I Q (Cfg.single U t₀ s₀ m₀) (fun t => if t = t₀ then h₀ else Heap.empty) hI := by
  refine ⟨?_, ?_, ?_, agI, hIp, ?_, ?_⟩
  · intro t u htu a
    by_cases ht : t = t₀
    · subst ht; right; simp [Ne.symm htu, Heap.empty]
    · left; simp [ht, Heap.empty]
  · intro t a
    by_cases ht : t = t₀
    · subst ht; simpa using d a
    · left; simp [ht, Heap.empty]
  · intro t a v e
    by_cases ht : t = t₀
    · subst ht; simp at e; exact ag a v e
    · simp [ht, Heap.empty] at e
  · intro t hn
    by_cases ht : t = t₀
    · subst ht; simp [Cfg.single] at hn
    · simp [ht]
  · intro t s e
    by_cases ht : t = t₀
    · subst ht; simp [Cfg.single] at e; subst e; simpa using hs
    · simp [Cfg.single, ht] at e

/-- **Adequacy under a concrete model** that refines SC with atomic steps on certified
programs. -/
theorem adequacy_model {X : Model U} (hX : X.Sound I Q) {c₀ c : X.Conf} {C₀ : Cfg U}
    {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U I Q C₀ hs hI) (ha : X.abs c₀ C₀)
    (r : Star X.step c₀ c) : ¬ X.fault c ∧ ∃ C, X.abs c C ∧ Good U I Q C := by
  obtain ⟨C, rC, hac, hf⟩ := hX c₀ c C₀ ha ⟨hs, hI, g⟩ r
  have gd := adequacy g rC
  exact ⟨fun f => gd.1 (hf f), C, hac, gd⟩

/-! ## Primitive calls -/

/-- The atomic obligations of a primitive call site follow from `PrimOk` of its spec. -/
theorem atomOk_prims {σ : Type} {P : Prims σ M} {K : σ → Heap A V → Prop}
    {t : Nat} {s : σ} {h : Heap A V}
    (hc : ∀ p args, P.call s = some (p, args) →
      AtomicOk (S := S) I ((P.spec p).fault t args) ((P.spec p).step t args)
        (fun r h' => K (P.resume s r) h') h) :
    AtomicOk (S := S) I (P.afault t s) (fun m s' m' => P.atom t s m s' m') K h := by
  intro hI iI dj m ag
  refine ⟨?_, ?_⟩
  · rintro ⟨p, args, e, f⟩
    exact (hc p args e hI iI dj m ag).1 f
  · rintro s' m' ⟨p, args, r, e, st, rfl⟩
    exact (hc p args e hI iI dj m ag).2 r m' st

end

end Silmaril.Proofs.Process.Mt.Csl
