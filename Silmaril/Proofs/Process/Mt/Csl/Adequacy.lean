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

variable {U : TIsa S} {P : PrimTable U} {I : HProp A V} {Q : Nat → U.St → Heap A V → Prop}

theorem safeF_mono {R R' : Nat → U.St → Heap A V → Prop} (hR : ∀ t s h, R t s h → R' t s h)
    {t : Nat} {s : U.St} {h : Heap A V} (hf : SafeF U P I Q R t s h) :
    SafeF U P I Q R' t s h := by
  obtain ⟨hd, hl, hp, hsp⟩ := hf
  refine ⟨hd, ?_, ?_, ?_⟩
  · intro m ag
    obtain ⟨h1, h2, h3⟩ := hl m ag
    exact ⟨h1, h2, fun s' m' st => let ⟨k, r⟩ := h3 s' m' st; ⟨k, hR _ _ _ r⟩⟩
  · intro p args hc hI iI dj m ag
    obtain ⟨h1, h2⟩ := hp p args hc hI iI dj m ag
    refine ⟨h1, fun r m' st => ?_⟩
    obtain ⟨k, h', hI', a, b, c, d, e⟩ := h2 r m' st
    exact ⟨k, h', hI', a, b, c, d, hR _ _ _ e⟩
  · intro m ag s₁ s₂ sp
    obtain ⟨h₁, h₂, a, b, c, d⟩ := hsp m ag s₁ s₂ sp
    exact ⟨h₁, h₂, a, b, hR _ _ _ c, fun u => hR _ _ _ (d u)⟩

theorem safe_unfold {t : Nat} {s : U.St} {h : Heap A V} (hs : Safe U P I Q t s h) :
    SafeF U P I Q (Safe U P I Q) t s h := by
  obtain ⟨R, hR, hpost⟩ := hs
  exact safeF_mono (fun t s h r => ⟨R, r, hpost⟩) (hpost t s h hR)

theorem safe_fold {t : Nat} {s : U.St} {h : Heap A V} (hs : SafeF U P I Q (Safe U P I Q) t s h) :
    Safe U P I Q t s h :=
  ⟨fun t s h => SafeF U P I Q (Safe U P I Q) t s h, hs,
    fun _ _ _ hf => safeF_mono (fun _ _ _ r => safe_unfold r) hf⟩

/-! ## Preservation -/

theorem upd_eq {α : Type} (f : Nat → α) (t : Nat) (x : α) : Heap.upd f t x t = x := by
  simp [Heap.upd]

theorem upd_ne {α : Type} (f : Nat → α) {t u : Nat} (x : α) (h : u ≠ t) : Heap.upd f t x u = f u := by
  simp [Heap.upd, h]

theorem ginv_step {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U P I Q C hs hI) (st : Step U P C C') :
    ∃ hs' hI', GInv U P I Q C' hs' hI' := by
  obtain ⟨hdj, hdjI, hag, hagI, hIp, habs, hsafe⟩ := g
  cases st with
  | @loc t s s' m' hth hstep =>
    obtain ⟨-, hl, -, -⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨-, -, h3⟩ := hl C.mem (hag t)
    obtain ⟨kp, sf⟩ := h3 s' m' hstep
    refine ⟨Heap.upd hs t (S.cut (hs t) m'), hI, ?_, ?_, ?_, keeps_agrees kp (hdjI t) hagI, hIp,
      ?_, ?_⟩
    · intro u w huw
      by_cases hu : u = t
      · subst hu; rw [upd_eq, upd_ne _ _ (Ne.symm huw)]
        exact disjoint_of_domle cut_domle (hdj _ _ huw)
      · by_cases hw : w = t
        · subst hw; rw [upd_eq, upd_ne _ _ hu]
          exact disjoint_symm (disjoint_of_domle cut_domle (hdj _ _ (Ne.symm huw)))
        · rw [upd_ne _ _ hu, upd_ne _ _ hw]; exact hdj u w huw
    · intro u
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; exact disjoint_of_domle cut_domle (hdjI _)
      · rw [upd_ne _ _ hu]; exact hdjI u
    · intro u
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; exact cut_agrees
      · rw [upd_ne _ _ hu]; exact keeps_agrees kp (hdj _ _ (Ne.symm hu)) (hag u)
    · intro u hn
      dsimp only at hn
      by_cases hu : u = t
      · subst hu; simp [Heap.upd] at hn
      · rw [upd_ne _ _ hu]; rw [upd_ne _ _ hu] at hn; exact habs u hn
    · intro u s₀ hu₀
      dsimp only at hu₀
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; rw [upd_eq] at hu₀; cases hu₀; exact sf
      · rw [upd_ne _ _ hu]; rw [upd_ne _ _ hu] at hu₀; exact hsafe u s₀ hu₀
  | @prim t s p args r m' hth hc hpst =>
    obtain ⟨-, -, hp, -⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨-, h2⟩ := hp p args hc hI hIp (hdjI t) C.mem (agrees_union (hag t) hagI)
    obtain ⟨kp, h', hI', d', dom', ag', hI'p, sf⟩ := h2 r m' hpst
    have hfree : ∀ u, u ≠ t → Heap.Disjoint (Heap.union (hs t) hI) (hs u) := fun u hu =>
      disjoint_union (hdj _ _ (Ne.symm hu)) (disjoint_symm (hdjI u))
    have dh' : Heap.DomLe h' (Heap.union (hs t) hI) := domle_trans domle_union_left dom'
    have dI' : Heap.DomLe hI' (Heap.union (hs t) hI) := domle_trans domle_union_right dom'
    refine ⟨Heap.upd hs t h', hI', ?_, ?_, ?_, agrees_right d' ag', hI'p, ?_, ?_⟩
    · intro u w huw
      by_cases hu : u = t
      · subst hu; rw [upd_eq, upd_ne _ _ (Ne.symm huw)]
        exact disjoint_of_domle dh' (hfree _ (Ne.symm huw))
      · by_cases hw : w = t
        · subst hw; rw [upd_eq, upd_ne _ _ hu]
          exact disjoint_symm (disjoint_of_domle dh' (hfree _ hu))
        · rw [upd_ne _ _ hu, upd_ne _ _ hw]; exact hdj u w huw
    · intro u
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; exact d'
      · rw [upd_ne _ _ hu]; exact disjoint_symm (disjoint_of_domle dI' (hfree _ hu))
    · intro u
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; exact agrees_left ag'
      · rw [upd_ne _ _ hu]; exact keeps_agrees kp (hfree _ hu) (hag u)
    · intro u hn
      dsimp only at hn
      by_cases hu : u = t
      · subst hu; simp [Heap.upd] at hn
      · rw [upd_ne _ _ hu]; rw [upd_ne _ _ hu] at hn; exact habs u hn
    · intro u s₀ hu₀
      dsimp only at hu₀
      by_cases hu : u = t
      · subst hu; rw [upd_eq]; rw [upd_eq] at hu₀; cases hu₀; exact sf
      · rw [upd_ne _ _ hu]; rw [upd_ne _ _ hu] at hu₀; exact hsafe u s₀ hu₀
  | @spawn t u s s₁ s₂ hth hsp hun =>
    obtain ⟨-, -, -, hspf⟩ := safe_unfold (hsafe t s hth)
    obtain ⟨h₁, h₂, d12, hun12, sf₁, sf₂⟩ := hspf C.mem (hag t) s₁ s₂ hsp
    have hut : u ≠ t := by intro e; subst e; rw [hth] at hun; cases hun
    have hsu : hs u = Heap.empty := habs u hun
    have d1 : Heap.DomLe h₁ (hs t) := hun12 ▸ domle_union_left
    have d2 : Heap.DomLe h₂ (hs t) := hun12 ▸ domle_union_right
    have ag1 : S.Agrees h₁ C.mem := agrees_left (hun12 ▸ hag t)
    have ag2 : S.Agrees h₂ C.mem := agrees_right d12 (hun12 ▸ hag t)
    -- the new heaps: `u ↦ h₂`, `t ↦ h₁`, others unchanged
    let hs' := Heap.upd (Heap.upd hs t h₁) u h₂
    have hs'u : hs' u = h₂ := upd_eq _ _ _
    have hs't : hs' t = h₁ := by simp [hs', Heap.upd, Ne.symm hut]
    have hs'w : ∀ w, w ≠ t → w ≠ u → hs' w = hs w := fun w h1 h2 => by
      simp [hs', Heap.upd, h1, h2]
    -- every new heap is within an old one, disjoint from the others
    have dom' : ∀ w, Heap.DomLe (hs' w) (hs (if w = u then t else w)) := by
      intro w
      by_cases hwu : w = u
      · subst hwu; rw [hs'u]; simpa using d2
      · by_cases hwt : w = t
        · subst hwt; rw [hs't]; simpa [hwu] using d1
        · rw [hs'w w hwt hwu]; simpa [hwu] using domle_refl
    refine ⟨hs', hI, ?_, ?_, ?_, hagI, hIp, ?_, ?_⟩
    · intro w x hwx
      by_cases hwu : w = u
      · subst hwu
        by_cases hxt : x = t
        · subst hxt; rw [hs'u, hs't]; exact disjoint_symm d12
        · have hxu : x ≠ w := Ne.symm hwx
          rw [hs'u, hs'w x hxt hxu]; exact disjoint_of_domle d2 (hdj _ _ (Ne.symm hxt))
      · by_cases hxu : x = u
        · subst hxu
          by_cases hwt : w = t
          · subst hwt; rw [hs'u, hs't]; exact d12
          · rw [hs'u, hs'w w hwt hwu]
            exact disjoint_symm (disjoint_of_domle d2 (hdj _ _ (Ne.symm hwt)))
        · have e1 := dom' w; have e2 := dom' x
          simp only [hwu, hxu, ite_false] at e1 e2
          by_cases hwt : w = t
          · subst hwt; rw [hs't, hs'w x (Ne.symm hwx) hxu]
            exact disjoint_of_domle d1 (hdj _ _ hwx)
          · by_cases hxt : x = t
            · subst hxt; rw [hs't, hs'w w hwt hwu]
              exact disjoint_symm (disjoint_of_domle d1 (hdj _ _ (Ne.symm hwx)))
            · rw [hs'w w hwt hwu, hs'w x hxt hxu]; exact hdj w x hwx
    · intro w
      exact disjoint_of_domle (dom' w) (hdjI _)
    · intro w
      by_cases hwu : w = u
      · subst hwu; rw [hs'u]; exact ag2
      · by_cases hwt : w = t
        · subst hwt; rw [hs't]; exact ag1
        · rw [hs'w w hwt hwu]; exact hag w
    · intro w hn
      by_cases hwu : w = u
      · subst hwu; simp [Heap.upd] at hn
      · by_cases hwt : w = t
        · subst hwt; simp [Heap.upd, hwu] at hn
        · rw [hs'w w hwt hwu]; simp [Heap.upd, hwu, hwt] at hn; exact habs w hn
    · intro w s₀ hw₀
      by_cases hwu : w = u
      · subst hwu; rw [hs'u]; simp [Heap.upd] at hw₀; subst hw₀; exact sf₂ _
      · by_cases hwt : w = t
        · subst hwt; rw [hs't]; simp [Heap.upd, hwu] at hw₀; subst hw₀; exact sf₁
        · rw [hs'w w hwt hwu]; simp [Heap.upd, hwu, hwt] at hw₀; exact hsafe w s₀ hw₀

theorem ginv_reach {C C' : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U P I Q C hs hI) (r : Reach U P C C') : ∃ hs' hI', GInv U P I Q C' hs' hI' := by
  induction r generalizing hs hI with
  | refl => exact ⟨hs, hI, g⟩
  | step st _ ih =>
    obtain ⟨hs', hI', g'⟩ := ginv_step g st
    exact ih g'

/-! ## Consequences -/

theorem no_fault {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U P I Q C hs hI) :
    ¬ Fault U P C := by
  obtain ⟨-, hdjI, hag, hagI, hIp, -, hsafe⟩ := g
  rintro ⟨t, s, hth, hf | ⟨p, args, hc, hpf⟩⟩
  · obtain ⟨-, hl, -, -⟩ := safe_unfold (hsafe t s hth)
    exact (hl C.mem (hag t)).1 hf
  · obtain ⟨-, -, hp, -⟩ := safe_unfold (hsafe t s hth)
    exact (hp p args hc hI hIp (hdjI t) C.mem (agrees_union (hag t) hagI)).1 hpf

theorem no_race {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U P I Q C hs hI) :
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

theorem post {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V} (g : GInv U P I Q C hs hI)
    {t : Nat} {s : U.St} (ht : C.th t = some s) (hd : U.done s) : Q t s (hs t) :=
  (safe_unfold (g.2.2.2.2.2.2 t s ht)).1 hd

theorem good_of_ginv {C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U P I Q C hs hI) : Good U P I Q C :=
  ⟨no_fault g, no_race g, hs, hI, g.2.2.2.2.1, g.2.2.2.1, g.2.2.1, g.1, g.2.1,
    fun _ _ ht hd => post g ht hd⟩

theorem adequacy {C₀ C : Cfg U} {hs : Nat → Heap A V} {hI : Heap A V}
    (g : GInv U P I Q C₀ hs hI) (r : Reach U P C₀ C) : Good U P I Q C :=
  let ⟨_, _, g'⟩ := ginv_reach g r
  good_of_ginv g'

theorem ginv_single {t₀ : Nat} {s₀ : U.St} {m₀ : M} {h₀ hI : Heap A V}
    (hs : Safe U P I Q t₀ s₀ h₀) (hIp : I hI) (d : Heap.Disjoint h₀ hI) (ag : S.Agrees h₀ m₀)
    (agI : S.Agrees hI m₀) :
    GInv U P I Q (Cfg.single U t₀ s₀ m₀) (fun t => if t = t₀ then h₀ else Heap.empty) hI := by
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

end

end Silmaril.Proofs.Process.Mt.Csl
