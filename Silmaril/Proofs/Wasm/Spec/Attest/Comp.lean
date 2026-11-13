module

public import Silmaril.Wasm.Spec.Attest.Defs
public import Silmaril.Games.Composition.Defs

/-!
# Relabelling and composition: may-call and trap propagation

* `inl_mem_map_move`, `relabel_trapProp`: lower moves and trap propagation of a relabelled
  strategy;
* `zip_inl_mem`, `zip_inr_mem`, `zip_snoc_left`, `zip_append_sync`: interactions;
* `Compat`, `zip_path`: positions along an interaction (copied, see below);
* `comp_trapProp`: composition preserves trap propagation.

`Compat` and `zip_path` are copied from `Silmaril.Proofs.Games.Composition.Legal` (this
repository, same statements and proof), which its topic does not export. The rest is new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Spec.Attest

universe u

variable {E E' F G : Sig.{u}}

/-! ### Relabelling -/

/-- A lower move of a relabelled play is the image of a lower move. -/
theorem inl_mem_map_move (ι : Relabel E E') {q : List (Move E F)} {x : Ev E'}
    (h : (.inl x : Move E' F) ∈ q.map ι.move) : ∃ y, (.inl y : Move E F) ∈ q ∧ ι.ev y = x := by
  obtain ⟨o, ho, he⟩ := List.mem_map.1 h
  rcases o with y | y
  · exact ⟨y, ho, Sum.inl.inj he⟩
  · cases he

/-- A relabelled question is the image of a question. -/
theorem ev_eq_ask (ι : Relabel E E') {y : Ev E} {m' : E'.Op} (h : ι.ev y = .ask m') :
    ∃ m, y = .ask m ∧ ι.op m = m' := by
  cases y with
  | ask m => exact ⟨m, rfl, Ev.ask.inj h⟩
  | ans m n => cases h

/-- **Relabelling preserves trap propagation** when the trap answers correspond. -/
theorem relabel_trapProp {σ : Strategy E F} {ι : Relabel E E'} {stopE : ∀ m : E.Op, E.Ar m}
    {stopE' : ∀ m : E'.Op, E'.Ar m} {stopF : ∀ q : F.Op, F.Ar q} (h : TrapProp σ stopE stopF)
    (hs : ∀ m, ι.ar m (stopE' (ι.op m)) = stopE m) : TrapProp (relabel σ ι) stopE' stopF := by
  rintro _ q m' ⟨p, hp, rfl⟩ hw
  obtain ⟨y₀, hy₀⟩ := σ.legal hp
  have hpos : ι.pos y₀ = .wait q m' := Path.det (path_map ι hy₀) hw
  obtain ⟨m, rfl, rfl⟩ : ∃ m, y₀ = .wait q m ∧ ι.op m = m' := by
    cases y₀ with
    | idle => cases hpos
    | run _ => cases hpos
    | wait q₀ m₀ =>
      have hw' : Pos.wait q₀ (ι.op m₀) = (.wait q m' : Pos E' F) := hpos
      cases hw'
      exact ⟨m₀, rfl, rfl⟩
  have hsymm : (ι.ar m).symm (stopE m) = stopE' (ι.op m) :=
    (Equiv.symm_apply_eq _).2 (hs m).symm
  refine ⟨p ++ [.inl (.ans m (stopE m)), .inr (.ans q (stopF q))], h p q m hp hy₀, ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, Relabel.move, Sum.map_inl,
    Sum.map_inr, Relabel.ev, hsymm, id]

/-! ### Interactions -/

section Zip

variable {α β γ : Type u}

/-- A visible lower move of an interaction is a move of the lower trace. -/
theorem zip_inl_mem {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p)
    {a : α} (ha : (.inl a : α ⊕ γ) ∈ p) : (.inl a : α ⊕ β) ∈ s := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | left a' _ ih =>
    rcases List.mem_cons.1 ha with h | h
    · obtain rfl : a = a' := Sum.inl.inj h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)
  | right c _ ih =>
    rcases List.mem_cons.1 ha with h | h
    · cases h
    · exact ih h
  | sync b _ ih => exact List.mem_cons_of_mem _ (ih ha)

/-- A shared move of the lower trace is a move of the upper trace. -/
theorem zip_inr_mem {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p)
    {b : β} (hb : (.inr b : α ⊕ β) ∈ s) : (.inl b : β ⊕ γ) ∈ t := by
  induction h with
  | nil => exact absurd hb List.not_mem_nil
  | left a _ ih =>
    rcases List.mem_cons.1 hb with h | h
    · cases h
    · exact ih h
  | right c _ ih => exact List.mem_cons_of_mem _ (ih hb)
  | sync b' _ ih =>
    rcases List.mem_cons.1 hb with h | h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- **An interaction ending with a visible lower move** comes from prefixes of the two traces,
the lower one ending with that move. -/
theorem zip_snoc_left {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {P : List (α ⊕ γ)} (h : Zip s t P) :
    ∀ {p : List (α ⊕ γ)} {a : α}, P = p ++ [.inl a] →
      ∃ s₁ t₁, s₁ ++ [.inl a] <+: s ∧ t₁ <+: t ∧ Zip s₁ t₁ p := by
  induction h with
  | nil => intro p a hp; exact absurd hp.symm (by simp)
  | @left s t P a' hz ih =>
    intro p a hp
    rcases p with _ | ⟨x, p⟩
    · obtain ⟨rfl, rfl⟩ : a' = a ∧ P = [] := by simpa using hp
      exact ⟨[], [], by simp, List.nil_prefix, .nil⟩
    · obtain ⟨rfl, hP⟩ : x = .inl a' ∧ P = p ++ [.inl a] := by simpa [eq_comm] using hp
      obtain ⟨s₁, t₁, hs, ht, hz₁⟩ := ih hP
      exact ⟨.inl a' :: s₁, t₁, List.cons_prefix_cons.2 ⟨rfl, hs⟩, ht, .left a' hz₁⟩
  | @right s t P c hz ih =>
    intro p a hp
    rcases p with _ | ⟨x, p⟩
    · simp at hp
    · obtain ⟨rfl, hP⟩ : x = .inr c ∧ P = p ++ [.inl a] := by simpa [eq_comm] using hp
      obtain ⟨s₁, t₁, hs, ht, hz₁⟩ := ih hP
      exact ⟨s₁, .inr c :: t₁, hs, List.cons_prefix_cons.2 ⟨rfl, ht⟩, .right c hz₁⟩
  | @sync s t P b hz ih =>
    intro p a hp
    obtain ⟨s₁, t₁, hs, ht, hz₁⟩ := ih hp
    exact ⟨.inr b :: s₁, .inl b :: t₁, List.cons_prefix_cons.2 ⟨rfl, hs⟩,
      List.cons_prefix_cons.2 ⟨rfl, ht⟩, .sync b hz₁⟩

/-- A shared move at the end of both traces. -/
theorem zip_append_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p)
    (b : β) : Zip (s ++ [.inr b]) (t ++ [.inl b]) p := by
  induction h with
  | nil => exact .sync b .nil
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b' _ ih => exact .sync b' ih

end Zip

/-! ### Positions along an interaction (copied) -/

/-- The reachable combinations of positions during an interaction. -/
inductive Compat : Pos E F → Pos F G → Pos E G → Prop
  | idle : Compat .idle .idle .idle
  | run (g : G.Op) : Compat .idle (.run g) (.run g)
  | call (g : G.Op) (f : F.Op) : Compat (.run f) (.wait g f) (.run g)
  | wait (g : G.Op) (f : F.Op) (e : E.Op) : Compat (.wait f e) (.wait g f) (.wait g e)

theorem zip_path {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b t b' →
      ∃ c', Path c p c' ∧ Compat a' b' c' := by
  induction h with
  | nil =>
    intro a b c a' b' hc hs ht
    cases hs; cases ht
    exact ⟨c, .nil _, hc⟩
  | @left s t p x _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inl x :: s) a' → Path b t b' →
      ∃ c', Path c (.inl x :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hst hs =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.wait _ _ _) hs ht
        exact ⟨c', .cons (.call _ _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.call _ _) hs ht
        exact ⟨c', .cons (.reply _ _ _) hp, hc'⟩
  | @right s t p y _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b (.inr y :: t) b' →
      ∃ c', Path c (.inr y :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases ht with
    | cons hst ht =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.run _) hs ht
        exact ⟨c', .cons (.ask _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih Compat.idle hs ht
        exact ⟨c', .cons (.ret _ _) hp, hc'⟩
  | @sync s t p z _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inr z :: s) a' → Path b (.inl z :: t) b' →
      ∃ c', Path c p c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hs₁ hs =>
      cases ht with
      | cons ht₁ ht =>
        cases hs₁ <;> cases ht₁ <;> cases hc
        · exact ih (Compat.call _ _) hs ht
        · exact ih (Compat.run _) hs ht

/-! ### Composition -/

/-- A play waiting for the answer to `m` ends with the question `m`. -/
theorem path_wait {E F : Sig.{u}} {P : List (Move E F)} {q : F.Op} {m : E.Op}
    (h : Path .idle P (.wait q m)) : ∃ p, P = p ++ [.inl (.ask m)] ∧ Path .idle p (.run q) := by
  rcases List.eq_nil_or_concat P with rfl | ⟨p, o, hP⟩
  · cases h
  · rw [List.concat_eq_append] at hP
    subst hP
    obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 h
    cases hst with
    | call => exact ⟨p, rfl, hy⟩

/-- The position before a lower question is a running position. -/
theorem step_call_inv {E F : Sig.{u}} {y z : Pos E F} {m : E.Op} (h : Step y (.inl (.ask m)) z) :
    ∃ f, y = .run f ∧ z = .wait f m := by
  cases h with
  | call f _ => exact ⟨f, rfl, rfl⟩

/-- `Compat` with a running lower side and a running composite. -/
theorem compat_run_inv {f : F.Op} {b : Pos F G} {g : G.Op} (h : Compat (E := E) (.run f) b (.run g)) :
    b = .wait g f := by
  cases h
  rfl

/-- **Composition preserves trap propagation.** -/
theorem comp_trapProp {σ : Strategy E F} {τ : Strategy F G} {stopE : ∀ m : E.Op, E.Ar m}
    {stopF : ∀ q : F.Op, F.Ar q} {stopG : ∀ q : G.Op, G.Ar q} (hσ : TrapProp σ stopE stopF)
    (hτ : TrapProp τ stopF stopG) : TrapProp (σ.comp τ) stopE stopG := by
  rintro P g e ⟨s, hs, t, ht, hz⟩ hw
  obtain ⟨p, rfl, hp⟩ := path_wait hw
  obtain ⟨s₁, t₁, hs₁, ht₁, hz₁⟩ := zip_snoc_left hz rfl
  have hs₁σ : s₁ ++ [.inl (.ask e)] ∈ σ := σ.of_prefix hs hs₁
  have ht₁τ : t₁ ∈ τ := τ.of_prefix ht ht₁
  obtain ⟨a, ha⟩ := σ.legal hs₁σ
  obtain ⟨a₀, ha₀, hst⟩ := Path.concat_iff.1 ha
  obtain ⟨f, rfl, rfl⟩ := step_call_inv hst
  obtain ⟨b, hb⟩ := τ.legal ht₁τ
  obtain ⟨c', hc', hcompat⟩ := zip_path hz₁ Compat.idle ha₀ hb
  have hc'eq : c' = .run g := Path.det hc' hp
  have hbeq : b = .wait g f := compat_run_inv (hc'eq ▸ hcompat)
  have hσ' := hσ _ f e hs₁σ ha
  have hτ' := hτ _ g f ht₁τ (hbeq ▸ hb)
  refine ⟨_, hσ', _, hτ', ?_⟩
  have hz₂ := zip_append_sync ((hz₁.append_left (.ask e)).append_left (.ans e (stopE e)))
    (.ans f (stopF f))
  have hz₃ := hz₂.append_right (.ans g (stopG g))
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using hz₃

end Silmaril.Proofs.Wasm.Spec.Attest
