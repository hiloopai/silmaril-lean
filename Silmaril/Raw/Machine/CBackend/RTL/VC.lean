module

public import Silmaril.Machine.CBackend.RTL.VC.Defs
@[expose] public section
namespace Silmaril.Machine.CBackend.RTL.VC
open Silmaril.Machine.RTL
open Silmaril.Machine.Lir (Word Memory)
variable {fn : Func Nat} {cuts : List (Node × Cut)} {post : List Word → Memory → Prop}

theorem Reach.head {μ : Option Word} {s s' : State Nat} (h : Step (prog fn) s s')
    (hr : Reach fn cuts post μ s') : Reach fn cuts post μ s := by
  rcases hr with ⟨t, vs, m', ht, hf, hp⟩ | ⟨n', c, fr', m', hc, hh, hb, ht⟩
  · exact .inl ⟨t, vs, m', .head h ht, hf, hp⟩
  · exact .inr ⟨n', c, fr', m', hc, hh, hb, .head h ht⟩

theorem fetch_prog (fn : Func Nat) (n : Node) : (prog fn).fetch ⟨0, n⟩ = fn.instr? n := by
  simp [Prog.fetch, Prog.instr?, Prog.func?, prog]

/-- **Paths**: `wpN` from a frame below the actual one reaches a return or a cut point. -/
theorem path (μ : Option Word) : ∀ (k : Nat) (n : Node) (fr : Frame Nat) (m : Memory) (fr' : Frame Nat),
    wpN fn cuts post μ k n fr m → FLe fr fr' → Reach fn cuts post μ ⟨⟨0, n⟩, fr', [], m⟩ := by
  intro k
  induction k with
  | zero => intro n fr m fr' h; exact absurd h id
  | succ k ih =>
    intro n fr m fr' h hle
    -- reaching the next node
    have hnext : ∀ (n₁ : Node) (f₁ : Frame Nat) (m₁ : Memory) (f₁' : Frame Nat),
        nextP cuts μ (wpN fn cuts post μ k) n₁ f₁ m₁ →
        FLe f₁ f₁' → Reach fn cuts post μ ⟨⟨0, n₁⟩, f₁', [], m₁⟩ := by
      intro n₁ f₁ m₁ f₁' h₁ hle₁
      unfold nextP at h₁
      cases hc : cuts.lookup n₁ with
      | none => rw [hc] at h₁; exact ih n₁ f₁ m₁ f₁' h₁ hle₁
      | some c =>
        rw [hc] at h₁
        exact .inr ⟨n₁, c, f₁', m₁, hc, Cut.holds_mono h₁.1 hle₁,
          by rw [← valsOn_eq h₁.1.1 hle₁]; exact h₁.2, .refl⟩
    have hf := fetch_prog fn n
    simp only [wpN] at h
    cases hi : fn.instr? n with
    | none => simp only [hi, wpI] at h
    | some i =>
      rw [hi] at h hf
      simp only [wpI] at h
      cases i with
      | nop n₁ =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h hle)
      | const d w n₁ =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h (hle.set d w))
      | move d s n₁ =>
        dsimp only at h
        cases hs : fr.get s with
        | none => simp only [hs] at h
        | some x =>
          simp only [hs] at h
          exact Reach.head (by unfold Step; simp [step, hf, hle s x hs, Point.at])
            (hnext _ _ _ _ h (hle.set d x))
      | unary op d s n₁ =>
        dsimp only at h
        cases hs : fr.get s with
        | none => simp only [hs] at h
        | some x =>
          simp only [hs] at h
          exact Reach.head (by unfold Step; simp [step, hf, hle s x hs, Point.at])
            (hnext _ _ _ _ h (hle.set d _))
      | binary op d a b n₁ =>
        dsimp only at h
        cases ha : fr.get a with
        | none => simp only [ha] at h
        | some x =>
          cases hb : fr.get b with
          | none => simp only [ha, hb] at h
          | some y =>
            simp only [ha, hb] at h
            cases hz : op.eval x y with
            | none => simp only [hz] at h
            | some z =>
              simp only [hz] at h
              exact Reach.head (by unfold Step; simp [step, hf, hle a x ha, hle b y hb, hz, Point.at])
                (hnext _ _ _ _ h (hle.set d z))
      | load w e d b off n₁ =>
        dsimp only at h
        cases hb : fr.get b with
        | none => simp only [hb] at h
        | some addr =>
          simp only [hb] at h
          cases hz : m.load w e (addr.toNat + off) with
          | none => simp only [hz] at h
          | some z =>
            simp only [hz] at h
            exact Reach.head (by unfold Step; simp [step, hf, hle b addr hb, hz, Point.at])
              (hnext _ _ _ _ h (hle.set d z))
      | store w b off s n₁ =>
        dsimp only at h
        cases hb : fr.get b with
        | none => simp only [hb] at h
        | some addr =>
          cases hs : fr.get s with
          | none => simp only [hb, hs] at h
          | some x =>
            simp only [hb, hs] at h
            cases hm : m.store w (addr.toNat + off) x with
            | none => simp only [hm] at h
            | some m₁ =>
              simp only [hm] at h
              exact Reach.head (by unfold Step; simp [step, hf, hle b addr hb, hle s x hs, hm, Point.at])
                (hnext _ _ _ _ h hle)
      | call => exact absurd h id
      | cond c n₁ n₂ =>
        dsimp only at h
        cases hc : fr.get c with
        | none => simp only [hc] at h
        | some x =>
          simp only [hc] at h
          by_cases hx : x = 0
          · exact Reach.head (by unfold Step; simp [step, hf, hle c x hc, hx, Point.at])
              (hnext _ _ _ _ (h.1 hx) hle)
          · exact Reach.head (by unfold Step; simp [step, hf, hle c x hc, Point.at]; exact fun h0 => absurd h0 hx)
              (hnext _ _ _ _ (h.2 hx) hle)
      | jump t =>
        exact Reach.head (by unfold Step; simp [step, hf, Point.at]) (hnext _ _ _ _ h hle)
      | ret rs =>
        dsimp only at h
        cases hr : fr.readAll rs with
        | none => simp only [hr] at h
        | some vs =>
          simp only [hr] at h
          exact .inl ⟨_, vs, m, .refl, by simp [step, hf, hle.readAll rs vs hr], h⟩
      | trap => exact absurd h id

theorem lookup_mem : ∀ {cuts : List (Node × Cut)} {n : Node} {c : Cut},
    cuts.lookup n = some c → (n, c) ∈ cuts
  | [], _, _, h => by simp at h
  | (n', c') :: rest, n, c, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      have : n = n' := by simpa [beq_iff_eq] using he
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem behaves_of_steps {p : Prog Nat} {s s' : State Nat} {vs : List Word} {m : Memory}
    (h : Steps p s s') (hb : Behaves p s' (.returned vs m)) : Behaves p s (.returned vs m) := by
  obtain ⟨t, ht, hf⟩ := hb
  exact ⟨t, h.trans ht, hf⟩

/-- From a cut point whose annotation holds, the function returns into the postcondition. -/
theorem from_cut {pre : List Word → Memory → Prop} {K : Nat} (hvc : vc fn cuts post pre K) :
    ∀ (w : Nat) (n : Node) (c : Cut) (fr : Frame Nat) (m : Memory),
      (c.measure (valsOn c.defined fr) m).toNat = w → cuts.lookup n = some c → c.holds fr m →
      ∃ vs m', Behaves (prog fn) ⟨⟨0, n⟩, fr, [], m⟩ (.returned vs m') ∧ post vs m' := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro n c fr m hw hc hh
    have hp := hvc.2 (n, c) (lookup_mem hc) (valsOn c.defined fr) m hh.2
    rcases path _ K n _ m fr hp (canon_le hh.1) with ⟨t, vs, m', ht, hf, hpost⟩ |
        ⟨n', c', fr', m', hc', hh', hb, ht⟩
    · exact ⟨vs, m', ⟨t, ht, hf⟩, hpost⟩
    · simp only [bound] at hb
      have hlt : (c'.measure (valsOn c'.defined fr') m').toNat < w := by
        rw [← hw]; exact (BitVec.lt_def).mp hb
      obtain ⟨vs, m'', hbeh, hpost⟩ := ih _ hlt n' c' fr' m' rfl hc' hh'
      exact ⟨vs, m'', behaves_of_steps ht hbeh, hpost⟩

/-- **Soundness of the RTL VC generator.** If `vc` holds, the function entered at its entry
with every parameter register written and the precondition true of their values returns,
with values and memory satisfying the postcondition. -/
theorem sound {pre : List Word → Memory → Prop} {K : Nat} (hvc : vc fn cuts post pre K)
    (fr : Frame Nat) (m : Memory) (hdef : ∀ r ∈ fn.params, (fr.get r).isSome)
    (hpre : pre (fn.params.map (valsOn fn.params fr)) m) :
    ∃ vs m', Behaves (prog fn) ⟨⟨0, fn.entry⟩, fr, [], m⟩ (.returned vs m') ∧ post vs m' := by
  have hp := hvc.1 (valsOn fn.params fr) m hpre
  rcases path _ K fn.entry _ m fr hp (canon_le hdef) with ⟨t, vs, m', ht, hf, hpost⟩ |
      ⟨n', c', fr', m', hc', hh', _, ht⟩
  · exact ⟨vs, m', ⟨t, ht, hf⟩, hpost⟩
  · obtain ⟨vs, m'', hbeh, hpost⟩ := from_cut hvc _ n' c' fr' m' rfl hc' hh'
    exact ⟨vs, m'', behaves_of_steps ht hbeh, hpost⟩

end Silmaril.Machine.CBackend.RTL.VC
