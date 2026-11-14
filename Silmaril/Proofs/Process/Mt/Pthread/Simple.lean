module

public import Silmaril.Process.Mt.Pthread.Simple.Defs

/-!
# The full model refines the simple pthread model (proofs)

`sim`: under the linearization obligations `Impl.Lin`, every step of the full model (from a
configuration whose abstraction has no undefined behaviour) is matched by no step of the simple
model (entering a call, code before or after its linearization point, leaving a call) or by
one (a client instruction, the linearization point of a call, output, return, create).
`refines` iterates it.
-/

@[expose] public section

namespace Silmaril.Proofs.Process.Mt.Pthread.Simple

open Silmaril.Process.Mt.Csl
open Silmaril.Process.Mt.Pthread
open Silmaril.Process.Mt.Pthread.Simple

variable {ι : Type} {P : Prog} {I : Impl ι}

theorem plain_mem {s s' : TSt} {m m' : SM} (h : Simple.plain P s m s' m') :
    m'.ps = m.ps ∧ m'.out = m.out := by
  unfold Simple.plain at h
  split at h <;> (try simp_all) <;> (obtain ⟨-, rfl⟩ := h; simp)

theorem cfg_eq {C D : Cfg (tisa P)} (e1 : C.th = D.th) (e2 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp only at e1 e2; subst e1; subst e2; rfl

theorem step_of_eq {C D D' : Cfg (tisa P)} (h : Step (tisa P) C D) (e : D = D') :
    Step (tisa P) C D' := e ▸ h

theorem absC_th (c : CCfg I.St ι) {t : Nat} {x : CT I.St} (h : c.th t = some x) :
    (absC P I c).th t = some (absT P I x) := by
  simp [absC, h] <;> rfl

/-- The abstraction of a configuration with thread `t` replaced. -/
theorem absC_upd (c c' : CCfg I.St ι) (t : Nat) (x : CT I.St) (h : c'.th = c.set I t x) :
    (absC P I c').th = Heap.upd (absC P I c).th t (some (absT P I x)) := by
  funext u
  by_cases e : u = t
  · subst e; simp [absC, CCfg.set, Heap.upd, h] <;> rfl
  · simp [absC, CCfg.set, Heap.upd, e, h] <;> rfl

theorem upd_same {α : Type} (f : Nat → Option α) (t : Nat) (x : α) (h : f t = some x) :
    Heap.upd f t (some x) = f := by
  funext u; by_cases e : u = t
  · subst e; simp [Heap.upd, h]
  · simp [Heap.upd, e]

/-- **The simulation.** -/
theorem sim (hl : I.Lin) {c c' : CCfg I.St ι} (hf : ¬ Fault (tisa P) (absC P I c))
    (hs : CStep P I c c') :
    absC P I c' = absC P I c ∨ Step (tisa P) (absC P I c) (absC P I c') := by
  cases hs with
  | @plain t s s' m' h hp =>
    right
    obtain ⟨e1, e2⟩ := plain_mem hp
    refine step_of_eq (Step.loc (U := tisa P) (C := absC P I c) (t := t) (s := s) (s' := s')
      (m' := m') (absC_th c h) hp) (cfg_eq ?_ ?_)
    · exact (absC_upd (P := P) c _ t ⟨s', none⟩ rfl).symm
    · rcases m' with ⟨cl, ps, o⟩
      simp only [absM] at e1 e2
      simp [absC, absM, e1, e2]
  | @enter t s o args h hc =>
    left
    refine cfg_eq ?_ rfl
    rw [absC_upd (P := P) c _ t _ (by rfl)]
    have : absT P I ⟨s, some (I.start o args)⟩ = absT P I ⟨s, none⟩ := by
      simp [absT, hl.start]
    rw [this]; exact upd_same _ _ _ (absC_th c h)
  | @code t s q o args q' x' h hc hs =>
    cases hq : I.lin q with
    | none =>
      have hnf : ¬ (o.spec).fault t args (I.β c.obj) := by
        intro e
        refine hf ⟨t, s, ?_, Or.inr (Or.inl ⟨o, args, hc, e⟩)⟩
        rw [absC_th c h]; simp [absT, hq] <;> rfl
      rcases hl.pre t o args q c.obj q' x' hs hq hnf with ⟨hb, hq'⟩ | ⟨r, hsp, hq'⟩
      · left
        refine cfg_eq ?_ (by simp [absC, absM, hb])
        rw [absC_upd (P := P) c _ t _ (by rfl)]
        have : absT P I ⟨s, some q'⟩ = absT P I ⟨s, none⟩ := by simp [absT, hq']
        rw [this]
        have h2 : (absC P I c).th t = some (absT P I ⟨s, none⟩) := by
          rw [absC_th c h]; simp [absT, hq] <;> rfl
        exact upd_same _ _ _ h2
      · right
        have h2 : (absC P I c).th t = some s := by rw [absC_th c h]; simp [absT, hq] <;> rfl
        refine step_of_eq (Step.atom (U := tisa P) (C := absC P I c) (t := t) (s := s)
          (s' := resume P s r) (m' := { absM I c with ps := I.β x' }) h2
          (Or.inl ⟨o, args, r, hc, ⟨I.β x', hsp, rfl⟩, rfl⟩)) (cfg_eq ?_ (by simp [absC, absM]))
        rw [absC_upd (P := P) c ⟨c.set I t ⟨s, some q'⟩, c.cells, x', c.out⟩ t ⟨s, some q'⟩ rfl]
        simp [absT, hq']
    | some r =>
      left
      obtain ⟨hb, hq'⟩ := hl.post t o args q c.obj q' x' r hs hq
      refine cfg_eq ?_ (by simp [absC, absM, hb])
      rw [absC_upd (P := P) c _ t _ (by rfl)]
      have : absT P I ⟨s, some q'⟩ = absT P I ⟨s, some q⟩ := by simp [absT, hq, hq']
      rw [this]; exact upd_same _ _ _ (absC_th c h)
  | @leave t s q r h hr =>
    left
    have hq := hl.ret q r hr
    refine cfg_eq ?_ rfl
    rw [absC_upd (P := P) c _ t _ (by rfl)]
    have : absT P I ⟨resume P s r, none⟩ = absT P I ⟨s, some q⟩ := by simp [absT, hq]
    rw [this]; exact upd_same _ _ _ (absC_th c h)
  | @out t s r h hfe =>
    right
    refine step_of_eq (Step.atom (U := tisa P) (C := absC P I c) (t := t) (s := s)
      (s' := s.next s.regs) (m' := { absM I c with out := c.out ++ [s.regs r] }) (absC_th c h)
      (Or.inr (Or.inl ⟨r, hfe, rfl, rfl⟩))) (cfg_eq ?_ (by simp [absC, absM]))
    refine (absC_upd (P := P) c _ t ⟨s.next s.regs, none⟩ ?_).symm; rfl
  | @ret t s r x' h hfe he =>
    right
    have hnf : ¬ Silmaril.Process.Mt.Pthread.exit.fault t [s.regs r] (I.β c.obj) := by
      intro e
      exact hf ⟨t, s, absC_th c h, Or.inr (Or.inr (Or.inl ⟨r, hfe, e⟩))⟩
    refine step_of_eq (Step.atom (U := tisa P) (C := absC P I c) (t := t) (s := s)
      (s' := { s with fin := true }) (m' := { absM I c with ps := I.β x' }) (absC_th c h)
      (Or.inr (Or.inr ⟨r, I.β x', hfe, hl.exit t _ _ _ he hnf, rfl, rfl⟩)))
      (cfg_eq ?_ (by simp [absC, absM]))
    refine (absC_upd (P := P) c _ t ⟨{ s with fin := true }, none⟩ ?_).symm; rfl
  | @create t s f a d u x' h hfe hu hc =>
    right
    refine step_of_eq (Step.spawn (U := tisa P) (C := absC P I c) (t := t) (u := u) (s := s)
      (s₁ := s.next (setReg s.regs d u))
      (s₂ := { fn := f, pc := 0, regs := fun r => if r = 0 then a.val s.regs else 0 })
      (m' := { absM I c with ps := I.β x' }) (absC_th c h) (by simp [absC, hu] <;> rfl)
      ⟨f, a, d, I.β x', hfe, hl.create u c.obj x' hc, rfl, rfl, rfl⟩)
      (cfg_eq ?_ (by simp [absC, absM]))
    funext v
    by_cases e : v = u
    · subst e; simp [absC, CCfg.set, Heap.upd] <;> rfl
    · by_cases e' : v = t
      · subst e'; simp [absC, CCfg.set, Heap.upd, e] <;> rfl
      · simp [absC, CCfg.set, Heap.upd, e, e']

/-- Runs of the full model stand for runs of the simple model. -/
theorem reach_abs (hl : I.Lin) {c₀ c : CCfg I.St ι} (r : Star (Impl.model P I).step c₀ c) :
    Reach (tisa P) (absC P I c₀) (absC P I c) := by
  induction r with
  | refl => exact Star.refl
  | step hab _ ih =>
    rcases sim hl hab.1 hab.2 with e | st
    · rw [e] at ih; exact ih
    · exact Star.step st ih

/-- **The full model refines the simple model**, given the linearization obligations. -/
theorem refines (hl : I.Lin) : Refines (Impl.model P I) := by
  intro c₀ c h₀ r
  refine ⟨absC P I c, ?_, rfl, id⟩
  have := reach_abs hl r
  rw [← show start P = absC P I c₀ from h₀] at this
  exact this

theorem fp_of_wr {s : TSt} {m : SM} {a : Nat} (h : wr P s a) : Simple.fp P s m a := by
  unfold wr at h; unfold Simple.fp
  split at h
  · rename_i e; rw [e]; exact h
  · exact h.elim

theorem raceFree_of_csl (h : ∀ C, Reach (tisa P) (start P) C → ¬ Race (tisa P) C) :
    RaceFree P := by
  rintro C r ⟨t, u, s, s', a, hne, ht, hu, hw, hf⟩
  exact h C r ⟨t, u, s, s', a, hne, ht, hu, fp_of_wr (m := C.mem) hw, hf⟩

end Silmaril.Proofs.Process.Mt.Pthread.Simple
