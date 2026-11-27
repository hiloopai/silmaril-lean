module

public import Silmaril.Semantics.SQLite.Isolation.Api.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms

public section

namespace Silmaril.Proofs.Semantics.SQLite.Isolation.Api

open Silmaril.Elgot
open Silmaril.SQLite.Isolation.Api

private theorem ret_bind {A B : Type} (a : A) (k : A → ApiTree B) :
    (ITree.ret a >>= k) = k a :=
  pure_bind a k

theorem treeAvoidsBad_ret {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeAvoidsBad profile (ITree.ret a) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ => trivial
  | request e =>
    rcases hp with ⟨k, hk⟩
    rw [ITree.out_ret] at hk
    cases Part.some_inj.mp hk
  | exchange e r tail =>
    rcases hp with ⟨k, hk, _⟩
    rw [ITree.out_ret] at hk
    cases Part.some_inj.mp hk

theorem treeAvoidsBad_diverge {A : Type} (profile : AuthorityProfile) :
    TreeAvoidsBad profile (ITree.diverge : ApiTree A) := by
  intro p hp
  rw [(ITree.hasTrace_diverge_iff p).mp hp]
  trivial

theorem treeAvoidsBad_vis {R A : Type} {profile : AuthorityProfile}
    {e : ApiEvent R} {k : R → ApiTree A}
    (he : ¬ BadEvent profile ⟨R, e⟩)
    (hk : ∀ r, TreeAvoidsBad profile (k r)) :
    TreeAvoidsBad profile (ITree.vis e k) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ =>
    rw [ITree.HasTrace, ITree.out_vis] at hp
    cases Part.some_inj.mp hp
  | request d =>
    obtain ⟨hR, hd⟩ := (ITree.hasTrace_vis_request_iff e k d).mp hp
    cases hR
    cases hd
    exact he
  | exchange d r tail =>
    obtain ⟨hR, hd, htail⟩ := (ITree.hasTrace_vis_exchange e k d r tail).mp hp
    cases hR
    cases hd
    exact ⟨he, hk r tail htail⟩

theorem treeAvoidsBad_bind {A B : Type} {profile : AuthorityProfile}
    {t : ApiTree A} {k : A → ApiTree B}
    (ht : TreeAvoidsBad profile t)
    (hk : ∀ a, TreeAvoidsBad profile (k a)) :
    TreeAvoidsBad profile (t >>= k) := by
  intro p
  induction p generalizing t with
  | «prefix» =>
    intro _
    trivial
  | result _ =>
    intro _
    trivial
  | request d =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · simp [ITree.diverge_bind] at hp
    · rw [ret_bind] at hp
      exact hk a (.request d) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he⟩ := (ITree.hasTrace_vis_request_iff e _ d).mp hp
      cases hR
      cases he
      exact ht (.request d) (ITree.hasTrace_vis_request d next)
  | exchange d r tail ih =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · simp [ITree.diverge_bind] at hp
    · rw [ret_bind] at hp
      exact hk a (.exchange d r tail) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he, htail⟩ := (ITree.hasTrace_vis_exchange e _ d r tail).mp hp
      cases hR
      cases he
      refine ⟨ht (.request d) (ITree.hasTrace_vis_request d next), ?_⟩
      have hnext : TreeAvoidsBad profile (next r) := fun q hq =>
        (ht (.exchange d r q) ((ITree.hasTrace_vis_exchange_iff d next r q).mpr hq)).2
      exact ih hnext htail

theorem handledTreeAvoidsBad_vis {S R A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {e : ApiEvent R} {k : R → ApiTree A}
    (he : ¬ BadEvent profile ⟨R, e⟩)
    (hk : ∀ r s', step ⟨R, e⟩ s r s' → HandledTreeAvoidsBad profile step s' (k r)) :
    HandledTreeAvoidsBad profile step s (ITree.vis e k) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ =>
    have h1 := hp.1
    rw [ITree.HasTrace, ITree.out_vis] at h1
    cases Part.some_inj.mp h1
  | request d =>
    obtain ⟨hR, hd⟩ := (ITree.hasTrace_vis_request_iff e k d).mp hp.1
    cases hR
    cases hd
    exact he
  | exchange d r tail =>
    obtain ⟨hR, hd, htail⟩ := (ITree.hasTrace_vis_exchange e k d r tail).mp hp.1
    cases hR
    cases hd
    rcases hp.2 with ⟨s', hstep, hrep⟩
    exact ⟨he, hk r s' hstep tail ⟨htail, hrep⟩⟩

theorem handledTreeAvoidsBad_bind {S A B : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t : ApiTree A} {k : A → ApiTree B}
    (ht : HandledTreeAvoidsBad profile step s t)
    (hk : ∀ y a, ITree.ReturnsTo step s t y a → HandledTreeAvoidsBad profile step y (k a)) :
    HandledTreeAvoidsBad profile step s (t >>= k) := by
  intro p
  induction p generalizing s t with
  | «prefix» =>
    intro _
    trivial
  | result _ =>
    intro _
    trivial
  | request d =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · exact False.elim (by simpa [ITree.diverge_bind, ITree.hasTrace_diverge_iff] using hp.1)
    · rw [ret_bind] at hp
      exact hk s a (.ret s a) (.request d) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he⟩ := (ITree.hasTrace_vis_request_iff e _ d).mp hp.1
      cases hR
      cases he
      exact ht (.request d) ⟨ITree.hasTrace_vis_request d next, trivial⟩
  | exchange d r tail ih =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · exact False.elim (by simpa [ITree.diverge_bind, ITree.hasTrace_diverge_iff] using hp.1)
    · rw [ret_bind] at hp
      exact hk s a (.ret s a) (.exchange d r tail) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he, htail⟩ := (ITree.hasTrace_vis_exchange e _ d r tail).mp hp.1
      cases hR
      cases he
      rcases hp.2 with ⟨mid, hstep, hrep⟩
      refine ⟨ht (.request d) ⟨ITree.hasTrace_vis_request d next, trivial⟩, ?_⟩
      have hnext : HandledTreeAvoidsBad profile step mid (next r) := fun q hq =>
        (ht (.exchange d r q)
          ⟨(ITree.hasTrace_vis_exchange_iff d next r q).mpr hq.1, ⟨mid, hstep, hq.2⟩⟩).2
      exact ih hnext (fun y a hret => hk y a (.exchange hstep hret)) ⟨htail, hrep⟩

/-! ## Arbitrary-tree confinement equations and universal safety -/

theorem confineTree_diverge {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A) :
    confineTree profile onBad ITree.diverge = ITree.diverge := by
  apply ITree.Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [confineTree, Approx.confine, ITree.diverge]

theorem confineTree_ret {A : Type} (profile : AuthorityProfile) (onBad : ApiTree A) (a : A) :
    confineTree profile onBad (ITree.ret a) = ITree.ret a := by
  apply ITree.Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n => simp [confineTree, Approx.confine, ITree.ret]

theorem confineTree_vis {R A : Type} (profile : AuthorityProfile) (onBad : ApiTree A)
    (e : ApiEvent R) (k : R → ApiTree A) :
    confineTree profile onBad (ITree.vis e k) =
      if isBadEvent profile e then onBad
      else ITree.vis e (fun r => confineTree profile onBad (k r)) := by
  apply ITree.Tree.ext
  intro n
  cases n with
  | zero =>
    cases isBadEvent profile e <;> rfl
  | succ n =>
    cases hbad : isBadEvent profile e <;>
      simp [confineTree, Approx.confine, ITree.vis, hbad]

/-- Universal arbitrary-tree confinement: for ANY raw tree `t : ApiTree A` (no
validity, admission, or limit premise) and ANY safe fallback `onBad : ApiTree A`
(whether returning success, an error, cleanup, or diverging), every finite
prefix of `confineTree profile onBad t` avoids `BadEvent profile`. -/
theorem confineTree_avoids_bad {A : Type} (profile : AuthorityProfile)
    {onBad : ApiTree A} (honBad : TreeAvoidsBad profile onBad) (t : ApiTree A) :
    TreeAvoidsBad profile (confineTree profile onBad t) := by
  intro p
  induction p generalizing t with
  | «prefix» =>
    intro _
    trivial
  | result _ =>
    intro _
    trivial
  | request d =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [confineTree_diverge] at hp
      exact treeAvoidsBad_diverge profile (.request d) hp
    · rw [confineTree_ret] at hp
      exact treeAvoidsBad_ret profile a (.request d) hp
    · rw [confineTree_vis] at hp
      cases hbad : isBadEvent profile e
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hp
        obtain ⟨hR, hd⟩ := (ITree.hasTrace_vis_request_iff e _ d).mp hp
        cases hR
        cases hd
        simp [TraceAvoidsBad, BadEvent, hbad]
      · simp only [hbad, ↓reduceIte] at hp
        exact honBad (.request d) hp
  | exchange d r tail ih =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [confineTree_diverge] at hp
      exact treeAvoidsBad_diverge profile (.exchange d r tail) hp
    · rw [confineTree_ret] at hp
      exact treeAvoidsBad_ret profile a (.exchange d r tail) hp
    · rw [confineTree_vis] at hp
      cases hbad : isBadEvent profile e
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at hp
        obtain ⟨hR, hd, htail⟩ := (ITree.hasTrace_vis_exchange e _ d r tail).mp hp
        cases hR
        cases hd
        exact ⟨by simp [BadEvent, hbad], ih (k r) htail⟩
      · simp only [hbad, ↓reduceIte] at hp
        exact honBad (.exchange d r tail) hp

/-! ## Replay, host-exchange exclusion, and protected-state preservation -/

theorem replayTo_iff_replay {S A : Type} (step : ApiHandler S) (s : S) (p : ApiTrace A) :
    (∃ s', ReplayTo step s p s') ↔ ITree.Replay step s p := by
  induction p generalizing s with
  | «prefix» =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | request _ =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | result _ =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | exchange e r tail ih =>
    constructor
    · rintro ⟨s', mid, hstep, htail⟩
      exact ⟨mid, hstep, (ih mid).mp ⟨s', htail⟩⟩
    · rintro ⟨mid, hstep, hrep⟩
      obtain ⟨s', htail⟩ := (ih mid).mpr hrep
      exact ⟨s', mid, hstep, htail⟩

theorem replay_excludes_bad_exchanges {S A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} (hexcl : HandlerExcludesBad profile step)
    {s : S} {p : ApiTrace A} (hrep : ITree.Replay step s p) :
    ExchangesAvoidBad profile p := by
  induction p generalizing s with
  | «prefix» => trivial
  | request _ => trivial
  | result _ => trivial
  | exchange e r tail ih =>
    rcases hrep with ⟨mid, hstep, htail⟩
    exact ⟨hexcl ⟨_, e⟩ s mid r hstep, ih htail⟩

theorem exchangesAvoidBad_replayTo_preserves_protected {S P A : Type}
    {profile : AuthorityProfile} {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {p : ApiTrace A}
    (hsafe : ExchangesAvoidBad profile p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s := by
  induction p generalizing s with
  | «prefix» => cases hrep; rfl
  | request _ => cases hrep; rfl
  | result _ => cases hrep; rfl
  | exchange e r tail ih =>
    rcases hsafe with ⟨he, htailSafe⟩
    rcases hrep with ⟨mid, hstep, htailRep⟩
    exact (ih htailSafe htailRep).trans (hframe ⟨_, e⟩ s mid r he hstep)

theorem traceAvoidsBad_to_exchangesAvoidBad {A : Type} {profile : AuthorityProfile}
    {p : ApiTrace A} (h : TraceAvoidsBad profile p) :
    ExchangesAvoidBad profile p := by
  induction p with
  | «prefix» => trivial
  | request _ => trivial
  | result _ => trivial
  | exchange _ _ _ ih => exact ⟨h.1, ih h.2⟩

theorem handled_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : HandledTreeAvoidsBad profile step s t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  exchangesAvoidBad_replayTo_preserves_protected hframe
    (traceAvoidsBad_to_exchangesAvoidBad
      (hsafe p ⟨htrace, (replayTo_iff_replay step s p).mp ⟨s', hrep⟩⟩))
    hrep

theorem handled_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : HandledTreeAvoidsBad profile step s t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s := by
  induction hret with
  | ret _ _ => rfl
  | @exchange R e k r x y z a hstep hrest ih =>
    have he : ¬ BadEvent profile ⟨R, e⟩ :=
      hsafe (.request e) ⟨ITree.hasTrace_vis_request e k, trivial⟩
    have hnext : HandledTreeAvoidsBad profile step y (k r) := fun q hq =>
      (hsafe (.exchange e r q)
        ⟨(ITree.hasTrace_vis_exchange_iff e k r q).mpr hq.1, ⟨y, hstep, hq.2⟩⟩).2
    exact (ih hnext).trans (hframe ⟨R, e⟩ x y r he hstep)

/-! ## Worked session and reference handler witnesses -/

theorem openReadCloseSession_avoids_bad (db : DbId) (input : QueryInput) :
    TreeAvoidsBad (readOnlyProfile db) (openReadCloseSession db input) := by
  unfold openReadCloseSession
  apply treeAvoidsBad_bind
  · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent, readOnlyProfile])
      (fun _ => treeAvoidsBad_ret _ _)
  · intro openRes
    cases openRes with
    | error _ => exact treeAvoidsBad_ret _ _
    | ok conn =>
      apply treeAvoidsBad_bind
      · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent, readOnlyProfile])
          (fun _ => treeAvoidsBad_ret _ _)
      · intro prepRes
        cases prepRes with
        | error _ =>
          apply treeAvoidsBad_bind
          · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent])
              (fun _ => treeAvoidsBad_ret _ _)
          · intro _
            exact treeAvoidsBad_ret _ _
        | ok stmt =>
          apply treeAvoidsBad_bind
          · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent, readOnlyProfile])
              (fun _ => treeAvoidsBad_ret _ _)
          · intro stepRes
            apply treeAvoidsBad_bind
            · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent])
                (fun _ => treeAvoidsBad_ret _ _)
            · intro _
              apply treeAvoidsBad_bind
              · exact treeAvoidsBad_vis (by simp [BadEvent, isBadEvent])
                  (fun _ => treeAvoidsBad_ret _ _)
              · intro _
                cases stepRes with
                | error _ => exact treeAvoidsBad_ret _ _
                | ok outcome =>
                  cases outcome <;> exact treeAvoidsBad_ret _ _

theorem readOnlyReferenceHandler_excludesBad (db : DbId) :
    HandlerExcludesBad (readOnlyProfile db) (readOnlyReferenceHandler db) := by
  intro q s s' r hstep
  rcases q with ⟨R, e⟩
  cases e with
  | openDb target mode =>
    cases mode with
    | readOnly =>
      rcases hstep with ⟨rfl, _⟩
      simp [BadEvent, isBadEvent, readOnlyProfile]
    | readWrite => exact False.elim hstep
  | prepare conn target input =>
    rcases hstep with ⟨rfl, _⟩
    simp [BadEvent, isBadEvent, readOnlyProfile]
  | stepRead stmt target =>
    rcases hstep with ⟨rfl, _⟩
    simp [BadEvent, isBadEvent, readOnlyProfile]
  | finalize stmt =>
    simp [BadEvent, isBadEvent]
  | closeDb conn =>
    simp [BadEvent, isBadEvent]
  | writeDb _ _ _ _ => exact False.elim hstep
  | attachDb _ _ _ => exact False.elim hstep
  | loadExtension _ _ => exact False.elim hstep
  | hostEffect _ => exact False.elim hstep

theorem readOnlyReferenceHandler_frameContract (db : DbId) :
    FrameContract (readOnlyProfile db) (readOnlyReferenceHandler db) ReferenceState.protectedDb := by
  intro q s s' r _ hstep
  rcases q with ⟨R, e⟩
  cases e with
  | openDb target mode =>
    cases mode with
    | readOnly =>
      rcases hstep with ⟨_, hbody⟩
      cases r with
      | error _ => simp only at hbody; rw [hbody]
      | ok _ => rcases hbody with ⟨_, _, rfl⟩; rfl
    | readWrite => exact False.elim hstep
  | prepare conn target input =>
    rcases hstep with ⟨_, hbody⟩
    cases r with
    | error _ => simp only at hbody; rw [hbody]
    | ok _ => rcases hbody with ⟨_, _, _, rfl⟩; rfl
  | stepRead stmt target =>
    rcases hstep with ⟨_, hbody⟩
    cases r with
    | error _ => simp only at hbody; rw [hbody]
    | ok _ => rcases hbody with ⟨_, rfl⟩; rfl
  | finalize stmt =>
    cases r with
    | error _ => simp [readOnlyReferenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, rfl⟩; rfl
  | closeDb conn =>
    cases r with
    | error _ => simp [readOnlyReferenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, rfl⟩; rfl
  | writeDb _ _ _ _ => exact False.elim hstep
  | attachDb _ _ _ => exact False.elim hstep
  | loadExtension _ _ => exact False.elim hstep
  | hostEffect _ => exact False.elim hstep

end Silmaril.Proofs.Semantics.SQLite.Isolation.Api
