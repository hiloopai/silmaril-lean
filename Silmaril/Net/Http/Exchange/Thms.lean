module

public import Silmaril.Net.Http.Exchange.Defs
public import Silmaril.Net.Http.Message.Thms

@[expose] public section

/-!
# HTTP exchanges and origin semantics: theorems

PROVED (standard axioms):

* **web origins** (`Origin.ofTargets W`): respect safe and idempotent methods
  (`ofTargets_respectsSafe`, `ofTargets_respectsIdempotent`), answer `HEAD` as `GET` without
  content (`ofTargets_headLikeGet`), and have valid responses when the web does
  (`ofTargets_validResponses`);
* **the resource store** (`storeOrigin`): `storeOrigin_respectsSafe`,
  `storeOrigin_respectsIdempotent` (`PUT` and `DELETE` repeated leave the state of the first),
  `storeOrigin_headLikeGet`, `storeOrigin_validResponses`; `storeOrigin_get_after_put`: a `GET`
  after a `PUT` of a target answers 200 with the content put (§9.3.4: "a successful PUT of a
  given representation would suggest that a subsequent GET on that same target resource will
  result in an equivalent representation being sent in a 200 (OK) response").
-/

namespace Silmaril.Net.Http

open Silmaril.Net.Http.Field

namespace Origin

theorem ofFun_iff {σ : Type} (f : σ → Request → Response × σ) (s : σ) (r : Request)
    (resp : Response) (s' : σ) : ofFun f s r resp s' ↔ f s r = (resp, s') := Iff.rfl

theorem ofTargets_respectsSafe (W : Web) : (ofTargets W).RespectsSafe := by
  intro _ _ _ _ _ _; rfl

theorem ofTargets_respectsIdempotent (W : Web) : (ofTargets W).RespectsIdempotent := by
  intro _ _ _ _ _ _ _ _ _; rfl

theorem withMethod_target (r : Request) (m : Method) : (r.withMethod m).target = r.target := rfl

theorem withMethod_method (r : Request) (m : Method) : (r.withMethod m).method = m := rfl

theorem ofTargets_headLikeGet (W : Web) : (ofTargets W).HeadLikeGet := by
  intro s r resp s' hr
  have hget : webAnswer W (r.withMethod .get) = W r.target := by
    simp [webAnswer, withMethod_method, withMethod_target]
  have hhead : webAnswer W r = (W r.target).stripContent := by simp [webAnswer, hr]
  show (webAnswer W r, ()) = (resp, s') ↔
    ∃ g, (webAnswer W (r.withMethod .get), ()) = (g, s') ∧ resp = g.stripContent
  rw [hget, hhead]
  cases s'
  constructor
  · intro h; cases h; exact ⟨_, rfl, rfl⟩
  · rintro ⟨g, hg, rfl⟩; cases hg; rfl

theorem ofTargets_validResponses (W : Web) (hW : ∀ t, (W t).isValid = true) :
    (ofTargets W).ValidResponses := by
  intro s r resp s' h
  simp only [ofTargets, ofFun, Prod.mk.injEq] at h
  rw [← h.1]
  unfold webAnswer
  split
  · exact Response.isValid_stripContent (hW _)
  · exact hW _

end Origin

/-! ## The resource store -/

theorem Store.update_self (S : Store) (t : Target) (v : Option (List UInt8)) :
    (S.update t v).update t v = S.update t v := by
  funext t'; simp only [Store.update]; split <;> rfl

theorem Store.update_eq_of (S : Store) (t : Target) (h : S t = none) : S.update t none = S := by
  funext t'; simp only [Store.update]; split <;> simp_all

theorem Store.update_apply (S : Store) (t : Target) (v : Option (List UInt8)) :
    S.update t v t = v := by simp [Store.update]

theorem storeStep_snd_safe (S : Store) (r : Request) (h : r.method.isSafe = true) :
    (storeStep S r).2 = S := by
  unfold storeStep
  cases hm : r.method <;> simp_all [Method.isSafe]

theorem storeOrigin_respectsSafe : storeOrigin.RespectsSafe := by
  intro S r resp S' hs h
  have hS : S' = (storeStep S r).2 := by rw [show storeStep S r = (resp, S') from h]
  rw [hS, storeStep_snd_safe S r hs]

theorem storeStep_snd_idem (S : Store) (r : Request) (h : r.method.isIdempotent = true) :
    (storeStep (storeStep S r).2 r).2 = (storeStep S r).2 := by
  cases hm : r.method with
  | put => simp only [storeStep, hm]; exact Store.update_self _ _ _
  | delete =>
    cases hS : S r.target with
    | none => simp [storeStep, hm, hS]
    | some c => simp [storeStep, hm, hS, Store.update_apply]
  | _ =>
    have hsafe : r.method.isSafe = true := by
      rw [hm] at h ⊢; simpa [Method.isIdempotent] using h
    rw [storeStep_snd_safe S r hsafe, storeStep_snd_safe S r hsafe]

theorem storeOrigin_respectsIdempotent : storeOrigin.RespectsIdempotent := by
  intro S r resp₁ S₁ resp₂ S₂ hi h₁ h₂
  have hS₁ : S₁ = (storeStep S r).2 := by rw [show storeStep S r = (resp₁, S₁) from h₁]
  have hS₂ : S₂ = (storeStep S₁ r).2 := by rw [show storeStep S₁ r = (resp₂, S₂) from h₂]
  rw [hS₂, hS₁, storeStep_snd_idem S r hi]

theorem storeOrigin_headLikeGet : storeOrigin.HeadLikeGet := by
  intro S r resp S' hr
  have hhead : storeStep S r = ((S.get r.target).stripContent, S) := by
    simp only [storeStep, hr]
  have hget : storeStep S (r.withMethod .get) = (S.get r.target, S) := rfl
  show storeStep S r = (resp, S') ↔
    ∃ g, storeStep S (r.withMethod .get) = (g, S') ∧ resp = g.stripContent
  rw [hhead, hget]
  constructor
  · intro h; cases h; exact ⟨_, rfl, rfl⟩
  · rintro ⟨g, hg, rfl⟩; cases hg; rfl

theorem allowLine_valid : allowLine.isValid = true := by decide

theorem simple_valid (s : Status) (hs : Status.isValid s = true) (c : List UInt8)
    (hc : Status.allowsContent s = true ∨ c = []) :
    Response.isValid (Response.simple s c) = true := by
  rcases hc with hc | rfl
  · simp [Response.isValid, Response.simple, Message.fieldsValid, Response.status, hs, hc,
      Section.isValid]
  · simp [Response.isValid, Response.simple, Message.fieldsValid, Response.status, hs,
      Section.isValid]

theorem allow_valid (s : Status) (hs : Status.isValid s = true) :
    Response.isValid ⟨s, [allowLine], [], []⟩ = true := by
  simp [Response.isValid, Message.fieldsValid, Response.status, hs, Section.isValid,
    allowLine_valid]

theorem putStatus_valid (b : Bool) :
    Status.isValid (if b then Status.noContent else Status.created) = true := by
  cases b <;> decide

theorem Store.get_valid (S : Store) (t : Target) : (S.get t).isValid = true := by
  unfold Store.get
  split
  · exact simple_valid _ (by decide) _ (Or.inl (by decide))
  · exact simple_valid _ (by decide) _ (Or.inr rfl)

theorem storeStep_fst_valid (S : Store) (r : Request) :
    Response.isValid (storeStep S r).1 = true := by
  unfold storeStep
  cases r.method with
  | get => exact Store.get_valid _ _
  | head => exact Response.isValid_stripContent (Store.get_valid _ _)
  | put => exact simple_valid _ (putStatus_valid _) [] (Or.inr rfl)
  | delete =>
    cases S r.target with
    | some _ => exact simple_valid Status.noContent (by decide) [] (Or.inr rfl)
    | none => exact simple_valid Status.notFound (by decide) [] (Or.inr rfl)
  | other _ => exact simple_valid Status.notImplemented (by decide) [] (Or.inr rfl)
  | options => exact allow_valid Status.noContent (by decide)
  | _ => exact allow_valid Status.methodNotAllowed (by decide)

theorem storeOrigin_validResponses : storeOrigin.ValidResponses := by
  intro S r resp S' h
  have hr : resp = (storeStep S r).1 := by rw [show storeStep S r = (resp, S') from h]
  rw [hr]
  exact storeStep_fst_valid S r

/-- A `GET` after a `PUT` of the same target answers 200 with the content put (§9.3.4). -/
theorem storeOrigin_get_after_put (S : Store) (r : Request) (hr : r.method = .put) :
    (storeStep (storeStep S r).2 (r.withMethod .get)).1 =
      Response.simple Status.ok r.content := by
  have hget : (r.withMethod .get).method = .get := rfl
  simp [storeStep, hr, hget, Origin.withMethod_target, Store.get, Store.update_apply]

end Silmaril.Net.Http
