module

public import Silmaril.Proofs.Wasm.Resource.ExternClient.Inv

/-!
# The `externref` client invariant: threads

`UClientIn U S₀ R G fs ia iu if_` collects what the checker establishes about the instantiated
store `S₀`: the reachable functions `R` are closed for calls (`CallPl`, the calls of the three
imports as bad steps), pass the client check without handle pairs and have no dynamic call; they
contain the exports and avoid the three imports. The guard set `G` contains `R` and the host
functions of the imports, and no other Wasm function; those hosts have the arities of their
imports.

* `InvU L c`: the reachability invariant at `G`, `Tight R` (call targets in `R`), sound facts and
  the check of the code, for the live list `L`; `invU_store`: any store holding references into
  `G` (`okA_gl`).
* `GuardedU L c`: a thread stopped at a call of one of the three imports, whose argument is live
  (a use; a free), prepared for every answer in every store keeping the instance.
* **`step_invU`**: one host-free step (every profile) of an invariant thread, in a store keeping
  the instance, leads to an invariant or a guarded thread.
* `guardedU_decompose`: a guarded thread is at the callout of its import.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
  Silmaril.Wasm.Resource.ExternExamples
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn PlOK PlainOK CallPl BadStep FuncsClosed
  Avoids refFuncs isHost callPl_plainOK hostIn_noHost decompose_fill)

/-- **What the checker establishes** about the instantiated store `S₀` of the untyped
instance `U`. -/
structure UClientIn (U : UInstance) (S₀ : Store Nat) (R G : Nat → Prop) (fs : List Nat)
    (ia iu if_ : Nat) : Prop where
  sub : ∀ a, R a → G a
  bad : ∀ a, isBadC S₀ ia iu if_ a = true → G a
  wasm : ∀ a fi code, G a → S₀.funcs[a]? = some fi → fi.code = .wasm code → R a
  closed : FuncsClosed R fs (CallPl R (isBadC S₀ ia iu if_) fs) S₀.funcs
  bodies : BodiesC R (cfgU S₀ fs ia iu if_) S₀.funcs
  nd : ∀ a fi code, R a → S₀.funcs[a]? = some fi → fi.code = .wasm code →
    noDynL code.body = true
  exports : ∀ x, R (U.addr x)
  avA : Avoids R S₀.funcs ia
  avU : Avoids R S₀.funcs iu
  avF : Avoids R S₀.funcs if_
  dAU : ia ≠ iu
  dAF : ia ≠ if_
  dUF : iu ≠ if_
  hostTy : ∀ a fi, isBadC S₀ ia iu if_ a = true → S₀.funcs[a]? = some fi →
    ∃ ps rs, Expand fi.type (.func ps rs) ∧ (isHost S₀ ia a = true → ps.length = 0) ∧
      (isHost S₀ ia a = false → ps.length = 1)

section
variable {U : UInstance} {S₀ : Store Nat} {R G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}

/-- **The client invariant of a running thread** for the live list `L`. -/
def InvU (S₀ : Store Nat) (R G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat) (L : List Val)
    (c : Config Nat) : Prop :=
  CfgIn G fs (CallPl R (isBadC S₀ ia iu if_) fs) c ∧ Tight R true False c.code ∧
    ∃ F, SoundF (cfgU S₀ fs ia iu if_).ps L c.store.globals c.frame.locals F ∧
      okA (cfgU S₀ fs ia iu if_) L c.store.globals c.frame.module.globals c.frame.locals
        ⟨F, .other, true⟩ c.code

/-- **A thread stopped at a call of one of the three imports**, prepared for every answer in
every store keeping the instance. -/
def GuardedU (S₀ : Store Nat) (R G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (L : List Val) (c : Config Nat) : Prop :=
  ∃ (E : Ctx) (args : List Val) (b : Nat) (d : DefType), isBadC S₀ ia iu if_ b = true ∧
    c.code = E.fill (vals args ++ [.ref (.func b), .callRefType d]) ∧
    (isHost S₀ iu b = true → ∃ v, args = [v] ∧ v ∈ L ∧ ∀ s' r, Keeps S₀ G s' → RefsOK G r →
      InvU S₀ R G fs ia iu if_ L ⟨s', c.frame, E.fill r.toAdmin⟩) ∧
    (isHost S₀ if_ b = true → ∃ v, args = [v] ∧ v ∈ L ∧ ∀ s' r, Keeps S₀ G s' → RefsOK G r →
      InvU S₀ R G fs ia iu if_ (L.erase v) ⟨s', c.frame, E.fill r.toAdmin⟩) ∧
    (isHost S₀ ia b = true → args = [] ∧
      (∀ s' h, h ∉ L → Keeps S₀ G s' → RefsOK G (.values [h]) →
        InvU S₀ R G fs ia iu if_ (h :: L) ⟨s', c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
      (∀ s' r, Keeps S₀ G s' → RefsOK G r → (∀ ws, r ≠ .values ws) →
        InvU S₀ R G fs ia iu if_ L ⟨s', c.frame, E.fill r.toAdmin⟩))

/-! ## Stores keeping the instance -/

theorem sigma_nil {L : List Val} {gl : List GlobalInst} :
    Sigma (cfgU S₀ fs ia iu if_).ps L gl := fun p hp => by simp [cfgU, cfgOf] at hp

theorem closedG (hK : UClientIn U S₀ R G fs ia iu if_) {s : Store Nat} (hk : Keeps S₀ G s) :
    FuncsClosed G fs (CallPl R (isBadC S₀ ia iu if_) fs) s.funcs := by
  intro a fi code ha hf hcode
  have hf' : S₀.funcs[a]? = some fi := by rw [← hk.1 a ha]; exact hf
  exact hK.closed a fi code (hK.wasm a fi code ha hf' hcode) hf' hcode

theorem bodiesG (hK : UClientIn U S₀ R G fs ia iu if_) {s : Store Nat} (hk : Keeps S₀ G s) :
    BodiesC G (cfgU S₀ fs ia iu if_) s.funcs := by
  intro a fi code ha hf hcode
  have hf' : S₀.funcs[a]? = some fi := by rw [← hk.1 a ha]; exact hf
  exact hK.bodies a fi code (hK.wasm a fi code ha hf' hcode) hf' hcode

theorem ndG (hK : UClientIn U S₀ R G fs ia iu if_) {s : Store Nat} (hk : Keeps S₀ G s) :
    ∀ a fi code, G a → s.funcs[a]? = some fi → fi.code = .wasm code → noDynL code.body = true := by
  intro a fi code ha hf hcode
  have hf' : S₀.funcs[a]? = some fi := by rw [← hk.1 a ha]; exact hf
  exact hK.nd a fi code (hK.wasm a fi code ha hf' hcode) hf' hcode

theorem plainOK_mono {bad : Nat → Bool} (hRG : ∀ a, R a → G a) :
    PlainOK G (fun a => bad a = true) fs (CallPl R bad fs) :=
  let h := callPl_plainOK (G := R) (bad := bad) (fs := fs)
  { block := h.block, loop := h.loop, tryTable := h.tryTable, ifLeft := h.ifLeft,
    ifRight := h.ifRight
    call := fun x a hi hx => (h.call x a hi hx).imp_left (hRG a)
    returnCall := fun x a hi hx => hRG a (h.returnCall x a hi hx)
    refFunc := fun x a hi hx => hRG a (h.refFunc x a hi hx) }

/-- The invariant in another store holding references into `G`. -/
theorem invU_store {L : List Val} {s s' : Store Nat} {f : Frame} {code : List Admin}
    (hc : InvU S₀ R G fs ia iu if_ L ⟨s, f, code⟩) (hs : StoreIn G s') :
    InvU S₀ R G fs ia iu if_ L ⟨s', f, code⟩ := by
  obtain ⟨hcf, ht, F, hF, hok⟩ := hc
  exact ⟨⟨hs, hcf.2.1, hcf.2.2⟩, ht, F, soundF_gl rfl hF, okA_gl rfl code hok⟩

/-- Replacing the hole of a context. -/
theorem invU_fill {L L' : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {Y X : List Admin}
    (hc : InvU S₀ R G fs ia iu if_ L ⟨s, f, E.fill Y⟩)
    (hp : ∀ (s : Store Nat) (f : Frame),
      CPost (cfgU S₀ fs ia iu if_) L L' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩)
    (hX : CodeIn G fs (CallPl R (isBadC S₀ ia iu if_) fs) X) (hY : Y.all Admin.isVal = false)
    (hXt : ∀ pr p, Tight R pr p X) :
    InvU S₀ R G fs ia iu if_ L' ⟨s, f, E.fill X⟩ := by
  obtain ⟨hcf, ht, F, hF, hok⟩ := hc
  obtain ⟨-, F', hF', hok'⟩ :=
    fill_post hp E s f F .other [] other_ne_ex sigma_nil hF (by simpa using hok)
  exact ⟨⟨hcf.1, hcf.2.1, CodeIn.fill hcf.2.2 hX⟩, tight_fill hY hXt E ht, F', hF',
    by simpa using hok'⟩

theorem not_all_call {pre : List Admin} {x : FuncIdx} :
    (pre ++ [Admin.plain (.call x)]).all Admin.isVal = false := by
  simp [List.all_append, Admin.isVal, Admin.val?]

theorem not_all_callRef {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) :
    (vals args ++ [.ref (.func a), yy]).all Admin.isVal = false := by
  unfold Admin.IsCallRef at hyy
  split at hyy <;> simp_all [List.all_append, Admin.isVal, Admin.val?]

/-! ## Calls of the three imports -/

section Guard
variable {L : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {x : FuncIdx} {a : Nat}
  {d : DefType}

theorem resume_keep {L' : List Val} {E' : Ctx} {Y : List Admin}
    (hc₁ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E'.fill Y⟩) (hY : Y.all Admin.isVal = false)
    (hp : ∀ (r : Result) (s : Store Nat) (f : Frame),
      CPost (cfgU S₀ fs ia iu if_) L L' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, r.toAdmin⟩) :
    ∀ s' r, Keeps S₀ G s' → RefsOK G r →
      InvU S₀ R G fs ia iu if_ L' ⟨s', f, E'.fill r.toAdmin⟩ := fun _ r hk hr =>
  invU_store (invU_fill hc₁ (hp r) (CodeIn.toAdmin hr) hY (tight_toAdmin r)) hk.2

/-- At a use: the guarded thread. -/
theorem guardedU_use (hK : UClientIn U S₀ R G fs ia iu if_)
    (hc₀ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC S₀ ia iu if_ a = true)
    (hU : isHost S₀ iu a = true) :
    GuardedU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hF' := host_false_of hU (Ne.symm hK.dUF)
  have hA' := host_false_of hU hK.dAU
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgU S₀ fs ia iu if_)
    (fun t ht e => by subst e; simp [callReq, hx, cfgU, cfgOf, hU] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgU, cfgOf, hU, ↓reduceIte, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hreq
    rcases hreq with rfl | rfl
    · exact hab.1
    · exact hab
  have hc₁ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun _ => ⟨v, rfl, hv, ?_⟩, fun h => ?_, fun h => ?_⟩
  · exact resume_keep hc₁ not_all_call (fun r s f => hole_use hx hU v r)
  · rw [hF'] at h; cases h
  · rw [hA'] at h; cases h

/-- At a free: the guarded thread. -/
theorem guardedU_free (hK : UClientIn U S₀ R G fs ia iu if_)
    (hc₀ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC S₀ ia iu if_ a = true)
    (hU' : isHost S₀ iu a = false) (hFr : isHost S₀ if_ a = true) :
    GuardedU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA' := host_false_of hFr hK.dAF
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgU S₀ fs ia iu if_)
    (fun t ht e => by subst e; simp [callReq, hx, cfgU, cfgOf, hU', hFr] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgU, cfgOf, hU', hFr, Bool.false_eq_true, ↓reduceIte,
      beq_iff_eq] at hreq
    subst hreq; exact hab.1
  have hc₁ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun h => ?_, fun _ => ⟨v, rfl, hv, ?_⟩, fun h => ?_⟩
  · rw [hU'] at h; cases h
  · exact resume_keep hc₁ not_all_call (fun r s f => hole_free hx hU' hFr v r)
  · rw [hA'] at h; cases h

/-- At an allocation: the guarded thread. -/
theorem guardedU_alloc (hc₀ : InvU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC S₀ ia iu if_ a = true)
    (hU' : isHost S₀ iu a = false) (hF' : isHost S₀ if_ a = false) :
    GuardedU S₀ R G fs ia iu if_ L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA : isHost S₀ ia a = true := by simpa [isBadC, hU', hF'] using ha
  refine ⟨E, [], a, d, ha, by simp [vals], fun h => ?_, fun h => ?_, fun _ => ⟨rfl, ?_, ?_⟩⟩
  · rw [hU'] at h; cases h
  · rw [hF'] at h; cases h
  · intro s' h hh hk hr
    exact invU_store (invU_fill hc₀ (fun s f => hole_alloc hx hU' hF' hA hh) (CodeIn.toAdmin hr)
      (not_all_call (pre := [])) (tight_toAdmin _)) hk.2
  · intro s' r hk hr hnv
    have hp : ∀ (s : Store Nat) (f : Frame), CPost (cfgU S₀ fs ia iu if_) L L
        (⟨s, f, [.plain (.call x)]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ := by
      intro s f
      cases r with
      | values ws => exact absurd rfl (hnv ws)
      | trap => exact post_trapR rfl
      | throw b => exact post_throwingR rfl b
    exact invU_store (invU_fill hc₀ hp (CodeIn.toAdmin hr) (not_all_call (pre := []))
      (tight_toAdmin _)) hk.2

end Guard

theorem isHost_some {s : Store Nat} {i a : Nat} (h : isHost s i a = true) :
    ∃ fi, s.funcs[a]? = some fi ∧ fi.code = .host i := by
  unfold isHost at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i hh hc; exact ⟨fi, hfi, by rw [hc, beq_iff_eq.1 h]⟩
    · cases h
  · cases h

/-- A call of one of the three imports leads to a guarded thread. -/
theorem guardedU_of_badStep (hK : UClientIn U S₀ R G fs ia iu if_) {L : List Val}
    {c c' : Config Nat} (hc : InvU S₀ R G fs ia iu if_ L c)
    (hb : BadStep (fun a => isBadC S₀ ia iu if_ a = true) fs c c') :
    GuardedU S₀ R G fs ia iu if_ L c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  have hc₀ : InvU S₀ R G fs ia iu if_ L ⟨c.store, c.frame, E.fill [.plain (.call x)]⟩ := by
    rw [← hcode]; exact hc
  by_cases hU : isHost S₀ iu a = true
  · exact guardedU_use hK hc₀ hx ha hU
  · have hU' : isHost S₀ iu a = false := by simpa using hU
    by_cases hFr : isHost S₀ if_ a = true
    · exact guardedU_free hK hc₀ hx ha hU' hFr
    · exact guardedU_alloc hc₀ hx ha hU' (by simpa using hFr)

/-- **One host-free step from an invariant thread** in a store keeping the instance (every
profile). -/
theorem step_invU (hK : UClientIn U S₀ R G fs ia iu if_) {L : List Val} {P : Profile}
    {c c' : Config Nat} (h : Step P (fun _ _ _ _ => False) c c') (hk : Keeps S₀ G c.store)
    (hc : InvU S₀ R G fs ia iu if_ L c) :
    (InvU S₀ R G fs ia iu if_ L c' ∨ GuardedU S₀ R G fs ia iu if_ L c') ∧
      c'.store.funcs = c.store.funcs ∧ StoreIn G c'.store := by
  by_cases hb : BadStep (fun a => isBadC S₀ ia iu if_ a = true) fs c c'
  · refine ⟨.inr (guardedU_of_badStep hK hc hb), ?_⟩
    obtain ⟨_, _, _, _, _, rfl, _⟩ := hb
    exact ⟨rfl, hk.2⟩
  obtain ⟨hc' | hb', hfun⟩ :=
    Silmaril.Wasm.Verify.Step.cfgIn (plainOK_mono hK.sub) hostIn_noHost h (closedG hK hk) hc.1
  · refine ⟨.inl ⟨hc', Step.tight h hc.1 (ndG hK hk) hb _ hc.2.1, ?_⟩, hfun, hc'.1⟩
    have hp := Step.clientU (C := cfgU S₀ fs ia iu if_) (L := L) h (show PairsOK [] by decide) rfl
      (fun a _ hba => by
        simp only [isBadC, Bool.or_eq_false_iff] at hba
        exact ⟨hba.1.2, hba.2, hba.1.1⟩) hc.1 hc' (bodiesG hK hk) hb
    obtain ⟨-, -, F, hF, hok⟩ := hc
    obtain ⟨-, F', hF', hok'⟩ := hp F .other [] other_ne_ex sigma_nil hF (by simpa using hok)
    exact ⟨F', hF', by simpa using hok'⟩
  · exact absurd hb' hb

/-- A guarded thread is at the callout of the import whose host it calls. -/
theorem guardedU_decompose (hK : UClientIn U S₀ R G fs ia iu if_) {L : List Val}
    {c : Config Nat} (hk : Keeps S₀ G c.store) (hg : GuardedU S₀ R G fs ia iu if_ L c) :
    ∃ E b args h, isHost S₀ h b = true ∧ isBadC S₀ ia iu if_ b = true ∧
      decompose? c.store c.code = some (E, b, h, args) ∧
      (isHost S₀ iu b = true → ∃ v, args = [v] ∧ v ∈ L ∧ ∀ s' r, Keeps S₀ G s' → RefsOK G r →
        InvU S₀ R G fs ia iu if_ L ⟨s', c.frame, E.fill r.toAdmin⟩) ∧
      (isHost S₀ if_ b = true → ∃ v, args = [v] ∧ v ∈ L ∧ ∀ s' r, Keeps S₀ G s' → RefsOK G r →
        InvU S₀ R G fs ia iu if_ (L.erase v) ⟨s', c.frame, E.fill r.toAdmin⟩) ∧
      (isHost S₀ ia b = true → args = [] ∧
        (∀ s' h, h ∉ L → Keeps S₀ G s' → RefsOK G (.values [h]) →
          InvU S₀ R G fs ia iu if_ (h :: L) ⟨s', c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
        (∀ s' r, Keeps S₀ G s' → RefsOK G r → (∀ ws, r ≠ .values ws) →
          InvU S₀ R G fs ia iu if_ L ⟨s', c.frame, E.fill r.toAdmin⟩)) := by
  obtain ⟨E, args, b, d, hbad, hcode, hU, hF, hA⟩ := hg
  have hb₀ : ∃ i, isHost S₀ i b = true := by
    simp only [isBadC, Bool.or_eq_true] at hbad
    rcases hbad with (h | h) | h <;> exact ⟨_, h⟩
  obtain ⟨h, hHb⟩ := hb₀
  obtain ⟨fi, hfi, hhost⟩ := isHost_some hHb
  obtain ⟨ps, rs, hexp, hp0, hp1⟩ := hK.hostTy b fi hbad hfi
  have hfi' : c.store.funcs[b]? = some fi := by rw [hk.1 b (hK.bad b hbad)]; exact hfi
  have hn : args.length = ps.length := by
    cases hA' : isHost S₀ ia b
    · simp only [isBadC, hA', Bool.false_or, Bool.or_eq_true] at hbad
      rcases hbad with hb' | hb'
      · obtain ⟨v, rfl, -⟩ := hU hb'; simp [hp1 hA']
      · obtain ⟨v, rfl, -⟩ := hF hb'; simp [hp1 hA']
    · rw [(hA hA').1, hp0 hA']; rfl
  refine ⟨E, b, args, h, hHb, hbad, ?_, hU, hF, hA⟩
  rw [hcode]
  exact decompose_fill hfi' hexp hhost (c := .callRefType d) trivial hn E

end

end Silmaril.Wasm.Resource.ExternClient
