module

public import Silmaril.Proofs.Wasm.Resource.OBClient.Basic

/-!
# Frees of owned handles: the two instances of the analysis

The ownership check with frees (`checkOF`) runs the client analysis twice over the same code:

* the **held** instance `InvC … if_ [] Lh` (`cfgOf`, live list `Lh`: the held handles), where a
  use needs a held handle;
* the **owned** instance `InvB … Lo` (`cfgO`, live list `Lo`: the owned handles), where uses
  are neutral and a free needs an owned handle.

`InvAB` is their conjunction, `GuardedAB` a thread stopped at a call of one of the three imports,
prepared for every answer in both instances. `step_invAB`: every host-free step keeps `InvAB` or
reaches `GuardedAB`. `EntryF`: a pending invocation of a role export, which enters the callee
frame (`entryF_step`), where the entry facts hold in both instances (`invAB_entry`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.OBClient

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn FuncsClosed CallPl Avoids isHost PlOK
  BadStep callPl_plainOK hostIn_noHost invoke_cfgIn decompose_fill isHost_iff)

/-! ## Owned handles of an ownership state -/

/-- The owned handles of an ownership state. -/
def ownedL (L : List (Val × Mode)) : List Val := (L.filter fun p => p.2 == .owned).map Prod.fst

theorem owns_iff (L : List (Val × Mode)) (h : Val) : owns L h = true ↔ h ∈ ownedL L := by
  simp [owns, ownedL]

theorem ownedL_sublist (L : List (Val × Mode)) : (ownedL L).Sublist (heldL L) :=
  (List.filter_sublist).map _

theorem heldL_release {L : List (Val × Mode)} (hn : (heldL L).Nodup) (h : Val) :
    heldL (release L h) = (heldL L).erase h := by
  rw [hn.erase_eq_filter, heldL, heldL, release, List.filter_map]
  rfl

theorem ownedL_release {L : List (Val × Mode)} (hn : (heldL L).Nodup) (h : Val) :
    ownedL (release L h) = (ownedL L).erase h := by
  have hn' : (ownedL L).Nodup := (ownedL_sublist L).nodup hn
  rw [hn'.erase_eq_filter, ownedL, ownedL, release, List.filter_map, List.filter_filter,
    List.filter_filter]
  congr 2
  funext p
  exact Bool.and_comm _ _

theorem heldL_endCall (L : List (Val × Mode)) :
    heldL (L.filter fun p => p.2 == .owned) = ownedL L := rfl

theorem ownedL_endCall (L : List (Val × Mode)) :
    ownedL (L.filter fun p => p.2 == .owned) = ownedL L := by
  simp only [ownedL, List.filter_filter, Bool.and_self]

/-! ## The owned-handle instance -/

section
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}

/-- **The owned-handle invariant** of a running thread (the code part; the reachability part is
the held instance's). -/
def InvB (I : ScalarInstance) (fs : List Nat) (ia iu if_ : Nat) (Lo : List Val)
    (c : Config Nat) : Prop :=
  ∃ F, SoundF [] Lo c.store.globals c.frame.locals F ∧
    okA (cfgO I.store fs ia iu if_) Lo c.store.globals c.frame.module.globals c.frame.locals
      ⟨F, .other, true⟩ c.code

/-- **Both instances**: the held handles `Lh`, the owned handles `Lo`. -/
def InvAB (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (Lh Lo : List Val) (c : Config Nat) : Prop :=
  InvC I G fs ia iu if_ [] Lh c ∧ InvB I fs ia iu if_ Lo c

/-- **A thread stopped at a call of one of the three imports**, prepared for every answer in
both instances: a use needs a held handle, a free an owned one. -/
def GuardedAB (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (Lh Lo : List Val) (c : Config Nat) : Prop :=
  ∃ (E : Ctx) (args : List Val) (b : Nat) (d : DefType), isBadC I.store ia iu if_ b = true ∧
    c.code = E.fill (vals args ++ [.ref (.func b), .callRefType d]) ∧
    (isHost I.store iu b = true → ∃ v, args = [v] ∧ v ∈ Lh ∧
      ∀ r, RefsOK G r → InvAB I G fs ia iu if_ Lh Lo ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store if_ b = true → ∃ v, args = [v] ∧ v ∈ Lo ∧
      ∀ r, RefsOK G r →
        InvAB I G fs ia iu if_ (Lh.erase v) (Lo.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store ia b = true → args = [] ∧
      (∀ h, h ∉ Lh → h ∉ Lo → RefsOK G (.values [h]) → InvAB I G fs ia iu if_ (h :: Lh) (h :: Lo)
        ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
      (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
        InvAB I G fs ia iu if_ Lh Lo ⟨c.store, c.frame, E.fill r.toAdmin⟩))

theorem cfgO_ps (s : Store Nat) : (cfgO s fs ia iu if_).ps = [] := rfl

theorem sigma_cfgO {s : Store Nat} {Lo : List Val} {gl : List GlobalInst} :
    Client.Sigma (cfgO s fs ia iu if_).ps Lo gl := fun p hp => by simp [cfgO_ps] at hp

theorem invB_fill {Lo Lo' : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {Y X : List Admin}
    (hc : InvB I fs ia iu if_ Lo ⟨s, f, E.fill Y⟩)
    (hp : ∀ (s : Store Nat) (f : Frame),
      CPost (cfgO I.store fs ia iu if_) Lo Lo' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩) :
    InvB I fs ia iu if_ Lo' ⟨s, f, E.fill X⟩ := by
  obtain ⟨F, hF, hok⟩ := hc
  obtain ⟨-, F', hF', hok'⟩ :=
    fill_post hp E s f F .other [] other_ne_ex sigma_cfgO hF (by simpa using hok)
  exact ⟨F', hF', by simpa using hok'⟩

theorem invC_fill' {Lh Lh' : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {Y X : List Admin}
    (hc : InvC I G fs ia iu if_ [] Lh ⟨s, f, E.fill Y⟩)
    (hp : ∀ (s : Store Nat) (f : Frame),
      CPost (cfgOf I.store fs ia iu if_ []) Lh Lh' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩)
    {r : Result} (hr : RefsOK G r) (hX : X = r.toAdmin) :
    InvC I G fs ia iu if_ [] Lh' ⟨s, f, E.fill X⟩ :=
  invC_fill hc hp (hX ▸ toAdmin_codeIn hr)

/-! ## The guard: the three imports -/

section Guard
variable {Lh Lo : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {x : FuncIdx} {a : Nat}
  {d : DefType}

theorem cfgO_fs (s : Store Nat) : (cfgO s fs ia iu if_).fs = fs := rfl

/-- At a use: the held instance supplies the argument; the owned instance is neutral. -/
theorem guardedAB_use (hR : ClientCore I G fs ia iu if_ [])
    (hc₀ : InvAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU : isHost I.store iu a = true) :
    GuardedAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hF' := host_false_of hU (Ne.symm hR.dUF)
  have hA' := host_false_of hU hR.dAU
  obtain ⟨⟨-, -, F, -, hok⟩, hB⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgOf I.store fs ia iu if_ [])
    (fun t ht e => by subst e; simp [callReq, hx, cfgOf, hU] at ht) E _ _ F hok
  have hv : v ∈ Lh := by
    simp only [callReq, hx, cfgOf, hU, ↓reduceIte, Bool.false_or, Bool.or_eq_true,
      beq_iff_eq] at hreq
    rcases hreq with rfl | rfl
    · exact hab.1
    · exact hab
  have hA₁ : InvC I G fs ia iu if_ [] Lh ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀.1
  have hB₁ : InvB I fs ia iu if_ Lo ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ := hE _ ▸ hB
  refine ⟨E', [v], a, d, ha, hE _, fun _ => ⟨v, rfl, hv, fun r hr => ⟨?_, ?_⟩⟩,
    fun h => absurd h (by rw [hF']; exact Bool.false_ne_true),
    fun h => absurd h (by rw [hA']; exact Bool.false_ne_true)⟩
  · exact invC_fill hA₁ (fun s f => hole_use hx hU v r) (toAdmin_codeIn hr)
  · exact invB_fill hB₁ (fun s f => hole_use (C := cfgO I.store fs ia iu if_) hx hU v r)

/-- At a free: the owned instance supplies the argument, an owned handle. -/
theorem guardedAB_free (hR : ClientCore I G fs ia iu if_ [])
    (hc₀ : InvAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU' : isHost I.store iu a = false) (hFr : isHost I.store if_ a = true) :
    GuardedAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA' := host_false_of hFr hR.dAF
  obtain ⟨hA, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgO I.store fs ia iu if_)
    (fun t ht e => by subst e; simp [callReq, hx, cfgO, cfgOf, hU', hFr] at ht) E _ _ F hok
  have hv : v ∈ Lo := by
    simp only [callReq, hx, cfgO, cfgOf, hU', hFr, Bool.false_eq_true, ↓reduceIte,
      beq_iff_eq] at hreq
    subst hreq; exact hab.1
  have hA₁ : InvC I G fs ia iu if_ [] Lh ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hA
  have hB₁ : InvB I fs ia iu if_ Lo ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀.2
  refine ⟨E', [v], a, d, ha, hE _, fun h => absurd h (by rw [hU']; exact Bool.false_ne_true),
    fun _ => ⟨v, rfl, hv, fun r hr => ⟨?_, ?_⟩⟩,
    fun h => absurd h (by rw [hA']; exact Bool.false_ne_true)⟩
  · exact invC_fill hA₁ (fun s f => hole_free hx hU' hFr v r) (toAdmin_codeIn hr)
  · exact invB_fill hB₁ (fun s f => hole_free (C := cfgO I.store fs ia iu if_) hx hU' hFr v r)

/-- At an allocation: both instances add the fresh handle. -/
theorem guardedAB_alloc (hc₀ : InvAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU' : isHost I.store iu a = false) (hF' : isHost I.store if_ a = false) :
    GuardedAB I G fs ia iu if_ Lh Lo ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA : isHost I.store ia a = true := by simpa [isBadC, hU', hF'] using ha
  have hother : ∀ r : Result, (∀ ws, r ≠ .values ws) → ∀ (C : Cfg) (L : List Val)
      (s : Store Nat) (f : Frame),
      CPost C L L (⟨s, f, [.plain (.call x)]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ := by
    intro r hnv C L s f
    cases r with
    | values ws => exact absurd rfl (hnv ws)
    | trap => exact post_trapR rfl
    | throw b => exact post_throwingR rfl b
  refine ⟨E, [], a, d, ha, by simp [vals],
    fun h => absurd h (by rw [hU']; exact Bool.false_ne_true),
    fun h => absurd h (by rw [hF']; exact Bool.false_ne_true), fun _ => ⟨rfl, ?_, ?_⟩⟩
  · intro h hh hho hr
    exact ⟨invC_fill hc₀.1 (fun s f => hole_alloc hx hU' hF' hA hh) (toAdmin_codeIn hr),
      invB_fill hc₀.2 (fun s f => hole_alloc (C := cfgO I.store fs ia iu if_) hx hU' hF' hA hho)⟩
  · intro r hr hnv
    exact ⟨invC_fill hc₀.1 (fun s f => hother r hnv _ _ s f) (toAdmin_codeIn hr),
      invB_fill hc₀.2 (fun s f => hother r hnv _ _ s f)⟩

end Guard

/-- A call of one of the three imports leads to a guarded thread. -/
theorem guardedAB_of_badStep (hR : ClientCore I G fs ia iu if_ []) {Lh Lo : List Val}
    {c c' : Config Nat} (hc : InvAB I G fs ia iu if_ Lh Lo c)
    (hb : BadStep (fun a => isBadC I.store ia iu if_ a = true) fs c c') :
    GuardedAB I G fs ia iu if_ Lh Lo c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  have hc₀ : InvAB I G fs ia iu if_ Lh Lo ⟨c.store, c.frame, E.fill [.plain (.call x)]⟩ := by
    rw [← hcode]; exact hc
  by_cases hU : isHost I.store iu a = true
  · exact guardedAB_use hR hc₀ hx ha hU
  · have hU' : isHost I.store iu a = false := by simpa using hU
    by_cases hFr : isHost I.store if_ a = true
    · exact guardedAB_free hR hc₀ hx ha hU' hFr
    · exact guardedAB_alloc hc₀ hx ha hU' (by simpa using hFr)

/-- The reachable functions are no import of the owned instance. -/
theorem avoids_cfgO (hR : ClientCore I G fs ia iu if_ []) (a : Nat) (ha : G a) :
    (cfgO I.store fs ia iu if_).isU a = false ∧ (cfgO I.store fs ia iu if_).isF a = false ∧
      (cfgO I.store fs ia iu if_).isA a = false :=
  avoids_cfg hR a ha

/-- **One host-free step from both instances** (every profile). -/
theorem step_invAB (hR : ClientCore I G fs ia iu if_ [])
    (hbO : BodiesC G (cfgO I.store fs ia iu if_) I.store.funcs) {Lh Lo : List Val} {P : Profile}
    {c c' : Config Nat} (h : Step P (fun _ _ _ _ => False) c c')
    (hf : c.store.funcs = I.store.funcs) (hc : InvAB I G fs ia iu if_ Lh Lo c) :
    (InvAB I G fs ia iu if_ Lh Lo c' ∨ GuardedAB I G fs ia iu if_ Lh Lo c') ∧
      c'.store.funcs = c.store.funcs := by
  have hcl : FuncsClosed G fs (CallPl G (isBadC I.store ia iu if_) fs) c.store.funcs :=
    hf ▸ hR.closed
  have hbf : BodiesC G (cfgOf I.store fs ia iu if_ []) c.store.funcs := hf ▸ hR.bodies
  have hbo : BodiesC G (cfgO I.store fs ia iu if_) c.store.funcs := hf ▸ hbO
  obtain ⟨hc' | hb, hfun⟩ :=
    Silmaril.Wasm.Verify.Step.cfgIn callPl_plainOK hostIn_noHost h hcl hc.1.1
  · have hpA := Step.client (C := cfgOf I.store fs ia iu if_ []) (L := Lh) h hR.pairs rfl
      (avoids_cfg hR) hc.1.1 hc' hbf
    have hpB := Step.client (C := cfgO I.store fs ia iu if_) (L := Lo) h hR.pairs rfl
      (avoids_cfgO hR) hc.1.1 hc' hbo
    obtain ⟨⟨-, hS, F, hF, hok⟩, F₂, hF₂, hok₂⟩ := hc
    obtain ⟨hS', F', hF', hok'⟩ := hpA F .other [] other_ne_ex hS hF (by simpa using hok)
    obtain ⟨-, F₂', hF₂', hok₂'⟩ :=
      hpB F₂ .other [] other_ne_ex sigma_cfgO hF₂ (by simpa using hok₂)
    exact ⟨.inl ⟨⟨hc', hS', F', hF', by simpa using hok'⟩, F₂', hF₂', by simpa using hok₂'⟩,
      hfun⟩
  · exact ⟨.inr (guardedAB_of_badStep hR hc hb), hfun⟩

end

/-! ## Threads, callouts and resumptions -/

section Threads
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}

theorem invAB_invoke {Lh Lo : List Val} {s : Store Nat} (hs : StoreIn G s) {a : Nat} (ha : G a)
    {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) :
    InvAB I G fs ia iu if_ Lh Lo (invoke s a args) := by
  refine ⟨invC_invoke hs (fun p hp => by simp at hp) ha hargs, [], SoundF_nil, ?_⟩
  have h := freeP_vals (C := cfgO I.store fs ia iu if_) (V := vals args ++ [.ref (.func a)])
    (R := [.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]) (fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; simp
      · simp only [List.mem_singleton] at hy; subst hy; simp)
    (freeP_nest trivial fun _ _ _ _ => trivial) Lo s.globals ({} : Frame).module.globals
    ({} : Frame).locals [] [] trivial
  simpa [invoke] using h

/-- Resuming an owned-instance thread at a host callout keeps the invariant. -/
theorem resume_invB {Lo : List Val} {s : Store Nat} {t : Thread}
    (hc : InvB I fs ia iu if_ Lo (t.config s)) (r : Result) :
    InvB I fs ia iu if_ Lo ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, yy, _, _, _, _, hyy, _, _, hfill⟩ := decompose?_sound hd
    have h₀ : t.config s = ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      cases t <;> rfl
    have hc' : InvB I fs ia iu if_ Lo
        ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := h₀ ▸ hc
    exact invB_fill hc' (fun _ _ => hole_host hyy r)

/-- Resuming at a callout of another import keeps both instances. -/
theorem resume_invAB {Lh Lo : List Val} {s : Store Nat} {t : Thread}
    (hc : InvAB I G fs ia iu if_ Lh Lo (t.config s)) (r : Result) (hr : RefsOK G r) :
    InvAB I G fs ia iu if_ Lh Lo ((resumeResult s t r).config s) :=
  ⟨resume_invC hc.1 r hr, resume_invB hc.2 r⟩

/-- The import of a guarded thread, with its decomposition. -/
theorem guardedAB_cases (hR : ClientCore I G fs ia iu if_ []) {Lh Lo : List Val}
    {c : Config Nat} (hf : c.store.funcs = I.store.funcs)
    (hg : GuardedAB I G fs ia iu if_ Lh Lo c) :
    ∃ (E : Ctx) (b : Nat),
      (∃ v, decompose? c.store c.code = some (E, b, iu, [v]) ∧ v ∈ Lh ∧ ∀ r, RefsOK G r →
          InvAB I G fs ia iu if_ Lh Lo ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (∃ v, decompose? c.store c.code = some (E, b, if_, [v]) ∧ v ∈ Lo ∧ ∀ r, RefsOK G r →
          InvAB I G fs ia iu if_ (Lh.erase v) (Lo.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (decompose? c.store c.code = some (E, b, ia, []) ∧
        (∀ h, h ∉ Lh → h ∉ Lo → RefsOK G (.values [h]) → InvAB I G fs ia iu if_ (h :: Lh)
          (h :: Lo) ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
        (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
          InvAB I G fs ia iu if_ Lh Lo ⟨c.store, c.frame, E.fill r.toAdmin⟩)) := by
  obtain ⟨E, args, b, d, hbad, hcode, hU, hF, hA⟩ := hg
  refine ⟨E, b, ?_⟩
  simp only [isBadC, Bool.or_eq_true] at hbad
  rcases hbad with (h | h) | h
  · obtain ⟨rfl, h₁, h₂⟩ := hA h
    exact .inr (.inr ⟨guarded_decompose hR hf h (fun hi => (hR.arA hi).1) hcode, h₁, h₂⟩)
  · obtain ⟨v, rfl, hv, hr⟩ := hU h
    exact .inl ⟨v, guarded_decompose hR hf h (fun hi => hR.arU hi) hcode, hv, hr⟩
  · obtain ⟨v, rfl, hv, hr⟩ := hF h
    exact .inr (.inl ⟨v, guarded_decompose hR hf h (fun hi => hR.arF hi) hcode, hv, hr⟩)

theorem guardedAB_callout (hR : ClientCore I G fs ia iu if_ []) {Lh Lo : List Val}
    {s : Store Nat} {t : Thread} (hf : s.funcs = I.store.funcs)
    (hg : GuardedAB I G fs ia iu if_ Lh Lo (t.config s)) :
    ∃ h args, CalloutAt s t h args := by
  have hf' : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hf
  obtain ⟨E, b, ⟨v, hd, -⟩ | ⟨v, hd, -⟩ | ⟨hd, -⟩⟩ := guardedAB_cases hR hf' hg <;>
    rw [Thread.config_store] at hd <;> exact ⟨_, _, E, b, hd⟩

end Threads

/-! ## Entering a role export -/

section Entry
variable {I : ScalarInstance} {G R : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}

/-- **A pending invocation of a role export** whose argument is held, and owned when the owned
instance starts from `loc 0` (`ow`). -/
def EntryF (I : ScalarInstance) (G R : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (Lh Lo : List Val) (s : Store Nat) (t : Thread) : Prop :=
  ∃ (a : Nat) (h : Val) (ow : Bool) (fi : FuncInst Nat) (code : Func) (ps rs : Ty (.list .val)),
    t = .pending a [h] ∧ R a ∧ h ∈ Lh ∧ (ow = true → h ∈ Lo) ∧ StoreIn G s ∧
    (∀ r, Val.ref r ∈ [h] → RefIn G r) ∧
    s.funcs[a]? = some fi ∧ fi.code = .wasm code ∧ Expand fi.type (.func ps rs) ∧
    [h].length = ps.length ∧ fi.module.funcs = fs ∧
    (∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu if_) fs) i) ∧
    okL (cfgOf I.store fs ia iu if_ []) fi.module.globals [.loc 0] .other code.body = true ∧
    okL (cfgO I.store fs ia iu if_) fi.module.globals (if ow then [.loc 0] else []) .other
      code.body = true

/-- The entered callee frame of a role export passes the held-instance check: its parameter is
held. -/
theorem invA_entry {Lh : List Val} {s : Store Nat} {h : Val} {fi : FuncInst Nat} {code : Func}
    {rs : Ty (.list .val)} (hs : StoreIn G s) (hh : h ∈ Lh)
    (hr : ∀ r, Val.ref r ∈ [h] → RefIn G r) (hm : fi.module.funcs = fs)
    (hpl : ∀ i ∈ code.body, PlOK (CallPl G (isBadC I.store ia iu if_) fs) i)
    (hok : okL (cfgOf I.store fs ia iu if_ []) fi.module.globals [.loc 0] .other code.body
      = true) :
    InvC I G fs ia iu if_ [] Lh ⟨s, {}, [Silmaril.Wasm.Logic.Hoare.callFrame fi code rs [h]]⟩ := by
  have hfr : FrameIn G fs (Frame.forCall fi.module [h] code.locals) :=
    Silmaril.Wasm.Verify.FrameIn.forCall hm hr _
  have hcode : CodeIn G fs (CallPl G (isBadC I.store ia iu if_) fs)
      [Silmaril.Wasm.Logic.Hoare.callFrame fi code rs [h]] :=
    CodeIn.frame_iff.2 ⟨hfr, CodeIn.label_iff.2 ⟨by simp, CodeIn.expression hpl⟩⟩
  have hsound : SoundF [] Lh s.globals (Frame.forCall fi.module [h] code.locals).locals
      [.loc 0] := by
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨h, by simp [Frame.forCall], hh, fun p hp => by cases hp⟩
  have hbody := okA_body (L := Lh) (gl := s.globals)
    (lc := (Frame.forCall fi.module [h] code.locals).locals) hok .other []
  simp only [vals, List.map_nil, List.nil_append] at hbody
  have h0 : FrameIn G fs ({} : Frame) := ⟨.inr rfl, fun r hr => by simp at hr⟩
  have hsig : Client.Sigma [] Lh s.globals := fun p hp => by simp at hp
  refine ⟨⟨hs, h0, hcode⟩, hsig, [], SoundF_nil, ?_⟩
  show okA _ Lh s.globals ({} : Frame).module.globals ({} : Frame).locals ⟨[], .other, true⟩
    [.frame rs.length (Frame.forCall fi.module [h] code.locals)
      [.label rs.length [] (expression code.body)]]
  rw [okA_frame_pre other_ne_ex]
  refine ⟨okX_frame.2 ⟨[.loc 0], hsound, ?_⟩, trivial⟩
  rw [okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, [.loc 0], hsound, hbody⟩, trivial⟩

/-- The entered frame passes the owned-instance check from the entry facts. -/
theorem invB_entry {Lo : List Val} {s : Store Nat} {h : Val} {ow : Bool} {fi : FuncInst Nat}
    {code : Func} {rs : Ty (.list .val)} (hh : ow = true → h ∈ Lo)
    (hok : okL (cfgO I.store fs ia iu if_) fi.module.globals (if ow then [.loc 0] else []) .other
      code.body = true) :
    InvB I fs ia iu if_ Lo ⟨s, {}, [Silmaril.Wasm.Logic.Hoare.callFrame fi code rs [h]]⟩ := by
  have hsound : SoundF [] Lo s.globals (Frame.forCall fi.module [h] code.locals).locals
      (if ow then [.loc 0] else []) := by
    intro f hf
    cases ow
    · simp at hf
    · simp only [↓reduceIte, List.mem_singleton] at hf
      subst hf
      exact ⟨h, by simp [Frame.forCall], hh rfl, fun p hp => by cases hp⟩
  have hbody := okA_body (L := Lo) (gl := s.globals)
    (lc := (Frame.forCall fi.module [h] code.locals).locals) hok .other []
  simp only [vals, List.map_nil, List.nil_append] at hbody
  refine ⟨[], SoundF_nil, ?_⟩
  show okA _ Lo s.globals ({} : Frame).module.globals ({} : Frame).locals ⟨[], .other, true⟩
    [.frame rs.length (Frame.forCall fi.module [h] code.locals)
      [.label rs.length [] (expression code.body)]]
  rw [okA_frame_pre other_ne_ex]
  refine ⟨okX_frame.2 ⟨_, hsound, ?_⟩, trivial⟩
  rw [okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, _, hsound, hbody⟩, trivial⟩

/-- An entering thread is at no callout. -/
theorem entryF_no_callout {Lh Lo : List Val} {s : Store Nat} {t : Thread}
    (he : EntryF I G R fs ia iu if_ Lh Lo s t) {h : Nat} {args : List Val} :
    ¬ CalloutAt s t h args := by
  obtain ⟨a, v, -, fi, code, ps, rs, rfl, -, -, -, -, -, hf, hcode, -⟩ := he
  rintro ⟨E, b, hd⟩
  have hn : decompose? s (vals [v] ++ [.ref (.func a), .callRefType
      ((s.funcs[a]?.map FuncInst.type).getD default)]) = none :=
    Silmaril.Wasm.Logic.Hoare.decompose?_call_wasm trivial hf hcode
  have hc : (Thread.pending a [v]).config s = invoke s a [v] := rfl
  rw [hc] at hd
  simp only [invoke] at hd
  rw [hn] at hd
  cases hd

/-- **The step of an entering thread** enters the callee frame, where both instances hold. -/
theorem entryF_step {P : Profile} {Lh Lo : List Val} {s s' : Store Nat} {t t' : Thread}
    (he : EntryF I G R fs ia iu if_ Lh Lo s t) (hst : InternalP P (s, t) (s', t')) :
    InvAB I G fs ia iu if_ Lh Lo (t'.config s') ∧ s' = s := by
  obtain ⟨a, v, ow, fi, code, ps, rs, rfl, -, hv, hvo, hs, hr, hf, hcode, hexp, hn, hm, hpl, hok,
    hokO⟩ := he
  obtain ⟨f', code', rfl, hstep⟩ := hst
  have hinv : (Thread.pending a [v]).config s =
      ⟨s, {}, vals [] ++ vals [v] ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [Thread.config, invoke, hf, vals]
  rw [hinv] at hstep
  have hc := Silmaril.Wasm.Logic.Hoare.call_step_inv (c := .callRefType fi.type) trivial hf hcode hexp
    hn hstep
  simp only [vals, List.map_nil, List.nil_append, Config.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  exact ⟨⟨invA_entry hs hv hr hm hpl hok, invB_entry hvo hokO⟩, rfl⟩

end Entry

end Silmaril.Wasm.Resource.OBClient
