module

public import Silmaril.Proofs.Wasm.Resource.Client.Step
public import Silmaril.Proofs.Wasm.Resource.Handle.Basic
public import Silmaril.Wasm.Verify.Check.Thms

/-!
# The client typestate analysis: every play is accepted

`ClientIn I G fs ia iu if_ ps` collects what the checker establishes: the reachable functions `G`
are closed for calls (`CallPl`, with calls of the three imports as the bad steps), their bodies
pass the client check (`BodiesC`), the store and the exports are in `G`, `G` avoids the three
imports, which are distinct and of arities `[] → [h]`, `[h] → …`, `[h] → …`; the pairs are
distinct and their flags start at `i32 0`.

* `InvC L c`: the reachability invariant, the store invariant and the check of the code for the
  live list `L`; `GuardedC L c`: a thread stopped at a call of one of the three imports, whose
  argument is live (a use) or live and held by no flagged pair (a free), and whose resumption with
  every answer is invariant for the new live list.
* `client_guard`: the argument of a use or free is found in the innermost sequence with its
  semantic top; `guardedC_of_badStep`, `step_invC`.
* `clientLTSInv`: **the protocol invariant of `I.dlts P I.store`** for
  `(clientSpec ia iu if_).comap moveEvent`; `clientIn_sound`: the client sentence over
  `wasmSem P`, every profile.
* `clientIn_of_checkInst`, **`checkClient_sound`**: the Boolean checker establishes `ClientIn`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.Client

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn StoreIn RefIn FuncsClosed CallPl Avoids isHost BadStep
  callPl_plainOK hostIn_noHost invoke_cfgIn typed_refIn answer_refIn callout_mem decompose_fill
  decompose_toAdmin_none ifaceOp?_fst ifaceOp?_snd isHost_iff refFuncs)

/-- What the checker establishes for the client sentence, the exports aside (the thread-level
part of the analysis). -/
structure ClientCore (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) : Prop where
  ok : I.Ok
  closed : FuncsClosed G fs (CallPl G (isBadC I.store ia iu if_) fs) I.store.funcs
  bodies : BodiesC G (cfgOf I.store fs ia iu if_ ps) I.store.funcs
  store : StoreIn G I.store
  avA : Avoids G I.store.funcs ia
  avU : Avoids G I.store.funcs iu
  avF : Avoids G I.store.funcs if_
  pairs : PairsOK ps
  init : ∀ p ∈ ps, gval I.store.globals p.1 = some (Val.i32 0)
  dAU : ia ≠ iu
  dAF : ia ≠ if_
  dUF : iu ≠ if_
  arA : ∀ h : ia < I.imports.length, (I.imports.get ⟨ia, h⟩).params.length = 0 ∧
    (I.imports.get ⟨ia, h⟩).results.length = 1
  arU : ∀ h : iu < I.imports.length, (I.imports.get ⟨iu, h⟩).params.length = 1
  arF : ∀ h : if_ < I.imports.length, (I.imports.get ⟨if_, h⟩).params.length = 1

/-- What the checker establishes for the client sentence. -/
structure ClientIn (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) : Prop extends ClientCore I G fs ia iu if_ ps where
  exports : ∀ j, G (I.addr j)

section
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}
  {ps : List (Nat × Nat)}

/-- The references of a result are in `G`. -/
def RefsOK (G : Nat → Prop) (r : Result) : Prop := ∀ x ∈ codeRefs r.toAdmin, RefIn G x

/-- **The client invariant of a running thread** for the live list `L`. -/
def InvC (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) (L : List Val) (c : Config Nat) : Prop :=
  CfgIn G fs (CallPl G (isBadC I.store ia iu if_) fs) c ∧ Sigma ps L c.store.globals ∧
    ∃ F, SoundF ps L c.store.globals c.frame.locals F ∧
      okA (cfgOf I.store fs ia iu if_ ps) L c.store.globals c.frame.module.globals c.frame.locals
        ⟨F, .other, true⟩ c.code

/-- **A thread stopped at a call of one of the three imports**, prepared for every answer. -/
def GuardedC (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) (L : List Val) (c : Config Nat) : Prop :=
  ∃ (E : Ctx) (args : List Val) (b : Nat) (d : DefType), isBadC I.store ia iu if_ b = true ∧
    c.code = E.fill (vals args ++ [.ref (.func b), .callRefType d]) ∧
    (isHost I.store iu b = true → ∃ v, args = [v] ∧ v ∈ L ∧
      ∀ r, RefsOK G r → InvC I G fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store if_ b = true → ∃ v, args = [v] ∧ v ∈ L ∧
      ∀ r, RefsOK G r → InvC I G fs ia iu if_ ps (L.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store ia b = true → args = [] ∧
      (∀ h, h ∉ L → RefsOK G (.values [h]) →
        InvC I G fs ia iu if_ ps (h :: L) ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
      (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
        InvC I G fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩))

/-! ## Hosts -/

theorem isHost_false_of_avoids {s : Store Nat} {i a : Nat} (hav : Avoids G s.funcs i) (ha : G a) :
    isHost s i a = false := by
  unfold isHost
  split
  · rename_i fi hfi
    split
    · rename_i h hh
      have := hav a fi ha hfi
      simp only [beq_eq_false_iff_ne, ne_eq]
      rintro rfl; exact this hh
    · rfl
  · rfl

theorem isHost_unique {s : Store Nat} {i j a : Nat} (hi : isHost s i a = true)
    (hj : isHost s j a = true) : i = j := by
  unfold isHost at hi hj
  split at hi
  · rename_i fi hfi
    simp only [hfi] at hj
    split at hi
    · rename_i h hh
      simp only [hh, beq_iff_eq] at hi hj
      exact hi.symm.trans hj
    · cases hi
  · cases hi

/-! ## The holes of the three imports -/

section Holes
variable {C : Cfg} {L : List Val}

theorem okA_result {gl : List GlobalInst} {gs : List Nat} {lc : List (Option Val)} {F : List Fact}
    {l : List Admin} {L' : List Val} (hl : okA C L' gl gs lc ⟨F, .other, false⟩ l) (r : Result) :
    okA C L' gl gs lc ⟨F, .other, true⟩ (r.toAdmin ++ l) := by
  cases r with
  | values vs =>
    exact okA_keep hl _ (fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
      exact Or.inl (by simp)) _ _
  | trap => exact okA_trap _ _
  | throw a => exact okA_throwing _ _ _ _

theorem SoundF_noLive {gl : List GlobalInst} {lc : List (Option Val)} {F : List Fact}
    {L' : List Val} (hn : ∀ f ∈ F, isLive f = false) (h : SoundF C.ps L gl lc F) :
    SoundF C.ps L' gl lc F := by
  intro f hf
  have h₁ := h f hf
  cases f with
  | on k => exact h₁
  | off k => exact h₁
  | live k => simp [isLive] at hn; exact absurd (hn _ hf) (by simp)
  | loc k => simp [isLive] at hn; exact absurd (hn _ hf) (by simp)

theorem okA_call_hole {gl : List GlobalInst} {gs : List Nat} {lc : List (Option Val)}
    {F : List Fact} {t : CTop}
    (ht : t ≠ .ex) {v : Val} {x : FuncIdx} {l : List Admin}
    (h : okA C L gl gs lc ⟨F, t, true⟩ (vals [v] ++ [.plain (.call x)] ++ l)) :
    ∃ t', Ab C.ps L gl t' v ∧ callReq C t' x = true ∧
      okA C L gl gs lc ⟨(callNext C F x).1, (callNext C F x).2, false⟩ l := by
  simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
  rw [okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [okA_plain ht₁ (.inr rfl)] at h
  exact ⟨t₁, hab, h⟩

/-- The hole of a use. -/
theorem hole_use {s : Store Nat} {f : Frame} {x : FuncIdx} {a : Nat} (hx : C.fs[x.toNat]? = some a)
    (hU : C.isU a = true) (v : Val) (r : Result) :
    CPost C L L (⟨s, f, vals [v] ++ [.plain (.call x)]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨t₁, -, -, hl⟩ := okA_call_hole ht h
  have hn : callNext C F x = (F, .other) := by simp [callNext, hx, hU]
  rw [hn] at hl
  exact ⟨hS, F, hF, okA_result hl r⟩

/-- The hole of a free: the freed handle is held by no flagged pair. -/
theorem hole_free {s : Store Nat} {f : Frame} {x : FuncIdx} {a : Nat}
    (hx : C.fs[x.toNat]? = some a) (hU : C.isU a = false) (hFr : C.isF a = true) (v : Val)
    (r : Result) :
    CPost C L (L.erase v) (⟨s, f, vals [v] ++ [.plain (.call x)]⟩ : Config Nat)
      ⟨s, f, r.toAdmin⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨t₁, hab, hreq, hl⟩ := okA_call_hole ht h
  have hfr : t₁ = .fr := by simpa [callReq, hx, hU, hFr] using hreq
  subst hfr
  obtain ⟨-, hfree⟩ := hab
  have hn : callNext C F x = (F.filter fun f => !isLive f, .other) := by
    simp [callNext, hx, hU, hFr]
  rw [hn] at hl
  refine ⟨fun p hp hon => ?_, _, SoundF_noLive (fun f hf => by simpa using (List.mem_filter.1 hf).2)
    (SoundF_filter _ hF), okA_result (okA_npre_indep l hl) r⟩
  obtain ⟨w, hw, hwL⟩ := hS p hp hon
  refine ⟨w, hw, (List.mem_erase_of_ne fun e => hfree p hp hon (by rw [← e]; exact hw)).2 hwL⟩

/-- The hole of an allocation answered with a fresh handle. -/
theorem hole_alloc {s : Store Nat} {f : Frame} {x : FuncIdx} {a : Nat}
    (hx : C.fs[x.toNat]? = some a) (hU : C.isU a = false) (hFr : C.isF a = false)
    (hA : C.isA a = true) {h : Val} (hh : h ∉ L) :
    CPost C L (h :: L) (⟨s, f, [.plain (.call x)]⟩ : Config Nat) ⟨s, f, [h.toAdmin]⟩ := by
  intro F t l ht hS hF hc
  simp only at hS hF hc ⊢
  rw [List.singleton_append, okA_plain ht (.inr rfl)] at hc
  have hn : nextI C f.module.globals F t (.call x) = (F, .fr) := by
    simp [nextI, callNext, hx, hU, hFr, hA]
  rw [hn] at hc
  have hsub : ∀ w ∈ L, w ∈ h :: L := fun _ hw => List.mem_cons_of_mem _ hw
  refine ⟨Sigma_mono hsub hS, F, SoundF_mono hsub hF, ?_⟩
  rw [List.singleton_append, okA_val_pre other_ne_ex]
  refine ⟨.fr, ⟨List.mem_cons_self, fun p hp hon e => ?_⟩, okA_pre_of_npre (okA_npre_indep l hc.2)⟩
  obtain ⟨w, hw, hwL⟩ := hS p hp hon
  rw [e] at hw; cases hw; exact hh hwL

/-- The hole of a host call (resumption with any result). -/
theorem hole_host {s : Store Nat} {f : Frame} {args : List Val} {a : Nat} {yy : Admin}
    (hyy : yy.IsCallRef) (r : Result) :
    CPost C L L (⟨s, f, vals args ++ [.ref (.func a), yy]⟩ : Config Nat) ⟨s, f, r.toAdmin⟩ := by
  refine post_kill rfl rfl rfl (killP_vals (by simp [vals])
    (killP_vals (V := [.ref (.func a)]) (by simp) (killP_callRef hyy))) ?_
  intro L gl gs lc F l hl
  exact okA_result (okA_bot hl _) r

end Holes

/-! ## Replacing the hole of a context -/

theorem fill_post {C : Cfg} {L L' : List Val} {X Y : List Admin}
    (h : ∀ (s : Store Nat) (f : Frame), CPost C L L' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩) :
    ∀ (E : Ctx) (s : Store Nat) (f : Frame),
      CPost C L L' (⟨s, f, E.fill Y⟩ : Config Nat) ⟨s, f, E.fill X⟩
  | .top pre rest, s, f => by
    simpa only [Ctx.fill] using post_ctxtInstrs (vs := pre) (rest := rest) (h s f)
  | .label pre n k E rest, s, f => by
    simpa only [Ctx.fill] using post_ctxtInstrs (vs := pre) (rest := rest)
      (post_ctxtLabel (n := n) (cont := k) (fill_post h E s f) rfl)
  | .handler pre n cs E rest, s, f => by
    simpa only [Ctx.fill] using post_ctxtInstrs (vs := pre) (rest := rest)
      (post_ctxtHandler (n := n) (cs := cs) (fill_post h E s f) rfl)
  | .frame pre n fr E rest, s, f => by
    simpa only [Ctx.fill] using post_ctxtInstrs (vs := pre) (rest := rest)
      (post_ctxtFrame (n := n) (f := f) (fill_post h E s fr))

theorem invC_fill {L L' : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {Y X : List Admin}
    (hc : InvC I G fs ia iu if_ ps L ⟨s, f, E.fill Y⟩)
    (hp : ∀ (s : Store Nat) (f : Frame),
      CPost (cfgOf I.store fs ia iu if_ ps) L L' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩)
    (hX : CodeIn G fs (CallPl G (isBadC I.store ia iu if_) fs) X) :
    InvC I G fs ia iu if_ ps L' ⟨s, f, E.fill X⟩ := by
  obtain ⟨hcf, hS, F, hF, hok⟩ := hc
  obtain ⟨hS', F', hF', hok'⟩ :=
    fill_post hp E s f F .other [] other_ne_ex hS hF (by simpa using hok)
  exact ⟨⟨hcf.1, hcf.2.1, CodeIn.fill hcf.2.2 hX⟩, hS', F', hF', by simpa using hok'⟩

/-! ## The argument of a use or a free -/

/-- **A call needing a precise top is preceded by a value of that top**, in its innermost
sequence. -/
theorem client_guard {C : Cfg} {L : List Val} {gl : List GlobalInst} {x : FuncIdx}
    (hreq : ∀ t, callReq C t x = true → t ≠ .other) :
    ∀ (E : Ctx) (gs : List Nat) (lc : List (Option Val)) (F : List Fact),
      okA C L gl gs lc ⟨F, .other, true⟩ (E.fill [.plain (.call x)]) →
      ∃ (E' : Ctx) (v : Val) (t : CTop), Ab C.ps L gl t v ∧ callReq C t x = true ∧
        ∀ Y, E.fill Y = E'.fill (vals [v] ++ Y)
  | .top pre rest, gs, lc, F, h => by
    simp only [Ctx.fill] at h
    rcases List.eq_nil_or_concat pre with rfl | ⟨pre', v, rfl⟩
    · simp only [vals, List.map_nil, List.nil_append, List.cons_append] at h
      rw [okA_plain other_ne_ex (.inr rfl)] at h
      exact absurd rfl (hreq _ h.1)
    · rw [List.concat_eq_append, List.append_assoc] at h
      obtain ⟨t, hab, h⟩ := okA_vals_last other_ne_ex pre' v h
      have ht : t ≠ .ex := by rintro rfl; exact hab
      rw [List.singleton_append, okA_plain ht (.inr rfl)] at h
      exact ⟨.top pre' rest, v, t, hab, h.1, fun Y => by simp [Ctx.fill, vals]⟩
  | .label pre n k E rest, gs, lc, F, h => by
    simp only [Ctx.fill, List.append_assoc] at h
    obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre pre other_ne_ex h
    rw [List.singleton_append, okA_label_pre ht₁, okX_label] at h
    obtain ⟨⟨-, Fb, -, hb⟩, -⟩ := h
    obtain ⟨E', v, t, hab, hr, hE⟩ := client_guard hreq E gs lc Fb hb
    exact ⟨.label pre n k E' rest, v, t, hab, hr, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .handler pre n cs E rest, gs, lc, F, h => by
    simp only [Ctx.fill, List.append_assoc] at h
    obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre pre other_ne_ex h
    rw [List.singleton_append, okA_handler_pre ht₁, okX_handler] at h
    obtain ⟨⟨Fb, -, hb⟩, -⟩ := h
    obtain ⟨E', v, t, hab, hr, hE⟩ := client_guard hreq E gs lc Fb hb
    exact ⟨.handler pre n cs E' rest, v, t, hab, hr, fun Y => by simp [Ctx.fill, hE Y]⟩
  | .frame pre n fr E rest, gs, lc, F, h => by
    simp only [Ctx.fill, List.append_assoc] at h
    obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre pre other_ne_ex h
    rw [List.singleton_append, okA_frame_pre ht₁, okX_frame] at h
    obtain ⟨⟨Fb, -, hb⟩, -⟩ := h
    obtain ⟨E', v, t, hab, hr, hE⟩ := client_guard hreq E _ _ Fb hb
    exact ⟨.frame pre n fr E' rest, v, t, hab, hr, fun Y => by simp [Ctx.fill, hE Y]⟩

/-! ## One step -/

theorem toAdmin_codeIn {r : Result} (hr : RefsOK G r) :
    CodeIn G fs (CallPl G (isBadC I.store ia iu if_) fs) r.toAdmin :=
  Silmaril.Wasm.Verify.CodeIn.toAdmin (show ∀ x ∈ codeRefs r.toAdmin, RefIn G x from hr)

theorem host_false_of {s : Store Nat} {i j a : Nat} (hi : isHost s i a = true) (hij : j ≠ i) :
    isHost s j a = false := by
  cases h : isHost s j a
  · rfl
  · exact absurd (isHost_unique h hi) hij

section Guard
variable {L : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {x : FuncIdx} {a : Nat}
  {d : DefType}

/-- At a use: the guarded thread. -/
theorem guarded_use (hR : ClientCore I G fs ia iu if_ ps)
    (hc₀ : InvC I G fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩) (hx : fs[x.toNat]? = some a)
    (ha : isBadC I.store ia iu if_ a = true) (hU : isHost I.store iu a = true) :
    GuardedC I G fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hF' := host_false_of hU (Ne.symm hR.dUF)
  have hA' := host_false_of hU hR.dAU
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgOf I.store fs ia iu if_ ps)
    (fun t ht e => by subst e; simp [callReq, hx, cfgOf, hU] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgOf, hU, ↓reduceIte, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hreq
    rcases hreq with rfl | rfl
    · exact hab.1
    · exact hab
  have hc₁ : InvC I G fs ia iu if_ ps L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun _ => ⟨v, rfl, hv, fun r hr => ?_⟩, fun h => ?_, fun h => ?_⟩
  · exact invC_fill hc₁ (fun s f => hole_use hx hU v r) (toAdmin_codeIn hr)
  · rw [hF'] at h; cases h
  · rw [hA'] at h; cases h

/-- At a free: the guarded thread. -/
theorem guarded_free (hR : ClientCore I G fs ia iu if_ ps)
    (hc₀ : InvC I G fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩) (hx : fs[x.toNat]? = some a)
    (ha : isBadC I.store ia iu if_ a = true) (hU' : isHost I.store iu a = false)
    (hFr : isHost I.store if_ a = true) :
    GuardedC I G fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA' := host_false_of hFr hR.dAF
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgOf I.store fs ia iu if_ ps)
    (fun t ht e => by subst e; simp [callReq, hx, cfgOf, hU', hFr] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgOf, hU', hFr, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hreq
    subst hreq; exact hab.1
  have hc₁ : InvC I G fs ia iu if_ ps L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun h => ?_, fun _ => ⟨v, rfl, hv, fun r hr => ?_⟩, fun h => ?_⟩
  · rw [hU'] at h; cases h
  · exact invC_fill hc₁ (fun s f => hole_free hx hU' hFr v r) (toAdmin_codeIn hr)
  · rw [hA'] at h; cases h

/-- At an allocation: the guarded thread. -/
theorem guarded_alloc (hc₀ : InvC I G fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU' : isHost I.store iu a = false) (hF' : isHost I.store if_ a = false) :
    GuardedC I G fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA : isHost I.store ia a = true := by simpa [isBadC, hU', hF'] using ha
  refine ⟨E, [], a, d, ha, by simp [vals], fun h => ?_, fun h => ?_, fun _ => ⟨rfl, ?_, ?_⟩⟩
  · rw [hU'] at h; cases h
  · rw [hF'] at h; cases h
  · intro h hh hr
    exact invC_fill hc₀ (fun s f => hole_alloc hx hU' hF' hA hh) (toAdmin_codeIn hr)
  · intro r hr hnv
    refine invC_fill hc₀ (fun s f => ?_) (toAdmin_codeIn hr)
    cases r with
    | values ws => exact absurd rfl (hnv ws)
    | trap => exact post_trapR rfl
    | throw b => exact post_throwingR rfl b

end Guard

/-- A call of one of the three imports leads to a guarded thread. -/
theorem guardedC_of_badStep (hR : ClientCore I G fs ia iu if_ ps) {L : List Val} {c c' : Config Nat}
    (hc : InvC I G fs ia iu if_ ps L c)
    (hb : BadStep (fun a => isBadC I.store ia iu if_ a = true) fs c c') :
    GuardedC I G fs ia iu if_ ps L c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  have hc₀ : InvC I G fs ia iu if_ ps L ⟨c.store, c.frame, E.fill [.plain (.call x)]⟩ := by
    rw [← hcode]; exact hc
  by_cases hU : isHost I.store iu a = true
  · exact guarded_use hR hc₀ hx ha hU
  · have hU' : isHost I.store iu a = false := by simpa using hU
    by_cases hFr : isHost I.store if_ a = true
    · exact guarded_free hR hc₀ hx ha hU' hFr
    · exact guarded_alloc hc₀ hx ha hU' (by simpa using hFr)

theorem avoids_cfg (hR : ClientCore I G fs ia iu if_ ps) (a : Nat) (ha : G a) :
    (cfgOf I.store fs ia iu if_ ps).isU a = false ∧ (cfgOf I.store fs ia iu if_ ps).isF a = false ∧
      (cfgOf I.store fs ia iu if_ ps).isA a = false :=
  ⟨isHost_false_of_avoids hR.avU ha, isHost_false_of_avoids hR.avF ha,
    isHost_false_of_avoids hR.avA ha⟩

/-- **One host-free step from an invariant thread** (every profile). -/
theorem step_invC (hR : ClientCore I G fs ia iu if_ ps) {L : List Val} {P : Profile}
    {c c' : Config Nat} (h : Step P (fun _ _ _ _ => False) c c')
    (hf : c.store.funcs = I.store.funcs) (hc : InvC I G fs ia iu if_ ps L c) :
    (InvC I G fs ia iu if_ ps L c' ∨ GuardedC I G fs ia iu if_ ps L c') ∧
      c'.store.funcs = c.store.funcs := by
  have hcl : FuncsClosed G fs (CallPl G (isBadC I.store ia iu if_) fs) c.store.funcs :=
    hf ▸ hR.closed
  have hbf : BodiesC G (cfgOf I.store fs ia iu if_ ps) c.store.funcs := hf ▸ hR.bodies
  obtain ⟨hc' | hb, hfun⟩ := Silmaril.Wasm.Verify.Step.cfgIn callPl_plainOK hostIn_noHost h hcl hc.1
  · refine ⟨.inl ?_, hfun⟩
    have hp := Step.client (C := cfgOf I.store fs ia iu if_ ps) (L := L) h hR.pairs rfl
      (avoids_cfg hR) hc.1 hc' hbf
    obtain ⟨-, hS, F, hF, hok⟩ := hc
    obtain ⟨hS', F', hF', hok'⟩ := hp F .other [] other_ne_ex hS hF (by simpa using hok)
    exact ⟨hc', hS', F', hF', by simpa using hok'⟩
  · exact ⟨.inr (guardedC_of_badStep hR hc hb), hfun⟩

end

/-! ## Threads, callouts and resumptions -/

section Threads
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {ia iu if_ : Nat}
  {ps : List (Nat × Nat)}

theorem invC_invoke {L : List Val} {s : Store Nat} (hs : StoreIn G s) (hS : Sigma ps L s.globals)
    {a : Nat} (ha : G a) {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) :
    InvC I G fs ia iu if_ ps L (invoke s a args) := by
  refine ⟨invoke_cfgIn hs ha hargs, hS, [], SoundF_nil, ?_⟩
  have h := freeP_vals (C := cfgOf I.store fs ia iu if_ ps) (V := vals args ++ [.ref (.func a)])
    (R := [.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]) (fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; simp
      · simp only [List.mem_singleton] at hy; subst hy; simp)
    (freeP_nest trivial fun _ _ _ _ => trivial) L s.globals ({} : Frame).module.globals
    ({} : Frame).locals [] []
    trivial
  simpa [invoke] using h

/-- Resuming an invariant thread at a host callout keeps the invariant. -/
theorem resume_invC {L : List Val} {s : Store Nat} {t : Thread}
    (hc : InvC I G fs ia iu if_ ps L (t.config s)) (r : Result) (hr : RefsOK G r) :
    InvC I G fs ia iu if_ ps L ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, yy, _, _, _, _, hyy, _, _, hfill⟩ := decompose?_sound hd
    have h₀ : t.config s = ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      cases t <;> rfl
    have hc' : InvC I G fs ia iu if_ ps L
        ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := h₀ ▸ hc
    exact invC_fill hc' (fun _ _ => hole_host hyy r) (toAdmin_codeIn hr)

/-- A guarded thread is at a callout of the import whose host it calls. -/
theorem guarded_decompose (hR : ClientCore I G fs ia iu if_ ps) {c : Config Nat}
    (hf : c.store.funcs = I.store.funcs) {E : Ctx} {args : List Val} {b i : Nat} {d : DefType}
    (hb : isHost I.store i b = true)
    (har : ∀ hi : i < I.imports.length, (I.imports.get ⟨i, hi⟩).params.length = args.length)
    (hcode : c.code = E.fill (vals args ++ [.ref (.func b), .callRefType d])) :
    decompose? c.store c.code = some (E, b, i, args) := by
  obtain ⟨fi, hfi, hhost⟩ := isHost_iff.1 hb
  obtain ⟨hlt, hexp⟩ := hR.ok.host_type b fi i hfi hhost
  have hfi' : c.store.funcs[b]? = some fi := hf ▸ hfi
  have hn : args.length =
      (Ty.ofList ((I.imports.get ⟨i, hlt⟩).params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList, List.length_map, har hlt]
  rw [hcode]
  exact decompose_fill hfi' hexp hhost (c := .callRefType d) trivial hn E

/-- The import of a guarded thread, with its decomposition. -/
theorem guarded_cases (hR : ClientCore I G fs ia iu if_ ps) {L : List Val} {c : Config Nat}
    (hf : c.store.funcs = I.store.funcs) (hg : GuardedC I G fs ia iu if_ ps L c) :
    ∃ (E : Ctx) (b : Nat),
      (∃ v, isHost I.store iu b = true ∧ decompose? c.store c.code = some (E, b, iu, [v]) ∧
        v ∈ L ∧ ∀ r, RefsOK G r →
          InvC I G fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (∃ v, isHost I.store if_ b = true ∧ decompose? c.store c.code = some (E, b, if_, [v]) ∧
        v ∈ L ∧ ∀ r, RefsOK G r →
          InvC I G fs ia iu if_ ps (L.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (isHost I.store ia b = true ∧ decompose? c.store c.code = some (E, b, ia, []) ∧
        (∀ h, h ∉ L → RefsOK G (.values [h]) →
          InvC I G fs ia iu if_ ps (h :: L) ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
        (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
          InvC I G fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩)) := by
  obtain ⟨E, args, b, d, hbad, hcode, hU, hF, hA⟩ := hg
  refine ⟨E, b, ?_⟩
  simp only [isBadC, Bool.or_eq_true] at hbad
  rcases hbad with (h | h) | h
  · obtain ⟨rfl, h₁, h₂⟩ := hA h
    exact .inr (.inr ⟨h, guarded_decompose hR hf h (fun hi => (hR.arA hi).1) hcode, h₁, h₂⟩)
  · obtain ⟨v, rfl, hv, hr⟩ := hU h
    exact .inl ⟨v, h, guarded_decompose hR hf h (fun hi => hR.arU hi) hcode, hv, hr⟩
  · obtain ⟨v, rfl, hv, hr⟩ := hF h
    exact .inr (.inl ⟨v, h, guarded_decompose hR hf h (fun hi => hR.arF hi) hcode, hv, hr⟩)

theorem guarded_callout (hR : ClientCore I G fs ia iu if_ ps) {L : List Val} {s : Store Nat}
    {t : Thread} (hf : s.funcs = I.store.funcs) (hg : GuardedC I G fs ia iu if_ ps L (t.config s)) :
    ∃ h args, CalloutAt s t h args := by
  have hf' : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hf
  obtain ⟨E, b, ⟨v, -, hd, -⟩ | ⟨v, -, hd, -⟩ | ⟨-, hd, -⟩⟩ := guarded_cases hR hf' hg <;>
    rw [Thread.config_store] at hd <;> exact ⟨_, _, E, b, hd⟩

end Threads

/-! ## The protocol invariant -/

section LTS
variable {I : ScalarInstance} {G : Nat → Prop} {fs : List Nat} {ps : List (Nat × Nat)}
  {ia iu if_ : (ifaceOf I).Imp}

/-- The client sentence on the moves of the instance. -/
abbrev πC (I : ScalarInstance) (ia iu if_ : (ifaceOf I).Imp) :
    Protocol (Option (List Val)) (Move I.E I.F) :=
  (clientSpec ia iu if_).comap (moveEvent (X := ifaceOf I))

/-- The invariant of a resumed thread. -/
def JR (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) : Option (List Val) → Config Nat → Prop
  | none, _ => True
  | some L, c => InvC I G fs ia iu if_ ps L c

/-- **The protocol invariant**: everything holds after an environment fault (`none`); otherwise
the client invariant of the hidden state for the live list. -/
def JC (I : ScalarInstance) (G : Nat → Prop) (fs : List Nat) (ia iu if_ : (ifaceOf I).Imp)
    (ps : List (Nat × Nat)) : Option (List Val) → I.HState → Prop
  | none, _ => True
  | some L, .idle s => StoreIn G s ∧ s.funcs = I.store.funcs ∧ Sigma ps L s.globals
  | some L, .running _ s t =>
    (InvC I G fs ia.val iu.val if_.val ps L (t.config s) ∨
      GuardedC I G fs ia.val iu.val if_.val ps L (t.config s)) ∧ s.funcs = I.store.funcs
  | some L, .waiting _ s t e => s.funcs = I.store.funcs ∧
    ∀ (v : I.E.Ar e) (q' : Option (List Val)), (πC I ia iu if_).step (some L) (.inl (.ans e v)) =
      some q' → JR I G fs ia.val iu.val if_.val ps q'
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) v)).config s)

theorem fin_ne {n : Nat} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (e ▸ rfl)

theorem step_skip (L : List Val) (m : Move I.E I.F)
    (hm : clientEv ia iu if_ (moveEvent m) = .skip) :
    (πC I ia iu if_).step (some L) m = some (some L) := by
  show handleStep .client (some L) (clientEv ia iu if_ (moveEvent m)) = _
  rw [hm]; rfl

theorem step_none (m : Move I.E I.F) : (πC I ia iu if_).step none m = some none := rfl

theorem ite_t' {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : c) :
    @ite α c inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

theorem ite_f' {α : Type} {c : Prop} {inst : Decidable c} {a b : α} (h : ¬ c) :
    @ite α c inst a b = b := by
  cases inst with
  | isTrue hc => exact absurd hc h
  | isFalse _ => rfl

/-- Answers of imports other than the allocator, export moves: skipped. -/
theorem ev_ans_ne {e : I.E.Op} (w : I.E.Ar e) (h : e.1 ≠ ia) :
    clientEv ia iu if_ (moveEvent (X := ifaceOf I) (.inl (.ans e w))) = .skip := by
  simp only [moveEvent, evOf, Sum.map_inl, clientEv]
  exact ite_f' h

theorem ev_ask_ne {e : I.E.Op} (hu : e.1 ≠ iu) (hf : e.1 ≠ if_) :
    clientEv ia iu if_ (moveEvent (X := ifaceOf I) (.inl (.ask e))) = .skip := by
  simp only [moveEvent, evOf, Sum.map_inl, clientEv]
  exact (ite_f' hu).trans (ite_f' hf)

theorem step_eq_skip {L : List Val} {m : Move I.E I.F} {q' : Option (List Val)}
    (hm : clientEv ia iu if_ (moveEvent m) = .skip)
    (h : (πC I ia iu if_).step (some L) m = some q') : q' = some L :=
  Option.some.inj (h.symm.trans (step_skip L m hm))

theorem step_use {L : List Val} {e : I.E.Op} {v : Val} (he : @Eq (ifaceOf I).Imp e.1 iu)
    (hargs : e.2.1 = [v]) (hv : v ∈ L) :
    (πC I ia iu if_).step (some L) (.inl (.ask e)) = some (some L) := by
  change handleStep .client (some L) (clientEv ia iu if_ (moveEvent (X := ifaceOf I) (.inl (.ask e))))
    = _
  simp only [moveEvent, evOf, Sum.map_inl, clientEv]
  rw [ite_t' he, hargs]
  simp [HEv.useOf, handleStep, hv]

theorem step_free {L : List Val} {e : I.E.Op} {v : Val} (he : @Eq (ifaceOf I).Imp e.1 if_)
    (hne : if_ ≠ iu) (hargs : e.2.1 = [v]) (hv : v ∈ L) :
    (πC I ia iu if_).step (some L) (.inl (.ask e)) = some (some (L.erase v)) := by
  change handleStep .client (some L) (clientEv ia iu if_ (moveEvent (X := ifaceOf I) (.inl (.ask e))))
    = _
  simp only [moveEvent, evOf, Sum.map_inl, clientEv]
  have hne' : ¬ (@Eq (ifaceOf I).Imp e.1 iu) := fun h => hne (by rw [← he]; exact h)
  rw [ite_f' hne', ite_t' he, hargs]
  simp [HEv.freeOf, handleStep, hv]

theorem step_alloc {L : List Val} {e : I.E.Op} {w : I.E.Ar e} (he : @Eq (ifaceOf I).Imp e.1 ia) :
    (πC I ia iu if_).step (some L) (.inl (.ans e w)) =
      handleStep .client (some L) (HEv.allocOf (Answer.toBehaviour w)) := by
  change handleStep .client (some L) (clientEv ia iu if_ (moveEvent (X := ifaceOf I) (.inl (.ans e w))))
    = _
  simp only [moveEvent, evOf, Sum.map_inl, clientEv]
  exact congrArg (handleStep .client (some L)) (ite_t' he)

section Vis
variable {f : I.F.Op} {s : Store Nat} {t : Thread} {e : I.E.Op} {L : List Val}

/-- A callout of an invariant thread: another import, skipped by the protocol. -/
theorem vis_ucall_inv (hR : ClientIn I G fs ia.val iu.val if_.val ps) {h : Nat} {args : List Val}
    (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : InvC I G fs ia.val iu.val if_.val ps L (t.config s)) (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JC I G fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨a, fi, ha, hf, hcode⟩ := callout_mem callout hy.1
  have he := ifaceOp?_fst op
  have hne : ∀ j : (ifaceOf I).Imp, ∀ hav : Avoids G I.store.funcs j.val, e.1 ≠ j :=
    fun j hav ej => hav a fi ha (hfy ▸ hf) (by rw [hcode, ← he, ej])
  refine ⟨some L, step_skip L _ (ev_ask_ne (ia := ia) (hne _ hR.avU) (hne _ hR.avF)), hfy, ?_⟩
  intro w q' hq'
  obtain rfl := step_eq_skip (ev_ans_ne (iu := iu) (if_ := if_) w (hne _ hR.avA)) hq'
  exact resume_invC hy _ (answer_refIn w)

/-- The answer of a use or a free: skipped by the protocol, the prepared resumption. -/
theorem vis_ret_skip {L' : List Val} {E : Ctx} {b : Nat} {args : List Val} (he : e.1 ≠ ia)
    (hd : decompose? s (t.config s).code = some (E, b, iu.val, args) ∨
      decompose? s (t.config s).code = some (E, b, if_.val, args))
    (hres : ∀ r, RefsOK G r →
      InvC I G fs ia.val iu.val if_.val ps L' ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∀ (w : I.E.Ar e) (q' : Option (List Val)),
      (πC I ia iu if_).step (some L') (.inl (.ans e w)) = some q' →
      JR I G fs ia.val iu.val if_.val ps q'
        ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  intro w q' hq'
  obtain rfl := step_eq_skip (ev_ans_ne (iu := iu) (if_ := if_) w he) hq'
  rcases hd with hd | hd <;>
  · rw [resumeResult_config hd]
    exact hres _ (answer_refIn w)

/-- The answer of an allocation. -/
theorem vis_ret_alloc (hR : ClientIn I G fs ia.val iu.val if_.val ps) {E : Ctx} {b : Nat}
    (he1 : @Eq (ifaceOf I).Imp e.1 ia) (hd : decompose? s (t.config s).code = some (E, b, ia.val, []))
    (hres₁ : ∀ h, h ∉ L → RefsOK G (.values [h]) → InvC I G fs ia.val iu.val if_.val ps (h :: L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvC I G fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩)
    (w : I.E.Ar e) (q' : Option (List Val))
    (hq' : (πC I ia iu if_).step (some L) (.inl (.ans e w)) = some q') :
    JR I G fs ia.val iu.val if_.val ps q'
      ((resumeResult s t (Answer.toResult (ft := I.imports.get e.1) w)).config s) := by
  rw [step_alloc he1] at hq'
  rw [resumeResult_config hd]
  cases w with
  | values vs =>
    obtain ⟨ws, hws⟩ := vs
    have hres : (I.imports.get e.1).results.length = 1 := by
      have he' : e.1 = ⟨ia.val, ia.isLt⟩ := Fin.ext (congrArg Fin.val he1)
      rw [he']; exact (hR.arA ia.isLt).2
    obtain ⟨h₁, rfl⟩ := List.length_eq_one_iff.1 ((List.Forall₂.length_eq hws).symm.trans hres)
    by_cases hh : h₁ ∈ L
    · simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep, hh, fault] at hq'
      subst hq'; trivial
    · simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep, hh] at hq'
      subst hq'
      exact hres₁ h₁ hh (answer_refIn (Answer.values (ft := I.imports.get e.1) ⟨[h₁], hws⟩))
  | trap =>
    simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep] at hq'
    subst hq'
    exact hres₂ .trap (answer_refIn (Answer.trap (ft := I.imports.get e.1))) (fun _ => nofun)
  | throw a =>
    simp [Answer.toBehaviour, Answer.toResult, HEv.allocOf, handleStep] at hq'
    subst hq'
    exact hres₂ (.throw a) (answer_refIn (Answer.throw (ft := I.imports.get e.1) a)) (fun _ => nofun)

/-- The decomposition of a guarded thread is the callout's. -/
theorem callout_eq {h₀ : Nat} {args args₀ : List Val} {E E₀ : Ctx} {a₀ b h : Nat}
    (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args₀))
    (hd : decompose? s (t.config s).code = some (E, b, h₀, args)) : h = h₀ ∧ args₀ = args := by
  have heq := Option.some.inj (hd₀.symm.trans hd)
  simp only [Prod.mk.injEq] at heq
  exact ⟨heq.2.2.1, heq.2.2.2⟩

theorem vis_use (hR : ClientIn I G fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx} {a₀ b : Nat}
    {args : List Val} {v : Val} (op : I.importOp? h args = some e) (hfy : s.funcs = I.store.funcs)
    (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, iu.val, [v])) (hv : v ∈ L)
    (hres : ∀ r, RefsOK G r →
      InvC I G fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JC I G fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 iu := Fin.ext (ifaceOp?_fst op)
  exact ⟨some L, step_use he1 (ifaceOp?_snd op) hv, hfy,
    vis_ret_skip (fun h' => hR.dAU (by rw [← h', he1])) (.inl hd) hres⟩

theorem vis_free (hR : ClientIn I G fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx}
    {a₀ b : Nat} {args : List Val} {v : Val} (op : I.importOp? h args = some e)
    (hfy : s.funcs = I.store.funcs) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, if_.val, [v])) (hv : v ∈ L)
    (hres : ∀ r, RefsOK G r →
      InvC I G fs ia.val iu.val if_.val ps (L.erase v) ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JC I G fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 if_ := Fin.ext (ifaceOp?_fst op)
  exact ⟨some (L.erase v), step_free he1 (fin_ne (Ne.symm hR.dUF)) (ifaceOp?_snd op) hv, hfy,
    vis_ret_skip (fun h' => hR.dAF (by rw [← h', he1])) (.inr hd) hres⟩

theorem vis_alloc (hR : ClientIn I G fs ia.val iu.val if_.val ps) {h : Nat} {E₀ E : Ctx}
    {a₀ b : Nat} {args : List Val} (op : I.importOp? h args = some e)
    (hfy : s.funcs = I.store.funcs) (hd₀ : decompose? s (t.config s).code = some (E₀, a₀, h, args))
    (hd : decompose? s (t.config s).code = some (E, b, ia.val, []))
    (hres₁ : ∀ h, h ∉ L → RefsOK G (.values [h]) → InvC I G fs ia.val iu.val if_.val ps (h :: L)
      ⟨s, (t.config s).frame, E.fill (Result.values [h]).toAdmin⟩)
    (hres₂ : ∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
      InvC I G fs ia.val iu.val if_.val ps L ⟨s, (t.config s).frame, E.fill r.toAdmin⟩) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JC I G fs ia iu if_ ps q' (.waiting f s t e) := by
  obtain ⟨rfl, rfl⟩ := callout_eq hd₀ hd
  have he1 : @Eq (ifaceOf I).Imp e.1 ia := Fin.ext (ifaceOp?_fst op)
  exact ⟨some L, step_skip L _ (ev_ask_ne (ia := ia) (fun h' => hR.dAU (by rw [← h', he1]))
    (fun h' => hR.dAF (by rw [← h', he1]))), hfy, vis_ret_alloc hR he1 hd hres₁ hres₂⟩

/-- A callout of a guarded thread: a use, a free or an allocation. -/
theorem vis_ucall_guard (hR : ClientIn I G fs ia.val iu.val if_.val ps) {h : Nat}
    {args : List Val} (callout : CalloutAt s t h args) (op : I.importOp? h args = some e)
    (hy : GuardedC I G fs ia.val iu.val if_.val ps L (t.config s)) (hfy : s.funcs = I.store.funcs) :
    ∃ q', (πC I ia iu if_).step (some L) (.inl (.ask e)) = some q' ∧
      JC I G fs ia iu if_ ps q' (.waiting f s t e) := by
  have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
  obtain ⟨E₀, a₀, hd₀⟩ := callout
  obtain ⟨E, b, ⟨v, -, hd, hv, hres⟩ | ⟨v, -, hd, hv, hres⟩ | ⟨-, hd, hres₁, hres₂⟩⟩ :=
    guarded_cases hR.toClientCore hf₀ hy
  · exact vis_use hR op hfy hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact vis_free hR op hfy hd₀ (by simpa [Thread.config_store] using hd) hv
      (by simpa [Thread.config_store] using hres)
  · exact vis_alloc hR op hfy hd₀ (by simpa [Thread.config_store] using hd)
      (by simpa [Thread.config_store] using hres₁) (by simpa [Thread.config_store] using hres₂)

/-- A finished thread is not guarded; its store is invariant. -/
theorem vis_oret (hR : ClientIn I G fs ia.val iu.val if_.val ps) {r : Result}
    (final : ResultAt s t r)
    (hx : (InvC I G fs ia.val iu.val if_.val ps L (t.config s) ∨
      GuardedC I G fs ia.val iu.val if_.val ps L (t.config s)) ∧ s.funcs = I.store.funcs) :
    StoreIn G s ∧ s.funcs = I.store.funcs ∧ Sigma ps L s.globals := by
  obtain ⟨hy | hy, hfy⟩ := hx
  · exact ⟨Thread.config_store s t ▸ hy.1.1, hfy, Thread.config_store s t ▸ hy.2.1⟩
  · have hf₀ : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hfy
    obtain ⟨E, b, ⟨v, -, hd, -⟩ | ⟨v, -, hd, -⟩ | ⟨-, hd, -⟩⟩ := guarded_cases hR.toClientCore hf₀ hy <;>
      · rw [final, decompose_toAdmin_none] at hd
        cases hd

end Vis

/-- The vis steps. -/
theorem jc_vis (hR : ClientIn I G fs ia.val iu.val if_.val ps) {P : Profile} {q : Option (List Val)}
    {x y : I.HState} {o : Move I.E I.F} (hs : I.DTrans P x (some o) y) (hx : JC I G fs ia iu if_ ps q x) :
    ∃ q', (πC I ia iu if_).step q o = some q' ∧ JC I G fs ia iu if_ ps q' y := by
  rcases q with _ | L
  · exact ⟨none, step_none o, trivial⟩
  cases hs with
  | call s f =>
    exact ⟨some L, step_skip L _ rfl,
      .inl (invC_invoke hx.1 hx.2.2 (hR.exports f.1) (typed_refIn f.2.2)), hx.2.1⟩
  | ucall callout op =>
    exact hx.1.elim (fun hy => vis_ucall_inv hR callout op hy hx.2)
      (fun hy => vis_ucall_guard hR callout op hy hx.2)
  | uret v =>
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (clientSpec_oTotal ia iu if_ (some L) (.inl (.ans _ v)) trivial)
    exact ⟨q', hq', match q' with
      | none => trivial
      | some _ => ⟨.inl (hx.2 v _ hq'), hx.1⟩⟩
  | oret final answer => exact ⟨some L, step_skip L _ rfl, vis_oret hR final hx⟩

/-- **The protocol invariant of the instance's transition system** (every profile). -/
def clientLTSInv (hR : ClientIn I G fs ia.val iu.val if_.val ps) (P : Profile) :
    LTSInv (I.dlts P I.store) (πC I ia iu if_) where
  J := JC I G fs ia iu if_ ps
  init := by
    refine ⟨hR.store, rfl, fun p hp hon => ?_⟩
    obtain ⟨v, hv, hv0⟩ := hon
    rw [hR.init p hp] at hv; cases hv; exact absurd rfl hv0
  tau := by
    intro q x y hst hx
    rcases q with _ | L
    · trivial
    cases hst with
    | @tau f s s' t t' h =>
      obtain ⟨hy | hy, hfy⟩ := hx
      · obtain ⟨f', code', ht', hstep⟩ := h
        have hf₀ : (t.config s).store.funcs = I.store.funcs := by
          rw [Thread.config_store]; exact hfy
        obtain ⟨hz, hfz⟩ := step_invC hR.toClientCore hstep hf₀ hy
        subst ht'
        exact ⟨hz, hfz.trans hf₀⟩
      · obtain ⟨hh, _, hc⟩ := guarded_callout hR.toClientCore hfy hy
        exact absurd h (calloutAt_no_internal hc _)
  vis := fun hst hx => jc_vis hR hst hx

/-- **Soundness of the client analysis** (every profile): every play of the instance is accepted
by the client sentence. -/
theorem clientIn_accepts (hR : ClientIn I G fs ia.val iu.val if_.val ps) (P : Profile) :
    ∀ p ∈ I.strategy P I.store, (πC I ia iu if_).Accepts p :=
  dlts_accepts (clientLTSInv hR P) (clientSpec_oTotal ia iu if_)

/-- **The client sentence over `wasmSem P`** (every profile). -/
theorem clientIn_sound (hR : ClientIn I G fs ia.val iu.val if_.val ps) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (WasmProg.ofInstance I) (clientSpec ia iu if_) :=
  models_of_plays _ _ (clientIn_accepts hR P)

end LTS

/-! ## The checker -/

section Check
open Silmaril.Wasm.Verify (instOf progOf instance? isInstance_instOf mem_exprRF mem_exprCalls
  storeIn_of_rootsB addr_mem_roots avoidsB_sound rootsB PlOK)

theorem funcOkC_sound {s : Store Nat} {fs G : List Nat} {ia iu if_ : Nat} {ps : List (Nat × Nat)}
    {a : Nat} {fi : FuncInst Nat} {code : Func} (h : funcOkC s fs G ia iu if_ ps a = true)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    fi.module.funcs = fs ∧
      (∀ ins ∈ code.body, PlOK (CallPl (· ∈ G) (isBadC s ia iu if_) fs) ins) ∧
      okL (cfgOf s fs ia iu if_ ps) fi.module.globals [] .other code.body = true := by
  simp only [funcOkC, hf, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hm, hrf⟩, hcall⟩, hok⟩ := h
  refine ⟨hm, fun ins hins => .inr ⟨fun x hx b hb => ?_, fun x hx b hb => ?_⟩, hok⟩
  · simpa [hb] using hrf x (mem_exprRF hins hx)
  · have h₁ := hcall x (mem_exprCalls hins hx)
    simpa only [hb, Bool.or_eq_true, List.contains_iff_mem] using h₁

theorem arity_of {I : ScalarInstance} {i n : Nat} (h : (importArity I i).map (·.1) == some n)
    (hi : i < I.imports.length) : (I.imports.get ⟨i, hi⟩).params.length = n := by
  simp only [importArity, beq_iff_eq, Option.map_map] at h
  simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq,
    Function.comp] at h
  simpa using h

theorem arity_res {I : ScalarInstance} {i n : Nat} (h : (importArity I i).map (·.2) == some n)
    (hi : i < I.imports.length) : (I.imports.get ⟨i, hi⟩).results.length = n := by
  simp only [importArity, beq_iff_eq, Option.map_map] at h
  simp only [List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq,
    Function.comp] at h
  simpa using h

/-- **The checker establishes `ClientIn`.** -/
theorem clientIn_of_checkInst {I : ScalarInstance} (hok : I.Ok) {ia iu if_ : Nat}
    {ps : List (Nat × Nat)} (h : checkInst I ia iu if_ ps = true) :
    ClientIn I (· ∈ reachC I ia iu if_) (fsOf I) ia iu if_ ps := by
  simp only [checkInst, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hAU, hAF⟩, hUF⟩, haA⟩, hrA⟩, haU⟩, haF⟩, hP⟩, hinit⟩, hfun⟩, hroots⟩,
    hvA⟩, hvU⟩, hvF⟩ := h
  refine ⟨⟨hok, fun a fi code ha hf hcode => ?_, fun a fi code ha hf hcode => ?_,
    storeIn_of_rootsB hroots, avoidsB_sound hvA, avoidsB_sound hvU,
    avoidsB_sound hvF, hP, fun p hp => by simpa using hinit p hp, hAU, hAF, hUF,
    fun hi => ⟨arity_of haA hi, arity_res hrA hi⟩, fun hi => arity_of haU hi,
    fun hi => arity_of haF hi⟩, addr_mem_roots hok hroots⟩
  · obtain ⟨h₁, h₂, -⟩ := funcOkC_sound (hfun a ha) hf hcode
    exact ⟨h₁, h₂⟩
  · exact (funcOkC_sound (hfun a ha) hf hcode).2.2

/-- **Soundness of the client checker on a module** (every profile, no determinism assumed). -/
theorem checkClient_sound {m : Module} {ia iu if_ : (ifaceOf (instOf m)).Imp}
    {ps : List (Nat × Nat)} (h : checkClient m ia.val iu.val if_.val ps = true) (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf m) (clientSpec ia iu if_) := by
  simp only [checkClient, Bool.and_eq_true] at h
  obtain ⟨mt, hI⟩ := isInstance_instOf h.1
  exact clientIn_sound (clientIn_of_checkInst hI.ok h.2) P

end Check

end Silmaril.Wasm.Resource.Client
