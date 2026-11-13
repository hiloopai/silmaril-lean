module

public import Silmaril.Wasm.Resource.ClientArg.Defs
public import Silmaril.Wasm.Resource.Client.Thms
public import Silmaril.Wasm.Game.ULink.Fill.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Handles passed to internal callees: threads

`ArgCore`: what the check with helpers establishes at the thread level. `InvH`: the client
invariant (`Silmaril.Wasm.Resource.Client`) with the helpers `H` as further callable functions
(`badH`) and the configuration `cfgH`. `GuardedH`: a thread stopped at a call of one of the
three imports. `EnterH`: **a thread between the call of a helper and the entry of its frame**,
`E.fill (vals [v] ++ [ref.func b, call_ref])`, with the entered configuration invariant.

* `enterH_of_badStep`: the `call` of a helper checked with a handle on top (`fr`) leads to an
  entering thread; its frame starts from the entry fact `loc 0` (`hole_helper`).
* `enterH_step`: the only step of an entering thread enters the frame (by
  `Silmaril.Wasm.Game.ULink.step_fill_call` and `Silmaril.Wasm.Logic.Hoare.call_step_inv`).
* `step_invH`: every host-free step of an invariant thread keeps the invariant, or reaches a
  guarded or an entering thread.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ClientArg

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn FuncsClosed CallPl Avoids isHost PlOK
  BadStep callPl_plainOK hostIn_noHost invoke_cfgIn isHost_iff decompose_fill codeRefs_fill)

/-- The callable functions outside `G`, as a predicate. -/
abbrev BadP (I : ScalarInstance) (ia iu if_ : Nat) (H : List Nat) (a : Nat) : Prop :=
  badH I.store ia iu if_ H a = true

/-- **What the check with helpers establishes**, at the thread level. -/
structure ArgCore (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat)
    (ia iu if_ : Nat) (ps : List (Nat × Nat)) : Prop where
  ok : I.Ok
  closed : FuncsClosed G fs (CallPl G (badH I.store ia iu if_ H) fs) I.store.funcs
  bodies : BodiesC G (cfgH I.store fs ia iu if_ ps H) I.store.funcs
  helpers : ∀ b ∈ H, ∃ (fi : FuncInst Nat) (code : Func) (pt rt : Ty (.list .val)),
    I.store.funcs[b]? = some fi ∧ fi.code = .wasm code ∧ Expand fi.type (.func pt rt) ∧
    pt.length = 1 ∧ fi.module.funcs = fs ∧
    (∀ i ∈ code.body, PlOK (CallPl G (badH I.store ia iu if_ H) fs) i) ∧
    okL (cfgH I.store fs ia iu if_ ps H) fi.module.globals [.loc 0] .other code.body = true
  store : StoreIn G I.store
  avA : Avoids G I.store.funcs ia
  avU : Avoids G I.store.funcs iu
  avF : Avoids G I.store.funcs if_
  avH : ∀ a, G a → a ∉ H
  pairs : PairsOK ps
  init : ∀ p ∈ ps, gval I.store.globals p.1 = some (Val.i32 0)
  dAU : ia ≠ iu
  dAF : ia ≠ if_
  dUF : iu ≠ if_
  arA : ∀ h : ia < I.imports.length, (I.imports.get ⟨ia, h⟩).params.length = 0 ∧
    (I.imports.get ⟨ia, h⟩).results.length = 1
  arU : ∀ h : iu < I.imports.length, (I.imports.get ⟨iu, h⟩).params.length = 1
  arF : ∀ h : if_ < I.imports.length, (I.imports.get ⟨if_, h⟩).params.length = 1

section
variable {I : ScalarInstance} {G : Nat → Prop} {H : List Nat} {fs : List Nat} {ia iu if_ : Nat}
  {ps : List (Nat × Nat)}

/-- **The client invariant with helpers** of a running thread. -/
def InvH (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) (L : List Val) (c : Config Nat) : Prop :=
  CfgIn G fs (CallPl G (badH I.store ia iu if_ H) fs) c ∧ Sigma ps L c.store.globals ∧
    ∃ F, SoundF ps L c.store.globals c.frame.locals F ∧
      okA (cfgH I.store fs ia iu if_ ps H) L c.store.globals c.frame.module.globals c.frame.locals
        ⟨F, .other, true⟩ c.code

/-- **A thread stopped at a call of one of the three imports**, prepared for every answer. -/
def GuardedH (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat)
    (ia iu if_ : Nat) (ps : List (Nat × Nat)) (L : List Val) (c : Config Nat) : Prop :=
  ∃ (E : Ctx) (args : List Val) (b : Nat) (d : DefType), isBadC I.store ia iu if_ b = true ∧
    c.code = E.fill (vals args ++ [.ref (.func b), .callRefType d]) ∧
    (isHost I.store iu b = true → ∃ v, args = [v] ∧ v ∈ L ∧
      ∀ r, RefsOK G r → InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store if_ b = true → ∃ v, args = [v] ∧ v ∈ L ∧
      ∀ r, RefsOK G r → InvH I G H fs ia iu if_ ps (L.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∧
    (isHost I.store ia b = true → args = [] ∧
      (∀ h, h ∉ L → RefsOK G (.values [h]) →
        InvH I G H fs ia iu if_ ps (h :: L) ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
      (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
        InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩))

/-- **A thread entering a helper**: the call is pending in the context `E`, and the configuration
with the helper's frame in the hole is invariant. -/
def EnterH (I : ScalarInstance) (G : Nat → Prop) (H : List Nat) (fs : List Nat) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) (L : List Val) (c : Config Nat) : Prop :=
  ∃ (E : Ctx) (v : Val) (b : Nat) (d : DefType) (fi : FuncInst Nat) (code : Func)
    (pt rt : Ty (.list .val)),
    c.code = E.fill (vals [v] ++ [.ref (.func b), .callRefType d]) ∧ c.store.funcs[b]? = some fi ∧
    fi.code = .wasm code ∧ Expand fi.type (.func pt rt) ∧ [v].length = pt.length ∧
    InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill [Silmaril.Wasm.Logic.Hoare.callFrame fi code rt [v]]⟩

/-! ## Contexts and holes -/

theorem invH_fill {L L' : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {Y X : List Admin}
    (hc : InvH I G H fs ia iu if_ ps L ⟨s, f, E.fill Y⟩)
    (hp : ∀ (s : Store Nat) (f : Frame),
      CPost (cfgH I.store fs ia iu if_ ps H) L L' (⟨s, f, Y⟩ : Config Nat) ⟨s, f, X⟩)
    (hX : CodeIn G fs (CallPl G (badH I.store ia iu if_ H) fs) X) :
    InvH I G H fs ia iu if_ ps L' ⟨s, f, E.fill X⟩ := by
  obtain ⟨hcf, hS, F, hF, hok⟩ := hc
  obtain ⟨hS', F', hF', hok'⟩ :=
    fill_post hp E s f F .other [] other_ne_ex hS hF (by simpa using hok)
  exact ⟨⟨hcf.1, hcf.2.1, CodeIn.fill hcf.2.2 hX⟩, hS', F', hF', by simpa using hok'⟩

theorem toAdmin_codeInH {r : Result} (hr : RefsOK G r) :
    CodeIn G fs (CallPl G (badH I.store ia iu if_ H) fs) r.toAdmin :=
  Silmaril.Wasm.Verify.CodeIn.toAdmin (show ∀ x ∈ codeRefs r.toAdmin, RefIn G x from hr)

/-- The entry fact of a callee frame whose parameter is a live handle held by no flagged pair. -/
theorem soundF_entry {ps : List (Nat × Nat)} {L : List Val} {gl : List GlobalInst} {v : Val}
    {m : ModuleInst} {ls : List ValType} (hv : Ab ps L gl .fr v) :
    SoundF ps L gl (Frame.forCall m [v] ls).locals [.loc 0] := by
  intro f hf
  rw [List.mem_singleton] at hf
  subst hf
  exact ⟨v, by simp [Frame.forCall], hv.1, hv.2⟩

/-- A callee frame checked from the entry fact, followed by code checked from no facts. -/
theorem okA_callFrame {C : Cfg} {L : List Val} {gl : List GlobalInst} {gs : List Nat}
    {lc : List (Option Val)} {v : Val} {fi : FuncInst Nat} {code : Func} {rt : Ty (.list .val)}
    {l : List Admin} (hv : Ab C.ps L gl .fr v)
    (hok : okL C fi.module.globals [.loc 0] .other code.body = true)
    (hl : okA C L gl gs lc ⟨[], .other, false⟩ l) :
    okA C L gl gs lc ⟨[], .other, true⟩
      ([Silmaril.Wasm.Logic.Hoare.callFrame fi code rt [v]] ++ l) := by
  have hsound : SoundF C.ps L gl (Frame.forCall fi.module [v] code.locals).locals [.loc 0] :=
    soundF_entry hv
  have hbody : okA C L gl fi.module.globals (Frame.forCall fi.module [v] code.locals).locals
      ⟨[.loc 0], .other, true⟩ (expression code.body) := by
    simpa [vals] using okA_body (L := L) (gl := gl)
      (lc := (Frame.forCall fi.module [v] code.locals).locals) hok .other []
  show okA C L gl gs lc ⟨[], .other, true⟩
    (.frame rt.length (Frame.forCall fi.module [v] code.locals)
      [.label rt.length [] (expression code.body)] :: l)
  rw [okA_frame_pre other_ne_ex]
  refine ⟨okX_frame.2 ⟨[.loc 0], hsound, ?_⟩, hl⟩
  rw [okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, [.loc 0], hsound, hbody⟩, trivial⟩

/-- The hole of a helper call: the callee frame starts from `loc 0`. -/
theorem hole_helper {C : Cfg} {L : List Val} {s : Store Nat} {f : Frame} {x : FuncIdx} {b : Nat}
    (hx : C.fs[x.toNat]? = some b) (hU : C.isU b = false) (hFr : C.isF b = false)
    (hA : C.isA b = false) (hH : C.isH b = true) {v : Val} {fi : FuncInst Nat} {code : Func}
    {rt : Ty (.list .val)}
    (hok : okL C fi.module.globals [.loc 0] .other code.body = true) :
    CPost C L L (⟨s, f, vals [v] ++ [.plain (.call x)]⟩ : Config Nat)
      ⟨s, f, [Silmaril.Wasm.Logic.Hoare.callFrame fi code rt [v]]⟩ := by
  intro F t l ht hS hF h
  obtain ⟨t₁, hab, hreq, hl⟩ := okA_call_hole ht h
  have hfr : t₁ = .fr := by simpa [callReq, hx, hU, hFr, hH] using hreq
  have hn : callNext C F x = ([], .other) := by simp [callNext, hx, hU, hFr, hA]
  have hl' : okA C L s.globals f.module.globals f.locals ⟨[], .other, false⟩ l := by
    simpa [hn] using hl
  exact ⟨hS, [], SoundF_nil, okA_callFrame (hfr ▸ hab) hok (okA_npre_indep l hl')⟩

/-! ## The calls outside `G` -/

theorem host_false_wasm {s : Store Nat} {i b : Nat} {fi : FuncInst Nat} {code : Func}
    (hf : s.funcs[b]? = some fi) (hc : fi.code = .wasm code) : isHost s i b = false := by
  cases h : isHost s i b
  · rfl
  · obtain ⟨fi', hf', hh⟩ := isHost_iff.1 h
    rw [hf] at hf'
    cases hf'
    rw [hc] at hh
    cases hh

/-- The code of a helper's frame is in the reachable set. -/
theorem codeIn_callFrame {fi : FuncInst Nat} {code : Func} {rt : Ty (.list .val)} {v : Val} (hfs : fi.module.funcs = fs)
    (hv : ∀ r, Val.ref r ∈ [v] → RefIn G r)
    (hpl : ∀ i ∈ code.body, PlOK (CallPl G (badH I.store ia iu if_ H) fs) i) :
    CodeIn G fs (CallPl G (badH I.store ia iu if_ H) fs)
      [Silmaril.Wasm.Logic.Hoare.callFrame fi code rt [v]] :=
  CodeIn.frame_iff.2 ⟨Silmaril.Wasm.Verify.FrameIn.forCall hfs hv _,
    CodeIn.label_iff.2 ⟨by simp, CodeIn.expression hpl⟩⟩

/-- **The call of a helper leads to an entering thread.** -/
theorem enterH_of_call (hR : ArgCore I G H fs ia iu if_ ps) {L : List Val} {s : Store Nat}
    {f : Frame} {E : Ctx} {x : FuncIdx} {b : Nat} {d : DefType}
    (hc₀ : InvH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hfs : s.funcs = I.store.funcs) (hx : fs[x.toNat]? = some b) (hb : b ∈ H) :
    EnterH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func b), .callRefType d]⟩ := by
  obtain ⟨fi, code, pt, rt, hfi, hcode, hexp, hpt, hm, hpl, hok⟩ := hR.helpers b hb
  have hnh : ∀ i, isHost I.store i b = false := fun i => host_false_wasm hfi hcode
  have hH : (cfgH I.store fs ia iu if_ ps H).isH b = true := by simp [cfgH, hb]
  obtain ⟨hcf, -, F, -, hok₀⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgH I.store fs ia iu if_ ps H)
    (fun t ht e => by subst e; simp [callReq, hx, cfgH, cfgOf, hnh, hb] at ht) E _ _ F hok₀
  have hc₁ : InvH I G H fs ia iu if_ ps L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  have hv : ∀ r, Val.ref r ∈ [v] → RefIn G r := fun r hr => by
    have hr' : r ∈ codeRefs (vals [v] ++ [.plain (.call x)]) := by
      simp only [List.mem_singleton] at hr; subst hr; simp [vals, Val.toAdmin]
    exact hc₁.1.2.2.1 r (codeRefs_fill E' _ r hr')
  have hpost := invH_fill hc₁ (fun s f => hole_helper (C := cfgH I.store fs ia iu if_ ps H)
      (rt := rt) hx (hnh _) (hnh _) (hnh _) hH hok) (codeIn_callFrame hm hv hpl)
  exact ⟨E', v, b, d, fi, code, pt, rt, by rw [hE], hfs ▸ hfi, hcode, hexp, by simp [hpt], hpost⟩

/-! ## The three imports -/

section Guard
variable {L : List Val} {s : Store Nat} {f : Frame} {E : Ctx} {x : FuncIdx} {a : Nat}
  {d : DefType}

/-- At a use: the guarded thread. -/
theorem guardedH_use (hR : ArgCore I G H fs ia iu if_ ps)
    (hc₀ : InvH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU : isHost I.store iu a = true) :
    GuardedH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hF' := host_false_of hU (Ne.symm hR.dUF)
  have hA' := host_false_of hU hR.dAU
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgH I.store fs ia iu if_ ps H)
    (fun t ht e => by subst e; simp [callReq, hx, cfgH, cfgOf, hU] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgH, cfgOf, hU, ↓reduceIte, Bool.false_or, Bool.or_eq_true,
      beq_iff_eq] at hreq
    rcases hreq with rfl | rfl
    · exact hab.1
    · exact hab
  have hc₁ : InvH I G H fs ia iu if_ ps L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun _ => ⟨v, rfl, hv, fun r hr => ?_⟩,
    fun h => absurd h (by rw [hF']; exact Bool.false_ne_true),
    fun h => absurd h (by rw [hA']; exact Bool.false_ne_true)⟩
  exact invH_fill hc₁ (fun s f => hole_use hx hU v r) (toAdmin_codeInH hr)

/-- At a free: the guarded thread. -/
theorem guardedH_free (hR : ArgCore I G H fs ia iu if_ ps)
    (hc₀ : InvH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU' : isHost I.store iu a = false) (hFr : isHost I.store if_ a = true) :
    GuardedH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA' := host_false_of hFr hR.dAF
  obtain ⟨-, -, F, -, hok⟩ := id hc₀
  obtain ⟨E', v, t, hab, hreq, hE⟩ := client_guard (C := cfgH I.store fs ia iu if_ ps H)
    (fun t ht e => by subst e; simp [callReq, hx, cfgH, cfgOf, hU', hFr] at ht) E _ _ F hok
  have hv : v ∈ L := by
    simp only [callReq, hx, cfgH, cfgOf, hU', hFr, Bool.false_eq_true, ↓reduceIte,
      beq_iff_eq] at hreq
    subst hreq; exact hab.1
  have hc₁ : InvH I G H fs ia iu if_ ps L ⟨s, f, E'.fill (vals [v] ++ [.plain (.call x)])⟩ :=
    hE _ ▸ hc₀
  refine ⟨E', [v], a, d, ha, hE _, fun h => absurd h (by rw [hU']; exact Bool.false_ne_true),
    fun _ => ⟨v, rfl, hv, fun r hr => ?_⟩,
    fun h => absurd h (by rw [hA']; exact Bool.false_ne_true)⟩
  exact invH_fill hc₁ (fun s f => hole_free hx hU' hFr v r) (toAdmin_codeInH hr)

/-- At an allocation: the guarded thread. -/
theorem guardedH_alloc (hc₀ : InvH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.plain (.call x)]⟩)
    (hx : fs[x.toNat]? = some a) (ha : isBadC I.store ia iu if_ a = true)
    (hU' : isHost I.store iu a = false) (hF' : isHost I.store if_ a = false) :
    GuardedH I G H fs ia iu if_ ps L ⟨s, f, E.fill [.ref (.func a), .callRefType d]⟩ := by
  have hA : isHost I.store ia a = true := by simpa [isBadC, hU', hF'] using ha
  refine ⟨E, [], a, d, ha, by simp [vals],
    fun h => absurd h (by rw [hU']; exact Bool.false_ne_true),
    fun h => absurd h (by rw [hF']; exact Bool.false_ne_true), fun _ => ⟨rfl, ?_, ?_⟩⟩
  · intro h hh hr
    exact invH_fill hc₀ (fun s f => hole_alloc hx hU' hF' hA hh) (toAdmin_codeInH hr)
  · intro r hr hnv
    refine invH_fill hc₀ (fun s f => ?_) (toAdmin_codeInH hr)
    cases r with
    | values ws => exact absurd rfl (hnv ws)
    | trap => exact post_trapR rfl
    | throw b => exact post_throwingR rfl b

end Guard

/-- A call outside `G` leads to a guarded or an entering thread. -/
theorem of_badStep (hR : ArgCore I G H fs ia iu if_ ps) {L : List Val} {c c' : Config Nat}
    (hf : c.store.funcs = I.store.funcs) (hc : InvH I G H fs ia iu if_ ps L c)
    (hb : BadStep (BadP I ia iu if_ H) fs c c') :
    GuardedH I G H fs ia iu if_ ps L c' ∨ EnterH I G H fs ia iu if_ ps L c' := by
  obtain ⟨E, x, a, d, hcode, rfl, hx, ha⟩ := hb
  have hc₀ : InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill [.plain (.call x)]⟩ := by
    rw [← hcode]; exact hc
  have ha' : isBadC I.store ia iu if_ a = true ∨ a ∈ H := by simpa [BadP, badH] using ha
  rcases ha' with ha | ha
  · refine .inl ?_
    by_cases hU : isHost I.store iu a = true
    · exact guardedH_use hR hc₀ hx ha hU
    · have hU' : isHost I.store iu a = false := by simpa using hU
      by_cases hFr : isHost I.store if_ a = true
      · exact guardedH_free hR hc₀ hx ha hU' hFr
      · exact guardedH_alloc hc₀ hx ha hU' (by simpa using hFr)
  · exact .inr (enterH_of_call hR hc₀ hf hx ha)

theorem avoids_cfgH (hR : ArgCore I G H fs ia iu if_ ps) (a : Nat) (ha : G a) :
    (cfgH I.store fs ia iu if_ ps H).isU a = false ∧ (cfgH I.store fs ia iu if_ ps H).isF a = false ∧
      (cfgH I.store fs ia iu if_ ps H).isA a = false :=
  ⟨isHost_false_of_avoids hR.avU ha, isHost_false_of_avoids hR.avF ha,
    isHost_false_of_avoids hR.avA ha⟩

/-- **One host-free step from an invariant thread** (every profile). -/
theorem step_invH (hR : ArgCore I G H fs ia iu if_ ps) {L : List Val} {P : Profile}
    {c c' : Config Nat} (h : Step P (fun _ _ _ _ => False) c c')
    (hf : c.store.funcs = I.store.funcs) (hc : InvH I G H fs ia iu if_ ps L c) :
    (InvH I G H fs ia iu if_ ps L c' ∨ GuardedH I G H fs ia iu if_ ps L c' ∨
      EnterH I G H fs ia iu if_ ps L c') ∧ c'.store.funcs = c.store.funcs := by
  have hcl : FuncsClosed G fs (CallPl G (badH I.store ia iu if_ H) fs) c.store.funcs :=
    hf ▸ hR.closed
  have hbf : BodiesC G (cfgH I.store fs ia iu if_ ps H) c.store.funcs := hf ▸ hR.bodies
  obtain ⟨hc' | hb, hfun⟩ := Silmaril.Wasm.Verify.Step.cfgIn (Bad := BadP I ia iu if_ H)
    callPl_plainOK hostIn_noHost h hcl hc.1
  · refine ⟨.inl ?_, hfun⟩
    have hp := Step.client (C := cfgH I.store fs ia iu if_ ps H) (L := L) h hR.pairs rfl
      (avoids_cfgH hR) hc.1 hc' hbf
    obtain ⟨-, hS, F, hF, hok⟩ := hc
    obtain ⟨hS', F', hF', hok'⟩ := hp F .other [] other_ne_ex hS hF (by simpa using hok)
    exact ⟨hc', hS', F', hF', by simpa using hok'⟩
  · exact ⟨.inr (of_badStep hR hf hc hb), hfun⟩

end

/-! ## Threads, callouts and resumptions -/

section Threads
variable {I : ScalarInstance} {G : Nat → Prop} {H : List Nat} {fs : List Nat} {ia iu if_ : Nat}
  {ps : List (Nat × Nat)}

theorem invH_invoke {L : List Val} {s : Store Nat} (hs : StoreIn G s) (hS : Sigma ps L s.globals)
    {a : Nat} (ha : G a) {args : List Val} (hargs : ∀ r, Val.ref r ∈ args → RefIn G r) :
    InvH I G H fs ia iu if_ ps L (invoke s a args) := by
  refine ⟨invoke_cfgIn hs ha hargs, hS, [], SoundF_nil, ?_⟩
  have h := freeP_vals (C := cfgH I.store fs ia iu if_ ps H) (V := vals args ++ [.ref (.func a)])
    (R := [.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]) (fun y hy => by
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; simp
      · simp only [List.mem_singleton] at hy; subst hy; simp)
    (freeP_nest trivial fun _ _ _ _ => trivial) L s.globals ({} : Frame).module.globals
    ({} : Frame).locals [] [] trivial
  simpa [invoke] using h

/-- Resuming an invariant thread at a host callout keeps the invariant. -/
theorem resume_invH {L : List Val} {s : Store Nat} {t : Thread}
    (hc : InvH I G H fs ia iu if_ ps L (t.config s)) (r : Result) (hr : RefsOK G r) :
    InvH I G H fs ia iu if_ ps L ((resumeResult s t r).config s) := by
  rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h, args⟩
  · have ht : resumeResult s t r = t := by unfold resumeResult; simp only [hd]
    rw [ht]; exact hc
  · rw [resumeResult_config hd]
    obtain ⟨_, yy, _, _, _, _, hyy, _, _, hfill⟩ := decompose?_sound hd
    have h₀ : t.config s = ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := by
      rw [← hfill]
      cases t <;> rfl
    have hc' : InvH I G H fs ia iu if_ ps L
        ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a), yy])⟩ := h₀ ▸ hc
    exact invH_fill hc' (fun _ _ => hole_host hyy r) (toAdmin_codeInH hr)

theorem guardedH_decompose (hR : ArgCore I G H fs ia iu if_ ps) {c : Config Nat}
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
theorem guardedH_cases (hR : ArgCore I G H fs ia iu if_ ps) {L : List Val} {c : Config Nat}
    (hf : c.store.funcs = I.store.funcs) (hg : GuardedH I G H fs ia iu if_ ps L c) :
    ∃ (E : Ctx) (b : Nat),
      (∃ v, decompose? c.store c.code = some (E, b, iu, [v]) ∧ v ∈ L ∧ ∀ r, RefsOK G r →
          InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (∃ v, decompose? c.store c.code = some (E, b, if_, [v]) ∧ v ∈ L ∧ ∀ r, RefsOK G r →
          InvH I G H fs ia iu if_ ps (L.erase v) ⟨c.store, c.frame, E.fill r.toAdmin⟩) ∨
      (decompose? c.store c.code = some (E, b, ia, []) ∧
        (∀ h, h ∉ L → RefsOK G (.values [h]) → InvH I G H fs ia iu if_ ps (h :: L)
          ⟨c.store, c.frame, E.fill (Result.values [h]).toAdmin⟩) ∧
        (∀ r, RefsOK G r → (∀ ws, r ≠ .values ws) →
          InvH I G H fs ia iu if_ ps L ⟨c.store, c.frame, E.fill r.toAdmin⟩)) := by
  obtain ⟨E, args, b, d, hbad, hcode, hU, hF, hA⟩ := hg
  refine ⟨E, b, ?_⟩
  simp only [isBadC, Bool.or_eq_true] at hbad
  rcases hbad with (h | h) | h
  · obtain ⟨rfl, h₁, h₂⟩ := hA h
    exact .inr (.inr ⟨guardedH_decompose hR hf h (fun hi => (hR.arA hi).1) hcode, h₁, h₂⟩)
  · obtain ⟨v, rfl, hv, hr⟩ := hU h
    exact .inl ⟨v, guardedH_decompose hR hf h (fun hi => hR.arU hi) hcode, hv, hr⟩
  · obtain ⟨v, rfl, hv, hr⟩ := hF h
    exact .inr (.inl ⟨v, guardedH_decompose hR hf h (fun hi => hR.arF hi) hcode, hv, hr⟩)

theorem guardedH_callout (hR : ArgCore I G H fs ia iu if_ ps) {L : List Val} {s : Store Nat}
    {t : Thread} (hf : s.funcs = I.store.funcs) (hg : GuardedH I G H fs ia iu if_ ps L (t.config s)) :
    ∃ h args, CalloutAt s t h args := by
  have hf' : (t.config s).store.funcs = I.store.funcs := by rw [Thread.config_store]; exact hf
  obtain ⟨E, b, ⟨v, hd, -⟩ | ⟨v, hd, -⟩ | ⟨hd, -⟩⟩ := guardedH_cases hR hf' hg <;>
    rw [Thread.config_store] at hd <;> exact ⟨_, _, E, b, hd⟩

/-! ## Entering a helper -/

/-- An entering thread is at no callout. -/
theorem enterH_no_callout {L : List Val} {s : Store Nat} {t : Thread}
    (he : EnterH I G H fs ia iu if_ ps L (t.config s)) {h : Nat} {args : List Val} :
    ¬ CalloutAt s t h args := by
  obtain ⟨E, v, b, d, fi, code, pt, rt, hcode, hfi, hwasm, hexp, hn, -⟩ := he
  rintro ⟨E₀, a₀, hd⟩
  rw [Thread.config_store] at hfi
  have h₀ : decompose? s (vals [v] ++ [.ref (.func b), .callRefType d]) = none :=
    Silmaril.Wasm.Logic.Hoare.decompose?_call_wasm trivial hfi hwasm
  rw [hcode, Silmaril.Wasm.Game.ULink.decompose_fill_call (c := .callRefType d) E trivial hfi hexp hn h₀] at hd
  cases hd

/-- An entering thread is not finished. -/
theorem enterH_not_result {L : List Val} {c : Config Nat}
    (he : EnterH I G H fs ia iu if_ ps L c) (r : Result) : c.code ≠ r.toAdmin := by
  obtain ⟨E, v, b, d, fi, code, pt, rt, hcode, hfi, -, hexp, hn, -⟩ := he
  rw [hcode]
  exact Silmaril.Wasm.Game.ULink.fill_call_ne_result (c := .callRefType d) E trivial hfi hexp hn r

/-- **The step of an entering thread** enters the helper's frame, which is invariant. -/
theorem enterH_step {P : Profile} {L : List Val} {c c' : Config Nat}
    (he : EnterH I G H fs ia iu if_ ps L c) (h : Step P (fun _ _ _ _ => False) c c') :
    InvH I G H fs ia iu if_ ps L c' ∧ c'.store = c.store := by
  obtain ⟨E, v, b, d, fi, code, pt, rt, hcode, hfi, hwasm, hexp, hn, hinv⟩ := he
  obtain ⟨st, fr, cd⟩ := c
  simp only at hcode hfi hinv
  subst hcode
  obtain ⟨s', Y', rfl, hst⟩ := Silmaril.Wasm.Game.ULink.step_fill_call (c := .callRefType d) E trivial hfi hexp hn h
  have hst' : Step P (fun _ _ _ _ => False)
      ⟨st, {}, vals [] ++ vals [v] ++ [.ref (.func b), .callRefType d]⟩ ⟨s', {}, Y'⟩ := by
    simpa [vals] using hst
  have hc := Silmaril.Wasm.Logic.Hoare.call_step_inv (c := .callRefType d) trivial hfi hwasm hexp hn hst'
  simp only [vals, List.map_nil, List.nil_append, Config.mk.injEq] at hc
  obtain ⟨rfl, -, rfl⟩ := hc
  exact ⟨hinv, rfl⟩

end Threads

end Silmaril.Wasm.Resource.ClientArg
