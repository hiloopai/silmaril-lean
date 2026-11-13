module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdMain

/-!
# The forward simulation of the tail-call rewrite: assembly

* `fwd_seg`: a callee segment at the source's head, in context;
* `call_split`: the operands of a call at a call-redex head are exactly the segment's values
  (the callee's parameter count is the annotation's, by typing);
* **`fstep`**: the one-step obligation of the forward relation, by strong induction on the size of
  the source's code;
* `fwd_terminal`: a terminal source is matched by a target run to the same result, with the same
  store;
* **`FRelCfg`**, **`fwdSim`**: the forward relation between typed configurations is a stuttering
  forward simulation (`ConfigSim`) at every profile and every host respecting `FRel` and
  meeting `HostOk`;
* `fwd_run`, `fwd_diverges`: runs to a result transport with related final stores, divergence
  transports.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A callee segment at the source's head.** -/
theorem fwd_seg (hhost : HostRespects FRel host) (hok : HostOk host) {k : Nat}
    {xs ys : List Admin} (hce : CE true k xs ys) {tl : Bool} {s t s' : Store H} {f : Frame}
    {W : List Val} {rest y xs' : List Admin}
    (ih : FIH P host (codeSize (vals W ++ xs ++ rest))) (hst : StoreRel FRel s t)
    (hr : R true tl rest y) (hTs : ContextTyped ⟨s, f, vals W ++ xs ++ rest⟩)
    (hTt : ContextTyped ⟨t, f, vals W ++ ys ++ y⟩) (hseg : SegRed P host f s xs s' xs') :
    FM P host tl s' f (vals W ++ xs' ++ rest) t f (vals W ++ ys ++ y)
      (codeSize (vals W ++ xs ++ rest)) := by
  obtain ⟨t', ys', hm, hst', hcer⟩ := ce_fwd hhost hok hce rfl
    (ih.mono (Closure.codeSize_le_ctx W xs rest)) hst hTs hTt hseg
  refine ⟨t', vals W ++ ys' ++ y, ?_, hst', ?_⟩
  · rcases hm with hT | ⟨rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid hT W y)
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.context_lt (vals W) rest hlt⟩
  · rcases hcer with hce' | ⟨r, rfl, rfl, -⟩
    · simpa using R.valPre (R.callee hce' hr) W
    · exact R.mid hr W r.toAdmin

/-- **The operands of a call at a call-redex head** are the segment's values. -/
theorem call_split {s s' : Store H} {f : Frame} {V₀ vs ws us₁ : List Val} {a k : Nat}
    {d : DefType} {rest is₂ : List Admin} (har : Arity d k vs)
    (hTs : ContextTyped ⟨s, f, vals (V₀ ++ (vs ++ [.ref (.func a)])) ++ .callRefType d :: rest⟩)
    (hV : V₀ ++ (vs ++ [.ref (.func a)]) = ws ++ us₁)
    (hch : CallHead host s us₁ (.callRefType d) s' is₂) :
    us₁ = vs ++ [.ref (.func a)] ∧ ws = V₀ := by
  have key : ∀ (vs₂ : List Val) (a₂ : Nat) (fn : FuncInst H) (ps rs : Ty (.list .val)),
      us₁ = vs₂ ++ [.ref (.func a₂)] → s.funcs[a₂]? = some fn → Expand fn.type (.func ps rs) →
      vs₂.length = ps.length → us₁ = vs ++ [.ref (.func a)] ∧ ws = V₀ := by
    intro vs₂ a₂ fn ps rs hu hf he hn
    subst hu
    have hlast := congrArg List.getLast? hV
    simp at hlast
    subst hlast
    have hV' : V₀ ++ vs = ws ++ vs₂ := by
      have := hV
      rw [← List.append_assoc, ← List.append_assoc] at this
      exact List.append_inj_left' this rfl
    have hT' : ContextTyped ⟨s, f, vals (ws ++ vs₂) ++ [.ref (.func a), .callRefType d] ++ rest⟩ := by
      rw [← hV']; simpa [Val.toAdmin] using hTs
    obtain ⟨-, hd⟩ := callRef_types (c := .callRefType d) hT' trivial hf he hn
    obtain ⟨psd, rsd, hed, hl, -⟩ := hd d rfl
    have hvl : vs.length = vs₂.length := by rw [(har psd rsd hed).2, hl, hn]
    obtain ⟨rfl, rfl⟩ := List.append_inj' hV'.symm hvl.symm
    exact ⟨rfl, rfl⟩
  cases hch with
  | null =>
    have hlast := congrArg List.getLast? hV
    simp at hlast
  | func hf he hn _ => exact key _ _ _ _ _ rfl hf he hn
  | host hf he hn _ _ => exact key _ _ _ _ _ rfl hf he hn
  | div hf he hn _ _ => exact key _ _ _ _ _ rfl hf he hn

/-- **The forward one-step obligation.** -/
theorem fstep (hhost : HostRespects FRel host) (hok : HostOk host) : ∀ m, FIH P host m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro tl s t s' f f' x y x' hm hst hR hTs hTt h
  have ih : FIH P host (codeSize x) := ihm _ hm
  obtain ⟨V, a, rest, ha, rfl⟩ := exists_head_of_not_all h.not_all_isVal
  obtain ⟨V₀, V₁, y₀, rfl, rfl, hh⟩ := R.split ha hR
  cases hh with
  | same hc hr =>
    simp only [List.append_nil] at h ih ⊢
    exact fwd_same hhost hst hc hr ha h
  | instr hr =>
    simp only [List.append_nil] at h ih ⊢
    exact fwd_instr hhost hst hr ha h
  | rcr hc _ => exact (fwd_stuck (RCRPair.isReturnCallRef hc) h).elim
  | label hcond hb hr =>
    simp only [List.append_nil] at h ih hTs ⊢
    exact fwd_label ih hst hcond hb hr hTs hTt h
  | handler hb hr =>
    simp only [List.append_nil] at h ih hTs ⊢
    exact fwd_handler ih hst hb hr hTs hTt h
  | @frame _ k n fc b ys _ y hce hr =>
    simp only [List.append_nil] at h ih hTs ⊢
    rcases Step.split_head ha h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₀, hcode, hfr⟩ := Closure.Step.frame_redex_aux hs us n fc b rfl
    dsimp only at hcode hfr
    have hff := FrameRedex.frame_eq hfr
    subst f'
    subst hcode
    have hfr' : SegRed P host f s [.frame n fc b] s' is₀ := .frame hfr
    have e1 : vals ws ++ (vals us ++ is₀) ++ rest = vals (ws ++ us) ++ is₀ ++ rest := by simp
    have e2 : vals (ws ++ us) ++ Admin.frame n fc b :: rest =
        vals (ws ++ us) ++ [.frame n fc b] ++ rest := by simp
    have e3 : vals (ws ++ us) ++ (ys ++ y) = vals (ws ++ us) ++ ys ++ y := by simp
    rw [e1, e2, e3]
    rw [e2] at ih hTs
    rw [e3] at hTt
    exact fwd_seg hhost hok hce ih hst hr hTs hTt hfr'
  | @call _ k vs a d ys _ y hce hr =>
    rcases Step.split_head ha h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨hff, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv (crt_isCallRef d) hs
    subst f'
    have har := CE.arity_call hce rfl rfl
    have hV' : V₀ ++ (vs ++ [.ref (.func a)]) = (ws ++ ws₂) ++ us₁ := by rw [hV]; simp
    obtain ⟨rfl, rfl⟩ := call_split har hTs hV' hch
    have hseg : SegRed P host f s (vals vs ++ [.ref (.func a), .callRefType d]) s' is₂ := .call hch
    have e1 : vals ws ++ (vals ws₂ ++ is₂) ++ rest = vals (ws ++ ws₂) ++ is₂ ++ rest := by simp
    have e2 : vals ((ws ++ ws₂) ++ (vs ++ [.ref (.func a)])) ++ Admin.callRefType d :: rest =
        vals (ws ++ ws₂) ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest := by
      simp [vals, Val.toAdmin]
    have e3 : vals (ws ++ ws₂) ++ (ys ++ y) = vals (ws ++ ws₂) ++ ys ++ y := by simp
    rw [e1, e2, e3]
    rw [e2] at ih hTs
    rw [e3] at hTt
    exact fwd_seg hhost hok hce ih hst hr hTs hTt hseg
  | bub U X hp =>
    obtain ⟨c', hc⟩ := PTL.rcr hp
    exact (fwd_stuck (RCRPair.isReturnCallRef hc) h).elim
  | trap _ _ ht =>
    exact fwd_trap hst (TA.prefix ht V₀) h
  | @throw _ e us _ _ ht =>
    have h' : Step P host ⟨s, f, vals ((V₀ ++ us) ++ [.ref (.exn e)]) ++ .plain .throwRef :: rest⟩
        ⟨s', f', x'⟩ := by simpa using h
    have := fwd_throw (tl := tl) hst (TT.prefix ht V₀) h'
    simpa using this

/-- **A terminal source** is matched by a target run to the same result, with the same store. -/
theorem fwd_terminal {tl : Bool} {t : Store H} {g : Frame} {r : Result} {y : List Admin}
    (hR : R true tl r.toAdmin y) : Steps P host ⟨t, g, y⟩ ⟨t, g, r.toAdmin⟩ := by
  cases r with
  | values ws =>
    rw [R.vals_inv hR]
    exact .refl
  | trap =>
    exact TA.run (R.trap_inv (V := []) (rest := []) (by simpa [Result.toAdmin, Sim.vals_nil'] using hR))
  | throw a =>
    exact TT.run (R.throw_inv (V := []) (rest := [])
      (by simpa [Result.toAdmin, Sim.vals_nil', throwing] using hR))

/-- **The forward relation** between typed configurations. -/
def FRelCfg (c d : Config H) : Prop :=
  StoreRel FRel c.store d.store ∧ c.frame = d.frame ∧ R true false c.code d.code ∧
    (∃ ts, ConfigOk c ts) ∧ ∃ ts, ConfigOk d ts

theorem configOk_trans (hok : HostOk host) {c d : Config H} (h : Relation.TransGen (Step P host) c d)
    {ts : List CValType} (hc : ConfigOk c ts) : ConfigOk d ts := by
  induction h with
  | single hs => exact (Step.preservation hok hc hs).1
  | tail _ hs ih => exact (Step.preservation hok ih hs).1

/-- **The forward simulation.** -/
theorem fwdSim (hhost : HostRespects FRel host) (hok : HostOk host) :
    ∃ sim : ConfigSim P host (FRelCfg (H := H)), sim.toForwardSim.measure = fun c => codeSize c.code :=
  ⟨{ toForwardSim :=
      { measure := fun c => codeSize c.code
        step := by
          intro c c' d hstep hrel
          obtain ⟨s, f, x⟩ := c
          obtain ⟨s', f', x'⟩ := c'
          obtain ⟨t, g, y⟩ := d
          obtain ⟨hst, hfg, hR, ⟨ts, hc⟩, ⟨ts', hd⟩⟩ := hrel
          dsimp only at hst hfg hR hc hd
          subst hfg
          obtain ⟨t', y', hm, hst', hR'⟩ := fstep hhost hok _ (Nat.lt_succ_self _) hst hR
            (ContextTyped.of_configOk hc) (ContextTyped.of_configOk hd) hstep
          refine ⟨⟨t', f', y'⟩, ?_, hst', rfl, hR', ⟨ts, (Step.preservation hok hc hstep).1⟩, ?_⟩
          · rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
            · exact Or.inl hT
            · exact Or.inr ⟨rfl, hlt⟩
          · rcases hm with hT | ⟨rfl, rfl, rfl, -⟩
            · exact ⟨ts', configOk_trans hok hT hd⟩
            · exact ⟨ts', hd⟩ }
     terminal := by
       intro c d r hrel hc
       obtain ⟨hst, hfg, hR, -, -⟩ := hrel
       obtain ⟨t, g, y⟩ := d
       dsimp only at hR
       rw [hc] at hR
       exact ⟨⟨t, g, r.toAdmin⟩, fwd_terminal hR, rfl⟩ }, rfl⟩

/-- **Runs transport** forwards with related final stores. -/
theorem fwd_run (hhost : HostRespects FRel host) (hok : HostOk host) {c d c' : Config H}
    {r : Result} (h : FRelCfg c d) (hs : Steps P host c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin ∧ StoreRel FRel c'.store d'.store := by
  obtain ⟨sim, -⟩ := fwdSim (P := P) hhost hok
  obtain ⟨d₁, hd, hr⟩ := sim.toForwardSim.steps hs h
  obtain ⟨hst, hfg, hR, -, -⟩ := hr
  obtain ⟨t, g, y⟩ := d₁
  dsimp only at hR hst
  rw [hc] at hR
  exact ⟨⟨t, g, r.toAdmin⟩, hd.trans (fwd_terminal hR), rfl, hst⟩

/-- **Divergence transports** forwards. -/
theorem fwd_diverges (hhost : HostRespects FRel host) (hok : HostOk host) {c d : Config H}
    (h : FRelCfg c d) (hd : Diverges P host c) : Diverges P host d := by
  obtain ⟨sim, -⟩ := fwdSim (P := P) hhost hok
  exact sim.toForwardSim.diverges hd h

end Silmaril.Raw.Wasm.LimeCompile.TailSim
