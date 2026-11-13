module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdSeg
public import Silmaril.Raw.Wasm.LimeCompile.TailSim.FwdSim

/-!
# The backward simulation of the tail-call rewrite

* `bwd_seg`: a callee segment's backward match, under values and a related suffix;
* **`bstep`**: the one-step obligation of the backward relation (target on the left), for pairs
  that are not pending, by strong induction on the size of the target's code;
* `bwd_terminal`: a terminal target is matched by a source run to the same result;
* **`bwdSim`**: the backward relation between typed configurations (`BRelCfg`, the target on
  the left) is a stuttering forward simulation of `Step` with itself (`ConfigSim`), with result
  transport, at every profile and every host whose converse respects `FRel` and that meets
  `HostOk`;
* `bwd_run`, `bwd_diverges`: runs (with related final stores) and divergence transport from
  the target to the source.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- **A callee segment's backward match** under values and a related suffix. -/
theorem bwd_seg {k : Nat} {xs ys is₀ : List Admin} {tl : Bool} {s t' : Store H} {f : Frame}
    {W : List Val} {x rest' : List Admin} (hr : R false tl x rest')
    (hm : BCEM P host k ys is₀ s f xs t') :
    BM P host tl t' f (vals W ++ is₀ ++ rest') s f (vals W ++ xs ++ x)
      (codeSize (vals W ++ ys ++ rest')) := by
  obtain ⟨s', xs', hm, hst', hcer⟩ := hm
  refine ⟨s', vals W ++ xs' ++ x, ?_, hst', ?_⟩
  · rcases hm with hT | ⟨rfl, rfl, hlt⟩
    · exact Or.inl (trans_mid hT W x)
    · exact Or.inr ⟨rfl, rfl, rfl, LawfulCodeRank.context_lt (vals W) rest' hlt⟩
  · rcases hcer with hce | ⟨rfl, hTA⟩ | ⟨e, rfl, hTT⟩ | ⟨ws, rfl, rfl, -⟩
    · simpa using R.valPre (R.callee hce hr) W
    · simpa using R.trapC (fw := false) (tl := tl) W x (TA.append (TA.prefix hTA W) rest')
    · exact R.throwC W x (TT.append (TT.prefix hTT W) rest')
    · simpa using R.valPre (R.append hr (R.refl false tl (vals ws))) W

/-- **The backward one-step obligation.** -/
theorem bstep (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host) :
    ∀ m, BIH P host m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro tl s t t' f f' x y y' hm hst hR hnp hTs hTt h
  have ih : BIH P host (codeSize y) := ihm _ hm
  obtain ⟨V, b, rest', hb, rfl⟩ := exists_head_of_not_all h.not_all_isVal
  obtain ⟨V₀, V₁, x₀, rfl, rfl, hh⟩ := R.tsplit hb hR
  cases hh with
  | same hc hr =>
    simp only [List.append_nil] at h ih hTt hnp ⊢
    exact bwd_same hhostB hst hc hr hb h
  | instr hr heq =>
    simp only [List.append_nil] at h ih hTt hnp ⊢
    exact bwd_instr hhostB hst hr hb heq h
  | rcr hcc hr =>
    simp only [List.append_nil] at hnp
    exact (hnp (PendR.rcr hcc)).elim
  | label hcond hb' hr =>
    simp only [List.append_nil] at h ih hTt hnp hTs ⊢
    exact bwd_label ih hst hcond hb' hr (fun hp => hnp (PendR.label hp)) hTs hTt h
  | handler hb' hr =>
    simp only [List.append_nil] at h ih hTt hnp hTs ⊢
    exact bwd_handler ih hst hb' hr hTs hTt h
  | @seg _ k xs _ _ x' hce hr =>
    simp only [List.append_nil] at h ih hTt hnp hTs ⊢
    obtain ⟨fi, B, rfl⟩ := CE.tgt_single hce
    rcases Step.split_head hb h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₀, hcode, hfr⟩ := Closure.Step.frame_redex_aux hs us k fi B rfl
    dsimp only at hcode hfr
    have hff := FrameRedex.frame_eq hfr
    subst f'
    subst hcode
    have e : vals (ws ++ us) ++ Admin.frame k fi B :: rest' =
        vals (ws ++ us) ++ [Admin.frame k fi B] ++ rest' := by simp
    rw [e] at ih hTt ⊢
    have hTs' : ContextTyped ⟨s, f, vals (ws ++ us) ++ xs ++ x'⟩ := by simpa using hTs
    have hm' := ce_bwd hhostB hok hce rfl (ih.mono (Closure.codeSize_le_ctx _ _ _)) hst hTs' hTt
      (TSegRed.frame hfr)
    have := bwd_seg (W := ws ++ us) hr hm'
    simpa using this
  | @call _ k vs a d _ x' har hr =>
    rcases Step.split_head hb h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨hff, ws₂, us₁, is₂, rfl, rfl, hch⟩ := call_inv (crt_isCallRef d) hs
    subst f'
    have hTs' : ContextTyped ⟨s, f, vals V₀ ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++
        x'⟩ := by simpa using hTs
    obtain ⟨rfl, rfl⟩ := call_split_t (pre := V₀) (ws₁ := ws ++ ws₂) har hst hTs'
      (by rw [hV]; simp) hch
    have e : vals ((ws ++ ws₂) ++ (vs ++ [.ref (.func a)])) ++ Admin.callRefType d :: rest' =
        vals (ws ++ ws₂) ++ (vals vs ++ [.ref (.func a), .callRefType d]) ++ rest' := by
      simp [vals, Val.toAdmin]
    rw [e] at ih hTt ⊢
    have hm' := ce_bwd hhostB hok (CE.call har) rfl (ih.mono (Closure.codeSize_le_ctx _ _ _))
      hst hTs' hTt (TSegRed.call hch)
    have := bwd_seg (W := ws ++ ws₂) hr hm'
    simpa using this
  | @trap _ _ _ _ us x' ht =>
    have := bwd_trap (tl := tl) (us := V₀ ++ us) (x := x') hst (TA.prefix ht V₀)
      (by simpa using h)
    simpa using this
  | @throw _ _ _ _ e us x' ht =>
    have := bwd_throw (tl := tl) (us := V₀ ++ us) (x := x') hst (TT.prefix ht V₀)
      (by simpa using h)
    simpa using this

/-- **A terminal target** is matched by a source run to the same result, in the same store. -/
theorem bwd_terminal {tl : Bool} {s : Store H} {f : Frame} {r : Result} {x : List Admin}
    (hR : R false tl x r.toAdmin) : Steps P host ⟨s, f, x⟩ ⟨s, f, r.toAdmin⟩ := by
  cases r with
  | values ws =>
    rw [R.vals_tinv hR]
    exact .refl
  | trap =>
    obtain ⟨us, x', rfl⟩ := R.trap_tinv (V := []) (rest' := [])
      (by simpa [Result.toAdmin, Sim.vals_nil'] using hR)
    exact disc_trap s f us x'
  | throw a =>
    obtain ⟨us, x', rfl⟩ := R.throw_tinv (V := []) (rest' := [])
      (by simpa [Result.toAdmin, Sim.vals_nil', throwing] using hR)
    exact disc_throw a s f us x'

/-- **The backward relation** between typed configurations: the target on the left. -/
def BRelCfg (c d : Config H) : Prop :=
  StoreRel FRel d.store c.store ∧ c.frame = d.frame ∧ R false false d.code c.code ∧
    (∃ ts, ConfigOk c ts) ∧ ∃ ts, ConfigOk d ts

/-- **The backward simulation.** -/
theorem bwdSim (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host) :
    ∃ sim : ConfigSim P host (BRelCfg (H := H)), sim.toForwardSim.measure = fun c => codeSize c.code :=
  ⟨{ toForwardSim :=
      { measure := fun c => codeSize c.code
        step := by
          intro c c' d hstep hrel
          obtain ⟨t, g, y⟩ := c
          obtain ⟨t', g', y'⟩ := c'
          obtain ⟨s, f, x⟩ := d
          obtain ⟨hst, hfg, hR, ⟨ts, hc⟩, ⟨ts', hd⟩⟩ := hrel
          dsimp only at hst hfg hR hc hd
          subst hfg
          obtain ⟨s', x', hm, hst', hR'⟩ := bstep hhostB hok _ (Nat.lt_succ_self _) hst hR
            (fun hp => R.not_pend hp hR) (ContextTyped.of_configOk hd)
            (ContextTyped.of_configOk hc) hstep
          refine ⟨⟨s', g', x'⟩, ?_, hst', rfl, hR', ⟨ts, (Step.preservation hok hc hstep).1⟩, ?_⟩
          · rcases hm with hT | ⟨rfl, rfl, rfl, hlt⟩
            · exact Or.inl hT
            · exact Or.inr ⟨rfl, hlt⟩
          · rcases hm with hT | ⟨rfl, rfl, rfl, -⟩
            · exact ⟨ts', configOk_trans hok hT hd⟩
            · exact ⟨ts', hd⟩ }
     terminal := by
       intro c d r hrel hc
       obtain ⟨hst, hfg, hR, -, -⟩ := hrel
       obtain ⟨s, f, x⟩ := d
       dsimp only at hR
       rw [hc] at hR
       exact ⟨⟨s, f, r.toAdmin⟩, bwd_terminal hR, rfl⟩ }, rfl⟩

/-- **Runs transport** backwards with related final stores. -/
theorem bwd_run (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {c d c' : Config H} {r : Result} (h : BRelCfg c d) (hs : Steps P host c c')
    (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin ∧ StoreRel FRel d'.store c'.store := by
  obtain ⟨sim, -⟩ := bwdSim (P := P) hhostB hok
  obtain ⟨d₁, hd, hr⟩ := sim.toForwardSim.steps hs h
  obtain ⟨hst, hfg, hR, -, -⟩ := hr
  obtain ⟨s, f, x⟩ := d₁
  dsimp only at hR hst
  rw [hc] at hR
  exact ⟨⟨s, f, r.toAdmin⟩, hd.trans (bwd_terminal hR), rfl, hst⟩

/-- **Divergence transports** backwards. -/
theorem bwd_diverges (hhostB : HostRespects (fun g f => FRel f g) host) (hok : HostOk host)
    {c d : Config H} (h : BRelCfg c d) (hd : Diverges P host c) : Diverges P host d := by
  obtain ⟨sim, -⟩ := bwdSim (P := P) hhostB hok
  exact sim.toForwardSim.diverges hd h

end Silmaril.Raw.Wasm.LimeCompile.TailSim
