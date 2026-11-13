module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.SimCall

/-!
# Simulation: returns and the final result

* `exit_kind`: a frame whose code is done, with one value, leaves its wrapper (`label` exit, and
  `frame` exit for an FX function frame);
* `exit_wait`: the value then leaves what the frame below waited under: nothing for a call, the
  `if` label, or, for a resume, the handler frame (`handlerVals`), the `block btH` label
  (`br 1` becomes `br 0`) and the `block btD` label (`br 0`);
* **`sim_return`**: a kernel return is matched by these steps;
* **`done_result`**: the kernel's final operands are the `StepFX'` result.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

theorem encI_nil {Y : List InstrFX} (h : EncI S W [] Y) : Y = [] := by
  cases h
  rfl

/-- A finished frame leaves its wrapper. -/
theorem exit_kind {k : Kind} (hk : k.isRoot = false) (G : Frame) (K : List (Option ContFX))
    (x : FVal) :
    Relation.TransGen (FS S G) (K, (kindCtx k .hole).plug (fvals [x])) (K, fvals [x]) := by
  match k, hk with
  | .fn fi, _ =>
    have h₁ : FS S G (K, [.frame 1 fi [.label 1 [] (fvals [x])]]) (K, [.frame 1 fi (fvals [x])]) :=
      step_lift (P := S.P) (host := S.host) (fx := S.fx) (f := G) (.frame 1 fi .hole)
        (X := [.label 1 [] (fvals [x])]) StepFX'.labelVals
    have h₂ : FS S G (K, [.frame 1 fi (fvals [x])]) (K, fvals [x]) := StepFX'.frameVals rfl
    exact .tail (.single h₁) h₂
  | .blk, _ => exact .single StepFX'.labelVals

theorem toNat_ix1 : (ix 1 : LabelIdx).toNat = 1 := rfl

theorem toNat_pred_ix1 : (labelPred (ix 1 : LabelIdx)).toNat = 0 := rfl

/-- The value leaves the context the frame below waited under. -/
theorem exit_wait {p : SFrame Val × Ann} (hp : WaitOk S W p) (G : Frame)
    (K : List (Option ContFX)) (x : FVal) :
    Relation.ReflTransGen (FS S G) (K, (waitCtx S p.1.wait p.2.wa).plug (fvals [x]))
      (K, fvals [x]) := by
  rcases hp with ⟨hw, jk, hwa⟩ | ⟨t, hf, np, bh, Z, hw, hwa, -, -⟩
  · rw [hw, hwa]
    match jk with
    | none => exact .refl
    | some n => exact .single StepFX'.labelVals
  · show Relation.ReflTransGen (FS S G) (K, (waitCtx S p.1.wait p.2.wa).plug (fvals [x]))
      (K, fvals [x])
    rw [hw, hwa]
    let E : CtxV := .label 1 [] (.seq [] (.label (S.ar t + 1) [] (.seq [] .hole [br1])) (adm Z))
    have h₁ : FS S G (K, E.plug [.handler [.onLabel (S.ta t) (ix 0)] (fvals [x])])
        (K, E.plug (fvals [x])) :=
      step_lift (P := S.P) (host := S.host) (fx := S.fx) (f := G) E StepFX'.handlerVals
    let E' : CtxV := .label 1 [] (.seq [] .hole (adm Z))
    have h₂ : FS S G (K, E'.plug [.label (S.ar t + 1) [] (fvals [x] ++ [br1] ++ [])])
        (K, E'.plug (fvals [x] ++ [.core (.plain (.br (labelPred (ix 1))))])) :=
      step_lift (P := S.P) (host := S.host) (fx := S.fx) (f := G) E'
        (StepFX'.brLabelSucc (by rw [toNat_ix1]; exact Nat.one_pos))
    have h₃ : FS S G (K, [.label 1 [] (fvals [] ++ fvals [x] ++
          [.core (.plain (.br (labelPred (ix 1))))] ++ adm Z)]) (K, fvals [x] ++ []) :=
      StepFX'.brLabelZero toNat_pred_ix1 rfl
    have e₁ : FS S G (K, (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug (fvals [x]))
        (K, E'.plug [.label (S.ar t + 1) [] (fvals [x] ++ [br1])]) := by
      simpa only [E, E', waitCtx, CtxV.plug, fvals_nil, List.nil_append, List.append_nil]
        using h₁
    have e₂ : FS S G (K, E'.plug [.label (S.ar t + 1) [] (fvals [x] ++ [br1])])
        (K, E'.plug (fvals [x] ++ [.core (.plain (.br (labelPred (ix 1))))])) := by
      simpa only [List.append_nil] using h₂
    have e₃ : FS S G (K, E'.plug (fvals [x] ++ [.core (.plain (.br (labelPred (ix 1))))]))
        (K, fvals [x]) := by
      simpa only [E', CtxV.plug, fvals_nil, List.nil_append, List.append_nil,
        List.append_assoc] using h₃
    exact .tail (.tail (.single e₁) e₂) e₃

theorem frameAt_wait (w : Option (List Clause)) (wa : WA) (f : Frame) :
    (waitCtx S w wa).frameAt f = f := by
  unfold waitCtx
  split <;> rfl

/-- **A return** of the top frame (one value `r`) to the frame below. -/
theorem sim_return {K : List (Option ContFX)} {KK : List (Option (List (SFrame Val)))}
    {fr b : SFrame Val} {a ab : Ann} {rs : List (SFrame Val × Ann)} {r : SV Val}
    (hmain : MainOk S W ((fr, a) :: (b, ab) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hc : fr.code = []) (hops : fr.ops = [r]) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: (b, ab) :: rs)).plug []⟩
      ⟨KK, { b with ops := fr.ops ++ b.ops } :: rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  have hY : a.code = [] := encI_nil S (hc ▸ hfr.1)
  have hroot : a.kind.isRoot = false :=
    (rootShape_append (xs := [(fr, a)]) (rootShape_of_mainOk S hmain) (List.cons_ne_nil _ _)).2
      _ (List.mem_singleton_self _)
  have hw : WaitOk S W (b, ab) := hmain.2.1 _ (List.mem_cons_self ..)
  let E₀ : CtxV := comp (outer S rs ab.kind) (.seq (opsF b.ops) .hole (adm ab.code))
  let G : Frame := E₀.frameAt S.f0
  have hkind := fplus_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0)
    (comp E₀ (waitCtx S b.wait ab.wa)) (by
      simpa only [frameAt_comp, frameAt_wait] using exit_kind S hroot G K (toF r))
  have hwait := frun_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0) E₀
    (exit_wait S hw G K (toF r))
  let p' : SFrame Val × Ann := ({ b with ops := fr.ops ++ b.ops }, ab)
  have hmain' : MainOk S W (p' :: rs) := by
    refine ⟨fun q hq => ?_, fun q hq => hmain.2.1 q (List.mem_cons_of_mem _ hq),
      rootShape_top (rootShape_pop (rootShape_of_mainOk S hmain)) rfl⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hmain.1 (b, ab) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact hmain.1 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  let X : List AdminFX := (kindCtx a.kind .hole).plug (fvals [toF r])
  have k₁ : Relation.TransGen (FS S S.f0) (K, E₀.plug ((waitCtx S b.wait ab.wa).plug X))
      (K, E₀.plug ((waitCtx S b.wait ab.wa).plug (fvals [toF r]))) := by
    simpa only [plug_comp] using hkind
  have hstart : (stkCtx S ((fr, a) :: (b, ab) :: rs)).plug [] =
      E₀.plug ((waitCtx S b.wait ab.wa).plug X) := by
    simp only [code_push, E₀, X, plug_comp, CtxV.plug, topCtx_plug, hops, hY, opsF_cons,
      opsF_nil, adm, List.map_nil, List.nil_append, List.append_nil]
  have hend : (stkCtx S (p' :: rs)).plug [] = E₀.plug (fvals [toF r]) := by
    simp only [code_top, E₀, p', plug_comp, CtxV.plug, hops, opsF_append, opsF_cons, opsF_nil,
      fvals_append, List.nil_append, List.append_assoc]
  refine ⟨⟨S.s, K, S.f0, (stkCtx S (p' :: rs)).plug []⟩, ?_,
    ⟨rfl, rfl, hK, p' :: rs, rfl, hmain', rfl⟩⟩
  rw [hstart, hend]
  exact fplus_plus (k₁.trans_left hwait)

/-- **The final result**: the root frame's Core operands. -/
theorem done_result {fr : SFrame Val} {a : Ann} {ws : List Val} (hmain : MainOk S W [(fr, a)])
    (hc : fr.code = []) (hv : allVals fr.ops = some ws) :
    (stkCtx S [(fr, a)]).plug [] = (Result.values ws.reverse).toAdmin.map .core := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  have hY : a.code = [] := encI_nil S (hc ▸ hfr.1)
  obtain ⟨init, last, heq, hlast, -⟩ := rootShape_of_mainOk S hmain
  have hinit : init = [] := by
    rcases init with _ | ⟨q, init'⟩
    · rfl
    · have hlen := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.cons_append, List.length_append] at hlen
      omega
  have hk : a.kind = .root := by
    have h : (fr, a) = last :=
      List.singleton_inj.mp (by simpa only [hinit, List.nil_append] using heq)
    rw [← hlast, ← h]
  simp only [stkCtx, lowsCtx, plug_comp, topCtx_plug, hk, hY, kindCtx, CtxV.plug,
    opsF_of_allVals hv, fvals_vals_map, Result.toAdmin, adm, List.map_nil, List.append_nil]

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
