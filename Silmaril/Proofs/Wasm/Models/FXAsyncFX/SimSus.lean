module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.SimRes

/-!
# Simulation: `suspend`

A kernel `suspend t (ar t)` captures the frames up to the innermost resumer with a clause for
`t` and calls the handler in the resumer. In the encoding the resumer's handler frame has the
clause `(on (ta t) 0)`, the frames passed have none (`not_handles_lows`), so the FX `suspend`
rule captures exactly the encoded segment, and its `br 0` leaves the `block btH` label with the
payload and the new continuation, entering the inlined handler code (`sim_suspend`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- The tag of an encoded `suspend` resolves at every frame of `M`. -/
theorem tag_resolves {t : Nat} (htag : TagOk S t) {F : Frame} (hF : F.module = S.M) :
    ∃ ti, S.s.tag? F (S.xt t) = some (S.ta t, ti) := by
  obtain ⟨ti, hm, hs⟩ := htag
  exact ⟨ti, by simp only [Store.tag?, hF, hm, hs, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]⟩

theorem find_clause (ta : Nat) :
    [HClause.onLabel ta (ix 0)].find? (fun c => c.tag == ta) = some (.onLabel ta (ix 0)) := by
  simp only [List.find?_cons, HClause.tag, BEq.rfl]

/-- The FX run of a `suspend`: the capture, then `br 0` out of `block btH`. -/
theorem run_suspend {K : List (Option ContFX)} {G : Frame} {t : Nat} (htag : TagOk S t)
    {E : CtxV} (hEm : (E.frameAt G).module = S.M) (hE : ¬ E.Handles (S.ta t))
    (pl : List FVal) (hpl : pl.length = S.ar t) (Pre : CtxV) (hG : Pre.frameAt S.f0 = G) :
    Relation.TransGen (FS S S.f0)
      (K, (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))).plug
        [.handler [.onLabel (S.ta t) (ix 0)] (E.plug (fvals pl ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩], Pre.plug (fvals (pl ++ [.cont K.length]))) := by
  obtain ⟨ti, hti⟩ := tag_resolves S htag hEm
  have g₁ : FS S G (K, [.handler [.onLabel (S.ta t) (ix 0)]
        (E.plug (fvals pl ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩], fvals pl ++ [.contRef K.length, .core (.plain (.br (ix 0)))]) :=
    StepFX'.suspend hti hE (find_clause _)
  have g₂ : FS S G (K ++ [some ⟨E.plug⟩], [.label (S.ar t + 1) []
        (fvals [] ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++ [br1])])
      (K ++ [some ⟨E.plug⟩], fvals (pl ++ [.cont K.length]) ++ []) :=
    StepFX'.brLabelZero rfl (by rw [List.length_append, hpl]; rfl)
  have h₁ := fstep_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0)
    (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))) (by
      rw [frameAt_comp, hG]; exact g₁)
  have h₂ := fstep_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0) Pre (by
      rw [hG]; exact g₂)
  have f₁ : FS S S.f0 (K, (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))).plug
        [.handler [.onLabel (S.ta t) (ix 0)] (E.plug (fvals pl ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩], Pre.plug [.label (S.ar t + 1) []
        (fvals [] ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++
          [br1])]) := by
    simpa only [plug_comp, CtxV.plug, fvals_nil, List.nil_append, fvals_append, fvals_cont1,
      List.append_assoc, List.cons_append] using h₁
  have f₂ : FS S S.f0 (K ++ [some ⟨E.plug⟩], Pre.plug [.label (S.ar t + 1) []
        (fvals [] ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++ [br1])])
      (K ++ [some ⟨E.plug⟩], Pre.plug (fvals (pl ++ [.cont K.length]))) := by
    simpa only [List.append_nil] using h₂
  exact .tail (.single f₁) f₂

/-- The handling resumer's frame, on top after the capture: it waits on its handler block. -/
def resumerAfter (q : SFrame Val × Ann) : SFrame Val × Ann :=
  ({ q.1 with wait := none }, { q.2 with wa := .call none })

/-- The inlined handler's frame. -/
def handlerFrame (body : List (Ins Val)) (pl : List (SV Val)) (k : Nat) (Z : List InstrFX) :
    SFrame Val × Ann :=
  (⟨body, .cont k :: pl, none⟩, ⟨.blk, .call none, Z⟩)

/-- The stack after the capture is well formed. -/
theorem mainOk_suspend {p : SFrame Val × Ann} {mA rsA : List (SFrame Val × Ann)}
    {q : SFrame Val × Ann} {body : List (Ins Val)} {pl : List (SV Val)} {k : Nat}
    {Z : List InstrFX} (hmain : MainOk S W (p :: (mA ++ q :: rsA))) (hZ : EncI S W body Z) :
    MainOk S W (handlerFrame body pl k Z :: resumerAfter q :: rsA) := by
  have hr₀ : RootShape ((p :: mA) ++ q :: rsA) := rootShape_of_mainOk S hmain
  have hroot : RootShape (q :: rsA) := (rootShape_append hr₀ (List.cons_ne_nil _ _)).1
  have hin : ∀ r ∈ q :: rsA, r ∈ p :: (mA ++ q :: rsA) := fun r hr =>
    List.mem_cons_of_mem _ (List.mem_append_right _ hr)
  refine ⟨fun r hr => ?_, fun r hr => ?_,
    rootShape_cons (rootShape_top hroot rfl) rfl⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hZ, fun _ h => nomatch h⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hmain.1 q (hin q (List.mem_cons_self ..))
    · exact hmain.1 r (hin r (List.mem_cons_of_mem _ hr))
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl ⟨rfl, none, rfl⟩
    · exact hmain.2.1 r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))

/-- The captured segment is well formed. -/
theorem segOk_suspend {p p'' : SFrame Val × Ann} {mA rsA : List (SFrame Val × Ann)}
    {q : SFrame Val × Ann} (hmain : MainOk S W (p :: (mA ++ q :: rsA))) (hp'' : FrOk S W p'')
    (hk : p''.2.kind = p.2.kind) : SegOk S W (p'' :: mA) := by
  have hr₀ : RootShape ((p :: mA) ++ q :: rsA) := rootShape_of_mainOk S hmain
  have hnr : ∀ r ∈ p :: mA, r.2.kind.isRoot = false :=
    (rootShape_append hr₀ (List.cons_ne_nil _ _)).2
  refine ⟨List.cons_ne_nil _ _, fun r hr => ?_, fun r hr =>
    hmain.2.1 r (List.mem_append_left _ hr)⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨hp'', hk ▸ hnr p (List.mem_cons_self ..)⟩
  · exact ⟨hmain.1 r (List.mem_cons_of_mem _ (List.mem_append_left _ hr)),
      hnr r (List.mem_cons_of_mem _ hr)⟩

theorem modM_preD (q : SFrame Val × Ann) (hq : FrOk S W q) (Z : List InstrFX) :
    ModM S.M (preD q Z) :=
  modM_kind S _ _ hq.2 trivial

/-- The code of the stack at a suspension, around the resumer's handler frame. -/
theorem code_suspend {p p'' q : SFrame Val × Ann} {mA rsA : List (SFrame Val × Ann)} {t hf : Nat}
    {Z : List InstrFX} (hw : q.1.wait = some [⟨t, hf⟩]) (hwa : q.2.wa = .res Z)
    (X : List AdminFX) (hX : (topCtx p).plug [] = (topCtx p'').plug X) :
    (stkCtx S (p :: (mA ++ q :: rsA))).plug [] =
      (comp (comp (lowsCtx S rsA) (preD q Z)) (.label (S.ar t + 1) [] (.seq [] .hole [br1]))).plug
        [.handler [.onLabel (S.ta t) (ix 0)] ((stkCtx S (p'' :: mA)).plug X)] := by
  simp only [stkCtx, lowsCtx_append, lowsCtx, plug_comp, lowCtx_res S hw hwa, preH, hX,
    CtxV.plug]

/-- **`suspend t (ar t)`** with payload `pl`, handled by resumer `q` below the frames `mA`. -/
theorem sim_suspend (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {t h np : Nat} {pl o : List (SV Val)} {c body : List (Ins Val)}
    {Y : List InstrFX} {m : List (SFrame Val)} {r : SFrame Val} {rs' : List (SFrame Val)}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = pl ++ o) (hpl : pl.length = S.ar t)
    (hY : a.code = .fx (.suspend (S.xt t)) :: Y) (htag : TagOk S t) (henc : EncI S W c Y)
    (hsplit : split t (rs.map Prod.fst) = some (m, h, r, rs')) (hWh : W h = some (np, body)) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK ++ [some ({ fr with code := c, ops := o } :: m)],
        ⟨body, .cont KK.length :: pl, none⟩ :: { r with wait := none } :: rs'⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨mA, q, rsA, rfl, rfl, rfl, rfl, hq, hmA⟩ := split_ann t rs hsplit
  have hwq : WaitOk S W q := hmain.2.1 q (List.mem_append_right _ (List.mem_cons_self ..))
  obtain ⟨t', hf, np', bh, Z, hw, hwa, hhf, hZ⟩ : ∃ (t' hf np' : Nat) (bh : List (Ins Val))
      (Z : List InstrFX), q.1.wait = some [⟨t', hf⟩] ∧ q.2.wa = .res Z ∧
        W hf = some (np', bh) ∧ EncI S W bh Z := by
    rcases hwq with ⟨hw, -, -⟩ | hres
    · simp only [hw, Option.bind_none, reduceCtorEq] at hq
    · exact hres
  have hlk : t' = t ∧ hf = h := lookup_single (by simpa only [hw, Option.bind_some] using hq)
  have hbody : bh = body := by
    have hh : W h = some (np', bh) := hlk.2 ▸ hhf
    rw [hWh] at hh
    exact (Prod.mk.inj (Option.some.inj hh)).2.symm
  have hw' : q.1.wait = some [⟨t, hf⟩] := by rw [hw, hlk.1]
  let p'' : SFrame Val × Ann := ({ fr with code := c, ops := o }, { a with code := Y })
  let E : CtxV := stkCtx S (p'' :: mA)
  let Pre : CtxV := comp (lowsCtx S rsA) (preD q Z)
  have hall : ∀ r ∈ (fr, a) :: (mA ++ q :: rsA), FrOk S W r := hmain.1
  have hModPre : ModM S.M Pre := (modM_comp _ _).mpr ⟨modM_lows S rsA fun r hr =>
    hall r (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hr))),
    modM_preD S q (hall q (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_self ..)))) Z⟩
  have hG : (Pre.frameAt S.f0).module = S.M := frameAt_module _ hModPre hok.root
  have hModE : ModM S.M E := (modM_comp _ _).mpr ⟨modM_lows S mA fun r hr =>
    hall r (List.mem_cons_of_mem _ (List.mem_append_left _ hr)),
    modM_kind S _ _ hfr.2 trivial⟩
  have hE : ¬ E.Handles (S.ta t) := by
    show ¬ (comp (lowsCtx S mA) (topCtx p'')).Handles (S.ta t)
    rw [handles_comp]
    rintro (h₁ | h₁)
    · exact not_handles_lows S hok mA (fun r hr => hmain.2.1 r (List.mem_append_left _ hr))
        hmA h₁
    · exact not_handles_top p'' _ h₁
  have hrun := run_suspend S (K := K) htag (frameAt_module E hModE hG) hE (opsF pl)
    (by rw [opsF_length, hpl]) Pre rfl
  have hX : (topCtx (fr, a)).plug [] =
      (topCtx p'').plug (fvals (opsF pl) ++ [.fx (.suspend (S.xt t))]) := by
    simp only [topCtx_plug, p'', hops, hY, opsF_append, fvals_append, adm, List.map_cons,
      InstrFX.toAdmin, List.append_assoc, List.singleton_append, List.nil_append]
  let hfrm := handlerFrame body pl KK.length Z
  have hmain' : MainOk S W (hfrm :: resumerAfter q :: rsA) :=
    mainOk_suspend S hmain (hbody ▸ hZ)
  have hseg : SegOk S W (p'' :: mA) := segOk_suspend S hmain ⟨henc, hfr.2⟩ rfl
  have hK' : List.Forall₂ (KRel S W) (KK ++ [some ({ fr with code := c, ops := o } ::
      mA.map Prod.fst)]) (K ++ [some ⟨E.plug⟩]) :=
    List.rel_append hK (.cons (Or.inr ⟨p'' :: mA, rfl, hseg, rfl⟩) .nil)
  refine ⟨⟨S.s, K ++ [some ⟨E.plug⟩], S.f0, (stkCtx S (hfrm :: resumerAfter q :: rsA)).plug []⟩,
    ?_, ⟨rfl, rfl, hK', hfrm :: resumerAfter q :: rsA, rfl, hmain', rfl⟩⟩
  have hL : (stkCtx S (hfrm :: resumerAfter q :: rsA)).plug [] = (lowsCtx S rsA).plug
      ((kindCtx q.2.kind .hole).plug (fvals (opsF q.1.ops) ++
        [.label 1 [] (fvals (opsF pl ++ [.cont KK.length]) ++ adm Z)] ++ adm q.2.code)) := by
    simp only [stkCtx, lowsCtx, plug_comp, lowCtx_plug, topCtx_plug, hfrm, handlerFrame,
      resumerAfter, waitCtx, opsF_cons, toF, CtxV.plug, List.append_nil]
    rfl
  have hR : Pre.plug (fvals (opsF pl ++ [.cont K.length])) = (lowsCtx S rsA).plug
      ((kindCtx q.2.kind .hole).plug (fvals (opsF q.1.ops) ++
        [.label 1 [] (fvals (opsF pl ++ [.cont K.length]) ++ adm Z)] ++ adm q.2.code)) := by
    simp only [Pre, preD, plug_comp]
    rw [kindCtx_plug]
    simp only [CtxV.plug, fvals_nil, List.nil_append]
  have hend : (stkCtx S (hfrm :: resumerAfter q :: rsA)).plug [] =
      Pre.plug (fvals (opsF pl ++ [.cont K.length])) := by
    rw [hL, hR, hK.length_eq]
  rw [code_suspend S hw' hwa _ hX, hend]
  exact fplus_plus hrun

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
