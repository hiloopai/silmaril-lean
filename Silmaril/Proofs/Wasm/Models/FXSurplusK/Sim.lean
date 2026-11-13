module

public import Silmaril.Wasm.Models.FXAsyncFX.Thms

/-!
# A `suspend` with surplus operands simulates the kernel without them

In the encoding of `Silmaril.Wasm.Models.FXAsyncFX`, the FX `suspend` may take any suffix of the
values in front of it as its payload. When the kernel frame holds `pl ++ ex ++ o` (top first)
and the tag takes `|pl|` values, the FX payload `ex ++ pl` (bottom first: `opsF (pl ++ ex)`) is
one of the choices. The `br 0` out of `block btH` keeps the last `|pl| + 1` values, so the
handler sees `pl` and the new continuation, as in the tight case; but the captured frame keeps
only `o`. The result is the related configuration of the **kernel step of the frame with `ex`
deleted** (`sim_suspend_ex`, `matched_suspend_ex`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXSurplusK

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX Silmaril.Proofs.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- The FX run of a `suspend` whose payload has `pre` in front of the tag's `pl`: the capture,
then `br 0` out of `block btH`, which drops `pre`. -/
theorem run_suspend_ex {K : List (Option ContFX)} {G : Frame} {t : Nat} (htag : TagOk S t)
    {E : CtxV} (hEm : (E.frameAt G).module = S.M) (hE : ¬ E.Handles (S.ta t))
    (pre pl : List FVal) (hpl : pl.length = S.ar t) (Pre : CtxV) (hG : Pre.frameAt S.f0 = G) :
    Relation.TransGen (FS S S.f0)
      (K, (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))).plug
        [.handler [.onLabel (S.ta t) (ix 0)]
          (E.plug (fvals (pre ++ pl) ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩], Pre.plug (fvals (pl ++ [.cont K.length]))) := by
  obtain ⟨ti, hti⟩ := tag_resolves S htag hEm
  have g₁ : FS S G (K, [.handler [.onLabel (S.ta t) (ix 0)]
        (E.plug (fvals (pre ++ pl) ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩],
        fvals (pre ++ pl) ++ [.contRef K.length, .core (.plain (.br (ix 0)))]) :=
    StepFX'.suspend hti hE (find_clause _)
  have g₂ : FS S G (K ++ [some ⟨E.plug⟩], [.label (S.ar t + 1) []
        (fvals pre ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++
          [br1])])
      (K ++ [some ⟨E.plug⟩], fvals (pl ++ [.cont K.length]) ++ []) :=
    StepFX'.brLabelZero rfl (by rw [List.length_append, hpl]; rfl)
  have h₁ := fstep_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0)
    (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))) (by
      rw [frameAt_comp, hG]; exact g₁)
  have h₂ := fstep_lift (P := S.P) (host := S.host) (fx := S.fx) (f := S.f0) Pre (by
      rw [hG]; exact g₂)
  have f₁ : FS S S.f0 (K, (comp Pre (.label (S.ar t + 1) [] (.seq [] .hole [br1]))).plug
        [.handler [.onLabel (S.ta t) (ix 0)]
          (E.plug (fvals (pre ++ pl) ++ [.fx (.suspend (S.xt t))]))])
      (K ++ [some ⟨E.plug⟩], Pre.plug [.label (S.ar t + 1) []
        (fvals pre ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++
          [br1])]) := by
    simpa only [plug_comp, CtxV.plug, fvals_nil, List.nil_append, fvals_append, fvals_cont1,
      List.append_assoc, List.cons_append] using h₁
  have f₂ : FS S S.f0 (K ++ [some ⟨E.plug⟩], Pre.plug [.label (S.ar t + 1) []
        (fvals pre ++ fvals (pl ++ [.cont K.length]) ++ [.core (.plain (.br (ix 0)))] ++
          [br1])])
      (K ++ [some ⟨E.plug⟩], Pre.plug (fvals (pl ++ [.cont K.length]))) := by
    simpa only [List.append_nil] using h₂
  exact .tail (.single f₁) f₂

/-- **`suspend t (ar t)` with surplus operands `ex`**: the frame holds `pl ++ ex ++ o`, the FX
payload is `ex ++ pl`, and the result is related to the kernel's capture of the frame with
operands `o`, as if `ex` had not been there. -/
theorem sim_suspend_ex (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {t h np : Nat} {pl ex o : List (SV Val)}
    {c body : List (Ins Val)} {Y : List InstrFX} {m : List (SFrame Val)} {r : SFrame Val}
    {rs' : List (SFrame Val)}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = pl ++ ex ++ o) (hpl : pl.length = S.ar t)
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
    modM_preD S q (hall q (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_self ..)))) Z⟩
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
  have hrun := run_suspend_ex S (K := K) htag (frameAt_module E hModE hG) hE (opsF ex)
    (opsF pl) (by rw [opsF_length, hpl]) Pre rfl
  have hX : (topCtx (fr, a)).plug [] =
      (topCtx p'').plug (fvals (opsF ex ++ opsF pl) ++ [.fx (.suspend (S.xt t))]) := by
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

/-! ## From related configurations -/

theorem enc_suspend_inv {t n : Nat} {c : List (Ins Val)} {Y : List InstrFX}
    (h : EncI S W (.suspend t n :: c) Y) :
    n = S.ar t ∧ TagOk S t ∧ ∃ Y', Y = .fx (.suspend (S.xt t)) :: Y' ∧ EncI S W c Y' := by
  cases h with
  | suspend htag h => exact ⟨rfl, htag, _, rfl, h⟩

/-- The kernel configuration whose top frame has operands `ops`. -/
def withOps (x : SCfg Val) (ops : List (SV Val)) : SCfg Val :=
  match x.stack with
  | [] => x
  | fr :: rest => ⟨x.conts, { fr with ops := ops } :: rest⟩

/-- **A surplus `suspend` step is matched by the kernel step of the configuration with the
surplus deleted.** The kernel frame on top holds `pl ++ ex ++ o` before `suspend t (ar t)`, with
`|pl| = ar t`; if the kernel's `suspend` from `withOps x (pl ++ o)` does not trap, the FX
`suspend` with payload `ex ++ pl` reaches a configuration related to its result. -/
theorem matched_suspend_ex (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    {fr : SFrame Val} {rest : List (SFrame Val)} {t : Nat} {cd : List (Ins Val)}
    {pl ex o : List (SV Val)} (hx : x.stack = fr :: rest)
    (hc : fr.code = .suspend t (S.ar t) :: cd) (hops : fr.ops = pl ++ ex ++ o)
    (hpl : pl.length = S.ar t) (hnt : sstep W i32Test (withOps x (pl ++ o)) ≠ .stop .trap) :
    ∃ x', sstep W i32Test (withOps x (pl ++ o)) = .next x' ∧ SimGoal S W c x' := by
  obtain ⟨hs, hf₀, hK, st, hstk, hmain, hcode⟩ := hR
  match st, hmain, hstk with
  | [], hm, _ =>
    obtain ⟨init, last, heq, -⟩ := hm.2.2
    exact absurd heq.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | (fr', a) :: rs, hm, hstk =>
    show ∃ x', sstep W i32Test (withOps x (pl ++ o)) = .next x' ∧ SimGoal S W c x'
    have hfr : fr' = fr ∧ rs.map Prod.fst = rest := by
      have h' : fr' :: rs.map Prod.fst = fr :: rest := by
        rw [← hx, hstk, List.map_cons]
      exact List.cons.inj h'
    obtain ⟨rfl, hrest⟩ := hfr
    have hwx : withOps x (pl ++ o) = ⟨x.conts, { fr' with ops := pl ++ o } :: rest⟩ := by
      simp only [withOps, hx]
    have henc : EncI S W fr'.code a.code := (hm.1 _ (List.mem_cons_self ..)).1
    obtain ⟨-, htag, Y, hY, hencY⟩ := enc_suspend_inv S (hc ▸ henc)
    have hc' : { fr' with ops := pl ++ o }.code = .suspend t (S.ar t) :: cd := hc
    have hnt' : sexec W i32Test x.conts { fr' with ops := pl ++ o } (.suspend t (S.ar t)) cd
        rest ≠ .stop .trap := by
      rw [hwx, sstep_exec hc'] at hnt; exact hnt
    rw [hwx, sstep_exec hc']
    have hp : popN (S.ar t) (pl ++ o) = some (pl, o) := by
      have hle : S.ar t ≤ (pl ++ o).length := by
        rw [List.length_append, hpl]; exact Nat.le_add_right _ _
      have htk : (pl ++ o).take (S.ar t) = pl := by rw [← hpl]; exact List.take_left
      have hdr : (pl ++ o).drop (S.ar t) = o := by rw [← hpl]; exact List.drop_left
      simp only [popN, hle, ite_true, htk, hdr]
    obtain ⟨m, h, r, rs', hsp⟩ : ∃ m h r rs', split t rest = some (m, h, r, rs') := by
      match hss : split t rest with
      | some (m, h, r, rs') => exact ⟨m, h, r, rs', rfl⟩
      | none => exact absurd (by simp only [sexec, hp, hss]) hnt'
    obtain ⟨np, body, hW⟩ : ∃ np body, W h = some (np, body) := by
      match hww : W h with
      | some (np, body) => exact ⟨np, body, rfl⟩
      | none => exact absurd (by simp only [sexec, hp, hsp, hww]) hnt'
    have hstep : sexec W i32Test x.conts { fr' with ops := pl ++ o } (.suspend t (S.ar t)) cd
        rest = .next ⟨x.conts ++ [some ({ fr' with code := cd, ops := o } :: m)],
          ⟨body, .cont x.conts.length :: pl, none⟩ :: { r with wait := none } :: rs'⟩ := by
      simp only [sexec, hp, hsp, hW]
    refine ⟨_, hstep, ?_⟩
    have hcfg : c = ⟨S.s, c.conts, S.f0, (stkCtx S ((fr', a) :: rs)).plug []⟩ := by
      rw [← hs, ← hf₀, ← hcode]
    rw [hcfg]
    exact sim_suspend_ex S hok hm hK hops hpl hY htag hencY (hrest ▸ hsp) hW

/-- A kernel run of `n` steps in the fragment is matched by a `StepFX'` run. -/
theorem steps_in_fx (hok : Ok S W) : ∀ (n : Nat) {x y : SCfg Val} {c : ConfigFX H},
    Rel S W x c → Supported W x → runN (sstep W i32Test) n x = .next y →
      ∃ d, StepsFX' S.P S.host S.fx c d ∧ Rel S W y d
  | 0, x, y, c, hR, _, h => by
    have hxy : x = y := Res.next.inj h
    exact ⟨c, .refl, hxy ▸ hR⟩
  | n + 1, x, y, c, hR, hsup, h => by
    have hm : Matched S W c (sstep W i32Test x) := FXAsyncFX.sim_step S hok hR (fine_of_supported hsup)
    cases hx : sstep W i32Test x with
    | next x' =>
      rw [hx] at hm
      obtain ⟨c', hcc', hR'⟩ := hm
      have hrun : runN (sstep W i32Test) n x' = .next y := by
        rw [← runN_succ_next hx]; exact h
      obtain ⟨d, hd, hRd⟩ := steps_in_fx hok n hR' (supported_next hsup hx) hrun
      exact ⟨d, hcc'.to_reflTransGen.trans hd, hRd⟩
    | stop o => simp only [runN, hx, reduceCtorEq] at h

theorem beh_of_next' {x x' : SCfg Val} (h : sstep W i32Test x = .next x') {ob : Obs Val}
    (hob : ob ∈ beh (sstep W i32Test) x') : ob ∈ beh (sstep W i32Test) x := by
  rcases hob with ⟨n, o, hrun, rfl⟩ | ⟨rfl, hdiv⟩
  · exact Or.inl ⟨n + 1, o, by rw [runN_succ_next h]; exact hrun, rfl⟩
  · refine Or.inr ⟨rfl, fun n => ?_⟩
    cases n with
    | zero => exact ⟨x, rfl⟩
    | succ n => rw [runN_succ_next h]; exact hdiv n

theorem beh_next_iff {x x' : SCfg Val} (h : sstep W i32Test x = .next x') (ob : Obs Val) :
    ob ∈ beh (sstep W i32Test) x ↔ ob ∈ beh (sstep W i32Test) x' := by
  refine ⟨fun hob => ?_, beh_of_next' h⟩
  rcases hob with ⟨n, o, hrun, rfl⟩ | ⟨rfl, hdiv⟩
  · cases n with
    | zero => simp only [runN, reduceCtorEq] at hrun
    | succ n => exact Or.inl ⟨n, o, by rw [← runN_succ_next h]; exact hrun, rfl⟩
  · refine Or.inr ⟨rfl, fun n => ?_⟩
    rw [← runN_succ_next h]
    exact hdiv (n + 1)

/-- **The kernel behaviours of the configuration with the surplus deleted are `StepFX'`
behaviours** of the configuration with it, when that kernel run is in the fragment. -/
theorem surplus_in_fx (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    {fr : SFrame Val} {rest : List (SFrame Val)} {t : Nat} {cd : List (Ins Val)}
    {pl ex o : List (SV Val)} (hx : x.stack = fr :: rest)
    (hc : fr.code = .suspend t (S.ar t) :: cd) (hops : fr.ops = pl ++ ex ++ o)
    (hpl : pl.length = S.ar t) (hsup : Supported W (withOps x (pl ++ o))) :
    ∀ b ∈ beh (sstep W i32Test) (withOps x (pl ++ o)),
      obsB b ∈ behavioursFX' S.P S.host S.fx c := by
  intro b hb
  have hnt : sstep W i32Test (withOps x (pl ++ o)) ≠ .stop .trap := by
    intro ht
    have hf : fine W (withOps x (pl ++ o)) = true := fine_of_supported hsup
    simp only [fine, ht, Bool.false_and, Bool.false_eq_true] at hf
  obtain ⟨x', hs, c', hcc', hR'⟩ := matched_suspend_ex S hok hR hx hc hops hpl hnt
  have hb' : b ∈ beh (sstep W i32Test) x' := (beh_next_iff hs b).mp hb
  have hin : obsB b ∈ behavioursFX' S.P S.host S.fx c' :=
    beh_in_fx S hok hR' (supported_next hsup hs) b hb'
  rcases hin with ⟨d, r, hd, hcode, hbd⟩ | ⟨hdv, hinf⟩
  · exact Or.inl ⟨d, r, hcc'.to_reflTransGen.trans hd, hcode, hbd⟩
  · exact Or.inr ⟨hdv, Silmaril.InfiniteTrace.of_steps hcc'.to_reflTransGen hinf⟩

end Silmaril.Proofs.Wasm.Models.FXSurplusK
