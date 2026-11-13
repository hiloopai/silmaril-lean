module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Inev

/-!
# The backward simulation at a kernel `suspend`

`umatched_suspend`: a kernel `suspend t (ar t)` whose frame holds exactly the payload (its
operand stack has `ar t` values) is matched backwards (`UMatched`): every `StepFX'` run of its
encoding reaches the related configuration of the kernel's next step, or is stuck without a
result. The context pieces of the encoding (`pre₁`: the frames below the resumer's inlined
handler block, an isolated context; `canon_pre_seg`: the captured segment has no values before
its hole) are computed here; the rest is `inev_sus`, with the related configuration of
`Silmaril.Proofs.Wasm.Models.FXAsyncFX.sim_suspend`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.Models.FXAsync (SV SFrame SCfg Ins Prog sstep sexec split lookup popN Res
  Outcome)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX Top cfgOf plug_comp frameAt_comp handles_comp
  preD kindCtx_plug split_ann lookup_single tag_resolves modM_comp modM_lows modM_kind
  frameAt_module ModM not_handles_lows not_handles_top topCtx_plug opsF_append opsF_length
  opsF_cons lowCtx_plug RootShape rootShape_of_mainOk rootShape_append handlerFrame
  resumerAfter mainOk_suspend segOk_suspend code_suspend modM_preD sstep_exec popN_eq opsF_nil
  fvals_nil)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (Iso IsoP Wr SD TermFX InevP UMatched RootLast
  iso_comp isoP_lows rootLast_of_shape)
open Silmaril.Wasm.Numerics (GrowKind)

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- The frames below a resumer's inlined handler block, with the hole at the block's body. -/
def pre₁ (rsA : List (SFrame Val × Ann)) (q : SFrame Val × Ann) : CtxV :=
  comp (lowsCtx S rsA) (kindCtx q.2.kind (.seq (opsF q.1.ops) (.label 1 [] .hole) (adm q.2.code)))

theorem pre_split (rsA : List (SFrame Val × Ann)) (q : SFrame Val × Ann) (Z : List InstrFX)
    (Y : List AdminFX) :
    (comp (lowsCtx S rsA) (preD q Z)).plug Y = (pre₁ S rsA q).plug (Y ++ adm Z) := by
  simp only [pre₁, preD, plug_comp]
  rw [kindCtx_plug, kindCtx_plug (E := .seq _ _ _)]
  simp [CtxV.plug]

theorem iso_pre₁ {rsA : List (SFrame Val × Ann)} {q : SFrame Val × Ann}
    (hl : RootLast (q :: rsA)) : Iso (pre₁ S rsA q) := by
  unfold pre₁
  cases hk : q.2.kind with
  | root =>
    have hrs : rsA = [] := hl.1 (by simp [hk, Kind.isRoot])
    rw [hrs]
    trivial
  | fn fi =>
    exact iso_comp (E' := kindCtx (.fn fi) (.seq (opsF q.1.ops) (.label 1 [] .hole)
      (adm q.2.code))) trivial trivial _ (isoP_lows S rsA hl.2)
  | blk =>
    exact iso_comp (E' := kindCtx .blk (.seq (opsF q.1.ops) (.label 1 [] .hole)
      (adm q.2.code))) trivial trivial _ (isoP_lows S rsA hl.2)

/-- Composition keeps the innermost values of a context with layers. -/
theorem canon_comp_pre (E₂ : CtxV) (h₂ : (canon E₂).layers ≠ []) :
    ∀ E₁ : CtxV, (canon (comp E₁ E₂)).pre = (canon E₂).pre ∧ (canon (comp E₁ E₂)).layers ≠ []
  | .hole => ⟨rfl, h₂⟩
  | .seq vs E rest => by
    obtain ⟨hp, hl⟩ := canon_comp_pre E₂ h₂ E
    rcases hc : (canon (comp E E₂)).layers with _ | ⟨L, Ls⟩
    · exact absurd hc hl
    · simp only [comp, canon, seqC, hc]
      exact ⟨hp, List.cons_ne_nil _ _⟩
  | .label n k E => by
    obtain ⟨hp, -⟩ := canon_comp_pre E₂ h₂ E
    exact ⟨hp, List.cons_ne_nil _ _⟩
  | .frame n f E => by
    obtain ⟨hp, -⟩ := canon_comp_pre E₂ h₂ E
    exact ⟨hp, List.cons_ne_nil _ _⟩
  | .handler hs E => by
    obtain ⟨hp, -⟩ := canon_comp_pre E₂ h₂ E
    exact ⟨hp, List.cons_ne_nil _ _⟩

/-- **The captured segment has no values before its hole** when its top frame has none. -/
theorem canon_pre_seg {p : SFrame Val × Ann} (hp : p.1.ops = []) (hk : p.2.kind.isRoot = false)
    (mA : List (SFrame Val × Ann)) : (canon (stkCtx S (p :: mA))).pre = [] := by
  have htop : (canon (topCtx p)).pre = [] ∧ (canon (topCtx p)).layers ≠ [] := by
    unfold topCtx
    rw [hp]
    cases h : p.2.kind with
    | root => simp [h, Kind.isRoot] at hk
    | fn fi => simp [kindCtx, canon, seqC]
    | blk => simp [kindCtx, canon, seqC]
  have h := canon_comp_pre (topCtx p) htop.2 (lowsCtx S mA)
  rw [stkCtx, h.1, htop.1]

/-- The handling resumer of a `suspend`, below the frames `mA` passed over. -/
structure ResAt (S : Setup H) (W : Prog (Ins Val)) (t : Nat) (q : SFrame Val × Ann)
    (Z : List InstrFX) : Prop where
  wait : ∃ hf, q.1.wait = some [⟨t, hf⟩]
  wa : q.2.wa = .res Z

/-- The resumer of a handled `suspend` waits on a one-clause `resume` for its tag. -/
theorem resAt_of_split {t h : Nat} {q : SFrame Val × Ann} (hq : q.1.wait.bind (lookup t) = some h)
    (hwq : WaitOk S W q) : ∃ Z bh np, ResAt S W t q Z ∧ W h = some (np, bh) ∧ EncI S W bh Z := by
  obtain ⟨t', hf, np', bh, Z, hw, hwa, hhf, hZ⟩ : ∃ (t' hf np' : Nat) (bh : List (Ins Val))
      (Z : List InstrFX), q.1.wait = some [⟨t', hf⟩] ∧ q.2.wa = .res Z ∧
        W hf = some (np', bh) ∧ EncI S W bh Z := by
    rcases hwq with ⟨hw, -, -⟩ | hres
    · simp only [hw, Option.bind_none, reduceCtorEq] at hq
    · exact hres
  have hlk : t' = t ∧ hf = h := lookup_single (by simpa only [hw, Option.bind_some] using hq)
  refine ⟨Z, bh, np', ⟨⟨hf, by rw [hw, hlk.1]⟩, hwa⟩, hlk.2 ▸ hhf, hZ⟩

/-- **The backward simulation at a tight `suspend`** (its frame holds exactly the payload). -/
theorem inev_suspend (hS : SX S = SD o S.fx) (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {t h np : Nat} {pl : List (SV Val)} {c body : List (Ins Val)}
    {Y : List InstrFX} {m : List (SFrame Val)} {r : SFrame Val} {rs' : List (SFrame Val)}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = pl) (hpl : pl.length = S.ar t)
    (hY : a.code = .fx (.suspend (S.xt t)) :: Y) (htag : TagOk S t) (henc : EncI S W c Y)
    (hsplit : split t (rs.map Prod.fst) = some (m, h, r, rs')) (hWh : W h = some (np, body)) :
    InevP (SX S) TermFX (Rel S W ⟨KK ++ [some ({ fr with code := c, ops := [] } :: m)],
        ⟨body, .cont KK.length :: pl, none⟩ :: { r with wait := none } :: rs'⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨mA, q, rsA, rfl, rfl, rfl, rfl, hq, hmA⟩ := split_ann t rs hsplit
  have hwq : WaitOk S W q := hmain.2.1 q (List.mem_append_right _ (List.mem_cons_self ..))
  obtain ⟨Z, bh, np', ⟨⟨hf, hw'⟩, hwa⟩, hhf, hZ⟩ := resAt_of_split S hq hwq
  have hbody : bh = body := by
    have hh : W h = some (np', bh) := hhf
    rw [hWh] at hh
    exact (Prod.mk.inj (Option.some.inj hh)).2.symm
  let p'' : SFrame Val × Ann := ({ fr with code := c, ops := [] }, { a with code := Y })
  let E : CtxV := stkCtx S (p'' :: mA)
  let Pre : CtxV := comp (lowsCtx S rsA) (preD q Z)
  have hall : ∀ r ∈ (fr, a) :: (mA ++ q :: rsA), FrOk S W r := hmain.1
  have hr₀ : RootShape (((fr, a) :: mA) ++ q :: rsA) := rootShape_of_mainOk S hmain
  have hroot : RootShape (q :: rsA) := (rootShape_append hr₀ (List.cons_ne_nil _ _)).1
  have hnr : ((fr, a) : SFrame Val × Ann).2.kind.isRoot = false :=
    (rootShape_append hr₀ (List.cons_ne_nil _ _)).2 _ (List.mem_cons_self ..)
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
  obtain ⟨ti, hti⟩ : ∃ ti, S.s.tag? (E.frameAt (Pre.frameAt S.f0)) (S.xt t) = some (S.ta t, ti) :=
    tag_resolves S htag (frameAt_module E hModE hG)
  have hX : (topCtx (fr, a)).plug [] =
      (topCtx p'').plug (fvals (opsF pl) ++ [.fx (.suspend (S.xt t))]) := by
    simp only [topCtx_plug, p'', hops, hY, adm, List.map_cons, InstrFX.toAdmin,
      List.append_assoc, List.singleton_append, opsF_nil, fvals_nil, List.nil_append]
  let hfrm := handlerFrame body pl KK.length Z
  have hmain' : MainOk S W (hfrm :: resumerAfter q :: rsA) :=
    mainOk_suspend S hmain (hbody ▸ hZ)
  have hseg : SegOk S W (p'' :: mA) := segOk_suspend S hmain ⟨henc, hfr.2⟩ rfl
  have hK' : List.Forall₂ (KRel S W) (KK ++ [some ({ fr with code := c, ops := [] } ::
      mA.map Prod.fst)]) (K ++ [some ⟨E.plug⟩]) :=
    List.rel_append hK (.cons (Or.inr ⟨p'' :: mA, rfl, hseg, rfl⟩) .nil)
  have hend : (stkCtx S (hfrm :: resumerAfter q :: rsA)).plug [] =
      Pre.plug (fvals (opsF pl ++ [.cont K.length])) := by
    simp only [stkCtx, lowsCtx, plug_comp, lowCtx_plug, topCtx_plug, hfrm, handlerFrame,
      resumerAfter, waitCtx, opsF_cons, toF, CtxV.plug, List.append_nil, Pre, preD]
    rw [kindCtx_plug q.2.kind (.seq _ _ _)]
    simp only [CtxV.plug, fvals_nil, hK.length_eq, kindCtx, List.nil_append]
  have hR : Rel S W ⟨KK ++ [some ({ fr with code := c, ops := [] } :: mA.map Prod.fst)],
      ⟨body, .cont KK.length :: pl, none⟩ :: { q.1 with wait := none } :: rsA.map Prod.fst⟩
      ⟨S.s, K ++ [some ⟨E.plug⟩], S.f0, Pre.plug (fvals (opsF pl ++ [.cont K.length]))⟩ :=
    ⟨rfl, rfl, hK', hfrm :: resumerAfter q :: rsA, rfl, hmain', hend.symm⟩
  have hcode : (stkCtx S ((fr, a) :: (mA ++ q :: rsA))).plug [] =
      (preC Pre ((opsF pl).length + 1)).plug
        [.handler [.onLabel (S.ta t) (ix 0)] (E.plug (fvals (opsF pl) ++ [.fx (.suspend (S.xt t))]))] := by
    rw [code_suspend S hw' hwa _ hX, preC, opsF_length, hpl]
  have hpre : (canon E).pre = [] := canon_pre_seg S (p := p'') rfl hnr mA
  have hRL : RootLast (q :: rsA) := rootLast_of_shape hroot
  have ht' : S.s.tag? (E.frameAt ((preC Pre ((opsF pl).length + 1)).frameAt S.f0)) (S.xt t) =
      some (S.ta t, ti) := by
    simpa only [preC, frameAt_comp, CtxV.frameAt] using hti
  rw [hcode, hS]
  exact inev_sus (iso_pre₁ S hRL) (pre_split S rsA q Z) hpre ht' hE hR

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
