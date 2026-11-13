module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.SimRet

/-!
# Simulation: `resume`

A kernel `resume 0 [(on t h)]` is matched by the entries of `block btD` and `block btH`, the FX
`resume` rule, and, for a fresh continuation, the FX `invoke` of its function (`cont_start`).
The resumed segment becomes the top of the stack, and the resumer waits under its handler frame
(`sim_resume`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {k : Nat} {x : α}, List.Forall₂ R l₁ l₂ → l₁[k]? = some x →
      ∃ y, l₂[k]? = some y ∧ R x y
  | _, _, _, _, .nil, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | _, _, 0, _, .cons hab _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨_, rfl, h ▸ hab⟩
  | _, _, k + 1, _, .cons _ hl, h => by
    simpa only [List.getElem?_cons_succ] using forall₂_getElem? hl h

theorem forall₂_set {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {l₁ : List α} {l₂ : List β} (k : Nat), List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.set k a) (l₂.set k b)
  | _, _, _, .nil => .nil
  | _, _, 0, .cons _ hl => .cons hab hl
  | _, _, k + 1, .cons hxy hl => .cons hxy (forall₂_set hab k hl)

/-- **The start of a resumed continuation**: a captured segment as it is, a fresh one after the
FX `invoke` of its function. -/
theorem cont_start (hok : Ok S W) {seg : List (SFrame Val)} {C : ContFX}
    (h : KRel S W (some seg) (some C)) :
    ∃ st, seg = st.map Prod.fst ∧ SegOk S W st ∧ ∀ (G : Frame) (K : List (Option ContFX)),
      Relation.ReflTransGen (FS S G) (K, C.plug []) (K, (stkCtx S st).plug []) := by
  rcases h with ⟨f, body, fi, hW, hfi, rfl, rfl⟩ | ⟨st, rfl, hst, rfl⟩
  · obtain ⟨-, fi', h, Yb, -, hfi', hcode, hfx, henc⟩ := hok.funcs f 0 body hW
    have hfi_eq : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
    let q : SFrame Val × Ann := (⟨body, [], none⟩, calleeAnn S [] Yb)
    refine ⟨[q], rfl, ⟨List.cons_ne_nil _ _, ?_, fun _ h => absurd h List.not_mem_nil⟩,
      fun G K => .single ?_⟩
    · intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact ⟨⟨henc, fun _ h => by cases h; rfl⟩, rfl⟩
    · have hstep : FS S G (K, cvals [] ++ [.core (.ref (.func (S.fa f))), .core (.callRefType fi.type)])
          (K, [.frame 1 (Frame.forCall S.M [] [])
            [.label 1 [] ((localGets 0 ++ Yb).map InstrFX.toAdmin)]]) :=
        StepFX'.invoke (vs := []) (show Admin.IsCallRef (.callRefType fi.type) from trivial) hfi
          (hfi_eq ▸ hcode) hfx rfl
      simpa only [cvals, vals, List.map_nil, List.nil_append, localGets, List.range_zero,
        stkCtx, lowsCtx, plug_comp, q, topCtx_plug, kindCtx, calleeAnn, opsF_nil, fvals_nil, adm,
        List.map_append, CtxV.plug] using hstep
  · exact ⟨st, rfl, hst, fun _ _ => .refl⟩

/-- The clause of an encoded `resume` resolves to tag address `ta t`, label `0`. -/
theorem resolve_clause {t : Nat} (htag : TagOk S t) {F : Frame} (hF : F.module = S.M) :
    [OnClause.onLabel (S.xt t) (ix 0)].mapM (resolve S.s F) =
      some [.onLabel (S.ta t) (ix 0)] := by
  obtain ⟨ti, hm, hs⟩ := htag
  simp only [List.mapM_cons, List.mapM_nil, resolve, Store.tag?, hF, hm, hs, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_some]

theorem mem_tail_append {α : Type} {xs ys : List α} (hxs : xs ≠ []) {p : α}
    (hp : p ∈ (xs ++ ys).tail) : p ∈ xs.tail ∨ p ∈ ys := by
  match xs, hxs with
  | x :: xs, _ => simpa only [List.cons_append, List.tail_cons, List.mem_append] using hp

/-- A resumed segment on a well-formed stack whose top frame now waits under the handler. -/
theorem mainOk_seg {p p' : SFrame Val × Ann} {rs st : List (SFrame Val × Ann)}
    (hmain : MainOk S W (p :: rs)) (hst : SegOk S W st) (hp' : FrOk S W p')
    (hk : p'.2.kind = p.2.kind) (hw : WaitOk S W p') : MainOk S W (st ++ p' :: rs) := by
  refine ⟨fun q hq => ?_, fun q hq => ?_,
    rootShape_seg (rootShape_top (rootShape_of_mainOk S hmain) hk) fun q hq => (hst.2.1 q hq).2⟩
  · rcases List.mem_append.mp hq with hq | hq
    · exact (hst.2.1 q hq).1
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp'
    · exact hmain.1 q (List.mem_cons_of_mem _ hq)
  · rcases mem_tail_append hst.1 hq with hq | hq
    · exact hst.2.2 q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hw
    · exact hmain.2.1 q hq

/-- The body of `block btH`. -/
def bodyH (S : Setup H) (t : Nat) : List InstrFX :=
  [.fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]), .core (.br (ix 1))]

/-- The FX run of an encoded `resume`, at the frame `F` of the resumer. -/
theorem run_resume {K : List (Option ContFX)} {F : Frame} (hF : F.module = S.M) {k t hf : Nat}
    {C : ContFX} (hk : K[k]? = some (some C)) (htag : TagOk S t) {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType}
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) {Z Y : List InstrFX} (o : List FVal) {Xst : List AdminFX}
    (hst : Relation.ReflTransGen (FS S F) (K.set k none, C.plug []) (K.set k none, Xst)) :
    Relation.TransGen (FS S F)
      (K, fvals (o ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y)
      (K.set k none, fvals o ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug Xst ++ adm Y) := by
  have g₁ := step_block S (K := K) (F := F) (body := .block btH (bodyH S t) :: Z)
    (vs := [.cont k]) (by rw [hF]; exact hD) (by rw [hD₁]; rfl) o (adm Y)
  let E₁ : CtxV := .seq o (.label 1 [] .hole) (adm Y)
  have g₂ : FS S F (K, E₁.plug (fvals [] ++ fvals [.cont k] ++ .block btH (bodyH S t) :: adm Z))
      (K, E₁.plug (fvals [] ++ .label e₂.length [] (fvals [.cont k] ++ adm (bodyH S t)) ::
        adm Z)) :=
    step_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F) E₁
      (step_block S (K := K) (F := F) (body := bodyH S t) (vs := [.cont k])
        (by rw [hF]; exact hH) (by rw [hH₁]; rfl) [] (adm Z))
  let E₂ : CtxV := .seq o (.label 1 [] (.seq [] (.label (S.ar t + 1) [] .hole) (adm Z))) (adm Y)
  have g₃ : FS S F (K, E₂.plug (fvals ([] ++ [.cont k]) ++
        .fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]) :: [br1]))
      (K.set k none, E₂.plug (fvals [] ++ .handler [.onLabel (S.ta t) (ix 0)] (C.plug []) ::
        [br1])) :=
    step_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F) E₂
      (step_resume S (K := K) (F := F) hk (resolve_clause S htag hF) [] [br1])
  let E₃ : CtxV := .seq o (.label 1 [] (.seq [] (.label (S.ar t + 1) []
    (.seq [] (.handler [.onLabel (S.ta t) (ix 0)] .hole) [br1])) (adm Z))) (adm Y)
  have g₄ := frun_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F) E₃ hst
  have f₁ : FS S F (K, fvals (o ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y)
      (K, E₁.plug (fvals [] ++ fvals [.cont k] ++ .block btH (bodyH S t) :: adm Z)) := by
    simpa only [E₁, CtxV.plug, fvals_append, hD₂, adm, List.map_cons, InstrFX.toAdmin,
      fvals_nil, List.nil_append, List.append_assoc, List.singleton_append] using g₁
  have f₂ : FS S F (K, E₁.plug (fvals [] ++ fvals [.cont k] ++ .block btH (bodyH S t) :: adm Z))
      (K, E₂.plug (fvals ([] ++ [.cont k]) ++ .fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]) ::
        [br1])) := by
    simpa only [E₁, E₂, CtxV.plug, hH₂, bodyH, adm, List.map_cons, List.map_nil,
      InstrFX.toAdmin, fvals_nil, List.nil_append, List.append_nil, List.append_assoc,
      List.singleton_append, br1] using g₂
  have f₃ : FS S F (K, E₂.plug (fvals ([] ++ [.cont k]) ++
        .fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]) :: [br1]))
      (K.set k none, E₃.plug (C.plug [])) := by
    simpa only [E₂, E₃, CtxV.plug, fvals_nil, List.nil_append, List.append_nil,
      List.append_assoc, List.singleton_append] using g₃
  have f₄ : Relation.ReflTransGen (FS S F) (K.set k none, E₃.plug (C.plug []))
      (K.set k none, fvals o ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug Xst ++ adm Y) := by
    simpa only [E₃, CtxV.plug, waitCtx, fvals_nil, List.nil_append, List.append_nil] using g₄
  exact (Relation.TransGen.head f₁ (.head' f₂ (.single f₃))).trans_left f₄

/-- **`resume 0 [(on t hf)]`** on continuation `k`, whose segment is `top :: seg`. -/
theorem sim_resume (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {k t hf np : Nat} {top : SFrame Val} {seg : List (SFrame Val)}
    {o : List (SV Val)} {c bh : List (Ins Val)} {Y Z : List InstrFX} {btD btH : BlockType}
    {d₁ d₂ e₁ e₂ : List Silmaril.Wasm.Validation.CValType}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = .cont k :: o) (hKK : KK[k]? = some (some (top :: seg)))
    (hY : a.code = .block btD (.block btH (bodyH S t) :: Z) :: Y) (htag : TagOk S t)
    (hh : W hf = some (np, bh)) (hZ : EncI S W bh Z)
    (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
    (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
    (hH₂ : e₂.length = S.ar t + 1) (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK.set k none, top :: seg ++ { fr with code := c, ops := o, wait := some [⟨t, hf⟩] } ::
        rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨C', hC', hrel⟩ := forall₂_getElem? hK hKK
  obtain ⟨C, rfl⟩ : ∃ C, C' = some C := by
    cases C' with
    | none => exact absurd hrel id
    | some C => exact ⟨C, rfl⟩
  obtain ⟨st, hseg, hst, hrun⟩ := cont_start S hok hrel
  let F := (outer S rs a.kind).frameAt S.f0
  have hF : F.module = S.M := top_module S hok hmain
  have hres := run_resume S (K := K) hF hC' htag hD hD₁ hD₂ hH hH₁ hH₂ (hf := hf) (Z := Z) (Y := Y)
    (opsF o) (hrun F (K.set k none))
  let p' : SFrame Val × Ann := ({ fr with code := c, ops := o, wait := some [⟨t, hf⟩] },
    { a with code := Y, wa := .res Z })
  have hmain' : MainOk S W (st ++ p' :: rs) :=
    mainOk_seg S hmain hst ⟨henc, hfr.2⟩ rfl (Or.inr ⟨t, hf, np, bh, Z, rfl, rfl, hh, hZ⟩)
  have hstk : top :: seg ++ p'.1 :: rs.map Prod.fst = (st ++ p' :: rs).map Prod.fst := by
    rw [List.map_append, ← hseg]
    rfl
  refine ⟨⟨S.s, K.set k none, S.f0, (stkCtx S (st ++ p' :: rs)).plug []⟩, ?_,
    ⟨rfl, rfl, forall₂_set trivial k hK, st ++ p' :: rs, hstk, hmain', rfl⟩⟩
  have hstart : fvals (opsF fr.ops) ++ adm a.code =
      fvals (opsF o ++ [.cont k]) ++ .block btD (.block btH (bodyH S t) :: Z) :: adm Y := by
    rw [hops, hY, opsF_cons]
    rfl
  have hend : (stkCtx S (st ++ p' :: rs)).plug [] = (outer S rs a.kind).plug
      (fvals (opsF o) ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug ((stkCtx S st).plug []) ++
        adm Y) := by
    rw [stkCtx_append S hst.1]
    simp only [lowsCtx, outer, plug_comp, lowCtx_plug, p']
  rw [code_top, hend]
  exact fplus_plus (fplus_lift _ (hstart ▸ hres))

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
