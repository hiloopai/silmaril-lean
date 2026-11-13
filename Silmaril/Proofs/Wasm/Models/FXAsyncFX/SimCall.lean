module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.SimTop

/-!
# Simulation: calls

A kernel `call f` is matched by `call`, the FX `invoke` rule and the prologue (`sim_call`); a
kernel `cond f g` by `if`, the entry of its block and the same call (`sim_cond`). The callee
becomes the top frame, an FX function frame, and the caller waits on it (inside the `if`'s
label for `cond`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- The code of a stack around a waiting frame and the frame above it. -/
theorem code_push (q p : SFrame Val × Ann) (rs : List (SFrame Val × Ann)) :
    (stkCtx S (q :: p :: rs)).plug [] = (outer S rs p.2.kind).plug
      (fvals (opsF p.1.ops) ++ (waitCtx S p.1.wait p.2.wa).plug ((topCtx q).plug []) ++
        adm p.2.code) := by
  simp only [stkCtx, lowsCtx, outer, plug_comp, lowCtx_plug]

theorem topCtx_fn (q : SFrame Val × Ann) {fi : Frame} (hq : q.2.kind = .fn fi) :
    (topCtx q).plug [] = [.frame 1 fi [.label 1 [] (fvals (opsF q.1.ops) ++ adm q.2.code)]] := by
  simp only [topCtx_plug, hq, kindCtx, CtxV.plug, List.append_nil]

/-- A new frame on a well-formed stack whose top frame now waits. -/
theorem mainOk_push {p p' q : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (hmain : MainOk S W (p :: rs)) (hq : FrOk S W q) (hqr : q.2.kind.isRoot = false)
    (hp' : FrOk S W p') (hk : p'.2.kind = p.2.kind) (hw : WaitOk S W p') :
    MainOk S W (q :: p' :: rs) := by
  have hroot : RootShape (q :: p' :: rs) :=
    rootShape_cons (rootShape_top (rootShape_of_mainOk S hmain) hk) hqr
  refine ⟨fun r hr => ?_, fun r hr => ?_, hroot⟩
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hq
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hp'
    · exact hmain.1 r (List.mem_cons_of_mem _ hr)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact hw
    · exact hmain.2.1 r hr

/-- The callee's frame. -/
def calleeAnn (S : Setup H) (ws : List Val) (Yb : List InstrFX) : Ann :=
  ⟨.fn (Frame.forCall S.M ws []), .call none, Yb⟩

/-- **A call**, from the top frame's operands `args ++ o` (Core values `ws`). -/
theorem sim_callCore (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {f np : Nat} {body : List (Ins Val)} {c : List (Ins Val)}
    {Y : List InstrFX} {args o : List (SV Val)} {ws : List Val} {jk : Option Nat}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hargs : allVals args = some ws) (hlen : args.length = np) (hW : W f = some (np, body))
    (henc : EncI S W c Y)
    (hrun : ∀ (F : Frame) (Q : AdminFX), F.module = S.M →
      Relation.TransGen (FS S F) (K, fvals [] ++ fvals (ws.reverse.map .val) ++
        .core (.plain (.call (S.xf f))) :: []) (K, fvals [] ++ Q :: []) →
      Relation.TransGen (FS S F) (K, fvals (opsF fr.ops) ++ adm a.code) (K, fvals (opsF o) ++
        (waitCtx S none (.call jk)).plug [Q] ++ adm Y)) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o, wait := none } ::
        rs.map Prod.fst⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨hnp, fi, h, Yb, hx, hfi, hcode, hfx, hencb⟩ := hok.funcs f np body hW
  have hws : ws.reverse.length = np := by rw [List.length_reverse, allVals_length hargs, hlen]
  have hops : opsF args = ws.reverse.map .val := opsF_of_allVals hargs
  let F := (outer S rs a.kind).frameAt S.f0
  have hcall := run_call S (K := K) (F := F) hx hfi hcode hfx hnp hws (top_module S hok hmain)
    [] []
  have hstep := hrun F _ (top_module S hok hmain) hcall
  let q : SFrame Val × Ann := (⟨body, args, none⟩, calleeAnn S ws.reverse Yb)
  let p' : SFrame Val × Ann := ({ fr with code := c, ops := o, wait := none },
    { a with code := Y, wa := .call jk })
  have hmain' : MainOk S W (q :: p' :: rs) :=
    mainOk_push S hmain ⟨hencb, fun _ h => by cases h; rfl⟩ rfl ⟨henc, hfr.2⟩ rfl
      (Or.inl ⟨rfl, jk, rfl⟩)
  refine ⟨⟨S.s, K, S.f0, (stkCtx S (q :: p' :: rs)).plug []⟩, ?_,
    ⟨rfl, rfl, hK, q :: p' :: rs, rfl, hmain', rfl⟩⟩
  have hq : (topCtx q).plug [] = [.frame 1 (Frame.forCall S.M ws.reverse [])
      [.label 1 [] (fvals (ws.reverse.map .val) ++ adm Yb)]] := by
    rw [topCtx_fn q rfl, hops]
    rfl
  rw [code_top, code_push, hq]
  exact fplus_plus (fplus_lift _ hstep)

/-- `call f`. -/
theorem sim_call (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {f np : Nat} {body : List (Ins Val)} {c : List (Ins Val)}
    {Y : List InstrFX} {args o : List (SV Val)} {ws : List Val}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = args ++ o) (hargs : allVals args = some ws) (hlen : args.length = np)
    (hW : W f = some (np, body)) (hY : a.code = .core (.call (S.xf f)) :: Y)
    (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o, wait := none } ::
        rs.map Prod.fst⟩ := by
  refine sim_callCore S hok (jk := none) hmain hK hargs hlen hW henc (fun F Q _ h => ?_)
  have h' := fplus_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F)
    (.seq (opsF o) .hole (adm Y)) h
  simpa only [CtxV.plug, hops, hY, opsF_append, opsF_of_allVals hargs, fvals_append, adm,
    List.map_cons, InstrFX.toAdmin, waitCtx, fvals_nil, List.nil_append, List.append_nil,
    List.append_assoc, List.singleton_append] using h'

theorem i32Test_i32 (b : BitVec 32) : i32Test (Val.i32 b) = decide (b ≠ 0) := by
  by_cases hb : b = 0
  · subst hb; rfl
  · have hne : Val.i32 b ≠ Val.i32 0 := fun h => hb (by cases h; rfl)
    simp only [i32Test, bne_iff_ne, ne_eq, hne, not_false_eq_true, decide_true, hb]

/-- `cond f g` on `i32 b`: `if`, block entry, then the call of the chosen function. -/
theorem sim_cond (hok : Ok S W) {K : List (Option ContFX)}
    {KK : List (Option (List (SFrame Val)))} {fr : SFrame Val} {a : Ann}
    {rs : List (SFrame Val × Ann)} {f g np : Nat} {body : List (Ins Val)} {c : List (Ins Val)}
    {Y : List InstrFX} {args o : List (SV Val)} {ws : List Val} {b : BitVec 32}
    {bt : BlockType} {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = .val (Val.i32 b) :: args ++ o) (hargs : allVals args = some ws)
    (hlen : args.length = np)
    (hW : W (if i32Test (Val.i32 b) then f else g) = some (np, body))
    (hbt : S.M.blockType? bt = some (t₁, t₂)) (ht : t₁.length = np)
    (hY : a.code = .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: Y)
    (henc : EncI S W c Y) :
    SimGoal S W ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩
      ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o, wait := none } ::
        rs.map Prod.fst⟩ := by
  refine sim_callCore S hok (jk := some t₂.length) hmain hK hargs hlen hW henc
    (fun F Q hF h => ?_)
  have hvs : (ws.reverse.map FVal.val).length = t₁.length := by
    rw [List.length_map, List.length_reverse, allVals_length hargs, hlen, ht]
  have hif : FS S F (K, fvals (opsF (args ++ o) ++ [.val (Val.i32 b)]) ++
      .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: adm Y)
      (K, fvals (opsF (args ++ o)) ++
        .block bt [.core (.call (S.xf (if i32Test (Val.i32 b) then f else g)))] :: adm Y) := by
    by_cases hb : b = 0
    · subst hb
      simpa only [i32Test_i32, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ite_false] using step_ifFalse S (K := K) (F := F) (opsF (args ++ o)) (adm Y)
    · simpa only [i32Test_i32, ne_eq, hb, not_false_eq_true, decide_true, ite_true] using
        step_ifTrue S (K := K) (F := F) hb (opsF (args ++ o)) (adm Y)
  have hblk := step_block S (K := K) (F := F)
    (body := [.core (.call (S.xf (if i32Test (Val.i32 b) then f else g)))])
    (by rw [hF]; exact hbt) hvs (opsF o) (adm Y)
  have hlift := fplus_lift (P := S.P) (host := S.host) (fx := S.fx) (f := F)
    (.seq (opsF o) (.label t₂.length [] .hole) (adm Y)) h
  have e₁ : fvals (opsF fr.ops) ++ adm a.code = fvals (opsF (args ++ o) ++ [.val (Val.i32 b)]) ++
      .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: adm Y := by
    rw [hops, List.cons_append, hY, opsF_cons]
    rfl
  have e₂ : fvals (opsF (args ++ o)) = fvals (opsF o) ++ fvals (ws.reverse.map .val) := by
    rw [opsF_append, opsF_of_allVals hargs, fvals_append]
  have e₃ : FS S F (K, fvals (opsF (args ++ o)) ++
      .block bt [.core (.call (S.xf (if i32Test (Val.i32 b) then f else g)))] :: adm Y)
      (K, fvals (opsF o) ++ .label t₂.length []
        (fvals (ws.reverse.map .val) ++
          adm [.core (.call (S.xf (if i32Test (Val.i32 b) then f else g)))]) :: adm Y) := by
    simpa only [e₂, List.append_assoc] using hblk
  have e₄ : Relation.TransGen (FS S F) (K, fvals (opsF o) ++ .label t₂.length []
        (fvals (ws.reverse.map .val) ++
          adm [.core (.call (S.xf (if i32Test (Val.i32 b) then f else g)))]) :: adm Y)
      (K, fvals (opsF o) ++ (waitCtx S none (.call (some t₂.length))).plug [Q] ++ adm Y) := by
    simpa only [CtxV.plug, waitCtx, adm, List.map_cons, List.map_nil, InstrFX.toAdmin,
      fvals_nil, List.nil_append, List.append_nil, List.append_assoc, List.singleton_append]
      using hlift
  rw [e₁]
  exact .head hif (.head e₃ e₄)

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
