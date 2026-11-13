module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UTop

/-!
# Backward simulation: calls

* `LRun`: zero or more unique local steps;
* `lrun_localGets`: the prologue of an FX function;
* **`lpath_call`**: `call x` of an FX function of the setting: the Core `call`, the FX `invoke`
  and the prologue are the only steps (the converse of `run_call`).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (outer SX FS code_top step_localGet step_seq
  fvals_vals_map)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-- Zero or more unique local steps. -/
def LRun (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX) (s : Store H)
    (F : Frame) (a b : List (Option ContFX) × List AdminFX) : Prop :=
  a = b ∨ LPath o fx s F a b

theorem LPath.run {s : Store H} {F : Frame} {a b c : List (Option ContFX) × List AdminFX}
    (h : LPath o fx s F a b) (h' : LRun o fx s F b c) : LPath o fx s F a c := by
  rcases h' with rfl | h'
  · exact h
  · exact h.trans h'

theorem LRun.path {s : Store H} {F : Frame} {a b c : List (Option ContFX) × List AdminFX}
    (h : LRun o fx s F a b) (h' : LPath o fx s F b c) : LPath o fx s F a c := by
  rcases h with rfl | h
  · exact h'
  · exact h.trans h'

theorem lrun_plug {E : CtxV} (hE : Iso E) {s : Store H} {F : Frame}
    {a b : List (Option ContFX) × List AdminFX} (h : LRun o fx s (E.frameAt F) a b) :
    LRun o fx s F (a.1, E.plug a.2) (b.1, E.plug b.2) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr (lpath_plug hE h)

variable (S : Setup H) {W : Prog (Ins Val)} {K : List (Option ContFX)}

theorem local_forCall {ws : List Val} {j : Nat} (hj : j < ws.length) (hlt : j < 2 ^ 32) :
    (Frame.forCall S.M ws []).local? (ix j) = some (some ws[j]) := by
  simp only [Frame.local?, Frame.forCall, ix, Idx.toNat, Nat.mod_eq_of_lt hlt,
    List.map_nil, List.append_nil, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some]

/-- One `local.get` of the prologue, as a unique local step. -/
theorem lu_localGet (hS : SX S = SD o S.fx) {ws : List Val} {j : Nat} (hj : j < ws.length)
    (hlt : j < 2 ^ 32) (R : List AdminFX) :
    LU o S.fx S.s (Frame.forCall S.M ws [])
      (K, fvals ((ws.take j).map .val) ++ .core (.plain (.localGet (ix j))) :: R)
      (K, fvals ((ws.take (j + 1)).map .val) ++ R) := by
  have h₀ : Head (Profile.deterministic o) S.s (Frame.forCall S.M ws []) []
      (.plain (.localGet (ix j))) ⟨S.s, Frame.forCall S.M ws [], [ws[j].toAdmin]⟩ :=
    .variable (.localGet (local_forCall S hj hlt))
  have e₁ : fvals ((ws.take (j + 1)).map .val) ++ R =
      fvals ((ws.take j).map .val) ++ [ws[j].toAdmin].map .core ++ R := by
    simp only [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      List.map_append, Silmaril.Proofs.Wasm.Models.FXVRuns.fvals_append,
      Silmaril.Proofs.Wasm.Models.FXAsyncFX.fvals_val1, List.append_assoc, List.map_cons,
      List.map_nil]
  rw [e₁]
  have l := lu_core (fx := S.fx) (K := K) (U := (ws.take j).map .val) (T := R) h₀
    (fun h => by cases h) rfl rfl (by
      have h := toSD S hS (step_localGet S (K := K) hj hlt R)
      rw [e₁] at h
      simpa [liftV] using h)
  simpa [liftV] using l

/-- The rest of the prologue from parameter `j` on. -/
theorem lrun_localGets_from (hS : SX S = SD o S.fx) {ws : List Val} (hlt : ws.length < 2 ^ 32)
    (R : List AdminFX) : ∀ d j, j + d = ws.length →
      LRun o S.fx S.s (Frame.forCall S.M ws [])
        (K, fvals ((ws.take j).map .val) ++
          adm ((List.range' j d).map fun i => .core (.localGet (ix i))) ++ R)
        (K, fvals (ws.map .val) ++ R) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hj' : j = ws.length := by omega
    subst hj'
    left
    simp [adm]
  | succ d ih =>
    intro j hj
    have hstep := lu_localGet S (K := K) hS (j := j) (ws := ws) (by omega) (by omega)
      (adm ((List.range' (j + 1) d).map fun i => .core (.localGet (ix i))) ++ R)
    refine .inr (LPath.run (.one ?_) (ih (j + 1) (by omega)))
    simpa only [List.range'_succ, List.map_cons, adm, InstrFX.toAdmin, List.cons_append,
      List.append_assoc] using hstep

theorem lrun_localGets (hS : SX S = SD o S.fx) {ws : List Val} (hlt : ws.length < 2 ^ 32)
    (R : List AdminFX) :
    LRun o S.fx S.s (Frame.forCall S.M ws [])
      (K, adm (localGets ws.length) ++ R) (K, fvals (ws.map .val) ++ R) := by
  have h := lrun_localGets_from S (K := K) hS hlt R ws.length 0 (Nat.zero_add _)
  simpa only [List.take_zero, List.map_nil, Silmaril.Proofs.Wasm.Models.FXVRuns.fvals_nil,
    List.nil_append, localGets, List.range_eq_range'] using h

/-- **A call of an FX function of the setting**: its only steps reach the function's frame with
the parameters pushed. -/
theorem lpath_call (hS : SX S = SD o S.fx) {F : Frame} (hF : F.module = S.M) {f a np : Nat}
    {fi : FuncInst H} {h : H} {Yb : List InstrFX} {ws : List Val}
    (hx : S.M.funcs[(S.xf f).toNat]? = some a) (hfi : S.s.funcs[a]? = some fi)
    (hcode : fi.code = .host h) (hfx : S.fx h = some ⟨S.M, np, 1, [], localGets np ++ Yb⟩)
    (hnp : np < 2 ^ 32) (hws : ws.length = np) (O : List FVal) (R : List AdminFX) :
    LPath o S.fx S.s F
      (K, fvals O ++ fvals (ws.map .val) ++ .core (.plain (.call (S.xf f))) :: R)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (fvals (ws.map .val) ++ adm Yb)] :: R) := by
  have hx' : F.module.funcs[(S.xf f).toNat]? = some a := by rw [hF]; exact hx
  -- the Core `call`
  have hst₁ : Step (Profile.deterministic o) (blockFX noHost S.fx) ⟨S.s, F, [.plain (.call (S.xf f))]⟩
      ⟨S.s, F, [.ref (.func a), .callRefType fi.type]⟩ := .call hx' hfi
  have l₁ : LU o S.fx S.s F
      (K, fvals ((O ++ ws.map .val) ++ liftV []) ++ .core (.plain (.call (S.xf f))) :: R)
      (K, fvals (O ++ ws.map .val) ++ [Admin.ref (.func a), .callRefType fi.type].map .core ++ R) :=
    lu_core (c₀ := ⟨S.s, F, [.ref (.func a), .callRefType fi.type]⟩) (.call hx' hfi)
      (fun h => by cases h) rfl rfl (by
        have h := step_seq (O ++ ws.map .val) R (StepFX'.core (K := K) hst₁)
        simpa [liftV] using h)
  -- the FX `invoke`
  have hinv := step_seq (P := Profile.deterministic o) (host := noHost) (fx := S.fx) (K := K)
    (f := F) O R (StepFX'.invoke (c := .callRefType fi.type)
      (show Admin.IsCallRef (.callRefType fi.type) from trivial) hfi hcode hfx hws)
  have l₂ : LU o S.fx S.s F
      (K, fvals (O ++ liftV ws ++ [.val (.ref (.func a))]) ++ .core (.callRefType fi.type) :: R)
      (K, fvals O ++ [.frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] ((localGets np ++ Yb).map InstrFX.toAdmin)]] ++ R) := by
    refine ⟨?_, fun d hd => ?_, quiet_of rfl (isCallRef_fval trivial) trivial id trivial⟩
    · simpa [liftV, cvals, vals, FVal.toAdmin, Val.toAdmin, Function.comp_def] using hinv
    · exact uniq_invoke (Fn := ⟨S.M, np, 1, [], localGets np ++ Yb⟩) (c := .callRefType fi.type)
        (show Admin.IsCallRef (.callRefType fi.type) from trivial) hfi hcode hfx hws hd
  -- the prologue
  have l₃ := lrun_plug (o := o) (fx := S.fx) (s := S.s) (F := F)
    (E := .seq O (.frame 1 (Frame.forCall S.M ws []) (.label 1 [] .hole)) R) trivial
    (lrun_localGets S (K := K) hS (ws := ws) (by omega) (adm Yb))
  have e₁ : fvals O ++ fvals (ws.map .val) ++ .core (.plain (.call (S.xf f))) :: R =
      fvals ((O ++ ws.map .val) ++ liftV []) ++ .core (.plain (.call (S.xf f))) :: R := by
    simp [liftV]
  have e₂ : fvals (O ++ ws.map .val) ++ [Admin.ref (.func a), .callRefType fi.type].map .core ++ R =
      fvals (O ++ liftV ws ++ [.val (.ref (.func a))]) ++ .core (.callRefType fi.type) :: R := by
    simp [liftV, FVal.toAdmin, Val.toAdmin]
  rw [e₁]
  rw [e₂] at l₁
  have e₃ : (List.map InstrFX.toAdmin (localGets np ++ Yb)) = adm (localGets ws.length) ++ adm Yb := by
    rw [hws]; simp [adm]
  rw [e₃] at l₂
  have l₃' : LRun o S.fx S.s F
      (K, fvals O ++ [.frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (adm (localGets ws.length) ++ adm Yb)]] ++ R)
      (K, fvals O ++ .frame 1 (Frame.forCall S.M ws [])
        [.label 1 [] (fvals (ws.map .val) ++ adm Yb)] :: R) := by
    simpa [CtxV.plug] using l₃
  exact .cons l₁ (LPath.run (.one l₂) l₃')

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (code_push topCtx_fn mainOk_push calleeAnn top_module
  opsF_of_allVals allVals_length opsF_append) in
/-- **A call**, from the top frame's operands `args ++ o` (Core values `ws`): the converse of
`sim_callCore`. -/
theorem u_callCore (hS : SX S = SD o S.fx) (hok : Ok S W) {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {f np : Nat}
    {body : List (Ins Val)} {c : List (Ins Val)} {Y : List InstrFX} {args o' : List (SV Val)}
    {ws : List Val} {jk : Option Nat}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hargs : allVals args = some ws) (hlen : args.length = np) (hW : W f = some (np, body))
    (henc : EncI S W c Y)
    (hrun : ∀ (F : Frame) (Q : AdminFX), F.module = S.M →
      (∀ (O : List FVal) (R : List AdminFX), LPath o S.fx S.s F
        (K, fvals O ++ fvals (ws.reverse.map .val) ++ .core (.plain (.call (S.xf f))) :: R)
        (K, fvals O ++ Q :: R)) →
      LPath o S.fx S.s F (K, fvals (opsF fr.ops) ++ adm a.code) (K, fvals (opsF o') ++
        (waitCtx S none (.call jk)).plug [Q] ++ adm Y)) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o', wait := none } ::
        rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨hnp, fi, h, Yb, hx, hfi, hcode, hfx, hencb⟩ := hok.funcs f np body hW
  have hws : ws.reverse.length = np := by rw [List.length_reverse, allVals_length hargs, hlen]
  have hops : opsF args = ws.reverse.map .val := opsF_of_allVals hargs
  let F := (outer S rs a.kind).frameAt S.f0
  have hF : F.module = S.M := top_module S hok hmain
  have hstep := hrun F _ hF (fun O R => lpath_call S (K := K) hS hF hx hfi hcode hfx hnp hws O R)
  let q : SFrame Val × Ann := (⟨body, args, none⟩, calleeAnn S ws.reverse Yb)
  let p' : SFrame Val × Ann := ({ fr with code := c, ops := o', wait := none },
    { a with code := Y, wa := .call jk })
  have hmain' : MainOk S W (q :: p' :: rs) :=
    mainOk_push S hmain ⟨hencb, fun _ h => by cases h; rfl⟩ rfl ⟨henc, hfr.2⟩ rfl
      (Or.inl ⟨rfl, jk, rfl⟩)
  have hq : (topCtx q).plug [] = [.frame 1 (Frame.forCall S.M ws.reverse [])
      [.label 1 [] (fvals (ws.reverse.map .val) ++ adm Yb)]] := by
    rw [topCtx_fn q rfl, hops]
    rfl
  rw [hS, code_top]
  refine inevP_of_upath (upath_of_lpath (iso_outer S hmain) hstep) ?_
  refine ⟨rfl, rfl, hK, q :: p' :: rs, rfl, hmain', ?_⟩
  rw [code_push, hq]

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (opsF_of_allVals opsF_append opsF_cons i32Test_i32
  step_ifTrue step_ifFalse step_block allVals_length) in
/-- `call f`. -/
theorem u_call (hS : SX S = SD o S.fx) (hok : Ok S W) {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {f np : Nat}
    {body : List (Ins Val)} {c : List (Ins Val)} {Y : List InstrFX} {args o' : List (SV Val)}
    {ws : List Val} (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = args ++ o') (hargs : allVals args = some ws) (hlen : args.length = np)
    (hW : W f = some (np, body)) (hY : a.code = .core (.call (S.xf f)) :: Y)
    (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o', wait := none } ::
        rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  refine u_callCore S hS hok (jk := none) hmain hK hargs hlen hW henc (fun F Q _ lp => ?_)
  have h := lp (opsF o') (adm Y)
  have e₁ : fvals (opsF fr.ops) ++ adm a.code =
      fvals (opsF o') ++ fvals (ws.reverse.map .val) ++ .core (.plain (.call (S.xf f))) :: adm Y := by
    rw [hops, opsF_append, opsF_of_allVals hargs, hY]
    simp [adm, InstrFX.toAdmin]
  rw [e₁]
  simpa [waitCtx, CtxV.plug] using h

open Silmaril.Proofs.Wasm.Models.FXAsyncFX (opsF_of_allVals opsF_append opsF_cons i32Test_i32
  step_ifTrue step_ifFalse step_block allVals_length top_module) in
/-- `cond f g` on `i32 b`: `if`, block entry, then the call of the chosen function. -/
theorem u_cond (hS : SX S = SD o S.fx) (hok : Ok S W) {KK : List (Option (List (SFrame Val)))}
    {fr : SFrame Val} {a : Ann} {rs : List (SFrame Val × Ann)} {f g np : Nat}
    {body : List (Ins Val)} {c : List (Ins Val)} {Y : List InstrFX} {args o' : List (SV Val)}
    {ws : List Val} {b : BitVec 32} {bt : BlockType}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
    (hmain : MainOk S W ((fr, a) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hops : fr.ops = .val (Val.i32 b) :: args ++ o') (hargs : allVals args = some ws)
    (hlen : args.length = np)
    (hW : W (if i32Test (Val.i32 b) then f else g) = some (np, body))
    (hbt : S.M.blockType? bt = some (t₁, t₂)) (ht : t₁.length = np)
    (hY : a.code = .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: Y)
    (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, ⟨body, args, none⟩ :: { fr with code := c, ops := o', wait := none } ::
        rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  refine u_callCore S hS hok (jk := some t₂.length) hmain hK hargs hlen hW henc
    (fun F Q hF lp => ?_)
  let x := S.xf (if i32Test (Val.i32 b) then f else g)
  have hvs : (ws.reverse.map FVal.val).length = t₁.length := by
    rw [List.length_map, List.length_reverse, allVals_length hargs, hlen, ht]
  have hbt' : F.module.blockType? bt = some (t₁, t₂) := by rw [hF]; exact hbt
  have e₁ : fvals (opsF fr.ops) ++ adm a.code = fvals (opsF (args ++ o') ++ [.val (Val.i32 b)]) ++
      .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: adm Y := by
    rw [hops, List.cons_append, hY, opsF_cons]
    rfl
  -- `if`
  have l₁ : LU o S.fx S.s F (K, fvals (opsF (args ++ o') ++ [.val (Val.i32 b)]) ++
      .if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: adm Y)
      (K, fvals (opsF (args ++ o')) ++ [.block bt [.core (.call x)]] ++ adm Y) := by
    refine ⟨?_, fun d hd => ?_, quiet_of rfl rfl trivial id trivial⟩
    · by_cases hb : b = 0
      · subst hb
        simpa [x, i32Test_i32] using
          toSD S hS (step_ifFalse S (K := K) (F := F) (bt := bt) (b₁ := [.core (.call (S.xf f))])
            (b₂ := [.core (.call (S.xf g))]) (opsF (args ++ o')) (adm Y))
      · have hx : x = S.xf f := by
          simp only [x, i32Test_i32, ne_eq, hb, not_false_eq_true, decide_true, ite_true]
        rw [hx]
        simpa using
          toSD S hS (step_ifTrue S (K := K) (F := F) hb (bt := bt) (b₁ := [.core (.call (S.xf f))])
            (b₂ := [.core (.call (S.xf g))]) (opsF (args ++ o')) (adm Y))
    · by_cases hb : b = 0
      · subst hb
        simpa [x, i32Test_i32] using uniq_ifFalse hd
      · have hx : x = S.xf f := by
          simp only [x, i32Test_i32, ne_eq, hb, not_false_eq_true, decide_true, ite_true]
        rw [hx]
        simpa using uniq_ifTrue hb hd
  -- block entry
  have e₂ : fvals (opsF (args ++ o')) ++ [.block bt [.core (.call x)]] ++ adm Y =
      fvals (opsF o' ++ ws.reverse.map .val) ++ .block bt [.core (.call x)] :: adm Y := by
    rw [opsF_append, opsF_of_allVals hargs]
    simp
  have l₂ : LU o S.fx S.s F
      (K, fvals (opsF o' ++ ws.reverse.map .val) ++ .block bt [.core (.call x)] :: adm Y)
      (K, fvals (opsF o') ++ [.label t₂.length []
        (fvals (ws.reverse.map .val) ++ [.core (.call x)].map InstrFX.toAdmin)] ++ adm Y) := by
    refine ⟨?_, fun d hd => uniq_block hbt' hvs hd, quiet_of rfl rfl trivial id trivial⟩
    have h := toSD S hS (step_block S (K := K) (F := F) (body := [.core (.call x)]) hbt' hvs
      (opsF o') (adm Y))
    simpa [adm] using h
  -- the call, under the block's label
  have l₃ := lpath_plug (o := o) (fx := S.fx) (s := S.s) (F := F)
    (E := .seq (opsF o') (.label t₂.length [] .hole) (adm Y)) trivial (lp [] [])
  rw [e₁]
  rw [e₂] at l₁
  refine .cons l₁ (.cons l₂ ?_)
  simpa [CtxV.plug, waitCtx, InstrFX.toAdmin, x] using l₃

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
