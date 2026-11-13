module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UCall

/-!
# Backward simulation: returns

The converse of `sim_return`: a finished frame (one value) leaves its wrapper (`lpath_exit_kind`:
the label of its body, then its FX frame, or the `btD` label of an inlined handler), then the
context the frame below waited under (`lrun_exit_wait`: nothing, the label of an `if`, or the
handler frame, `br 1` and `br 0` of a `resume`); these steps are the only ones (`u_return`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (outer SX FS code_top code_push step_seq step_lift
  topCtx_plug opsF_cons encI_nil rootShape_append rootShape_of_mainOk rootShape_top
  rootShape_pop toNat_ix1 toNat_pred_ix1 frameAt_wait plug_comp)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-! ## Quiet wrappers -/

theorem quiet_label {X : List AdminFX} {V : List FVal} {n : Nat} {k : List InstrFX}
    {b T : List AdminFX} (hX : X = fvals V ++ .label n k b :: T)
    (hin : ∀ e, Deep e b → DCalm e) : Quiet X := by
  refine ⟨⟨V, _, T, hX, rfl, trivial⟩, fun e hd => ?_⟩
  rw [hX] at hd
  rcases deep_inv hd rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, hb⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, he, -⟩
  · subst he; exact absurd trivial hw
  · cases he; exact hin e hb
  · cases he
  · cases he

theorem quiet_frame {X : List AdminFX} {V : List FVal} {n : Nat} {fi : Frame}
    {b T : List AdminFX} (hX : X = fvals V ++ .frame n fi b :: T)
    (hin : ∀ e, Deep e b → DCalm e) : Quiet X := by
  refine ⟨⟨V, _, T, hX, rfl, trivial⟩, fun e hd => ?_⟩
  rw [hX] at hd
  rcases deep_inv hd rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, _, he, hb⟩ | ⟨_, _, he, -⟩
  · subst he; exact absurd trivial hw
  · cases he
  · cases he; exact hin e hb
  · cases he

theorem quiet_handler {X : List AdminFX} {V : List FVal} {hs : List HClause}
    {b T : List AdminFX} (hX : X = fvals V ++ .handler hs b :: T)
    (hin : ∀ e, Deep e b → DCalm e) : Quiet X := by
  refine ⟨⟨V, _, T, hX, rfl, trivial⟩, fun e hd => ?_⟩
  rw [hX] at hd
  rcases deep_inv hd rfl rfl with ⟨he, hw⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, he, hb⟩
  · subst he; exact absurd trivial hw
  · cases he
  · cases he
  · cases he; exact hin e hb

theorem dcalm_fvals {vs : List FVal} : ∀ e, Deep e (fvals vs) → DCalm e :=
  fun _ h => (not_deep_fvals h).elim

theorem dcalm_br {vs : List FVal} {l : LabelIdx} {T : List AdminFX} :
    ∀ e, Deep e (fvals vs ++ .core (.plain (.br l)) :: T) → DCalm e := by
  intro e h
  rw [deep_unique h (Deep.here rfl id)]
  trivial

/-! ## Leaving a frame's wrapper -/

variable {s : Store H} {K : List (Option ContFX)}

theorem lu_labelVals {G : Frame} {O vs : List FVal} {n : Nat} {k : List InstrFX}
    {R : List AdminFX} :
    LU o fx s G (K, fvals O ++ .label n k (fvals vs) :: R) (K, fvals O ++ fvals vs ++ R) := by
  refine ⟨?_, fun d hd => uniq_labelVals hd, quiet_label rfl dcalm_fvals⟩
  simpa using step_seq O R (StepFX'.labelVals (P := Profile.deterministic o) (host := noHost)
    (fx := fx) (s := s) (K := K) (f := G) (n := n) (k := k) (vs := vs))

theorem lu_frameVals {G : Frame} {O vs : List FVal} {n : Nat} {fi : Frame}
    {R : List AdminFX} (hn : vs.length = n) :
    LU o fx s G (K, fvals O ++ .frame n fi (fvals vs) :: R) (K, fvals O ++ fvals vs ++ R) := by
  refine ⟨?_, fun d hd => uniq_frameVals hd, quiet_frame rfl dcalm_fvals⟩
  simpa using step_seq O R (StepFX'.frameVals (P := Profile.deterministic o) (host := noHost)
    (fx := fx) (s := s) (K := K) (f := G) (fi := fi) hn)

theorem lu_handlerVals {G : Frame} {O vs : List FVal} {hs : List HClause} {R : List AdminFX} :
    LU o fx s G (K, fvals O ++ .handler hs (fvals vs) :: R) (K, fvals O ++ fvals vs ++ R) := by
  refine ⟨?_, fun d hd => uniq_handlerVals hd, quiet_handler rfl dcalm_fvals⟩
  simpa using step_seq O R (StepFX'.handlerVals (P := Profile.deterministic o) (host := noHost)
    (fx := fx) (s := s) (K := K) (f := G) (hs := hs) (vs := vs))

/-- **A finished frame leaves its wrapper**, and that is the only run. -/
theorem lpath_exit_kind {k : Kind} (hk : k.isRoot = false) (G : Frame) (O : List FVal)
    (R : List AdminFX) (x : FVal) :
    LPath o fx s G (K, fvals O ++ (kindCtx k .hole).plug (fvals [x]) ++ R)
      (K, fvals O ++ fvals [x] ++ R) := by
  match k, hk with
  | .fn fi, _ =>
    have l₁ := lu_plug (o := o) (fx := fx) (s := s) (F := G) (E := .seq O (.frame 1 fi .hole) R)
      trivial (lu_labelVals (K := K) (O := []) (vs := [x]) (n := 1) (k := []) (R := []))
    have l₂ := lu_frameVals (o := o) (fx := fx) (s := s) (K := K) (G := G) (O := O) (vs := [x])
      (fi := fi) (R := R) rfl
    refine .cons ?_ (.one l₂)
    simpa [CtxV.plug, kindCtx] using l₁
  | .blk, _ =>
    simpa [CtxV.plug, kindCtx] using
      (LPath.one (lu_labelVals (o := o) (fx := fx) (s := s) (G := G) (K := K) (O := O)
        (vs := [x]) (n := 1) (k := []) (R := R)))

theorem lu_brSucc {G : Frame} {A : List FVal} {n : Nat} {k : List InstrFX} {l : LabelIdx}
    {T : List AdminFX} (hl : 0 < l.toNat) :
    LU o fx s G (K, fvals [] ++ .label n k (fvals A ++ [.core (.plain (.br l))]) :: T)
      (K, fvals [] ++ fvals A ++ [.core (.plain (.br (labelPred l)))] ++ T) := by
  refine ⟨?_, fun d hd => ?_, quiet_label rfl dcalm_br⟩
  · simpa using step_seq [] T (StepFX'.brLabelSucc (P := Profile.deterministic o) (host := noHost)
      (fx := fx) (s := s) (K := K) (f := G) (n := n) (k := k) (vs := A) (rest := []) hl)
  · exact uniq_brSucc (U := []) (rest := []) hl hd

theorem lu_brZero {G : Frame} {O : List FVal} {vs : List FVal} {n : Nat} {k : List InstrFX}
    {l : LabelIdx} {rest R : List AdminFX} (hl : l.toNat = 0) (hn : vs.length = n) :
    LU o fx s G (K, fvals O ++ .label n k (fvals vs ++ .core (.plain (.br l)) :: rest) :: R)
      (K, fvals O ++ fvals vs ++ k.map InstrFX.toAdmin ++ R) := by
  refine ⟨?_, fun d hd => uniq_brZero (A := []) hl hn (by simpa using hd), quiet_label rfl dcalm_br⟩
  simpa using step_seq O R (StepFX'.brLabelZero (P := Profile.deterministic o) (host := noHost)
    (fx := fx) (s := s) (K := K) (f := G) (n := n) (k := k) (vs' := []) (vs := vs) (rest := rest)
    hl hn)

variable (S : Setup H) {W : Prog (Ins Val)}

/-- The value leaves an inlined handler's `resume`: the handler frame, `br 1`, `br 0`. -/
theorem lpath_exit_res (G : Frame) (O : List FVal) (R : List AdminFX) (x : FVal) (t : Nat)
    (hf : Nat) (Z : List InstrFX) :
    LPath o fx s G (K, fvals O ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug (fvals [x]) ++ R)
      (K, fvals O ++ fvals [x] ++ R) := by
  have l₁ : LU o fx s G (K, fvals O ++ (waitCtx S (some [⟨t, hf⟩]) (.res Z)).plug (fvals [x]) ++ R)
      (K, fvals O ++ [.label 1 [] (.label (S.ar t + 1) [] (fvals [x] ++ [br1]) :: adm Z)] ++ R) := by
    simpa [waitCtx, CtxV.plug] using lu_plug (o := o) (fx := fx) (s := s) (F := G)
      (E := .seq O (.label 1 [] (.seq [] (.label (S.ar t + 1) [] .hole) (adm Z))) R) trivial
      (lu_handlerVals (K := K) (O := []) (vs := [x]) (hs := [.onLabel (S.ta t) (ix 0)])
        (R := [br1]))
  have l₂ : LU o fx s G
      (K, fvals O ++ [.label 1 [] (.label (S.ar t + 1) [] (fvals [x] ++ [br1]) :: adm Z)] ++ R)
      (K, fvals O ++ [.label 1 [] (fvals [x] ++ [.core (.plain (.br (labelPred (ix 1))))] ++
        adm Z)] ++ R) := by
    simpa [CtxV.plug, br1] using lu_plug (o := o) (fx := fx) (s := s) (F := G)
      (E := .seq O (.label 1 [] .hole) R) trivial (lu_brSucc (K := K) (A := [x])
        (n := S.ar t + 1) (k := []) (l := ix 1) (T := adm Z) (by rw [toNat_ix1]; exact Nat.one_pos))
  have l₃ : LU o fx s G
      (K, fvals O ++ [.label 1 [] (fvals [x] ++ [.core (.plain (.br (labelPred (ix 1))))] ++
        adm Z)] ++ R) (K, fvals O ++ fvals [x] ++ R) := by
    simpa using lu_brZero (o := o) (fx := fx) (s := s) (G := G) (K := K) (O := O) (vs := [x])
      (n := 1) (k := []) (l := labelPred (ix 1)) (rest := adm Z) (R := R) toNat_pred_ix1 rfl
  exact .cons l₁ (.cons l₂ (.one l₃))

/-- **The value leaves the context the frame below waited under**, and that is the only run. -/
theorem lrun_exit_wait {p : SFrame Val × Ann} (hp : WaitOk S W p) (G : Frame) (O : List FVal)
    (R : List AdminFX) (x : FVal) :
    LRun o fx s G (K, fvals O ++ (waitCtx S p.1.wait p.2.wa).plug (fvals [x]) ++ R)
      (K, fvals O ++ fvals [x] ++ R) := by
  rcases hp with ⟨hw, jk, hwa⟩ | ⟨t, hf, np, bh, Z, hw, hwa, -, -⟩
  · rw [hw, hwa]
    match jk with
    | none => exact .inl rfl
    | some n =>
      exact .inr (.one (by simpa [waitCtx, CtxV.plug] using
        (lu_labelVals (o := o) (fx := fx) (s := s) (G := G) (K := K) (O := O) (vs := [x])
          (n := n) (k := []) (R := R))))
  · rw [hw, hwa]
    exact .inr (lpath_exit_res S G O R x t hf Z)

/-- A finished frame leaves its wrapper inside the context the frame below waits under. -/
theorem lpath_exit_kind_wait {p : SFrame Val × Ann} (hp : WaitOk S W p) {k : Kind}
    (hk : k.isRoot = false) (G : Frame) (O : List FVal) (R : List AdminFX) (x : FVal) :
    LPath o fx s G
      (K, fvals O ++ (waitCtx S p.1.wait p.2.wa).plug ((kindCtx k .hole).plug (fvals [x])) ++ R)
      (K, fvals O ++ (waitCtx S p.1.wait p.2.wa).plug (fvals [x]) ++ R) := by
  rcases hp with ⟨hw, jk, hwa⟩ | ⟨t, hf, np, bh, Z, hw, hwa, -, -⟩
  · rw [hw, hwa]
    match jk with
    | none =>
      have h := lpath_exit_kind (o := o) (fx := fx) (s := s) (K := K) hk G O R x
      simpa [waitCtx, CtxV.plug] using h
    | some n =>
      have h := lpath_plug (o := o) (fx := fx) (s := s) (F := G)
        (E := .seq O (.label n [] .hole) R) trivial
        (lpath_exit_kind (K := K) hk G [] [] x)
      simpa [waitCtx, CtxV.plug] using h
  · rw [hw, hwa]
    have h := lpath_plug (o := o) (fx := fx) (s := s) (F := G)
      (E := .seq O (.label 1 [] (.seq [] (.label (S.ar t + 1) []
        (.seq [] (.handler [.onLabel (S.ta t) (ix 0)] .hole) [br1])) (adm Z))) R) trivial
      (lpath_exit_kind (K := K) hk G [] [] x)
    simpa [waitCtx, CtxV.plug] using h

/-- **A return** of the top frame (one value `r`) to the frame below: the converse of
`sim_return`. -/
theorem u_return (hS : SX S = SD o S.fx) {KK : List (Option (List (SFrame Val)))}
    {fr b : SFrame Val} {a ab : Ann} {rs : List (SFrame Val × Ann)} {r : SV Val}
    (hmain : MainOk S W ((fr, a) :: (b, ab) :: rs)) (hK : List.Forall₂ (KRel S W) KK K)
    (hc : fr.code = []) (hops : fr.ops = [r]) :
    InevP (SX S) TermFX (Rel S W ⟨KK, { b with ops := fr.ops ++ b.ops } :: rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: (b, ab) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  have hY : a.code = [] := encI_nil S (hc ▸ hfr.1)
  have hroot : a.kind.isRoot = false :=
    (rootShape_append (xs := [(fr, a)]) (rootShape_of_mainOk S hmain) (List.cons_ne_nil _ _)).2
      _ (List.mem_singleton_self _)
  have hw : WaitOk S W (b, ab) := hmain.2.1 _ (List.mem_cons_self ..)
  let G : Frame := (outer S rs ab.kind).frameAt S.f0
  let p' : SFrame Val × Ann := ({ b with ops := fr.ops ++ b.ops }, ab)
  have hmain₂ : MainOk S W ((b, ab) :: rs) := by
    refine ⟨fun q hq => hmain.1 q (List.mem_cons_of_mem _ hq),
      fun q hq => hmain.2.1 q (List.mem_cons_of_mem _ hq),
      rootShape_pop (rootShape_of_mainOk S hmain)⟩
  have hmain' : MainOk S W (p' :: rs) := by
    refine ⟨fun q hq => ?_, fun q hq => hmain.2.1 q (List.mem_cons_of_mem _ hq),
      rootShape_top (rootShape_pop (rootShape_of_mainOk S hmain)) rfl⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hmain.1 (b, ab) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact hmain.1 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  have hstart : (stkCtx S ((fr, a) :: (b, ab) :: rs)).plug [] = (outer S rs ab.kind).plug
      (fvals (opsF b.ops) ++ (waitCtx S b.wait ab.wa).plug
        ((kindCtx a.kind .hole).plug (fvals [toF r])) ++ adm ab.code) := by
    rw [code_push, topCtx_plug, hops, hY]
    simp [opsF, adm]
  have hend : (stkCtx S (p' :: rs)).plug [] =
      (outer S rs ab.kind).plug (fvals (opsF b.ops) ++ fvals [toF r] ++ adm ab.code) := by
    rw [code_top]
    simp [p', hops, opsF]
  have hpath : LPath o S.fx S.s G
      (K, fvals (opsF b.ops) ++ (waitCtx S b.wait ab.wa).plug
        ((kindCtx a.kind .hole).plug (fvals [toF r])) ++ adm ab.code)
      (K, fvals (opsF b.ops) ++ fvals [toF r] ++ adm ab.code) :=
    LPath.run (lpath_exit_kind_wait S hw hroot G _ _ _) (lrun_exit_wait S hw G _ _ _)
  rw [hS, hstart]
  refine inevP_of_upath (upath_of_lpath (iso_outer S hmain₂) hpath) ?_
  exact ⟨rfl, rfl, hK, p' :: rs, rfl, hmain', hend.symm⟩

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
