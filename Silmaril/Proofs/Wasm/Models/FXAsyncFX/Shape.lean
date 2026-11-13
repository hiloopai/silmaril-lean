module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Local

/-!
# The shape of encoded stacks

* `outer`, `code_top`: the code of an annotated stack is the top frame's operands and code,
  plugged into the waiting frames and the top frame's wrapper;
* `lowsCtx_append`, `stkCtx_append`: stacks split into segments compose;
* `modM_lows`, `modM_outer`: every frame of the context belongs to `M`;
* `mainOk_top`, `mainOk_pop`: well-formedness after changing the top frame, or after it returns;
* `split_ann`: the kernel's `split` on an annotated stack;
* `not_handles_lows`: frames passed by `split` do not handle the tag;
* `lowCtx_res`: a waiting resumer's context ends with its handler frame.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- The waiting frames and the top frame's wrapper. -/
def outer (rs : List (SFrame Val × Ann)) (k : Kind) : CtxV := comp (lowsCtx S rs) (kindCtx k .hole)

theorem kindCtx_plug (k : Kind) (E : CtxV) (X : List AdminFX) :
    (kindCtx k E).plug X = (kindCtx k .hole).plug (E.plug X) := by
  rw [kindCtx_eq, plug_comp]

theorem topCtx_plug (p : SFrame Val × Ann) (X : List AdminFX) :
    (topCtx p).plug X = (kindCtx p.2.kind .hole).plug (fvals (opsF p.1.ops) ++ X ++ adm p.2.code) :=
  kindCtx_plug p.2.kind _ X

theorem lowCtx_plug (p : SFrame Val × Ann) (X : List AdminFX) :
    (lowCtx S p).plug X = (kindCtx p.2.kind .hole).plug
      (fvals (opsF p.1.ops) ++ (waitCtx S p.1.wait p.2.wa).plug X ++ adm p.2.code) :=
  kindCtx_plug p.2.kind _ X

/-- **The code of a stack** around its top frame. -/
theorem code_top (p : SFrame Val × Ann) (rs : List (SFrame Val × Ann)) :
    (stkCtx S (p :: rs)).plug [] =
      (outer S rs p.2.kind).plug (fvals (opsF p.1.ops) ++ adm p.2.code) := by
  simp only [stkCtx, outer, plug_comp, topCtx_plug, List.append_nil]

theorem lowsCtx_append (xs ys : List (SFrame Val × Ann)) :
    lowsCtx S (xs ++ ys) = comp (lowsCtx S ys) (lowsCtx S xs) := by
  induction xs with
  | nil => simp only [List.nil_append, lowsCtx, comp_hole]
  | cons p xs ih => simp only [List.cons_append, lowsCtx, ih, comp_assoc]

theorem stkCtx_append {xs : List (SFrame Val × Ann)} (hxs : xs ≠ [])
    (ys : List (SFrame Val × Ann)) :
    stkCtx S (xs ++ ys) = comp (lowsCtx S ys) (stkCtx S xs) := by
  match xs, hxs with
  | p :: xs, _ => simp only [List.cons_append, stkCtx, lowsCtx_append, comp_assoc]

/-! ## Frames of the module -/

theorem modM_kind (k : Kind) (E : CtxV) (hk : ∀ fi, k = .fn fi → fi.module = S.M)
    (hE : ModM S.M E) : ModM S.M (kindCtx k E) := by
  match k with
  | .fn fi => exact ⟨hk fi rfl, hE⟩
  | .blk => exact hE
  | .root => exact hE

theorem modM_wait (w : Option (List Clause)) (wa : WA) : ModM S.M (waitCtx S w wa) := by
  unfold waitCtx
  split <;> trivial

theorem modM_lows (rs : List (SFrame Val × Ann)) (hrs : ∀ p ∈ rs, FrOk S W p) :
    ModM S.M (lowsCtx S rs) := by
  induction rs with
  | nil => trivial
  | cons p rs ih =>
    have hp : ModM S.M (lowCtx S p) :=
      modM_kind S _ _ (hrs p (List.mem_cons_self ..)).2 (modM_wait S _ _)
    exact (modM_comp _ _).mpr ⟨ih fun q hq => hrs q (List.mem_cons_of_mem _ hq), hp⟩

/-- The frame at the top of a well-formed stack belongs to `M`. -/
theorem outer_module (hok : Ok S W) (p : SFrame Val × Ann) (rs : List (SFrame Val × Ann))
    (hst : ∀ q ∈ p :: rs, FrOk S W q) :
    ((outer S rs p.2.kind).frameAt S.f0).module = S.M := by
  have hlows : ModM S.M (lowsCtx S rs) := modM_lows S rs fun q hq => hst q (List.mem_cons_of_mem _ hq)
  have hk : ModM S.M (kindCtx p.2.kind .hole) :=
    modM_kind S _ _ (hst p (List.mem_cons_self ..)).2 trivial
  exact frameAt_module _ ((modM_comp _ _).mpr ⟨hlows, hk⟩) hok.root

/-! ## Well-formed stacks -/

theorem mainOk_frames {st : List (SFrame Val × Ann)} (h : MainOk S W st) :
    ∀ p ∈ st, FrOk S W p := h.1

/-- Change the top frame, keeping its wrapper. -/
theorem mainOk_top {p p' : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (h : MainOk S W (p :: rs)) (hp' : FrOk S W p') (hk : p'.2.kind = p.2.kind) :
    MainOk S W (p' :: rs) := by
  obtain ⟨hfr, htl, init, last, heq, hlast, hinit⟩ := h
  refine ⟨?_, htl, ?_⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp'
    · exact hfr q (List.mem_cons_of_mem _ hq)
  · match init, heq with
    | [], heq =>
      have hp : p = last ∧ rs = [] := by simpa only [List.nil_append, List.cons.injEq] using heq
      exact ⟨[], p', by rw [hp.2]; rfl, by rw [hk, hp.1]; exact hlast, fun _ h => absurd h List.not_mem_nil⟩
    | q :: init', heq =>
      have hp : p = q ∧ rs = init' ++ [last] := by simpa only [List.cons_append, List.cons.injEq] using heq
      refine ⟨p' :: init', last, by rw [hp.2]; rfl, hlast, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [hk, hp.1]; exact hinit q (List.mem_cons_self ..)
      · exact hinit r (List.mem_cons_of_mem _ hr)

/-! ## The root at the bottom -/

/-- The root frame is the last one, and only that one. -/
def RootShape (st : List (SFrame Val × Ann)) : Prop :=
  ∃ init last, st = init ++ [last] ∧ last.2.kind = .root ∧ ∀ p ∈ init, p.2.kind.isRoot = false

theorem rootShape_of_mainOk {st : List (SFrame Val × Ann)} (h : MainOk S W st) : RootShape st :=
  h.2.2

theorem rootShape_append {xs ys : List (SFrame Val × Ann)} (h : RootShape (xs ++ ys))
    (hys : ys ≠ []) : RootShape ys ∧ ∀ p ∈ xs, p.2.kind.isRoot = false := by
  obtain ⟨init, last, heq, hlast, hinit⟩ := h
  obtain ⟨ys', y, rfl⟩ : ∃ ys' y, ys = ys' ++ [y] := ⟨ys.dropLast, ys.getLast hys,
    (List.dropLast_append_getLast hys).symm⟩
  have h2 : (xs ++ ys') ++ [y] = init ++ [last] := by rw [List.append_assoc]; exact heq
  have h3 : xs ++ ys' = init ∧ [y] = [last] := List.append_inj' h2 rfl
  have hsplit : xs ++ ys' = init ∧ y = last := ⟨h3.1, List.singleton_inj.mp h3.2⟩
  refine ⟨⟨ys', y, rfl, hsplit.2 ▸ hlast, fun p hp => hinit p ?_⟩, fun p hp => hinit p ?_⟩
  · rw [← hsplit.1]; exact List.mem_append_right _ hp
  · rw [← hsplit.1]; exact List.mem_append_left _ hp

theorem rootShape_cons {p : SFrame Val × Ann} {st : List (SFrame Val × Ann)} (h : RootShape st)
    (hp : p.2.kind.isRoot = false) : RootShape (p :: st) := by
  obtain ⟨init, last, rfl, hlast, hinit⟩ := h
  refine ⟨p :: init, last, rfl, hlast, fun q hq => ?_⟩
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hp
  · exact hinit q hq

theorem rootShape_seg {seg rs : List (SFrame Val × Ann)} (h : RootShape rs)
    (hseg : ∀ p ∈ seg, p.2.kind.isRoot = false) : RootShape (seg ++ rs) := by
  induction seg with
  | nil => exact h
  | cons p seg ih =>
    exact rootShape_cons (ih fun q hq => hseg q (List.mem_cons_of_mem _ hq))
      (hseg p (List.mem_cons_self ..))

theorem rootShape_top {p p' : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (h : RootShape (p :: rs)) (hk : p'.2.kind = p.2.kind) : RootShape (p' :: rs) := by
  obtain ⟨init, last, heq, hlast, hinit⟩ := h
  match init, heq with
  | [], heq =>
    have hp : p = last ∧ rs = [] := by simpa only [List.nil_append, List.cons.injEq] using heq
    exact ⟨[], p', by rw [hp.2]; rfl, by rw [hk, hp.1]; exact hlast,
      fun _ h => absurd h List.not_mem_nil⟩
  | q :: init', heq =>
    have hp : p = q ∧ rs = init' ++ [last] := by
      simpa only [List.cons_append, List.cons.injEq] using heq
    refine rootShape_cons ⟨init', last, hp.2, hlast, fun r hr => hinit r ?_⟩ ?_
    · exact List.mem_cons_of_mem _ hr
    · rw [hk, hp.1]; exact hinit q (List.mem_cons_self ..)

theorem rootShape_pop {p q : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (h : RootShape (p :: q :: rs)) : RootShape (q :: rs) :=
  (rootShape_append (xs := [p]) h (List.cons_ne_nil _ _)).1

/-! ## Suspension: the frames passed and the handling resumer -/

/-- The kernel's `split` on an annotated stack. -/
theorem split_ann (t : Nat) : ∀ (rs : List (SFrame Val × Ann)) {m : List (SFrame Val)} {h : Nat}
    {r : SFrame Val} {rs' : List (SFrame Val)}, split t (rs.map Prod.fst) = some (m, h, r, rs') →
    ∃ mA q rsA, rs = mA ++ q :: rsA ∧ m = mA.map Prod.fst ∧ r = q.1 ∧
      rs' = rsA.map Prod.fst ∧ q.1.wait.bind (lookup t) = some h ∧
      ∀ p ∈ mA, p.1.wait.bind (lookup t) = none
  | [], _, _, _, _, hs => by simp only [List.map_nil, split, reduceCtorEq] at hs
  | q :: rs, m, h, r, rs', hs => by
    cases hq : q.1.wait.bind (lookup t) with
    | some h' =>
      have hs' : some ([], h', q.1, rs.map Prod.fst) = some (m, h, r, rs') := by
        simpa only [List.map_cons, split, hq] using hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
      exact ⟨[], q, rs, rfl, rfl, rfl, rfl, hq, fun _ h => absurd h List.not_mem_nil⟩
    | none =>
      have hs' : (split t (rs.map Prod.fst)).map (fun x => (q.1 :: x.1, x.2)) =
          some (m, h, r, rs') := by
        simpa only [List.map_cons, split, hq] using hs
      obtain ⟨⟨m', h', r', rs''⟩, hsp, heq⟩ := Option.map_eq_some_iff.mp hs'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      obtain ⟨mA, q', rsA, rfl, rfl, rfl, rfl, hq', hmA⟩ := split_ann t rs hsp
      refine ⟨q :: mA, q', rsA, rfl, rfl, rfl, rfl, hq', fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · exact hmA p hp

theorem handles_kind (k : Kind) (E : CtxV) (ta : Nat) :
    (kindCtx k E).Handles ta ↔ E.Handles ta := by
  cases k <;> exact Iff.rfl

theorem lookup_single {t t' hf h : Nat} (hl : lookup t [⟨t', hf⟩] = some h) : t' = t ∧ hf = h := by
  by_cases ht : t' = t
  · subst ht
    simp only [lookup, List.find?_cons, BEq.rfl, Option.map_some,
      Option.some.injEq] at hl
    exact ⟨rfl, hl⟩
  · have hne : (t' == t) = false := by simpa only [beq_eq_false_iff_ne, ne_eq] using ht
    simp only [lookup, List.find?_cons, hne, List.find?_nil, Option.map_none, reduceCtorEq] at hl

/-- A frame passed by `split` does not handle the tag. -/
theorem not_handles_low (hok : Ok S W) {t : Nat} {p : SFrame Val × Ann} (hp : WaitOk S W p)
    (hl : p.1.wait.bind (lookup t) = none) : ¬ (lowCtx S p).Handles (S.ta t) := by
  rw [lowCtx, handles_kind]
  rcases hp with ⟨hw, jk, hwa⟩ | ⟨t', hf, np, bh, Z, hw, hwa, -, -⟩
  · rw [hw, hwa]
    cases jk <;> exact id
  · rw [hw, hwa]
    have hne : t' ≠ t := by
      intro heq
      subst heq
      simp only [hw, Option.bind_some, lookup, List.find?_cons, BEq.rfl,
        Option.map_some, reduceCtorEq] at hl
    intro hh
    simp only [waitCtx, CtxV.Handles, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_left, HClause.tag] at hh
    exact hne (hok.tags hh)

theorem not_handles_lows (hok : Ok S W) {t : Nat} (mA : List (SFrame Val × Ann))
    (hw : ∀ p ∈ mA, WaitOk S W p) (hl : ∀ p ∈ mA, p.1.wait.bind (lookup t) = none) :
    ¬ (lowsCtx S mA).Handles (S.ta t) := by
  induction mA with
  | nil => exact id
  | cons p mA ih =>
    rw [lowsCtx, handles_comp]
    rintro (h | h)
    · exact ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
        (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h
    · exact not_handles_low S hok (hw p (List.mem_cons_self ..)) (hl p (List.mem_cons_self ..)) h

theorem not_handles_top (p : SFrame Val × Ann) (ta : Nat) : ¬ (topCtx p).Handles ta := by
  rw [topCtx, handles_kind]
  exact id

theorem kindCtx_comp (k : Kind) (E E' : CtxV) : comp (kindCtx k E) E' = kindCtx k (comp E E') := by
  cases k <;> rfl

/-- The part of a waiting resumer's context outside its `block btH` label. -/
def preD (p : SFrame Val × Ann) (Z : List InstrFX) : CtxV :=
  kindCtx p.2.kind (.seq (opsF p.1.ops) (.label 1 [] (.seq [] .hole (adm Z))) (adm p.2.code))

/-- The part of a waiting resumer's context outside its handler frame. -/
def preH (p : SFrame Val × Ann) (t : Nat) (Z : List InstrFX) : CtxV :=
  comp (preD p Z) (.label (S.ar t + 1) [] (.seq [] .hole [br1]))

theorem lowCtx_res {p : SFrame Val × Ann} {t hf : Nat} {Z : List InstrFX}
    (hw : p.1.wait = some [⟨t, hf⟩]) (hwa : p.2.wa = .res Z) :
    lowCtx S p = comp (preH S p t Z) (.handler [.onLabel (S.ta t) (ix 0)] .hole) := by
  simp only [lowCtx, hw, hwa, preH, preD, comp_assoc, kindCtx_comp]
  rfl

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
