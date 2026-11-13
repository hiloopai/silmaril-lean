module

public import Silmaril.Proofs.Wasm.FX.Examples.EveryRun.Cancel

/-!
# Switching between two coroutines, by the every-run logic

`switch_tsafe`: the program `switchProg` (`Silmaril.Wasm.FX.Examples.EveryRun.Defs`) is totally
safe, at every profile without host calls, for the postcondition "returns `[42]`":

* `start_spec`: `startFX f` runs a coroutine whose body begins with `suspend` up to that
  suspension and leaves its continuation `coK rest` on the stack (`co_suspend`);
* the main function resumes `A` with `B`'s continuation under `(on $e switch)`. For the payload
  `[B]`, `A` switches to `B` (`tsafe_switch_seq` and the handler rule's `switch` arm), `B` drops
  `A`'s new continuation (`tsafe_dropCont_seq`) and returns `42` through the handler; for the
  empty payload, `A`'s `switch` has no continuation to switch to and is stuck
  (`tsafe_switch_nil_seq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled TSafe Inv seqPost labelPost framePost handlerPost totJ)
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- The frame of every function of the switch example. -/
abbrev sF : Frame := ⟨[], swM⟩

/-- The resolved switch handler. -/
def switchHs : List HClause := [.onSwitch 0]

/-- The continuation of a coroutine suspended before the code `rest`. -/
def coK (rest : List AdminFX) : ContFX := ⟨fun c => [.frame 1 sF [.label 1 [] (c ++ rest)]]⟩

/-- The instance of function `f`. -/
abbrev swFi (f : Nat) : FuncInst Nat := ⟨kitTypes.head!, swM, .host f⟩

theorem sw_tag : swStore.tag? sF (ix 0) = some (0, ⟨kitTypes.head!⟩) := rfl

theorem sw_handles {hs : List HClause} {E : CtxV} {x : TagIdx} (hx : x = ix 0)
    (hcl : ∃ c ∈ hs, c.tag = 0) (hu : Unhandled swStore sF (.handler hs E) x)
    (hf : E.frameAt sF = sF) : False := by
  subst hx
  exact hu 0 _ (by rw [CtxV.frameAt, hf]; rfl) (Or.inl hcl)

variable {Q₁ : PostFX Nat} {K : Conts}

/-- **A coroutine that suspends at once**, under the yield handler. -/
theorem co_suspend (hQ₁ : Inv Q₁) (rest : List AdminFX)
    (h : Q₁ swStore (K ++ [some (coK rest)]) sF (.br 0 [.cont K.length])) :
    TSafe P swFx (handlerPost (totJ P swFx Q₁) yieldHs [] Q₁)
      ⟨swStore, K, sF, [.frame 1 sF [.label 1 [] (.fx (.suspend (ix 0)) :: rest)]]⟩ := by
  refine tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_suspend_seq (V := []) (by inv_tac) fun V₁ vs hV => ?_
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV.symm
  simp only [labelPost, framePost, handlerPost]
  refine ⟨fun ta ti l ht _ hc => ?_,
    fun hu => (sw_handles rfl ⟨.onLabel 0 (ix 0), by simp [yieldHs], rfl⟩ hu rfl).elim⟩
  have ht' : swStore.tag? sF (ix 0) = some (ta, ti) := ht
  rw [sw_tag] at ht'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ht')
  have hl : l = ix 0 := by simp [yieldHs] at hc; exact hc.2.symm
  rw [hl, show (ix 0 : LabelIdx).toNat = 0 from rfl]
  have hK : (⟨(CtxV.seq [] (.frame 1 sF (.seq [] (.label 1 [] (.seq [] .hole rest)) [])) []).plug⟩ :
      ContFX) = coK rest := by
    simp only [coK, ContFX.mk.injEq]; funext c; simp [CtxV.plug]
  simpa [hK] using h

/-- **Starting a coroutine** `f` whose body begins with `suspend`: its continuation is left on
the stack. -/
theorem start_spec {Q : PostFX Nat} (hQ : Inv Q) {V : List FVal} {rest : List AdminFX}
    (f : Nat) (restf : List AdminFX)
    (hx : swM.funcs[(ix f : FuncIdx).toNat]? = some f) (hf : swStore.funcs[f]? = some (swFi f))
    (hfx : swFx f = some ⟨swM, 0, 1, [], switchWY f⟩)
    (hb : (switchWY f).map InstrFX.toAdmin = .fx (.suspend (ix 0)) :: restf)
    (h : TSafe P swFx Q ⟨swStore, (K ++ [some (newCont f (swFi f))]).set K.length none ++
      [some (coK restf)], sF, fvals (V ++ [.cont (K.length + 1)]) ++ rest⟩) :
    TSafe P swFx Q ⟨swStore, K, sF, fvals V ++ InstrFX.toAdmin (startFX f) :: rest⟩ := by
  refine tsafe_block_seq hQ (t₁ := []) (t₂ := [ti32]) rfl fun V₁ vs hV hm => ?_
  obtain rfl : vs = [] := List.length_eq_zero_iff.mp hm
  obtain rfl : V₁ = V := by simpa using hV.symm
  refine tsafe_refFunc (V := []) (by inv_tac) hx ?_
  refine tsafe_contNew_seq (V := []) (by inv_tac) hf ?_
  refine tsafe_resume_seq (V := []) (C := newCont f (swFi f)) (by inv_tac) (by simp) rfl
    fun V₁ vs hV => ?_
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV.symm
  show TSafe _ _ _ ⟨_, _, _, fvals ([] ++ [.val (.ref (.func f))]) ++ [.core (.callRefType _)]⟩
  refine tsafe_invoke (by simp [Admin.IsCallRef]) hf rfl hfx fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  show TSafe _ _ _ ⟨_, _, _, [.frame 1 sF [.label 1 [] ((switchWY f).map InstrFX.toAdmin)]]⟩
  rw [hb]
  refine co_suspend (by inv_tac) restf ?_
  simp only [seqPost, labelPost]
  intro vs₁ vs₂ h12 hl
  rw [split_one h12 hl]
  simp only [totJ, List.map_nil, List.append_nil, List.length_set, List.length_append,
    List.length_singleton]
  refine tsafe_vals ?_
  simpa [seqPost, totJ] using h

/-- The code of `B` and `A` after their first `suspend`. -/
def restB : List AdminFX := [.core (.plain .drop), .core (.plain (.intConst .i32 42)), .core (.plain .nop)]

def restA : List AdminFX := [.fx (.switch (ix 0) (ix 0))]

theorem cont_split {k : Nat} {V₁ vs : List FVal} (h : [FVal.cont k] = V₁ ++ vs) :
    (V₁ = [] ∧ vs = [.cont k]) ∨ (V₁ = [.cont k] ∧ vs = []) := by
  rcases V₁ with _ | ⟨w, _ | ⟨w', V₁⟩⟩
  · exact Or.inl ⟨rfl, h.symm⟩
  · simp only [List.singleton_append, List.cons.injEq] at h
    exact Or.inr ⟨by rw [h.1], h.2.symm⟩
  · simp at h

/-- `B` after the switch: drop `A`'s continuation, return `42`. -/
theorem b_ret {K' : Conts} (hQ₁ : Inv Q₁) (k : Nat) (hr : Q₁ swStore K' sF (.normal [.val (Val.i32 42)])) :
    TSafe P swFx (handlerPost (totJ P swFx Q₁) switchHs [] Q₁)
      ⟨swStore, K', sF, (coK restB).plug [.contRef k]⟩ := by
  show TSafe _ _ _ ⟨_, _, _, [.frame 1 sF [.label 1 [] (fvals ([] ++ [.cont k]) ++
    .core (.plain .drop) :: [.core (.plain (.intConst .i32 42)), .core (.plain .nop)])]]⟩
  refine tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_dropCont_seq (by inv_tac) ?_
  refine tsafe_nop (V := [.val (Val.i32 42)]) (rest := []) (by inv_tac) ?_
  rw [List.append_nil]
  refine tsafe_vals ?_
  simp only [labelPost, framePost, handlerPost, List.nil_append]
  exact fun _ => hr

/-- **`A` resumed with `B`'s continuation switches to `B`**, which returns `42`. -/
theorem a_switch {K' : Conts} (hQ₁ : Inv Q₁) (hK : K'[1]? = some (some (coK restB)))
    (hr : ∀ K'', Q₁ swStore K'' sF (.normal [.val (Val.i32 42)])) :
    TSafe P swFx (handlerPost (totJ P swFx Q₁) switchHs [] Q₁)
      ⟨swStore, K', sF, (coK restA).plug [.contRef 1]⟩ := by
  show TSafe _ _ _ ⟨_, _, _, [.frame 1 sF [.label 1 [] (fvals ([] ++ [.cont 1]) ++
    .fx (.switch (ix 0) (ix 0)) :: [])]]⟩
  refine tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_switch_seq (by inv_tac) fun V₁ vs hV => ?_
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV.symm
  simp only [labelPost, framePost, handlerPost]
  refine ⟨fun C ta ti hk ht _ _ => ?_,
    fun hu => (sw_handles rfl ⟨.onSwitch 0, by simp [switchHs], rfl⟩ hu rfl).elim⟩
  obtain rfl : C = coK restB := by simpa [hK] using hk.symm
  have ht' : swStore.tag? sF (ix 0) = some (ta, ti) := ht
  rw [sw_tag] at ht'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ht')
  simp only [totJ]
  exact tsafe_handler' (us := []) hQ₁ (b_ret hQ₁ _ (hr _))

/-- The switch handler resolves. -/
theorem switch_resolve : [OnClause.onSwitch (ix 0)].mapM (resolve swStore sF) = some switchHs := rfl

theorem two_split {a b : FVal} {V₁ vs : List FVal} (hV : [a, b] = V₁ ++ vs)
    (hm : vs.length = 2) : V₁ = [] ∧ vs = [a, b] := by
  obtain ⟨a', b', rfl⟩ : ∃ a' b', vs = [a', b'] := by
    match vs, hm with
    | [a', b'], _ => exact ⟨a', b', rfl⟩
  have h2 : V₁ ++ [a', b'] = [] ++ [a, b] := hV.symm
  obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
  exact ⟨h3, h4⟩

/-- **The resume of `A` with `B`'s continuation**, under `(on $e switch)`: `B` returns `42`
for the full payload; the empty payload is stuck. -/
theorem switch_resume {Q : PostFX Nat} (hQ : Inv Q) {K : Conts}
    (hK3 : K[3]? = some (some (coK restA))) (hK1 : (K.set 3 none)[1]? = some (some (coK restB)))
    (hend : ∀ K', TSafe P swFx Q ⟨swStore, K', sF, fvals [.val (Val.i32 42)]⟩) :
    TSafe P swFx Q ⟨swStore, K, sF, fvals [.cont 1, .cont 3] ++
      [InstrFX.toAdmin (.block btR [.fx (.resume (ix 0) [.onSwitch (ix 0)])])]⟩ := by
  refine tsafe_block_seq hQ (t₁ := [ti32, ti32]) (t₂ := [ti32]) rfl fun V₁ vs hV hm => ?_
  obtain ⟨rfl, rfl⟩ := two_split hV hm
  show TSafe _ _ _ ⟨_, _, _, fvals ([.cont 1] ++ [.cont 3]) ++
    .fx (.resume (ix 0) [.onSwitch (ix 0)]) :: []⟩
  refine tsafe_resume_seq (C := coK restA) (by inv_tac) hK3 switch_resolve fun V₁ vs hV => ?_
  rcases cont_split hV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine a_switch (by inv_tac) hK1 fun K'' => ?_
    simp only [seqPost, totJ]
    vals_tac
    simpa using hend _
  · show TSafe _ _ _ ⟨_, _, _, [.frame 1 sF [.label 1 [] (fvals [] ++ .fx (.switch (ix 0) (ix 0)) :: [])]]⟩
    exact tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac)
      (tsafe_switch_nil_seq (by inv_tac)))

/-- **Switching between two coroutines is totally safe** and returns `42`. -/
theorem switch_tsafe : TSafe P swFx (qRet 42) switchProg := by
  have hQ := inv_qRet 42
  show TSafe _ _ _ ⟨swStore, [], sF, fvals [] ++ .core (.plain (.call (ix 2))) :: []⟩
  refine tsafe_call hQ rfl rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  refine tsafe_label' (us := []) (by inv_tac) ?_
  refine start_spec (V := []) (by inv_tac) 0 restB rfl rfl rfl rfl ?_
  refine start_spec (by inv_tac) 1 restA rfl rfl rfl rfl ?_
  refine switch_resume (by inv_tac) rfl rfl fun K' => ?_
  vals_tac
  intro _
  vals_tac
  rfl

end Silmaril.Proofs.Wasm.FX.Examples.EveryRun
