module

public import Silmaril.Wasm.FX.Logic.EveryRun.Thms
public import Silmaril.Wasm.FX.Examples.Thms

/-!
# The generator examples, re-proved with the every-run logic

The generator programs of `Silmaril.Wasm.FX.Examples.Defs` (`genWY`: sum of a generator, `takeWY`:
take two values, then drop the continuation) are proved **totally safe** in the every-run logic
`Silmaril.Wasm.FX.Logic.EveryRun`, for **every profile**, without host calls, with the postcondition
"the program returns `[6]`" (resp. `[3]`). With `gen_mem`/`take_mem` (one run returns the result)
the adequacy theorem gives the exact behaviour sets.

The proof follows the program's structure, with two specifications:

* the **generator stages** (`gen_yield`, `gen_ret`): under the yield handler `yieldHs`, the
  generator's frame either suspends with its value and a new continuation `genK rest` (the
  shorter payload split ends in a branch that the handler's label cannot take), or returns `0`;
* the **encoded resume** `resumeFX Z` (`resumeFX_yield`, `resumeFX_ret`): a body that yields
  continues with the handler code `Z` on the payload and the new continuation; a body that
  returns `r` continues after the block with `r` on the stack.

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

variable {P : Profile} {nf : Nat} {Y : Nat → List InstrFX}

/-- The frame of every kit function (no locals). -/
abbrev kF (nf : Nat) : Frame := ⟨[], kitM nf⟩

/-- The resolved yield handler: tag `0` to label `0`. -/
def yieldHs : List HClause := [.onLabel 0 (ix 0)]

/-- The continuation captured by a generator suspending before the code `rest`. -/
def genK (nf : Nat) (rest : List AdminFX) : ContFX :=
  ⟨fun c => [.frame 1 (kF nf) [.label 1 [] (c ++ rest)]]⟩

/-- Discharge `Inv` of the postconditions built by the context rules. -/
macro "inv_tac" : tactic => `(tactic| repeat (first
  | assumption
  | apply inv_seqPost
  | apply inv_labelPost
  | apply inv_framePost
  | apply inv_handlerPost))

theorem kit_tag : (kitStore nf).tag? (kF nf) (ix 0) = some (0, ⟨kitTypes.head!⟩) := rfl

theorem yield_resolve :
    [OnClause.onLabel (ix 0) (ix 0)].mapM (resolve (kitStore nf) (kF nf)) = some yieldHs := rfl

theorem yield_find {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : (kitStore nf).tag? (kF nf) (ix 0) = some (ta, ti))
    (hc : yieldHs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) : ta = 0 ∧ l.toNat = 0 := by
  rw [kit_tag] at ht
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ht)
  simp [yieldHs] at hc
  exact ⟨rfl, by rw [← hc.2]; rfl⟩

theorem yield_handles {E : CtxV} {x : TagIdx} (hx : x = ix 0)
    (hu : Unhandled (kitStore nf) (kF nf) (.handler yieldHs E) x) (hf : E.frameAt (kF nf) = kF nf) :
    False := by
  subst hx
  exact hu 0 _ (by rw [CtxV.frameAt, hf]; rfl) (Or.inl ⟨.onLabel 0 (ix 0), by simp [yieldHs], rfl⟩)

theorem payload_split {v : Val} {V₁ vs : List FVal} (h : [FVal.val v] = V₁ ++ vs) :
    (V₁ = [] ∧ vs = [.val v]) ∨ (V₁ = [.val v] ∧ vs = []) := by
  rcases V₁ with _ | ⟨w, _ | ⟨w', V₁⟩⟩
  · exact Or.inl ⟨rfl, h.symm⟩
  · simp only [List.singleton_append, List.cons.injEq] at h
    exact Or.inr ⟨by rw [h.1], h.2.symm⟩
  · simp at h

/-! ## The generator stages -/

variable {Q₁ : PostFX Nat} {K : Conts}

/-- **A generator stage that yields `v`.** -/
theorem gen_yield (hQ₁ : Inv Q₁) (v : BitVec 32) (rest : List AdminFX)
    (hy : Q₁ (kitStore nf) (K ++ [some (genK nf rest)]) (kF nf) (.br 0 [.val (Val.i32 v), .cont K.length]))
    (hb : ∀ C, Q₁ (kitStore nf) (K ++ [some C]) (kF nf) (.br 0 [.cont K.length])) :
    TSafe P (kitFx nf Y) (handlerPost (totJ P (kitFx nf Y) Q₁) yieldHs [] Q₁)
      ⟨kitStore nf, K, kF nf, [.frame 1 (kF nf) [.label 1 []
        (.core (.plain (.intConst .i32 v)) :: .core (.plain .nop) :: .fx (.suspend (ix 0)) :: rest)]]⟩ := by
  refine tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_nop (V := [.val (Val.i32 v)]) (by inv_tac) (tsafe_suspend_seq (by inv_tac) ?_)
  intro V₁ vs hV
  simp only [labelPost, framePost, handlerPost]
  refine ⟨fun ta ti l ht _ hc => ?_, fun hu => (yield_handles rfl hu rfl).elim⟩
  obtain ⟨rfl, hl⟩ := yield_find ht hc
  rw [hl]
  rcases payload_split hV with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hK : (⟨(CtxV.seq [] (.frame 1 (kF nf) (.seq [] (.label 1 [] (.seq [] .hole rest)) [])) []).plug⟩ : ContFX) =
        genK nf rest := by
      simp only [genK, ContFX.mk.injEq]; funext c; simp [CtxV.plug]
    simpa [hK] using hy
  · exact hb _

/-- **The last generator stage**: it returns `0`. -/
theorem gen_ret (hQ₁ : Inv Q₁) (hr : Q₁ (kitStore nf) K (kF nf) (.normal [.val (Val.i32 0)])) :
    TSafe P (kitFx nf Y) (handlerPost (totJ P (kitFx nf Y) Q₁) yieldHs [] Q₁)
      ⟨kitStore nf, K, kF nf, [.frame 1 (kF nf) [.label 1 []
        [.core (.plain (.intConst .i32 0)), .core (.plain .nop)]]]⟩ := by
  refine tsafe_frame' (us := []) (by inv_tac) (tsafe_label' (us := []) (by inv_tac) ?_)
  refine tsafe_nop (V := [.val (Val.i32 0)]) (rest := []) (by inv_tac) ?_
  rw [List.append_nil]
  refine tsafe_vals ?_
  simp only [labelPost, framePost, handlerPost, List.nil_append]
  exact fun _ => hr

/-! ## The encoded resume `resumeFX Z` -/

section Resume

variable {Q : PostFX Nat} {K : Conts} {k : Nat} {C : ContFX} {us : List FVal}
  {Z : List InstrFX} {rest : List AdminFX}

theorem split_cont {us V₁ vs : List FVal} {k : Nat} (hV : us ++ [.cont k] = V₁ ++ vs)
    (hm : vs.length = 1) : V₁ = us ∧ vs = [.cont k] := by
  obtain ⟨w, rfl⟩ : ∃ w, vs = [w] := List.length_eq_one_iff.mp hm
  obtain ⟨h1, h2⟩ := List.append_inj' hV rfl
  exact ⟨h1.symm, h2.symm⟩

theorem split_two {a b : FVal} {vs₁ vs₂ : List FVal} (h : [a, b] = vs₁ ++ vs₂)
    (hl : vs₂.length = 2) : vs₂ = [a, b] := by
  have hl' := congrArg List.length h
  have h1 : vs₁ = [] := List.length_eq_zero_iff.mp (by simp at hl'; omega)
  simpa [h1] using h.symm

theorem split_one {a : FVal} {vs₁ vs₂ : List FVal} (h : [a] = vs₁ ++ vs₂)
    (hl : vs₂.length = 1) : vs₂ = [a] := by
  have hl' := congrArg List.length h
  have h1 : vs₁ = [] := List.length_eq_zero_iff.mp (by simp at hl'; omega)
  simpa [h1] using h.symm

theorem not_split_two {a : FVal} {vs₁ vs₂ : List FVal} (h : [a] = vs₁ ++ vs₂)
    (hl : vs₂.length = 2) : False := by
  have hl' := congrArg List.length h
  simp at hl'; omega

/-- A body under the yield handler that **yields** `v` with the new continuation `C'`. -/
def Yields (P : Profile) (nf : Nat) (Y : Nat → List InstrFX) (K : Conts) (b : List AdminFX)
    (v : Val) (C' : ContFX) : Prop :=
  ∀ Q₁ : PostFX Nat, Inv Q₁ →
    Q₁ (kitStore nf) (K ++ [some C']) (kF nf) (.br 0 [.val v, .cont K.length]) →
    (∀ C'', Q₁ (kitStore nf) (K ++ [some C'']) (kF nf) (.br 0 [.cont K.length])) →
    TSafe P (kitFx nf Y) (handlerPost (totJ P (kitFx nf Y) Q₁) yieldHs [] Q₁) ⟨kitStore nf, K, kF nf, b⟩

/-- A body under the yield handler that **returns** `r`. -/
def Returns (P : Profile) (nf : Nat) (Y : Nat → List InstrFX) (K : Conts) (b : List AdminFX)
    (r : Val) : Prop :=
  ∀ Q₁ : PostFX Nat, Inv Q₁ → Q₁ (kitStore nf) K (kF nf) (.normal [.val r]) →
    TSafe P (kitFx nf Y) (handlerPost (totJ P (kitFx nf Y) Q₁) yieldHs [] Q₁) ⟨kitStore nf, K, kF nf, b⟩

/-- **`resumeFX Z` of a body that yields**: the handler code `Z` runs on the payload and the new
continuation, inside the outer block. -/
theorem resumeFX_yield (hQ : Inv Q) (hk : K[k]? = some (some C)) {v : Val} {C' : ContFX}
    (hbody : Yields P nf Y (K.set k none) (C.plug []) v C')
    (hZ : TSafe P (kitFx nf Y) (labelPost (totJ P (kitFx nf Y) (seqPost (totJ P (kitFx nf Y) Q) rest Q))
      1 [] us (seqPost (totJ P (kitFx nf Y) Q) rest Q))
      ⟨kitStore nf, K.set k none ++ [some C'], kF nf,
        fvals [.val v, .cont (K.set k none).length] ++ Z.map InstrFX.toAdmin⟩) :
    TSafe P (kitFx nf Y) Q
      ⟨kitStore nf, K, kF nf, fvals (us ++ [.cont k]) ++ InstrFX.toAdmin (resumeFX Z) :: rest⟩ := by
  refine tsafe_block_seq hQ (t₁ := [ti32]) (t₂ := [ti32]) rfl fun V₁ vs hV hm => ?_
  obtain ⟨rfl, rfl⟩ := split_cont hV hm
  refine tsafe_block_seq (V := [.cont k]) (by inv_tac) (t₁ := [ti32]) (t₂ := [ti32, ti32]) rfl
    fun V₁ vs hV hm => ?_
  obtain ⟨rfl, rfl⟩ := split_cont (us := []) hV hm
  refine tsafe_resume_seq (V := []) (by inv_tac) hk yield_resolve fun V₁ vs hV => ?_
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV.symm
  refine hbody _ (by inv_tac) ?_ fun C'' => ?_
  · simp only [seqPost, labelPost]
    intro vs₁ vs₂ h12 hl
    rw [split_two h12 hl]
    simp only [totJ, List.nil_append, List.map_nil, List.append_nil]
    refine tsafe_vals ?_
    simpa [seqPost, totJ] using hZ
  · simp only [seqPost, labelPost]
    exact fun vs₁ vs₂ h12 hl => (not_split_two h12 hl).elim

/-- **`resumeFX Z` of a body that returns `r`**: the code after the block runs on `r`. -/
theorem resumeFX_ret (hQ : Inv Q) (hk : K[k]? = some (some C)) {r : Val}
    (hbody : Returns P nf Y (K.set k none) (C.plug []) r)
    (hcont : TSafe P (kitFx nf Y) Q ⟨kitStore nf, K.set k none, kF nf, fvals (us ++ [.val r]) ++ rest⟩) :
    TSafe P (kitFx nf Y) Q
      ⟨kitStore nf, K, kF nf, fvals (us ++ [.cont k]) ++ InstrFX.toAdmin (resumeFX Z) :: rest⟩ := by
  refine tsafe_block_seq hQ (t₁ := [ti32]) (t₂ := [ti32]) rfl fun V₁ vs hV hm => ?_
  obtain ⟨rfl, rfl⟩ := split_cont hV hm
  refine tsafe_block_seq (V := [.cont k]) (by inv_tac) (t₁ := [ti32]) (t₂ := [ti32, ti32]) rfl
    fun V₁ vs hV hm => ?_
  obtain ⟨rfl, rfl⟩ := split_cont (us := []) hV hm
  refine tsafe_resume_seq (V := []) (by inv_tac) hk yield_resolve fun V₁ vs hV => ?_
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV.symm
  refine hbody _ (by inv_tac) ?_
  simp only [seqPost, totJ]
  refine tsafe_br (x := ix 1) (R := []) (V := [.val r]) ?_
  show labelPost _ 2 [] [] _ _ _ _ (.br (0 + 1) [.val r])
  simp only [labelPost, seqPost, List.nil_append]
  intro vs₁ vs₂ h12 hl
  rw [split_one h12 hl]
  simp only [totJ, List.map_nil, List.append_nil]
  refine tsafe_vals ?_
  simpa [seqPost, totJ] using hcont

end Resume

/-! ## Sum of a generator -/

/-- The generator code after its first, second and third `suspend`. -/
def gR1 : List AdminFX :=
  [.core (.plain (.intConst .i32 2)), .core (.plain .nop), .fx (.suspend (ix 0)),
    .core (.plain (.intConst .i32 3)), .core (.plain .nop), .fx (.suspend (ix 0)),
    .core (.plain (.intConst .i32 0)), .core (.plain .nop)]

def gR2 : List AdminFX :=
  [.core (.plain (.intConst .i32 3)), .core (.plain .nop), .fx (.suspend (ix 0)),
    .core (.plain (.intConst .i32 0)), .core (.plain .nop)]

def gR3 : List AdminFX := [.core (.plain (.intConst .i32 0)), .core (.plain .nop)]

/-- The postcondition: the program returns `[6]`. -/
def qRet (v : BitVec 32) : PostFX Nat := fun _ _ _ o => o = .normal [.val (Val.i32 v)]

theorem inv_qRet (v : BitVec 32) : Inv (qRet v) :=
  inv_of_noEff (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ h => by cases h)

/-- Close a value stage: the values reach the enclosing context's postcondition. -/
macro "vals_tac" : tactic => `(tactic| (
  try simp only [List.map_nil, List.append_nil, List.map_cons]
  refine tsafe_vals ?_
  try simp only [labelPost, seqPost, framePost, totJ, List.nil_append, List.append_nil,
    List.cons_append, List.length_singleton]))

theorem gen_body0 :
    Yields P 6 genWY [none] [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]
      (Val.i32 1) (genK 6 gR1) := by
  intro Q₁ hQ₁ hy hb
  show TSafe _ _ _ ⟨_, _, _, fvals ([] ++ [.val (.ref (.func 0))]) ++ [.core (.callRefType _)]⟩
  refine tsafe_invoke (by simp [Admin.IsCallRef]) rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  exact gen_yield hQ₁ 1 gR1 hy hb

/-- The main function's three resumes of the generator and its three additions. -/
theorem gen_resumes {Q : PostFX Nat} (hQ : Inv Q)
    (hend : ∀ K, TSafe P (kitFx 6 genWY) Q
      ⟨kitStore 6, K, kF 6, fvals [.val (Val.i32 (1 + (2 + (3 + 0))))]⟩) :
    TSafe P (kitFx 6 genWY) Q ⟨kitStore 6, [] ++ [some (newCont 0 ⟨kitTypes.head!, kitM 6, .host 0⟩)],
      kF 6, fvals ([] ++ [.cont ([] : Conts).length]) ++ [InstrFX.toAdmin (resumeFX genH2)]⟩ := by
  refine resumeFX_yield (us := []) (C := newCont 0 ⟨kitTypes.head!, kitM 6, .host 0⟩)
    (by inv_tac) rfl gen_body0 ?_
  refine resumeFX_yield (us := [.val (Val.i32 1)]) (C := genK 6 gR1) (by inv_tac) rfl
    (fun Q₁ hQ₁ hy hb => gen_yield hQ₁ 2 gR2 hy hb) ?_
  refine resumeFX_yield (us := [.val (Val.i32 2)]) (C := genK 6 gR2) (by inv_tac) rfl
    (fun Q₁ hQ₁ hy hb => gen_yield hQ₁ 3 gR3 hy hb) ?_
  refine resumeFX_ret (us := [.val (Val.i32 3)]) (C := genK 6 gR3) (by inv_tac) rfl
    (fun Q₁ hQ₁ hr => gen_ret hQ₁ hr) ?_
  refine tsafe_i32Add (V := []) (by inv_tac) ?_
  vals_tac
  refine tsafe_i32Add (V := []) (by inv_tac) ?_
  vals_tac
  refine tsafe_i32Add (V := []) (by inv_tac) ?_
  vals_tac
  simpa using hend _

theorem gen_tsafe : TSafe P (kitFx 6 genWY) (qRet 6) (genProg P noHost) := by
  have hQ := inv_qRet 6
  show TSafe _ _ _ ⟨kitStore 6, [], kF 6, fvals [] ++ .core (.plain (.call (ix 1))) :: []⟩
  refine tsafe_call hQ rfl rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  refine tsafe_label' (us := []) (by inv_tac) ?_
  refine tsafe_refFunc (V := []) (by inv_tac) rfl ?_
  refine tsafe_contNew_seq (V := []) (by inv_tac) rfl ?_
  refine gen_resumes (by inv_tac) fun K => ?_
  vals_tac
  intro _
  vals_tac
  rfl

/-- **Sum of a generator, by the every-run logic**: at every profile, the only `StepFX'`
behaviour returns `1 + 2 + 3 = 6`. -/
theorem gen_beh (P : Profile) :
    behavioursFX' P noHost (kitFx 6 genWY) (genProg P noHost) = {.returns [Val.i32 6]} :=
  tsafe_behaviours_eq gen_tsafe (fun _ _ _ _ h => h) (gen_mem P noHost)

/-! ## Take two from a generator, then drop it -/

theorem take_body0 :
    Yields P 4 takeWY [none] [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]
      (Val.i32 1) (genK 4 gR1) := by
  intro Q₁ hQ₁ hy hb
  show TSafe _ _ _ ⟨_, _, _, fvals ([] ++ [.val (.ref (.func 0))]) ++ [.core (.callRefType _)]⟩
  refine tsafe_invoke (by simp [Admin.IsCallRef]) rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  exact gen_yield hQ₁ 1 gR1 hy hb

theorem take_tsafe : TSafe P (kitFx 4 takeWY) (qRet 3) (takeProg P noHost) := by
  have hQ := inv_qRet 3
  show TSafe _ _ _ ⟨kitStore 4, [], kF 4, fvals [] ++ .core (.plain (.call (ix 1))) :: []⟩
  refine tsafe_call hQ rfl rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  refine tsafe_label' (us := []) (by inv_tac) ?_
  refine tsafe_refFunc (V := []) (by inv_tac) rfl ?_
  refine tsafe_contNew_seq (V := []) (by inv_tac) rfl ?_
  refine resumeFX_yield (us := []) (C := newCont 0 ⟨kitTypes.head!, kitM 4, .host 0⟩)
    (by inv_tac) rfl take_body0 ?_
  refine resumeFX_yield (us := [.val (Val.i32 1)]) (C := genK 4 gR1) (by inv_tac) rfl
    (fun Q₁ hQ₁ hy hb => gen_yield hQ₁ 2 gR2 hy hb) ?_
  refine tsafe_dropCont_seq (V := [.val (Val.i32 2)]) (by inv_tac) ?_
  vals_tac
  refine tsafe_i32Add (V := []) (by inv_tac) ?_
  vals_tac
  vals_tac
  intro _
  vals_tac
  rfl

/-- **Take two from a generator and drop it, by the every-run logic**: at every profile, the
only `StepFX'` behaviour returns `1 + 2 = 3`. -/
theorem take_beh (P : Profile) :
    behavioursFX' P noHost (kitFx 4 takeWY) (takeProg P noHost) = {.returns [Val.i32 3]} :=
  tsafe_behaviours_eq take_tsafe (fun _ _ _ _ h => h) (take_mem P noHost)

end Silmaril.Proofs.Wasm.FX.Examples.EveryRun
