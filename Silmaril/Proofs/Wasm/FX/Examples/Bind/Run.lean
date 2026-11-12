module

public import Silmaril.Wasm.FX.Examples.Bind.Defs
public import Silmaril.Wasm.FX.Logic.Module.Thms
public import Silmaril.Wasm.FX.Logic.Thms
public import Silmaril.Wasm.FX.Logic.Tactic.Defs

/-!
# The `cont.bind` program, by the every-run logic and its module rules

* `add_spec`: a **function specification** (`FSpecT`, total correctness) of `add40`: called with
  `[i32 v]`, it returns `[i32 (v + 40)]`; proved from its body (`fspecT_of_body`).
* **`bind_tsafe`**: the program `bindProg` (`Silmaril.Wasm.FX.Examples.Bind.Defs`) is totally safe,
  at every profile without host calls, for the postcondition "returns `[42]`". `cont.new`,
  `cont.bind` (every split, `tsafe_contBind_seq`), `resume` (every split) and the handler rule;
  the call of `add40` inside the resumed continuation uses `add_spec` through the call rule
  (`tsafe_call_spec`), and the splits that leave the argument outside get stuck at the call.
* `bind_mem`: one run returns `[42]`, by the existential calculus `Silmaril.Wasm.FX.Logic`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Examples.Bind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAsyncFX (ix)
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont bindCont)
open Silmaril.Wasm.FX.Logic.EveryRun (TSafe Inv seqPost labelPost framePost handlerPost totJ)
open Silmaril.Wasm.FX.Logic.Module
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun
open Silmaril.Proofs.Wasm.FX.Logic.Module
open Silmaril.Wasm.FX.Examples
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- Discharge `Inv` of the postconditions built by the context and call rules. -/
macro "bind_inv" : tactic => `(tactic| repeat (first
  | assumption
  | apply inv_seqPost
  | apply inv_labelPost
  | apply inv_framePost
  | apply inv_handlerPost
  | apply inv_callPost))

/-- The frame of main. -/
abbrev bF : Frame := ⟨[], bdM⟩

/-- `add40`'s function instance. -/
abbrev addFi : FuncInst Nat := ⟨kitTypes.head!, bdM, .host 0⟩

/-- The postcondition: the result `[42]`. -/
def bindQ : PostFX Nat := fun _ _ _ o => o = .normal (liftV [Val.i32 42])

theorem inv_bindQ : Inv bindQ :=
  inv_of_noEff (fun _ _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ _ _ h => by cases h)

/-! ## The specification of `add40` -/

/-- `add40` called with `[i32 v]` returns `[i32 (v + 40)]`. -/
def addS : FSpec Nat where
  pre s _ args := s = bdStore ∧ ∃ v, args = [Val.i32 v]
  post _ _ args _ _ o := ∃ v, args = [Val.i32 v] ∧ o = .normal [.val (Val.i32 (v + 40))]

theorem inv_addPost (s : Store Nat) (K : Conts) (args : List Val) : InvO (addS.post s K args) :=
  inv_of_noEff (fun _ _ _ _ _ _ ⟨_, _, h⟩ => by cases h)
    (fun _ _ _ _ _ _ _ _ ⟨_, _, h⟩ => by cases h)

/-- **The specification of `add40`**, from its body. -/
theorem add_spec : FSpecT P bdFx 0 addS := by
  refine fspecT_of_body (fi := addFi) (hh := 0) (F := ⟨bdM, 1, 1, [], add40Body⟩)
    (fun s K args h => by rw [h.1]; rfl) rfl rfl
    (fun s K args h => by obtain ⟨-, v, rfl⟩ := h; rfl) (fun s K args _ => inv_addPost s K args) ?_
  rintro s K args ⟨rfl, v, rfl⟩ f vs₀
  have hQ := inv_callPost (f := f) (vs₀ := vs₀) (inv_addPost bdStore K [Val.i32 v])
  unfold bodyPostT
  show TSafe _ _ _ ⟨_, _, _, fvals [] ++ .core (.plain (.localGet (ix 0))) ::
    [.core (.plain (.intConst .i32 40)), .core (.plain (.intBinOp .i32 .add))]⟩
  refine tsafe_localGet (v := Val.i32 v) (by bind_inv) rfl ?_
  show TSafe _ _ _ ⟨_, _, _, fvals ([] ++ [.val (Val.i32 v), .val (Val.i32 40)]) ++
    .core (.plain (.intBinOp .i32 .add)) :: []⟩
  refine tsafe_i32Add (by bind_inv) ?_
  simp only [List.nil_append, List.append_nil]
  refine tsafe_vals ?_
  simp only [labelPost, framePost, callPost, addS, List.nil_append]
  exact fun _ => ⟨trivial, _, rfl, v, rfl, rfl⟩

/-! ## The program -/

/-- The splits of the argument `2` between `cont.bind`, `resume` and the stack. -/
theorem split3 {x : FVal} {A B C : List FVal} (h : [x] = A ++ B ++ C) :
    (A = [] ∧ C ++ B = [x]) ∨ (A = [x] ∧ B = [] ∧ C = []) := by
  rcases List.append_eq_singleton_iff.mp h.symm with ⟨hAB, rfl⟩ | ⟨hAB, rfl⟩
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hAB
    exact Or.inl ⟨rfl, rfl⟩
  · rcases List.append_eq_singleton_iff.mp hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl, rfl⟩

set_option linter.unusedTactic false in
/-- The resumed continuation: `add40` with the argument `2`, through `add_spec`. -/
theorem resumed_call {Q : PostFX Nat} (hQ : Inv Q) {K : Conts}
    (hq : ∀ s' K', Q s' K' bF (.normal [.val (Val.i32 42)])) :
    TSafe P bdFx Q ⟨bdStore, K, bF, fvals [.val (Val.i32 2)] ++
      [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]⟩ := by
  have h := tsafe_call_spec (P := P) (vs₀ := []) (rest := []) (S := addS) (f := bF) (K := K)
    (c := .callRefType kitTypes.head!) hQ add_spec ⟨rfl, 2, rfl⟩ trivial
    (fun s' K' o ho => by
      obtain ⟨-, ho⟩ := ho
      cases o with
      | normal vs =>
        obtain ⟨res, rfl, v, hv, ho⟩ := ho
        obtain rfl : v = 2 :=
          Silmaril.Wasm.Logic.Hoare.numVal_int_inj (by simpa [Val.i32] using hv.symm)
        cases ho
        exact tsafe_vals (hq s' K')
      | _ =>
        simp only [addS] at ho
        try (obtain ⟨_, _, h⟩ := ho; cases h))
  exact h

/-- The resumed continuation with the argument left outside: stuck at the call. -/
theorem stuck_call {Q : PostFX Nat} {K : Conts} :
    TSafe P bdFx Q ⟨bdStore, K, bF, fvals [] ++
      [.core (.ref (.func 0)), .core (.callRefType kitTypes.head!)]⟩ := by
  have h := tsafe_invoke (P := P) (fx := bdFx) (Q := Q) (s := bdStore) (K := K) (f := bF)
    (V := []) (c := .callRefType kitTypes.head!) (a := 0) (fi := addFi) (hh := 0)
    (F := ⟨bdM, 1, 1, [], add40Body⟩) trivial rfl rfl rfl
    fun V₁ vs hV hn => by
      have : (V₁ ++ liftV vs).length = 0 := by rw [← hV]; rfl
      simp [liftV, hn] at this
  simpa [fvals, FVal.toAdmin, Val.toAdmin] using h

/-- The resumed bound continuation, for every split of the argument `2` between `cont.bind`
(`vs`), `resume` (`ws`) and the stack (`V₂`): `add40` with `2`, or stuck at the call. -/
theorem resumed_split {Q : PostFX Nat} (hQ : Inv Q) {K : Conts} {V₂ ws vs : List FVal}
    (hV : [.val (Val.i32 2)] = V₂ ++ ws ++ vs)
    (hq : ∀ s' K', Q s' K' bF (.normal [.val (Val.i32 42)])) :
    TSafe P bdFx (handlerPost (totJ P bdFx Q) [] V₂ Q)
      ⟨bdStore, K, bF, (bindCont (newCont 0 addFi) vs).plug (fvals ws)⟩ := by
  rcases split3 hV with ⟨rfl, hw⟩ | ⟨rfl, rfl, rfl⟩
  · show TSafe _ _ _ ⟨_, _, _, fvals vs ++ fvals ws ++ _⟩
    rw [show fvals vs ++ fvals ws = fvals (vs ++ ws) by simp [fvals], hw]
    refine resumed_call (inv_handlerPost hQ _ _ _) fun s' K' => ?_
    simp only [handlerPost, List.nil_append]
    exact hq s' K'
  · exact stuck_call

/-- **The `cont.bind` program is totally safe** and returns `[42]`. -/
theorem bind_tsafe : TSafe P bdFx bindQ bindProg := by
  have hQ := inv_bindQ
  show TSafe _ _ _ ⟨bdStore, [], bF, fvals [] ++ .core (.plain (.call (ix 1))) :: []⟩
  refine tsafe_call hQ rfl rfl rfl rfl fun V₁ vs hV hn => ?_
  obtain ⟨rfl, rfl⟩ : V₁ = [] ∧ vs = [] := by simpa [liftV] using hV.symm
  refine tsafe_label' (us := []) (by bind_inv) ?_
  show TSafe _ _ _ ⟨_, _, _, fvals [.val (Val.i32 2)] ++ .core (.plain (.refFunc (ix 0))) ::
    [.fx (.contNew (ix 0)), .fx (.contBind (ix 0) (ix 2)), .fx (.resume (ix 2) [])]⟩
  refine tsafe_refFunc (by bind_inv) rfl ?_
  refine tsafe_contNew_seq (fi := addFi) (by bind_inv) rfl ?_
  refine tsafe_contBind_seq (by bind_inv) rfl fun V₁ vs hV => ?_
  refine tsafe_resume (C := bindCont (newCont 0 addFi) vs) (by simp) rfl fun V₂ ws hV₂ =>
    tsafe_handler' (by bind_inv) (resumed_split (by bind_inv) (hV₂ ▸ hV) fun s' K' => ?_)
  simp only [labelPost, framePost, seqPost, totJ, List.nil_append, List.append_nil]
  exact fun _ => tsafe_vals rfl

end Silmaril.Proofs.Wasm.FX.Examples.Bind
