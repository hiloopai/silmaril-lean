module

public import Silmaril.Proofs.Wasm.FX.Asyncify.SelBase

/-!
# Selective asyncify: `resume` and `suspend` on fully checked stacks

A frame running `resume` or `suspend` is not calm, so by the invariant of `SelBase` no frame
below it is unchecked: the target is the fully checked translation `trCO o`. On such
configurations the steps of `FXAsync`'s simulation go through for `compO o` as for `comp`: a
`resume` is one step and one rewinding step per frame (`simO_resume`), a `suspend` is one step,
one unwinding step per passed frame and one at the handler, or a trap at the bottom
(`simO_suspend`). The generic rewinding run and the `split` facts of `FXAsync` are reused.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Proofs.Wasm.Models.FXAsync (runN_add runN_one rewind_run split_spec split_none)

variable {V : Type} (o : Opt) (P : Prog (Ins V)) (test : V → Bool)

/-- A matched step in one target step. -/
theorem ofLockO {x : SCfg V}
    (h : tstep (compPO o P) test (trCO o x) = (sstep P test x).map (trCO o)) :
    ∃ n, 0 < n ∧ runN (tstep (compPO o P) test) n (trCO o x) = (sstep P test x).map (trCO o) :=
  ⟨1, Nat.one_pos, by rw [runN_one]; exact h⟩

/-! ## Rewinding -/

/-- The successful `resume`: one step to start rewinding, then one per frame. -/
theorem simO_resume_ok (K : List (Option (List (SFrame V)))) (n k : Nat) (hs : List Clause)
    (c : List (Ins V)) (ops args o' : List (SV V)) (w : Option (List Clause))
    (rest : List (SFrame V)) (top : SFrame V) (seg : List (SFrame V))
    (hp : popN n ops = some (args, o')) (hk : K[k]? = some (some (top :: seg))) :
    ∃ n', 0 < n' ∧ runN (tstep (compPO o P) test) n'
        (trCO o ⟨K, ⟨.resume n hs :: c, .cont k :: ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.resume n hs :: c, .cont k :: ops, w⟩ :: rest⟩).map (trCO o) := by
  have hK : (trKO o K)[k]? = some (some (trSO o (top :: seg))) := by
    simp only [trKO, List.getElem?_map, hk, Option.map_some]
  let R := (trSO o (top :: seg)).reverse
  have hR : R ≠ [] := by simp [R, trSO]
  have h1 : tstep (compPO o P) test (trCO o ⟨K, ⟨.resume n hs :: c, .cont k :: ops, w⟩ :: rest⟩) =
      .next ⟨(trKO o K).set k none, .rewind R args,
        ⟨.rchk hs :: compO o c, o'⟩ :: rest.map (trBO o)⟩ := by
    simp only [tstep, trCO, trSO, compO, texec, hp, hK, R]
  have h2 := rewind_run test (compPO o P) ((trKO o K).set k none) args R hR
    (⟨.rchk hs :: compO o c, o'⟩ :: rest.map (trBO o))
  have hS : sstep P test ⟨K, ⟨.resume n hs :: c, .cont k :: ops, w⟩ :: rest⟩ =
      .next ⟨K.set k none, { top with ops := args ++ top.ops } :: seg ++
        ⟨c, o', some hs⟩ :: rest⟩ := by
    simp only [sstep, sexec, hp, hk]
  refine ⟨1 + R.length, by omega, ?_⟩
  rw [runN_add, runN_one, h1, hS]
  show runN (tstep (compPO o P) test) R.length _ = _
  rw [h2]
  simp only [R, List.reverse_reverse, trSO, pushTop, Res.map, trCO, trKO, List.map_set,
    Option.map_none, List.cons_append, List.map_append, List.map_cons]
  rfl

/-- **`resume`** on a fully checked stack. -/
theorem simO_resume (K : List (Option (List (SFrame V)))) (n : Nat) (hs : List Clause)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    ∃ n', 0 < n' ∧ runN (tstep (compPO o P) test) n'
        (trCO o ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩).map (trCO o) := by
  rcases ops with _ | ⟨_ | k, ops⟩
  · exact ofLockO o P test rfl
  · exact ofLockO o P test rfl
  rcases hp : popN n ops with _ | ⟨args, o'⟩
  · exact ofLockO o P test (by simp only [tstep, sstep, trCO, trSO, compO, texec, sexec, hp]; rfl)
  have hK : (trKO o K)[k]? = K[k]?.map (Option.map (trSO o)) := List.getElem?_map ..
  rcases hk : K[k]? with _ | _ | _ | ⟨top, seg⟩
  · refine ofLockO o P test ?_
    simp only [tstep, sstep, trCO, trSO, compO, texec, sexec, hp, hK, hk, Option.map_none]
    rfl
  · refine ofLockO o P test ?_
    simp only [tstep, sstep, trCO, trSO, compO, texec, sexec, hp, hK, hk, Option.map_some,
      Option.map_none]
    rfl
  · refine ofLockO o P test ?_
    simp only [tstep, sstep, trCO, trSO, compO, texec, sexec, hp, hK, hk, Option.map_some]
    rfl
  · exact simO_resume_ok o P test K n k hs c ops args o' w rest top seg hp hk

/-! ## Unwinding -/

/-- At a frame that does not handle `t`, unwinding saves the frame. -/
theorem unwindO_pass (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (buf : List (TFrame V)) (b : SFrame V) (rest : List (TFrame V))
    (hb : b.wait.bind (lookup t) = none) :
    tstep P' test ⟨h, .unwind t p buf, trBO o b :: rest⟩ =
      .next ⟨h, .unwind t p (buf ++ [trBO o b]), rest⟩ := by
  rcases b with ⟨code, ops, _ | hs⟩
  · rfl
  · have hl : lookup t hs = none := hb
    simp only [tstep, tunwind, trBO, mark, List.cons_append, List.nil_append, hl]

/-- Unwinding passes the frames that do not handle `t`. -/
theorem unwindO_run (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) : ∀ (m : List (SFrame V)) (buf : List (TFrame V)) (rest : List (TFrame V)),
    (∀ b ∈ m, b.wait.bind (lookup t) = none) →
    runN (tstep P' test) m.length ⟨h, .unwind t p buf, m.map (trBO o) ++ rest⟩ =
      .next ⟨h, .unwind t p (buf ++ m.map (trBO o)), rest⟩
  | [], buf, rest, _ => by simp only [List.length_nil, List.map_nil, List.append_nil]; rfl
  | b :: m, buf, rest, hm => by
    have hb : b.wait.bind (lookup t) = none := hm b (List.mem_cons_self ..)
    have hm' : ∀ x ∈ m, x.wait.bind (lookup t) = none :=
      fun x hx => hm x (List.mem_cons_of_mem _ hx)
    have hstep := unwindO_pass o test P' h t p buf b (m.map (trBO o) ++ rest) hb
    rw [List.length_cons, List.map_cons, List.cons_append]
    simp only [runN]
    rw [hstep]
    show runN (tstep P' test) m.length
      ⟨h, .unwind t p (buf ++ [trBO o b]), m.map (trBO o) ++ rest⟩ = _
    rw [unwindO_run P' h t p m (buf ++ [trBO o b]) rest hm', List.append_assoc]
    rfl

/-- Without a handler for `t`, unwinding reaches the bottom and traps. -/
theorem unwindO_trap (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (L : List (SFrame V)) (buf : List (TFrame V))
    (hL : ∀ b ∈ L, b.wait.bind (lookup t) = none) :
    runN (tstep P' test) (L.length + 1) ⟨h, .unwind t p buf, L.map (trBO o)⟩ = .stop .trap := by
  have h1 := unwindO_run o test P' h t p L buf [] hL
  rw [List.append_nil] at h1
  rw [runN_add, h1]
  rfl

/-- At the resumer that handles `t`, unwinding stops and calls the handler. -/
theorem unwindO_handle (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (buf : List (TFrame V)) (r : SFrame V) (rest : List (TFrame V)) {hf : Nat}
    (hr : r.wait.bind (lookup t) = some hf) :
    tstep P' test ⟨h, .unwind t p buf, trBO o r :: rest⟩ =
      match P' hf with
      | none => .stop .trap
      | some (_, body) =>
        .next ⟨h ++ [some buf], .normal, ⟨body, .cont h.length :: p⟩ ::
          ⟨.chk :: compO o r.code, r.ops⟩ :: rest⟩ := by
  rcases r with ⟨code, ops, _ | hs⟩
  · cases hr
  · have hl : lookup t hs = some hf := hr
    simp only [tstep, tunwind, trBO, mark, List.cons_append, List.nil_append, hl]
    rcases P' hf with _ | ⟨_, _⟩ <;> rfl

/-- The first step of a `suspend`: set the payload aside and start unwinding. -/
theorem suspendO_first (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o' : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (hp : popN n ops = some (p, o')) :
    tstep (compPO o P) test (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) =
      .next ⟨trKO o K, .unwind t p [⟨compO o c, o'⟩], rest.map (trBO o)⟩ := by
  simp only [tstep, trCO, trSO, compO, texec, hp]

theorem simO_suspend_ok (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o' : List (SV V)) (w : Option (List Clause)) (m : List (SFrame V)) (hf : Nat)
    (r : SFrame V) (rs : List (SFrame V)) (hp : popN n ops = some (p, o'))
    (hsp : split t (m ++ r :: rs) = some (m, hf, r, rs))
    (hm : ∀ b ∈ m, b.wait.bind (lookup t) = none) (hr : r.wait.bind (lookup t) = some hf) :
    ∃ n', 0 < n' ∧ runN (tstep (compPO o P) test) n'
        (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩) =
      (sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩).map (trCO o) := by
  have h1 := suspendO_first o P test K t n c ops p o' w (m ++ r :: rs) hp
  have h2 := unwindO_run o test (compPO o P) (trKO o K) t p m [⟨compO o c, o'⟩]
    (trBO o r :: rs.map (trBO o)) hm
  have h3 := unwindO_handle o test (compPO o P) (trKO o K) t p
    ([⟨compO o c, o'⟩] ++ m.map (trBO o)) r (rs.map (trBO o)) hr
  have hmap : (m ++ r :: rs).map (trBO o) = m.map (trBO o) ++ trBO o r :: rs.map (trBO o) := by
    simp
  refine ⟨1 + (m.length + 1), by omega, ?_⟩
  rw [runN_add, runN_one, h1, hmap]
  show runN _ (m.length + 1) _ = _
  rw [runN_add, h2]
  show runN _ 1 _ = _
  rw [runN_one, h3]
  simp only [sstep, sexec, hp, hsp, compPO]
  rcases P hf with _ | ⟨np, body⟩
  · rfl
  · simp only [Option.map_some, Res.map, trCO, trKO, trSO, List.map_append, List.map_cons,
      List.map_nil, Option.map_some, List.length_map, List.singleton_append]
    rfl

/-- **`suspend`** on a fully checked stack. -/
theorem simO_suspend (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    ∃ n', 0 < n' ∧ runN (tstep (compPO o P) test) n'
        (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩).map (trCO o) := by
  rcases hp : popN n ops with _ | ⟨p, o'⟩
  · refine ofLockO o P test ?_
    simp only [tstep, sstep, trCO, trSO, compO, texec, sexec, hp]
    rfl
  rcases hsp : split t rest with _ | ⟨m, hf, r, rs⟩
  · have h1 := suspendO_first o P test K t n c ops p o' w rest hp
    have h2 := unwindO_trap o test (compPO o P) (trKO o K) t p rest [⟨compO o c, o'⟩]
      (split_none hsp)
    have hS : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩ = .stop .trap := by
      simp only [sstep, sexec, hp, hsp]
    refine ⟨1 + (rest.length + 1), by omega, ?_⟩
    rw [runN_add, runN_one, h1, hS]
    exact h2
  · obtain ⟨hL, hm, hr⟩ := split_spec hsp
    rw [hL] at hsp ⊢
    exact simO_suspend_ok o P test K t n c ops p o' w m hf r rs hp hsp hm hr

end Silmaril.Proofs.Wasm.FX.Asyncify
