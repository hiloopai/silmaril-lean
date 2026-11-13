module

public import Silmaril.Proofs.Wasm.Models.FXAsync.Run

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsync

open Silmaril.Wasm.Models.FXAsync

variable {V : Type} (P : Prog (Ins V)) (test : V → Bool)

theorem runN_one {C : Type} (step : C → Res C V) (c : C) : runN step 1 c = step c := by
  simp only [runN]; cases step c <;> rfl

/-- The target of the top frame. -/
abbrev tgt (K : List (Option (List (SFrame V)))) (code : List (Ins V)) (ops : List (SV V))
    (rest : List (SFrame V)) : TCfg V :=
  ⟨K.map (Option.map trS), .normal, ⟨comp code, ops⟩ :: rest.map trB⟩

theorem lock_push (K : List (Option (List (SFrame V)))) (v : V) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.push v :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.push v :: c, ops, w⟩ :: rest⟩).map trC := rfl

theorem lock_prim (K : List (Option (List (SFrame V)))) (n : Nat) (op : List V → List V)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.prim n op :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.prim n op :: c, ops, w⟩ :: rest⟩).map trC := by
  simp only [tstep, sstep, trC, trS, comp, texec, sexec]
  rcases popN n ops with _ | ⟨a, o⟩
  · rfl
  · dsimp only; cases allVals a <;> rfl

theorem lock_drop (K : List (Option (List (SFrame V)))) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.drop :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.drop :: c, ops, w⟩ :: rest⟩).map trC := by
  cases ops <;> rfl


theorem lock_call_gen (K : List (Option (List (SFrame V)))) (f : Nat) (fr : SFrame V)
    (ops : List (SV V)) (c : List (Ins V)) (rest : List (SFrame V)) :
    tcall (compP P) (K.map (Option.map trS)) f ops (.chk :: comp c) (rest.map trB) =
      (scall P K f fr ops c rest).map trC := by
  simp only [tcall, scall, compP]
  rcases P f with _ | ⟨np, body⟩
  · rfl
  · simp only [Option.map_some]; rcases popN np ops with _ | ⟨a, o⟩ <;> rfl

theorem lock_call (K : List (Option (List (SFrame V)))) (f : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.call f :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.call f :: c, ops, w⟩ :: rest⟩).map trC :=
  lock_call_gen P K f ⟨.call f :: c, ops, w⟩ ops c rest

theorem lock_cond (K : List (Option (List (SFrame V)))) (f g : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.cond f g :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.cond f g :: c, ops, w⟩ :: rest⟩).map trC := by
  rcases ops with _ | ⟨_ | _, o⟩
  · rfl
  · exact lock_call_gen P K _ ⟨[], [], none⟩ o c rest
  · rfl

theorem lock_contNew (K : List (Option (List (SFrame V)))) (f : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    tstep (compP P) test (trC ⟨K, ⟨.contNew f :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.contNew f :: c, ops, w⟩ :: rest⟩).map trC := by
  simp only [tstep, sstep, trC, trS, comp, texec, sexec, compP]
  rcases P f with _ | ⟨np, body⟩
  · rfl
  · simp only [Option.map_some, Res.map, trC, trS, List.map_append, List.map_cons,
      List.map_nil, List.length_map]

/-! ## Rewinding -/

theorem pushTop_append {F : Type} (u : F → F) {L : List F} (hL : L ≠ []) (M : List F) :
    pushTop u (L ++ M) = pushTop u L ++ M := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs => rfl

/-- **Rewinding** re-enters the pending frames, one per step. -/
theorem rewind_run (P' : Prog (TIns V)) (h : List (Option (List (TFrame V))))
    (args : List (SV V)) (R : List (TFrame V)) (hR : R ≠ []) (S : List (TFrame V)) :
    runN (tstep P' test) R.length ⟨h, .rewind R args, S⟩ =
      .next ⟨h, .normal, pushTop (fun x => ⟨x.code, args ++ x.ops⟩) R.reverse ++ S⟩ := by
  induction R generalizing S with
  | nil => exact absurd rfl hR
  | cons b R ih =>
    cases R with
    | nil => rfl
    | cons b' bs =>
      have hstep : runN (tstep P' test) (b :: b' :: bs).length ⟨h, .rewind (b :: b' :: bs) args, S⟩
          = runN (tstep P' test) (b' :: bs).length ⟨h, .rewind (b' :: bs) args, b :: S⟩ := rfl
      have hrev : (b :: b' :: bs).reverse = (b' :: bs).reverse ++ [b] := List.reverse_cons
      have hne : (b' :: bs).reverse ≠ [] := by simp
      rw [hstep, ih (List.cons_ne_nil _ _) (b :: S), hrev, pushTop_append _ hne, List.append_assoc]
      rfl

/-! ## Unwinding -/

theorem split_spec {t : Nat} : ∀ {L m : List (SFrame V)} {hf : Nat} {r : SFrame V}
    {rs : List (SFrame V)}, split t L = some (m, hf, r, rs) →
    L = m ++ r :: rs ∧ (∀ b ∈ m, b.wait.bind (lookup t) = none) ∧
      r.wait.bind (lookup t) = some hf
  | [], _, _, _, _, h => by cases h
  | b :: L, m, hf, r, rs, h => by
    unfold split at h
    cases hb : b.wait.bind (lookup t) with
    | some h' =>
      rw [hb] at h; cases h
      exact ⟨rfl, by simp, hb⟩
    | none =>
      rw [hb] at h
      obtain ⟨⟨m', hf', r', rs'⟩, hsp, heq⟩ := Option.map_eq_some_iff.mp h
      cases heq
      obtain ⟨hL, hm, hr⟩ := split_spec hsp
      refine ⟨by rw [hL]; rfl, ?_, hr⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hm x hx

theorem split_none {t : Nat} : ∀ {L : List (SFrame V)}, split t L = none →
    ∀ b ∈ L, b.wait.bind (lookup t) = none
  | [], _ => by simp
  | b :: L, h => by
    unfold split at h
    cases hb : b.wait.bind (lookup t) with
    | some h' => rw [hb] at h; cases h
    | none =>
      rw [hb] at h
      have hL : split t L = none := Option.map_eq_none_iff.mp h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact split_none hL x hx

/-- At a frame that does not handle `t`, unwinding saves the frame. -/
theorem unwind_pass (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (buf : List (TFrame V)) (b : SFrame V) (rest : List (TFrame V))
    (hb : b.wait.bind (lookup t) = none) :
    tstep P' test ⟨h, .unwind t p buf, trB b :: rest⟩ =
      .next ⟨h, .unwind t p (buf ++ [trB b]), rest⟩ := by
  rcases b with ⟨code, ops, _ | hs⟩
  · rfl
  · have hl : lookup t hs = none := hb
    simp only [tstep, tunwind, trB, mark, List.cons_append, List.nil_append, hl]

/-- Unwinding passes the frames that do not handle `t`. -/
theorem unwind_run (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) : ∀ (m : List (SFrame V)) (buf : List (TFrame V)) (rest : List (TFrame V)),
    (∀ b ∈ m, b.wait.bind (lookup t) = none) →
    runN (tstep P' test) m.length ⟨h, .unwind t p buf, m.map trB ++ rest⟩ =
      .next ⟨h, .unwind t p (buf ++ m.map trB), rest⟩
  | [], buf, rest, _ => by simp only [List.length_nil, List.map_nil, List.append_nil]; rfl
  | b :: m, buf, rest, hm => by
    have hb : b.wait.bind (lookup t) = none := hm b (List.mem_cons_self ..)
    have hm' : ∀ x ∈ m, x.wait.bind (lookup t) = none := fun x hx => hm x (List.mem_cons_of_mem _ hx)
    have hstep := unwind_pass test P' h t p buf b (m.map trB ++ rest) hb
    rw [List.length_cons, List.map_cons, List.cons_append]
    simp only [runN]
    rw [hstep]
    show runN (tstep P' test) m.length ⟨h, .unwind t p (buf ++ [trB b]), m.map trB ++ rest⟩ = _
    rw [unwind_run P' h t p m (buf ++ [trB b]) rest hm', List.append_assoc]
    rfl

/-- Without a handler for `t`, unwinding reaches the bottom and traps. -/
theorem unwind_trap (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (L : List (SFrame V)) (buf : List (TFrame V))
    (hL : ∀ b ∈ L, b.wait.bind (lookup t) = none) :
    runN (tstep P' test) (L.length + 1) ⟨h, .unwind t p buf, L.map trB⟩ = .stop .trap := by
  have h1 := unwind_run test P' h t p L buf [] hL
  rw [List.append_nil] at h1
  rw [runN_add, h1]
  rfl


/-! ## The simulation, instruction by instruction -/

/-- A matched step in one target step. -/
theorem of_lock {x : SCfg V}
    (h : tstep (compP P) test (trC x) = (sstep P test x).map trC) :
    ∃ n, 0 < n ∧ runN (tstep (compP P) test) n (trC x) = (sstep P test x).map trC :=
  ⟨1, Nat.one_pos, by rw [runN_one]; exact h⟩

/-- The heap of a source continuation store. -/
abbrev trK (K : List (Option (List (SFrame V)))) : List (Option (List (TFrame V))) :=
  K.map (Option.map trS)

/-- The successful `resume`: one step to start rewinding, then one per frame. -/
theorem sim_resume_ok (K : List (Option (List (SFrame V)))) (n k : Nat) (hs : List Clause)
    (c : List (Ins V)) (o args o' : List (SV V)) (w : Option (List Clause))
    (rest : List (SFrame V)) (top : SFrame V) (seg : List (SFrame V))
    (hp : popN n o = some (args, o')) (hk : K[k]? = some (some (top :: seg))) :
    ∃ n', 0 < n' ∧ runN (tstep (compP P) test) n'
        (trC ⟨K, ⟨.resume n hs :: c, .cont k :: o, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.resume n hs :: c, .cont k :: o, w⟩ :: rest⟩).map trC := by
  have hK : (trK K)[k]? = some (some (trS (top :: seg))) := by
    rw [List.getElem?_map, hk]; rfl
  let R := (trS (top :: seg)).reverse
  have hR : R ≠ [] := by simp [R, trS]
  have h1 : tstep (compP P) test (trC ⟨K, ⟨.resume n hs :: c, .cont k :: o, w⟩ :: rest⟩) =
      .next ⟨(trK K).set k none, .rewind R args, ⟨.rchk hs :: comp c, o'⟩ :: rest.map trB⟩ := by
    simp only [tstep, trC, trS, comp, texec, hp, hK, R]
  have h2 := rewind_run test (compP P) ((trK K).set k none) args R hR
    (⟨.rchk hs :: comp c, o'⟩ :: rest.map trB)
  have hS : sstep P test ⟨K, ⟨.resume n hs :: c, .cont k :: o, w⟩ :: rest⟩ =
      .next ⟨K.set k none, { top with ops := args ++ top.ops } :: seg ++
        ⟨c, o', some hs⟩ :: rest⟩ := by
    simp only [sstep, sexec, hp, hk]
  refine ⟨1 + R.length, by omega, ?_⟩
  rw [runN_add, runN_one, h1, hS]
  show runN (tstep (compP P) test) R.length _ = _
  rw [h2]
  simp only [R, List.reverse_reverse, trS, pushTop, Res.map, trC, List.map_set,
    Option.map_none, List.cons_append, List.map_append, List.map_cons]
  rfl

theorem sim_resume (K : List (Option (List (SFrame V)))) (n : Nat) (hs : List Clause)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    ∃ n', 0 < n' ∧ runN (tstep (compP P) test) n'
        (trC ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩).map trC := by
  rcases ops with _ | ⟨_ | k, o⟩
  · exact of_lock P test rfl
  · exact of_lock P test rfl
  rcases hp : popN n o with _ | ⟨args, o'⟩
  · exact of_lock P test (by simp only [tstep, sstep, trC, trS, comp, texec, sexec, hp]; rfl)
  have hK : (trK K)[k]? = K[k]?.map (Option.map trS) := List.getElem?_map ..
  rcases hk : K[k]? with _ | _ | _ | ⟨top, seg⟩
  · refine of_lock P test ?_
    simp only [tstep, sstep, trC, trS, comp, texec, sexec, hp, hK, hk, Option.map_none]
    rfl
  · refine of_lock P test ?_
    simp only [tstep, sstep, trC, trS, comp, texec, sexec, hp, hK, hk, Option.map_some,
      Option.map_none]
    rfl
  · refine of_lock P test ?_
    simp only [tstep, sstep, trC, trS, comp, texec, sexec, hp, hK, hk, Option.map_some]
    rfl
  · exact sim_resume_ok P test K n k hs c o args o' w rest top seg hp hk


/-- At the resumer that handles `t`, unwinding stops and calls the handler. -/
theorem unwind_handle (P' : Prog (TIns V)) (h : List (Option (List (TFrame V)))) (t : Nat)
    (p : List (SV V)) (buf : List (TFrame V)) (r : SFrame V) (rest : List (TFrame V)) {hf : Nat}
    (hr : r.wait.bind (lookup t) = some hf) :
    tstep P' test ⟨h, .unwind t p buf, trB r :: rest⟩ =
      match P' hf with
      | none => .stop .trap
      | some (_, body) =>
        .next ⟨h ++ [some buf], .normal, ⟨body, .cont h.length :: p⟩ :: ⟨.chk :: comp r.code, r.ops⟩ ::
          rest⟩ := by
  rcases r with ⟨code, ops, _ | hs⟩
  · cases hr
  · have hl : lookup t hs = some hf := hr
    simp only [tstep, tunwind, trB, mark, List.cons_append, List.nil_append, hl]
    rcases P' hf with _ | ⟨_, _⟩ <;> rfl

/-- The first step of a `suspend`: set the payload aside and start unwinding. -/
theorem suspend_first (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (hp : popN n ops = some (p, o)) :
    tstep (compP P) test (trC ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) =
      .next ⟨trK K, .unwind t p [⟨comp c, o⟩], rest.map trB⟩ := by
  simp only [tstep, trC, trS, comp, texec, hp]

theorem sim_suspend_ok (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o : List (SV V)) (w : Option (List Clause)) (m : List (SFrame V)) (hf : Nat)
    (r : SFrame V) (rs : List (SFrame V)) (hp : popN n ops = some (p, o))
    (hsp : split t (m ++ r :: rs) = some (m, hf, r, rs))
    (hm : ∀ b ∈ m, b.wait.bind (lookup t) = none) (hr : r.wait.bind (lookup t) = some hf) :
    ∃ n', 0 < n' ∧ runN (tstep (compP P) test) n'
        (trC ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩) =
      (sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩).map trC := by
  have h1 := suspend_first P test K t n c ops p o w (m ++ r :: rs) hp
  have h2 := unwind_run test (compP P) (trK K) t p m [⟨comp c, o⟩] (trB r :: rs.map trB) hm
  have h3 := unwind_handle test (compP P) (trK K) t p ([⟨comp c, o⟩] ++ m.map trB) r
    (rs.map trB) hr
  have hmap : (m ++ r :: rs).map trB = m.map trB ++ trB r :: rs.map trB := by simp
  refine ⟨1 + (m.length + 1), by omega, ?_⟩
  rw [runN_add, runN_one, h1, hmap]
  show runN _ (m.length + 1) _ = _
  rw [runN_add, h2]
  show runN _ 1 _ = _
  rw [runN_one, h3]
  simp only [sstep, sexec, hp, hsp, compP]
  rcases P hf with _ | ⟨np, body⟩
  · rfl
  · simp only [Option.map_some, Res.map, trC, trS, List.map_append, List.map_cons,
      List.map_nil, Option.map_some, List.length_map, List.singleton_append]
    rfl

theorem sim_suspend (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V)) :
    ∃ n', 0 < n' ∧ runN (tstep (compP P) test) n'
        (trC ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩).map trC := by
  rcases hp : popN n ops with _ | ⟨p, o⟩
  · refine of_lock P test ?_
    simp only [tstep, sstep, trC, trS, comp, texec, sexec, hp]
    rfl
  rcases hsp : split t rest with _ | ⟨m, hf, r, rs⟩
  · have h1 := suspend_first P test K t n c ops p o w rest hp
    have h2 := unwind_trap test (compP P) (trK K) t p rest [⟨comp c, o⟩] (split_none hsp)
    have hS : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩ = .stop .trap := by
      simp only [sstep, sexec, hp, hsp]
    refine ⟨1 + (rest.length + 1), by omega, ?_⟩
    rw [runN_add, runN_one, h1, hS]
    exact h2
  · obtain ⟨hL, hm, hr⟩ := split_spec hsp
    rw [hL] at hsp ⊢
    exact sim_suspend_ok P test K t n c ops p o w m hf r rs hp hsp hm hr

/-- A frame whose code is exhausted returns to the frame below, which then passes its check. -/
theorem sim_return (K : List (Option (List (SFrame V)))) (ops : List (SV V))
    (w : Option (List Clause)) (rest : List (SFrame V)) :
    ∃ n', 0 < n' ∧ runN (tstep (compP P) test) n' (trC ⟨K, ⟨[], ops, w⟩ :: rest⟩) =
      (sstep P test ⟨K, ⟨[], ops, w⟩ :: rest⟩).map trC := by
  rcases rest with _ | ⟨⟨code, bops, _ | hs⟩, rest⟩
  · exact of_lock P test rfl
  · exact ⟨2, by omega, rfl⟩
  · exact ⟨2, by omega, rfl⟩

/-- **Every source step is matched by a positive number of target steps.** -/
theorem simStep : SimStep (sstep P test) (tstep (compP P) test) trC := by
  rintro ⟨K, _ | ⟨⟨code, ops, w⟩, rest⟩⟩
  · exact of_lock P test rfl
  rcases code with _ | ⟨i, c⟩
  · exact sim_return P test K ops w rest
  cases i with
  | push v => exact of_lock P test (lock_push P test K v c ops w rest)
  | prim n op => exact of_lock P test (lock_prim P test K n op c ops w rest)
  | drop => exact of_lock P test (lock_drop P test K c ops w rest)
  | call f => exact of_lock P test (lock_call P test K f c ops w rest)
  | cond f g => exact of_lock P test (lock_cond P test K f g c ops w rest)
  | contNew f => exact of_lock P test (lock_contNew P test K f c ops w rest)
  | resume n hs => exact sim_resume P test K n hs c ops w rest
  | suspend t n => exact sim_suspend P test K t n c ops w rest

/-- **The lowering preserves behaviours**, from every source configuration. -/
theorem beh_eq (x : SCfg V) : beh (sstep P test) x = beh (tstep (compP P) test) (trC x) :=
  beh_eq_of_sim (simStep P test) x

end Silmaril.Proofs.Wasm.Models.FXAsync
