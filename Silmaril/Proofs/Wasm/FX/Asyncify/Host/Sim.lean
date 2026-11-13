module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Host.Lift

/-!
# Asyncify with a host: the simulation

`simRel_host`: for a sound analysis, the selective relation `Rel o f args` of `SelSim`, with
equal host states, is a stuttering simulation between the host-closed kernel `hsstep` and the
host-closed asyncify machine `htstep` on `compPO o P`.

* Away from a blocking call, a kernel step is matched as in `simRel_sel`; continuing and
  returning runs carry over (`runN_h_next`, `runN_h_done`). A trap is matched by a trap of the
  closed target: every such trap happens before an unwinding reaches the root (`free_trap`).
* A **blocking call** (`blocked_sim`) is matched by `1 + |frames| + 1 + (|frames| + 1)` target
  steps: start unwinding, save every frame (none handles the tag), the host's answer at the root,
  and rewinding every saved frame, the answers pushed on the suspending one.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Proofs.Wasm.FX.Asyncify
open Silmaril.Proofs.Wasm.Models.FXAsync (runN_one rewind_run split_none split_spec)

variable {V σ : Type} (o : Opt) (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ)
  (f : Nat) (args : List (SV V))

/-- **The relation**: the selective relation, equal host states. -/
def HRel (x : SCfg V × σ) (y : TCfg V × σ) : Prop := Rel o f args x.1 y.1 ∧ x.2 = y.2

/-- A trap is matched by a trap. -/
theorem resRel_trap {C D : Type} {R : C → D → Prop} {r : Res D V}
    (h : ResRel R (.stop (.trap : Outcome V)) r) : r = .stop .trap := by
  rcases r with _ | o'
  · exact absurd h id
  · have ho : (Outcome.trap : Outcome V) = o' := h
    rw [← ho]

/-- A kernel trap matched in one step. -/
theorem trap_of_res {x : SCfg V} {y : TCfg V} (h : sstep P test x = .stop .trap)
    (hr : ResRel (Rel o f args) (sstep P test x) (tstep (compPO o P) test y)) :
    tstep (compPO o P) test y = .stop .trap :=
  resRel_trap (h ▸ hr)

/-- A one-step trap of the asyncify machine in normal mode is a trap of the closed target. -/
theorem trap_one {y : TCfg V} (hy : y.mode = .normal) (h : tstep (compPO o P) test y = .stop .trap)
    (s : σ) : ∃ m, 0 < m ∧ runN (htstep (compPO o P) test H) m (y, s) = .stop .trap := by
  refine ⟨1, Nat.one_pos, ?_⟩
  rw [runN_one, htstep_stop H h (.inr (atRoot_normal hy)) s]

/-! ## Traps away from blocking calls -/

/-- A two-way call: the matched one-step result. -/
theorem cond_res (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (g g' : Nat)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause))
    (A : List (SFrame V × Bool)) (htop : HasU A → Calm o.instr (.cond g g' :: c))
    (hok : OkR o.instr A) :
    ResRel (Rel o f args) (sstep P test ⟨K, ⟨.cond g g' :: c, ops, w⟩ :: A.map Prod.fst⟩)
      (tstep (compPO o P) test
        ⟨trKO o K, .normal, ⟨compO o (.cond g g' :: c), ops⟩ :: A.map (trF o)⟩) := by
  rcases ops with _ | ⟨v | k, o'⟩
  · exact rfl
  · have hb : (o.instr g || o.instr g') = false →
        o.instr (if test v then g else g') = false := by
      intro h
      have h' : o.instr g = false ∧ o.instr g' = false := Bool.or_eq_false_iff.mp h
      split
      · exact h'.1
      · exact h'.2
    have hc : HasU A → Calm o.instr c ∧ o.instr (if test v then g else g') = false := by
      intro hu
      have h' : o.instr g = false ∧ o.instr g' = false := calm_cond (htop hu)
      refine ⟨calm_tail (htop hu), ?_⟩
      split
      · exact h'.1
      · exact h'.2
    exact sel_call o P f args hS K _ _ ⟨[], [], none⟩ o' c A hb hc hok
  · exact rfl

/-- A `resume` that traps in the kernel traps in one target step. -/
theorem resume_trap (K : List (Option (List (SFrame V)))) (n : Nat) (hs : List Clause)
    (c : List (Ins V)) (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (h : sstep P test ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩ = .stop .trap) :
    tstep (compPO o P) test (trCO o ⟨K, ⟨.resume n hs :: c, ops, w⟩ :: rest⟩) = .stop .trap := by
  rcases ops with _ | ⟨_ | k, ops⟩
  · rfl
  · rfl
  rcases hp : popN n ops with _ | ⟨a, o'⟩
  · simp only [tstep, trCO, trSO, compO, texec, hp]
  have hK : (trKO o K)[k]? = K[k]?.map (Option.map (trSO o)) := List.getElem?_map ..
  rcases hk : K[k]? with _ | _ | _ | ⟨top, seg⟩
  · simp only [tstep, trCO, trSO, compO, texec, hp, hK, hk, Option.map_none]
  · simp only [tstep, trCO, trSO, compO, texec, hp, hK, hk, Option.map_some, Option.map_none]
  · simp only [tstep, trCO, trSO, compO, texec, hp, hK, hk, Option.map_some]
  · simp only [sstep, sexec, hp, hk, reduceCtorEq] at h

/-- A handled `suspend` whose handler is missing traps after the unwinding, before the root. -/
theorem handled_trap (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o' : List (SV V)) (w : Option (List Clause)) (m : List (SFrame V)) (hf : Nat)
    (r : SFrame V) (rs : List (SFrame V)) (hp : popN n ops = some (p, o'))
    (hm : ∀ b ∈ m, b.wait.bind (lookup t) = none) (hr : r.wait.bind (lookup t) = some hf)
    (hP : P hf = none) (s : σ) :
    runN (htstep (compPO o P) test H) (1 + (m.length + 1))
      (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩, s) = .stop .trap := by
  have h1 : tstep (compPO o P) test (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩) =
      .next ⟨trKO o K, .unwind t p [⟨compO o c, o'⟩], (m ++ r :: rs).map (trBO o)⟩ :=
    suspendO_first o P test K t n c ops p o' w (m ++ r :: rs) hp
  have hmap : (m ++ r :: rs).map (trBO o) = m.map (trBO o) ++ trBO o r :: rs.map (trBO o) := by
    simp only [List.map_append, List.map_cons]
  have h2 : runN (tstep (compPO o P) test) m.length
      ⟨trKO o K, .unwind t p [⟨compO o c, o'⟩], m.map (trBO o) ++ trBO o r :: rs.map (trBO o)⟩ =
      .next ⟨trKO o K, .unwind t p ([⟨compO o c, o'⟩] ++ m.map (trBO o)),
        trBO o r :: rs.map (trBO o)⟩ :=
    unwindO_run o test (compPO o P) (trKO o K) t p m _ _ hm
  have hPc : compPO o P hf = none := by simp only [compPO, hP, Option.map_none]
  have h3 : tstep (compPO o P) test ⟨trKO o K, .unwind t p ([⟨compO o c, o'⟩] ++ m.map (trBO o)),
      trBO o r :: rs.map (trBO o)⟩ = .stop .trap := by
    rw [unwindO_handle o test (compPO o P) (trKO o K) t p _ r _ hr, hPc]
  rw [runN_cat (runN_one_eq (htstep_next H h1 s)), hmap,
    runN_cat (runN_h_next H s _ _ _ h2), runN_one]
  exact htstep_stop H h3 (.inr atRoot_cons) s

/-- A `suspend` that traps in the kernel and is not a blocking call traps in the target. -/
theorem suspend_trap (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (hb : blockedOn (⟨.suspend t n :: c, ops, w⟩ :: rest) = none)
    (h : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩ = .stop .trap) (s : σ) :
    ∃ m, 0 < m ∧ runN (htstep (compPO o P) test H) m
      (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩, s) = .stop .trap := by
  rcases hp : popN n ops with _ | ⟨p, o'⟩
  · show ∃ m, 0 < m ∧ _
    refine trap_one o P test H rfl ?_ s
    simp only [tstep, trCO, trSO, compO, texec, hp]
  rcases hsp : split t rest with _ | ⟨m, hf, r, rs⟩
  · have hb' : blockedOn (⟨.suspend t n :: c, ops, w⟩ :: rest) = some (t, p, ⟨c, o', w⟩) := by
      simp only [blockedOn, hp, hsp]
    cases hb.symm.trans hb'
  · show ∃ m, 0 < m ∧ _
    obtain ⟨hL, hm, hr⟩ := split_spec hsp
    have hsp' : split t (m ++ r :: rs) = some (m, hf, r, rs) := hL ▸ hsp
    have hP : P hf = none := by
      cases hPf : P hf with
      | none => rfl
      | some q =>
        have hn : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩ ≠ .stop .trap := by
          simp only [sstep, sexec, hp, hsp', hPf, ne_eq, reduceCtorEq, not_false_eq_true]
        exact absurd (hL ▸ h) hn
    refine ⟨1 + (m.length + 1), by omega, ?_⟩
    rw [hL]
    exact handled_trap o P test H K t n c ops p o' w m hf r rs hp hm hr hP s

/-- A step result of the shape `TopRes` that the kernel traps on traps in the target. -/
theorem topRes_trap {A : List (SFrame V × Bool)} {c : List (Ins V)} {r : Res (SCfg V) V}
    {r' : Res (TCfg V) V} (hT : TopRes o A c r r') (h : r = .stop .trap) : r' = .stop .trap := by
  rcases hT with ⟨out, hs, ht⟩ | ⟨_, _, _, hs, _⟩
  · exact ht.trans (congrArg _ (Res.stop.inj (hs.symm.trans h)))
  · cases hs.symm.trans h

/-- The top frame of the main relation: a kernel trap is a one-step target trap, or (for a
`suspend` that is not a blocking call) a trap after unwinding. -/
theorem main_trap (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (top : SFrame V)
    (A : List (SFrame V × Bool)) (htop : HasU A → Calm o.instr top.code)
    (hok : OkR o.instr A) (hb : blockedOn (top :: A.map Prod.fst) = none)
    (h : sstep P test ⟨K, top :: A.map Prod.fst⟩ = .stop .trap) (s : σ) :
    ∃ m, 0 < m ∧ runN (htstep (compPO o P) test H) m
      (⟨trKO o K, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩, s) = .stop .trap := by
  rcases top with ⟨_ | ⟨i, c⟩, ops, w⟩
  · show ∃ m, 0 < m ∧ _
    rcases A with _ | ⟨⟨b, fl⟩, L⟩ <;> cases h
  cases i with
  | push v => cases h
  | prim n op => exact trap_one o P test H rfl (topRes_trap o (top_prim o P test K n op c ops w A) h) s
  | drop => exact trap_one o P test H rfl (topRes_trap o (top_drop o P test K c ops w A) h) s
  | contNew g =>
    exact trap_one o P test H rfl (topRes_trap o (top_contNew o P test K g c ops w A) h) s
  | call g =>
    exact trap_one o P test H rfl (trap_of_res o P test 0 []
      (y := ⟨trKO o K, .normal, ⟨compO o (.call g :: c), ops⟩ :: A.map (trF o)⟩) h
      (sel_call o P 0 [] hS K g (o.instr g) ⟨.call g :: c, ops, w⟩ ops c A id
        (fun hu => ⟨calm_tail (htop hu), calm_call (htop hu)⟩) hok)) s
  | cond g g' =>
    exact trap_one o P test H rfl
      (trap_of_res o P test 0 [] h (cond_res o P test 0 [] hS K g g' c ops w A htop hok)) s
  | resume n hs =>
    rw [full_of_not_calm o htop calm_resume]
    exact trap_one o P test H rfl (resume_trap o P test K n hs c ops w _ h) s
  | suspend t n =>
    rw [full_of_not_calm o htop calm_suspend]
    exact suspend_trap o P test H K t n c ops w _ hb h s

/-- **Away from a blocking call, a kernel trap is matched by a trap of the closed target.** -/
theorem free_trap (hS : Sound o.instr P) {x : SCfg V} {y : TCfg V} (hxy : Rel o f args x y)
    (hb : blockedOn x.stack = none) (h : sstep P test x = .stop .trap) (s : σ) :
    ∃ m, 0 < m ∧ runN (htstep (compPO o P) test H) m (y, s) = .stop .trap := by
  rcases hxy with ⟨-, hy⟩ | ⟨top, A, hx, htop, hok, hy⟩ | ⟨hx, hy⟩
  · rw [hy]
    exact trap_one o P test H rfl rfl s
  · rcases x with ⟨K, stk⟩
    have hstk : stk = top :: A.map Prod.fst := hx
    have hb' : blockedOn (top :: A.map Prod.fst) = none := hstk ▸ hb
    have h' : sstep P test ⟨K, top :: A.map Prod.fst⟩ = .stop .trap := hstk ▸ h
    rw [hy]
    exact main_trap o P test H hS K top A htop hok hb' h' s
  · have h' : sstep P test (sInit f args) = .stop .trap := hx ▸ h
    have hr : tstep (compPO o P) test (tInit f args) = .stop .trap :=
      trap_of_res o P test f args (x := sInit f args) (y := tInit f args) h'
        (sel_call o P f args hS [] f true ⟨[.call f], args, none⟩ args [] []
          (fun h => by cases h) (fun ⟨_, h, _⟩ => by cases h) trivial)
    rw [hy]
    exact trap_one o P test H rfl hr s

/-! ## Blocking calls -/

/-- **A blocking call**: unwind every frame, the host answers at the root, rewind every frame. -/
theorem blocked_run (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o' : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (hp : popN n ops = some (p, o')) (hsp : split t rest = none) (s : σ) :
    runN (htstep (compPO o P) test H) (1 + (rest.length + (1 + (rest.length + 1))))
      (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩, s) =
      .next (trCO o ⟨K, ⟨c, (H.answer s t p).2 ++ o', w⟩ :: rest⟩, (H.answer s t p).1) := by
  let B : List (TFrame V) := ⟨compO o c, o'⟩ :: rest.map (trBO o)
  let a := H.answer s t p
  have h1 : tstep (compPO o P) test (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) =
      .next ⟨trKO o K, .unwind t p [⟨compO o c, o'⟩], rest.map (trBO o)⟩ :=
    suspendO_first o P test K t n c ops p o' w rest hp
  have h2 : runN (tstep (compPO o P) test) rest.length
      ⟨trKO o K, .unwind t p [⟨compO o c, o'⟩], rest.map (trBO o)⟩ =
      .next ⟨trKO o K, .unwind t p B, []⟩ := by
    have h := unwindO_run o test (compPO o P) (trKO o K) t p rest [⟨compO o c, o'⟩] []
      (split_none hsp)
    simpa only [List.append_nil, List.singleton_append] using h
  have h3 : htstep (compPO o P) test H (⟨trKO o K, .unwind t p B, []⟩, s) =
      .next (⟨trKO o K, .rewind B.reverse a.2, []⟩, a.1) := rfl
  have hB : B.reverse ≠ [] := by simp only [B, ne_eq, List.reverse_eq_nil_iff, reduceCtorEq,
    not_false_eq_true]
  have hlen : B.reverse.length = rest.length + 1 := by
    simp only [B, List.length_reverse, List.length_cons, List.length_map]
  have h4 : runN (tstep (compPO o P) test) B.reverse.length
      ⟨trKO o K, .rewind B.reverse a.2, []⟩ =
      .next (trCO o ⟨K, ⟨c, a.2 ++ o', w⟩ :: rest⟩) := by
    rw [rewind_run test (compPO o P) (trKO o K) a.2 B.reverse hB []]
    simp only [B, List.reverse_reverse, pushTop, List.append_nil, trCO, trSO]
  rw [runN_cat (runN_one_eq (htstep_next H h1 s)), runN_cat (runN_h_next H s _ _ _ h2),
    runN_cat (runN_one_eq h3), ← hlen]
  exact runN_h_next H a.1 _ _ _ h4

/-- A blocking call from a related pair is matched. -/
theorem blocked_sim {x : SCfg V} {y : TCfg V} (hxy : Rel o f args x y) {t : Nat}
    {p : List (SV V)} {fr : SFrame V} (hb : blockedOn x.stack = some (t, p, fr)) (s : σ) :
    ∃ n, 0 < n ∧ ResRel (HRel o f args) (hsstep P test H (x, s))
      (runN (htstep (compPO o P) test H) n (y, s)) := by
  obtain ⟨n, c, ops, w, rest, o', hx, hp, hsp, rfl⟩ := blockedOn_some hb
  have hsrc : hsstep P test H (x, s) =
      .next (⟨x.conts, ⟨c, (H.answer s t p).2 ++ o', w⟩ :: rest⟩, (H.answer s t p).1) := by
    have hb' : blockedOn (⟨.suspend t n :: c, ops, w⟩ :: rest) = some (t, p, ⟨c, o', w⟩) :=
      hx ▸ hb
    simp only [hsstep, hx, hb', List.tail_cons]
  have hy : y = trCO o x := by
    rcases hxy with ⟨hx', -⟩ | ⟨top, A, hx', htop, -, rfl⟩ | ⟨rfl, -⟩
    · cases hx.symm.trans hx'
    · have htop' : top = ⟨.suspend t n :: c, ops, w⟩ :=
        (List.cons.inj (hx'.symm.trans hx)).1
      have hn : ¬ Calm o.instr top.code := htop' ▸ calm_suspend
      rw [full_of_not_calm o htop hn, ← hx']
    · cases hx
  rcases x with ⟨K, stk⟩
  have hstk : stk = ⟨.suspend t n :: c, ops, w⟩ :: rest := hx
  refine ⟨1 + (rest.length + (1 + (rest.length + 1))), by omega, ?_⟩
  rw [hsrc, hy, hstk, blocked_run o P test H K t n c ops p o' w rest hp hsp s]
  exact ⟨rel_trCO o f args _, rfl⟩

/-! ## The simulation -/

/-- A kernel result matched by `n` asyncify steps is matched by `n` closed-target steps, unless
it is a trap. -/
theorem lift_res {x : SCfg V} {y : TCfg V} {n : Nat}
    (hres : ResRel (Rel o f args) (sstep P test x) (runN (tstep (compPO o P) test) n y))
    (hnt : sstep P test x ≠ .stop .trap) (s : σ) :
    ResRel (HRel o f args) ((sstep P test x).map (·, s))
      (runN (htstep (compPO o P) test H) n (y, s)) := by
  cases hs : sstep P test x with
  | next x' =>
    rw [hs] at hres
    obtain ⟨y', hy', hR⟩ := resRel_next hres
    rw [runN_h_next H s n y y' hy']
    exact ⟨hR, rfl⟩
  | stop out =>
    rw [hs] at hres
    have hr : runN (tstep (compPO o P) test) n y = .stop out := (resRel_stop hres).symm ▸ rfl
    cases out with
    | trap => exact absurd hs hnt
    | done vs =>
      rw [runN_h_done H s vs n y hr]
      rfl

/-- **The host-closed instance is a stuttering simulation** on a sound analysis. -/
theorem simRel_host (hS : Sound o.instr P) :
    SimRel (hsstep P test H) (htstep (compPO o P) test H) (HRel o f args) := by
  rintro ⟨x, s⟩ ⟨y, s'⟩ ⟨hxy, hs⟩
  have hs' : s' = s := hs.symm
  rw [hs']
  cases hb : blockedOn x.stack with
  | some b => exact blocked_sim o P test H f args hxy hb s
  | none =>
    show ∃ n, 0 < n ∧ ResRel _ (hsstep P test H (x, s)) _
    rw [hsstep_of_none hb s]
    by_cases ht : sstep P test x = .stop .trap
    · obtain ⟨m, hm, hrun⟩ := free_trap o P test H f args hS hxy hb ht s
      refine ⟨m, hm, ?_⟩
      rw [ht, hrun]
      rfl
    · obtain ⟨n, hn, hres⟩ := simRel_sel o P test f args hS x y hxy
      exact ⟨n, hn, lift_res o P test H f args hres ht s⟩

/-- **Blocking calls asyncified: equal behaviours** on a sound analysis, under every host. -/
theorem beh_host (hS : Sound o.instr P) (s : σ) :
    beh (hsstep P test H) (sInit f args, s) =
      beh (htstep (compPO o P) test H) (tInit f args, s) :=
  beh_eq_of_simRel (simRel_host o P test H f args hS) ⟨.inr (.inr ⟨rfl, rfl⟩), rfl⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Host
