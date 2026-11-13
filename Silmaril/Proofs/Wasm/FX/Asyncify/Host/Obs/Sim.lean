module

public import Silmaril.Wasm.FX.Asyncify.Host.Thms
public import Silmaril.Wasm.FX.Asyncify.Host.Obs.Defs

/-!
# Asyncify with a host: the simulation, host states observed

`simRel_hostO`: the relation `HRel` of `simRel_host` (the selective relation, equal host
states) is a stuttering simulation between the observing machines `observe hsstep` and
`observe htstep`. Continuing steps are those of `simRel_host`; a stop is matched by a stop with
the same outcome **and the same host state**: every stop of the closed target that matches a
kernel stop is reached by asyncify steps alone, away from the root, so the host state is the
one of the related pair. The trap lemmas of `Host.Sim` are restated for the observing target
(`trap_oneO`, `handled_trapO`, `suspend_trapO`, `main_trapO`, `free_trapO`), with the same
proofs on the same runs.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Host

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Proofs.Wasm.FX.Asyncify
open Silmaril.Proofs.Wasm.Models.FXAsync (runN_one split_spec)

variable {V σ : Type}

/-! ## Observing machines -/

section generic

variable {C : Type} {step : C × σ → Res (C × σ) V}

theorem observe_next {x y : C × σ} (h : step x = .next y) : observe step x = .next y := by
  simp only [observe, h]

theorem observe_stop {x : C × σ} {out : Outcome V} (h : step x = .stop out) :
    observe step x = .stop (.done [.val (HOut.ofOutcome x.2 out)]) := by
  simp only [observe, h]

/-- A continuing run is a run of the observing machine. -/
theorem runN_observe_next : ∀ (n : Nat) (x z : C × σ), runN step n x = .next z →
    runN (observe step) n x = .next z
  | 0, _, _, h => by
    have e : _ = _ := Res.next.inj h
    rw [e]; rfl
  | n + 1, x, z, h => by
    cases hs : step x with
    | next x₁ =>
      have h' : runN step n x₁ = .next z := by simpa only [runN, hs] using h
      have e : runN (observe step) (n + 1) x = runN (observe step) n x₁ := by
        simp only [runN, observe_next hs]
      rw [e]
      exact runN_observe_next n x₁ z h'
    | stop o =>
      have h' : (Res.stop o : Res (C × σ) V) = .next z := by simpa only [runN, hs] using h
      cases h'

/-- Related results transfer to the observing machines when the source continues. -/
theorem resRel_observe {D : Type} {t : D × σ → Res (D × σ) V} {R : C × σ → D × σ → Prop}
    {x x' : C × σ} {y : D × σ} {n : Nat} (hx : step x = .next x')
    (h : ResRel R (step x) (runN t n y)) :
    ResRel R (observe step x) (runN (observe t) n y) := by
  rw [hx] at h
  obtain ⟨y', hy', hR⟩ := resRel_next h
  rw [observe_next hx, runN_observe_next n y y' hy']
  exact hR

end generic

/-! ## The observing closed target -/

section target

variable {Q : Prog (TIns V)} {test : V → Bool} (H : KHost V σ)

/-- Asyncify steps, then a trap away from the root: an observed trap with the same host state. -/
theorem trap_after {a : Nat} {y z : TCfg V} (h : runN (tstep Q test) a y = .next z)
    (hz : tstep Q test z = .stop .trap) (hr : atRoot z = none) (s : σ) :
    runN (observe (htstep Q test H)) (a + 1) (y, s) = .stop (.done [.val (.trap s)]) := by
  rw [runN_cat (runN_observe_next a _ _ (runN_h_next H s a y z h))]
  exact runN_one_eq (observe_stop (htstep_stop H hz (.inr hr) s))

/-- A returning run of the asyncify machine: an observed result with the same host state. -/
theorem runN_hO_done (s : σ) (vs : List (SV V)) : ∀ (n : Nat) (y : TCfg V),
    runN (tstep Q test) n y = .stop (.done vs) →
    runN (observe (htstep Q test H)) n (y, s) = .stop (.done [.val (.done vs s)])
  | 0, _, h => by cases h
  | n + 1, y, h => by
    cases hs : tstep Q test y with
    | next y₁ =>
      have h' : runN (tstep Q test) n y₁ = .stop (.done vs) := by simpa only [runN, hs] using h
      have e : runN (observe (htstep Q test H)) (n + 1) (y, s) =
          runN (observe (htstep Q test H)) n (y₁, s) := by
        simp only [runN, observe_next (htstep_next H hs s)]
      rw [e]
      exact runN_hO_done s vs n y₁ h'
    | stop o =>
      have ho : o = .done vs := by simpa only [runN, hs, Res.stop.injEq] using h
      have hstep : htstep Q test H (y, s) = .stop (.done vs) :=
        htstep_stop H (hs.trans (congrArg _ ho)) (.inl (by intro h; cases h)) s
      simp only [runN, observe_stop hstep]
      rfl

end target

/-! ## Traps away from blocking calls, observed -/

variable (o : Opt) (P : Prog (Ins V)) (test : V → Bool) (H : KHost V σ)
  (f : Nat) (args : List (SV V))

/-- An observed trap of the closed target, with host state `s`. -/
def TrapO (y : TCfg V) (s : σ) : Prop :=
  ∃ m, 0 < m ∧ runN (observe (htstep (compPO o P) test H)) m (y, s) = .stop (.done [.val (.trap s)])

theorem trap_oneO {y : TCfg V} (hy : y.mode = .normal) (h : tstep (compPO o P) test y = .stop .trap)
    (s : σ) : TrapO o P test H y s :=
  ⟨0 + 1, Nat.succ_pos 0, trap_after H (a := 0) rfl h (atRoot_normal hy) s⟩

theorem handled_trapO (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops p o' : List (SV V)) (w : Option (List Clause)) (m : List (SFrame V)) (hf : Nat)
    (r : SFrame V) (rs : List (SFrame V)) (hp : popN n ops = some (p, o'))
    (hm : ∀ b ∈ m, b.wait.bind (lookup t) = none) (hr : r.wait.bind (lookup t) = some hf)
    (hP : P hf = none) (s : σ) :
    TrapO o P test H (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩) s := by
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
  have h12 : runN (tstep (compPO o P) test) (1 + m.length)
      (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩) =
      .next ⟨trKO o K, .unwind t p ([⟨compO o c, o'⟩] ++ m.map (trBO o)),
        trBO o r :: rs.map (trBO o)⟩ := by
    rw [runN_cat (runN_one_eq h1), hmap]
    exact h2
  have hPc : compPO o P hf = none := by simp only [compPO, hP, Option.map_none]
  have h3 : tstep (compPO o P) test ⟨trKO o K, .unwind t p ([⟨compO o c, o'⟩] ++ m.map (trBO o)),
      trBO o r :: rs.map (trBO o)⟩ = .stop .trap := by
    rw [unwindO_handle o test (compPO o P) (trKO o K) t p _ r _ hr, hPc]
  exact ⟨1 + m.length + 1, by omega, trap_after H h12 h3 atRoot_cons s⟩

theorem suspend_trapO (K : List (Option (List (SFrame V)))) (t n : Nat) (c : List (Ins V))
    (ops : List (SV V)) (w : Option (List Clause)) (rest : List (SFrame V))
    (hb : blockedOn (⟨.suspend t n :: c, ops, w⟩ :: rest) = none)
    (h : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩ = .stop .trap) (s : σ) :
    TrapO o P test H (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) s := by
  rcases hp : popN n ops with _ | ⟨p, o'⟩
  · refine trap_oneO o P test H rfl ?_ s
    simp only [tstep, trCO, trSO, compO, texec, hp]
  rcases hsp : split t rest with _ | ⟨m, hf, r, rs⟩
  · have hb' : blockedOn (⟨.suspend t n :: c, ops, w⟩ :: rest) = some (t, p, ⟨c, o', w⟩) := by
      simp only [blockedOn, hp, hsp]
    cases hb.symm.trans hb'
  · show TrapO o P test H (trCO o ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: rest⟩) s
    obtain ⟨hL, hm, hr⟩ := split_spec hsp
    have hsp' : split t (m ++ r :: rs) = some (m, hf, r, rs) := hL ▸ hsp
    have hP : P hf = none := by
      cases hPf : P hf with
      | none => rfl
      | some q =>
        have hn : sstep P test ⟨K, ⟨.suspend t n :: c, ops, w⟩ :: (m ++ r :: rs)⟩ ≠ .stop .trap := by
          simp only [sstep, sexec, hp, hsp', hPf, ne_eq, reduceCtorEq, not_false_eq_true]
        exact absurd (hL ▸ h) hn
    rw [hL]
    exact handled_trapO o P test H K t n c ops p o' w m hf r rs hp hm hr hP s

theorem main_trapO (hS : Sound o.instr P) (K : List (Option (List (SFrame V)))) (top : SFrame V)
    (A : List (SFrame V × Bool)) (htop : HasU A → Calm o.instr top.code)
    (hok : OkR o.instr A) (hb : blockedOn (top :: A.map Prod.fst) = none)
    (h : sstep P test ⟨K, top :: A.map Prod.fst⟩ = .stop .trap) (s : σ) :
    TrapO o P test H ⟨trKO o K, .normal, ⟨compO o top.code, top.ops⟩ :: A.map (trF o)⟩ s := by
  rcases top with ⟨_ | ⟨i, c⟩, ops, w⟩
  · rcases A with _ | ⟨⟨b, fl⟩, L⟩ <;> cases h
  cases i with
  | push v => cases h
  | prim n op =>
    exact trap_oneO o P test H rfl (topRes_trap o (top_prim o P test K n op c ops w A) h) s
  | drop => exact trap_oneO o P test H rfl (topRes_trap o (top_drop o P test K c ops w A) h) s
  | contNew g =>
    exact trap_oneO o P test H rfl (topRes_trap o (top_contNew o P test K g c ops w A) h) s
  | call g =>
    exact trap_oneO o P test H rfl (trap_of_res o P test 0 []
      (y := ⟨trKO o K, .normal, ⟨compO o (.call g :: c), ops⟩ :: A.map (trF o)⟩) h
      (sel_call o P 0 [] hS K g (o.instr g) ⟨.call g :: c, ops, w⟩ ops c A id
        (fun hu => ⟨calm_tail (htop hu), calm_call (htop hu)⟩) hok)) s
  | cond g g' =>
    exact trap_oneO o P test H rfl
      (trap_of_res o P test 0 [] h (cond_res o P test 0 [] hS K g g' c ops w A htop hok)) s
  | resume n hs =>
    rw [full_of_not_calm o htop calm_resume]
    exact trap_oneO o P test H rfl (resume_trap o P test K n hs c ops w _ h) s
  | suspend t n =>
    rw [full_of_not_calm o htop calm_suspend]
    exact suspend_trapO o P test H K t n c ops w _ hb h s

/-- **Away from a blocking call, a kernel trap is an observed trap with the same host state.** -/
theorem free_trapO (hS : Sound o.instr P) {x : SCfg V} {y : TCfg V} (hxy : Rel o f args x y)
    (hb : blockedOn x.stack = none) (h : sstep P test x = .stop .trap) (s : σ) :
    TrapO o P test H y s := by
  rcases hxy with ⟨-, hy⟩ | ⟨top, A, hx, htop, hok, hy⟩ | ⟨hx, hy⟩
  · rw [hy]
    exact trap_oneO o P test H rfl rfl s
  · rcases x with ⟨K, stk⟩
    have hstk : stk = top :: A.map Prod.fst := hx
    have hb' : blockedOn (top :: A.map Prod.fst) = none := hstk ▸ hb
    have h' : sstep P test ⟨K, top :: A.map Prod.fst⟩ = .stop .trap := hstk ▸ h
    rw [hy]
    exact main_trapO o P test H hS K top A htop hok hb' h' s
  · have h' : sstep P test (sInit f args) = .stop .trap := hx ▸ h
    have hr : tstep (compPO o P) test (tInit f args) = .stop .trap :=
      trap_of_res o P test f args (x := sInit f args) (y := tInit f args) h'
        (sel_call o P f args hS [] f true ⟨[.call f], args, none⟩ args [] []
          (fun h => by cases h) (fun ⟨_, h, _⟩ => by cases h) trivial)
    rw [hy]
    exact trap_oneO o P test H rfl hr s

/-! ## The simulation -/

/-- Away from a blocking call, a kernel result matched by `n` asyncify steps, not a trap,
observed. -/
theorem lift_resO {x : SCfg V} {y : TCfg V} {n : Nat} (hbl : blockedOn x.stack = none)
    (hres : ResRel (Rel o f args) (sstep P test x) (runN (tstep (compPO o P) test) n y))
    (hnt : sstep P test x ≠ .stop .trap) (s : σ) :
    ResRel (HRel o f args) (observe (hsstep P test H) (x, s))
      (runN (observe (htstep (compPO o P) test H)) n (y, s)) := by
  have e : hsstep P test H (x, s) = (sstep P test x).map (·, s) := hsstep_of_none hbl s
  have hl : ResRel (HRel o f args) (hsstep P test H (x, s))
      (runN (htstep (compPO o P) test H) n (y, s)) := by
    rw [e]
    exact lift_res o P test H f args hres hnt s
  cases hs : sstep P test x with
  | next x' =>
    have hn : hsstep P test H (x, s) = .next (x', s) := by rw [e, hs]; rfl
    exact resRel_observe hn hl
  | stop out =>
    cases out with
    | trap => exact absurd hs hnt
    | done vs =>
      have hres' : ResRel (Rel o f args) (.stop (.done vs))
          (runN (tstep (compPO o P) test) n y) := hs ▸ hres
      have hr : runN (tstep (compPO o P) test) n y = .stop (.done vs) := resRel_stop hres'
      have hst : hsstep P test H (x, s) = .stop (.done vs) := by rw [e, hs]; rfl
      rw [observe_stop hst, runN_hO_done H s vs n y hr]
      rfl

/-- A blocking call from a related pair, observed. -/
theorem blocked_simO {x : SCfg V} {y : TCfg V} (hxy : Rel o f args x y) {t : Nat}
    {p : List (SV V)} {fr : SFrame V} (hb : blockedOn x.stack = some (t, p, fr)) (s : σ) :
    ∃ n, 0 < n ∧ ResRel (HRel o f args) (observe (hsstep P test H) (x, s))
      (runN (observe (htstep (compPO o P) test H)) n (y, s)) := by
  obtain ⟨n, hn, hres⟩ := blocked_sim o P test H f args hxy hb s
  have hx : hsstep P test H (x, s) =
      .next (⟨x.conts, { fr with ops := (H.answer s t p).2 ++ fr.ops } :: x.stack.tail⟩,
        (H.answer s t p).1) := by
    simp only [hsstep, hb]
  exact ⟨n, hn, resRel_observe hx hres⟩

/-- **The host-closed instance, host states observed, is a stuttering simulation.** -/
theorem simRel_hostO (hS : Sound o.instr P) :
    SimRel (observe (hsstep P test H)) (observe (htstep (compPO o P) test H)) (HRel o f args) := by
  rintro ⟨x, s⟩ ⟨y, s'⟩ ⟨hxy, hs⟩
  have hs' : s' = s := hs.symm
  rw [hs']
  cases hb : blockedOn x.stack with
  | some b =>
    obtain ⟨t, p, fr⟩ := b
    exact blocked_simO o P test H f args hxy hb s
  | none =>
    by_cases ht : sstep P test x = .stop .trap
    · obtain ⟨m, hm, hrun⟩ := free_trapO o P test H f args hS hxy hb ht s
      have hst : hsstep P test H (x, s) = .stop .trap := by rw [hsstep_of_none hb s, ht]; rfl
      refine ⟨m, hm, ?_⟩
      rw [observe_stop hst, hrun]
      rfl
    · obtain ⟨n, hn, hres⟩ := simRel_sel o P test f args hS x y hxy
      exact ⟨n, hn, lift_resO o P test H f args hb hres ht s⟩

/-- **Blocking calls asyncified: equal behaviours with the final host state.** -/
theorem beh_hostO (hS : Sound o.instr P) (s : σ) :
    beh (observe (hsstep P test H)) (sInit f args, s) =
      beh (observe (htstep (compPO o P) test H)) (tInit f args, s) :=
  beh_eq_of_simRel (simRel_hostO o P test H f args hS) ⟨.inr (.inr ⟨rfl, rfl⟩), rfl⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Host
