module

public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Mem
public import Silmaril.Proofs.X86.Concurrency.Bridge.TvRun
public import Silmaril.X86.Atomic9.Converse.Thms

/-!
# Gap 1: recording a TSO pool run of validated threads

`reach_inv`: a run of the TSO pool (`TsoReach atomic9Ev`) from a test memory, for a
test whose certificates `tvRun` accepts, is a recorded run (`RunA`), keeps the memory
invariant `MemInv`, and every thread's history is a symbolic run (`XRun`) of the thread from its
initial core (`ThInv`). One step (`step_acts`): the view has the thread's regions, code and
backing (`MemInv.view`), so the symbolic step is defined there (`tvRunDefined_holds`) and
the real step is one of its branches (`xstep_of_step`); the pool's fetch on the view is the litmus
fetch on the code (`fetch_of_listed_base`, `fetch_of_listed_new`), so the branch's events are
the instruction's access list.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun

open Silmaril.X86 (State Byte Word)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep stepSym)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Pool (TPool TsoStep TsoFlush TsoReach overlay syncs storeEntries atomic9Ev)
open Silmaril.X86.Concurrency.Bridge
open Silmaril.X86.Concurrency.Bridge.PoolRun
open Silmaril.X86.Concurrency.Cir.TvCfg (XStep XRun)
open Silmaril.X86.Concurrency.Cir.Tv (XThread TvTest Cert tvRun)

theorem xrun_snoc {t : XThread} {s : State} {acc : List (List XAct)} {s₁ : State}
    (h : XRun t s acc s₁) {acts : List XAct} {s₂ : State} (hs : XStep t s₁ acts s₂) :
    XRun t s (acc ++ [acts]) s₂ := by
  revert hs
  induction h with
  | nil => exact fun hs => .cons hs .nil
  | cons h _ ih => exact fun hs => .cons h (ih hs)

/-- **One step of an accepted thread on a good view** has `StepActs` actions and is a symbolic
step. -/
theorem step_acts {X : XThread} {ct : Cert} {K : List Silmaril.X86.Reg} (hK : tvRun X ct = some K)
    {acc : List (List XAct)} {c : State} (hx : XRun X X.init acc c) (hne : c.rip ≠ X.endRip)
    {view : Memory} (hR : view.regions = X.regions) (hl : Loaded view X.base X.code)
    (hb : Backed view) {i : Atomic9.Instr} {n : Nat} {c' : State} {view' : Memory}
    (hf : MemEvent.atomic9Fetch view c.rip.toNat = some (i, n))
    (he : Atomic9.exec i c view n = .ok c' view') :
    ∃ acts, StepActs acts i c n ⟨view, c', view'⟩ ∧ XStep X c acts c' := by
  have hs : Atomic9.step ⟨c, view⟩ = some ⟨c', view'⟩ := by
    rw [MemEvent.atomic9_step_eq]
    simp [hf, he, Open.ofResult]
  obtain ⟨dom₀, outs₀, h0⟩ :=
    Bridge.tvRunDefined_holds hK acc c hx hne view c' view' hR hl hs
  obtain ⟨dom, outs, acts, hso, hmem, hans, hap⟩ := Bridge.xstep_of_step h0 hR hl hb hs
  obtain ⟨o, i₂, n₂, K₁, Z₁, ops, K₂, Z₂, hrip, ho, hfa, hc⟩ :=
    Silmaril.X86.Concurrency.Cir.Tv.tvRun_reach hK hx hne
  have hft : X.fetch c = some (i₂, n₂) := by
    unfold Silmaril.X86.Litmus.Thread.fetch
    rw [Bridge.off_of_rip hrip (Nat.lt_trans ho (Bridge.tvRun_len hK))]
    exact hfa
  obtain ⟨hsh, -⟩ := Bridge.chk1_ok hc
  obtain ⟨hfit, hdec⟩ := Bridge.fetchAt_spec hfa
  have hf2 : MemEvent.atomic9Fetch view c.rip.toNat = some (i₂, n₂) := by
    rcases hsh with ⟨b, rfl⟩ | ⟨j, rfl⟩
    · exact Atomic9.fetch_of_listed_base hl hrip hfit hdec
    · exact Atomic9.fetch_of_listed_new hl hrip hfit hdec
  rw [hf2] at hf
  simp only [Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  obtain ⟨i₃, n₃, hf3, hev⟩ := Silmaril.X86.Litmus.stepSym_events hso hmem
  rw [hft] at hf3
  simp only [Option.some.injEq, Prod.mk.injEq] at hf3
  obtain ⟨rfl, rfl⟩ := hf3
  exact ⟨acts, ⟨Silmaril.X86.Concurrency.Bridge.PoolRun.stepSym_shape hso _ hmem, hev, hans, hap⟩, dom, outs, hso, hmem⟩

/-! ## The thread invariant -/

/-- Every thread of the test has a core whose history is a symbolic run from its initial core;
no other thread exists. -/
structure ThInv (c : TvTest) (H : Nat → List Obs) (p : TPool Nat) : Prop where
  run : ∀ k th, c.test.threads[k]? = some th → ∃ s, p.threads k = some s ∧
    XRun (c.test.xthread k th) (c.test.xthread k th).init ((H k).map Obs.acts) s
  none : ∀ k, c.test.threads[k]? = none → p.threads k = none

theorem mapM_id_get {α : Type} : ∀ {l : List (Option α)} {rs : List α}, l.mapM id = some rs →
    ∀ k : Nat, l[k]? = (rs[k]?).map some
  | [], rs, h, k => by simp at h; subst h; simp
  | a :: l, rs, h, k => by
    rw [List.mapM_cons] at h
    simp only [id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, rfl, ys, hl, rfl⟩ := h
    cases k with
    | zero => simp
    | succ k => simpa using mapM_id_get hl k

/-- **An accepted test's threads are accepted**, with the clobber set the test records. -/
theorem tvRun_of_tvOk {c : TvTest} (hok : c.tvOk = true) :
    ∃ Ks, c.clobs = some Ks ∧ Silmaril.X86.Concurrency.Cir.Tv.condAvoids c.test.cond Ks = true ∧
      c.test.threads.length = c.certs.length ∧
      ∀ k th, c.test.threads[k]? = some th →
        tvRun (c.test.xthread k th) (c.cert k) = some (Ks.getD k []) := by
  unfold TvTest.tvOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hlen, hc⟩ := hok
  split at hc
  · rename_i Ks hKs
    refine ⟨Ks, hKs, hc, hlen, fun k th hth => ?_⟩
    have := mapM_id_get hKs k
    rw [List.getElem?_mapIdx, hth] at this
    simp only [Option.map_some] at this
    cases hk : Ks[k]? with
    | none => rw [hk] at this; cases this
    | some K =>
      rw [hk] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this]
      simp [List.getD_eq_getElem?_getD, hk]
  · cases hc

/-- **The views of a test's threads are good**: the thread's regions, its code, backed. -/
theorem good_view {c : TvTest} {m₀ : Memory} (hm : TestMem c.test m₀) {p : TPool Nat}
    (hmi : MemInv c.test.threads.length m₀ p) (t : Nat) {th : Silmaril.X86.MemoryModel.Litmus.Thread}
    (hth : c.test.threads[t]? = some th) :
    (overlay p.memory (p.buffer t)).regions = (c.test.xthread t th).regions ∧
      Loaded (overlay p.memory (p.buffer t)) (c.test.xthread t th).base
        (c.test.xthread t th).code ∧
      Backed (overlay p.memory (p.buffer t)) := by
  obtain ⟨hR, hb, hx⟩ := hmi.view t
  refine ⟨hR, loaded_congr (hm.2.1 t th hth) (hR.trans hm.1.symm) fun a ha => hx a ?_, hb⟩
  have : (overlay p.memory (p.buffer t)).permits .execute a = m₀.permits .execute a := by
    simp only [Memory.permits, hR, hm.1]
  rw [this]; exact ha

/-- The stepping thread exists, has not finished, and its history is a symbolic run. -/
theorem stepping {c : TvTest} {H : Nat → List Obs} {p : TPool Nat} (h : ThInv c H p) {t : Nat}
    {c₁ : State} (ht : p.threads t = some c₁) (hnf : ¬ TestFin c.test t c₁) :
    ∃ th, c.test.threads[t]? = some th ∧ c₁.rip ≠ (c.test.xthread t th).endRip ∧
      XRun (c.test.xthread t th) (c.test.xthread t th).init ((H t).map Obs.acts) c₁ := by
  cases hth : c.test.threads[t]? with
  | none => rw [h.none t hth] at ht; cases ht
  | some th =>
    obtain ⟨s, hs, hx⟩ := h.run t th hth
    rw [ht] at hs
    cases hs
    refine ⟨th, rfl, fun he => hnf fun th' hth' => ?_, hx⟩
    rw [hth] at hth'
    cases hth'
    exact he

/-- **The thread invariant is kept by a step** of thread `t` to core `c'` with actions `acts`. -/
theorem thInv_update {c : TvTest} {H : Nat → List Obs} {p : TPool Nat} (h : ThInv c H p)
    {t : Nat} {c₁ c' : State} {o : Obs} (ht : p.threads t = some c₁)
    (hx : ∀ th, c.test.threads[t]? = some th → XStep (c.test.xthread t th) c₁ o.acts c')
    {p' : TPool Nat} (hp' : p'.threads = Function.update p.threads t (some c')) :
    ThInv c (Function.update H t (H t ++ [o])) p' := by
  refine ⟨fun k th hth => ?_, fun k hk => ?_⟩
  · by_cases hkt : k = t
    · subst hkt
      obtain ⟨s, hs, hr⟩ := h.run k th hth
      rw [ht] at hs
      cases hs
      refine ⟨c', by rw [hp']; simp, ?_⟩
      simp only [Function.update_self, List.map_append, List.map_cons, List.map_nil]
      exact xrun_snoc hr (hx th hth)
    · obtain ⟨s, hs, hr⟩ := h.run k th hth
      refine ⟨s, by rw [hp', Function.update_of_ne hkt]; exact hs, ?_⟩
      rw [Function.update_of_ne hkt]
      exact hr
  · have hkt : k ≠ t := by
      rintro rfl
      rw [h.none k hk] at ht
      cases ht
    rw [hp', Function.update_of_ne hkt]
    exact h.none k hk

/-- **The invariants along a TSO pool run** of an accepted test from a test memory. -/
theorem reach_inv {c : TvTest} (hok : c.tvOk = true) {m₀ : Memory} (hm : TestMem c.test m₀)
    {p : TPool Nat} (h : TsoReach atomic9Ev (TestFin c.test) (testPool c.test m₀) p) :
    ∃ H, RunA (TestFin c.test) (testPool c.test m₀) H p ∧
      MemInv c.test.threads.length m₀ p ∧ ThInv c H p := by
  obtain ⟨Ks, -, -, -, hKs⟩ := tvRun_of_tvOk hok
  induction h with
  | refl =>
    refine ⟨fun _ => [], .refl, memInv_init hm, fun k th hth => ?_, fun k hk => ?_⟩
    · exact ⟨_, by simp [testPool, hth], .nil⟩
    · simp [testPool, hk]
  | tail _ hst ih =>
    obtain ⟨H, hr, hmi, hti⟩ := ih
    rcases hst with ⟨t, hs⟩ | hf
    · -- the thread's history and view
      have hmi' := memInv_step hmi hs
      cases hs with
      | @sync c₁ c' i n mem' ht hnf hf hsy he hx =>
        obtain ⟨th, hth, hne, hxr⟩ := stepping hti ht hnf
        obtain ⟨hR, hl, hb⟩ := good_view hm hmi t hth
        rw [he] at hR hl hb hf
        obtain ⟨acts, ha, hxs⟩ := step_acts (hKs t th hth) hxr hne hR hl hb hf hx
        exact ⟨_, .step hr (.sync ht hnf (by rw [he]; exact hf) hsy he hx ha), hmi',
          thInv_update hti ht (o := ⟨c₁, acts, _⟩) (fun th' hth' => by
            rw [hth] at hth'; cases hth'; exact hxs) rfl⟩
      | @buffered c₁ c' i n view' ht hnf hf hsy hx =>
        obtain ⟨th, hth, hne, hxr⟩ := stepping hti ht hnf
        obtain ⟨hR, hl, hb⟩ := good_view hm hmi t hth
        obtain ⟨acts, ha, hxs⟩ := step_acts (hKs t th hth) hxr hne hR hl hb hf hx
        exact ⟨_, .step hr (.buffered ht hnf hf hsy hx ha), hmi',
          thInv_update hti ht (o := ⟨c₁, acts, _⟩) (fun th' hth' => by
            rw [hth] at hth'; cases hth'; exact hxs) rfl⟩
    · refine ⟨H, .flush hr hf, memInv_flush hmi hf, ?_⟩
      cases hf with
      | head hb => exact ⟨fun k th h => hti.run k th h, fun k h => hti.none k h⟩

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun
