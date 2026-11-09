module

public import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Units

/-!
# The single-threaded lift for litmus traces

`axReach_one_iff`: for one thread whose actions are `ActOk`, under every
model `M` with `SC ⊑ M ⊑ XL`, the axiomatic final states are exactly the final states of the
sequential replays (`actsReplay`) of its traces. The `XL` half (`axReach_one_sound`) needs only
`M ⊑ XL`; the `SC` half (`axReach_one_complete`) needs only `SC ⊑ M`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Test Final AxReach ReadsOk finalAx finalOf
  units rmwPairs)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel)

theorem forall2_single {T : List XTrace} {trs : List XTrace} :
    List.Forall₂ (· ∈ ·) trs [T] ↔ ∃ tr ∈ T, trs = [tr] := by
  constructor
  · intro h
    cases h with
    | cons h1 h2 => cases h2; exact ⟨_, h1, rfl⟩
  · rintro ⟨tr, h, rfl⟩; exact .cons h .nil

theorem Test_initB (t : Test) : t.initB = fun y => (t.initMem y).getD 0 := rfl

/-- In the sequential candidate, the coherence-last write is the last write. -/
theorem seq_coLast {evs : List Ev} {rmw : List (Nat × Nat)} (y : Nat) (w0 : Nat) (hw0 : WC evs y w0) :
    ((seqExec evs rmw).co y).getLast? = lastW evs y evs.length := by
  have hne : (seqExec evs rmw).co y ≠ [] := fun h => by
    have := (mem_co (rmw := rmw)).mpr hw0; rw [h] at this; simp at this
  obtain ⟨w, hw⟩ : ∃ w, ((seqExec evs rmw).co y).getLast? = some w :=
    ⟨_, List.getLast?_eq_some_getLast hne⟩
  rw [hw]
  have hwm := (mem_co (rmw := rmw)).mp (List.mem_of_getLast? hw)
  symm
  refine lastW_eq hwm.1 hwm fun j hj _ hjw => ?_
  have hb := before_last (List.Nodup.filter _ List.nodup_range) hw ((mem_co (rmw := rmw)).mpr hjw)
    (by omega)
  have := before_sorted (co_sorted (rmw := rmw) y) hb
  omega

/-- The core of soundness: from a well-formed candidate over the units of one thread whose
reads return their bytes and whose `po-loc | com` is acyclic, the actions replay to `memAt`,
which is the candidate's final memory. -/
theorem core_sound (tr : XTrace) (hok : ∀ a ∈ tr.acts, ActOk a) (m0 : Mem) (x : Exec)
    (hev : x.evs = (units [tr]).map Prod.fst) (hwf : x.Wf = true)
    (hrd : ∀ r < x.n, (x.evN r).isR = true →
      x.readBytes (fun y => (m0 y).getD 0) r = ((units [tr]).map Prod.snd).getD r [])
    (hu : BRel.Acyclic x.uniprocXl) :
    actsReplay m0 tr.acts = some (memAt x.evs m0 x.n) ∧ finalMem m0 x = memAt x.evs m0 x.n := by
  obtain ⟨hS, -⟩ := units_shape tr hok
  rw [← hev] at hS
  set us := units [tr] with hus
  have hlen : x.n = us.length := by simp [Exec.n, hev]
  have hget : ∀ r (hr : r < x.n), x.evs[r] = (us[r]'(hlen ▸ hr)).1 := by
    intro r hr; simp [hev]
  refine ⟨?_, ?_⟩
  · rw [← uReplay_units tr hok, (uReplay_iff us m0).mpr]
    refine ⟨fun r hr _ hR => ?_, by rw [← hev, hlen]⟩
    have hr' : r < x.n := hlen ▸ hr
    have hRx : (x.ev ⟨r, hr'⟩).isR = true := by simpa [Exec.ev, hget r hr'] using hR
    have h1 := hrd r hr' (by rwa [evN_eq hr'])
    rw [readBytes_of m0 hr' fun y hy => rf_lastW hS hwf hu ⟨r, hr'⟩ hRx hy] at h1
    rw [hget r hr'] at h1
    rw [← hev, h1]
    simp [List.getElem?_eq_getElem hr]
  · funext y
    exact finalMem_of m0 (fun y w hW hC => coLast_lastW hS hwf hu w hW hC) y

/-- The core of completeness: if the actions replay to `m`, the sequential candidate over their
units is well-formed, SC, returns the actions' bytes, and ends in `m`. -/
theorem core_complete (tr : XTrace) (hok : ∀ a ∈ tr.acts, ActOk a) (m0 : Mem) {m : Mem}
    (hm : actsReplay m0 tr.acts = some m) :
    let x := seqExec ((units [tr]).map Prod.fst) (rmwPairs ((units [tr]).map Prod.fst))
    x.Wf = true ∧ x.Sc ∧
      (∀ r < x.n, (x.evN r).isR = true →
        x.readBytes (fun y => (m0 y).getD 0) r = ((units [tr]).map Prod.snd).getD r []) ∧
      finalMem m0 x = m := by
  intro x
  obtain ⟨hS, hW⟩ := units_shape tr hok
  set us := units [tr] with hus
  set evs := us.map Prod.fst with hevs
  rw [← uReplay_units tr hok, uReplay_iff] at hm
  obtain ⟨hR, rfl⟩ := hm
  have hlen : x.n = us.length := by simp [Exec.n, x, seqExec, hus]
  refine ⟨seqExec_wf hS hW, seqExec_sc hS, ?_, ?_⟩
  · intro r hr hRx
    have hr' : r < us.length := hlen ▸ hr
    rw [readBytes_of (x := x) m0 hr fun y _ => rfl]
    have hxr : x.evs[r] = us[r].1 := by simp [x, seqExec, hus]
    rw [evN_eq hr, hxr] at hRx
    have h3 := hR r hr' hr' hRx
    simp only [← hus] at h3 ⊢
    rw [hxr, show x.evs = us.map Prod.fst from rfl, ← h3]
    simp [List.getElem?_eq_getElem hr']
  · funext y
    have := finalMem_of (x := x) m0 (fun y w hW hC => seq_coLast y w.val ⟨w.2, hW, hC⟩) y
    simp only [finalMem]
    rw [this]
    simp [x, seqExec, Exec.n]

/-- **Soundness**: under `M ⊑ XL`, every axiomatic final state of one thread is a sequential
one. -/
theorem axReach_one_sound (t : Test) (T : List XTrace) (hok : ∀ tr ∈ T, ∀ a ∈ tr.acts, ActOk a)
    {M : Exec → Prop} (hxl : ∀ x, M x → x.Xl) {f : Final} (h : AxReach t [T] M f) :
    ∃ tr ∈ T, ∃ m, actsReplay t.initMem tr.acts = some m ∧ f = finalOf [tr] m := by
  obtain ⟨trs, h2, x, hev, hrmw, hwf, hrd, hM, rfl⟩ := h
  obtain ⟨tr, htr, rfl⟩ := forall2_single.mp h2
  obtain ⟨h1, h2⟩ := core_sound tr (hok tr htr) t.initMem x hev hwf hrd (hxl x hM).2.1
  refine ⟨tr, htr, _, h1, ?_⟩
  simp only [finalAx, Test_initB]
  rw [← h2]; rfl

/-- **Completeness**: under `SC ⊑ M`, every sequential final state of one thread is an axiomatic
one. -/
theorem axReach_one_complete (t : Test) (T : List XTrace) (hok : ∀ tr ∈ T, ∀ a ∈ tr.acts, ActOk a)
    {M : Exec → Prop} (hsc : ∀ x, x.Sc → M x) {tr : XTrace} (htr : tr ∈ T) {m : Mem}
    (hm : actsReplay t.initMem tr.acts = some m) : AxReach t [T] M (finalOf [tr] m) := by
  obtain ⟨h1, h2, h3, h4⟩ := core_complete tr (hok tr htr) t.initMem hm
  refine ⟨[tr], forall2_single.mpr ⟨tr, htr, rfl⟩, _, rfl, rfl, h1, h3, hsc _ h2, ?_⟩
  simp only [finalAx, Test_initB]
  rw [← h4]; rfl

/-- **The single-threaded lift for litmus traces.** -/
theorem axReach_one_iff (t : Test) (T : List XTrace) (hok : ∀ tr ∈ T, ∀ a ∈ tr.acts, ActOk a)
    {M : Exec → Prop} (hsc : ∀ x, x.Sc → M x) (hxl : ∀ x, M x → x.Xl) (f : Final) :
    AxReach t [T] M f ↔ ∃ tr ∈ T, ∃ m, actsReplay t.initMem tr.acts = some m ∧ f = finalOf [tr] m := by
  constructor
  · exact axReach_one_sound t T hok hxl
  · rintro ⟨tr, htr, m, hm, rfl⟩
    exact axReach_one_complete t T hok hsc htr hm

theorem trOf_acts (acts : List XAct) : (trOf acts).acts = acts := by
  simp [trOf, Silmaril.X86.Litmus.Trace.acts]

/-- **The single-threaded lift from any memory**: under every `M` with `SC ⊑ M ⊑ XL`, the
behaviours of one thread's action list are exactly its sequential replay. -/
theorem oneSem_iff {M : Exec → Prop} (hsc : ∀ x, x.Sc → M x) (hxl : ∀ x, M x → x.Xl)
    (m0 : Mem) (acts : List XAct) (hok : ∀ a ∈ acts, ActOk a) (m : Mem) :
    OneSem M m0 acts m ↔ actsReplay m0 acts = some m := by
  have hok' : ∀ a ∈ (trOf acts).acts, ActOk a := by rw [trOf_acts]; exact hok
  constructor
  · rintro ⟨x, hev, -, hwf, hrd, hM, rfl⟩
    obtain ⟨h1, h2⟩ := core_sound (trOf acts) hok' m0 x hev hwf hrd (hxl x hM).2.1
    rw [trOf_acts] at h1
    rw [h1, h2]
  · intro hm
    rw [← trOf_acts acts] at hm
    obtain ⟨h1, h2, h3, h4⟩ := core_complete (trOf acts) hok' m0 hm
    exact ⟨_, rfl, rfl, h1, h3, hsc _ h2, h4.symm⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Seq
