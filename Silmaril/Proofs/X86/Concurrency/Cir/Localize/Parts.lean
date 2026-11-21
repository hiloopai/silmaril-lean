module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Frag

/-!
# Localisation: the parts of the units, and the traces

Facts about the kept parts `A` and `C` of `units_split`, and about the
per-thread traces of a behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace actUnits threadUnits accUnits units)

/-! ## The kept parts -/

theorem mem_sp_flatMap {us : List (Ev × List Byte)} {l : List (Ev × List Byte)}
    {u : Ev × List Byte} (h : u ∈ l.flatMap (sp us)) : ∃ v ∈ l, u ∈ sp us v := by
  simpa using h

/-- The kept units before the fragment. -/
theorem partA {trs : List XTrace} {i : Nat} {a1 : List XAct} {cs : List (Nat × Nat)}
    (hoth : ∀ k (hk : k < trs.length), k ≠ i → ∀ a ∈ (trs[k]).acts, ActAvoid cs a)
    (h1 : ∀ a ∈ a1, ActAvoid cs a) :
    ∀ u ∈ (((UL trs).take i).flatten ++ threadUnits i 0 a1).flatMap (sp (accUnits trs)),
      UK cs u ∧ (u.1.tid = i → u.1.pos < (threadUnits i 0 a1).length) := by
  intro u hu
  obtain ⟨v, hv, huv⟩ := mem_sp_flatMap hu
  obtain ⟨ht, hp, -⟩ := sp_fields huv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨k, hk, hik, hv'⟩ := mem_take_UL hv
    refine ⟨sp_UK (threadUnits_all 0 _ (fun a ha p => actUnits_UK (hoth k hk (by omega) a ha) k p)
      v hv') huv, fun h => ?_⟩
    rw [ht, mem_threadUnits_tid hv'] at h; omega
  · refine ⟨sp_UK (threadUnits_all 0 _ (fun a ha p => actUnits_UK (h1 a ha) i p) v hv) huv,
      fun _ => ?_⟩
    rw [hp]; have := mem_threadUnits_pos hv; omega

/-- The kept units after the fragment. -/
theorem partC {trs : List XTrace} {i : Nat} {a3 : List XAct} {cs : List (Nat × Nat)} {q : Nat}
    (hoth : ∀ k (hk : k < trs.length), k ≠ i → ∀ a ∈ (trs[k]).acts, ActAvoid cs a)
    (h3 : ∀ a ∈ a3, ActAvoid cs a) (hl3 : ∀ a ∈ a3, a.ev.locked = true → a.ev.kind = .rmw) :
    ∀ u ∈ (threadUnits i q a3 ++ ((UL trs).drop (i + 1)).flatten).flatMap (sp (accUnits trs)),
      UK cs u ∧ (u.1.tid = i → q ≤ u.1.pos) ∧
        (u.1.tid = i → u.1.isW = true → u.1.locked = true → q < u.1.pos) := by
  intro u hu
  obtain ⟨v, hv, huv⟩ := mem_sp_flatMap hu
  obtain ⟨ht, hp, hact, hlk, -⟩ := sp_fields huv
  rcases List.mem_append.mp hv with hv | hv
  · refine ⟨sp_UK (threadUnits_all _ _ (fun a ha p => actUnits_UK (h3 a ha) i p) v hv) huv,
      fun _ => ?_, fun _ hW hL => ?_⟩
    · rw [hp]; exact (mem_threadUnits_pos hv).1
    · rw [hp]
      exact threadUnits_lockW i q a3 hl3 v hv (by rw [← sp_isW huv]; exact hW) (by rw [← hlk]; exact hL)
  · obtain ⟨k, hk, hik, hv'⟩ := mem_drop_UL hv
    have hK := sp_UK (threadUnits_all 0 _ (fun a ha p => actUnits_UK (hoth k hk (by omega) a ha) k p)
      v hv') huv
    have hne : u.1.tid ≠ i := by rw [ht, mem_threadUnits_tid hv']; omega
    exact ⟨hK, fun h => absurd h hne, fun h => absurd h hne⟩

/-! ## Traces of a behaviour -/

theorem traces_get (P : Prog) (dom : List Nat) (k : Nat) (hk : k < (P.traces dom).length) :
    (P.traces dom)[k] = (run dom (P.threads[k]'(by simpa [Prog.traces] using hk)).body
      Regs.zero).map ((P.threads[k]'(by simpa [Prog.traces] using hk)).xtrace k) := by
  simp [Prog.traces]

theorem length_traces (P : Prog) (dom : List Nat) : (P.traces dom).length = P.threads.length := by
  simp [Prog.traces]

/-- Each chosen trace is a run of its thread. -/
theorem trace_run {P : Prog} {dom : List Nat} {trs : List XTrace}
    (hF : List.Forall₂ (· ∈ ·) trs (P.traces dom)) (k : Nat) (hk : k < trs.length) :
    ∃ hk' : k < P.threads.length, ∃ p ∈ run dom (P.threads[k]).body Regs.zero,
      trs[k] = (P.threads[k]).xtrace k p := by
  have hl := hF.length_eq
  rw [length_traces] at hl
  have hk' : k < P.threads.length := by omega
  refine ⟨hk', ?_⟩
  have := (List.forall₂_iff_get.mp hF).2 k hk (by rw [length_traces]; exact hk')
  simp only [List.get_eq_getElem] at this
  rw [traces_get P dom k (by rw [length_traces]; exact hk')] at this
  obtain ⟨p, hp, he⟩ := List.mem_map.mp this
  exact ⟨p, hp, he.symm⟩

/-- The traces of the localised program. -/
theorem forall2_set {P : Prog} {dom dom' : List Nat} (hd : ∀ v ∈ dom, v ∈ dom') {trs : List XTrace}
    (hF : List.Forall₂ (· ∈ ·) trs (P.traces dom)) {i : Nat} (th' : Thread) (t' : XTrace)
    (ht' : ∃ p ∈ run dom' th'.body Regs.zero, t' = th'.xtrace i p) :
    List.Forall₂ (· ∈ ·) (trs.set i t') (Prog.traces ⟨P.locs, P.threads.set i th'⟩ dom') := by
  have hl := hF.length_eq
  rw [length_traces] at hl
  refine List.forall₂_iff_get.mpr ⟨by simp [length_traces, hl], fun k h1 h2 => ?_⟩
  simp only [List.get_eq_getElem]
  have h2' : k < (P.threads.set i th').length := by
    simpa [length_traces] using h2
  rw [traces_get ⟨P.locs, P.threads.set i th'⟩ dom' k h2]
  simp only [List.getElem_set]
  split
  · rename_i hik
    subst hik
    obtain ⟨p, hp, rfl⟩ := ht'
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · rename_i hik
    obtain ⟨hk', p, hp, he⟩ := trace_run hF k (by simpa using h1)
    rw [he]
    exact List.mem_map.mpr ⟨p, run_mono hd _ _ _ hp, rfl⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
