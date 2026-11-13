module

public import Silmaril.X86.Litmus.Complete.Defs
public import Silmaril.X86.Litmus.Extract.Thms

/-!
# Completeness of litmus event extraction: proofs

`extract_complete` (header `Silmaril.X86.Litmus.Complete.Thms`). The pieces:

* `memStep_cover`, `stepSym_cover`: when the step's reads return domain values, some branch
  answers them (each read form has one branch per domain value, with exactly those bytes);
* `stepSym_complete`: that branch is the machine's step, because `Atomic9.step` is a function
  and the branch replays (`stepSym_sound`);
* `explore_complete`: induction on the run.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemEvent (Event Kind)
open Silmaril.X86.Litmus

/-! ## Covering branches -/

theorem storeStep_cover {R : List Region} {sz : Sz} {a : Mem} {v : Word} {s : State} {next : Word}
    {outs : List (List Act × State)} (h : storeStep R sz a v s next = some outs) (m : Memory) :
    ∃ o ∈ outs, Answers m o.1 := by
  unfold storeStep at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    intro a ha hr
    simp only [List.mem_singleton] at ha
    subst ha
    simp [MemEvent.Kind.reads] at hr
  · cases h

theorem store8Step_cover {R : List Region} {a : Mem} {v : Word} {s : State} {next : Word}
    {outs : List (List Act × State)} (h : store8Step R a v s next = some outs) (m : Memory) :
    ∃ o ∈ outs, Answers m o.1 := by
  unfold store8Step at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    intro a ha hr
    simp only [List.mem_singleton] at ha
    subst ha
    simp [MemEvent.Kind.reads] at hr
  · cases h

theorem rmwStep_cover {R : List Region} {dom : List Nat} {sz : Sz} {lk : Bool} {a : Mem}
    {s : State} {next : Word} {f : BitVec sz.bits → Word × State}
    {outs : List (List Act × State)} (h : rmwStep R dom sz lk a s next f = some outs)
    {m : Memory}
    (hd : ∃ v ∈ dom, m.readBytes (a.addr s next).toNat sz.bytes = some (valBytes v sz.bytes)) :
    ∃ o ∈ outs, Answers m o.1 := by
  unfold rmwStep at h
  dsimp only at h
  split at h
  · cases h
    obtain ⟨v, hv, hrd⟩ := hd
    refine ⟨_, List.mem_map_of_mem (f := fun v => _) hv, ?_⟩
    intro a' ha' _
    simp only [List.mem_singleton] at ha'
    subst ha'
    exact hrd
  · cases h

/-- A load's branches cover the domain. -/
theorem load_cover {dom : List Nat} {addr k : Nat} {g : Nat → State} {m : Memory}
    (hd : ∃ v ∈ dom, m.readBytes addr k = some (valBytes v k)) :
    ∃ o ∈ dom.map (fun v => ([(⟨⟨.load, addr, k, false⟩, .plain, valBytes v k, []⟩ : Act)], g v)),
      Answers m o.1 := by
  obtain ⟨v, hv, hrd⟩ := hd
  refine ⟨_, List.mem_map_of_mem (f := fun v => _) hv, ?_⟩
  intro a' ha' _
  simp only [List.mem_singleton] at ha'
  subst ha'
  exact hrd

/-- Discharge the read hypothesis of a branch from `DomReads` on the access list. -/
macro "dom_read" hd:ident : tactic => `(tactic|
  (simp only [DomReads, MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
      MemEvent.ext9Accesses, MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv,
      MemEvent.memEv, MemEvent.aluKind, Atomic9.tag, Atomic9.RM.isMem, List.mem_cons,
      List.mem_nil_iff, or_false, forall_eq, MemEvent.Kind.reads, forall_const] at $hd:ident
   simpa using $hd:ident))

/-- **Some branch of a memory form answers the step's reads**, when they return domain
values. -/
theorem memStep_cover {R : List Region} {dom : List Nat} {i : Atomic9.Instr} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : memStep R dom i s n = some outs) {m : Memory}
    (hd : DomReads dom m (MemEvent.atomic9Accesses i s n)) : ∃ o ∈ outs, Answers m o.1 := by
  unfold memStep at h
  dsimp only at h
  split at h
  · exact storeStep_cover h m
  · exact storeStep_cover h m
  · split at h
    · cases h
      exact load_cover (by dom_read hd)
    · cases h
  · exact rmwStep_cover h (by dom_read hd)
  · exact rmwStep_cover h (by dom_read hd)
  · exact rmwStep_cover h (by dom_read hd)
  · split at h
    · cases h
      exact load_cover (by dom_read hd)
    · cases h
  · exact store8Step_cover h m
  · exact rmwStep_cover h (by dom_read hd)
  · exact rmwStep_cover h (by dom_read hd)
  · split at h
    · cases h
    · rename_i hop
      refine rmwStep_cover h ?_
      simp only [DomReads, MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
        MemEvent.memEv, MemEvent.aluKind, hop, Atomic9.tag, List.mem_cons, List.mem_nil_iff,
        or_false, forall_eq, MemEvent.Kind.reads, forall_const, ite_false] at hd
      simpa using hd
  · cases h

/-- **Some branch of a symbolic step answers the step's reads**, when they return domain
values. -/
theorem stepSym_cover {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {m : Memory}
    (hd : ∀ i n, t.fetch s = some (i, n) → DomReads dom m (MemEvent.atomic9Accesses i s n)) :
    ∃ o ∈ outs, Answers m o.1 := by
  unfold stepSym at h
  split at h
  · cases h
  · rename_i i n hf
    dsimp only at h
    split at h
    · rename_i hin
      split at h
      · cases h
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        intro a ha hr
        simp only [List.mem_map] at ha
        obtain ⟨e, he, rfl⟩ := ha
        have := List.all_eq_true.mp hin e he
        simp [Litmus.Event.inert, Act.inert] at this hr
        rw [this.1] at hr
        cases hr
      · cases h
    · exact memStep_cover h (hd i n hf)

/-- **A step of the sequential machine whose reads return domain values is a branch of the
symbolic step.** -/
theorem stepSym_complete {t : Thread} {dom : List Nat} {s : State}
    {outs : List (List Act × State)} (h : stepSym t dom s = some outs) {q : SeqStep}
    (hR : q.pre.regions = t.regions) (hl : Loaded q.pre t.base t.code)
    (hd : ∀ i n, t.fetch s = some (i, n) → DomReads dom q.pre (MemEvent.atomic9Accesses i s n))
    (hs : Atomic9.step ⟨s, q.pre⟩ = some ⟨q.post, q.mem⟩) :
    ∃ o ∈ outs, o.2 = q.post ∧ Answers q.pre o.1 ∧ applyWrites q.pre o.1 = some q.mem := by
  obtain ⟨o, ho, hans⟩ := stepSym_cover h hd
  obtain ⟨m', hst, hap⟩ := stepSym_sound h ho q.pre hR hl hans
  rw [hs] at hst
  simp only [Option.some.injEq, MState.mk.injEq] at hst
  obtain ⟨h1, h2⟩ := hst
  exact ⟨o, ho, h1.symm, hans, by rw [hap, h2]⟩

/-! ## Exploration -/

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {rs : List β}, l.mapM f = some rs → ∀ {x : α}, x ∈ l →
      ∃ y, f x = some y ∧ y ∈ rs
  | [], _, _, _, hx => by simp at hx
  | a :: l, rs, h, x, hx => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hl, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, hy, by simp⟩
    · obtain ⟨y', h', hm⟩ := mapM_some_mem hl hx
      exact ⟨y', h', by simp [hm]⟩

/-- **Exploration is complete** for domain-bounded runs. -/
theorem explore_complete {t : Thread} {dom : List Nat} {s : State} {run : List SeqStep}
    {fin : State} (hr : DomRun t dom s run fin) :
    ∀ {fuel : Nat} {trs : List Trace}, explore t dom fuel s = some trs →
      ∃ tr ∈ trs, tr.Matches run fin := by
  induction hr with
  | done s he =>
    intro fuel trs h
    cases fuel <;>
    · unfold explore at h
      simp only [he, ↓reduceIte] at h
      cases h
      exact ⟨_, List.mem_singleton_self _, rfl, List.Forall₂.nil⟩
  | step s q rest fin hne hR hl hd hs _ ih =>
    intro fuel trs h
    cases fuel with
    | zero =>
      unfold explore at h
      simp only [hne, ↓reduceIte] at h
      cases h
    | succ f =>
      unfold explore at h
      simp only [hne, ↓reduceIte] at h
      split at h
      · cases h
      · rename_i outs hst
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho, hpost, hans, hap⟩ := stepSym_complete hst hR hl hd hs
        obtain ⟨ys, hys, hyr⟩ := mapM_some_mem hm ho
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        rw [hpost] at he
        obtain ⟨tr', htr', hfin, hsteps⟩ := ih he
        refine ⟨⟨⟨o.1, o.2⟩ :: tr'.steps, tr'.final⟩, ?_, hfin, ?_⟩
        · exact List.mem_flatten.mpr ⟨_, hyr, List.mem_map.mpr ⟨tr', htr', rfl⟩⟩
        · exact List.Forall₂.cons ⟨hpost, hans, hap⟩ hsteps

/-- **Extraction is complete** for domain-bounded runs. -/
theorem extract_complete {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : extract t dom fuel = some trs) {run : List SeqStep} {fin : State}
    (hr : DomRun t dom t.init run fin) : ∃ tr ∈ trs, tr.Matches run fin :=
  explore_complete hr h

end Silmaril.Proofs.X86.Litmus
