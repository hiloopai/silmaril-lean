module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Litmus.Complete.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Thms

/-!
# The front ends against the real step: proofs

`xstep_of_step` (header `Silmaril.X86.Concurrency.Bridge.Thms`). The pieces:

* `memStep_dom`, `stepSym_dom`: whether the symbolic step is defined does not depend on the
  value domain (each read form maps over the domain, its guard does not look at it);
* `memStep_reads`, `stepSym_reads`: the reads of a defined step are read-permitted by the
  regions and at most 8 bytes (case split over `memStep`'s forms; inert steps read nothing);
* `readBytes_of_backed`, `domReads_readVals`: on a backed memory those reads succeed, and the
  domain of the values they return covers them (`leBytes_leValue`);
* `xstep_of_step`: so `stepSym_complete` applies, and the real step is a branch;
* `xrun_of_a9run`, `frun_of_a9frun`: induction on the run.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemEvent (Event Kind)
open Silmaril.X86.Litmus
open Silmaril.X86.Concurrency.Bridge

theorem memStep_dom {R : List Region} {dom : List Nat} {i : Atomic9.Instr} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : memStep R dom i s n = some outs) (dom' : List Nat) :
    ∃ outs', memStep R dom' i s n = some outs' := by
  unfold memStep at h ⊢
  dsimp only at h ⊢
  split at h <;> simp_all [storeStep, store8Step, rmwStep]

theorem stepSym_dom {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) (dom' : List Nat) :
    ∃ outs', stepSym t dom' s = some outs' := by
  unfold stepSym at h ⊢
  split at h
  · cases h
  · rename_i i n hf
    dsimp only at h ⊢
    split at h
    · rename_i hin
      simp only [hin, ↓reduceIte]
      split at h
      · exact ⟨_, rfl⟩
      · cases h
    · rename_i hin
      simp only [hin, Bool.false_eq_true, ↓reduceIte]
      exact memStep_dom h dom'

theorem sz_bytes_le (sz : Sz) : sz.bytes ≤ 8 := by cases sz <;> decide

/-- The reads of an accepted memory form are at most 8 bytes and read-permitted. -/
theorem memStep_reads {R : List Region} {dom : List Nat} {i : Atomic9.Instr} {s : State} {n : Nat}
    {outs : List (List Act × State)} (h : memStep R dom i s n = some outs) :
    ∀ e ∈ MemEvent.atomic9Accesses i s n, e.kind.reads = true →
      e.size ≤ 8 ∧ readOk R e.addr e.size = true := by
  unfold memStep at h
  dsimp only at h
  intro e he hr
  split at h
  all_goals first
    | (simp at h; done)
    | (simp only [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses,
        MemEvent.ext9Accesses, MemEvent.ext8Accesses, MemEvent.extAccesses, MemEvent.rmEv,
        MemEvent.memEv, MemEvent.aluKind, Atomic9.tag, Atomic9.RM.isMem, List.mem_cons,
        List.mem_nil_iff, or_false] at he
       subst he
       simp_all [MemEvent.Kind.reads, storeStep, store8Step, rmwStep, sz_bytes_le])

/-- The reads of a symbolic step are at most 8 bytes and read-permitted. -/
theorem stepSym_reads {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {i : Atomic9.Instr} {n : Nat} (hf : t.fetch s = some (i, n)) :
    ∀ e ∈ MemEvent.atomic9Accesses i s n, e.kind.reads = true →
      e.size ≤ 8 ∧ readOk t.regions e.addr e.size = true := by
  intro e he hr
  unfold stepSym at h
  rw [hf] at h
  dsimp only at h
  split at h
  · rename_i hin
    have := List.all_eq_true.mp hin e he
    simp [Litmus.Event.inert] at this
    rw [this.1] at hr
    cases hr
  · exact memStep_reads h e he hr

/-- On a backed memory, a read-permitted span reads. -/
theorem readBacking_of_backed {m : Memory} (hb : Backed m) :
    ∀ (k a : Nat), (∀ j < k, m.permits .read (a + j) = true) →
      ∃ bs, Memory.readBacking m.bytes a k = some bs
  | 0, a, _ => ⟨[], rfl⟩
  | k + 1, a, hp => by
    obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.mp (hb a (by simpa using hp 0 (by omega)))
    obtain ⟨bs, hbs⟩ := readBacking_of_backed hb k (a + 1) fun j hj => by
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hp (j + 1) (by omega)
    have hb'' : m.bytes[a]? = some b := hb'
    exact ⟨b :: bs, by simp [Memory.readBacking, hb'', hbs]⟩

theorem readBytes_of_backed {m : Memory} (hb : Backed m) {a k : Nat}
    (hok : m.checkSpan .read a k = true) : ∃ bs, m.readBytes a k = some bs := by
  have h' := hok
  rw [Memory.checkSpan_iff] at h'
  obtain ⟨bs, hbs⟩ := readBacking_of_backed hb k a h'.2.2
  exact ⟨bs, by simp [Memory.readBytes, Memory.readWith, hok, hbs]⟩

/-- The values a memory returns for the reads of an access list. -/
def readVals (m : Memory) (es : List Event) : List Nat :=
  es.map fun e => leValue ((m.readBytes e.addr e.size).getD [])

theorem domReads_readVals {m : Memory} {es : List Event}
    (h : ∀ e ∈ es, e.kind.reads = true → e.size ≤ 8 ∧ m.checkSpan .read e.addr e.size = true)
    (hb : Backed m) : DomReads (readVals m es) m es := by
  intro e he hr
  obtain ⟨hsz, hok⟩ := h e he hr
  obtain ⟨bs, hbs⟩ := readBytes_of_backed hb hok
  have hlen : bs.length = e.size := Memory.readWith_length hbs
  refine ⟨leValue bs, List.mem_map.mpr ⟨e, he, by simp [hbs]⟩, ?_⟩
  rw [hbs, valBytes, ← hlen, Silmaril.X86.Ext.leBytes_leValue bs (by omega)]

/-- **A real step where the symbolic step is defined is a symbolic step** (gap 2, step level):
on a backed memory with the thread's regions and code, `Atomic9.step` from `s` goes to one of
the branches of `stepSym` (over the domain of the values it reads), whose reads the memory
answers and whose writes are the step's. -/
theorem xstep_of_step {t : Thread} {dom₀ : List Nat} {s : State}
    {outs₀ : List (List Act × State)} (hsym : stepSym t dom₀ s = some outs₀) {m : Memory}
    {s' : State} {m' : Memory} (hR : m.regions = t.regions) (hl : Loaded m t.base t.code)
    (hb : Backed m) (hs : Atomic9.step ⟨s, m⟩ = some ⟨s', m'⟩) :
    ∃ dom outs acts, stepSym t dom s = some outs ∧ (acts, s') ∈ outs ∧ Answers m acts ∧
      applyWrites m acts = some m' := by
  let es : List Event := match t.fetch s with
    | some (i, n) => MemEvent.atomic9Accesses i s n
    | none => []
  obtain ⟨outs, ho⟩ := stepSym_dom hsym (readVals m es)
  have hd : ∀ i n, t.fetch s = some (i, n) →
      DomReads (readVals m es) m (MemEvent.atomic9Accesses i s n) := by
    intro i n hf
    have hes : es = MemEvent.atomic9Accesses i s n := by simp only [es, hf]
    rw [← hes]
    refine domReads_readVals (fun e he hr => ?_) hb
    rw [hes] at he
    obtain ⟨h1, h2⟩ := stepSym_reads hsym hf e he hr
    refine ⟨h1, ?_⟩
    simpa [readOk, Memory.checkSpan, Memory.permits, hR] using h2
  obtain ⟨o, hmem, hpost, hans, hap⟩ :=
    stepSym_complete ho (q := ⟨m, s', m'⟩) hR hl hd hs
  have hpost' : o.2 = s' := hpost
  exact ⟨_, outs, o.1, ho, by rw [← hpost']; exact hmem, hans, hap⟩

/-! ## Runs -/

open Silmaril.X86.Concurrency.Cir.Tv (XThread)
open Silmaril.X86.Concurrency.Cir.TvCfg (XStep XRun)
open Silmaril.X86.Concurrency.Cir.TvCfg.Fx (FStep FRun)
open Silmaril.X86.MemoryModel.Litmus (XAct)

/-- A real run is an `XRun` when the symbolic step is defined at every unfinished core an
`XRun` reaches. -/
theorem xrun_of_a9run {t : XThread} {s : State} {run : List SeqStep} {s' : State}
    (hr : A9Run t s run s') :
    (∀ acc s₁, XRun t s acc s₁ → s₁.rip ≠ t.endRip → ∀ (m : Memory) (s₂ : State) (m₂ : Memory),
      m.regions = t.regions → Loaded m t.base t.code →
      Atomic9.step ⟨s₁, m⟩ = some ⟨s₂, m₂⟩ → SymDefined t s₁) →
    ∃ acc, XRun t s acc s' ∧ List.Forall₂ ActsOk acc run := by
  induction hr with
  | nil s => exact fun _ => ⟨[], .nil, .nil⟩
  | cons s q rest s' hne hR hl hb hs _ ih =>
    intro hD
    obtain ⟨dom₀, outs₀, hsym⟩ := hD [] s .nil hne q.pre q.post q.mem hR hl hs
    obtain ⟨dom, outs, acts, ho, hmem, hans, hap⟩ := xstep_of_step hsym hR hl hb hs
    have hx : XStep t s acts q.post := ⟨dom, outs, ho, hmem⟩
    obtain ⟨acc, hrun, hok⟩ := ih fun acc s₁ hr' => hD (acts :: acc) s₁ (.cons hx hr')
    exact ⟨acts :: acc, .cons hx hrun, .cons ⟨hans, hap⟩ hok⟩

/-- A real futex-thread run is an `FRun` when the symbolic step is defined at every core an
`FRun` reaches that has not returned and is not at a `syscall`. -/
theorem frun_of_a9frun {t : XThread} {s : State} {run : List FObs} {s' : State}
    (hr : A9FRun t s run s') :
    (∀ acc s₁, FRun t s acc s₁ → ¬ Silmaril.X86.Concurrency.Cir.TvCfg.Fx.Returned t s₁ →
      Silmaril.X86.Concurrency.Cir.TvCfg.Fx.isSysAt t (s₁.rip - t.base).toNat = false →
      ∀ (m : Memory) (s₂ : State) (m₂ : Memory),
      m.regions = t.regions → Loaded m t.base t.code →
      Atomic9.step ⟨s₁, m⟩ = some ⟨s₂, m₂⟩ → SymDefined t s₁) →
    ∃ acc, FRun t s acc s' ∧ List.Forall₂ FObs.Ok acc run := by
  induction hr with
  | nil s => exact fun _ => ⟨[], .nil, .nil⟩
  | mach s q rest s' hne hsys hR hl hb hs _ ih =>
    intro hD
    obtain ⟨dom₀, outs₀, hsym⟩ := hD [] s .nil hne hsys q.pre q.post q.mem hR hl hs
    obtain ⟨dom, outs, acts, ho, hmem, hans, hap⟩ := xstep_of_step hsym hR hl hb hs
    have hx : FStep t s acts q.post := .inl ⟨dom, outs, ho, hmem⟩
    obtain ⟨acc, hrun, hok⟩ := ih fun acc s₁ hr' => hD (acts :: acc) s₁ (.cons hx hr')
    exact ⟨acts :: acc, .cons hx hrun, .cons ⟨hans, hap⟩ hok⟩
  | sys s acts s₁ rest s' h _ ih =>
    intro hD
    have hx : FStep t s acts s₁ := .inr h
    obtain ⟨acc, hrun, hok⟩ := ih fun acc s₂ hr' => hD (acts :: acc) s₂ (.cons hx hr')
    exact ⟨acts :: acc, .cons hx hrun, .cons rfl hok⟩

end Silmaril.Proofs.X86.Concurrency.Bridge
