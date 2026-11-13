module

public import Silmaril.X86.Litmus.Extract.Defs
public import Silmaril.X86.MemEvent.Thms
public import Silmaril.X86.Atomic9.Thms

/-!
# Soundness of litmus event extraction

`extract_sound`: every extracted trace replays on `Atomic9.step` (`Replay`). The pieces:

* `fetch_spec`: what `Thread.fetch` checked (the listing law's hypotheses);
* `inert_sound`: an inert instruction (only fence events) runs on any memory with the
  thread's regions exactly as on the regions-only `Thread.frame`, leaving memory equal (the
  `atomic9_local` locality lemma, with an empty read and write set);
* `memStep_sound`: the litmus memory forms, by unfolding `Atomic9.exec` to `loadN`/`storeN`;
* `explore_sound`: induction on the fuel.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Sz Mem RM leBytes leValue Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.MemEvent (Event Kind)
open Silmaril.X86.Litmus

/-! ## Memories -/

theorem memory_ext {m m' : Memory} (hr : m.regions = m'.regions)
    (hb : ∀ a : Nat, m.bytes[a]? = m'.bytes[a]?) : m = m' := by
  cases m; cases m'
  simp only at hr hb
  subst hr
  congr
  exact Std.ExtHashMap.ext_getElem? hb

theorem checkSpan_regions {m m' : Memory} (h : m.regions = m'.regions)
    (acc : Silmaril.Process.Access) (a k : Nat) : m.checkSpan acc a k = m'.checkSpan acc a k := by
  simp [Memory.checkSpan, Memory.permits, h]

/-! ## Fetch -/

theorem fetch_spec {t : Thread} {s : State} {i : Atomic9.Instr} {n : Nat}
    (h : t.fetch s = some (i, n)) :
    s.rip = t.base + BitVec.ofNat 64 (s.rip - t.base).toNat ∧
      (s.rip - t.base).toNat + n ≤ t.code.length ∧
      Atomic9.decode ((t.code.drop (s.rip - t.base).toNat).take n) = some (i, n) := by
  unfold Thread.fetch at h
  dsimp only at h
  refine ⟨?_, ?_⟩
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

/-! ## Applying writes -/

theorem applyWrites_inert (m : Memory) (es : List Event) (h : es.all Litmus.Event.inert = true) :
    applyWrites m (es.map Act.inert) = some m := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, applyWrites, Act.inert]
    have hw : e.kind.writes = false := by
      have := h.1; simp [Litmus.Event.inert] at this; exact this.2
    simp [hw, ih h.2]

/-! ## Inert instructions -/

/-- **An inert instruction does not depend on memory.** -/
theorem inert_sound {t : Thread} {i : Atomic9.Instr} {s c : State} {n : Nat} {m₀ : Memory}
    (hin : (MemEvent.atomic9Accesses i s n).all Litmus.Event.inert = true)
    (hx : Atomic9.exec i s t.frame n = .ok c m₀) (m : Memory) (hR : m.regions = t.regions) :
    Atomic9.exec i s m n = .ok c m := by
  have hl := MemEvent.atomic9_local i s n
  have hag : MemEvent.Agree (MemEvent.readSet (MemEvent.atomic9Accesses i s n)) t.frame m := by
    refine ⟨hR.symm, ?_⟩
    rintro a ⟨e, he, hr, -⟩
    have := List.all_eq_true.mp hin e he
    simp [Litmus.Event.inert, hr] at this
  have hnw : ∀ a, ¬ MemEvent.writeSet (MemEvent.atomic9Accesses i s n) a := by
    rintro a ⟨e, he, hw, -⟩
    have := List.all_eq_true.mp hin e he
    simp [Litmus.Event.inert, hw] at this
  have hrel := hl.congr t.frame m hag
  rw [hx] at hrel
  revert hrel
  cases hm : Atomic9.exec i s m n <;> simp [MemEvent.extView, MemEvent.Rel]
  rename_i c' m₁
  intro hc hp
  subst hc
  exact ⟨rfl, memory_ext hp.regions' (fun a => hp.outside' a (hnw a))⟩

/-! ## Memory forms -/

/-- What a memory form's branch satisfies. -/
def Good (m : Memory) (i : Atomic9.Instr) (s : State) (n : Nat) (o : List Act × State) : Prop :=
  Answers m o.1 → ∃ m', Atomic9.exec i s m n = .ok o.2 m' ∧ applyWrites m o.1 = some m'

theorem writeBytes_of_ok {R : List Region} {m : Memory} (hR : m.regions = R) {a : Nat}
    {bs : List Byte} (h : writeOk R a bs.length = true) :
    ∃ m', m.writeBytes a bs = some m' := by
  unfold writeOk at h
  rw [← hR, ← checkSpan_regions (m := m) (m' := ⟨m.regions, ∅⟩) rfl] at h
  exact ⟨{ m with bytes := Memory.install m.bytes a bs }, by simp [Memory.writeBytes, h]⟩

theorem loadN_of_read {m : Memory} {a : Word} {k : Nat} {bs : List Byte}
    (h : m.readBytes a.toNat k = some bs) :
    Silmaril.X86.Ext.loadN m a k = some (ldVal bs) := by
  simp [Silmaril.X86.Ext.loadN, h, ldVal]

theorem storeStep_sound {R : List Region} {m : Memory} (hR : m.regions = R) {sz : Sz} {a : Mem}
    {v : Word} {s : State} {next : Word} {outs : List (List Act × State)}
    (h : storeStep R sz a v s next = some outs) {o : List Act × State} (ho : o ∈ outs) :
    ∃ m', Silmaril.X86.Ext.storeN m (a.addr s next) sz.bytes v = some m' ∧
      applyWrites m o.1 = some m' ∧ o.2 = { s with rip := next } := by
  unfold storeStep at h
  dsimp only at h
  split at h
  · rename_i hw
    cases h
    simp only [List.mem_singleton] at ho
    subst ho
    have hw' : writeOk R (a.addr s next).toNat (leBytes v sz.bytes).length = true := by
      simpa using hw
    obtain ⟨m', hm'⟩ := writeBytes_of_ok hR hw'
    exact ⟨m', hm', by simp [applyWrites, MemEvent.Kind.writes, hm'], rfl⟩
  · cases h

theorem store8Step_sound {R : List Region} {m : Memory} (hR : m.regions = R) {a : Mem}
    {v : Word} {s : State} {next : Word} {outs : List (List Act × State)}
    (h : store8Step R a v s next = some outs) {o : List Act × State} (ho : o ∈ outs) :
    ∃ m', Silmaril.X86.Ext.storeN m (a.addr s next) 1 v = some m' ∧
      applyWrites m o.1 = some m' ∧ o.2 = { s with rip := next } := by
  unfold store8Step at h
  dsimp only at h
  split at h
  · rename_i hw
    cases h
    simp only [List.mem_singleton] at ho
    subst ho
    have hw' : writeOk R (a.addr s next).toNat (leBytes v 1).length = true := by
      simpa using hw
    obtain ⟨m', hm'⟩ := writeBytes_of_ok hR hw'
    exact ⟨m', hm', by simp [applyWrites, MemEvent.Kind.writes, hm'], rfl⟩
  · cases h

theorem rmwStep_sound {R : List Region} {dom : List Nat} {m : Memory} (hR : m.regions = R)
    {sz : Sz} {lk : Bool} {a : Mem} {s : State} {next : Word}
    {f : BitVec sz.bits → Word × State} {outs : List (List Act × State)}
    (h : rmwStep R dom sz lk a s next f = some outs) {o : List Act × State} (ho : o ∈ outs)
    (hans : Answers m o.1) :
    ∃ x m', Silmaril.X86.Ext.loadN m (a.addr s next) sz.bytes = some x ∧
      Silmaril.X86.Ext.storeN m (a.addr s next) sz.bytes (f (x.setWidth sz.bits)).1 = some m' ∧
      applyWrites m o.1 = some m' ∧ o.2 = { (f (x.setWidth sz.bits)).2 with rip := next } := by
  unfold rmwStep at h
  dsimp only at h
  split at h
  · rename_i hw
    cases h
    simp only [List.mem_map] at ho
    obtain ⟨v, -, rfl⟩ := ho
    have hr := hans _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
    have hw' : writeOk R (a.addr s next).toNat
        (leBytes (f ((ldVal (valBytes v sz.bytes)).setWidth sz.bits)).1 sz.bytes).length =
          true := by simp only [Bool.and_eq_true] at hw; simpa using hw.2
    obtain ⟨m', hm'⟩ := writeBytes_of_ok hR hw'
    exact ⟨_, m', loadN_of_read hr, hm', by simp [applyWrites, MemEvent.Kind.writes, hm'], rfl⟩
  · cases h

theorem memStep_sound {R : List Region} {dom : List Nat} {m : Memory} (hR : m.regions = R)
    {i : Atomic9.Instr} {s : State} {n : Nat} {outs : List (List Act × State)}
    (h : memStep R dom i s n = some outs) {o : List Act × State} (ho : o ∈ outs) :
    Good m i s n o := by
  intro hans
  unfold memStep at h
  dsimp only at h
  split at h
  · obtain ⟨m', hst, hap, ho2⟩ := storeStep_sound hR h ho
    refine ⟨m', ?_, hap⟩
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.writeRM, hst, Silmaril.X86.Ext.retire, ho2]
  · obtain ⟨m', hst, hap, ho2⟩ := storeStep_sound hR h ho
    refine ⟨m', ?_, hap⟩
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.writeRM, hst, Silmaril.X86.Ext.retire, ho2]
  · rename_i sz dst a
    split at h
    swap
    · cases h
    cases h
    simp only [List.mem_map] at ho
    obtain ⟨v, -, rfl⟩ := ho
    have hr := hans _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
    refine ⟨m, ?_, by simp [applyWrites, MemEvent.Kind.writes]⟩
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.readRM, loadN_of_read hr, Silmaril.X86.Ext.retire]
  · obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only at hst ho2
    simp [Atomic9.exec, Atomic9.execNew, Atomic9.xaddStep, Silmaril.X86.Ext.readRM, hl,
      Silmaril.X86.Ext.retire, ho2, hst]
  · obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only at hst ho2
    simp [Atomic9.exec, Atomic9.execNew, Atomic9.xchgStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, hl, Silmaril.X86.Ext.retire, ho2, hst]
  · obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only [Atomic9.exec, Atomic9.execNew, Atomic9.cmpxchgStep, Silmaril.X86.Ext.readRM, hl,
      Option.map_some] at hst ⊢
    split at hst
    · simp_all [Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.retire]
    · simp_all [Silmaril.X86.Ext.retire]
  · split at h
    swap
    · cases h
    cases h
    simp only [List.mem_map] at ho
    obtain ⟨v, -, rfl⟩ := ho
    have hr := hans _ (List.mem_singleton_self _) (by simp [MemEvent.Kind.reads])
    refine ⟨m, ?_, by simp [applyWrites, MemEvent.Kind.writes]⟩
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.readNarrow, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
      loadN_of_read hr, Silmaril.X86.Ext.retire]
  · obtain ⟨m', hst, hap, ho2⟩ := store8Step_sound hR h ho
    refine ⟨m', ?_, hap⟩
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.writeRM8, hst, Silmaril.X86.Ext.retire, ho2]
  · obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only at hst ho2
    simp [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
      Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, hl, Silmaril.X86.Ext.retire, ho2, hst]
  · obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only at hst ho2
    simp [Atomic9.exec, Atomic9.execNew, Atomic9.incDecStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, hl, Silmaril.X86.Ext.retire, ho2, hst]
  · split at h
    · cases h
    rename_i hop
    obtain ⟨x, m', hl, hst, hap, ho2⟩ := rmwStep_sound hR h ho hans
    refine ⟨m', ?_, hap⟩
    simp only at hst ho2
    simp [Atomic9.exec, Atomic9.execNew, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.readRM,
      Silmaril.X86.Ext.writeRM, hl, hop, Silmaril.X86.Ext.retire, ho2, hst]
  · cases h

/-! ## The actions are the events -/

theorem memStep_events {R : List Region} {dom : List Nat} {i : Atomic9.Instr} {s : State}
    {n : Nat} {outs : List (List Act × State)} (h : memStep R dom i s n = some outs)
    {o : List Act × State} (ho : o ∈ outs) :
    o.1.map Act.ev = MemEvent.atomic9Accesses i s n := by
  unfold memStep at h
  dsimp only at h
  split at h <;>
  first
  | (cases h)
  | (unfold storeStep at h; dsimp only at h; split at h
     · cases h; simp only [List.mem_singleton] at ho; subst ho
       simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
         MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv]
     · cases h)
  | (unfold rmwStep at h; dsimp only at h; split at h
     · cases h; simp only [List.mem_map] at ho; obtain ⟨v, -, rfl⟩ := ho
       simp [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses, MemEvent.rmEv,
         MemEvent.memEv, Atomic9.tag, Atomic9.RM.isMem]
     · cases h)
  | (unfold store8Step at h; dsimp only at h; split at h
     · cases h; simp only [List.mem_singleton] at ho; subst ho
       simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
         MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv]
     · cases h)
  | (unfold rmwStep at h; dsimp only at h; split at h
     · cases h; simp only [List.mem_map] at ho; obtain ⟨v, -, rfl⟩ := ho
       simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
         MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv]
     · cases h)
  | (split at h
     · cases h
     · rename_i hop
       unfold rmwStep at h; dsimp only at h; split at h
       · cases h; simp only [List.mem_map] at ho; obtain ⟨v, -, rfl⟩ := ho
         simp [MemEvent.atomic9Accesses, MemEvent.atomic9NewAccesses, MemEvent.memEv,
           MemEvent.aluKind, hop, Atomic9.tag]
       · cases h)
  | (split at h
     · cases h; simp only [List.mem_map] at ho; obtain ⟨v, -, rfl⟩ := ho
       simp [MemEvent.atomic9Accesses, MemEvent.ext9Accesses, MemEvent.ext8Accesses,
         MemEvent.extAccesses, MemEvent.rmEv, MemEvent.memEv]
     · cases h)

/-- **The actions of a symbolic step are exactly the access list** of the instruction at
`rip` (`MemEvent.atomic9Accesses`), with its kinds, addresses, sizes and `locked` tags. -/
theorem stepSym_events {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {o : List Act × State} (ho : o ∈ outs) :
    ∃ i n, t.fetch s = some (i, n) ∧ o.1.map Act.ev = MemEvent.atomic9Accesses i s n := by
  unfold stepSym at h
  split at h
  · cases h
  · rename_i i n hf
    refine ⟨i, n, hf, ?_⟩
    dsimp only at h
    split at h
    · split at h
      · cases h
        simp only [List.mem_singleton] at ho
        subst ho
        have e : Act.ev ∘ Act.inert = id := rfl
        simp [e]
      · cases h
    · exact memStep_events h ho

/-! ## One symbolic step -/

/-- **A symbolic step is sound**: each branch is one `Atomic9.step` on every memory with the
thread's regions and code that answers the branch's reads. -/
theorem stepSym_sound {t : Thread} {dom : List Nat} {s : State} {outs : List (List Act × State)}
    (h : stepSym t dom s = some outs) {o : List Act × State} (ho : o ∈ outs) (m : Memory)
    (hR : m.regions = t.regions) (hl : Loaded m t.base t.code) (hans : Answers m o.1) :
    ∃ m', Atomic9.step ⟨s, m⟩ = some ⟨o.2, m'⟩ ∧ applyWrites m o.1 = some m' := by
  unfold stepSym at h
  split at h
  · cases h
  · rename_i i n hf
    obtain ⟨hrip, hfit, hdec⟩ := fetch_spec hf
    dsimp only at h
    split at h
    · rename_i hin
      split at h
      · rename_i c m₀ hx
        cases h
        simp only [List.mem_singleton] at ho
        subst ho
        exact ⟨m, Atomic9.step_of_listed (m := ⟨s, m⟩) hl hrip hfit hdec
          (inert_sound hin hx m hR), applyWrites_inert m _ hin⟩
      · cases h
    · obtain ⟨m', hx, hap⟩ := memStep_sound hR h ho hans
      exact ⟨m', Atomic9.step_of_listed (m := ⟨s, m⟩) hl hrip hfit hdec hx, hap⟩

/-! ## Exploration -/

theorem mapM_mem {α β : Type} {f : α → Option (List β)} :
    ∀ {l : List α} {rss : List (List β)}, l.mapM f = some rss → ∀ {y : β}, y ∈ rss.flatten →
      ∃ x ∈ l, ∃ ys, f x = some ys ∧ y ∈ ys
  | [], rss, h, y, hy => by
    simp at h; subst h; simp at hy
  | x :: l, rss, h, y, hy => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, hx, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨x, by simp, ys, hx, hy⟩
    · obtain ⟨x', hx', ys', h', hy'⟩ := mapM_mem hl hy
      exact ⟨x', by simp [hx'], ys', h', hy'⟩

/-- **Exploration is sound.** -/
theorem explore_sound {t : Thread} {dom : List Nat} :
    ∀ (fuel : Nat) {s : State} {trs : List Trace}, explore t dom fuel s = some trs →
      ∀ tr ∈ trs, Replay t s tr.steps tr.final := by
  intro fuel
  induction fuel with
  | zero =>
    intro s trs h tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · cases h
  | succ f ih =>
    intro s trs h tr htr
    unfold explore at h
    split at h
    · rename_i he
      cases h
      simp only [List.mem_singleton] at htr
      subst htr
      exact .done s he
    · dsimp only at h
      split at h
      · cases h
      · rename_i outs hs
        obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨o, ho, ys, hys, hy⟩ := mapM_mem hm htr
        obtain ⟨trs', he, rfl⟩ := Option.map_eq_some_iff.mp hys
        simp only [consStep, List.mem_map] at hy
        obtain ⟨tr', htr', rfl⟩ := hy
        exact .step s ⟨o.1, o.2⟩ tr'.steps tr'.final
          (fun m hR hl hans => stepSym_sound hs ho m hR hl hans) (ih he tr' htr')

/-- **Extraction is sound.** -/
theorem extract_sound {t : Thread} {dom : List Nat} {fuel : Nat} {trs : List Trace}
    (h : extract t dom fuel = some trs) : ∀ tr ∈ trs, Replay t t.init tr.steps tr.final :=
  explore_sound fuel h

/-- **A replayed trace runs solo**: on a memory sequence with no interference, the machine
reaches the final core with the trace's writes applied. -/
theorem Replay.reaches {t : Thread} {s s' : State} {steps : List StepRec}
    (h : Replay t s steps s') :
    ∀ {m m' : Memory}, Solo t m steps m' →
      Silmaril.Machine.Execution.Reaches Atomic9.step ⟨s, m⟩ ⟨s', m'⟩ := by
  induction h with
  | done s _ =>
    intro m m' hs
    cases hs
    exact .refl _ _
  | step s r rest s' hstep _ ih =>
    intro m m'' hs
    obtain ⟨hR, hl, hans, m', hap, hrest⟩ := hs
    obtain ⟨m₁, hst, hap₁⟩ := hstep m hR hl hans
    rw [hap] at hap₁
    cases hap₁
    obtain ⟨k, hk⟩ := ih hrest
    exact ⟨k + 1, by simp [Silmaril.Machine.Execution.run, hst, hk]⟩

/-! ## Non-vacuity -/

theorem loaded_install {t : Thread} {bm : Silmaril.Process.ByteMemory}
    (hx : t.frame.checkSpan .execute t.base.toNat t.code.length = true) :
    Loaded ⟨t.regions, Memory.install bm t.base.toNat t.code⟩ t.base t.code := by
  unfold Loaded Memory.fetchBytes
  refine Memory.readWith_eq _ _ _ _ ?_ ?_
  · exact (checkSpan_regions (m' := t.frame) rfl _ _ _).trans hx
  · intro i hi; exact Memory.install_get _ _ _ _ hi

/-- **The replay hypothesis of a `placed` step is satisfiable.** -/
theorem placed_satisfiable {t : Thread} {acts : List Act} (h : t.placed acts = true) :
    ∃ m : Memory, m.regions = t.regions ∧ Loaded m t.base t.code ∧ Answers m acts := by
  unfold Thread.placed at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hx, h⟩ := h
  split at h
  · rename_i hf
    refine ⟨⟨t.regions, Memory.install ∅ t.base.toNat t.code⟩, rfl, loaded_install hx, ?_⟩
    intro a ha hr
    have : a ∈ acts.filter (fun a => a.ev.kind.reads) := List.mem_filter.mpr ⟨ha, by simp [hr]⟩
    simp [hf] at this
  · rename_i a hf
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hsz⟩, hdisj⟩ := h
    refine ⟨⟨t.regions, Memory.install (Memory.install ∅ a.ev.addr a.rd) t.base.toNat t.code⟩,
      rfl, loaded_install hx, ?_⟩
    intro a' ha' hr'
    have : a' ∈ acts.filter (fun a => a.ev.kind.reads) := List.mem_filter.mpr ⟨ha', by simp [hr']⟩
    rw [hf, List.mem_singleton] at this
    subst this
    rw [← hsz]
    refine Memory.readWith_eq _ _ _ _ ?_ ?_
    · exact (checkSpan_regions (m' := t.frame) rfl _ _ _).trans hr
    · intro i hi
      simp only
      rw [Memory.install_outside _ _ _ _ (by omega)]
      exact Memory.install_get _ _ _ _ hi
  · cases h

/-- **Non-vacuity of `Replay`**: if every step of the extracted traces is `placed`, then at
every step some memory satisfies the replay hypothesis. -/
theorem allPlaced_satisfiable {t : Thread} {trs : List Trace} (h : t.allPlaced trs = true) :
    ∀ tr ∈ trs, ∀ r ∈ tr.steps,
      ∃ m : Memory, m.regions = t.regions ∧ Loaded m t.base t.code ∧ Answers m r.acts := by
  intro tr htr r hr
  unfold Thread.allPlaced at h
  exact placed_satisfiable (List.all_eq_true.mp (List.all_eq_true.mp h tr htr) r hr)

end Silmaril.Proofs.X86.Litmus
