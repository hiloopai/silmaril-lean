module

public import Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun.Run
public import Silmaril.X86.Litmus.Domain.Thms

/-!
# Gap 1: the cell check on the skeletons

`xrun_skel`: on straight-line code every symbolic run (`XRun`) to the end of the
code has the code's skeleton as its events, whatever the values read (the run form of
`explore_skel`). `CellsP`: the facts the Boolean check `cellsB` gives (`cellsP_of`); with them
`foot_of_actX` and `unit_of_threadUnits` place every footprint of the store-buffer machine events
and every memory
unit of the litmus translation at a skeleton event.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun

open Silmaril.X86 (State Byte Word)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Act stepSym)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test actX threadUnits actUnits)
open Silmaril.X86.Concurrency.Bridge
open Silmaril.X86.Concurrency.Bridge.PoolRun
open Silmaril.X86.Concurrency.Cir.TvCfg (XStep XRun)
open Silmaril.X86.Concurrency.Cir.Tv (XThread)

theorem decode_nil : Atomic9.decode [] = none := by decide

theorem fetch_end {t : XThread} {s : State} (hlen : t.code.length < 2 ^ 64)
    (h : s.rip = t.endRip) : t.fetch s = none := by
  have ho : (s.rip - t.base).toNat = t.code.length := by
    have e : t.base + BitVec.ofNat 64 t.code.length - t.base = BitVec.ofNat 64 t.code.length := by
      bv_omega
    rw [h, Silmaril.X86.Litmus.Thread.endRip, e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [Silmaril.X86.Litmus.Thread.fetch, ho, List.drop_length, List.take_nil,
    decode_nil]

/-- **A symbolic run of straight-line code to its end has the skeleton's events.** -/
theorem xrun_skel {t : XThread} (hlen : t.code.length < 2 ^ 64) {s : State}
    {acc : List (List XAct)} {s' : State} (hx : XRun t s acc s') (he : s'.rip = t.endRip) :
    ∀ {f : Nat} {S : List (List MemEvent.Event)}, t.skelFrom f s.rip = some S →
      acc.map (fun acts => acts.map Act.ev) = S := by
  induction hx with
  | nil =>
    intro f S hS
    unfold Silmaril.X86.Litmus.Thread.skelFrom at hS
    simp only [he, ↓reduceIte, Option.some.injEq] at hS
    exact hS
  | @cons s acts s₁ rest s₂ hst _ ih =>
    intro f S hS
    obtain ⟨dom, outs, hso, hmem⟩ := hst
    have hne : s.rip ≠ t.endRip := fun h => by
      simp [stepSym, fetch_end hlen h] at hso
    obtain ⟨i, n, hf, hev⟩ := Silmaril.X86.Litmus.stepSym_events hso hmem
    unfold Silmaril.X86.Litmus.Thread.skelFrom at hS
    simp only [hne, ↓reduceIte] at hS
    cases f with
    | zero => cases hS
    | succ g =>
      have hf' : t.fetch { t.init with rip := s.rip } = some (i, n) := hf
      simp only [hf'] at hS
      split at hS
      · rename_i hi
        obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.mp hS
        have hpost := Silmaril.X86.Litmus.stepSym_post hso hf hi hmem
        simp only at hpost
        simp only [List.map_cons]
        rw [ih he (by rw [hpost]; exact hS')]
        simp only at hev
        rw [hev]
        exact congrArg (· :: S') (Silmaril.X86.Litmus.straight_events hi (s := s) (s' := { t.init with rip := s.rip }) rfl n)
      · cases hS

/-- What a passing `cellsB` says. -/
structure CellsP (t : Test) (Ss : List (List (List MemEvent.Event))) : Prop where
  skels : testSkels t = some Ss
  sc : ∀ e ∈ memEvs Ss, 0 < e.size ∧ e.size ≤ 8 ∧ e.addr % e.size = 0
  disj : ∀ e ∈ memEvs Ss, ∀ f ∈ memEvs Ss, (e.addr = f.addr ∧ e.size = f.size) ∨
    e.addr + e.size ≤ f.addr ∨ f.addr + f.size ≤ e.addr
  init : ∀ e ∈ memEvs Ss, e.kind.reads = true → ∀ j < e.size, (t.initMem (e.addr + j)).isSome = true

theorem cellsP_of {t : Test} (h : cellsB t = true) : ∃ Ss, CellsP t Ss := by
  unfold cellsB at h
  split at h
  · rename_i Ss hS
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.or_eq_true, Bool.not_eq_true', List.mem_range] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨Ss, hS, fun e he => ?_, fun e he f hf => ?_, fun e he hr j hj => ?_⟩
    · obtain ⟨⟨a, b⟩, c⟩ := h1 e he; exact ⟨a, b, c⟩
    · rcases h2 e he f hf with (⟨a, b⟩ | c) | d
      · exact .inl ⟨a, b⟩
      · exact .inr (.inl c)
      · exact .inr (.inr d)
    · rcases h3 e he with h | h
      · rw [hr] at h; cases h
      · exact h j hj
  · cases h

/-- The skeleton of thread `k`. -/
theorem skel_get {t : Test} {Ss : List (List (List MemEvent.Event))} (h : testSkels t = some Ss)
    {k : Nat} {th : Silmaril.X86.MemoryModel.Litmus.Thread} (hth : t.threads[k]? = some th) :
    ∃ S ∈ Ss, (t.xthread k th).skel t.fuel = some S := by
  have := mapM_id_get h k
  rw [List.getElem?_mapIdx, hth] at this
  simp only [Option.map_some] at this
  cases hk : Ss[k]? with
  | none => rw [hk] at this; cases this
  | some S =>
    rw [hk] at this
    simp only [Option.map_some, Option.some.injEq] at this
    exact ⟨S, List.mem_of_getElem? hk, this⟩

/-- The memory actions of a run with the skeleton `S ∈ Ss` are at memory events of `Ss`. -/
theorem act_memEvs {Ss : List (List (List MemEvent.Event))} {S : List (List MemEvent.Event)}
    (hS : S ∈ Ss) {acc : List (List XAct)} (h : acc.map (fun acts => acts.map Act.ev) = S)
    {a : XAct} (ha : a ∈ acc.flatten) (hm : (a.ev.kind.reads || a.ev.kind.writes) = true) :
    a.ev ∈ memEvs Ss := by
  obtain ⟨acts, hacts, ha⟩ := List.mem_flatten.mp ha
  unfold memEvs
  refine List.mem_filter.mpr ⟨List.mem_flatten.mpr ⟨acts.map Act.ev, ?_, List.mem_map_of_mem ha⟩, hm⟩
  exact List.mem_flatten.mpr ⟨S, hS, h ▸ List.mem_map_of_mem hacts⟩

/-- **The footprints of the store-buffer machine events of an action** are the action's, for a
memory
action. -/
theorem foot_of_actX {i : Nat} {a : XAct} (hok : ActOk a) {ev : Silmaril.X86.MemoryModel.Tso.XEvent Nat}
    (hev : ev ∈ actX i a) {p : Nat × Nat} (hp : p ∈ Silmaril.X86.MemoryModel.OpAx.footOf ev) :
    p = (a.ev.addr, a.ev.size) ∧ (a.ev.kind.reads || a.ev.kind.writes) = true := by
  obtain ⟨-, -, hr, hw, -⟩ := hok
  cases hk : a.ev.kind with
  | load =>
    simp only [actX, hk, List.mem_singleton] at hev
    subst hev
    simp only [Silmaril.X86.MemoryModel.OpAx.footOf, List.mem_singleton] at hp
    subst hp
    simp [hr (by simp [hk, MemEvent.Kind.reads]), MemEvent.Kind.reads]
  | store =>
    simp only [actX, hk, List.mem_singleton] at hev
    subst hev
    simp only [Silmaril.X86.MemoryModel.OpAx.footOf, List.mem_singleton] at hp
    subst hp
    simp [hw (by simp [hk, MemEvent.Kind.writes]), MemEvent.Kind.writes]
  | rmw =>
    have h1 := hr (by simp [hk, MemEvent.Kind.reads])
    have h2 := hw (by simp [hk, MemEvent.Kind.writes])
    by_cases hl : a.ev.locked = true
    · simp only [actX, hk, hl, ite_true, List.mem_singleton] at hev
      subst hev
      simp only [Silmaril.X86.MemoryModel.OpAx.footOf, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [h1, h2, MemEvent.Kind.reads]
    · simp only [actX, hk, hl, Bool.false_eq_true, ite_false, List.mem_cons,
        List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl <;>
        simp only [Silmaril.X86.MemoryModel.OpAx.footOf, List.mem_singleton] at hp <;> subst hp <;>
        simp [h1, h2, MemEvent.Kind.reads]
  | fence k =>
    simp only [actX, hk] at hev
    split at hev
    · simp only [List.mem_singleton] at hev
      subst hev
      simp [Silmaril.X86.MemoryModel.OpAx.footOf] at hp
    · cases hev

/-- **A memory unit of the litmus translation is at its action's footprint.** -/
theorem unit_of_threadUnits {i : Nat} :
    ∀ {p : Nat} {as : List XAct} {u : Silmaril.X86.MemoryModel.Axiomatic.Ev × List Byte},
      u ∈ threadUnits i p as → u.1.isM = true →
      ∃ a ∈ as, u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size ∧ u.1.accAddr = a.ev.addr ∧
        u.1.accSize = a.ev.size ∧ (a.ev.kind.reads || a.ev.kind.writes) = true
  | _, [], _, hu, _ => by simp [threadUnits] at hu
  | p, a :: as, u, hu, hm => by
    simp only [threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · refine ⟨a, List.mem_cons_self, ?_⟩
      unfold actUnits at hu
      cases hk : a.ev.kind with
      | load =>
        rw [hk] at hu; simp only [List.mem_singleton] at hu; subst hu
        simp [MemEvent.Kind.reads]
      | store =>
        rw [hk] at hu; simp only [List.mem_singleton] at hu; subst hu
        simp [MemEvent.Kind.writes]
      | rmw =>
        rw [hk] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> simp [MemEvent.Kind.reads]
      | fence k =>
        rw [hk] at hu; simp only [List.mem_singleton] at hu; subst hu
        simp [Silmaril.X86.MemoryModel.Axiomatic.Ev.isM, Silmaril.X86.MemoryModel.Axiomatic.Ev.isR,
          Silmaril.X86.MemoryModel.Axiomatic.Ev.isW] at hm
    · obtain ⟨b, hb, h⟩ := unit_of_threadUnits hu hm
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun
