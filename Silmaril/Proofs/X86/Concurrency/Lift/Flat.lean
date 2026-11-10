module

public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Defs
import Silmaril.X86.MemEvent.Thms

/-!
# The Memory-event glue for `Open` and `Open9`: proofs

These proofs close `Lift.Task.openFlatStep` and `Lift.Task.open9FlatStep`.

The argument is generic in the access list and needs no per-instruction semantics:

* `fillAct m m' e`: an event filled with the bytes its reads find in the pre-memory `m` and the
  bytes its writes leave in the post-memory `m'`;
* `replay_fill`: if no event of a list reads after an event that writes (`ReadsFirst`), the
  filled list replays from any memory agreeing with `m` on the read set, and the result is that
  memory overwritten on the write set by `m'`;
* `flat_of_patched`: `Patched` (the new memory is the old one changed exactly on the write
  set, every byte of which is backed afterwards) makes that result the flat post-memory;
* `flat_acts`: so every `Good` list (`ReadsFirst`, unlocked, positive sizes) under `Patched` has
  `ActOk` actions with exactly that event list that replay to the post-memory;
* `ext_good`, `ext8_good`, `ext9_good`: every `Open`/`Open9` access list is `Good` (a case
  split over the decoder arms; every list has at most two events, and the only two-event lists,
  `push r/m` and `call r/m`, load before they store);
* `openFlatStep`, `open9FlatStep`: from `MemEvent.open_step_sc` / `open9_step_sc`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Lift.Flat

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.Concurrency.Lift
open Silmaril.X86.MemoryModel.Litmus (XAct Byte)
open Silmaril.X86.MemEvent

/-! ## Filling and replaying a generic access list -/

/-- An event filled with the bytes its reads find in `m` and its writes leave in `m'`. -/
def fillAct (m m' : Mem) (e : Event) : XAct :=
  ⟨e, .plain, if e.kind.reads then bytesAt m e.addr e.size else [],
    if e.kind.writes then bytesAt m' e.addr e.size else []⟩

/-- No event reads after an event that writes. -/
def ReadsFirst : List Event → Prop
  | [] => True
  | e :: es => (e.kind.writes = true → ∀ e' ∈ es, e'.kind.reads = false) ∧ ReadsFirst es

/-- The shape an access list needs: `ReadsFirst`, no `locked` event, positive sizes. -/
def Good (es : List Event) : Prop := ReadsFirst es ∧ ∀ e ∈ es, e.locked = false ∧ 0 < e.size

theorem length_bytesAt (m : Mem) (a sz : Nat) : (bytesAt m a sz).length = sz := by
  simp [bytesAt]

theorem fillAct_ev (m m' : Mem) (e : Event) : (fillAct m m' e).ev = e := rfl

theorem bytesAt_congr {M m : Mem} {a sz : Nat} (h : ∀ y, a ≤ y → y < a + sz → M y = m y) :
    bytesAt M a sz = bytesAt m a sz := by
  unfold bytesAt
  refine List.map_congr_left fun y hy => ?_
  rw [List.mem_range'_1] at hy
  rw [h y hy.1 hy.2]

theorem putBytes_bytesAt (M m' : Mem) (a sz y : Nat) :
    putBytes M a sz (bytesAt m' a sz) y =
      if a ≤ y ∧ y < a + sz then some ((m' y).getD 0) else M y := by
  unfold putBytes bytesAt
  split
  · rename_i hy
    have h1 : y - a < sz := by omega
    have h2 : a + (y - a) = y := by omega
    simp [h1, h2]
  · rfl

theorem readSet_cons {e : Event} {es : List Event} {a : Nat} :
    readSet (e :: es) a ↔ (e.kind.reads = true ∧ e.Covers a) ∨ readSet es a := by
  simp [readSet]

theorem writeSet_cons {e : Event} {es : List Event} {a : Nat} :
    writeSet (e :: es) a ↔ (e.kind.writes = true ∧ e.Covers a) ∨ writeSet es a := by
  simp [writeSet]

open Classical in
/-- **Replay of a filled `ReadsFirst` list**: from a memory agreeing with `m` on the read set,
the result is that memory overwritten by `m'` on the write set. -/
theorem replay_fill (m m' : Mem) :
    ∀ (es : List Event) (M : Mem), ReadsFirst es → (∀ a, readSet es a → M a = m a) →
      actsReplay M (es.map (fillAct m m')) =
        some (fun y => if writeSet es y then some ((m' y).getD 0) else M y)
  | [], M, _, _ => by simp [actsReplay, writeSet]
  | e :: es, M, ⟨hw, hrf⟩, hagr => by
    have hrd : e.kind.reads = true → bytesAt M e.addr e.size = bytesAt m e.addr e.size :=
      fun hr => bytesAt_congr fun y h1 h2 => hagr y (readSet_cons.2 (.inl ⟨hr, h1, h2⟩))
    -- the memory after the first event
    let M1 : Mem := if e.kind.writes then putBytes M e.addr e.size (bytesAt m' e.addr e.size)
      else M
    have hstep : actStep M (fillAct m m' e) = some M1 := by
      unfold actStep fillAct M1
      cases hk : e.kind <;> simp_all [Kind.reads, Kind.writes]
    have hagr1 : ∀ a, readSet es a → M1 a = m a := by
      intro a ha
      by_cases hwe : e.kind.writes = true
      · obtain ⟨e', he', hr', -⟩ := ha
        rw [hw hwe e' he'] at hr'
        cases hr'
      · simp only [M1, hwe]
        exact hagr a (readSet_cons.2 (.inr ha))
    rw [List.map_cons, actsReplay, hstep, Option.bind_some, replay_fill m m' es M1 hrf hagr1]
    congr 1
    funext y
    by_cases hwe : e.kind.writes = true
    · simp only [M1, hwe, ite_true, putBytes_bytesAt, writeSet_cons, Event.Covers]
      by_cases h1 : writeSet es y <;> by_cases h2 : e.addr ≤ y ∧ y < e.addr + e.size <;>
        simp [h1, h2]
    · simp only [M1, hwe, writeSet_cons]
      by_cases h1 : writeSet es y <;> simp [h1]

open Classical in
/-- `Patched` makes the replay result the flat post-memory. -/
theorem flat_of_patched {W : Nat → Prop} {mem mem' : Silmaril.Process.Memory}
    (hp : Patched W mem mem' mem mem') :
    (fun y => if W y then some ((flat mem' y).getD 0) else flat mem y) = flat mem' := by
  funext y
  by_cases hy : W y
  · have hs := (hp.wrote y hy).2
    simp only [hy, ite_true, flat]
    cases h : mem'.bytes[y]? with
    | none => rw [h] at hs; cases hs
    | some b => rfl
  · simp only [hy, ite_false, flat]
    exact (hp.outside y hy).symm

/-- **A `Good` access list under `Patched` has flat actions**: `ActOk` actions with exactly
that event list, replaying from the flat pre-memory to the flat post-memory. -/
theorem flat_acts {es : List Event} (hg : Good es) {mem mem' : Silmaril.Process.Memory}
    (hp : Patched (writeSet es) mem mem' mem mem') :
    ∃ acts : List XAct, acts.map (·.ev) = es ∧ (∀ a ∈ acts, ActOk a) ∧
      actsReplay (flat mem) acts = some (flat mem') := by
  refine ⟨es.map (fillAct (flat mem) (flat mem')), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, fillAct_ev]
  · intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨hl, hs⟩ := hg.2 e he
    refine ⟨fun h => by simp [fillAct, hl] at h, ?_⟩
    unfold fillAct
    cases hk : e.kind <;> simp [Kind.reads, Kind.writes, length_bytesAt, hs]
  · rw [replay_fill _ _ es _ hg.1 (fun _ _ => rfl), flat_of_patched hp]

/-! ## Every `Open`/`Open9` access list is `Good` -/

theorem good_nil : Good [] := ⟨trivial, by simp⟩

theorem good_single {e : Event} (hl : e.locked = false) (hs : 0 < e.size) : Good [e] :=
  ⟨⟨fun _ _ h => by simp at h, trivial⟩, by simp [hl, hs]⟩

theorem good_memEv (k : Kind) {sz : Nat} (hsz : 0 < sz) (a : Silmaril.X86.Ext.Mem)
    (s : Silmaril.X86.State) (next : Silmaril.X86.Word) : Good (memEv k false sz a s next) :=
  good_single rfl hsz

theorem good_rmEv (k : Kind) {sz : Nat} (hsz : 0 < sz) (op : Silmaril.X86.Ext.RM)
    (s : Silmaril.X86.State) (next : Silmaril.X86.Word) : Good (rmEv k false sz op s next) := by
  cases op
  · exact good_nil
  · exact good_memEv k hsz _ s next

theorem good_rm8Ev (k : Kind) (op : Silmaril.X86.Ext8.RM8) (s : Silmaril.X86.State)
    (next : Silmaril.X86.Word) : Good (rm8Ev k false op s next) := by
  cases op
  · exact good_nil
  · exact good_memEv k (by decide) _ s next

theorem good_pushEv (s : Silmaril.X86.State) : Good (pushEv s) := good_single rfl (Nat.succ_pos 7)

theorem good_popEv (s : Silmaril.X86.State) : Good (popEv s) := good_single rfl (Nat.succ_pos 7)

/-- A load of an `r/m` operand, then a `push`: the two-event lists (`push r/m`, `call r/m`). -/
theorem good_load_push {sz : Nat} (hsz : 0 < sz) (op : Silmaril.X86.Ext.RM)
    (s : Silmaril.X86.State) (next : Silmaril.X86.Word) :
    Good (rmEv .load false sz op s next ++ pushEv s) := by
  cases op
  · exact good_pushEv s
  · refine ⟨⟨fun h => by simp [Kind.writes] at h, good_pushEv s |>.1⟩, ?_⟩
    simp [rmEv, memEv, pushEv, hsz]

theorem sz_bytes_pos (sz : Silmaril.X86.Ext.Sz) : 0 < sz.bytes := by cases sz <;> decide

theorem narrow_bytes_pos (n : Silmaril.X86.Ext.Narrow) : 0 < n.bytes := by cases n <;> decide

/-- Discharge `Good` for one arm of an access list. -/
local macro "good_arm" : tactic => `(tactic| first
  | exact good_nil
  | exact good_pushEv _
  | exact good_popEv _
  | exact good_single rfl (Nat.succ_pos _)
  | exact good_rmEv _ (sz_bytes_pos _) _ _ _
  | exact good_rmEv _ (narrow_bytes_pos _) _ _ _
  | exact good_rmEv _ (by decide) _ _ _
  | exact good_rm8Ev _ _ _ _
  | exact good_memEv _ (sz_bytes_pos _) _ _ _
  | exact good_load_push (by decide) _ _ _
  | (split <;> exact good_rm8Ev _ _ _ _))

theorem ext_good (i : Silmaril.X86.Ext.Instr) (s : Silmaril.X86.State) (len : Nat) :
    Good (extAccesses i s len) := by
  cases i <;> simp only [extAccesses] <;> good_arm

theorem ext8_good (i : Silmaril.X86.Ext8.Instr) (s : Silmaril.X86.State) (len : Nat) :
    Good (ext8Accesses i s len) := by
  cases i with
  | base i => exact ext_good i s len
  | new i => cases i <;> simp only [ext8Accesses, ext8NewAccesses] <;> good_arm

theorem ext9_good (i : Silmaril.X86.Ext9.Instr) (s : Silmaril.X86.State) (len : Nat) :
    Good (ext9Accesses i s len) := by
  cases i with
  | ext8 i => exact ext8_good i s len
  | new i => cases i <;> simp only [ext9Accesses, ext9NewAccesses] <;> good_arm

/-! ## The glue -/

/-- **Memory-event glue for `Open`.** -/
theorem openFlatStep : Task.openFlatStep := by
  intro m m' h
  obtain ⟨i, n, hf, -, -, hp⟩ := open_step_sc h
  obtain ⟨acts, hmap, hok, hr⟩ := flat_acts (ext8_good i m.core n) hp
  refine ⟨acts, ?_, hok, hr⟩
  simp only [openActs, hf]
  exact hmap

/-- **Memory-event glue for `Open9`.** -/
theorem open9FlatStep : Task.open9FlatStep := by
  intro m m' h
  obtain ⟨i, n, hf, -, -, hp⟩ := open9_step_sc h
  obtain ⟨acts, hmap, hok, hr⟩ := flat_acts (ext9_good i m.core n) hp
  refine ⟨acts, ?_, hok, hr⟩
  simp only [open9Acts, hf]
  exact hmap

end Silmaril.Proofs.X86.Concurrency.Lift.Flat
