module

public import Silmaril.Proofs.X86.MemEvent.Atomic9

/-!
# The SC reading of the open machines, and the one-step `Sep` frame rule

* `Local.frame`: taking both memories equal, a local executor changes only the write set,
  keeps the mapping list, and really wrote every byte of the write set.
* `open_step_eq`, `open9_step_eq`, `atomic9_step_eq`: a step is the fetch followed by the
  executor of the fetched instruction on the one memory.
* `open_step_sc`, `open9_step_sc`, `atomic9_step_sc`: the **SC reading**: every step is a
  fetched instruction whose executor is local for its access list, and the step's memory is
  the old memory patched on exactly that access list's write set.
* `changesWithin_of_local`, `triple_of_step`, `triple_step_of_local`: the instruction-level
  frame rule for `Sep.Triple`. For one `Open.step`, the memory part of the frame obligation
  reduces to "the precondition's fragment owns the write set of the access list".
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.MemEvent
open Silmaril.X86.Sep (Frag SProp toFrag permsAt Triple)

/-! ## Frame and exactness -/

theorem Local.frame {ρ ε α : Type} {view : ρ → ε ⊕ (α × Memory)} {exec : Memory → ρ}
    {es : List Event} (hl : Local view exec es) {m m₁ : Memory} {a : α}
    (h : view (exec m) = .inr (a, m₁)) : Patched (writeSet es) m m₁ m m₁ := by
  have := hl.congr m m (Agree.refl _ m)
  rw [h] at this
  exact this.2

/-! ## A step is a fetch followed by an execution -/

theorem open_step_eq (m : MState) :
    Silmaril.X86.Open.step m =
      (openFetch m.memory m.core.rip.toNat).bind fun p =>
        Silmaril.X86.Open.ofResult (Silmaril.X86.Ext8.exec p.1 m.core m.memory p.2) := by
  unfold Silmaril.X86.Open.step openFetch
  rcases Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with f | ⟨i, n⟩
  · cases f <;> rfl
  · rfl

theorem open9_step_eq (m : MState) :
    Silmaril.X86.Open9.step m =
      (open9Fetch m.memory m.core.rip.toNat).bind fun p =>
        Silmaril.X86.Open.ofResult (Silmaril.X86.Ext9.exec p.1 m.core m.memory p.2) := by
  unfold Silmaril.X86.Open9.step open9Fetch
  rw [open_step_eq]
  unfold openFetch
  rcases Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with f | ⟨i, n⟩
  · cases f with
    | decoded i k => rfl
    | truncated => rfl
    | undecodable =>
      dsimp only
      rcases Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat with _ | _ | ⟨i, n⟩ <;> rfl
  · rfl

theorem atomic9_step_eq (m : MState) :
    Silmaril.X86.Atomic9.step m =
      (atomic9Fetch m.memory m.core.rip.toNat).bind fun p =>
        Silmaril.X86.Open.ofResult
          (Silmaril.X86.Atomic9.exec p.1 m.core m.memory p.2) := by
  unfold Silmaril.X86.Atomic9.step atomic9Fetch
  rw [open_step_eq]
  unfold openFetch
  rcases Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat with f | ⟨i, n⟩
  · cases f with
    | decoded i k => rfl
    | truncated => rfl
    | undecodable =>
      dsimp only
      rcases Silmaril.X86.Ext9.fetchNew m.memory m.core.rip.toNat with _ | _ | ⟨i, n⟩
      · rcases Silmaril.X86.Atomic9.fetchNew m.memory m.core.rip.toNat with
          _ | _ | ⟨i, n⟩ <;> rfl
      · rfl
      · rfl
  · rfl

theorem ofResult_eq_some {r : Silmaril.X86.Ext.Result} {m' : MState}
    (h : Silmaril.X86.Open.ofResult r = some m') : r = .ok m'.core m'.memory := by
  cases r with
  | ok c mm =>
    simp only [Silmaril.X86.Open.ofResult, Option.some.injEq] at h
    subst h; rfl
  | _ => simp [Silmaril.X86.Open.ofResult] at h

/-! ## The SC reading -/

/-- **The SC reading of `Open.step`.** -/
theorem open_step_sc {m m' : MState} (h : Silmaril.X86.Open.step m = some m') :
    ∃ i n, openFetch m.memory m.core.rip.toNat = some (i, n) ∧
      Silmaril.X86.Ext8.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Silmaril.X86.Ext8.exec i m.core mem n) (ext8Accesses i m.core n) ∧
      Patched (writeSet (ext8Accesses i m.core n)) m.memory m'.memory m.memory m'.memory := by
  rw [open_step_eq, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i, n⟩, hf, he⟩ := h
  have he := ofResult_eq_some he
  have hl := ext8_local i m.core n
  exact ⟨i, n, hf, he, hl, Local.frame hl (by simp only [he]; rfl)⟩

/-- **The SC reading of `Open9.step`**: the fetched instruction's executor is local for its
access list, and the step's memory is the old memory patched on exactly its write set. -/
theorem open9_step_sc {m m' : MState} (h : Silmaril.X86.Open9.step m = some m') :
    ∃ i n, open9Fetch m.memory m.core.rip.toNat = some (i, n) ∧
      Silmaril.X86.Ext9.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Silmaril.X86.Ext9.exec i m.core mem n)
        (ext9Accesses i m.core n) ∧
      Patched (writeSet (ext9Accesses i m.core n)) m.memory m'.memory m.memory m'.memory := by
  rw [open9_step_eq, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i, n⟩, hf, he⟩ := h
  have he := ofResult_eq_some he
  have hl := ext9_local i m.core n
  exact ⟨i, n, hf, he, hl, Local.frame hl (by simp only [he]; rfl)⟩

/-- **The SC reading of `Atomic9.step`.** -/
theorem atomic9_step_sc {m m' : MState} (h : Silmaril.X86.Atomic9.step m = some m') :
    ∃ i n, atomic9Fetch m.memory m.core.rip.toNat = some (i, n) ∧
      Silmaril.X86.Atomic9.exec i m.core m.memory n = .ok m'.core m'.memory ∧
      Local extView (fun mem => Silmaril.X86.Atomic9.exec i m.core mem n)
        (atomic9Accesses i m.core n) ∧
      Patched (writeSet (atomic9Accesses i m.core n)) m.memory m'.memory m.memory m'.memory := by
  rw [atomic9_step_eq, Option.bind_eq_some_iff] at h
  obtain ⟨⟨i, n⟩, hf, he⟩ := h
  have he := ofResult_eq_some he
  have hl := atomic9_local i m.core n
  exact ⟨i, n, hf, he, hl, Local.frame hl (by simp only [he]; rfl)⟩

/-! ## The one-step frame rule for `Sep.Triple` -/

/-- A transition that keeps the bytes outside `W` and the mapping list, with a core that
changes only owned locations, changes only owned locations, provided `h` owns `W`. -/
theorem changesWithin_of_patched {h : Frag} {m m' : MState} {W : Nat → Prop}
    (hp : Patched W m.memory m'.memory m.memory m'.memory)
    (hw : ∀ a, W a → (h (.mem a)).isSome = true) (hc : CoreWithin h m.core m'.core) :
    ChangesWithin h m m' := by
  intro l hl
  cases l with
  | reg r =>
    by_cases e : m'.core.read r = m.core.read r
    · simp only [toFrag, e]
    · have := hc.1 r e; rw [hl] at this; cases this
  | rip =>
    by_cases e : m'.core.rip = m.core.rip
    · simp only [toFrag, e]
    · have := hc.2.1 e; rw [hl] at this; cases this
  | flags =>
    by_cases e : m'.core.flags = m.core.flags
    · simp only [toFrag, e]
    · have := hc.2.2 e; rw [hl] at this; cases this
  | mem a =>
    have hnw : ¬ W a := fun hW => by have := hw a hW; rw [hl] at this; cases this
    have hb := hp.outside a hnw
    have hperm : permsAt m'.memory a = permsAt m.memory a := by
      unfold permsAt Memory.permits; rw [hp.regions]
    simp only [toFrag, Std.ExtHashMap.get?_eq_getElem?, hb, hperm]
  | regions => simp only [toFrag, hp.regions]

/-- **The one-step triple rule.** If every state whose fragment contains a `P`-fragment `h`
takes one `Open.step` that changes only locations of `h` and ends with `Q` on `h`'s domain,
then `Triple P Q`. -/
theorem triple_of_step {P Q : SProp}
    (hstep : ∀ m h, Frag.Le h (toFrag m) → P h →
      ∃ m', Silmaril.X86.Open.step m = some m' ∧ ChangesWithin h m m' ∧
        Q (Frag.reval h (toFrag m'))) :
    Triple Silmaril.X86.Open.isa P Q := by
  intro F m _ hpf
  change Silmaril.X86.Sep.sep P F (toFrag m) at hpf
  show ∃ t, Silmaril.Machine.Execution.Reaches Silmaril.X86.Open.step m t ∧
    Silmaril.X86.Sep.sep Q F (toFrag t)
  obtain ⟨h₁, h₂, hd, hu, hP, hF⟩ := hpf
  have hle : Frag.Le h₁ (toFrag m) := by
    intro l v hv; rw [hu]; simp only [Frag.union, hv]
  obtain ⟨m', hs, hch, hQ⟩ := hstep m h₁ hle hP
  refine ⟨m', ⟨1, by simp [Silmaril.Machine.Execution.run, hs]⟩, Frag.reval h₁ (toFrag m'), h₂,
    ?_, ?_, hQ, hF⟩
  · intro l
    rcases hd l with e | e
    · left; simp only [Frag.reval, e, Option.isSome_none, Bool.false_eq_true, ite_false]
    · right; exact e
  · funext l
    simp only [Frag.union, Frag.reval]
    cases e : h₁ l with
    | some v =>
      simp only [Option.isSome_some, ite_true]
      cases h' : toFrag m' l with
      | none => cases l <;> simp [toFrag] at h'
      | some w => rfl
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [hch l e]
      have := congrFun hu l
      simp only [Frag.union, e] at this
      exact this

/-- **The instruction-level frame rule for `Sep.Triple`**. To prove a one-step
triple it suffices, for every state whose fragment contains a `P`-fragment `h`, to name the
fetched instruction and its successful execution, to show that `h` owns the **write set of the
instruction's access list** and the registers, `rip` and flags the step changes, and that `Q`
holds on `h`'s domain afterwards. The memory frame (bytes outside the write set, the mapping
list and the permissions are unchanged) comes from `ext8_local`. -/
theorem triple_step_of_local {P Q : SProp}
    (hstep : ∀ m h, Frag.Le h (toFrag m) → P h →
      ∃ i n m', openFetch m.memory m.core.rip.toNat = some (i, n) ∧
        Silmaril.X86.Ext8.exec i m.core m.memory n = .ok m'.core m'.memory ∧
        (∀ a, writeSet (ext8Accesses i m.core n) a → (h (.mem a)).isSome = true) ∧
        CoreWithin h m.core m'.core ∧ Q (Frag.reval h (toFrag m'))) :
    Triple Silmaril.X86.Open.isa P Q := by
  refine triple_of_step fun m h hle hP => ?_
  obtain ⟨i, n, m', hf, he, hw, hc, hQ⟩ := hstep m h hle hP
  have hl := ext8_local i m.core n
  have hp := Local.frame hl (m := m.memory) (m₁ := m'.memory) (a := m'.core) (by simp only [he]; rfl)
  refine ⟨m', ?_, changesWithin_of_patched hp hw hc, hQ⟩
  rw [open_step_eq, hf]
  simp only [Option.bind_some, he, Silmaril.X86.Open.ofResult]

/-! ## A concrete access list -/

/-- gcc's SEQ_CST fence `lock or qword ptr [rsp], 0` (`f0 48 83 0c 24 00`) has one locked
read-modify-write event: the eight bytes at `rsp`. -/
theorem lockOr_rsp_zero_events (s : State) (next : Word) :
    (Silmaril.X86.Atomic9.decodeNew [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00]).map
        (fun p => (atomic9NewAccesses p.1 s next, p.2)) =
      some ([⟨.rmw, (s.read .rsp).toNat, 8, true⟩], 6) := by
  have h : Silmaril.X86.Atomic9.decodeNew [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00] =
      some (.lockAluI .q .or ⟨.reg .rsp, none, 0, by simp⟩ 0, 6) := by decide
  rw [h]
  simp [atomic9NewAccesses, memEv, aluKind, Silmaril.X86.Atomic9.tag,
    Silmaril.X86.Ext.Mem.addr]
  exact (s.read .rsp).isLt

/-! ## Write sets are exact: a spurious store is rejected -/

/-- The memory with one readable, writable byte at address 0 holding `b`. -/
def oneByte (b : Byte) : Memory :=
  ⟨[⟨0, 1, ⟨true, true, false⟩⟩], (∅ : Std.ExtHashMap Nat Byte).insert 0 b⟩

/-- **`Local` is not vacuous about write sets**: `endbr64` writes nothing, and an access list
that claims a store to byte 0 is not local for it (on two memories that differ only at byte 0,
the claimed write set would have to agree afterwards). -/
theorem not_local_spurious_store (s : State) :
    ¬ Local extView (fun m => Silmaril.X86.Ext.exec .endbr64 s m 4) [⟨.store, 0, 1, false⟩] := by
  intro h
  have := h.congr (oneByte 0) (oneByte 1) ⟨rfl, fun a ha => by simp [readSet] at ha⟩
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, extView, Rel] at this
  have e := this.2.inside 0 (by simp [writeSet, Event.Covers])
  simp [oneByte] at e

/-! ## Read sets are needed, and a claimed `rmw` must really write -/

/-- Eight bytes at address 0 with the permissions `perm`, all backed by zero. -/
def eightZero (perm : Silmaril.Process.Permissions) : Memory :=
  ⟨[⟨0, 8, perm⟩], Memory.install ∅ 0 [0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- The same mapping as `eightZero` with no backing bytes. -/
def eightUnbacked (perm : Silmaril.Process.Permissions) : Memory := ⟨[⟨0, 8, perm⟩], ∅⟩

/-- **Read sets are not vacuous**: `pop rax` with its load dropped from the access list is not
local (with `rsp = 0`, an unbacked and a backed memory agree on the empty read set, but the
first faults and the second succeeds). -/
theorem not_local_dropped_load (s : State) (hs : s.read .rsp = 0) :
    ¬ Local extView (fun m => Silmaril.X86.Ext.exec (.pop .rax) s m 1) [] := by
  intro h
  have := h.congr (eightUnbacked ⟨true, true, false⟩) (eightZero ⟨true, true, false⟩)
    ⟨rfl, fun a ha => by simp [readSet] at ha⟩
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.popWord, hs, extView, Rel,
    Memory.readBytes, Memory.readWith, eightUnbacked, eightZero, Memory.readBacking,
    Memory.install, Memory.permits, Silmaril.Process.Region.Contains, addressLimit,
    Silmaril.Process.Permissions.allows, Std.ExtHashMap.getElem_insert,
    Silmaril.X86.wordOfBytes?] at this

/-- `[rsp]` as an effective address. -/
def rspMem : Silmaril.X86.Ext.Mem := ⟨.reg .rsp, none, 0, by simp⟩

/-- **Write sets of `rmw` events are exact**: `test qword ptr [rsp], rax` (which writes nothing)
with its load replaced by an `rmw` is not local. On read-only memory the instruction succeeds,
but `Patched.wrote` asks for write permission on the claimed write set. -/
theorem not_local_spurious_rmw (s : State) (hs : s.read .rsp = 0) :
    ¬ Local extView (fun m => Silmaril.X86.Ext.exec (.test .q (.mem rspMem) .rax) s m 3)
      [⟨.rmw, 0, 8, false⟩] := by
  intro h
  have := h.congr (eightZero ⟨true, false, false⟩) (eightZero ⟨true, false, false⟩)
    (Agree.refl _ _)
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.readRM, rspMem,
    Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.loadN, hs, extView, Rel,
    Memory.readBytes, Memory.readWith, eightZero, Memory.readBacking, Memory.install,
    Memory.permits, Silmaril.Process.Region.Contains, addressLimit,
    Silmaril.Process.Permissions.allows, Std.ExtHashMap.getElem_insert] at this
  have w := (this.wrote 0 ⟨_, List.mem_singleton_self _, rfl, by simp, by simp⟩).1
  simp [Memory.permits, Silmaril.Process.Region.Contains, Silmaril.Process.Permissions.allows]
    at w

end Silmaril.Proofs.X86.MemEvent
