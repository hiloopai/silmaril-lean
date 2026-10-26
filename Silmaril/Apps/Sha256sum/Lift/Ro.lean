module

public import Silmaril.X86.Ext.Regions
public import Silmaril.X86.Ext8.Basic

/-! # Execution never changes a byte that is not writable

`RO m m'`: `m'` has the mapping of `m`, and every byte that `m` does not permit writing is
unchanged. Every store of `X86.Ext` and of the `Ext8` variant goes through
`Memory.writeBytes`, which checks the write permission of the whole span first, so

* `exec_ro`: every retiring `Ext.exec` is `RO`;
* `exec8_ro`: every retiring `Ext8.exec` is `RO`.

This is **code integrity for free**: if the text is mapped without write permission, no
instruction can change it, whatever the addresses it stores to — no disjointness argument and
no address arithmetic at any step. It is what lets a symbolic executor keep fetching the
original instructions after arbitrary stores (`Lift.Code.of_ro`).
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (Reg Word State MState pushWord popWord)
open Silmaril.Process (Memory)

/-- `m'` has `m`'s mapping, and every byte `m` does not permit writing is unchanged. -/
def RO (m m' : Memory) : Prop :=
  m'.regions = m.regions ∧ ∀ a, m.permits .write a = false → m'.bytes.get? a = m.bytes.get? a

theorem RO.refl (m : Memory) : RO m m := ⟨rfl, fun _ _ => rfl⟩

theorem RO.permits {m m' : Memory} (h : RO m m') (acc) (a : Nat) :
    m'.permits acc a = m.permits acc a := by
  unfold Memory.permits; rw [h.1]

theorem RO.trans {m₁ m₂ m₃ : Memory} (h₁ : RO m₁ m₂) (h₂ : RO m₂ m₃) : RO m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, fun a ha => (h₂.2 a (by rw [h₁.permits]; exact ha)).trans (h₁.2 a ha)⟩

theorem writeBytes_ro {m m' : Memory} {address : Nat} {bytes : List Silmaril.Process.Byte}
    (h : m.writeBytes address bytes = some m') : RO m m' := by
  have hw := Memory.writeBytes_writesOnly h
  have hp := Memory.writeBytes_permitted h
  rw [Memory.Permitted, Memory.checkSpan_iff] at hp
  refine ⟨hw.1, fun a ha => hw.2 a ?_⟩
  by_contra hin
  have := hp.2.2 (a - address) (by omega)
  rw [show address + (a - address) = a by omega, ha] at this
  cases this

theorem storeN_ro {m m' : Memory} {a : Word} {k : Nat} {v : Word}
    (h : storeN m a k v = some m') : RO m m' := writeBytes_ro h

/-- Results of an instruction body that are `RO` from `m`. -/
def KeepsRO (m : Memory) (o : Option (State × Memory)) : Prop :=
  ∀ s m', o = some (s, m') → RO m m'

theorem keepsRO_same (m : Memory) (s : State) : KeepsRO m (some (s, m)) := by
  rintro _ _ ⟨⟩
  exact RO.refl _

theorem keepsRO_map_same {α : Type} (m : Memory) (o : Option α) (f : α → State) :
    KeepsRO m (o.map fun x => (f x, m)) := by
  rintro s m' h
  cases o <;> simp_all [RO.refl]

theorem keepsRO_store {m : Memory} {a : Word} {k : Nat} {v : Word} (s : State) :
    KeepsRO m ((storeN m a k v).map fun after => (s, after)) := by
  rintro s' m' h
  cases hs : storeN m a k v with
  | none => simp [hs] at h
  | some m'' =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact storeN_ro hs

theorem keepsRO_writeRM (sz : Sz) (op : RM) (v : BitVec sz.bits) (s : State) (m : Memory)
    (next : Word) : KeepsRO m (writeRM sz op v s m next) := by
  cases op with
  | reg r => exact keepsRO_same _ _
  | mem a => exact keepsRO_store _

theorem keepsRO_writeNarrow (n : Narrow) (op : RM) (v : BitVec n.bits) (s : State)
    (m : Memory) (next : Word) : KeepsRO m (writeNarrow n op v s m next) := by
  cases op with
  | reg r => exact keepsRO_same _ _
  | mem a => exact keepsRO_store _

theorem keepsRO_writeRM8 (op : RM) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsRO m (writeRM8 op v s m next) := by
  cases op with
  | reg r => exact keepsRO_same _ _
  | mem a => exact keepsRO_store _

theorem keepsRO_map {m : Memory} {o : Option (State × Memory)} (h : KeepsRO m o)
    (f : State × Memory → State) : KeepsRO m (o.map fun r => (f r, r.2)) := by
  rintro s m' h'
  cases ho : o with
  | none => simp [ho] at h'
  | some r =>
    simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨-, rfl⟩ := h'
    exact h _ _ ho

theorem keepsRO_aluStep (sz : Sz) (op : AluOp) (dst : RM) (y : BitVec sz.bits) (s : State)
    (m : Memory) (next : Word) : KeepsRO m (aluStep sz op dst y s m next) := by
  unfold aluStep
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsRO_same _ _
    · exact keepsRO_map (keepsRO_writeRM sz dst _ s m next) _

theorem keepsRO_aluStepR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) (s : State)
    (m : Memory) (next : Word) : KeepsRO m (aluStepR sz op dst src s m next) := by
  unfold aluStepR
  split
  · rintro _ _ ⟨⟩
  · split <;> exact keepsRO_same _ _

theorem keepsRO_pushWord (s : State) (m : Memory) (v : Word) :
    KeepsRO m (pushWord s m v) := by
  rintro s' m' h
  unfold pushWord at h
  cases hw : m.writeBytes (s.read .rsp - 8#64).toNat (Machine.LittleEndian.encodeWords [v]) with
  | none => rw [hw] at h; cases h
  | some m'' =>
    rw [hw] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact writeBytes_ro hw

theorem retire_ro {m : Memory} {next : Word} {o : Option (State × Memory)}
    (h : KeepsRO m o) {core : State} {m' : Memory} (he : retire next o = .ok core m') :
    RO m m' := by
  unfold retire at he
  split at he
  · cases he
    exact h _ _ rfl
  · cases he

theorem keepsRO_pushWord' {s : State} {m : Memory} {v : Word} {t : State} {m' : Memory}
    (h : pushWord s m v = some (t, m')) : RO m m' :=
  keepsRO_pushWord s m v t m' h

/-- **No instruction changes a byte that is not writable.** -/
theorem exec_ro {i : Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : exec i s m len = .ok core m') : RO m m' := by
  cases i
  all_goals try (unfold exec at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; exact RO.refl _)
    | (cases h; exact keepsRO_pushWord' ‹_›)
    | (refine retire_ro ?_ h
       first
        | with_reducible apply keepsRO_same
        | with_reducible apply keepsRO_map_same
        | with_reducible apply keepsRO_writeRM
        | with_reducible apply keepsRO_writeNarrow
        | with_reducible apply keepsRO_writeRM8
        | with_reducible apply keepsRO_aluStep
        | with_reducible apply keepsRO_aluStepR
        | with_reducible apply keepsRO_pushWord
        | with_reducible apply keepsRO_store
        | (with_reducible apply keepsRO_map; with_reducible apply keepsRO_writeRM)
        | exact keepsRO_pushWord _ _ _
        | apply keepsRO_map_same)

end Silmaril.X86.Ext

namespace Silmaril.X86.Ext8

open Silmaril.X86 (Reg Word State)
open Silmaril.X86.Ext (RO KeepsRO keepsRO_same keepsRO_store keepsRO_map retire_ro)
open Silmaril.Process (Memory)

theorem keepsRO_rm8_write (op : RM8) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsRO m (op.write v s m next) := by
  cases op with
  | reg b => exact keepsRO_same _ _
  | mem a => exact keepsRO_store _

theorem keepsRO_alu8 (op : AluOp) (dst : RM8) (y : BitVec 8) (s : State) (m : Memory)
    (next : Word) : KeepsRO m (alu8 op dst y s m next) := by
  unfold alu8
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsRO_same _ _
    · exact keepsRO_map (keepsRO_rm8_write _ _ _ _ _) _

theorem execNew_ro {i : New} {s : State} {m : Memory} {next : Word} {core : State}
    {m' : Memory} (h : execNew i s m next = .ok core m') : RO m m' := by
  cases i
  all_goals (unfold execNew at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (refine retire_ro ?_ h
       first
        | exact keepsRO_alu8 _ _ _ _ _ _
        | exact keepsRO_same _ _
        | exact keepsRO_rm8_write _ _ _ _ _
        | exact Ext.keepsRO_map_same _ _ _
        | exact keepsRO_map (keepsRO_rm8_write _ _ _ _ _) _)

/-- **No instruction of the variant changes a byte that is not writable.** -/
theorem exec8_ro {i : Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : exec i s m len = .ok core m') : RO m m' := by
  cases i with
  | base i => exact Ext.exec_ro h
  | new i => exact execNew_ro h

end Silmaril.X86.Ext8
