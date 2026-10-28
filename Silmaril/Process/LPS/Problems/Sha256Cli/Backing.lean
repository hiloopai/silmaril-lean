module

public import Silmaril.X86.Ext.Regions
public import Silmaril.X86.Ext.Store

/-! # Execution keeps the memory map and only adds backing (VERIFIED)

`exec_grows`: a retiring `X86.Ext` instruction keeps `regions` and every backed byte stays
backed (stores install bytes, nothing is erased). Hence "every writable byte is backed"
(`Backed`) is preserved by instructions. The proof follows `X86.Ext.exec_regions`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.X86.Ext.Backing

open Silmaril.X86 (Reg Word State MState pushWord popWord)
open Silmaril.Process (Memory)

/-- `m'` has the regions of `m` and every byte backed in `m` is backed in `m'`. -/
def Grows (m m' : Memory) : Prop :=
  m'.regions = m.regions ∧ ∀ a : Nat, (m.bytes.get? a).isSome = true → (m'.bytes.get? a).isSome = true

theorem Grows.refl (m : Memory) : Grows m m := ⟨rfl, fun _ h => h⟩

theorem Grows.of_stored {before after : Memory} {address : Nat} {bytes : List Byte}
    (h : Stored before after address bytes) : Grows before after := by
  refine ⟨h.frame.1, fun a ha => ?_⟩
  by_cases inside : address ≤ a ∧ a < address + bytes.length
  · have := h.installed (a - address) (by omega)
    rw [show address + (a - address) = a by omega] at this
    rw [this]; rfl
  · have := h.frame.2 a (by omega)
    rw [this]; exact ha

def KeepsGrows (m : Memory) (o : Option (State × Memory)) : Prop :=
  ∀ s m', o = some (s, m') → Grows m m'

theorem keeps_same (m : Memory) (s : State) : KeepsGrows m (some (s, m)) := by
  rintro _ _ ⟨⟩
  exact Grows.refl _

theorem keeps_map_same {α : Type} (m : Memory) (o : Option α) (f : α → State) :
    KeepsGrows m (o.map fun x => (f x, m)) := by
  rintro s m' h
  cases o with
  | none => simp at h
  | some x =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Grows.refl _

theorem keeps_store {m : Memory} {a : Word} {k : Nat} {v : Word} (s : State) :
    KeepsGrows m ((storeN m a k v).map fun after => (s, after)) := by
  rintro s' m' h
  cases hs : storeN m a k v with
  | none => simp [hs] at h
  | some m'' =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Grows.of_stored (Stored.of_storeN hs)

theorem keeps_writeRM (sz : Sz) (op : RM) (v : BitVec sz.bits) (s : State) (m : Memory)
    (next : Word) : KeepsGrows m (writeRM sz op v s m next) := by
  cases op with
  | reg r => exact keeps_same _ _
  | mem a => exact keeps_store _

theorem keeps_writeNarrow (n : Narrow) (op : RM) (v : BitVec n.bits) (s : State)
    (m : Memory) (next : Word) : KeepsGrows m (writeNarrow n op v s m next) := by
  cases op with
  | reg r => exact keeps_same _ _
  | mem a => exact keeps_store _

theorem keeps_writeRM8 (op : RM) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsGrows m (writeRM8 op v s m next) := by
  cases op with
  | reg r => exact keeps_same _ _
  | mem a => exact keeps_store _

theorem keeps_map {m : Memory} {o : Option (State × Memory)} (h : KeepsGrows m o)
    (f : State × Memory → State) : KeepsGrows m (o.map fun r => (f r, r.2)) := by
  rintro s m' h'
  cases ho : o with
  | none => simp [ho] at h'
  | some r =>
    simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨-, rfl⟩ := h'
    exact h _ _ ho

theorem keeps_aluStep (sz : Sz) (op : AluOp) (dst : RM) (y : BitVec sz.bits) (s : State)
    (m : Memory) (next : Word) : KeepsGrows m (aluStep sz op dst y s m next) := by
  unfold aluStep
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keeps_same _ _
    · exact keeps_map (keeps_writeRM sz dst _ s m next) _

theorem keeps_aluStepR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) (s : State)
    (m : Memory) (next : Word) : KeepsGrows m (aluStepR sz op dst src s m next) := by
  unfold aluStepR
  split
  · rintro _ _ ⟨⟩
  · split <;> exact keeps_same _ _

theorem keeps_pushWord (s : State) (m : Memory) (v : Word) :
    KeepsGrows m (pushWord s m v) := by
  rintro s' m' h
  exact Grows.of_stored (Stored.of_pushWord h)

theorem retire_grows {m : Memory} {next : Word} {o : Option (State × Memory)}
    (h : KeepsGrows m o) {core : State} {m' : Memory} (he : retire next o = .ok core m') :
    Grows m m' := by
  unfold retire at he
  split at he
  · cases he
    exact h _ _ rfl
  · cases he

theorem keeps_pushWord' {s : State} {m : Memory} {v : Word} {t : State} {m' : Memory}
    (h : pushWord s m v = some (t, m')) : Grows m m' :=
  keeps_pushWord s m v t m' h

/-- **An instruction keeps the map and the backing.** -/
theorem exec_grows {i : Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : exec i s m len = .ok core m') : Grows m m' := by
  cases i
  all_goals try (unfold exec at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; exact Grows.refl _)
    | (cases h; exact keeps_pushWord' ‹_›)
    | (refine retire_grows ?_ h
       first
        | with_reducible apply keeps_same
        | with_reducible apply keeps_map_same
        | with_reducible apply keeps_writeRM
        | with_reducible apply keeps_writeNarrow
        | with_reducible apply keeps_writeRM8
        | with_reducible apply keeps_aluStep
        | with_reducible apply keeps_aluStepR
        | with_reducible apply keeps_pushWord
        | with_reducible apply keeps_store
        | (with_reducible apply keeps_map; with_reducible apply keeps_writeRM)
        | exact keeps_pushWord _ _ _
        | apply keeps_map_same)

end Silmaril.X86.Ext.Backing
