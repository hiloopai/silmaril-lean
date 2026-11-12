module

public import Silmaril.X86.Open9.Defs
public import Silmaril.X86.Ext.Regions

/-! # The machine step's memory frame: no mapping change, writes only to writable bytes

`WFrame m m'`: `m'` has the regions of `m`, and every byte that `m` does not permit writing is
unchanged. Every instruction of `X86.Ext` (`exec_wframe`), of `Ext8`'s new forms
(`execNew8_wframe`) and of `Ext9`'s new forms (`execNew9_wframe`) keeps it, so a step of the
open machine `Open9.step` does (`open9_step_wframe`). The proof follows `Ext.exec_regions`:
every store goes through `Memory.writeBytes`, which checks write permission.

Used for invariants of the process (`Proc.proc`) that concern unmapped or read-only memory: a
program step neither maps memory nor writes a read-only byte.
-/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.Proc.StepFrame

open Silmaril.X86 (Reg Word Byte State MState pushWord AluOp)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext

/-- Same regions; bytes not writable before are unchanged. -/
def WFrame (m m' : Memory) : Prop :=
  m'.regions = m.regions ∧ ∀ a, m.permits .write a = false → m'.bytes.get? a = m.bytes.get? a

theorem wframe_refl (m : Memory) : WFrame m m := ⟨rfl, fun _ _ => rfl⟩

theorem WFrame.trans {m₁ m₂ m₃ : Memory} (h₁ : WFrame m₁ m₂) (h₂ : WFrame m₂ m₃) : WFrame m₁ m₃ := by
  refine ⟨h₂.1.trans h₁.1, fun a ha => ?_⟩
  have hp : m₂.permits .write a = m₁.permits .write a := by
    unfold Memory.permits; rw [h₁.1]
  rw [h₂.2 a (by rw [hp]; exact ha), h₁.2 a ha]

theorem writeBytes_wframe {m m' : Memory} {a : Nat} {l : List Byte} (h : m.writeBytes a l = some m') :
    WFrame m m' := by
  have hw := Memory.writeBytes_writesOnly h
  refine ⟨hw.1, fun x hx => hw.2 x ?_⟩
  unfold Memory.writeBytes at h
  split at h
  · rename_i hc
    rw [Memory.checkSpan_iff] at hc
    by_contra hn
    have := hc.2.2 (x - a) (by omega)
    rw [show a + (x - a) = x by omega, hx] at this
    exact absurd this (by simp)
  · cases h

theorem storeN_wframe {m m' : Memory} {a : Word} {k : Nat} {v : Word} (h : storeN m a k v = some m') :
    WFrame m m' := writeBytes_wframe h

theorem pushWord_wframe {s t : State} {m m' : Memory} {v : Word} (h : pushWord s m v = some (t, m')) :
    WFrame m m' := by
  simp only [pushWord, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨_, hw, _, rfl⟩ := h
  exact writeBytes_wframe hw

/-- Results of an instruction body that keep the frame of `m`. -/
def KeepsW (m : Memory) (o : Option (State × Memory)) : Prop :=
  ∀ s m', o = some (s, m') → WFrame m m'

theorem keepsW_same (m : Memory) (s : State) : KeepsW m (some (s, m)) := by
  rintro _ _ ⟨⟩
  exact wframe_refl _

theorem keepsW_map_same {α : Type} (m : Memory) (o : Option α) (f : α → State) :
    KeepsW m (o.map fun x => (f x, m)) := by
  rintro s m' h
  cases o with
  | none => simp at h
  | some x =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact wframe_refl _

theorem keepsW_store {m : Memory} {a : Word} {k : Nat} {v : Word} (s : State) :
    KeepsW m ((storeN m a k v).map fun after => (s, after)) := by
  rintro s' m' h
  cases hs : storeN m a k v with
  | none => simp [hs] at h
  | some m'' =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact storeN_wframe hs

theorem keepsW_writeRM (sz : Sz) (op : RM) (v : BitVec sz.bits) (s : State) (m : Memory)
    (next : Word) : KeepsW m (writeRM sz op v s m next) := by
  cases op with
  | reg r => exact keepsW_same _ _
  | mem a => exact keepsW_store _

theorem keepsW_writeNarrow (n : Narrow) (op : RM) (v : BitVec n.bits) (s : State)
    (m : Memory) (next : Word) : KeepsW m (writeNarrow n op v s m next) := by
  cases op with
  | reg r => exact keepsW_same _ _
  | mem a => exact keepsW_store _

theorem keepsW_writeRM8 (op : RM) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsW m (writeRM8 op v s m next) := by
  cases op with
  | reg r => exact keepsW_same _ _
  | mem a => exact keepsW_store _

theorem keepsW_map {m : Memory} {o : Option (State × Memory)} (h : KeepsW m o)
    (f : State × Memory → State) : KeepsW m (o.map fun r => (f r, r.2)) := by
  rintro s m' h'
  cases ho : o with
  | none => simp [ho] at h'
  | some r =>
    simp only [ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨-, rfl⟩ := h'
    exact h _ _ ho

theorem keepsW_aluStep (sz : Sz) (op : AluOp) (dst : RM) (y : BitVec sz.bits) (s : State)
    (m : Memory) (next : Word) : KeepsW m (aluStep sz op dst y s m next) := by
  unfold aluStep
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsW_same _ _
    · exact keepsW_map (keepsW_writeRM sz dst _ s m next) _

theorem keepsW_aluStepR (sz : Sz) (op : AluOp) (dst : Reg) (src : RM) (s : State)
    (m : Memory) (next : Word) : KeepsW m (aluStepR sz op dst src s m next) := by
  unfold aluStepR
  split
  · rintro _ _ ⟨⟩
  · split <;> exact keepsW_same _ _

theorem keepsW_pushWord (s : State) (m : Memory) (v : Word) : KeepsW m (pushWord s m v) := by
  rintro s' m' h
  exact pushWord_wframe h

theorem retire_wframe {m : Memory} {next : Word} {o : Option (State × Memory)}
    (h : KeepsW m o) {core : State} {m' : Memory} (he : retire next o = .ok core m') :
    WFrame m m' := by
  unfold retire at he
  split at he
  · cases he
    exact h _ _ rfl
  · cases he

/-- **An instruction of `X86.Ext` keeps the frame.** -/
theorem exec_wframe {i : Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : exec i s m len = .ok core m') : WFrame m m' := by
  cases i
  all_goals (unfold exec at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; exact wframe_refl _)
    | (cases h; exact pushWord_wframe ‹_›)
    | (refine retire_wframe ?_ h
       first
        | with_reducible apply keepsW_map_same
        | with_reducible apply keepsW_writeRM
        | with_reducible apply keepsW_writeNarrow
        | with_reducible apply keepsW_writeRM8
        | with_reducible apply keepsW_aluStep
        | with_reducible apply keepsW_aluStepR
        | with_reducible apply keepsW_pushWord
        | with_reducible apply keepsW_store
        | (with_reducible apply keepsW_map; with_reducible apply keepsW_writeRM)
        | exact keepsW_pushWord _ _ _
        | apply keepsW_map_same)


/-! ## `Ext8`'s new forms -/

theorem keepsW_rm8 (op : Silmaril.X86.Ext8.RM8) (v : BitVec 8) (s : State) (m : Memory) (next : Word) :
    KeepsW m (op.write v s m next) := by
  cases op with
  | reg r => exact keepsW_same _ _
  | mem a => exact keepsW_store _

theorem keepsW_alu8 (op : AluOp) (dst : Silmaril.X86.Ext8.RM8) (y : BitVec 8) (s : State) (m : Memory)
    (next : Word) : KeepsW m (Silmaril.X86.Ext8.alu8 op dst y s m next) := by
  unfold Silmaril.X86.Ext8.alu8
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsW_same _ _
    · exact keepsW_map (keepsW_rm8 dst _ s m next) _

theorem execNew8_wframe {i : Silmaril.X86.Ext8.New} {s : State} {m : Memory} {next : Word} {core : State}
    {m' : Memory} (h : Silmaril.X86.Ext8.execNew i s m next = .ok core m') : WFrame m m' := by
  cases i
  all_goals (unfold Silmaril.X86.Ext8.execNew at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; exact wframe_refl _)
    | (refine retire_wframe ?_ h
       first
        | with_reducible apply keepsW_alu8
        | with_reducible apply keepsW_rm8
        | (with_reducible apply keepsW_map; with_reducible apply keepsW_rm8)
        | with_reducible apply keepsW_map_same)

theorem exec8_wframe {i : Silmaril.X86.Ext8.Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : Silmaril.X86.Ext8.exec i s m len = .ok core m') : WFrame m m' := by
  cases i with
  | base i => exact exec_wframe h
  | new i => exact execNew8_wframe h

/-! ## `Ext9`'s new forms -/

theorem carryStep_wframe {sz : Sz} {sub : Bool} {dst : RM} {y : BitVec sz.bits} {s : State} {m : Memory}
    {next : Word} {core : State} {m' : Memory}
    (h : Silmaril.X86.Ext9.carryStep sz sub dst y s m next = .ok core m') : WFrame m m' := by
  unfold Silmaril.X86.Ext9.carryStep at h
  repeat' split at h
  all_goals first
    | contradiction
    | exact retire_wframe (keepsW_map (keepsW_writeRM sz dst _ s m next) _) h

theorem keepsW_alu16 (op : AluOp) (dst : RM) (y : BitVec 16) (s : State) (m : Memory) (next : Word) :
    KeepsW m (Silmaril.X86.Ext9.alu16 op dst y s m next) := by
  unfold Silmaril.X86.Ext9.alu16
  split
  · rintro _ _ ⟨⟩
  · split
    · exact keepsW_same _ _
    · exact keepsW_map (keepsW_writeNarrow .w dst _ s m next) _

theorem keepsW_test16 (dst : RM) (y : BitVec 16) (s : State) (m : Memory) (next : Word) :
    KeepsW m (Silmaril.X86.Ext9.test16 dst y s m next) := by
  unfold Silmaril.X86.Ext9.test16
  exact keepsW_map_same _ _ _

theorem execNew9_wframe {i : Silmaril.X86.Ext9.New} {s : State} {m : Memory} {next : Word} {core : State}
    {m' : Memory} (h : Silmaril.X86.Ext9.execNew i s m next = .ok core m') : WFrame m m' := by
  cases i
  all_goals (unfold Silmaril.X86.Ext9.execNew at h; dsimp only at h)
  all_goals repeat' split at h
  all_goals first
    | contradiction
    | (cases h; done)
    | (cases h; exact wframe_refl _)
    | (cases h; exact pushWord_wframe ‹_›)
    | exact carryStep_wframe h
    | exact exec_wframe h
    | (refine retire_wframe ?_ h
       first
        | with_reducible apply keepsW_alu16
        | exact keepsW_alu16 _ _ _ _ _ _
        | with_reducible apply keepsW_test16
        | with_reducible apply keepsW_pushWord
        | with_reducible apply keepsW_map_same)

theorem exec9_wframe {i : Silmaril.X86.Ext9.Instr} {s : State} {m : Memory} {len : Nat} {core : State}
    {m' : Memory} (h : Silmaril.X86.Ext9.exec i s m len = .ok core m') : WFrame m m' := by
  cases i with
  | ext8 i => exact exec8_wframe h
  | new i => exact execNew9_wframe h

/-! ## The open machine -/

theorem ofResult_some {r : Result} {m' : MState} (h : Silmaril.X86.Open.ofResult r = some m') :
    r = .ok m'.core m'.memory := by
  unfold Silmaril.X86.Open.ofResult at h
  split at h
  · cases h; rfl
  · cases h

theorem open_step_wframe {m m' : MState} (h : Silmaril.X86.Open.step m = some m') :
    WFrame m.memory m'.memory := by
  unfold Silmaril.X86.Open.step at h
  split at h
  · exact exec_wframe (ofResult_some h)
  · exact execNew8_wframe (ofResult_some h)
  · cases h

/-- **A step of the open machine keeps the memory map and writes only writable bytes.** -/
theorem open9_step_wframe {m m' : MState} (h : Silmaril.X86.Open9.step m = some m') :
    WFrame m.memory m'.memory := by
  unfold Silmaril.X86.Open9.step at h
  split at h
  · split at h
    · exact execNew9_wframe (ofResult_some h)
    · cases h
  · exact open_step_wframe h

end Silmaril.Elf.Link.Dyn.Proc.StepFrame
