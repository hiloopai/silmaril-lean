module

public import Silmaril.X86.Concurrency.Bridge.PoolRun.Defs

/-!
# Every branch of the litmus symbolic step has the recorded shape

`stepSym_shape`: the actions of a branch of `stepSym` are fences that read and
write nothing (inert instructions), or one unlocked load or store, or one read-modify-write, of
4 or 8 bytes (1 for `mov m8, imm8` and `mov r8, m8`) with byte lists of that size. So the
`Shape` hypothesis of a recorded pool run (`StepA`) is met by every step that a real step
`XStep` (`Bridge.xstep_of_step`) gives.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86 (State)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (Act stepSym memStep storeStep store8Step rmwStep valBytes)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Bridge.PoolRun

theorem sz_pos (sz : Silmaril.X86.Ext.Sz) : 0 < sz.bytes := by cases sz <;> decide

theorem shape_single {a : XAct} (hk : ∀ k, a.ev.kind ≠ .fence k)
    (hl : a.ev.kind = .load → a.ev.locked = false) (hs : a.ev.kind = .store → a.ev.locked = false)
    (hpos : 0 < a.ev.size) (hrd : a.ev.kind.reads = true → a.rd.length = a.ev.size)
    (hwr : a.ev.kind.writes = true → a.wr.length = a.ev.size) : Shape [a] :=
  .inr ⟨a, rfl, hk, hl, hs, hpos, hrd, hwr⟩

theorem storeStep_shape {R sz a v s next outs} (h : storeStep R sz a v s next = some outs) :
    ∀ o ∈ outs, Shape o.1 := by
  simp only [storeStep] at h
  split at h
  · cases h
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact shape_single (by simp) (by simp) (by simp) (sz_pos sz)
      (by simp [MemEvent.Kind.reads]) (by simp)
  · cases h

theorem store8Step_shape {R a v s next outs} (h : store8Step R a v s next = some outs) :
    ∀ o ∈ outs, Shape o.1 := by
  simp only [store8Step] at h
  split at h
  · cases h
    intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact shape_single (by simp) (by simp) (by simp) Nat.one_pos
      (by simp [MemEvent.Kind.reads]) (by simp)
  · cases h

theorem rmwStep_shape {R dom sz lk a s next f outs}
    (h : rmwStep R dom sz lk a s next f = some outs) : ∀ o ∈ outs, Shape o.1 := by
  simp only [rmwStep] at h
  split at h
  · cases h
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨v, -, rfl⟩ := ho
    exact shape_single (by simp) (by simp) (by simp) (sz_pos sz)
      (by simp [valBytes]) (by simp)
  · cases h

theorem memStep_shape {R dom i s n outs} (h : memStep R dom i s n = some outs) :
    ∀ o ∈ outs, Shape o.1 := by
  unfold memStep at h
  split at h
  · exact storeStep_shape h
  · exact storeStep_shape h
  · dsimp only at h
    split at h
    · cases h
      intro o ho
      simp only [List.mem_map] at ho
      obtain ⟨v, -, rfl⟩ := ho
      exact shape_single (by simp) (by simp) (by simp) (sz_pos _) (by simp [valBytes])
        (by simp [MemEvent.Kind.writes])
    · cases h
  · exact rmwStep_shape h
  · exact rmwStep_shape h
  · exact rmwStep_shape h
  · dsimp only at h
    split at h
    · cases h
      intro o ho
      simp only [List.mem_map] at ho
      obtain ⟨v, -, rfl⟩ := ho
      exact shape_single (by simp) (by simp) (by simp) Nat.one_pos (by simp [valBytes])
        (by simp [MemEvent.Kind.writes])
    · cases h
  · exact store8Step_shape h
  · exact rmwStep_shape h
  · exact rmwStep_shape h
  · split at h
    · cases h
    · exact rmwStep_shape h
  · cases h

theorem kind_of_inert {e : MemEvent.Event} (h : Silmaril.X86.Litmus.Event.inert e = true) :
    ∃ k, e.kind = .fence k := by
  cases hk : e.kind with
  | fence k => exact ⟨k, rfl⟩
  | _ => simp [Silmaril.X86.Litmus.Event.inert, hk, MemEvent.Kind.reads,
      MemEvent.Kind.writes] at h

/-- **Every branch of `stepSym` has the recorded shape.** -/
theorem stepSym_shape {t : Silmaril.X86.Litmus.Thread} {dom : List Nat} {s : State}
    {outs : List (List XAct × State)} (h : stepSym t dom s = some outs) :
    ∀ o ∈ outs, Shape o.1 := by
  unfold stepSym at h
  split at h
  · cases h
  · rename_i i n _
    dsimp only at h
    by_cases hall : (MemEvent.atomic9Accesses i s n).all Silmaril.X86.Litmus.Event.inert = true
    · simp only [hall, ite_true] at h
      split at h
      · cases h
        intro o ho
        simp only [List.mem_singleton] at ho
        subst ho
        left
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨e, he, rfl⟩ := ha
        rw [List.all_eq_true] at hall
        exact ⟨kind_of_inert (hall e he), rfl, rfl⟩
      · cases h
    · simp only [hall, Bool.false_eq_true, ite_false] at h
      exact memStep_shape h

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
