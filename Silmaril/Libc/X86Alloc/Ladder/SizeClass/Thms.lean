module

public import Silmaril.Libc.X86Alloc.Ladder.SizeClass.Defs
public import Silmaril.Libc.X86Alloc.Pinned.SizeClass
public import Silmaril.Libc.X86Alloc.Spec.Thms
public import Silmaril.X86.Ladder.Pinned.Thms
import Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClassFree

/-!
# Rung 07 (`sizeclass`): results

* `malloc_sat`, `free_sat`: the code meets the size-class reference model `ref` on `Open.isa`
  (per-class LIFO reuse, then the arena; `free` reads the class from the block's header).
* `init`: the loaded static state (all zero) is `s0`: empty lists, an unused arena.
* `code_loaded`, `data_loaded`: the pinned executable loads the layout (kernel evaluation).
-/

@[expose] public section

namespace Silmaril.Libc.X86Alloc.Ladder.SizeClass

open Silmaril.X86.Sep
open Silmaril.Libc.X86Alloc

theorem malloc_sat :
    (mallocSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.mallocAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass.malloc_sat

theorem free_sat :
    (freeSpecF iface).Sat Silmaril.X86.Open.isa layout.C layout.freeAt :=
  Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass.free_sat

theorem init : layout.Init ⊢ₛ iface.mmS s0 := Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass.init

theorem code_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.SizeClass.exe
    "rx" layout.codeAddr layout.code = true := by decide +kernel

theorem data_loaded : Silmaril.X86.Ladder.Pinned.check Silmaril.Libc.X86Alloc.Pinned.SizeClass.exe
    "rw" layout.dataAddr layout.data = true := by decide +kernel

/-- All free blocks. -/
def all (s : St) : List Silmaril.X86.Word := s.l16 ++ s.l32 ++ s.l64 ++ s.l128

/-- The invariant: the arena cursor is in range and free blocks are non-null. -/
def Inv : ref.St → Prop := fun (s : St) => s.u ≤ 4096 ∧ ∀ p ∈ all s, p ≠ 0

theorem isClass_cls (n : Nat) : IsClass (cls n) := by
  unfold cls IsClass; split_ifs <;> simp

theorem mem_lst (s : St) (c : Nat) (p : Silmaril.X86.Word) (h : p ∈ s.lst c) : p ∈ all s := by
  unfold St.lst at h; unfold all; split_ifs at h <;> simp [h]

theorem mem_set (s : St) (c : Nat) (l : List Silmaril.X86.Word) (p : Silmaril.X86.Word)
    (h : p ∈ all (s.set c l)) : p ∈ l ∨ p ∈ all s := by
  unfold St.set at h; unfold all at h ⊢; split_ifs at h <;> simp at h <;> simp <;> tauto

theorem lst_set_self {c : Nat} (hc : IsClass c) (s : St) (l : List Silmaril.X86.Word) :
    (s.set c l).lst c = l := by
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

theorem lst_set_ne {c c' : Nat} (hc : IsClass c) (hc' : IsClass c') (hne : c' ≠ c) (s : St)
    (l : List Silmaril.X86.Word) : (s.set c l).lst c' = s.lst c' := by
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | rfl

theorem α_set {c : Nat} (hc : IsClass c) (s : St) (l : List Silmaril.X86.Word) :
    α (s.set c l) = { α s with k := Function.update (α s).k c l.length, r := 4096 - (s.set c l).u } := by
  simp only [α, CapSt.mk.injEq, and_true]
  funext c'
  by_cases e : c' = c
  · subst e; simp [hc, lst_set_self hc]
  · rw [Function.update_of_ne e]
    by_cases hc' : IsClass c'
    · simp [hc', lst_set_ne hc hc' e]
    · simp [hc']

theorem u_set' {c : Nat} (s : St) (l : List Silmaril.X86.Word) : (s.set c l).u = s.u := by
  unfold St.set; split_ifs <;> rfl

theorem malloc_ne_bump (s : St) (h : s.u ≤ 4096) :
    BitVec.ofNat 64 (arena + s.u + 16) ≠ 0 := by
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, arena] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this; simp at this

theorem sim_avail (s : St) (n : Nat) (hI : Inv s) (ha : cap.avail (α s) n) :
    ref.malloc s n ≠ 0 := by
  obtain ⟨hn, hk⟩ := ha
  have hc := isClass_cls n
  simp only [ref, show ¬ 128 < n by omega, ite_false]
  cases hl : s.lst (cls n) with
  | cons p ps => exact hI.2 p (mem_lst s _ p (by rw [hl]; exact List.mem_cons_self))
  | nil =>
    simp only [α, hc, ite_true, hl, List.length_nil, Nat.lt_irrefl, false_or] at hk
    simp only [hk, ite_true]; exact malloc_ne_bump s hI.1

theorem sim_alloc (s : St) (n : Nat) (hI : Inv s) (hm : ref.malloc s n ≠ 0) :
    Inv (ref.alloc s n) ∧ α (ref.alloc s n) = cap.alloc (α s) n (ref.malloc s n) := by
  have hn : ¬ 128 < n := by intro h; exact hm (by simp only [ref, h, ite_true])
  have hc := isClass_cls n
  cases hl : s.lst (cls n) with
  | cons p ps =>
    show Inv (ref.alloc s n) ∧ α (ref.alloc s n) = cap.alloc (α s) n (ref.malloc s n)
    have ha : ref.alloc s n = s.set (cls n) ps := by simp only [ref, hl]
    have hpos : 0 < (α s).k (cls n) := by simp [α, hc, hl]
    rw [ha]
    refine ⟨⟨by rw [u_set']; exact hI.1, fun q hq => ?_⟩, ?_⟩
    · rcases mem_set s _ _ q hq with h | h
      · exact hI.2 q (mem_lst s _ q (by rw [hl]; exact List.mem_cons_of_mem _ h))
      · exact hI.2 q h
    · show α (s.set (cls n) ps) = if 0 < (α s).k (cls n) then _ else _
      simp only [hpos, ite_true]; rw [α_set hc, u_set']
      simp [α, hc, hl]
  | nil =>
    show Inv (ref.alloc s n) ∧ α (ref.alloc s n) = cap.alloc (α s) n (ref.malloc s n)
    have hfit : cls n + 16 ≤ 4096 - s.u := by
      by_contra h; exact hm (by simp only [ref, hn, ite_false, hl, h])
    have ha : ref.alloc s n = { s with u := s.u + cls n + 16 } := by simp only [ref, hl]
    have hz : ¬ 0 < (α s).k (cls n) := by simp [α, hc, hl]
    rw [ha]
    refine ⟨⟨by show s.u + cls n + 16 ≤ 4096; omega, fun q hq => hI.2 q hq⟩, ?_⟩
    show α { s with u := s.u + cls n + 16 } = if 0 < (α s).k (cls n) then _ else _
    simp only [hz, ite_false]
    simp only [α, CapSt.mk.injEq]
    refine ⟨rfl, by omega⟩

theorem sim_dealloc (s : St) (p : Silmaril.X86.Word) (n : Nat) (hI : Inv s) (hp : p ≠ 0) :
    Inv (ref.dealloc s p n) ∧ α (ref.dealloc s p n) = cap.dealloc (α s) p n := by
  have hc := isClass_cls n
  show Inv (s.set (cls n) (p :: s.lst (cls n))) ∧ α (s.set (cls n) (p :: s.lst (cls n))) = _
  refine ⟨⟨by rw [u_set']; exact hI.1, fun q hq => ?_⟩, ?_⟩
  · rcases mem_set s _ _ q hq with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact hp
      · exact hI.2 q (mem_lst s _ q h)
    · exact hI.2 q h
  · rw [α_set hc, u_set']
    show _ = { (α s) with k := Function.update (α s).k (cls n) ((α s).k (cls n) + 1) }
    simp [α, hc]

/-- **`ref` simulates the size-class capacity model** at `α`. -/
theorem sim : ref.Sim cap α Inv where
  avail := sim_avail
  alloc := sim_alloc
  dealloc := sim_dealloc

theorem inv_s0 : Inv s0 := ⟨by decide, fun _ h => by simp [all, s0] at h⟩

end Silmaril.Libc.X86Alloc.Ladder.SizeClass
