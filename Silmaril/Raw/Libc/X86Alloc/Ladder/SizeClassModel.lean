module

public import Silmaril.Libc.X86Alloc.Ladder.SizeClass.Defs
public import Silmaril.X86.Sep.Alloc.Thms

/-! # Proofs: rung 07 (size classes) — views of the state and the three postconditions

`mm_view` isolates one class `c` of the allocator's memory (its head and list) from the other
three (`others s c`), the arena and the rest. `post_pop`, `post_bump` and `post_push` close the
three non-failing exits (pop a class list, carve the arena, push onto a class list). -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass

open Silmaril.X86 (Word Byte Reg)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Alloc
open Silmaril.Libc.X86Alloc
open Silmaril.Libc.X86Alloc.Ladder.SizeClass

/-- A class size. -/
def IsCls (c : Nat) : Prop := c = 16 ∨ c = 32 ∨ c = 64 ∨ c = 128

theorem isCls_cls (n : Nat) : IsCls (cls n) := by
  unfold cls IsCls; split_ifs <;> simp

theorem le_cls (n : Nat) (hn : n ≤ 128) : n ≤ cls n := by
  unfold cls; split_ifs <;> omega

theorem IsCls.facts {c : Nat} (h : IsCls c) : 16 ≤ c ∧ c ≤ 128 ∧ c % 16 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem others_zero {c : Nat} (hc : IsCls c) (s : St) :
    others s 0 = (hd c (s.lst c) ∗ others s c) := by
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [others, St.lst, reduceIte, Nat.reduceEqDiff, emp_sep, sep_emp] <;> ac_rfl

theorem others_set {c : Nat} (hc : IsCls c) (s : St) (l : List Word) :
    others (s.set c l) c = others s c := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [others, St.set, reduceIte, Nat.reduceEqDiff]

theorem lst_set {c : Nat} (hc : IsCls c) (s : St) (l : List Word) : (s.set c l).lst c = l := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [St.lst, St.set, reduceIte, Nat.reduceEqDiff]

theorem u_set {c : Nat} (hc : IsCls c) (s : St) (l : List Word) : (s.set c l).u = s.u := by
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [St.set, reduceIte, Nat.reduceEqDiff]

/-- **One class of the state.** -/
theorem mm_view {c : Nat} (hc : IsCls c) (s : St) :
    iface.mmS s = (⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ hd c (s.lst c) ∗ others s c ∗ arenaPt s.u ∗
      strue) := by
  show (⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ others s 0 ∗ arenaPt s.u ∗ strue) = _
  rw [others_zero hc]; ac_rfl

theorem mm_set {c : Nat} (hc : IsCls c) (s : St) (l : List Word) :
    iface.mmS (s.set c l) = (⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗ hd c l ∗ others s c ∗ arenaPt s.u ∗
      strue) := by
  rw [mm_view hc, lst_set hc, others_set hc, u_set hc]

theorem mm_bump {c : Nat} (hc : IsCls c) (s : St) (u' : Nat) :
    iface.mmS ({ s with u := u' } : St) = (⌜u' ≤ 4096 ∧ u' % 16 = 0⌝ ∗ hd c (s.lst c) ∗
      others s c ∗ arenaPt u' ∗ strue) :=
  mm_view hc { s with u := u' }

/-- A block of class `c` from its first word and the rest, split at `n ≤ c`. -/
theorem block_split (p : Nat) (q : Word) (c n : Nat) (h8 : 8 ≤ c) (hn : n ≤ c) :
    (wordPt p q ∗ blockAny (p + 8) (c - 8)) ⊢ₛ (blockAny p n ∗ blockAny (p + n) (c - n)) := by
  refine entails_trans (sep_mono_left _ (wordPt_blockAny _ _)) (entails_of_eq ?_)
  rw [← blockAny_add, ← blockAny_add, Nat.add_sub_cancel' h8, Nat.add_sub_cancel' hn]

theorem block_join (p c n : Nat) (h8 : 8 ≤ c) (hn : n ≤ c) :
    (blockAny p n ∗ blockAny (p + n) (c - n)) = (blockAny p 8 ∗ blockAny (p + 8) (c - 8)) := by
  rw [← blockAny_add, ← blockAny_add, Nat.add_sub_cancel' h8, Nat.add_sub_cancel' hn]

/-- A failing call. -/
theorem post_fail (s : St) (n : Word) (hm : ref.malloc s n.toNat = 0) {M : SProp}
    (hM : M ⊢ₛ iface.mmS s) (v : Word) (hv : v = 0) :
    M ⊢ₛ (mallocSpecF iface).post (s, n) v := by
  subst hv
  show M ⊢ₛ (⌜(0 : Word) = ref.malloc s n.toNat⌝ ∗ sor (⌜(0 : Word) = 0⌝ ∗ iface.mmS s) _)
  exact spure_sep_intro hm.symm (entails_trans (spure_sep_intro rfl hM) (sor_intro_left _ _))

/-- **Popping the list of class `c`.** -/
theorem post_pop (s : St) (n : Word) (p q : Word) (ps : List Word)
    (hn : n.toNat ≤ 128) (hl : s.lst (cls n.toNat) = p :: ps) (hi : s.u ≤ 4096 ∧ s.u % 16 = 0)
    (hp : p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat) (v : Word) (hv : v = p) :
    (wordPt (headA (cls n.toNat)) q ∗ wordPt p.toNat q ∗
      wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + 8) (cls n.toNat - 8) ∗ clist (cls n.toNat) ps q ∗
      others s (cls n.toNat) ∗ arenaPt s.u ∗ strue) ⊢ₛ
      (mallocSpecF iface).post (s, n) v := by
  subst v
  have hc := isCls_cls n.toNat
  have hcf := hc.facts
  have hle := le_cls n.toNat hn
  have hm : ref.malloc s n.toNat = p := by
    simp only [ref, show ¬ 128 < n.toNat by omega, ite_false, hl]
  have ha : ref.alloc s n.toNat = s.set (cls n.toNat) ps := by simp only [ref, hl]
  show _ ⊢ₛ (⌜p = ref.malloc s n.toNat⌝ ∗ sor (⌜p = 0⌝ ∗ iface.mmS s)
    ((⌜p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗ (⌜n.toNat ≤ 128 ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
      wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + n.toNat) (cls n.toNat - n.toNat)) ∗ blockAny p.toNat n.toNat) ∗
      iface.mmS (ref.alloc s n.toNat)))
  rw [ha, mm_set hc]
  refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
  refine entails_trans ?_ (entails_of_eq (show (⌜p ≠ 0 ∧ p.toNat % 16 = 0⌝ ∗
    ⌜n.toNat ≤ 128 ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗ ⌜s.u ≤ 4096 ∧ s.u % 16 = 0⌝ ∗
    ((blockAny p.toNat n.toNat ∗ blockAny (p.toNat + n.toNat) (cls n.toNat - n.toNat)) ∗
      (wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
      hd (cls n.toNat) ps ∗ others s (cls n.toNat) ∗ arenaPt s.u ∗ strue))) = _ by ac_rfl))
  refine spure_sep_intro ⟨hp.1, hp.2.1⟩ (spure_sep_intro ⟨hn, hp⟩ (spure_sep_intro hi ?_))
  refine entails_trans (entails_of_eq (show _ = ((wordPt p.toNat q ∗
    blockAny (p.toNat + 8) (cls n.toNat - 8)) ∗ (wordPt (p.toNat - 16)
      (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (p.toNat - 8) 8 ∗
      (wordPt (headA (cls n.toNat)) q ∗ clist (cls n.toNat) ps q) ∗ others s (cls n.toNat) ∗
      arenaPt s.u ∗ strue)) by ac_rfl)) (sep_mono (block_split _ _ _ _ (by omega) hle) ?_)
  exact sep_mono_right _ (sep_mono_right _ (sep_mono_left _ (sexists_intro q (entails_refl _))))

/-- **Carving a block of class `c` off the arena.** -/
theorem post_bump (s : St) (n : Word) (hn : n.toNat ≤ 128) (hl : s.lst (cls n.toNat) = [])
    (hi : s.u ≤ 4096 ∧ s.u % 16 = 0) (hfit : cls n.toNat + 16 ≤ 4096 - s.u) (w v : Word)
    (hw : w = BitVec.ofNat 64 (s.u + cls n.toNat + 16))
    (hv : v = BitVec.ofNat 64 (arena + s.u + 16)) :
    (wordPt usedA w ∗ wordPt (arena + s.u) (BitVec.ofNat 64 (cls n.toNat)) ∗
      blockAny (arena + s.u + 8) 8 ∗ blockAny (arena + s.u + 16) (4096 - s.u - 16) ∗
      wordPt (headA (cls n.toNat)) 0 ∗ others s (cls n.toNat) ∗ strue) ⊢ₛ
      (mallocSpecF iface).post (s, n) v := by
  subst hw hv
  have hc := isCls_cls n.toNat
  have hcf := hc.facts
  have hle := le_cls n.toNat hn
  have hvn : (BitVec.ofNat 64 (arena + s.u + 16)).toNat = arena + s.u + 16 := by
    simp only [BitVec.toNat_ofNat, arena]; omega
  have hv0 : BitVec.ofNat 64 (arena + s.u + 16) ≠ 0 := by
    intro e; have := congrArg BitVec.toNat e; rw [hvn] at this; simp at this
  have hm : ref.malloc s n.toNat = BitVec.ofNat 64 (arena + s.u + 16) := by
    simp only [ref, show ¬ 128 < n.toNat by omega, ite_false, hl, hfit, ite_true]
  have ha : ref.alloc s n.toNat = { s with u := s.u + cls n.toNat + 16 } := by
    simp only [ref, hl]
  set c := cls n.toNat with hcdef
  set v := BitVec.ofNat 64 (arena + s.u + 16) with hvdef
  have hal : (arena + s.u + 16) % 16 = 0 := by simp only [arena]; omega
  show _ ⊢ₛ (⌜v = ref.malloc s n.toNat⌝ ∗ sor (⌜v = 0⌝ ∗ iface.mmS s)
    ((⌜v ≠ 0 ∧ v.toNat % 16 = 0⌝ ∗ (⌜n.toNat ≤ 128 ∧ v ≠ 0 ∧ v.toNat % 16 = 0 ∧ 16 ≤ v.toNat⌝ ∗
      wordPt (v.toNat - 16) (BitVec.ofNat 64 (cls n.toNat)) ∗ blockAny (v.toNat - 8) 8 ∗
      blockAny (v.toNat + n.toNat) (cls n.toNat - n.toNat)) ∗ blockAny v.toNat n.toNat) ∗
      iface.mmS (ref.alloc s n.toNat)))
  rw [ha, ← hcdef, hvn]
  refine spure_sep_intro hm.symm (entails_trans ?_ (sor_intro_right _ _))
  refine entails_trans ?_ (sep_mono_right _ (entails_of_eq (mm_bump hc s _).symm))
  have hsplit : blockAny (arena + s.u + 16) (4096 - s.u - 16) = (blockAny (arena + s.u + 16) n.toNat ∗
      blockAny (arena + s.u + 16 + n.toNat) (c - n.toNat) ∗
      blockAny (arena + (s.u + c + 16)) (4096 - (s.u + c + 16))) := by
    rw [show 4096 - s.u - 16 = n.toNat + ((c - n.toNat) + (4096 - (s.u + c + 16))) by omega,
      blockAny_add, blockAny_add,
      show arena + s.u + 16 + n.toNat + (c - n.toNat) = arena + (s.u + c + 16) by omega]
  rw [hsplit, show arena + s.u + 16 - 16 = arena + s.u by omega,
    show arena + s.u + 16 - 8 = arena + s.u + 8 by omega]
  rw [hl]
  refine entails_trans ?_ (entails_of_eq (show (⌜v ≠ 0 ∧ (arena + s.u + 16) % 16 = 0⌝ ∗
    ⌜n.toNat ≤ 128 ∧ v ≠ 0 ∧ (arena + s.u + 16) % 16 = 0 ∧ 16 ≤ arena + s.u + 16⌝ ∗
    ⌜s.u + c + 16 ≤ 4096 ∧ (s.u + c + 16) % 16 = 0⌝ ∗
    ((wordPt (arena + s.u) (BitVec.ofNat 64 c) ∗ blockAny (arena + s.u + 8) 8 ∗
      blockAny (arena + s.u + 16 + n.toNat) (c - n.toNat) ∗ blockAny (arena + s.u + 16) n.toNat) ∗
      hd c [] ∗ others s c ∗ arenaPt (s.u + c + 16) ∗ strue)) = _ by
    simp only [Nat.add_assoc]; ac_rfl))
  refine spure_sep_intro ⟨hv0, hal⟩ (spure_sep_intro ⟨hn, hv0, hal, by omega⟩
    (spure_sep_intro ⟨by omega, by omega⟩ ?_))
  have hhd : wordPt (headA c) 0 ⊢ₛ hd c [] :=
    sexists_intro 0 (entails_trans (entails_of_eq (sep_emp _).symm)
      (sep_mono_right _ (entails_of_eq (by show emp = ⌜(0 : Word) = 0⌝; rw [eq_self, spure_true_emp]))))
  refine entails_trans ?_ (sep_mono_right _ (sep_mono_left _ hhd))
  unfold arenaPt
  refine entails_trans ?_ (entails_of_eq (show ((wordPt (arena + s.u) (BitVec.ofNat 64 c) ∗
      blockAny (arena + s.u + 8) 8 ∗ blockAny (arena + s.u + 16 + n.toNat) (c - n.toNat) ∗
      blockAny (arena + s.u + 16) n.toNat) ∗ wordPt (headA c) 0 ∗ others s c ∗
      (wordPt usedA (BitVec.ofNat 64 (s.u + c + 16)) ∗
        blockAny (arena + (s.u + c + 16)) (4096 - (s.u + c + 16))) ∗ strue) = _ by
    simp only [Nat.add_assoc]))
  exact entails_of_eq (by ac_rfl)

/-- **Pushing a block onto the list of its class.** -/
theorem post_push (s : St) (p h : Word) (n : Nat) (hi : s.u ≤ 4096 ∧ s.u % 16 = 0)
    (hp : p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat) :
    (wordPt p.toNat h ∗ wordPt (headA (cls n)) p ∗
      wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
      blockAny (p.toNat + 8) (cls n - 8) ∗ clist (cls n) (s.lst (cls n)) h ∗
      others s (cls n) ∗ arenaPt s.u ∗ strue) ⊢ₛ iface.mmS (ref.dealloc s p n) := by
  have hc := isCls_cls n
  show _ ⊢ₛ iface.mmS (s.set (cls n) (p :: s.lst (cls n)))
  rw [mm_set hc]
  refine spure_sep_intro hi ?_
  refine entails_trans ?_ (sep_mono_left _ (sexists_intro p (entails_refl _)))
  refine entails_trans ?_ (entails_of_eq (show ((wordPt (headA (cls n)) p ∗
    (⌜p = p ∧ p ≠ 0 ∧ p.toNat % 16 = 0 ∧ 16 ≤ p.toNat⌝ ∗
      wordPt (p.toNat - 16) (BitVec.ofNat 64 (cls n)) ∗ blockAny (p.toNat - 8) 8 ∗
      sexists fun q => wordPt p.toNat q ∗ blockAny (p.toNat + 8) (cls n - 8) ∗
        clist (cls n) (s.lst (cls n)) q)) ∗ others s (cls n) ∗ arenaPt s.u ∗ strue) = _ by
    simp only [clist]))
  refine entails_trans ?_ (sep_mono_left _ (sep_mono_right _ (spure_sep_intro ⟨rfl, hp⟩
    (sep_mono_right _ (sep_mono_right _ (sexists_intro h (entails_refl _)))))))
  exact entails_of_eq (by ac_rfl)

end Silmaril.Raw.Libc.X86Alloc.Ladder.SizeClass
