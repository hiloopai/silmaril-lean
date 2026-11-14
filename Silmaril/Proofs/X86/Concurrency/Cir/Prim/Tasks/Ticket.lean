module

public import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Spin

/-!
# The ticket lock is a lock on TSO, for every client

`Task.ticketMutexTso`, proved with the release rule of `Csl.Rel` (`rel_tsoG`) and the ghost
invariant `ticketInvG l B R` (`Prim/Tasks/Defs.lean`):

* **draw** (`lock xadd` on `next`, draining): the thread deposits its permit `D u` and takes the
  ticket token `T Nv`; `Nv` grows by one (`safeR_take`);
* **claim** (the plain load of `serving` that sees the thread's ticket): with `T k` in hand the
  turn `k` cannot be claimed already, so the invariant holds `R`, `G k` and `U k`; the thread takes
  them and a permit, and gives back `T k` (`safeR_wait_ld`). A load that sees another value
  changes nothing. The 32-bit comparison is exact: the tickets in flight are at most the permits
  deposited, and there are at most `B < 2 ^ 32` permits;
* **release** (`ticket_unlock`: load `serving`, add one, plain `mov`): with `G k`, the turn `k` is
  the claimed one, so the load reads `k`; the `mov` of `k + 1` releases `R` and `G k` (the release
  rule's obligation holds in every invariant state disjoint from the holder) (`ticketUnlock_rel`);
* at a finished, drained state ghost conservation and ghost disjointness (`rel_tsoG`) give: no
  turn claimed (every `G` is back), no ticket in flight (every `T` is back, so `Sv = Nv`), and
  exactly `N` turns taken (each thread keeps exactly one receipt `U`, receipts below `Sv` are all
  held), so `next = serving = N`.

The lemmas are stated under the bare invariant; `Csl.Rel.safeR_inv_frame` frames them for the
Mutex interface with ghost state (`Mutex.IfaceG`, `Mutex.ticketMutexG`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.TvCfg (setB notE mask32)

/-! ## Ghost cells -/

theorem tkA_eq {l c k l' c' k' : Nat} (hc : c < 4) (hc' : c' < 4) :
    tkA l c k = tkA l' c' k' ↔ l = l' ∧ c = c' ∧ k = k' := by
  unfold tkA; rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact ⟨rfl, rfl⟩

theorem gsetL_apply (l : Nat) (P : Nat → Nat → Prop) (a : Nat) :
    gsetL l P a = open Classical in
      if ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k then some 0 else none := rfl

theorem gsetL_isSome {l : Nat} {P : Nat → Nat → Prop} {a : Nat} :
    (gsetL l P a).isSome ↔ ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k := by
  rw [gsetL_apply]; split <;> simp_all

theorem gsetL_tk {l : Nat} {P : Nat → Nat → Prop} {c k : Nat} (hc : c < 4) :
    (gsetL l P (tkA l c k)).isSome ↔ P c k := by
  rw [gsetL_isSome]
  constructor
  · rintro ⟨c', k', hc', hp, e⟩
    obtain ⟨-, rfl, rfl⟩ := (tkA_eq hc hc').mp e
    exact hp
  · intro hp; exact ⟨c, k, hc, hp, rfl⟩

theorem gsetL_union (l : Nat) (P P' : Nat → Nat → Prop) :
    Heap.union (gsetL l P) (gsetL l P') = gsetL l (fun c k => P c k ∨ P' c k) := by
  funext a
  rw [union_apply, gsetL_apply, gsetL_apply, gsetL_apply]
  have e3 : (∃ c k, c < 4 ∧ (P c k ∨ P' c k) ∧ a = tkA l c k) ↔
      (∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k) ∨ (∃ c k, c < 4 ∧ P' c k ∧ a = tkA l c k) := by
    constructor
    · rintro ⟨c, k, hc, hp | hp, e⟩
      · exact Or.inl ⟨c, k, hc, hp, e⟩
      · exact Or.inr ⟨c, k, hc, hp, e⟩
    · rintro (⟨c, k, hc, hp, e⟩ | ⟨c, k, hc, hp, e⟩)
      · exact ⟨c, k, hc, Or.inl hp, e⟩
      · exact ⟨c, k, hc, Or.inr hp, e⟩
  by_cases h1 : ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k
  · rw [ite_eq_left h1, ite_eq_left (e3.mpr (Or.inl h1))]; rfl
  · rw [ite_eq_right h1, Option.none_or]
    by_cases h2 : ∃ c k, c < 4 ∧ P' c k ∧ a = tkA l c k
    · rw [ite_eq_left h2, ite_eq_left (e3.mpr (Or.inr h2))]
    · rw [ite_eq_right h2, ite_eq_right (fun h => (e3.mp h).elim h1 h2)]

theorem gsetL_ext {l : Nat} {P P' : Nat → Nat → Prop} (h : ∀ c k, c < 4 → (P c k ↔ P' c k)) :
    gsetL l P = gsetL l P' := by
  funext a
  rw [gsetL_apply, gsetL_apply]
  have : (∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k) ↔ (∃ c k, c < 4 ∧ P' c k ∧ a = tkA l c k) :=
    ⟨fun ⟨c, k, hc, hp, e⟩ => ⟨c, k, hc, (h c k hc).mp hp, e⟩,
      fun ⟨c, k, hc, hp, e⟩ => ⟨c, k, hc, (h c k hc).mpr hp, e⟩⟩
  by_cases h1 : ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k
  · rw [ite_eq_left h1, ite_eq_left (this.mp h1)]
  · rw [ite_eq_right h1, ite_eq_right (mt this.mpr h1)]

theorem gsetL_disj {l : Nat} {P P' : Nat → Nat → Prop}
    (h : ∀ c k, c < 4 → P c k → P' c k → False) : Heap.Disjoint (gsetL l P) (gsetL l P') := by
  intro a
  by_cases h1 : ∃ c k, c < 4 ∧ P c k ∧ a = tkA l c k
  · right
    rw [gsetL_apply, ite_eq_right]
    rintro ⟨c', k', hc', hp', e'⟩
    obtain ⟨c, k, hc, hp, rfl⟩ := h1
    obtain ⟨-, rfl, rfl⟩ := (tkA_eq hc hc').mp e'
    exact h c k hc hp hp'
  · left; rw [gsetL_apply, ite_eq_right h1]

theorem disj_gsetL {l : Nat} {P P' : Nat → Nat → Prop}
    (d : Heap.Disjoint (gsetL l P) (gsetL l P')) {c k : Nat} (hc : c < 4) (hp : P c k)
    (hp' : P' c k) : False := by
  rcases d (tkA l c k) with e | e
  · have := (gsetL_tk (l := l) (P := P) hc).mpr hp; rw [e] at this; cases this
  · have := (gsetL_tk (l := l) (P := P') hc).mpr hp'; rw [e] at this; cases this

theorem gsetL_empty (l : Nat) : gsetL l (fun _ _ => False) = Heap.empty := by
  funext a; rw [gsetL_apply, ite_eq_right (by rintro ⟨_, _, _, h, _⟩; exact h)]; rfl

/-! ## Heap lemmas -/

theorem none_of_disj' {A B : Heap} (d : Heap.Disjoint A B) {a : Nat} (e : (B a).isSome) :
    A a = none := by
  rcases d a with e' | e'
  · exact e'
  · rw [e'] at e; cases e

theorem le_union_right' {A B : Heap} (d : Heap.Disjoint A B) : Heap.Le B (Heap.union A B) := by
  intro a v e; rw [union_apply, none_of_disj' d (by rw [e]; rfl), Option.none_or]; exact e

theorem disjoint_symm' {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_comm' {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext a; rw [union_apply, union_apply]
  rcases d a with e | e <;> rw [e] <;> cases h₁ a <;> cases h₂ a <;> simp_all

theorem tkObj_apply (l Nv Sv x : Nat) : tkObj l Nv Sv x =
    if x = l then some (Nv % 2 ^ 32) else if x = l + 4 then some (Sv % 2 ^ 32) else none := by
  simp only [tkObj, union_apply, single_apply]
  by_cases h1 : x = l
  · simp [h1]
  · simp [h1]

theorem tkObj_disj {l Nv Sv Nv' Sv' : Nat} {X : Heap} (d : Heap.Disjoint (tkObj l Nv Sv) X) :
    Heap.Disjoint (tkObj l Nv' Sv') X := fun x => by
  rcases d x with e | e
  · left; rw [tkObj_apply] at e ⊢; split_ifs at e ⊢; simp_all
  · exact Or.inr e

theorem tkObj_l (l Nv Sv : Nat) : tkObj l Nv Sv l = some (Nv % 2 ^ 32) := by
  rw [tkObj_apply]; simp

theorem tkObj_l4 (l Nv Sv : Nat) : tkObj l Nv Sv (l + 4) = some (Sv % 2 ^ 32) := by
  rw [tkObj_apply]; simp

/-- The invariant's physical heap: the two words, and `R` when unclaimed. -/
theorem inv_l {l Nv Sv : Nat} {hI : Heap} {cl : Bool} {R : HProp}
    (hp : (cl = true ∧ hI = tkObj l Nv Sv) ∨ (cl = false ∧ ∃ hR, R hR ∧
      Heap.Disjoint (tkObj l Nv Sv) hR ∧ hI = Heap.union (tkObj l Nv Sv) hR)) (x : Nat)
    (hx : x = l ∨ x = l + 4) : hI x = tkObj l Nv Sv x := by
  have hs : (tkObj l Nv Sv x).isSome := by
    rw [tkObj_apply]; rcases hx with rfl | rfl <;> simp
  rcases hp with ⟨-, rfl⟩ | ⟨-, hR, -, -, rfl⟩
  · rfl
  · rw [union_apply]; cases e : tkObj l Nv Sv x with
    | none => rw [e] at hs; cases hs
    | some v => rfl

/-! ## Values -/

theorem mask_ofNat {a : Nat} (ha : a < 2 ^ 32) :
    (BitVec.ofNat 64 a &&& 0xffffffff#64) = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp at this; omega
  · rintro rfl; rfl

theorem inc_val (a : Nat) :
    ((BitVec.ofNat 64 a + BitVec.ofNat 64 1 &&& BitVec.ofNat 64 4294967295).toNat) % 2 ^ (8 * 4) =
      (a + 1) % 2 ^ 32 := by
  rw [BitVec.toNat_and, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  rw [show (4294967295 : Nat) % 2 ^ 64 = 2 ^ 32 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem at_rdi4 {rs : Regs} {l : Nat} (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64) :
    ((at_ .rdi 4).eval rs).toNat = l + 4 := by
  simp only [at_, Expr.eval, BinOp.eval, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

theorem truthy_notE_zCmp (rs : Regs) :
    truthy ((notE (zCmp .rax .rdx)).eval rs) =
      !decide ((rs .rax &&& 0xffffffff#64) = (rs .rdx &&& 0xffffffff#64)) := by
  simp only [notE, zCmp, r32, mask32, Expr.eval, BinOp.eval, truthy]
  by_cases h : (rs .rax &&& 4294967295#64) = (rs .rdx &&& 4294967295#64) <;> simp [h]

theorem card_le_B {S : Finset Nat} {B : Nat} (h : ∀ u ∈ S, u < B) : S.card ≤ B := by
  have := Finset.card_le_card (s := S) (t := Finset.range B)
    (fun u hu => Finset.mem_range.mpr (h u hu))
  rwa [Finset.card_range] at this

/-! ## The draw: `lock xadd [rdi], edx` -/

theorem updH_tkObj_l {l Nv Nv' Sv : Nat} {X : Heap} (m : Mode) (old : Nat) :
    (Lab.rmw m l 4 old (Nv' % 2 ^ 32)).updH (Heap.union (tkObj l Nv Sv) X) =
      Heap.union (tkObj l Nv' Sv) X := by
  funext x
  simp only [Lab.updH, Lab.wval, union_apply, tkObj_apply]
  by_cases hx : x = l
  · subst hx; simp
  · simp [Ne.symm hx, hx]

/-- **The draw**: from a permit `u < B`, the thread gets a ticket `k` (in `rdx`, as 32 bits). -/
theorem safeR_take {l B : Nat} {R : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    {p : Bool} {u : Nat} {F : Nat → Prop} (hl : (rs .rdi).toNat = l) (hdx : rs .rdx = 1)
    (hu : u < B)
    (hQ : ∀ k, Q false (rs.set .rdx (BitVec.ofNat 64 (k % 2 ^ 32))) Heap.empty
      (gsetL l (tkWait k F))) :
    SafeR (ticketInvG l B R) Q p TicketLock.take rs Heap.empty (gsetL l (tkReady u F)) := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | rmw hv =>
    rename_i old
    have ha : ((at_ .rdi 0).eval rs).toNat = l := by rw [at_rdi, hl]
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inr rfl, fun hI gI hIi _ dg =>
      ⟨?_, (fun e => by cases e), ?_⟩⟩)⟩
    · obtain ⟨Nv, Sv, S, cl, -, -, -, -, -, hp⟩ := hIi
      intro a hta
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, ha, List.mem_singleton,
        Prod.mk.injEq] at hta
      have ha' : a = l := by
        rcases hta with ⟨v, h1, -⟩ | h2
        · exact h1
        · by_contra hne; simp [Ne.symm hne] at h2
      subst ha'
      rw [inv_l hp a (Or.inl rfl), tkObj_l]; rfl
    · intro hok
      rw [union_empty] at hok ⊢
      obtain ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩ := hIi
      have hrd : hI l = some old := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, ha] using this
      rw [inv_l hp l (Or.inl rfl), tkObj_l] at hrd
      have hold : old = Nv % 2 ^ 32 := by injection hrd with e; exact e.symm
      subst hold
      have hres : RmwOp.result rs 4 (Nv % 2 ^ 32) ((Expr.reg .rdx).eval rs) .fadd =
          (Nv + 1) % 2 ^ 32 := by
        have h1 : (1 : BitVec 64).toNat = 1 := rfl
        simp only [RmwOp.result, Expr.eval, hdx, h1]; omega
      rw [ha, hres]
      have huS : u ∉ S := fun hm =>
        disj_gsetL dg (c := 3) (k := u) (by decide) (Or.inl ⟨rfl, rfl⟩)
          (Or.inr (Or.inr (Or.inr ⟨rfl, hm⟩)))
      have hcl : cl = true → Sv < Nv := fun e => (hc1 e).1
      refine ⟨Heap.empty, ?_, gsetL l (tkWait Nv F),
        gsetL l (tkSet Sv (Nv + 1) (insert u S) cl), disjoint_empty _, ?_, ?_, ?_, ?_,
        hQ Nv, fun e => by cases e⟩
      · exact (Lab.rmw .rlx l 4 (Nv % 2 ^ 32) ((Nv + 1) % 2 ^ 32)).updH hI
      · rw [union_empty]
      · refine gsetL_disj fun c k hc h1 h2 => ?_
        simp only [tkWait, tkSet] at h1 h2
        rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, hF⟩
        · rcases h2 with ⟨-, h | ⟨e1, e2⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · omega
          · have := hcl e1; omega
          · omega
          all_goals omega
        · exact disj_gsetL dg (c := 2) (k := k) (by decide) (Or.inr ⟨rfl, hF⟩)
            (by simp only [tkSet] at h2 ⊢; rcases h2 with h | h | h | h <;> simp_all)
      · rw [gsetL_union, gsetL_union]
        refine gsetL_ext fun c k hc => ?_
        simp only [tkWait, tkSet, tkReady, Finset.mem_insert]
        have := hcl
        constructor
        · rintro ((⟨rfl, rfl⟩ | ⟨rfl, hF⟩) | h)
          · right; left; exact ⟨rfl, Or.inr (Or.inr (Nat.le_refl _))⟩
          · left; right; exact ⟨rfl, hF⟩
          · rcases h with ⟨rfl, h⟩ | h | h | ⟨rfl, rfl | h⟩
            · right; left; refine ⟨rfl, ?_⟩
              rcases h with h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (by omega))
            · right; right; left; exact h
            · right; right; right; left; exact h
            · left; left; exact ⟨rfl, rfl⟩
            · right; right; right; right; exact ⟨rfl, h⟩
        · rintro ((⟨rfl, rfl⟩ | ⟨rfl, hF⟩) | h)
          · right; right; right; right; exact ⟨rfl, Or.inl rfl⟩
          · left; right; exact ⟨rfl, hF⟩
          · rcases h with ⟨rfl, h⟩ | h | h | ⟨rfl, h⟩
            · by_cases hk : k = Nv
              · subst hk; left; left; exact ⟨rfl, rfl⟩
              · right; left; refine ⟨rfl, ?_⟩
                rcases h with h | h | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr (by omega))
            · right; right; left; exact h
            · right; right; right; left; exact h
            · right; right; right; right; exact ⟨rfl, Or.inr h⟩
      · refine ⟨Nv + 1, Sv, insert u S, cl, by omega, ?_, ?_, ?_, rfl, ?_⟩
        · intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hu
          · exact hSB v hv
        · intro e; have := hc1 e; rw [Finset.card_insert_of_notMem huS]; omega
        · intro e; have := hc0 e; rw [Finset.card_insert_of_notMem huS]; omega
        · rcases hp with ⟨e, rfl⟩ | ⟨e, hR, hRR, dR, rfl⟩
          · left; refine ⟨e, ?_⟩
            have := updH_tkObj_l (l := l) (Nv := Nv) (Nv' := Nv + 1) (Sv := Sv) (X := Heap.empty)
              .rlx (Nv % 2 ^ 32)
            rw [union_empty_right, union_empty_right] at this; exact this
          · right; exact ⟨e, hR, hRR, tkObj_disj dR, updH_tkObj_l .rlx _⟩

/-! ## The claim: the plain load of `serving` -/

/-- What a waiting thread with ticket `k` knows after a load of `serving`: if it saw its ticket
it holds `R` and the turn; otherwise nothing changed. -/
def TkGot (l B : Nat) (R : HProp) (k : Nat) (F : Nat → Prop) (rs : Regs) (h g : Heap) : Prop :=
  ((rs .rax &&& 0xffffffff#64) = (rs .rdx &&& 0xffffffff#64) →
      R h ∧ ∃ u, u < B ∧ g = gsetL l (tkHeld k u F)) ∧
  ((rs .rax &&& 0xffffffff#64) ≠ (rs .rdx &&& 0xffffffff#64) →
      h = Heap.empty ∧ g = gsetL l (tkWait k F))

theorem set_rax (rs : Regs) (w : BitVec 64) : (rs.set .rax w) .rax = w := by simp [Regs.set]

theorem set_rax_rdx (rs : Regs) (w : BitVec 64) : (rs.set .rax w) .rdx = rs .rdx := by
  simp [Regs.set]

theorem set_rax_rdi (rs : Regs) (w : BitVec 64) : (rs.set .rax w) .rdi = rs .rdi := by
  simp [Regs.set]

theorem set_rdx_rdi (rs : Regs) (w : BitVec 64) : (rs.set .rdx w) .rdi = rs .rdi := by
  simp [Regs.set]

theorem got_iff {rs : Regs} {v k : Nat} (hv : v < 2 ^ 32)
    (hdx : rs .rdx = BitVec.ofNat 64 (k % 2 ^ 32)) :
    ((rs.set .rax (BitVec.ofNat 64 v)) .rax &&& 0xffffffff#64) =
        ((rs.set .rax (BitVec.ofNat 64 v)) .rdx &&& 0xffffffff#64) ↔ v = k % 2 ^ 32 := by
  have hk : k % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [set_rax, set_rax_rdx, hdx, mask_ofNat hv, mask_ofNat hk, ofNat_inj hv hk]

theorem updH_rd (H : Heap) (m : Mode) (fl : Flav) (a sz v : Nat) :
    (Lab.rd m fl a sz v).updH H = H := by
  funext x; simp [Lab.updH, Lab.wval]

/-- **The claim**: a waiting thread loads `serving`. If it sees its ticket, the turn was not
claimed (the thread still has `T k`), so it takes `R`, `G k`, `U k` and a permit and gives `T k`
back; otherwise (and then the 32-bit values differ, as fewer than `2 ^ 32` tickets are in flight)
nothing changes. -/
theorem safeR_wait_ld {l B : Nat} {R : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    {k : Nat} {F : Nat → Prop} (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64)
    (hB : B < 2 ^ 32) (hdx : rs .rdx = BitVec.ofNat 64 (k % 2 ^ 32))
    (hQ : ∀ v h g, TkGot l B R k F (rs.set .rax (BitVec.ofNat 64 v)) h g →
      Q false (rs.set .rax (BitVec.ofNat 64 v)) h g) :
    SafeR (ticketInvG l B R) Q false TicketLock.ld rs Heap.empty (gsetL l (tkWait k F)) := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | load hv =>
    rename_i v
    have ha := at_rdi4 hl h4
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi _ dg =>
      ⟨?_, (fun _ a ha => by cases ha), ?_⟩⟩)⟩
    · obtain ⟨Nv, Sv, S, cl, -, -, -, -, -, hp⟩ := hIi
      intro a hta
      rw [union_empty]
      simp only [Lab.Touches, Lab.reads, Lab.wval, ha, List.mem_singleton,
        Prod.mk.injEq, Option.isSome_none, Bool.false_eq_true, or_false] at hta
      obtain ⟨_, rfl, -⟩ := hta
      rw [inv_l hp _ (Or.inr rfl), tkObj_l4]; rfl
    · intro hok
      rw [union_empty] at hok ⊢
      rw [ha, updH_rd]
      obtain ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩ := hIi
      have hrd : hI (l + 4) = some v := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, ha] using this
      rw [inv_l hp _ (Or.inr rfl), tkObj_l4] at hrd
      have hval : v = Sv % 2 ^ 32 := by injection hrd with e; exact e.symm
      subst hval
      -- the thread's ticket is in flight and not claimed
      have hT : ¬ (k < Sv ∨ (cl = true ∧ k = Sv) ∨ Nv ≤ k) := fun h =>
        disj_gsetL dg (c := 0) (k := k) (by decide) (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, h⟩)
      have hv32 : Sv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      by_cases hkS : k = Sv
      · subst hkS
        have hcl : cl = false := by
          cases cl
          · rfl
          · exact absurd (Or.inr (Or.inl ⟨rfl, rfl⟩)) hT
        rcases hp with ⟨e, -⟩ | ⟨-, hR, hRR, dR, rfl⟩
        · rw [hcl] at e; cases e
        have hkN : k < Nv := by omega
        have hcard := hc0 hcl
        obtain ⟨u, hu⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
        refine ⟨hR, tkObj l Nv k, gsetL l (tkHeld k u F),
          gsetL l (tkSet k Nv (S.erase u) true), disjoint_symm' dR, (union_comm' dR).symm, ?_, ?_,
          ⟨Nv, k, S.erase u, true, hSN, fun w hw => hSB w (Finset.mem_of_mem_erase hw),
            fun _ => ⟨hkN, by rw [Finset.card_erase_of_mem hu]; omega⟩, nofun, rfl,
            Or.inl ⟨rfl, rfl⟩⟩,
          hQ _ _ _ ⟨fun _ => ⟨hRR, u, hSB u hu, rfl⟩,
            fun hne => absurd ((got_iff hv32 hdx).mpr rfl) hne⟩,
          fun _ _ e => by cases e⟩
        · have hF : ∀ j, F j → j < k := fun j hj => by
            by_contra hlt
            exact disj_gsetL dg (c := 2) (k := j) (by decide) (Or.inr ⟨rfl, hj⟩)
              (Or.inr (Or.inr (Or.inl ⟨rfl, by
                rcases Nat.lt_or_ge k j with h | h
                · exact Or.inl h
                · exact Or.inr ⟨hcl, by omega⟩⟩)))
          refine gsetL_disj fun c j hc h1 h2 => ?_
          rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
            simp [tkHeld, tkSet] at h1 h2
          all_goals first
            | exact h2 h1
            | exact h2.1 h1
            | (rcases h1 with h1 | h1
               · have := hF j h1; omega
               · omega)
        · rw [gsetL_union, gsetL_union]
          refine gsetL_ext fun c j hc => ?_
          rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
            by_cases hj : j = k <;> by_cases hj' : j = u <;>
            simp [tkWait, tkSet, tkHeld, hcl, Finset.mem_erase, hj, hj', hu]
          all_goals first
            | omega
            | (by_cases hF : F u <;> simp [hF]; omega)
            | (by_cases hk : k = u <;> simp_all)
      · -- another ticket: nothing changes hands, and the 32-bit values differ
        have hcS : S.card ≤ B := card_le_B hSB
        have hlt : Nv - Sv ≤ S.card + 1 := by
          cases cl
          · have := hc0 rfl; omega
          · exact (hc1 rfl).2
        have hne : Sv % 2 ^ 32 ≠ k % 2 ^ 32 := by omega
        refine ⟨Heap.empty, hI, gsetL l (tkWait k F), gsetL l (tkSet Sv Nv S cl),
          disjoint_empty _, by rw [union_empty], dg, rfl,
          ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩,
          hQ _ _ _ ⟨fun he => absurd ((got_iff hv32 hdx).mp he) hne, fun _ => ⟨rfl, rfl⟩⟩,
          fun _ _ e => by cases e⟩

/-! ## The acquire -/

theorem lock_eq (L : Nat) : TicketLock.cert.body L =
    .seq (.assign .rdx (.lit 1)) (.seq TicketLock.take (.seq TicketLock.ld
      (.seq (.loop L (notE (zCmp .rax .rdx)) TicketLock.ld) .skip))) := rfl

/-- **Acquire** (`SafeR`, every loop bound, from either pending flag): from a permit `u < B` and
receipts `F`, `ticket_lock` ends owning `R` and a turn `k` (with a permit and the receipts `F`
and `k`), with `rdi` unchanged. -/
theorem ticketLock_acquireR (l B : Nat) (R : HProp) (L : Nat) (rs : Regs) (p : Bool) (u : Nat)
    (F : Nat → Prop) (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64) (hB : B < 2 ^ 32)
    (hu : u < B) :
    SafeR (ticketInvG l B R) (fun p' rs' h g => p' = false ∧ rs' .rdi = rs .rdi ∧ R h ∧
      ∃ k u', u' < B ∧ g = gsetL l (tkHeld k u' F)) p (TicketLock.cert.body L) rs Heap.empty
      (gsetL l (tkReady u F)) := by
  rw [lock_eq]
  apply safeR_seq
  apply safeR_assign
  apply safeR_seq
  refine safeR_take (by rw [set_rdx_rdi, hl]) (by simp [Regs.set, Expr.eval]) hu (fun k => ?_)
  apply safeR_seq
  have e1 : ∀ v, (((rs.set .rdx ((Expr.lit 1).eval rs)).set .rdx
      (BitVec.ofNat 64 (k % 2 ^ 32))).set .rax (BitVec.ofNat 64 v)) .rdi = rs .rdi := by
    intro v; simp [Regs.set]
  let J : Nat → Bool → Regs → Heap → Heap → Prop := fun _ p rs' h g =>
    p = false ∧ rs' .rdi = rs .rdi ∧ rs' .rdx = BitVec.ofNat 64 (k % 2 ^ 32) ∧
      TkGot l B R k F rs' h g
  refine safeR_wait_ld (by simp [Regs.set, hl]) h4 hB (by simp [Regs.set]) (fun v h g hg => ?_)
  apply safeR_seq
  refine safeR_loop J ?_ ?_ (show J L false _ _ _ from ⟨rfl, e1 v, by simp [Regs.set], hg⟩)
  · intro n p' rs' h' g' ⟨hp, h1, _, hg'⟩ hc
    rw [truthy_notE_zCmp] at hc
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
    obtain ⟨hR, u', hu', rfl⟩ := hg'.1 hc
    exact safeR_skip ⟨hp, h1, hR, k, u', hu', rfl⟩
  · intro n p' rs' h' g' ⟨hp, h1, h2, hg'⟩ hc
    subst hp
    rw [truthy_notE_zCmp] at hc
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hc
    obtain ⟨rfl, rfl⟩ := hg'.2 hc
    exact safeR_wait_ld (by rw [h1, hl]) h4 hB h2 (fun v h g hg =>
      ⟨rfl, by rw [set_rax_rdi, h1], by rw [set_rax_rdx, h2], hg⟩)

/-! ## The release -/

theorem tunlock_eq (L : Nat) : TicketUnlock.cert.body L =
    .seq TicketUnlock.ld (.seq TicketUnlock.inc (.seq TicketUnlock.st .skip)) := rfl

theorem union_isSome_right {h₁ h₂ : Heap} {a : Nat} (e : (h₂ a).isSome) :
    (Heap.union h₁ h₂ a).isSome := by
  rw [union_apply]; cases h₁ a <;> simp [e]

/-- The holder of turn `k` sees the claimed state with `serving = k`. -/
theorem held_claimed {l Nv Sv k u : Nat} {S : Finset Nat} {cl : Bool} {F : Nat → Prop}
    (dg : Heap.Disjoint (gsetL l (tkHeld k u F)) (gsetL l (tkSet Sv Nv S cl))) :
    cl = true ∧ Sv = k := by
  by_contra hc
  exact disj_gsetL dg (c := 1) (k := k) (by decide) (Or.inl ⟨rfl, rfl⟩)
    (Or.inr (Or.inl ⟨rfl, fun ⟨h1, h2⟩ => hc ⟨h1, h2.symm⟩⟩))

/-- **The release store** `mov [rdi+4], eax` with `eax = k + 1`: the holder of turn `k` gives
`R` and `G k` back to the invariant, which becomes unclaimed with `serving = k + 1` in every
state disjoint from the holder (that state is claimed with `serving = k`). -/
theorem tk_st_release {l B : Nat} {R : HProp} {Q : Bool → Regs → Heap → Heap → Prop} {rs : Regs}
    {h : Heap} {k u : Nat} {F : Nat → Prop} (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64)
    (hv : (rs .rax).toNat % 2 ^ 32 = (k + 1) % 2 ^ 32) (hR : R h)
    (hQ : Q true rs Heap.empty (gsetL l (tkReady u (fun j => F j ∨ j = k)))) :
    SafeR (ticketInvG l B R) Q false TicketUnlock.st rs h (gsetL l (tkHeld k u F)) := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | store =>
    have ha := at_rdi4 hl h4
    have hv' : ((Expr.reg .rax).eval rs).toNat % 2 ^ (8 * 4) = (k + 1) % 2 ^ 32 := by
      simp only [Expr.eval]; rw [← hv]
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨.rel, .wb, _, 4, _, rfl, by decide, Heap.empty, h,
      gsetL l (tkReady u (fun j => F j ∨ j = k)), gsetL l (fun c j => c = 1 ∧ j = k),
      disjoint_empty _, (union_empty h).symm, ?_, ?_, hQ, ?_⟩)⟩
    · refine gsetL_disj fun c j hc h1 h2 => ?_
      obtain ⟨rfl, -⟩ := h2
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h
    · rw [gsetL_union]
      refine gsetL_ext fun c j hc => ?_
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
        simp [tkWait, tkSet, tkHeld, tkReady, Finset.mem_erase, Finset.mem_insert, or_assoc,
          or_comm, or_left_comm]
    · intro hI gI hIi dh dg
      obtain ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩ := hIi
      obtain ⟨rfl, rfl⟩ := held_claimed dg
      rcases hp with ⟨-, rfl⟩ | ⟨e, -⟩
      swap
      · cases e
      have hkN := (hc1 rfl).1
      have hcnt := (hc1 rfl).2
      rw [ha, hv']
      refine ⟨⟨l + 4, (Sv + 1) % 2 ^ 32, false, rfl,
        union_isSome_right (by rw [tkObj_l4]; rfl)⟩, ?_⟩
      refine ⟨Nv, Sv + 1, S, false, by omega, hSB, nofun, fun _ => by omega, ?_,
        Or.inr ⟨rfl, h, hR, tkObj_disj (disjoint_symm' dh), ?_⟩⟩
      · rw [gsetL_union]
        refine gsetL_ext fun c j hc => ?_
        rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
          simp [tkWait, tkSet, tkHeld, tkReady, Finset.mem_erase, Finset.mem_insert, or_assoc,
            or_comm, or_left_comm]
        all_goals omega
      · rw [union_comm' dh]
        funext x
        simp only [Ent.apply, union_apply, tkObj_apply]
        by_cases hx : x = l + 4
        · subst hx; simp
        · by_cases hx' : x = l
          · subst hx'; simp
          · simp [hx, hx']

/-- **Release by a plain `mov`**: `ticket_unlock` (load `serving`, add one, store) gives `R` and
the turn back to the invariant; the thread keeps its permit and gains the receipt `k`. -/
theorem ticketUnlock_rel (l B : Nat) (R : HProp) (L : Nat) (rs : Regs) (h : Heap) (k u : Nat)
    (F : Nat → Prop) (hl : (rs .rdi).toNat = l) (h4 : l + 4 < 2 ^ 64) (hR : R h) :
    SafeR (ticketInvG l B R) (fun _ _ h' g' => h' = Heap.empty ∧
      g' = gsetL l (tkReady u (fun j => F j ∨ j = k))) false (TicketUnlock.cert.body L) rs h
      (gsetL l (tkHeld k u F)) := by
  rw [tunlock_eq]
  apply safeR_seq
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro lab s' rs' hs
  cases hs with
  | load hv =>
    rename_i v
    have ha := at_rdi4 hl h4
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi dh dg =>
      ⟨?_, (fun _ a ha => by cases ha), ?_⟩⟩)⟩
    · obtain ⟨Nv, Sv, S, cl, -, -, -, -, -, hp⟩ := hIi
      intro a hta
      simp only [Lab.Touches, Lab.reads, Lab.wval, ha, List.mem_singleton,
        Prod.mk.injEq, Option.isSome_none, Bool.false_eq_true, or_false] at hta
      obtain ⟨_, rfl, -⟩ := hta
      apply union_isSome_right
      rw [inv_l hp _ (Or.inr rfl), tkObj_l4]; rfl
    · intro hok
      rw [ha, updH_rd]
      obtain ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩ := hIi
      obtain ⟨rfl, rfl⟩ := held_claimed dg
      have h4I : hI (l + 4) = some (Sv % 2 ^ 32) := by rw [inv_l hp _ (Or.inr rfl), tkObj_l4]
      have hh4 : h (l + 4) = none := none_of_disj' dh (by rw [h4I]; rfl)
      have hrd : Heap.union h hI (l + 4) = some v := by
        have := hok _ (List.mem_singleton_self _)
        simpa [Lab.reads, ha] using this
      rw [union_apply, hh4, Option.none_or, h4I] at hrd
      have hval : v = Sv % 2 ^ 32 := by injection hrd with e; exact e.symm
      subst hval
      refine ⟨h, hI, gsetL l (tkHeld Sv u F), gsetL l (tkSet Sv Nv S true), dh, rfl, dg, rfl,
        ⟨Nv, Sv, S, true, hSN, hSB, hc1, hc0, rfl, hp⟩, ?_, fun _ => fun _ e => e⟩
      -- the increment and the release store
      apply safeR_seq
      apply safeR_assign
      apply safeR_seq
      refine tk_st_release (by simp [Regs.set, hl]) h4 ?_ hR (safeR_skip ⟨rfl, rfl⟩)
      simp only [Regs.set, ite_true, op32, mask32, Expr.eval, BinOp.eval]
      have := inc_val (Sv % 2 ^ 32)
      simp only [show (8 * 4 : Nat) = 32 from rfl] at this
      rw [this]; omega

/-! ## The program -/

/-- **One thread** of the ticket-lock client: lock, critical section, unlock. It starts with the
permit `t` and ends with a permit and exactly one receipt. -/
theorem ticket_thread {l N L t : Nat} {R : HProp} {cs : Stmt} (ht : t < N) (hN : N < 2 ^ 32)
    (hl : l + 8 < 2 ^ 64) (hw : .rdi ∉ cs.writes)
    (hcs : ∀ rs h, R h → Safe (fun h => h = Heap.empty) (fun _ h' => R h') cs rs h) :
    SafeR (ticketInvG l N R) (fun _ _ h g => h = Heap.empty ∧ ∃ u k, u < N ∧
        g = gsetL l (tkReady u (fun j => False ∨ j = k))) false
      (Tv.chain [TicketLock.cert.body L, cs, TicketUnlock.cert.body L]) (regs [(.rdi, l)])
      Heap.empty (gsetL l (tkReady t (fun _ => False))) := by
  have hl' := regs_rdi l (by omega)
  simp only [Tv.chain]
  apply safeR_seq
  refine safeR_conseq (fun p rs' h g ⟨hp, e1, hR, k, u', hu', hg⟩ => ?_)
    (ticketLock_acquireR l N R L _ false t _ hl' (by omega) hN ht)
  subst hp hg
  apply safeR_seq
  have hc := safeR_keep hw (safeR_lift (I := ticketInvG l N R) (I0 := fun h => h = Heap.empty)
    (g := gsetL l (tkHeld k u' (fun _ => False)))
    (fun hI gI i => ⟨Heap.empty, hI, disjoint_empty _, (union_empty hI).symm, rfl,
      fun hA' e _ => by rw [e, union_empty]; exact i⟩) (hcs rs' h hR))
  refine safeR_conseq (fun p rs'' h' g' ⟨⟨hp', hR', hg'⟩, e2⟩ => ?_) hc
  subst hp' hg'
  apply safeR_seq
  exact safeR_conseq (fun _ _ h g ⟨e3, e4⟩ => safeR_skip ⟨e3, u', k, hu', e4⟩)
    (ticketUnlock_rel l N R L rs'' h' k u' _ (by rw [e2, e1, hl']) (by omega) hR')

theorem heapOf_two (l : Nat) (h : Heap) :
    heapOf [(l, 0), (l + 4, 0)] h = Heap.union (tkObj l 0 0) h := by
  funext a
  rw [union_apply, tkObj_apply]
  by_cases ha : a = l
  · subst ha; simp [heapOf, List.find?]
  · by_cases ha4 : a = l + 4
    · subst ha4
      have e : (l == l + 4) = false := by simp
      simp [heapOf, List.find?, e]
    · have e1 : (l == a) = false := by simp [Ne.symm ha]
      have e2 : (l + 4 == a) = false := by simp [Ne.symm ha4]
      simp [heapOf, List.find?, e1, e2, ha, ha4]

/-- Counting: an injection of `N` threads onto the receipts below `S` is a bijection. -/
theorem count_eq {N S : Nat} (k : Nat → Nat) (hinj : ∀ t < N, ∀ t' < N, k t = k t' → t = t')
    (hlt : ∀ t < N, k t < S) (hsurj : ∀ j < S, ∃ t < N, k t = j) : S = N := by
  have h1 : ((Finset.range N).image k).card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hinj a (by simpa using ha) b (by simpa using hb) e
  have h2 : (Finset.range N).image k = Finset.range S := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact hlt t ht
    · intro hj; exact hsurj j hj
  rw [h2, Finset.card_range] at h1
  exact h1

/-- **`Task.ticketMutexTso` holds.** -/
theorem ticketMutexTso_holds : Task.ticketMutexTso := by
  intro N L l R hR0 cs hN hl hR0l hR0l4 hRR hw hcs C hr hd hf
  have G : GInvR (ticketInvG l N R) (fun _ _ _ h g => h = Heap.empty ∧ ∃ u k, u < N ∧
        g = gsetL l (tkReady u (fun j => False ∨ j = k))) N
      (lockCfg (TicketLock.cert.body L) (TicketUnlock.cert.body L) N l cs
        (heapOf [(l, 0), (l + 4, 0)] hR0))
      (fun _ => Heap.empty) (fun t => gsetL l (tkReady t (fun _ => False)))
      (heapOf [(l, 0), (l + 4, 0)] hR0) (gsetL l (tkSet 0 0 ∅ false)) := by
    refine ⟨fun _ _ _ => disjoint_empty _, fun _ => disjoint_empty _, fun t u ne => ?_,
      fun t => ?_, fun _ _ _ e => (by simp [Heap.empty] at e), fun _ _ e => e, ?_, fun t ht => ?_⟩
    · refine gsetL_disj fun c k hc h1 h2 => ?_
      simp only [tkReady] at h1 h2
      rcases h1 with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · rcases h2 with ⟨-, e⟩ | ⟨h, -⟩
        · exact ne e
        · cases h
      · exact h
    · refine gsetL_disj fun c k hc h1 h2 => ?_
      simp only [tkReady, tkSet] at h1 h2
      rcases h1 with ⟨rfl, rfl⟩ | ⟨-, h⟩
      · rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
        · cases h
        · cases h
        · cases h
        · simp at h
      · exact h
    · refine ⟨0, 0, ∅, false, Nat.le_refl _, by simp, nofun, fun _ => by simp, rfl,
        Or.inr ⟨rfl, hR0, hRR, fun x => ?_, heapOf_two l hR0⟩⟩
      rw [tkObj_apply]
      by_cases hx : x = l
      · subst hx; exact Or.inr hR0l
      · by_cases hx4 : x = l + 4
        · subst hx4; exact Or.inr hR0l4
        · left; simp [hx, hx4]
    · simp only [lockCfg, ht, ↓reduceIte]
      exact ticket_thread ht hN hl (hw t) (fun rs h hR => hcs t rs h hR)
  obtain ⟨hs', gs', hI', gI', ps', q, i, -, l2, -, -, dgT, dgI, cons⟩ :=
    rel_tsoG (G0 := gsetL l (fun c k => tkSet 0 0 ∅ false c k ∨ (c = 3 ∧ k < N))) G
      (fun c hc => by
        obtain ⟨c', k, hc', hp, rfl⟩ := gsetL_isSome.mp hc
        rcases hp with hp | ⟨rfl, hk⟩
        · exact Or.inl ((gsetL_tk hc').mpr hp)
        · exact Or.inr ⟨k, hk, (gsetL_tk hc').mpr (Or.inl ⟨rfl, rfl⟩)⟩) hr hd hf
  have hk : ∀ t, ∃ k, t < N → ∃ u, u < N ∧
      gs' t = gsetL l (tkReady u (fun j => False ∨ j = k)) := fun t => by
    by_cases ht : t < N
    · obtain ⟨-, u, k, hu, e⟩ := q t ht; exact ⟨k, fun _ => ⟨u, hu, e⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose kf hkf using hk
  -- a thread holds only its permit and its receipt
  have thr : ∀ t < N, ∀ c j, c < 4 → (gs' t (tkA l c j)).isSome → c = 3 ∨ (c = 2 ∧ j = kf t) :=
    fun t ht c j hc e => by
      obtain ⟨u, -, e'⟩ := hkf t ht
      rw [e', gsetL_tk hc] at e
      rcases e with ⟨rfl, -⟩ | ⟨rfl, h | e⟩
      · exact Or.inl rfl
      · exact h.elim
      · exact Or.inr ⟨rfl, e⟩
  have rcpt : ∀ t < N, (gs' t (tkA l 2 (kf t))).isSome := fun t ht => by
    obtain ⟨u, -, e'⟩ := hkf t ht
    rw [e', gsetL_tk (by decide)]
    exact Or.inr ⟨rfl, Or.inr rfl⟩
  -- the cells in `G0` that no thread can hold are in the invariant
  have inI : ∀ c j, c < 4 → c ≠ 3 → c ≠ 2 → tkSet 0 0 ∅ false c j →
      (gI' (tkA l c j)).isSome := fun c j hc h3 h2 h0 => by
    rcases cons (tkA l c j) ((gsetL_tk hc).mpr (Or.inl h0)) with e | ⟨t, ht, e⟩
    · exact e
    · rcases thr t ht c j hc e with e | ⟨e, -⟩
      · exact absurd e h3
      · exact absurd e h2
  obtain ⟨Nv, Sv, S, cl, hSN, hSB, hc1, hc0, rfl, hp⟩ := i
  have hcl : cl = false := by
    have := (gsetL_tk (by decide)).mp (inI 1 Sv (by decide) (by decide) (by decide)
      (Or.inr (Or.inl ⟨rfl, fun ⟨h, _⟩ => by cases h⟩)))
    rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · cases h
    · cases cl
      · rfl
      · exact absurd ⟨rfl, rfl⟩ h
    · cases h
    · cases h
  subst hcl
  have hNS : Nv = Sv := by
    have := (gsetL_tk (by decide)).mp (inI 0 Sv (by decide) (by decide) (by decide)
      (Or.inl ⟨rfl, Or.inr (Or.inr (Nat.zero_le _))⟩))
    rcases this with ⟨-, h | ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · omega
    · cases h
    · omega
    · cases h
    · cases h
    · cases h
  subst hNS
  have hSv : Nv = N := by
    refine count_eq kf (fun t ht t' ht' e => ?_) (fun t ht => ?_) (fun j hj => ?_)
    · by_contra ne
      have h1 := rcpt t ht
      have h2 := rcpt t' ht'
      rw [e] at h1
      rcases dgT t t' ne (tkA l 2 (kf t')) with z | z
      · rw [z] at h1; cases h1
      · rw [z] at h2; cases h2
    · have h1 := rcpt t ht
      have h2 : gsetL l (tkSet Nv Nv S false) (tkA l 2 (kf t)) = none := by
        rcases dgI t (tkA l 2 (kf t)) with z | z
        · rw [z] at h1; cases h1
        · exact z
      have h3 : ¬ tkSet Nv Nv S false 2 (kf t) := fun h => by
        have := (gsetL_tk (l := l) (by decide)).mpr h; rw [h2] at this; cases this
      by_contra hge
      apply h3
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      by_cases e : kf t = Nv
      · exact Or.inr ⟨rfl, e⟩
      · exact Or.inl (by omega)
    · have h0 : tkSet 0 0 ∅ false 2 j := by
        refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        rcases Nat.eq_zero_or_pos j with h | h
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl h
      rcases cons (tkA l 2 j) ((gsetL_tk (by decide)).mpr (Or.inl h0)) with e | ⟨t, ht, e⟩
      · rcases (gsetL_tk (by decide)).mp e with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h | ⟨-, h⟩⟩ | ⟨h, -⟩
        · cases h
        · cases h
        · omega
        · omega
        · cases h
      · rcases thr t ht 2 j (by decide) e with h | ⟨-, h⟩
        · cases h
        · exact ⟨t, ht, h.symm⟩
  subst hSv
  rcases hp with ⟨h, -⟩ | ⟨-, hR, hRR', dR, rfl⟩
  · cases h
  have hm : Nv % 2 ^ 32 = Nv := Nat.mod_eq_of_lt hN
  refine ⟨?_, ?_, hR, hRR', fun a v e => l2 a v (le_union_right' dR a v e)⟩
  · have := l2 l (Nv % 2 ^ 32) (by rw [union_apply, tkObj_l]; rfl)
    rwa [hm] at this
  · have := l2 (l + 4) (Nv % 2 ^ 32) (by rw [union_apply, tkObj_l4]; rfl)
    rwa [hm] at this

/-! ## Static facts for the Mutex interface with ghost state -/

theorem tk_gdom {l : Nat} {P : Nat → Nat → Prop} {a : Nat} (e : (gsetL l P a).isSome) :
    (Nat.unpair a).1 = l := by
  obtain ⟨c, k, -, -, rfl⟩ := gsetL_isSome.mp e
  simp [tkA, Nat.unpair_pair]

theorem tk_ready_disj (l : Nat) {t u : Nat} (ne : t ≠ u) :
    Heap.Disjoint (gsetL l (tkReady t (fun _ => False))) (gsetL l (tkReady u (fun _ => False))) := by
  refine gsetL_disj fun c k hc h1 h2 => ?_
  simp only [tkReady] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · rcases h2 with ⟨-, e⟩ | ⟨h, -⟩
    · exact ne e
    · cases h
  · exact h

theorem tk_init_ready_disj (l t : Nat) :
    Heap.Disjoint (gsetL l (tkSet 0 0 ∅ false)) (gsetL l (tkReady t (fun _ => False))) := by
  refine gsetL_disj fun c k hc h2 h1 => ?_
  simp only [tkReady, tkSet] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · rcases h2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · cases h
    · cases h
    · cases h
    · simp at h
  · exact h

/-- A fresh ticket lock: both words `0`, no ticket drawn, `R` in the invariant. -/
theorem tk_init_inv (l B : Nat) (R : HProp) (hR : Heap) (r : R hR)
    (d : Heap.Disjoint (Heap.union (Heap.single l 0) (Heap.single (l + 4) 0)) hR) :
    ticketInvG l B R (Heap.union (Heap.union (Heap.single l 0) (Heap.single (l + 4) 0)) hR)
      (gsetL l (tkSet 0 0 ∅ false)) := by
  have e : tkObj l 0 0 = Heap.union (Heap.single l 0) (Heap.single (l + 4) 0) := by
    simp [tkObj]
  refine ⟨0, 0, ∅, false, Nat.le_refl _, by simp, nofun, fun _ => by simp, rfl,
    Or.inr ⟨rfl, hR, r, by rw [e]; exact d, by rw [e]⟩⟩

/-- **The ticket token is exclusive relative to the invariant**: two disjoint tokens hold two
turns, and the invariant lacks at most one turn token. -/
theorem tk_locked_excl (l B : Nat) (R : HProp) (h g : Heap) :
    ¬ gsep (gsep (tkLockedG l B) (tkLockedG l B)) (ticketInvG l B R) h g := by
  rintro ⟨h12, hI, g12, gI, -, -, dg, -, ⟨h1, h2, g1, g2, -, -, d12, rfl, ⟨-, k, u, F, -, rfl⟩,
    ⟨-, k', u', F', -, rfl⟩⟩, ⟨Nv, Sv, S, cl, -, -, -, -, rfl, -⟩⟩
  have d1 : Heap.Disjoint (gsetL l (tkHeld k u F)) (gsetL l (tkSet Sv Nv S cl)) := fun a => by
    rcases dg a with e | e
    · left; rw [union_apply] at e; revert e; cases gsetL l (tkHeld k u F) a <;> simp
    · exact Or.inr e
  have d2 : Heap.Disjoint (gsetL l (tkHeld k' u' F')) (gsetL l (tkSet Sv Nv S cl)) := fun a => by
    rcases dg a with e | e
    · left; rw [union_apply] at e; revert e; cases gsetL l (tkHeld k u F) a <;> simp
    · exact Or.inr e
  obtain ⟨-, rfl⟩ := held_claimed d1
  obtain ⟨-, e⟩ := held_claimed d2
  subst e
  exact disj_gsetL d12 (c := 1) (k := Sv) (by decide) (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks
