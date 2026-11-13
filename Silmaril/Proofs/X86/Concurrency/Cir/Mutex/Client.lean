module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Frame

/-!
# Proofs: the `Even` client, proved against the interface

`even_proved : Even.client.Proved Even.goal`: for **every** `M : Iface` with an object of at
most 8 bytes and every loop bound, the linked start has a CSL certificate whose postconditions
give the goal (both outputs even). The proof uses only `M`'s fields: `lock_spec`,
`unlock_spec`, `init_inv` and `init_dom`; it never looks at `M`'s code or representation.

The invariant is `M.inv m R ∗ emp`, with `R = ∃ v even, x ↦ v`. Each thread owns its output cell,
locks (getting `R ∗ locked m`, framed with the output cell), runs the critical section on owned
cells, and unlocks (handing `R ∗ locked m` back), keeping its output cell with an even value.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Mutex.Even

/-! ## Loads and stores at known addresses -/

theorem updH_wr {m : Mode} {fl : Flav} {a sz c : Nat} (h : Heap) :
    (Lab.wr m fl a sz c).updH h = fun y => if y = a then some c else h y := by
  funext y
  by_cases hy : y = a
  · subst hy; simp [Lab.updH, Lab.wval]
  · have : a ≠ y := Ne.symm hy
    simp [Lab.updH, Lab.wval, this, hy]

theorem load_at {I : HProp} {Q : Regs → HProp} {d : Reg} {sz : Nat} {fl : Flav} {a : Expr}
    {rs : Regs} {h : Heap} {addr v : Nat} (ha : (a.eval rs).toNat = addr) (hv : h addr = some v)
    (hq : Q (rs.set d (BitVec.ofNat 64 v)) h) : Csl.Safe I Q (.load d .na sz fl a) rs h :=
  safe_load_na (by rw [ha]; exact hv) hq

theorem store_at {I : HProp} {Q : Regs → HProp} {sz : Nat} {fl : Flav} {a e : Expr} {rs : Regs}
    {h : Heap} {addr val : Nat} {h' : Heap} (ha : (a.eval rs).toNat = addr)
    (hv : (e.eval rs).toNat % 2 ^ (8 * sz) = val) (hdom : (h addr).isSome)
    (heq : (fun y => if y = addr then some val else h y) = h') (hq : Q rs h') :
    Csl.Safe I Q (.store .na sz fl a e) rs h := by
  apply safe_store_na (by rw [ha]; exact hdom)
  rw [updH_wr, ha, hv, heq]; exact hq

/-! ## Shapes of the owned heap in the critical section -/

/-- `x ↦ a`, the token heap, `out t ↦ b`. -/
def shape (htok : Heap) (o a b : Nat) : Heap :=
  Heap.union (Heap.union (Heap.single x a) htok) (Heap.single o b)

theorem x_ne_out (t : Nat) : x ≠ out t := by simp [x, out]; omega

theorem shape_x {htok : Heap} {o a b : Nat} :
    shape htok o a b x = some a := by
  simp [shape, union_apply, single_apply]

theorem shape_o {htok : Heap} {o a b : Nat} (ho : htok o = none) (hxo : x ≠ o) :
    shape htok o a b o = some b := by
  rw [shape, union_none (union_eq_none.mpr ⟨by simp [single_apply, Ne.symm hxo], ho⟩)]
  simp [single_apply]

theorem shape_wx {htok : Heap} {o a b c : Nat} :
    (fun y => if y = x then some c else shape htok o a b y) = shape htok o c b := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [shape, union_apply, single_apply]
  · simp only [hy, ite_false, shape]
    rw [union_apply, union_apply (Heap.union _ _), union_apply (Heap.single x a),
      union_apply (Heap.single x c)]
    simp [single_apply, hy]

theorem shape_wo {htok : Heap} {o a b c : Nat} (ho : htok o = none) (hxo : x ≠ o) :
    (fun y => if y = o then some c else shape htok o a b y) = shape htok o a c := by
  funext y
  by_cases hy : y = o
  · subst hy
    simp only [ite_true]
    rw [shape, union_none (union_eq_none.mpr ⟨by simp [single_apply, Ne.symm hxo], ho⟩)]
    simp [single_apply]
  · simp only [hy, ite_false, shape]
    cases e : Heap.union (Heap.single x a) htok y with
    | some w => rw [union_some e, union_some e]
    | none => rw [union_none e, union_none e]; simp [single_apply, hy]

theorem shape_disj {htok : Heap} {o a b : Nat} (ho : htok o = none) (hxo : x ≠ o) :
    Heap.Disjoint (Heap.union (Heap.single x a) htok) (Heap.single o b) :=
  disjoint_union_left.mpr ⟨disjoint_single hxo, disjoint_symm (disjoint_single_left ho)⟩

/-! ## One thread -/

/-- The invariant of the client at `M`. -/
def evInv (M : Iface) : HProp := M.inv m R ∗ hemp

/-- Thread `t` ends owning its output cell, with an even value. -/
def evPost (t : Nat) : Regs → HProp := fun _ h => ∃ v, v % 2 = 0 ∧ h = Heap.single (out t) v

theorem rdi_m (rs : Regs) : ((rs.set .rdi ((Expr.lit m).eval rs)) .rdi).toNat = m := by
  simp [Regs.set, Expr.eval, m]

theorem lit_toNat (a : Nat) (h : a < 2 ^ 64) (rs : Regs) : ((Expr.lit a).eval rs).toNat = a := by
  simp [Expr.eval]; omega

/-- **The unlock**, from the critical section's final heap. -/
theorem safe_unl (M : Iface) {t L : Nat} {rs : Regs} {htok : Heap} {w : Nat} (hw : w % 2 = 0)
    (hx : htok x = none) (ho : htok (out t) = none) (htk : M.locked m htok) :
    Csl.Safe (evInv M) (evPost t) (M.unlock L (.lit m)) rs (shape htok (out t) w w) := by
  apply safe_seq
  apply safe_assign
  have hxo := x_ne_out t
  have H := safe_frame (F := fun h => h = Heap.single (out t) w)
    (M.unlock_spec m R hemp L _ (Heap.union (Heap.single x w) htok) (rdi_m rs)
      (sep_iff.mpr ⟨_, htok, disjoint_single_left hx, rfl, ⟨w, hw, rfl⟩, htk⟩))
    (shape_disj ho hxo) rfl
  refine safe_conseq (fun rs' h hp => ?_) H
  obtain ⟨h₁, h₂, -, rfl, e1, rfl⟩ := sep_iff.mp hp
  cases e1
  exact ⟨w, hw, union_empty_left _⟩

/-- **The critical section** on owned cells. -/
theorem safe_cs (M : Iface) {t L : Nat} (ht : t < 2) {rs : Regs} {htok : Heap} {v : Nat}
    (hv : v % 2 = 0) (hx : htok x = none) (ho : htok (out t) = none) (htk : M.locked m htok) :
    Csl.Safe (evInv M) (fun rs h => Csl.Safe (evInv M) (evPost t) (M.unlock L (.lit m)) rs h)
      (cs t) rs (shape htok (out t) v 0) := by
  have hxo := x_ne_out t
  have hout : out t < 2 ^ 64 := by simp [out]; omega
  apply safe_seq
  refine load_at (lit_toNat x (by decide) rs) (shape_x) ?_
  apply safe_seq
  refine store_at (val := 1) (lit_toNat x (by decide) _) (by simp [Expr.eval])
    (by rw [shape_x]; rfl)
    (shape_wx) ?_
  apply safe_seq
  refine store_at (lit_toNat (out t) hout _) rfl (by rw [shape_o ho hxo]; rfl)
    (shape_wo ho hxo) ?_
  apply safe_seq
  refine store_at (lit_toNat x (by decide) _) rfl (by rw [shape_x]; rfl)
    (shape_wx) ?_
  apply safe_skip
  refine safe_unl M ?_ hx ho htk
  simp [Regs.set, Expr.eval]
  omega

/-- **One thread is safe**, for every mutex meeting the interface. -/
theorem thread_safe (M : Iface) (L : Nat) {t : Nat} (ht : t < 2) :
    Csl.Safe (evInv M) (evPost t) (body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (out t) 0) := by
  apply safe_seq
  apply safe_seq
  apply safe_assign
  have H := safe_frame (F := fun h => h = Heap.single (out t) 0)
    (M.lock_spec m R hemp L _ (rdi_m Regs.zero)) (disjoint_empty _) rfl
  rw [union_empty_left] at H
  refine safe_conseq (fun rs h hp => ?_) H
  obtain ⟨h12, hF, d, rfl, hRL, rfl⟩ := sep_iff.mp hp
  obtain ⟨h₁, htok, d12, rfl, ⟨v, hv, rfl⟩, htk⟩ := sep_iff.mp hRL
  have hx : htok x = none := by
    rcases d12 x with e | e
    · simp [single_apply] at e
    · exact e
  have ho : htok (out t) = none := by
    rcases d (out t) with e | e
    · exact (union_eq_none.mp e).2
    · simp [single_apply] at e
  apply safe_seq
  exact safe_cs M ht hv hx ho htk

/-! ## The certificate -/

/-- The ghost start: each thread owns its output cell. -/
def evOwn (t : Nat) : Heap := if t < 2 then Heap.single (out t) 0 else Heap.empty

/-- The invariant's start: the unlocked mutex and `x ↦ 0`. -/
def evHI (M : Iface) : Heap := Heap.union (M.init m) (Heap.single x 0)

theorem init_far (M : Iface) (hM : M.size ≤ 8) {a : Nat} (ha : a < m ∨ m + 8 ≤ a) :
    M.init m a = none := by
  cases e : M.init m a with
  | none => rfl
  | some w =>
    have := M.init_dom m a (by simp [e])
    omega

theorem out_far (t : Nat) : m + 8 ≤ out t := by simp [m, out]; omega

theorem evHI_out (M : Iface) (hM : M.size ≤ 8) (t : Nat) : evHI M (out t) = none := by
  rw [evHI, union_none (init_far M hM (Or.inr (out_far t)))]
  simp [single_apply, Ne.symm (x_ne_out t)]

theorem ginv (M : Iface) (hM : M.size ≤ 8) (L : Nat) :
    GInv (evInv M) evPost 2 (client.link M L) evOwn (evHI M) := by
  have hmem : (client.link M L).mem = Heap.union Even.mem (Heap.union (M.init m) Heap.empty) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u htu
    unfold evOwn
    split
    · split
      · exact disjoint_single (by simp [out]; omega)
      · exact disjoint_empty_right _
    · exact disjoint_empty _
  · intro t
    unfold evOwn
    split
    · exact disjoint_single_left (evHI_out M hM t)
    · exact disjoint_empty _
  · intro t a v hv
    unfold evOwn at hv
    split at hv
    · rename_i ht
      simp only [single_apply] at hv
      split at hv
      · rename_i e
        subst e
        cases hv
        rw [hmem]
        apply union_some
        rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> simp [Even.mem]
      · cases hv
    · simp [Heap.empty] at hv
  · intro a v hv
    rw [hmem]
    simp only [evHI] at hv
    cases e : M.init m a with
    | some w =>
      rw [union_some e] at hv
      cases hv
      have := M.init_dom m a (by simp [e])
      have hn : Even.mem a = none := by
        have hne : ¬ (a = x ∨ a = out 0 ∨ a = out 1) := by
          simp only [x, out, m] at this ⊢; omega
        simp only [Even.mem, hne, ite_false]
      rw [union_none hn, union_some e]
    | none =>
      rw [union_none e] at hv
      simp only [single_apply] at hv
      split at hv
      · rename_i ex
        subst ex
        cases hv
        exact union_some (by simp [Even.mem])
      · cases hv
  · refine sep_emp (M.init_inv m R _ ⟨0, rfl, rfl⟩ ?_)
    intro a
    by_cases ha : a = x
    · subst ha; exact Or.inl (init_far M hM (Or.inr (by simp [m, x])))
    · exact Or.inr (by simp [single_apply, ha])
  · intro t ht
    have : (client.link M L).ts t = (body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Client.link, Client.startWith, client, ht]
    rw [this]
    have : evOwn t = Heap.single (out t) 0 := by simp [evOwn, ht]
    rw [this]
    exact thread_safe M L ht

/-- **`Even` is proved against the interface.** -/
theorem even_proved : client.Proved goal := by
  intro M hM L
  refine ⟨evInv M, evPost, evOwn, evHI M, ginv M hM L, ?_⟩
  intro rs mem hs' hI' hq _ hle _ t ht
  obtain ⟨v, hv, e⟩ := hq t ht
  exact ⟨v, hle t (out t) v (by rw [e]; simp [single_apply]), hv⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
