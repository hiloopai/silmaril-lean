module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Step

/-!
# Proofs: the Arc specification of the derived ops

* **ghost exchange** (`exch`): giving the token cell of slot `k` to the ledger and taking its
  blank cell (or back) leaves the union of thread and ledger unchanged;
* `regroup`: a re-split of the ghost cells between a thread and the invariant, around a fixed
  rest of the invariant, keeps every disjointness and the union;
* `rc_inc_tok`: `{tok l j ∗ blank l k} rc_inc {tok l j ∗ tok l k}`;
* `rc_dec_tok`: `{tok l k} rc_dec {blank l k ∗ (old = 1 → l ↦ 0 ∗ P)}`;
* `rc_dec_keep`: `{tok l k ∗ tok l j} rc_dec {old ≠ 1 ∧ blank l k ∗ tok l j}`;
* `rc_load_tok`: a token gives atomic read access to a payload cell of fixed value.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc

theorem union_or (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [union_apply]; cases h₁ a <;> rfl

theorem single_self (a v : Nat) : Heap.single a v a = some v := by simp [single_apply]

theorem single_ne {a v x : Nat} (h : x ≠ a) : Heap.single a v x = none := by
  simp [single_apply, h]

theorem eval_lt (e : Expr) (rs : Regs) : (e.eval rs).toNat < gbase := by
  unfold gbase; exact (e.eval rs).isLt

/-! ## Domains -/

theorem isSome_of_le {h s : Heap} (hle : Heap.Le h s) {a : Nat} (ha : (h a).isSome) :
    (s a).isSome := by
  cases e : h a with
  | none => simp [e] at ha
  | some v => rw [hle a v e]; rfl

theorem none_of_disjoint {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) {a : Nat}
    (ha : (h₁ a).isSome) : h₂ a = none := by
  rcases d a with e | e
  · simp [e] at ha
  · exact e

theorem union_isSome {h₁ h₂ : Heap} {a : Nat} :
    (Heap.union h₁ h₂ a).isSome ↔ (h₁ a).isSome ∨ (h₂ a).isSome := by
  rw [union_or]; cases h₁ a <;> cases h₂ a <;> simp

theorem setH_isSome {R : Heap} {c n x : Nat} (hc : (R c).isSome) :
    (setH R c n x).isSome = (R x).isSome := by
  unfold setH; by_cases hx : x = c
  · subst hx; simp [hc]
  · simp [hx]

theorem disjoint_setH {X R : Heap} {c n : Nat} (hc : (R c).isSome) (d : Heap.Disjoint X R) :
    Heap.Disjoint X (setH R c n) := by
  intro x
  rcases d x with e | e
  · exact Or.inl e
  · right; unfold setH; by_cases hx : x = c
    · subst hx; simp [e] at hc
    · simp [hx, e]

theorem union_setH {X R : Heap} {c n : Nat} (hX : X c = none) :
    Heap.union X (setH R c n) = setH (Heap.union X R) c n := by
  funext x; simp only [union_or, setH]
  by_cases hx : x = c
  · subst hx; simp [hX]
  · simp [hx]

theorem setH_union_single {c o n : Nat} {R : Heap} :
    setH (Heap.union (Heap.single c o) R) c n = Heap.union (Heap.single c n) R := by
  funext x; simp only [union_or, setH]
  by_cases hx : x = c
  · subst hx; simp [single_self]
  · simp [hx, single_ne hx]

/-! ## The ghost exchange -/

/-- The token cell of a slot `k ∉ S` moves to the ledger and its blank cell out (or, read
right to left, back): thread-plus-ledger is unchanged. -/
theorem exch {l k : Nat} {S : List Nat} (hl : l < gbase) (hk : k < M) (hkS : k ∉ S) (x : Nat) :
    (Heap.single (gA l k) 0 x).or (ledger l (k :: S) x) =
      (Heap.single (gB l k) 0 x).or (ledger l S x) := by
  by_cases hA : x = gA l k
  · subst hA
    rw [single_ne (gA_ne_gB l k k hl), ledger_gA _ hl hk, ledger_gA _ hl hk, single_self]
    simp [hkS]
  · by_cases hB : x = gB l k
    · subst hB
      rw [single_ne (Ne.symm (gA_ne_gB l k k hl)), ledger_gB _ hl hk, ledger_gB _ hl hk,
        single_self]
      simp [hkS]
    · rw [single_ne hA, single_ne hB,
        ledger_off (S := k :: S) (S' := S) (fun j hj => by simp [hj]) hA hB]

theorem exch_disj_in {l k : Nat} {S : List Nat} (hl : l < gbase) (hk : k < M) :
    Heap.Disjoint (Heap.single (gA l k) 0) (ledger l (k :: S)) := by
  intro x
  by_cases hA : x = gA l k
  · subst hA; right; rw [ledger_gA _ hl hk]; simp
  · left; exact single_ne hA

theorem exch_disj_out {l k : Nat} {S : List Nat} (hl : l < gbase) (hk : k < M) (hkS : k ∉ S) :
    Heap.Disjoint (Heap.single (gB l k) 0) (ledger l S) := by
  intro x
  by_cases hB : x = gB l k
  · subst hB; right; rw [ledger_gB _ hl hk]; simp [hkS]
  · left; exact single_ne hB

/-- **Re-splitting the ghost cells**: the thread `T ∪ G` and the invariant `L ∪ R` become
`T ∪ G'` and `L' ∪ R`, where `G'` and `L'` hold exactly the cells of `G` and `L`. -/
theorem regroup {T G G' L L' R : Heap} (dTG : Heap.Disjoint T G)
    (dB : Heap.Disjoint (Heap.union T G) (Heap.union L R)) (dLR : Heap.Disjoint L R)
    (hx : ∀ x, (G' x).or (L' x) = (G x).or (L x)) (dG' : Heap.Disjoint G' L') :
    Heap.Disjoint T G' ∧ Heap.Disjoint (Heap.union T G') (Heap.union L' R) ∧
      Heap.Disjoint L' R ∧
      Heap.union (Heap.union T G') (Heap.union L' R) =
        Heap.union (Heap.union T G) (Heap.union L R) := by
  -- a cell of `G'` or `L'` is a cell of `G` or `L`
  have sub : ∀ x, ((G' x).isSome ∨ (L' x).isSome) → ((G x).isSome ∨ (L x).isSome) := by
    intro x h
    have := hx x
    cases e1 : G' x <;> cases e2 : L' x <;> cases e3 : G x <;> cases e4 : L x <;>
      simp_all
  have dT : ∀ x, (T x).isSome → G x = none ∧ L x = none := by
    intro x ht
    refine ⟨none_of_disjoint dTG ht, ?_⟩
    have := none_of_disjoint dB (union_isSome.mpr (Or.inl ht))
    exact (union_eq_none.mp this).1
  have dGR : ∀ x, (G x).isSome → R x = none := by
    intro x hg
    exact (union_eq_none.mp (none_of_disjoint dB (union_isSome.mpr (Or.inr hg)))).2
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, ?_⟩
  · cases e : T x with
    | none => exact Or.inl rfl
    | some v =>
      right
      obtain ⟨g, l⟩ := dT x (by simp [e])
      cases e' : G' x with
      | none => rfl
      | some w => have := sub x (Or.inl (by simp [e'])); simp_all
  · cases e : Heap.union T G' x with
    | none => exact Or.inl rfl
    | some v =>
      right
      have hs : (T x).isSome ∨ (G' x).isSome := union_isSome.mp (by simp [e])
      refine union_eq_none.mpr ⟨?_, ?_⟩
      · cases e' : L' x with
        | none => rfl
        | some w =>
          rcases hs with ht | hg
          · have := sub x (Or.inr (by simp [e'])); obtain ⟨g, l⟩ := dT x ht; simp_all
          · rcases dG' x with h1 | h1 <;> simp_all
      · rcases hs with ht | hg
        · exact (union_eq_none.mp (none_of_disjoint dB (union_isSome.mpr (Or.inl ht)))).2
        · rcases sub x (Or.inl hg) with h1 | h1
          · exact dGR x h1
          · exact none_of_disjoint dLR h1
  · cases e : L' x with
    | none => exact Or.inl rfl
    | some v =>
      right
      rcases sub x (Or.inr (by simp [e])) with h1 | h1
      · exact dGR x h1
      · exact none_of_disjoint dLR h1
  · funext x
    simp only [union_or, Option.or_assoc]
    congr 1
    rw [← Option.or_assoc, ← Option.or_assoc, hx]

/-! ## Reading the invariant -/

/-- **A token means the object is live**: the invariant holds slots `S ∋ k`, the ledger, the
count `|S|` and the payload. -/
theorem live_of_tok {l k : Nat} {P : HProp} {hT hI : Heap} (hl : l < gbase) (hk : k < M)
    (hTk : (hT (gA l k)).isSome) (d : Heap.Disjoint hT hI) (hi : rcInv l P hI) :
    ∃ S hP, S.Nodup ∧ (∀ j ∈ S, j < M) ∧ k ∈ S ∧ P hP ∧
      Heap.Disjoint (ledger l S) (Heap.union (Heap.single l S.length) hP) ∧
      Heap.Disjoint (Heap.single l S.length) hP ∧
      hI = Heap.union (ledger l S) (Heap.union (Heap.single l S.length) hP) := by
  obtain ⟨S, hn, hb, (⟨rfl, rfl⟩ | ⟨hne, H⟩)⟩ := hi
  · exfalso
    have := none_of_disjoint d hTk
    rw [ledger_gA _ hl hk] at this; simp at this
  · obtain ⟨g, r, dgr, rfl, rfl, H2⟩ := sep_iff.mp H
    obtain ⟨c, hP, dc, rfl, rfl, hp⟩ := sep_iff.mp H2
    refine ⟨S, hP, hn, hb, ?_, hp, dgr, dc, rfl⟩
    by_contra hkS
    have := (union_eq_none.mp (none_of_disjoint d hTk)).1
    rw [ledger_gA _ hl hk] at this; simp [hkS] at this

theorem not_mem_of_blank {l k : Nat} {S : List Nat} {hT R : Heap} (hl : l < gbase) (hk : k < M)
    (hTk : (hT (gB l k)).isSome) (d : Heap.Disjoint hT (Heap.union (ledger l S) R)) :
    k ∉ S := by
  intro hkS
  have := (union_eq_none.mp (none_of_disjoint d hTk)).1
  rw [ledger_gB _ hl hk] at this; simp [hkS] at this

/-! ## Counts -/

theorem add_one_result {rs : Regs} {old : Nat} (h : old + 1 < 2 ^ 32) :
    (RmwOp.op .add).result rs 4 old ((Expr.lit 1).eval rs) = old + 1 := by
  simp only [RmwOp.result, BinOp.eval, Expr.eval, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : old < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show old + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

theorem sub_one_result {rs : Regs} {old : Nat} (h0 : 1 ≤ old) (h : old < 2 ^ 32) :
    (RmwOp.op .sub).result rs 4 old ((Expr.lit 1).eval rs) = old - 1 := by
  simp only [RmwOp.result, BinOp.eval, Expr.eval]
  have h1 : (BitVec.ofNat 64 old - BitVec.ofNat 64 1).toNat = old - 1 := by
    rw [BitVec.toNat_sub_of_le] <;> simp [BitVec.le_def] <;> omega
  rw [h1, Nat.mod_eq_of_lt (by omega)]

theorem M_lt : M < 2 ^ 32 := by unfold M; omega

theorem disjoint_single_val {c v w : Nat} {R : Heap} (d : Heap.Disjoint (Heap.single c v) R) :
    Heap.Disjoint (Heap.single c w) R := by
  intro x
  by_cases hx : x = c
  · subst hx; rcases d x with e | e
    · simp [single_self] at e
    · exact Or.inr e
  · exact Or.inl (single_ne hx)

theorem union_single_l {T L : Heap} {c n : Nat} {hP : Heap} (hT : T c = none) (hL : L c = none) :
    Heap.union T (Heap.union L (Heap.union (Heap.single c n) hP)) c = some n := by
  simp [union_or, hT, hL, single_self]

/-! ## Clone -/

/-- **`rc_inc` from a token and a blank**: the blank's slot comes into use, so the thread ends
with two tokens. The count `|S|` becomes `|S| + 1 ≤ M`, so the 32-bit add does not wrap. -/
theorem rc_inc_tok {P : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hh : (tok l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h := by
  have hl : l < gbase := ha ▸ eval_lt a rs
  obtain ⟨h1, h2, dh, rfl, ⟨hj, rfl⟩, ⟨hk, rfl⟩⟩ := sep_iff.mp hh
  refine safe_rmw_at ha (fun hI hi hd => ?_)
  obtain ⟨S, hP, hn, hb, hjS, hp, dLR, dcP, rfl⟩ :=
    live_of_tok (P := P) hl hj (hT := Heap.union (Heap.single (gA l j) 0) (Heap.single (gB l k) 0))
      (by simp [union_or, single_self]) hd hi
  have hkS : k ∉ S := not_mem_of_blank hl hk (by simp [union_or, single_self,
    single_ne (Ne.symm (gA_ne_gB l j k hl))]) hd
  have hjk : j ≠ k := fun e => hkS (e ▸ hjS)
  have hlen : S.length + 1 ≤ M := by
    have := length_le_M (S := k :: S) (List.nodup_cons.mpr ⟨hkS, hn⟩)
      (fun i hi => by rcases List.mem_cons.mp hi with rfl | hi; exacts [hk, hb i hi])
    simpa using this
  have hTl : Heap.union (Heap.single (gA l j) 0) (Heap.single (gB l k) 0) l = none := by
    simp [union_or, single_ne (gA_ne_lt hl).symm, single_ne (gB_ne_lt hl).symm]
  have hT'l : Heap.union (Heap.single (gA l j) 0) (Heap.single (gA l k) 0) l = none := by
    simp [union_or, single_ne (gA_ne_lt hl).symm]
  refine ⟨by rw [union_single_l hTl (ledger_lt _ hl)]; rfl, fun old hold => ?_⟩
  rw [union_single_l hTl (ledger_lt _ hl)] at hold
  cases hold
  rw [add_one_result (by have := M_lt; omega)]
  obtain ⟨-, dA, dL'R, heq⟩ := regroup (T := Heap.single (gA l j) 0)
    (G' := Heap.single (gA l k) 0) (L' := ledger l (k :: S)) dh hd dLR (exch hl hk hkS)
    (exch_disj_in hl hk)
  have hRl : (Heap.union (Heap.single l S.length) hP l).isSome := by simp [union_or, single_self]
  have eR : Heap.union (Heap.single l (S.length + 1)) hP =
      setH (Heap.union (Heap.single l S.length) hP) l (S.length + 1) := setH_union_single.symm
  refine ⟨Heap.union (Heap.single (gA l j) 0) (Heap.single (gA l k) 0),
    Heap.union (ledger l (k :: S)) (Heap.union (Heap.single l (S.length + 1)) hP), ?_, ?_, ?_, ?_⟩
  · have hR' : (Heap.union (ledger l (k :: S)) (Heap.union (Heap.single l S.length) hP) l).isSome :=
      by simpa [union_or, ledger_lt _ hl] using hRl
    rw [eR, union_setH (ledger_lt _ hl)]; exact disjoint_setH hR' dA
  · rw [eR, union_setH (ledger_lt _ hl), union_setH hT'l, heq]
  · refine ⟨k :: S, List.nodup_cons.mpr ⟨hkS, hn⟩,
      fun i hi => by rcases List.mem_cons.mp hi with rfl | hi; exacts [hk, hb i hi],
      Or.inr ⟨List.cons_ne_nil _ _, sep_iff.mpr ⟨_, _, ?_, rfl, rfl,
        sep_iff.mpr ⟨_, hP, disjoint_single_val dcP, rfl, by simp [pt], hp⟩⟩⟩⟩
    rw [eR]; exact disjoint_setH hRl dL'R
  · exact sep_iff.mpr ⟨_, _, disjoint_single (fun e => hjk (gA_inj hl e)), rfl, ⟨hj, rfl⟩,
      ⟨hk, rfl⟩⟩

/-! ## Drop -/

/-- What `rc_dec` leaves, from the frame `T` and the token of slot `k`: the old count `old`
in `d`, the slot's blank back, and on the last reference (`old = 1`, and then no other token
is in `T`) the count cell (now `0`) and the payload. -/
def DecPost (P : HProp) (l k : Nat) (d : Reg) (T : Heap) : Regs → HProp := fun rs' h' =>
  ∃ old, old < 2 ^ 32 ∧ rs' d = BitVec.ofNat 64 old ∧
    ((old = 1 ∧ (∀ j < M, j ≠ k → T (gA l j) = none) ∧ ∃ hP, P hP ∧
        Heap.Disjoint (Heap.union T (Heap.single (gB l k) 0))
          (Heap.union (Heap.single l 0) hP) ∧ Heap.Disjoint (Heap.single l 0) hP ∧
        h' = Heap.union (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP))
      ∨ (old ≠ 1 ∧ h' = Heap.union T (Heap.single (gB l k) 0)))

/-- **`rc_dec` from a token** (any frame `T`): the slot leaves use; on the last reference the
invariant goes back to its empty-ledger state and the thread takes the count and the payload. -/
theorem rc_dec_gen {P : HProp} {l k : Nat} {d : Reg} {a : Expr} {rs : Regs} {T : Heap}
    (ha : (a.eval rs).toNat = l) (hk : k < M) (dT : Heap.Disjoint T (Heap.single (gA l k) 0)) :
    Csl.Safe (rcInv l P) (DecPost P l k d T) (rcDec d a) rs
      (Heap.union T (Heap.single (gA l k) 0)) := by
  have hl : l < gbase := ha ▸ eval_lt a rs
  refine safe_rmw_at ha (fun hI hi hd => ?_)
  obtain ⟨S, hP, hn, hb, hkS, hp, dLR, dcP, rfl⟩ :=
    live_of_tok (P := P) hl hk (hT := Heap.union T (Heap.single (gA l k) 0))
      (by simp [union_or]; cases T (gA l k) <;> simp [single_self]) hd hi
  have hTl : T l = none := by
    rcases hd l with e | e
    · exact (union_eq_none.mp e).1
    · simp [union_or, ledger_lt _ hl, single_self] at e
  have hhl : Heap.union T (Heap.single (gA l k) 0) l = none := by
    simp [union_or, hTl, single_ne (gA_ne_lt hl).symm]
  refine ⟨by rw [union_single_l hhl (ledger_lt _ hl)]; rfl, fun old hold => ?_⟩
  rw [union_single_l hhl (ledger_lt _ hl)] at hold
  cases hold
  have hpos : 1 ≤ S.length := List.length_pos_of_mem hkS
  have hlenM : S.length ≤ M := length_le_M hn hb
  have hlt : S.length < 2 ^ 32 := by have := M_lt; omega
  rw [sub_one_result hpos hlt]
  -- `S` is `k` and the rest
  have hperm : S.Perm (k :: S.erase k) := List.perm_cons_erase hkS
  have hn0 : (S.erase k).Nodup := hn.erase k
  have hk0 : k ∉ S.erase k := fun h => by
    have := (List.nodup_cons.mp (hperm.nodup_iff.mp hn)).1; exact this h
  have hlen0 : (S.erase k).length = S.length - 1 := List.length_erase_of_mem hkS
  have hb0 : ∀ i ∈ S.erase k, i < M := fun i hi => hb i (List.mem_of_mem_erase hi)
  have hL : ledger l S = ledger l (k :: S.erase k) := ledger_congr fun i => hperm.mem_iff
  rw [hL] at dLR hd ⊢
  obtain ⟨-, dA, dL'R, heq⟩ := regroup (T := T) (G := Heap.single (gA l k) 0)
    (G' := Heap.single (gB l k) 0) (L' := ledger l (S.erase k)) dT hd dLR
    (fun x => (exch hl hk hk0 x).symm) (exch_disj_out hl hk hk0)
  have hRl : (Heap.union (Heap.single l S.length) hP l).isSome := by simp [union_or, single_self]
  have hT'l : Heap.union T (Heap.single (gB l k) 0) l = none := by
    simp [union_or, hTl, single_ne (gB_ne_lt hl).symm]
  have eR : Heap.union (Heap.single l (S.length - 1)) hP =
      setH (Heap.union (Heap.single l S.length) hP) l (S.length - 1) := setH_union_single.symm
  have hold : (S.length < 2 ^ 32) := hlt
  by_cases h1 : S.length = 1
  · -- the last reference: the ledger is empty again
    have hS0 : S.erase k = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hS0] at dA dL'R heq
    have hR0 : Heap.union (Heap.single l 0) hP =
        setH (Heap.union (Heap.single l S.length) hP) l 0 := setH_union_single.symm
    have dR0 : Heap.Disjoint (ledger l []) (Heap.union (Heap.single l 0) hP) := by
      rw [hR0]; exact disjoint_setH hRl dL'R
    have dAll := (disjoint_union_right.mp dA)
    refine ⟨Heap.union (Heap.union T (Heap.single (gB l k) 0)) (Heap.union (Heap.single l 0) hP),
      ledger l [], ?_, ?_, ⟨[], List.nodup_nil, by simp, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    · exact disjoint_union_left.mpr ⟨dAll.1, disjoint_symm dR0⟩
    · rw [union_assoc, ← union_comm dR0, hR0, union_setH (ledger_lt _ hl), union_setH hT'l, heq,
        h1, hS0]
    · refine ⟨1, by decide, by simp [Regs.set, h1], Or.inl ⟨rfl, fun j hj hjk => ?_, hP, hp,
        by rw [hR0]; exact disjoint_setH hRl dAll.2, disjoint_single_val dcP, rfl⟩⟩
      have hS : S.erase k = [] := hS0
      have hjS : j ∉ k :: S.erase k := by rw [hS]; simpa using hjk
      have := ledger_gA (l := l) (k := j) (k :: S.erase k) hl hj
      rw [ite_eq_right hjS] at this
      rcases hd (gA l j) with e | e
      · exact (union_eq_none.mp e).1
      · simp [union_or, this] at e
  · -- not the last reference
    have hne : S.erase k ≠ [] := fun e => by rw [e] at hlen0; simp at hlen0; omega
    refine ⟨Heap.union T (Heap.single (gB l k) 0),
      Heap.union (ledger l (S.erase k)) (Heap.union (Heap.single l (S.length - 1)) hP),
      ?_, ?_, ?_, ?_⟩
    · have hR' : (Heap.union (ledger l (S.erase k))
          (Heap.union (Heap.single l S.length) hP) l).isSome := by
        simpa [union_or, ledger_lt _ hl] using hRl
      rw [eR, union_setH (ledger_lt _ hl)]
      exact disjoint_setH hR' dA
    · rw [eR, union_setH (ledger_lt _ hl), union_setH hT'l, heq]
    · refine ⟨S.erase k, hn0, hb0, Or.inr ⟨hne, sep_iff.mpr ⟨_, _, ?_, rfl, rfl,
        sep_iff.mpr ⟨_, hP, disjoint_single_val dcP, rfl, by simp [pt, hlen0], hp⟩⟩⟩⟩
      rw [eR]; exact disjoint_setH hRl dL'R
    · exact ⟨S.length, hlt, by simp [Regs.set], Or.inr ⟨h1, rfl⟩⟩

/-! ## Reading through a token -/

/-- **A token gives atomic read access to the payload**: an atomic load of a payload cell
whose value `P` fixes returns that value. -/
theorem rc_load_tok {P : HProp} {Q : Regs → HProp} {l k c v0 : Nat} {d : Reg} {m : Mode}
    {sz : Nat} {fl : Flav} {a : Expr} {rs : Regs} {h : Heap} (hm : m ≠ .na)
    (hc : (a.eval rs).toNat = c) (hl : l < gbase) (hk : k < M) (hT : (h (gA l k)).isSome)
    (hPc : ∀ hP, P hP → hP c = some v0) (hq : Q (rs.set d (BitVec.ofNat 64 v0)) h) :
    Csl.Safe (rcInv l P) Q (.load d m sz fl a) rs h := by
  have hcg : c < gbase := hc ▸ eval_lt a rs
  refine safe_load_at hm hc (fun hI hi hd => ?_)
  obtain ⟨S, hP, -, -, -, hp, -, dcP, rfl⟩ := live_of_tok (P := P) hl hk hT hd hi
  have hv := hPc hP hp
  have hIc : Heap.union (ledger l S) (Heap.union (Heap.single l S.length) hP) c = some v0 := by
    have hcl : Heap.single l S.length c = none := by
      rcases dcP c with e | e
      · exact e
      · simp [hv] at e
    simp [union_or, ledger_lt _ hcg, hcl, hv]
  have hhc : h c = none := none_of_disjoint (disjoint_symm hd) (by simp [hIc])
  refine ⟨by simp [union_or, hhc, hIc], fun v hv' => ?_⟩
  rw [union_or, hhc, Option.none_or, hIc] at hv'
  cases hv'; exact hq

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
