module

public import Silmaril.X86.Concurrency.Story.Pipe.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms

/-!
# Proofs: generic rules for the pipeline

Heap lemmas, the ghost-token heaps `gh`, and four `SafeR` rules the pipeline needs that
`Csl.Rel` does not export:

* `safeR_gframe`: the **ghost frame rule** (a ghost heap the thread never re-splits stays with it);
  `Csl.Rel.safeR_frame` frames physical cells only, and the mutex interface's lock and unlock
  specs fix the thread's ghost heap, so a client with ghost tokens of its own needs this;
* `safeR_load_own`, `safeR_store_own`: plain accesses to owned cells (any flag);
* `safeR_mfence`: `mfence` drains, so it clears the pending flag;
* `gsep_comm`: the ghost-aware separating conjunction commutes.

Heap lemmas are restated here (other topics' proof modules are not imported).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Story.Pipe

/-! ## Heaps -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v x : Nat) : Heap.single a v x = if x = a then some v else none := rfl

theorem empty_apply (x : Nat) : Heap.empty x = none := rfl

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext x; rw [union_apply]; rfl

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext x; rw [union_apply]; cases h x <;> rfl

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem disjoint_symm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ :=
  fun a => (d a).symm

theorem union_comm {h₁ h₂ : Heap} (d : Heap.Disjoint h₁ h₂) :
    Heap.union h₁ h₂ = Heap.union h₂ h₁ := by
  funext x; rw [union_apply, union_apply]
  rcases d x with e | e <;> simp [e]

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    Heap.union (Heap.union h₁ h₂) h₃ = Heap.union h₁ (Heap.union h₂ h₃) := by
  funext x; simp only [union_apply, Option.or_assoc]

theorem disj_iff {h₁ h₂ : Heap} : Heap.Disjoint h₁ h₂ ↔ ∀ a, h₁ a = none ∨ h₂ a = none :=
  Iff.rfl

theorem disj_union_left {h₁ h₂ h : Heap} (d₁ : Heap.Disjoint h₁ h) (d₂ : Heap.Disjoint h₂ h) :
    Heap.Disjoint (Heap.union h₁ h₂) h := fun a => by
  rw [union_apply]
  rcases d₁ a with e | e
  · rw [e, Option.none_or]; exact d₂ a
  · exact Or.inr e

theorem disj_union_right {h₁ h₂ h : Heap} (d₁ : Heap.Disjoint h h₁) (d₂ : Heap.Disjoint h h₂) :
    Heap.Disjoint h (Heap.union h₁ h₂) :=
  disjoint_symm (disj_union_left (disjoint_symm d₁) (disjoint_symm d₂))

theorem disj_of_union_left {h₁ h₂ h : Heap} (d : Heap.Disjoint (Heap.union h₁ h₂) h) :
    Heap.Disjoint h₁ h := fun a => by
  rcases d a with e | e
  · rw [union_apply] at e; cases e1 : h₁ a
    · exact Or.inl rfl
    · rw [e1] at e; cases e
  · exact Or.inr e

theorem disj_of_union_right {h₁ h₂ h : Heap} (d : Heap.Disjoint (Heap.union h₁ h₂) h) :
    Heap.Disjoint h₂ h := fun a => by
  rcases d a with e | e
  · rw [union_apply] at e; cases e1 : h₁ a
    · rw [e1, Option.none_or] at e; exact Or.inl e
    · rw [e1] at e; cases e
  · exact Or.inr e

/-- Cells of `h'` are cells of `A` or `B`. -/
theorem disj_of_sub {h' A B C : Heap} (hs : ∀ a, (h' a).isSome → (A a).isSome ∨ (B a).isSome)
    (dA : Heap.Disjoint A C) (dB : Heap.Disjoint B C) : Heap.Disjoint h' C := fun a => by
  cases e : h' a with
  | none => exact Or.inl rfl
  | some v =>
    rcases hs a (by rw [e]; rfl) with h | h
    · rcases dA a with e' | e'
      · rw [e'] at h; cases h
      · exact Or.inr e'
    · rcases dB a with e' | e'
      · rw [e'] at h; cases h
      · exact Or.inr e'

theorem union_isSome (h₁ h₂ : Heap) (a : Nat) :
    (Heap.union h₁ h₂ a).isSome = ((h₁ a).isSome || (h₂ a).isSome) := by
  rw [union_apply]; cases h₁ a <;> simp

theorem updH_apply (H : Heap) (l : Lab) (a : Nat) : l.updH H a = (l.wval a).or (H a) := rfl

theorem lit_eval (a : Nat) (h : a < 2 ^ 64) (rs : Regs) : ((Expr.lit a).eval rs).toNat = a := by
  simp [Expr.eval]; omega

/-! ## Ghost-token heaps -/

theorem gh_apply (T : Nat → Nat → Bool) (x : Nat) :
    gh T x = if (Nat.unpair x).1 = gbase ∧ T ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) = true
      then some 0 else none := rfl

theorem gh_tok (T : Nat → Nat → Bool) {f : Nat} (hf : f < 6) (i : Nat) :
    gh T (tok f i) = if T f i = true then some 0 else none := by
  have h1 : (6 * i + f) % 6 = f := by omega
  have h2 : (6 * i + f) / 6 = i := by omega
  simp [gh_apply, tok, Nat.unpair_pair, h1, h2]

theorem gh_union (T₁ T₂ : Nat → Nat → Bool) :
    Heap.union (gh T₁) (gh T₂) = gh fun f i => T₁ f i || T₂ f i := by
  funext x
  rw [union_apply, gh_apply, gh_apply, gh_apply]
  by_cases hb : (Nat.unpair x).1 = gbase
  · cases e1 : T₁ ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) <;>
      cases e2 : T₂ ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) <;> simp [hb]
  · simp [hb]

/-- Every cell with base `gbase` is a token. -/
theorem tok_of {x : Nat} (hb : (Nat.unpair x).1 = gbase) :
    x = tok ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) := by
  have : 6 * ((Nat.unpair x).2 / 6) + (Nat.unpair x).2 % 6 = (Nat.unpair x).2 := Nat.div_add_mod _ _
  simp only [tok, this, ← hb, Nat.pair_unpair]

theorem gh_ext {T₁ T₂ : Nat → Nat → Bool} (h : ∀ f i, f < 6 → T₁ f i = T₂ f i) :
    gh T₁ = gh T₂ := by
  funext x
  rw [gh_apply, gh_apply, h _ _ (Nat.mod_lt _ (by decide))]

theorem gh_disj {T₁ T₂ : Nat → Nat → Bool} :
    Heap.Disjoint (gh T₁) (gh T₂) ↔ ∀ f i, f < 6 → ¬ (T₁ f i = true ∧ T₂ f i = true) := by
  constructor
  · intro d f i hf ⟨e1, e2⟩
    rcases d (tok f i) with e | e
    · rw [gh_tok _ hf, e1] at e; cases e
    · rw [gh_tok _ hf, e2] at e; cases e
  · intro h x
    rw [gh_apply, gh_apply]
    by_cases hb : (Nat.unpair x).1 = gbase
    · by_cases e1 : T₁ ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) = true
      · have e2 : T₂ ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6) = false := by
          cases e : T₂ ((Nat.unpair x).2 % 6) ((Nat.unpair x).2 / 6)
          · rfl
          · exact absurd ⟨e1, e⟩ (h _ _ (Nat.mod_lt _ (by decide)))
        exact Or.inr (by simp [e2])
      · exact Or.inl (by simp [e1])
    · exact Or.inl (by simp [hb])

/-- A ghost heap of tokens is disjoint from a heap with no cell at base `gbase`. -/
theorem gh_disj_far {T : Nat → Nat → Bool} {g : Heap}
    (hg : ∀ x, (g x).isSome → (Nat.unpair x).1 ≠ gbase) : Heap.Disjoint (gh T) g := fun x => by
  by_cases hb : (Nat.unpair x).1 = gbase
  · right; cases e : g x
    · rfl
    · exact absurd hb (hg x (by rw [e]; rfl))
  · left; rw [gh_apply]; simp [hb]

/-! ## The separating conjunction of `GProp`s commutes -/

theorem gsep_comm (P Q : GProp) : gsep P Q = gsep Q P := by
  funext h g
  apply propext
  constructor <;>
  · rintro ⟨h₁, h₂, g₁, g₂, dh, rfl, dg, rfl, p, q⟩
    exact ⟨h₂, h₁, g₂, g₁, disjoint_symm dh, union_comm dh, disjoint_symm dg, union_comm dg, q, p⟩

/-! ## The ghost frame rule -/

section GF
variable {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

theorem oblig_mono_G {e : Ent} {hR gR H G G' : Heap}
    (dG : ∀ a, (G a).isSome → (G' a).isSome) (ob : Oblig I e hR gR H G) : Oblig I e hR gR H G' :=
  fun hI gI i d1 d2 => ob hI gI i d1 (fun a => by
    rcases d2 a with e | e
    · cases e' : G a
      · exact Or.inl rfl
      · have := dG a (by rw [e']; rfl); rw [e] at this; cases this
    · exact Or.inr e)

/-- **The ghost frame rule**: a ghost heap `gF` disjoint from the thread's is never re-split
and is still there at the end. -/
theorem safeR_gframe {p : Bool} {s : Stmt} {rs : Regs} {h g gF : Heap}
    (H : SafeR I Q p s rs h g) (hd : Heap.Disjoint g gF) :
    SafeR I (fun p rs h' g' => ∃ g1, Q p rs h' g1 ∧ Heap.Disjoint g1 gF ∧
      g' = Heap.union g1 gF) p s rs h (Heap.union g gF) := by
  refine safeR_coind (fun p s rs h G => ∃ g, SafeR I Q p s rs h g ∧ Heap.Disjoint g gF ∧
    G = Heap.union g gF) ?_ ⟨g, H, hd, rfl⟩
  rintro p s rs h _ ⟨g, H, hd, rfl⟩
  have S := safeR_unfold H
  refine ⟨fun e => ⟨g, S.1 e, hd, rfl⟩, fun s' rs' st => Or.inl ⟨g, S.2.1 _ _ st, hd, rfl⟩,
    fun l s' rs' st => ?_⟩
  obtain ⟨hm, H⟩ := S.2.2 l s' rs' st
  refine ⟨hm, ?_⟩
  rcases H with ⟨tc, k⟩ | ⟨ena, pc, sh⟩ |
    ⟨m, fl, a, sz, v, rfl, hmn, h', hR, g', gR, d1, eh, d2, eg, k, ob⟩
  · exact Or.inl ⟨tc, fun ok => Or.inl ⟨g, k ok, hd, rfl⟩⟩
  · refine Or.inr (Or.inl ⟨ena, pc, fun hI gI hIi dI dgI => ?_⟩)
    have dgI' : Heap.Disjoint g gI := disj_of_union_left dgI
    have dFI : Heap.Disjoint gF gI := disj_of_union_right dgI
    obtain ⟨c1, c2, c3⟩ := sh hI gI hIi dI dgI'
    refine ⟨c1, c2, fun ok => ?_⟩
    obtain ⟨h'', hI', g'', gI', y1, y2, y3, y4, y5, y6, y7⟩ := c3 ok
    have sub : ∀ x, (g'' x).isSome ∨ (gI' x).isSome → (g x).isSome ∨ (gI x).isSome := by
      intro x hx
      have := congrArg (fun H => (H x).isSome) y4
      simp only [union_isSome] at this
      cases e1 : (g'' x).isSome <;> cases e2 : (gI' x).isSome <;>
        cases e3 : (g x).isSome <;> cases e4 : (gI x).isSome <;> simp_all
    have dg''F : Heap.Disjoint g'' gF := disj_of_sub (fun x e => sub x (Or.inl e)) hd
      (disjoint_symm dFI)
    have dgI'F : Heap.Disjoint gI' gF := disj_of_sub (fun x e => sub x (Or.inr e)) hd
      (disjoint_symm dFI)
    refine ⟨h'', hI', Heap.union g'' gF, gI', y1, y2,
      disj_union_left y3 (disjoint_symm dgI'F), ?_, y5, Or.inl ⟨g'', y6, dg''F, rfl⟩, y7⟩
    funext x
    have e4 := congrFun y4 x
    simp only [union_apply] at e4 ⊢
    cases eF : gF x with
    | none => simp only [Option.or_none]; exact e4
    | some w =>
      have a1 : g'' x = none := ((dg''F x).resolve_right (by rw [eF]; simp))
      have a2 : gI' x = none := ((dgI'F x).resolve_right (by rw [eF]; simp))
      have a3 : g x = none := ((hd x).resolve_right (by rw [eF]; simp))
      have a4 : gI x = none := ((dFI x).resolve_left (by rw [eF]; simp))
      simp [a1, a2, a3, a4]
  · have dRF : Heap.Disjoint gR gF := by
      rw [eg] at hd; exact disj_of_union_right hd
    have dg'F : Heap.Disjoint g' gF := by
      rw [eg] at hd; exact disj_of_union_left hd
    refine Or.inr (Or.inr ⟨m, fl, a, sz, v, rfl, hmn, h', hR, Heap.union g' gF, gR, d1, eh,
      disj_union_left d2 (disjoint_symm dRF), ?_, Or.inl ⟨g', k, dg'F, rfl⟩,
      oblig_mono_G (fun x e => by rw [union_isSome, e]; rfl) ob⟩)
    rw [eg]
    funext x
    simp only [union_apply]
    rcases dRF x with e | e <;> simp [e]

end GF

/-! ## Plain accesses to owned cells, and `mfence` -/

section Acc
variable {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

/-- **A plain load of an owned cell** (any mode, any flag): it reads the owned value. -/
theorem safeR_load_own {p : Bool} {d : Reg} {m : Mode} {sz : Nat} {fl : Flav} {a : Expr}
    {rs : Regs} {h g : Heap} {v : Nat} (hv : h ((a.eval rs).toNat) = some v)
    (hq : Q p (rs.set d (BitVec.ofNat 64 v)) h g) :
    SafeR I Q p (.load d m sz fl a) rs h g := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | load hv' =>
    rename_i v'
    refine ⟨rfl, rfl, Or.inl ⟨fun x hx => ?_, fun ok => ?_⟩⟩
    · simp only [Lab.Touches, Lab.reads, Lab.wval, List.mem_singleton, Prod.mk.injEq] at hx
      rcases hx with ⟨_, rfl, -⟩ | hx
      · rw [hv]; rfl
      · cases hx
    · have e := ok _ (List.mem_singleton_self _)
      simp only [hv] at e
      cases e
      have hu : (Lab.rd m fl (a.eval rs).toNat sz v).updH h = h := by
        funext x; rfl
      simp only [Lab.drains, Bool.not_false, Bool.and_true, hu]
      exact hq

/-- **A plain store to an owned cell** (any flag; the value is reduced to the store's width). -/
theorem safeR_store_own {p : Bool} {m : Mode} {sz : Nat} {fl : Flav} {a e : Expr}
    {rs : Regs} {h g : Heap} (ha : (h ((a.eval rs).toNat)).isSome)
    (hq : Q p rs (fun x => if x = (a.eval rs).toNat then some ((e.eval rs).toNat % 2 ^ (8 * sz))
      else h x) g) :
    SafeR I Q p (.store m sz fl a e) rs h g := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | store =>
    refine ⟨rfl, rfl, Or.inl ⟨fun x hx => ?_, fun _ => ?_⟩⟩
    · simp only [Lab.Touches, Lab.reads, Lab.wval, List.not_mem_nil] at hx
      rcases hx with ⟨_, hx⟩ | hx
      · exact hx.elim
      · by_cases e : (a.eval rs).toNat = x
        · rw [← e]; exact ha
        · simp [e] at hx
    · have hu : (Lab.wr m fl (a.eval rs).toNat sz ((e.eval rs).toNat % 2 ^ (8 * sz))).updH h =
          fun x => if x = (a.eval rs).toNat then some ((e.eval rs).toNat % 2 ^ (8 * sz))
            else h x := by
        funext x
        rw [updH_apply]
        by_cases hx : x = (a.eval rs).toNat
        · subst hx; simp [Lab.wval]
        · simp [Lab.wval, Ne.symm hx, hx]
      simp only [Lab.drains, Bool.not_false, Bool.and_true, hu]
      exact hq

/-- **`mfence`** drains: from any flag, to a clear flag, nothing moves. -/
theorem safeR_mfence {p : Bool} {rs : Regs} {h g : Heap} (hq : Q false rs h g) :
    SafeR I Q p (.fence .mfence) rs h g := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | fence =>
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inr rfl, fun hI gI hIi dI dgI => ?_⟩)⟩
    refine ⟨fun x hx => ?_, fun e => (by cases e), fun _ => ?_⟩
    · simp [Lab.Touches, Lab.reads, Lab.wval] at hx
    · refine ⟨h, hI, g, gI, dI, ?_, dgI, rfl, hIi, hq, fun e => by cases e⟩
      funext x; rfl

end Acc

end Silmaril.Proofs.X86.Concurrency.Story.Pipe
