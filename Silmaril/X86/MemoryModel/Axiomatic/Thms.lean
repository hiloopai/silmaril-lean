module

public import Silmaril.X86.MemoryModel.Axiomatic.Defs
import Silmaril.Proofs.X86.MemoryModel.Axiomatic.Acyclic

/-!
# Axiomatic memory models over candidate executions: theorems

PROVED (standard axioms only; the decision-procedure proofs are in
`Silmaril.Proofs.X86.MemoryModel.Axiomatic.Acyclic`):

* `BRel.acyclic_iff`: Kahn's algorithm `acyclicB` decides herd's `acyclic` (no `TransGen`
  cycle); hence the `Decidable` instances for `BRel.Acyclic`, `BRel.Empty`, `Exec.Sc` and
  `Exec.Tso`, usable by `decide`;
* `BRel.acyclic_mono` and `BRel.acyclic_po_union` (the cycle-shape lemma used for
  "x86-TSO implies no-thin-air" in `Silmaril.X86.MemoryModel.Xl.Thms`);
* basic facts: `po` is a strict order (`Exec.po_trans`, `Exec.po_irrefl`), `sm` is reflexive,
  `fencerel` edges are two `po` edges;
* `Exec.tso_of_sc`: **every** SC-consistent candidate execution is x86-TSO-consistent. No
  well-formedness hypothesis is needed.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Axiomatic

open Relation

namespace BRel
variable {n : Nat}

/-- `acyclicB` decides `Acyclic`. -/
theorem acyclic_iff (r : BRel n) : r.Acyclic ↔ r.acyclicB = true := Proofs.BRel.acyclic_iff r

instance (r : BRel n) : Decidable r.Acyclic := decidable_of_iff _ (acyclic_iff r).symm

/-- `emptyB` decides `Empty`. -/
theorem emptyB_iff (r : BRel n) : r.emptyB = true ↔ r.Empty := Proofs.BRel.emptyB_iff r

instance (r : BRel n) : Decidable r.Empty := decidable_of_iff _ (emptyB_iff r)

/-- If every `r` edge is an `s` path and `s` is acyclic, `r` is acyclic. -/
theorem acyclic_mono {r s : BRel n} (h : ∀ a b, r a b = true → TransGen s.Holds a b)
    (hs : s.Acyclic) : r.Acyclic := Proofs.BRel.acyclic_mono h hs

/-- Cycle shape: with `po` a strict order, `E` edges from `isW` to `isR` nodes, and `G`
containing `E` and the `po` edges from `isR` to `isW` nodes, `G` acyclic gives `po ∪ E`
acyclic. -/
theorem acyclic_po_union (po E G : BRel n) (isR isW : Fin n → Bool)
    (trans : ∀ a b c, po a b = true → po b c = true → po a c = true)
    (irr : ∀ a, po a a = false)
    (hE : ∀ a b, E a b = true → isW a = true ∧ isR b = true)
    (hRW : ∀ a, isR a = true → isW a = true → False)
    (hEG : ∀ a b, E a b = true → G a b = true)
    (hRM : ∀ a b, isR a = true → isW b = true → po a b = true → G a b = true)
    (hG : G.Acyclic) : (po.union E).Acyclic :=
  Proofs.BRel.acyclic_po_union po E G isR isW trans irr hE hRW hEG hRM hG

theorem seq_mono {r r' s s' : BRel n} (hr : ∀ a b, r a b = true → r' a b = true)
    (hs : ∀ a b, s a b = true → s' a b = true) {a b : Fin n} (h : r.seq s a b = true) :
    r'.seq s' a b = true := by
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨c, hc, h1, h2⟩ := h
  exact ⟨c, hc, hr _ _ h1, hs _ _ h2⟩

theorem seq_of_left {r s : BRel n} (hs : ∀ a, s a a = true) {a b : Fin n}
    (h : r a b = true) : r.seq s a b = true := by
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
  exact ⟨b, List.mem_finRange b, h, hs b⟩

theorem seq_elim {r s : BRel n} {a b : Fin n} (h : r.seq s a b = true) :
    ∃ c, r a c = true ∧ s c b = true := by
  simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨c, -, h1, h2⟩ := h
  exact ⟨c, h1, h2⟩

theorem union_iff {r s : BRel n} {a b : Fin n} :
    r.union s a b = true ↔ r a b = true ∨ s a b = true := by
  simp [BRel.union]

theorem inter_iff {r s : BRel n} {a b : Fin n} :
    r.inter s a b = true ↔ r a b = true ∧ s a b = true := by
  simp [BRel.inter]

end BRel

namespace Exec
variable (x : Exec)

theorem po_trans {a b c : Fin x.n} (h1 : x.po a b = true) (h2 : x.po b c = true) :
    x.po a c = true := by
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at *
  exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem po_irrefl (a : Fin x.n) : x.po a a = false := by
  simp [Exec.po]

theorem sm_refl (a : Fin x.n) : x.sm a a = true := by
  simp [Exec.sm]

theorem fencerel_elim {k} {a b : Fin x.n} (h : x.fencerel k a b = true) :
    ∃ f, x.po a f = true ∧ x.po f b = true := by
  simp only [Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨f, -, ⟨-, h1⟩, h2⟩ := h
  exact ⟨f, h1, h2⟩

theorem fencerel_po {k} {a b : Fin x.n} (h : x.fencerel k a b = true) : x.po a b = true := by
  obtain ⟨f, h1, h2⟩ := x.fencerel_elim h
  exact x.po_trans h1 h2

theorem poLoc_po {a b : Fin x.n} (h : x.poLoc a b = true) : x.po a b = true :=
  (BRel.inter_iff.mp h).1

theorem rfe_com {a b : Fin x.n} (h : x.rfe a b = true) : x.com a b = true := by
  simp only [Exec.com, BRel.union_iff]
  exact .inl (BRel.inter_iff.mp h).1

/-- `rfe | fr | co` is contained in `com`. -/
theorem comGhb_part {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) :
    x.com a b = true := by
  simp only [Exec.com, BRel.union_iff] at h ⊢
  rcases h with h | h | h
  · exact .inl (BRel.inter_iff.mp h).1
  · exact .inr (.inr h)
  · exact .inr (.inl h)

/-- Each `ghb` edge is an `scRel` path. -/
theorem ghb_sc {a b : Fin x.n} (h : x.ghb a b = true) : TransGen x.scRel.Holds a b := by
  have po_sc : ∀ {a b}, x.po a b = true → TransGen x.scRel.Holds a b := fun h =>
    .single (BRel.union_iff.mpr (.inl h))
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · obtain ⟨f, h1, h2⟩ := x.fencerel_elim h
    exact (po_sc h1).tail (BRel.union_iff.mpr (.inl h2))
  · simp only [Exec.implied, Bool.and_eq_true] at h
    exact po_sc h.1.1.1
  · simp only [Exec.ppo, Bool.and_eq_true] at h
    exact po_sc h.1
  · exact .single (BRel.union_iff.mpr (.inr (BRel.seq_mono (fun _ _ => x.comGhb_part)
      (fun _ _ h => h) h)))

theorem uniproc_sc {a b : Fin x.n} (h : x.uniproc a b = true) : TransGen x.scRel.Holds a b := by
  simp only [Exec.uniproc, BRel.union_iff] at h
  rcases h with h | h
  · exact .single (BRel.union_iff.mpr (.inl (x.poLoc_po h)))
  · exact .single (BRel.union_iff.mpr (.inr h))

/-- SC implies x86-TSO, for every candidate execution. -/
theorem tso_of_sc (h : x.Sc) : x.Tso :=
  ⟨h.1, BRel.acyclic_mono (fun _ _ => x.uniproc_sc) h.2,
    BRel.acyclic_mono (fun _ _ => x.ghb_sc) h.2⟩

end Exec

namespace Exec
variable (x : Exec)

instance : Decidable x.Sc := inferInstanceAs (Decidable (_ ∧ _))
instance : Decidable x.Tso := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Exec

end Silmaril.X86.MemoryModel.Axiomatic
