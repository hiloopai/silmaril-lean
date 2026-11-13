module

public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Tso
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.Frame
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.InvFrame

/-!
# CSL with a release rule for plain stores: rules and soundness on TSO

Everything here is PROVED (standard axioms
only). Proofs are in `Silmaril/Proofs/X86/Concurrency/Cir/Csl/Rel/`.

* Thread-local rules on `SafeR`: `safeR_skip`, `safeR_conseq`, `safeR_seq`, `safeR_ite`,
  `safeR_loop`, `safeR_assign`, `safeR_atomic`, the frame rule `safeR_frame`, and the inversion
  `safeR_unfold`; `safeR_flag`: code that drains first (`DF`) is safe from any pending flag.
* `safeR_lift`: **every CSL proof is a `SafeR` proof** (flag clear, ghost unchanged), under any
  invariant that frames the CSL invariant; `ginvR_of_ginv`: a CSL certificate (`GInv`) is a `GInvR`
  certificate with empty ghosts.
* `safeR_inv_frame`: **the invariant frame rule**, `SafeR I Q → SafeR (I ∗ J) Q`
  for the ghost-aware separating conjunction `gsep`;
* `rel_tsoG`: `rel_tso`, also giving the ghost heaps' disjointness at the end.
* **`rel_tso`**: soundness on the CIR-native TSO store-buffer machine. From a `GInvR` start,
  every finished, drained TSO configuration satisfies every thread's postcondition and the
  invariant, with disjoint heaps inside memory, and no ghost cell is lost.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl.Rel

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy)
open Silmaril.X86.Concurrency.Cir.Csl

variable {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop}

/-! ## Thread-local rules -/

theorem safeR_unfold {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I Q p s rs h g) : SafeFR I Q (SafeR I Q) p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_unfold H

theorem safeR_fold {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeFR I Q (SafeR I Q) p s rs h g) : SafeR I Q p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_fold H

theorem safeR_coind (R : Bool → Stmt → Regs → Heap → Heap → Prop)
    (hR : ∀ p s rs h g, R p s rs h g →
      SafeFR I Q (fun p s rs h g => R p s rs h g ∨ SafeR I Q p s rs h g) p s rs h g)
    {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap} (H : R p s rs h g) : SafeR I Q p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_coind R hR H

theorem labOkR_mono {K K' : Bool → Heap → Heap → Prop} (hK : ∀ p h g, K p h g → K' p h g)
    {p : Bool} {l : Lab} {h g : Heap} (H : LabOkR I K p l h g) : LabOkR I K' p l h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.labOkR_mono hK H

theorem safeR_skip {p : Bool} {rs : Regs} {h g : Heap} (hq : Q p rs h g) :
    SafeR I Q p .skip rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_skip hq

theorem safeR_skip_inv {p : Bool} {rs : Regs} {h g : Heap} (H : SafeR I Q p .skip rs h g) :
    Q p rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_skip_inv H

theorem safeR_conseq {Q' : Bool → Regs → Heap → Heap → Prop}
    (hQ : ∀ p rs h g, Q p rs h g → Q' p rs h g) {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I Q p s rs h g) : SafeR I Q' p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_conseq hQ H

/-- **Sequential composition**; the pending flag flows from `s` into `t`. -/
theorem safeR_seq {p : Bool} {s t : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I (fun p rs h g => SafeR I Q p t rs h g) p s rs h g) :
    SafeR I Q p (.seq s t) rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_seq H

theorem safeR_ite {p : Bool} {c : Expr} {s t : Stmt} {rs : Regs} {h g : Heap}
    (hs : truthy (c.eval rs) = true → SafeR I Q p s rs h g)
    (ht : truthy (c.eval rs) = false → SafeR I Q p t rs h g) :
    SafeR I Q p (.ite c s t) rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_ite hs ht

theorem safeR_loop {c : Expr} {b : Stmt} (J : Nat → Bool → Regs → Heap → Heap → Prop)
    (hexit : ∀ k p rs h g, J k p rs h g → truthy (c.eval rs) = false → Q p rs h g)
    (hbody : ∀ k p rs h g, J (k + 1) p rs h g → truthy (c.eval rs) = true →
      SafeR I (J k) p b rs h g)
    {n : Nat} {p : Bool} {rs : Regs} {h g : Heap} (hJ : J n p rs h g) :
    SafeR I Q p (.loop n c b) rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_loop J hexit hbody hJ

theorem safeR_assign {p : Bool} {d : Silmaril.X86.Concurrency.Cir.Reg} {e : Expr} {rs : Regs}
    {h g : Heap} (hq : Q p (rs.set d (e.eval rs)) h g) : SafeR I Q p (.assign d e) rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_assign hq

/-- **One labelled step**: the generic rule for an atomic statement, including a release store. -/
theorem safeR_atomic {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (hs : s ≠ .skip) (hτ : ∀ s' rs', ¬ TStep s rs none s' rs')
    (hl : ∀ l s' rs', TStep s rs (some l) s' rs' →
      s' = .skip ∧ LabOkR I (fun p' h' g' => Q p' rs' h' g') p l h g) :
    SafeR I Q p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_atomic hs hτ hl

/-- **The frame rule**: a disjoint frame is never touched and is still there at the end. -/
theorem safeR_frame {p : Bool} {s : Stmt} {rs : Regs} {h g hF : Heap}
    (H : SafeR I Q p s rs h g) (hd : Heap.Disjoint h hF) :
    SafeR I (fun p rs h' g' => ∃ h1, Q p rs h1 g' ∧ Heap.Disjoint h1 hF ∧
      h' = Heap.union h1 hF) p s rs (Heap.union h hF) g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_frame H hd

/-- **The invariant frame rule**: a thread safe under `I` stays safe when the
invariant is extended by any `J` (physical and ghost) it never opens. -/
theorem safeR_inv_frame {J : GProp} {p : Bool} {s : Stmt} {rs : Regs} {h g : Heap}
    (H : SafeR I Q p s rs h g) : SafeR (gsep I J) Q p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_inv_frame H

/-- **Code that drains first is safe from any pending flag.** -/
theorem safeR_flag {s : Stmt} {rs : Regs} (hdf : DF s rs) {h g : Heap}
    (H : SafeR I Q false s rs h g) (p : Bool) : SafeR I Q p s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_flag hdf H p

theorem df_seq_skip {s : Stmt} {rs : Regs} (h : DF s rs) : DF (.seq .skip s) rs :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.df_seq_skip h

theorem df_seq_assign {d : Silmaril.X86.Concurrency.Cir.Reg} {e : Expr} {s : Stmt} {rs : Regs}
    (h : ∀ rs', DF s rs') : DF (.seq (.assign d e) s) rs :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.df_seq_assign h

theorem df_seq_rmw {d : Silmaril.X86.Concurrency.Cir.Reg} {m : Silmaril.X86.Concurrency.Cir.Mode}
    {sz : Nat} {op : Silmaril.X86.Concurrency.Cir.RmwOp} {a arg : Expr} {t : Stmt} {rs : Regs} :
    DF (.seq (.rmw d m sz op a arg) t) rs :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.df_seq_rmw

/-! ## CSL proofs are `SafeR` proofs -/

/-- **Lifting**: a thread CSL-safe under `I0` is `SafeR` under any `I` whose states split into an
`I0` part and an untouched frame, with flag clear and ghost heap unchanged. -/
theorem safeR_lift {I0 : HProp} {Q0 : Regs → HProp} {g : Heap}
    (split : ∀ hI gI, I hI gI → ∃ hA hB, Heap.Disjoint hA hB ∧ hI = Heap.union hA hB ∧ I0 hA ∧
      ∀ hA', I0 hA' → Heap.Disjoint hA' hB → I (Heap.union hA' hB) gI)
    {s : Stmt} {rs : Regs} {h : Heap} (H : Safe I0 Q0 s rs h) :
    SafeR I (fun p rs h' g' => p = false ∧ Q0 rs h' ∧ g' = g) false s rs h g :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.safeR_lift split H

/-- **A CSL certificate is a `GInvR` certificate** with empty ghosts and the same invariant. -/
theorem ginvR_of_ginv {I0 : HProp} {Q0 : Nat → Regs → HProp} {N : Nat} {C : Cfg}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I0 Q0 N C hs hI) :
    GInvR (liftI I0) (fun t p rs h g => p = false ∧ Q0 t rs h ∧ g = Heap.empty) N C hs
      (fun _ => Heap.empty) hI Heap.empty := by
  obtain ⟨d1, d2, l1, l2, iI, safe⟩ := G
  refine ⟨d1, d2, fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, l1, l2, iI, fun t ht => ?_⟩
  exact safeR_lift (I0 := I0) (fun hI' _ i => ⟨hI', Heap.empty, fun _ => Or.inr rfl,
    (Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.union_empty_right hI').symm, i,
    fun hA' i' _ => by
      rw [Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.union_empty_right]; exact i'⟩)
    (safe t ht)

/-! ## Soundness on TSO -/

/-- **Soundness of the release rule on TSO.** From a `GInvR` start, every finished, drained
configuration of the CIR-native TSO store-buffer machine satisfies every thread's postcondition
and the invariant, with disjoint thread and invariant heaps inside memory; no ghost cell of `G0`
(which the start holds) is lost. -/
theorem rel_tso {Q : Nat → Bool → Regs → Heap → Heap → Prop} {N : Nat} {G0 : Heap} {C0 : Cfg}
    {hs gs : Nat → Heap} {hI gI : Heap} (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    {C : OCfg} (hr : OReach .tso N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.rel_tso G hG0 hr hd hf

/-- **`rel_tso` with ghost disjointness**: as `rel_tso`, and the threads' final
ghost heaps are pairwise disjoint and disjoint from the invariant's. -/
theorem rel_tsoG {Q : Nat → Bool → Regs → Heap → Heap → Prop} {N : Nat} {G0 : Heap} {C0 : Cfg}
    {hs gs : Nat → Heap} {hI gI : Heap} (G : GInvR I Q N C0 hs gs hI gI)
    (hG0 : ∀ c, (G0 c).isSome → (gI c).isSome ∨ ∃ t < N, (gs t c).isSome)
    {C : OCfg} (hr : OReach .tso N C0.toO C) (hd : C.Drained)
    (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' gs' : Nat → Heap) (hI' gI' : Heap) (ps' : Nat → Bool),
      (∀ t < N, Q t (ps' t) (C.ts t).2 (hs' t) (gs' t)) ∧ I hI' gI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem ∧
      (∀ t u, t ≠ u → Heap.Disjoint (hs' t) (hs' u)) ∧ (∀ t, Heap.Disjoint (hs' t) hI') ∧
      (∀ t u, t ≠ u → Heap.Disjoint (gs' t) (gs' u)) ∧ (∀ t, Heap.Disjoint (gs' t) gI') ∧
      (∀ c, (G0 c).isSome → (gI' c).isSome ∨ ∃ t < N, (gs' t c).isSome) :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.Rel.rel_tsoG G hG0 hr hd hf

/-- **The CSL guarantee, rederived** (a sanity check of the generalisation): a CSL certificate
gives the postconditions at every finished, drained TSO state through `rel_tso`. -/
theorem csl_tso_of_rel {I0 : HProp} {Q0 : Nat → Regs → HProp} {N : Nat} {C0 : Cfg}
    {hs : Nat → Heap} {hI : Heap} (G : GInv I0 Q0 N C0 hs hI) {C : OCfg}
    (hr : OReach .tso N C0.toO C) (hd : C.Drained) (hf : ∀ t < N, (C.ts t).1 = .skip) :
    ∃ (hs' : Nat → Heap) (hI' : Heap), (∀ t < N, Q0 t (C.ts t).2 (hs' t)) ∧ I0 hI' ∧
      (∀ t, Heap.Le (hs' t) C.mem) ∧ Heap.Le hI' C.mem := by
  obtain ⟨hs', _gs, hI', _gI, _ps, q, i, l1, l2, -, -, -⟩ :=
    rel_tso (G0 := Heap.empty) (ginvR_of_ginv G) (fun _ e => by cases e) hr hd hf
  exact ⟨hs', hI', fun t ht => (q t ht).2.1, i, l1, l2⟩

end Silmaril.X86.Concurrency.Cir.Csl.Rel
