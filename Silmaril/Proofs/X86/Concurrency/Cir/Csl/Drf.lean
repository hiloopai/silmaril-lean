module

public import Silmaril.Proofs.X86.Concurrency.Cir.Csl.Sound

/-!
# CSL over CIR: ownership ⇒ DRF ⇒ SC for the store-buffer TSO and XL machines

The proof is a forward simulation of the buffered machine by the SC
machine through `OCfg.abs` (install every buffered value). The invariant `XInv` says every
buffered cell is owned by its thread, so

* a load reads its own buffer or memory, which is what the abstraction holds for the cells it
  may touch (its own, where only it buffers; the invariant's, which nobody buffers);
* a buffered store or block is an SC write of the abstraction (the cell is owned);
* a draining label runs with an empty buffer on cells nobody buffers;
* a flush does not change the abstraction (no earlier entry to the same cell, by
  `Ent.passes`; later ones win in both).

Stated in `Silmaril.X86.Concurrency.Cir.Csl.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir (Stmt Regs Expr Lab truthy cellVals cellLast)
open Silmaril.X86.Concurrency.Cir.Csl

/-! ## Buffers -/

theorem newest_append (b c : List Ent) (a : Nat) :
    newest (b ++ c) a = (newest c a).or (newest b a) := by
  induction b with
  | nil => simp [newest]
  | cons e b ih => simp only [List.cons_append, newest, ih, Option.or_assoc]

theorem newest_cellLast (outs : List (Nat × Nat × Nat)) (a : Nat) :
    newest (outs.map fun c => Ent.st c.1 c.2.2 false) a = cellLast outs a := by
  induction outs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, newest, ih, cellLast, Ent.val]

theorem newest_ents {l : Lab} (hd : l.drains = false) (a : Nat) : newest l.ents a = l.wval a := by
  cases l with
  | wr m fl a0 sz v => simp [Lab.ents, newest, Ent.val, Lab.wval]
  | blk n ins outs rvs => exact newest_cellLast outs a
  | fence k => cases k <;> simp_all [Lab.ents, newest, Ent.val, Lab.wval, Lab.drains]
  | _ => simp_all [Lab.ents, newest, Lab.wval, Lab.drains]

theorem passes_none {a v : Nat} {w : Bool} {pre : List Ent} (hp : (Ent.st a v w).passes pre) :
    newest pre a = none := by
  induction pre with
  | nil => rfl
  | cons e pre ih =>
    simp only [Ent.passes, List.mem_cons, forall_eq_or_imp] at hp
    obtain ⟨he, hp'⟩ := hp
    simp only [newest, ih hp']
    cases e with
    | bar => exact absurd he id
    | st a' v' w' => simp [Ent.val, he.1]

theorem firstNewest_congr {b b' : Nat → List Ent} {a : Nat}
    (h : ∀ u, newest (b u) a = newest (b' u) a) (us : List Nat) :
    firstNewest b a us = firstNewest b' a us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [firstNewest, h u, ih]

theorem firstNewest_only {b : Nat → List Ent} {a t : Nat}
    (h : ∀ u, u ≠ t → newest (b u) a = none) (us : List Nat) :
    firstNewest b a us = if t ∈ us then newest (b t) a else none := by
  induction us with
  | nil => simp [firstNewest]
  | cons u us ih =>
    simp only [firstNewest, ih, List.mem_cons]
    by_cases e : u = t
    · subst e; by_cases m : u ∈ us <;> simp [m]
    · rw [h u e, Option.none_or]
      by_cases m : t ∈ us <;> simp [m, Ne.symm e]

theorem firstNewest_none {b : Nat → List Ent} {a : Nat} (h : ∀ u, newest (b u) a = none)
    (us : List Nat) : firstNewest b a us = none := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [firstNewest, h u, ih, Option.none_or]

theorem map_getD_none (x : Option Nat) : (x.map fun v => (none : Option Nat).getD v) = x := by
  cases x <;> rfl

theorem abs_mem_isSome (N : Nat) (C : OCfg) (a : Nat) :
    ((C.abs N).mem a).isSome = (C.mem a).isSome := by
  simp [OCfg.abs]

/-! ## The invariant's consequences -/

section X
variable {I : HProp} {Q : Nat → Regs → HProp} {N : Nat}

theorem xinv_excl {C : OCfg} {hs : Nat → Heap} {hI : Heap} (X : XInv I Q N C hs hI) {t a : Nat}
    (e : (hs t a).isSome) : ∀ u, u ≠ t → newest (C.buf u) a = none := by
  intro u hu
  cases en : newest (C.buf u) a with
  | none => rfl
  | some _ =>
    have := (X.2 u a (by rw [en]; rfl)).2
    rcases X.1.1 u t hu a with e' | e'
    · rw [e'] at this; cases this
    · rw [e'] at e; cases e

theorem xinv_exclI {C : OCfg} {hs : Nat → Heap} {hI : Heap} (X : XInv I Q N C hs hI) {a : Nat}
    (e : (hI a).isSome) : ∀ u, newest (C.buf u) a = none := by
  intro u
  cases en : newest (C.buf u) a with
  | none => rfl
  | some _ =>
    have := (X.2 u a (by rw [en]; rfl)).2
    rcases X.1.2.1 u a with e' | e'
    · rw [e'] at this; cases this
    · rw [e'] at e; cases e

/-- A touched cell is buffered by nobody but (perhaps) the stepping thread. -/
theorem xinv_touch {C : OCfg} {hs : Nat → Heap} {hI : Heap} (X : XInv I Q N C hs hI) {t a : Nat}
    (e : (Heap.union (hs t) hI a).isSome) : ∀ u, u ≠ t → newest (C.buf u) a = none := by
  rw [union_isSome, Bool.or_eq_true] at e
  rcases e with e | e
  · exact xinv_excl X e
  · exact fun u _ => xinv_exclI X e u

theorem mem_some_of_owned {C : OCfg} {hs : Nat → Heap} {hI : Heap} (X : XInv I Q N C hs hI)
    {t a : Nat} (e : (Heap.union (hs t) hI a).isSome) : (C.mem a).isSome := by
  rw [← abs_mem_isSome N]
  exact isSome_of_le (union_le (X.1.2.2.1 t) X.1.2.2.2.1) e

/-- The abstraction holds the thread's view on every cell it may touch. -/
theorem view_eq_abs {C : OCfg} {hs : Nat → Heap} {hI : Heap} (X : XInv I Q N C hs hI) {t a : Nat}
    (ht : t < N) (e : (Heap.union (hs t) hI a).isSome) :
    view C.mem (C.buf t) a = (C.abs N).mem a := by
  have hm := mem_some_of_owned X e
  cases em : C.mem a with
  | none => rw [em] at hm; cases hm
  | some v =>
    simp only [view, OCfg.abs, em, Option.map_some, Option.or_some]
    rw [firstNewest_only (xinv_touch X e)]
    simp [List.mem_range, ht]

/-- With every buffer empty at `a`, the abstraction is memory at `a`. -/
theorem abs_eq_mem {C : OCfg} {a : Nat} (h : ∀ u, newest (C.buf u) a = none) (N : Nat) :
    (C.abs N).mem a = C.mem a := by
  simp only [OCfg.abs, firstNewest_none h]; exact map_getD_none _

/-! ## One step -/

theorem xinv_step {M : OModel} {C C' : OCfg} {hs : Nat → Heap} {hI : Heap}
    (X : XInv I Q N C hs hI) (hst : OStep M N C C') :
    (C'.abs N = C.abs N ∧ XInv I Q N C' hs hI) ∨
    (ScStep N (C.abs N) (C'.abs N) ∧ ∃ hs' hI', XInv I Q N C' hs' hI') := by
  cases hst with
  | tau ht st =>
    exact Or.inr ⟨ScStep.tau ht st, hs, hI, ginv_tau X.1 ht st, X.2⟩
  | @buffered t l s' rs' ht st hm hd hc hok =>
    have F := ginv_foot X.1 ht st
    have hok' : l.okH (C.abs N).mem :=
      okH_congr (fun a ta => view_eq_abs X ht (F.2.1 a ta)) hok
    have hc' : ∀ a, l.Touches a → ((C.abs N).mem a).isSome := fun a ta => by
      rw [abs_mem_isSome]; exact hc a ta
    have eqm : ({ C with ts := upd C.ts t (s', rs'), buf := upd C.buf t (C.buf t ++ l.ents) } :
        OCfg).abs N = ⟨upd C.ts t (s', rs'), l.updH (C.abs N).mem⟩ := by
      simp only [OCfg.abs, Cfg.mk.injEq, true_and]
      funext a
      rw [updH_apply]
      cases ew : l.wval a with
      | none =>
        rw [Option.none_or]
        congr 1; funext v; congr 1
        refine firstNewest_congr (fun u => ?_) _
        by_cases eu : u = t
        · subst eu; rw [upd_self, newest_append, newest_ents hd, ew, Option.none_or]
        · rw [upd_ne _ _ eu]
      | some w =>
        have own := F.2.2.2 hd a (by rw [ew]; rfl)
        have hm' := hc a (wval_touch (by rw [ew]; rfl))
        cases em : C.mem a with
        | none => rw [em] at hm'; cases hm'
        | some v =>
          simp only [Option.map_some, Option.some_or]
          rw [firstNewest_only (b := upd C.buf t (C.buf t ++ l.ents)) (t := t) (fun u hu => by
            rw [upd_ne _ _ hu]; exact xinv_excl X own u hu)]
          simp [List.mem_range, ht, upd_self, newest_append, newest_ents hd, ew]
    obtain ⟨h', hI', G', sur⟩ := ginv_lab X.1 ht st hok'
    refine Or.inr ⟨eqm ▸ ScStep.lab ht st hm hc' hok', upd hs t h', hI', eqm ▸ G', fun u a e => ?_⟩
    by_cases eu : u = t
    · subst eu
      simp only [upd_self, newest_append, newest_ents hd, or_isSome, Bool.or_eq_true] at e ⊢
      refine ⟨ht, sur hd a ?_⟩
      rcases e with e | e
      · exact F.2.2.2 hd a e
      · exact (X.2 u a e).2
    · simp only [upd_ne _ _ eu] at e ⊢; exact X.2 u a e
  | @drained t l s' rs' ht st hm hd he hc hok =>
    have F := ginv_foot X.1 ht st
    have nob : ∀ a, l.Touches a → ∀ u, newest (C.buf u) a = none := fun a ta u => by
      by_cases eu : u = t
      · subst eu; rw [he]; rfl
      · exact xinv_touch X (F.2.1 a ta) u eu
    have hok' : l.okH (C.abs N).mem :=
      okH_congr (fun a ta => (abs_eq_mem (nob a ta) N).symm) hok
    have hc' : ∀ a, l.Touches a → ((C.abs N).mem a).isSome := fun a ta => by
      rw [abs_mem_isSome]; exact hc a ta
    have eqm : ({ C with ts := upd C.ts t (s', rs'), mem := l.updH C.mem } : OCfg).abs N =
        ⟨upd C.ts t (s', rs'), l.updH (C.abs N).mem⟩ := by
      simp only [OCfg.abs, Cfg.mk.injEq, true_and]
      funext a
      cases ew : l.wval a with
      | none =>
        rw [updH_of_not ew, updH_of_not ew]
      | some w =>
        have nb := nob a (wval_touch (by rw [ew]; rfl))
        rw [firstNewest_none nb, map_getD_none]
        rw [updH_apply, updH_apply, ew, Option.some_or, Option.some_or]
    obtain ⟨h', hI', G', -⟩ := ginv_lab X.1 ht st hok'
    refine Or.inr ⟨eqm ▸ ScStep.lab ht st hm hc' hok', upd hs t h', hI', eqm ▸ G', fun u a e => ?_⟩
    by_cases eu : u = t
    · subst eu; rw [he] at e; cases e
    · simp only [upd_ne _ _ eu] at e ⊢; exact X.2 u a e
  | @flush t pre e post ht hb hp _ =>
    have eqm : ({ C with mem := e.apply C.mem, buf := upd C.buf t (pre ++ post) } : OCfg).abs N =
        C.abs N := by
      simp only [OCfg.abs, Cfg.mk.injEq, true_and]
      funext b
      cases e with
      | bar =>
        cases hp
        simp only [Ent.apply]
        congr 1; funext v; congr 1
        refine firstNewest_congr (fun u => ?_) _
        by_cases eu : u = t
        · subst eu; rw [upd_self, hb]; simp [newest, Ent.val]
        · rw [upd_ne _ _ eu]
      | st a v w =>
        by_cases eb : b = a
        · subst eb
          have hnb : (newest (C.buf t) b).isSome := by
            rw [hb, newest_append]; simp [newest, Ent.val]
          have own := (X.2 t b hnb).2
          have hm' : (C.mem b).isSome := by
            rw [← abs_mem_isSome N]
            exact isSome_of_le (X.1.2.2.1 t) own
          cases em : C.mem b with
          | none => rw [em] at hm'; cases hm'
          | some v0 =>
            simp only [Ent.apply, Option.map_some]
            rw [firstNewest_only (b := upd C.buf t (pre ++ post)) (t := t) (fun u hu => by
              rw [upd_ne _ _ hu]; exact xinv_excl X own u hu)]
            rw [firstNewest_only (b := C.buf) (t := t) (xinv_excl X own)]
            simp [List.mem_range, ht, upd_self, hb, newest_append, newest, Ent.val,
              passes_none hp, Option.or_some]
        · simp only [Ent.apply, eb, ↓reduceIte]
          congr 1; funext v0; congr 1
          refine firstNewest_congr (fun u => ?_) _
          by_cases eu : u = t
          · subst eu
            rw [upd_self, hb, newest_append, newest_append]
            simp [newest, Ent.val, Ne.symm eb]
          · rw [upd_ne _ _ eu]
    refine Or.inl ⟨eqm, ?_⟩
    refine ⟨eqm ▸ X.1, fun u a ea => ?_⟩
    by_cases eu : u = t
    · subst eu
      simp only [upd_self] at ea
      refine X.2 u a ?_
      rw [hb, newest_append, newest]
      rw [newest_append, or_isSome, Bool.or_eq_true] at ea
      simp only [or_isSome, Bool.or_eq_true]
      rcases ea with ea | ea
      · exact Or.inl (Or.inl ea)
      · exact Or.inr ea
    · simp only [upd_ne _ _ eu] at ea; exact X.2 u a ea

/-- **The simulation along runs.** -/
theorem xinv_reach {M : OModel} {C C' : OCfg} (h : OReach M N C C') :
    ∀ {hs : Nat → Heap} {hI : Heap}, XInv I Q N C hs hI →
      ScReach N (C.abs N) (C'.abs N) ∧ ∃ hs' hI', XInv I Q N C' hs' hI' := by
  induction h with
  | refl => exact fun X => ⟨Star.refl, _, _, X⟩
  | step h _ ih =>
    intro hs hI X
    rcases xinv_step X h with ⟨e, X'⟩ | ⟨s, hs', hI', X'⟩
    · obtain ⟨r, rest⟩ := ih X'; rw [e] at r; exact ⟨r, rest⟩
    · obtain ⟨r, rest⟩ := ih X'; exact ⟨Star.step s r, rest⟩

theorem abs_toO (N : Nat) (C : Cfg) : C.toO.abs N = C := by
  cases C with
  | mk ts mem =>
    simp only [Cfg.toO, OCfg.abs, Cfg.mk.injEq, true_and]
    funext a
    rw [firstNewest_none (fun _ => rfl)]; exact map_getD_none _

theorem abs_drained {C : OCfg} (h : C.Drained) (N : Nat) : C.abs N = ⟨C.ts, C.mem⟩ := by
  simp only [OCfg.abs, Cfg.mk.injEq, true_and]
  funext a
  rw [firstNewest_none (fun u => by rw [h u]; rfl)]; exact map_getD_none _

theorem xinv_init {C : Cfg} {hs : Nat → Heap} {hI : Heap} (G : GInv I Q N C hs hI) :
    XInv I Q N C.toO hs hI :=
  ⟨(abs_toO N C).symm ▸ G, fun _ _ e => by simp [Cfg.toO, newest] at e⟩

/-- **Ownership ⇒ DRF ⇒ SC** for the buffered machines: from a CSL-certified start, every
TSO/XL-reachable configuration abstracts to an SC-reachable one, and its CSL invariant
continues to hold. -/
theorem drf_reach {M : OModel} {C0 : Cfg} {hs : Nat → Heap} {hI : Heap}
    (G : GInv I Q N C0 hs hI) {C : OCfg} (h : OReach M N C0.toO C) :
    ScReach N C0 (C.abs N) ∧ ∃ hs' hI', XInv I Q N C hs' hI' := by
  have := xinv_reach h (xinv_init G)
  rw [abs_toO] at this; exact this

end X

end Silmaril.Proofs.X86.Concurrency.Cir.Csl
