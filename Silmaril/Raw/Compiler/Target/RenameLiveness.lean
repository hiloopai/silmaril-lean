module

public import Silmaril.Compiler.Target.RenameSets.Defs
/-! # `liveness` stops at a fixpoint

When `liveness` returns `some (liveIn, liveOut)`, its last backward pass changed no set.
The sets only grow and are sorted sets, so an unchanged size is an unchanged set: every
block's `gen ∪ (out \ kill)` lies in its `liveIn` and its `out` (the union of its
successors' `liveIn`) lies in its `liveOut`.
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- The live-out set `liveness` computes for block `b` from live-in sets `LI`. -/
def outOf (blocks : Array (Block Nat)) (LI : Array (Array Nat)) (b : Nat) : Array Nat :=
  (termSuccs (blocks[b]?.map (·.term) |>.getD .trap)).foldl
    (fun s l => union s (LI[l]?.getD #[])) #[]

private theorem mem_foldl_union {LI : Array (Array Nat)} {x : Nat} :
    ∀ {ls : List Nat} {acc : Array Nat},
      x ∈ ls.foldl (fun s (l : Nat) => union s (LI[l]?.getD #[])) acc ↔
        x ∈ acc ∨ ∃ l ∈ ls, x ∈ LI[l]?.getD #[]
  | [], _ => by simp
  | l :: ls, acc => by
    rw [List.foldl_cons, mem_foldl_union, mem_union]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_outOf {blocks : Array (Block Nat)} {LI : Array (Array Nat)} {b x : Nat} :
    x ∈ outOf blocks LI b ↔
      ∃ l ∈ termSuccs (blocks[b]?.map (·.term) |>.getD .trap), x ∈ LI[l]?.getD #[] := by
  simp [outOf, mem_foldl_union]

private theorem sset_foldl_union {LI : Array (Array Nat)} (h : ∀ l : Nat, SSet (LI[l]?.getD #[])) :
    ∀ {ls : List Nat} {acc : Array Nat}, SSet acc →
      SSet (ls.foldl (fun s (l : Nat) => union s (LI[l]?.getD #[])) acc)
  | [], _, ha => ha
  | l :: ls, _, ha => sset_foldl_union (ls := ls) h (union_sset ha (h l))

private theorem outOf_sset {blocks : Array (Block Nat)} {LI : Array (Array Nat)}
    (h : ∀ l : Nat, SSet (LI[l]?.getD #[])) (b : Nat) : SSet (outOf blocks LI b) :=
  sset_foldl_union h (by simp [SSet])

/-- The live-in set `liveness` computes for block `b` from live-in sets `LI`. -/
private def inOf (blocks : Array (Block Nat)) (LI : Array (Array Nat)) (b : Nat) : Array Nat :=
  union (blocks.map genKill)[b]!.1 (diff (outOf blocks LI b) (blocks.map genKill)[b]!.2)

private theorem gk_sset (blocks : Array (Block Nat)) (b : Nat) :
    SSet (blocks.map genKill)[b]!.1 ∧ SSet (blocks.map genKill)[b]!.2 := by
  by_cases hb : b < blocks.size
  · simpa [getElem!_pos (blocks.map genKill) b (by simpa using hb)] using genKill_sset blocks[b]
  · rw [getElem!_neg (blocks.map genKill) b (by simpa using hb)]
    exact ⟨List.Pairwise.nil, List.Pairwise.nil⟩

/-- One step of a backward pass of `liveness`. -/
private def passStep (blocks : Array (Block Nat)) (s : Array (Array Nat) × Array (Array Nat) × Bool)
    (k : Nat) : Array (Array Nat) × Array (Array Nat) × Bool :=
  if ((inOf blocks s.1 (blocks.size - 1 - k)).size != s.1[blocks.size - 1 - k]!.size ||
      (outOf blocks s.1 (blocks.size - 1 - k)).size != s.2.1[blocks.size - 1 - k]!.size) = true then
    (s.1.set! (blocks.size - 1 - k) (inOf blocks s.1 (blocks.size - 1 - k)),
      s.2.1.set! (blocks.size - 1 - k) (outOf blocks s.1 (blocks.size - 1 - k)), true)
  else (s.1, s.2.1, s.2.2)

private theorem passStep_eq (blocks : Array (Block Nat))
    (s : Array (Array Nat) × Array (Array Nat) × Bool) (k : Nat) :
    (if ((union (Array.map genKill blocks)[blocks.size - 1 - k]!.1
          (diff (List.foldl (fun a (l : Nat) => union a (s.1[l]?.getD #[])) #[]
              (termSuccs ((Option.map (fun x => x.term) blocks[blocks.size - 1 - k]?).getD Term.trap)))
            (Array.map genKill blocks)[blocks.size - 1 - k]!.2)).size != s.1[blocks.size - 1 - k]!.size ||
        (List.foldl (fun a (l : Nat) => union a (s.1[l]?.getD #[])) #[]
            (termSuccs ((Option.map (fun x => x.term) blocks[blocks.size - 1 - k]?).getD Term.trap))).size !=
          s.2.1[blocks.size - 1 - k]!.size) = true then
      pure (ForInStep.yield
        (s.1.set! (blocks.size - 1 - k)
            (union (Array.map genKill blocks)[blocks.size - 1 - k]!.1
              (diff (List.foldl (fun a (l : Nat) => union a (s.1[l]?.getD #[])) #[]
                  (termSuccs ((Option.map (fun x => x.term) blocks[blocks.size - 1 - k]?).getD Term.trap)))
                (Array.map genKill blocks)[blocks.size - 1 - k]!.2)),
          s.2.1.set! (blocks.size - 1 - k)
            (List.foldl (fun a (l : Nat) => union a (s.1[l]?.getD #[])) #[]
              (termSuccs ((Option.map (fun x => x.term) blocks[blocks.size - 1 - k]?).getD Term.trap))),
          true))
    else (pure (ForInStep.yield (s.1, s.2.1, s.2.2)) : Id _)) =
      pure (ForInStep.yield (passStep blocks s k)) := by
  unfold passStep inOf outOf
  split <;> rfl


private theorem getElem!_eq_getD (a : Array (Array Nat)) (c : Nat) : a[c]! = a[c]?.getD #[] := by
  by_cases hc : c < a.size
  · simp [getElem!_pos a c hc, getElem?_pos a c hc]
  · rw [getElem!_neg a c hc, getElem?_neg a c hc]; rfl

private theorem getD_set! {a : Array (Array Nat)} {b : Nat} (hb : b < a.size) (v : Array Nat)
    (l : Nat) : (a.set! b v)[l]?.getD #[] = if l = b then v else a[l]?.getD #[] := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : l = b
  · subst h; simp [hb]
  · simp [Ne.symm h, h]

/-- An SSet inside an SSet of no larger size has its members. -/
private theorem sset_sub_eq {a c : Array Nat} (ha : SSet a) (hc : SSet c)
    (hsub : ∀ x ∈ a, x ∈ c) (hsz : c.size ≤ a.size) : ∀ x ∈ c, x ∈ a := by
  have hna : a.toList.Nodup := List.Pairwise.imp (fun h => Nat.ne_of_lt h) ha
  have hnc : c.toList.Nodup := List.Pairwise.imp (fun h => Nat.ne_of_lt h) hc
  have hp := (hna.subperm fun x hx => Array.mem_toList_iff.mpr
    (hsub x (Array.mem_toList_iff.mp hx))).perm_of_length_le (by simpa using hsz)
  intro x hx
  exact Array.mem_toList_iff.mp (hp.mem_iff.mpr (Array.mem_toList_iff.mpr hx))

private def Le (LI LI' : Array (Array Nat)) : Prop :=
  ∀ (l x : Nat), x ∈ LI[l]?.getD #[] → x ∈ LI'[l]?.getD #[]

private theorem outOf_mono {blocks : Array (Block Nat)} {LI LI' : Array (Array Nat)}
    (hle : Le LI LI') {b x : Nat} (h : x ∈ outOf blocks LI b) : x ∈ outOf blocks LI' b := by
  obtain ⟨l, hl, hx⟩ := mem_outOf.mp h
  exact mem_outOf.mpr ⟨l, hl, hle l x hx⟩

private theorem inOf_mono {blocks : Array (Block Nat)} {LI LI' : Array (Array Nat)}
    (hs : ∀ l : Nat, SSet (LI[l]?.getD #[])) (hle : Le LI LI') {b x : Nat}
    (h : x ∈ inOf blocks LI b) : x ∈ inOf blocks LI' b := by
  unfold inOf at h ⊢
  rcases mem_union.mp h with hg | hd
  · exact mem_union.mpr (.inl hg)
  · obtain ⟨ho, hk⟩ := (mem_diff (outOf_sset hs b) (gk_sset blocks b).2).mp hd
    exact mem_union.mpr (.inr (mem_diff_of_mem (outOf_mono hle ho) hk))

private theorem inOf_sset {blocks : Array (Block Nat)} {LI : Array (Array Nat)}
    (hs : ∀ l : Nat, SSet (LI[l]?.getD #[])) (b : Nat) : SSet (inOf blocks LI b) :=
  union_sset (gk_sset blocks b).1 (diff_sset (outOf_sset hs b))

/-- The invariant of `liveness`: sorted sets that only grow towards the fixpoint. -/
private def Inv (blocks : Array (Block Nat)) (LI LO : Array (Array Nat)) : Prop :=
  LI.size = blocks.size ∧ LO.size = blocks.size ∧
    (∀ l : Nat, SSet (LI[l]?.getD #[])) ∧ (∀ l : Nat, SSet (LO[l]?.getD #[])) ∧
    (∀ (c x : Nat), x ∈ LI[c]?.getD #[] → x ∈ inOf blocks LI c) ∧
    (∀ (c x : Nat), x ∈ LO[c]?.getD #[] → x ∈ outOf blocks LI c)

private theorem Inv.update {blocks : Array (Block Nat)} {LI LO : Array (Array Nat)}
    (h : Inv blocks LI LO) {b : Nat} (hb : b < blocks.size) :
    Inv blocks (LI.set! b (inOf blocks LI b)) (LO.set! b (outOf blocks LI b)) := by
  obtain ⟨hLI, hLO, hsI, hsO, hin, hout⟩ := h
  have gI := getD_set! (hLI ▸ hb) (inOf blocks LI b)
  have gO := getD_set! (hLO ▸ hb) (outOf blocks LI b)
  have hle : Le LI (LI.set! b (inOf blocks LI b)) := by
    intro l x hx
    rw [gI]
    split
    · next e => subst e; exact hin l x hx
    · exact hx
  refine ⟨by simp [hLI], by simp [hLO], fun l => ?_, fun l => ?_, fun c x hx => ?_, fun c x hx => ?_⟩
  · rw [gI]; split
    · exact inOf_sset hsI b
    · exact hsI l
  · rw [gO]; split
    · exact outOf_sset hsI b
    · exact hsO l
  · rw [gI] at hx
    split at hx
    · next e => subst e; exact inOf_mono hsI hle hx
    · exact inOf_mono hsI hle (hin c x hx)
  · rw [gO] at hx
    split at hx
    · next e => subst e; exact outOf_mono hle hx
    · exact outOf_mono hle (hout c x hx)

/-- Block `b` is unchanged by a step of a pass. -/
private def Same (blocks : Array (Block Nat)) (LI LO : Array (Array Nat)) (b : Nat) : Prop :=
  (inOf blocks LI b).size = LI[b]!.size ∧ (outOf blocks LI b).size = LO[b]!.size

private theorem passStep_cases (blocks : Array (Block Nat)) (LI LO : Array (Array Nat)) (ch : Bool)
    (k : Nat) :
    passStep blocks (LI, LO, ch) k =
        (LI.set! (blocks.size - 1 - k) (inOf blocks LI (blocks.size - 1 - k)),
          LO.set! (blocks.size - 1 - k) (outOf blocks LI (blocks.size - 1 - k)), true) ∨
      (Same blocks LI LO (blocks.size - 1 - k) ∧ passStep blocks (LI, LO, ch) k = (LI, LO, ch)) := by
  unfold passStep
  split
  · exact .inl rfl
  · next hc =>
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
    exact .inr ⟨hc, rfl⟩

/-- Once a pass has changed a set, it says so. -/
private theorem foldl_passStep_flag {blocks : Array (Block Nat)} :
    ∀ (ks : List Nat) (s : Array (Array Nat) × Array (Array Nat) × Bool), s.2.2 = true →
      (ks.foldl (passStep blocks) s).2.2 = true
  | [], _, hs => hs
  | k :: ks, s, hs => by
    refine foldl_passStep_flag ks _ ?_
    unfold passStep
    split
    · rfl
    · exact hs

private theorem foldl_passStep {blocks : Array (Block Nat)} :
    ∀ (ks : List Nat) (LI LO : Array (Array Nat)) (ch : Bool), Inv blocks LI LO →
      (∀ k ∈ ks, k < blocks.size) →
      Inv blocks (ks.foldl (passStep blocks) (LI, LO, ch)).1
          (ks.foldl (passStep blocks) (LI, LO, ch)).2.1 ∧
        ((ks.foldl (passStep blocks) (LI, LO, ch)).2.2 = false →
          (ks.foldl (passStep blocks) (LI, LO, ch)).1 = LI ∧
          (ks.foldl (passStep blocks) (LI, LO, ch)).2.1 = LO ∧
          ∀ k ∈ ks, Same blocks LI LO (blocks.size - 1 - k))
  | [], LI, LO, _, h, _ => ⟨h, fun _ => ⟨rfl, rfl, by simp⟩⟩
  | k :: ks, LI, LO, ch, h, hks => by
    have hk : blocks.size - 1 - k < blocks.size := by
      have := hks k (by simp); omega
    rw [List.foldl_cons]
    rcases passStep_cases blocks LI LO ch k with he | ⟨hs, he⟩ <;> rw [he]
    · obtain ⟨hI, hF⟩ := foldl_passStep ks _ _ true (h.update hk) fun k' hk' => hks k' (by simp [hk'])
      refine ⟨hI, fun hf => ?_⟩
      have := foldl_passStep_flag (blocks := blocks) ks (LI.set! (blocks.size - 1 - k) (inOf blocks LI (blocks.size - 1 - k)),
        LO.set! (blocks.size - 1 - k) (outOf blocks LI (blocks.size - 1 - k)), true) rfl
      rw [hf] at this
      exact absurd this Bool.false_ne_true
    · obtain ⟨hI, hF⟩ := foldl_passStep ks LI LO ch h fun k' hk' => hks k' (by simp [hk'])
      refine ⟨hI, fun hf => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hF hf
      refine ⟨h1, h2, ?_⟩
      intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · exact hs
      · exact h3 k' hk'

/-- What a pass that changes nothing leaves: the invariant, and every block unchanged. -/
private def Fix (blocks : Array (Block Nat)) (LI LO : Array (Array Nat)) : Prop :=
  Inv blocks LI LO ∧ ∀ b, b < blocks.size → Same blocks LI LO b

private theorem pass_fix {blocks : Array (Block Nat)} {LI LO : Array (Array Nat)}
    (h : Inv blocks LI LO)
    (hf : (List.foldl (passStep blocks) (LI, LO, false) (List.range' 0 blocks.size)).2.2 = false) :
    Fix blocks (List.foldl (passStep blocks) (LI, LO, false) (List.range' 0 blocks.size)).1
      (List.foldl (passStep blocks) (LI, LO, false) (List.range' 0 blocks.size)).2.1 := by
  obtain ⟨-, hF⟩ := foldl_passStep (List.range' 0 blocks.size) LI LO false h
    fun k hk => by simp at hk; omega
  obtain ⟨h1, h2, h3⟩ := hF hf
  rw [h1, h2]
  refine ⟨h, fun b hb => ?_⟩
  have := h3 (blocks.size - 1 - b) (by simp; omega)
  rwa [show blocks.size - 1 - (blocks.size - 1 - b) = b by omega] at this

private theorem outer_loop {blocks : Array (Block Nat)} :
    ∀ (L : List Nat) (LI LO : Array (Array Nat)) (r : Array (Array Nat) × Array (Array Nat)),
      Inv blocks LI LO →
      (forIn (m := Id) L ((none : Option (Option (Array (Array Nat) × Array (Array Nat)))), LI, LO)
        fun _ __s =>
          if (!(List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                (List.range' 0 blocks.size)).2.2) = true then
            pure (ForInStep.done
              (some (some ((List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                    (List.range' 0 blocks.size)).1,
                  (List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                    (List.range' 0 blocks.size)).2.1)),
                (List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                  (List.range' 0 blocks.size)).1,
                (List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                  (List.range' 0 blocks.size)).2.1))
          else
            pure (ForInStep.yield
              (none, (List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                  (List.range' 0 blocks.size)).1,
                (List.foldl (fun b a => passStep blocks b a) (__s.2.1, __s.2.2, false)
                  (List.range' 0 blocks.size)).2.1))).1 = some (some r) →
      Fix blocks r.1 r.2
  | [], _, _, _, _, h => by simp at h
  | _ :: L, LI, LO, r, hI, h => by
    rw [List.forIn_cons] at h
    split at h
    · next hc =>
      simp only [Bool.not_eq_true', pure_bind] at hc h
      obtain rfl := Option.some.inj (Option.some.inj h)
      exact pass_fix hI hc
    · next hc =>
      simp only [pure_bind] at h
      exact outer_loop L _ _ r (foldl_passStep _ _ _ _ hI fun k hk => by simp at hk; omega).1 h

theorem liveness_fix {blocks : Array (Block Nat)} {fuel : Nat} {LI LO : Array (Array Nat)}
    (h : liveness blocks fuel = some (LI, LO)) :
    LI.size = blocks.size ∧ LO.size = blocks.size ∧
      ∀ b (hb : b < blocks.size) (x : Nat),
        (x ∈ union (genKill blocks[b]).1 (diff (outOf blocks LI b) (genKill blocks[b]).2) →
          x ∈ LI[b]!) ∧
        (x ∈ outOf blocks LI b → x ∈ LO[b]!) := by
  unfold liveness at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, passStep_eq,
    List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    Id.run_bind] at h
  split at h
  · next r heq =>
    have e : ∀ l : Nat, (blocks.map fun _ => (#[] : Array Nat))[l]?.getD #[] = #[] := by
      intro l
      rw [Array.getElem?_map]
      cases blocks[l]? <;> rfl
    have hinit : Inv blocks (blocks.map fun _ => #[]) (blocks.map fun _ => #[]) := by
      refine ⟨by simp, by simp, fun l => ?_, fun l => ?_, fun c x hx => ?_, fun c x hx => ?_⟩
      · rw [e]; exact List.Pairwise.nil
      · rw [e]; exact List.Pairwise.nil
      · rw [e] at hx; simp at hx
      · rw [e] at hx; simp at hx
    obtain ⟨⟨hLI, hLO, hsI, hsO, hin, hout⟩, hsame⟩ :=
      outer_loop (List.range' 0 fuel) _ _ (LI, LO) hinit
        (by rw [show r = some (LI, LO) by simpa using h] at heq; exact heq)
    refine ⟨hLI, hLO, fun b hb x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · have hg : (blocks.map genKill)[b]! = genKill blocks[b] := by
        simp [getElem!_pos (blocks.map genKill) b (by simpa using hb)]
      rw [getElem!_eq_getD]
      refine sset_sub_eq (hsI b) (inOf_sset hsI b) (hin b) ?_ x (by simpa [inOf, hg] using hx)
      rw [← getElem!_eq_getD]; exact (hsame b hb).1.le
    · rw [getElem!_eq_getD]
      refine sset_sub_eq (hsO b) (outOf_sset hsI b) (hout b) ?_ x hx
      rw [← getElem!_eq_getD]; exact (hsame b hb).2.le
  · simp at h

end Silmaril.Compile.Target.RegAlloc
