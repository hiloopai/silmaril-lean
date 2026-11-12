module

public import Silmaril.Compiler.Target.RenameAssign.Defs
public import Std.Data.HashMap.Lemmas
public import Init.Data.Range.Lemmas

/-! # The intervals of `infos`

`infos` walks the points of a function in list order and extends the interval of every
register at each point where it is live in, used, defined or live out. `infos_cover` lists
the positions every block contributes (`Covers m v q`: the interval of `v` contains `q`),
with `blockPos` the index of a block's header.
-/

@[expose] public section

namespace Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine Silmaril.Machine.Lir

/-- The index of the header of block `b` among the points of the function: each block
has a header, its instructions and its terminator. -/
def blockPos (blocks : Array (Block Nat)) (b : Nat) : Nat :=
  ((blocks.toList.take b).map fun blk => blk.instrs.length + 2).sum

/-- Every interval of `m` is nonempty. -/
private def InfoWF (m : Std.HashMap Nat Info) : Prop :=
  ∀ (v : Nat) (i : Info), m[v]? = some i → i.start ≤ i.stop

/-- `m'` keeps the intervals of `m` (and their well-formedness). -/
private def Grows (m m' : Std.HashMap Nat Info) : Prop :=
  (∀ u q, Covers m u q → Covers m' u q) ∧ (InfoWF m → InfoWF m')

private theorem Grows.refl (m : Std.HashMap Nat Info) : Grows m m := ⟨fun _ _ h => h, id⟩

private theorem Grows.trans {m₁ m₂ m₃ : Std.HashMap Nat Info} (h₁ : Grows m₁ m₂)
    (h₂ : Grows m₂ m₃) : Grows m₁ m₃ :=
  ⟨fun u q h => h₂.1 u q (h₁.1 u q h), fun h => h₂.2 (h₁.2 h)⟩

private theorem grows_ext (m : Std.HashMap Nat Info) (v pos w : Nat) :
    Grows m (m.insert v (Info.extend m[v]? pos w)) := by
  refine ⟨fun u q ⟨i, hi, h₁, h₂⟩ => ?_, fun h u i hi => ?_⟩
  · rw [Covers, Std.HashMap.getElem?_insert]
    by_cases hvu : v = u
    · subst hvu
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, exists_eq_left', hi,
        Info.extend]
      omega
    · simp only [beq_iff_eq, hvu, ↓reduceIte]
      exact ⟨i, hi, h₁, h₂⟩
  · rw [Std.HashMap.getElem?_insert] at hi
    by_cases hvu : v = u
    · subst hvu
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hi
      subst hi
      cases hm : m[v]? with
      | none => simp [Info.extend]
      | some j => have := h v j hm; simp only [Info.extend]; omega
    · simp only [beq_iff_eq, hvu, ↓reduceIte] at hi
      exact h u i hi

private theorem covers_ext (m : Std.HashMap Nat Info) (v pos w : Nat) :
    Covers (m.insert v (Info.extend m[v]? pos w)) v pos := by
  refine ⟨Info.extend m[v]? pos w, by simp, ?_⟩
  cases m[v]? <;> simp only [Info.extend] <;> omega

private theorem grows_foldl (l : List Nat) (pos w : Nat) :
    ∀ m : Std.HashMap Nat Info,
      Grows m (l.foldl (fun b a => b.insert a (Info.extend b[a]? pos w)) m) := by
  induction l with
  | nil => exact Grows.refl
  | cons a l ih => exact fun m => (grows_ext m a pos w).trans (ih _)

private theorem covers_foldl {l : List Nat} {v : Nat} (hv : v ∈ l) (pos w : Nat) :
    ∀ m : Std.HashMap Nat Info,
      Covers (l.foldl (fun b a => b.insert a (Info.extend b[a]? pos w)) m) v pos := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    intro m
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (grows_foldl l pos w _).1 _ _ (covers_ext m v pos w)
    · exact ih hv _

private theorem forIn_inv {α β : Type} {l : List α} {init : β} {f : α → β → Id (ForInStep β)}
    (I : Nat → β → Prop) (h0 : I 0 init)
    (hs : ∀ j (hj : j < l.length) s, I j s → ∃ s', f l[j] s = .yield s' ∧ I (j + 1) s') :
    I l.length (forIn l init f).run := by
  induction l generalizing init I with
  | nil => simpa using h0
  | cons a l ih =>
    obtain ⟨s', hf, hI⟩ := hs 0 (by simp) init h0
    rw [List.forIn_cons]
    simp only [List.getElem_cons_zero] at hf
    simp only [hf]
    exact ih (I := fun j s => I (j + 1) s) hI fun j hj s h => hs (j + 1) (by simp; omega) s h

private theorem forIn'_range_inv {β : Type} {init : β} :
    ∀ (s k : Nat) {f : (a : Nat) → a ∈ List.range' s k → β → Id (ForInStep β)}
      (I : Nat → β → Prop), I s init →
      (∀ a (h : a ∈ List.range' s k) st, I a st → ∃ st', f a h st = .yield st' ∧ I (a + 1) st') →
      I (s + k) (forIn' (List.range' s k) init f).run := by
  intro s k
  induction k generalizing s init with
  | zero => intro f I h0 _; simpa using h0
  | succ k ih =>
    intro f I h0 hs
    obtain ⟨s', hf, hI⟩ := hs s (by simp) init h0
    simp only [List.range'_succ, List.forIn'_cons, hf]
    have := ih (s + 1) (init := s') (f := fun a h st => f a (List.mem_cons_of_mem s h) st) I hI
      fun a h st hst => hs a _ st hst
    rw [show s + 1 + k = s + (k + 1) by omega] at this
    exact this

private theorem forIn'_range0_inv {β : Type} {init : β} {n : Nat}
    {f : (a : Nat) → a ∈ List.range' 0 n → β → Id (ForInStep β)}
    {I : Nat → β → Prop} (h0 : I 0 init)
    (hs : ∀ a (h : a ∈ List.range' 0 n) st, I a st → ∃ st', f a h st = .yield st' ∧ I (a + 1) st') :
    I n (forIn' (List.range' 0 n) init f).run := by
  simpa using forIn'_range_inv 0 n I h0 hs

/-- The covers block `b` contributes (the conclusion of `infos_cover`). -/
private def BlockFacts (fn : Func Nat) (blocks : Array (Block Nat)) (LI LO : Array (Array Nat))
    (m : Std.HashMap Nat Info) (b : Nat) (hb : b < blocks.size) : Prop :=
  (∀ v ∈ LI[b]!, Covers m v (2 * blockPos blocks b)) ∧
    (b = fn.entry → ∀ v ∈ locRegs fn.params, Covers m v (2 * blockPos blocks b + 1)) ∧
    (∀ j (hj : j < blocks[b].instrs.length),
      (∀ v ∈ instrUses blocks[b].instrs[j], Covers m v (2 * (blockPos blocks b + 1 + j))) ∧
      (∀ v ∈ instrDefs blocks[b].instrs[j], Covers m v (2 * (blockPos blocks b + 1 + j) + 1))) ∧
    (∀ v ∈ termUses blocks[b].term,
      Covers m v (2 * (blockPos blocks b + 1 + blocks[b].instrs.length))) ∧
    (∀ v ∈ LO[b]!, Covers m v (2 * (blockPos blocks b + 1 + blocks[b].instrs.length) + 1))

private theorem BlockFacts.mono {fn : Func Nat} {blocks : Array (Block Nat)}
    {LI LO : Array (Array Nat)} {m m' : Std.HashMap Nat Info} {b : Nat} {hb : b < blocks.size}
    (hg : Grows m m') (h : BlockFacts fn blocks LI LO m b hb) : BlockFacts fn blocks LI LO m' b hb :=
  ⟨fun v hv => hg.1 _ _ (h.1 v hv), fun he v hv => hg.1 _ _ (h.2.1 he v hv),
    fun j hj => ⟨fun v hv => hg.1 _ _ ((h.2.2.1 j hj).1 v hv),
      fun v hv => hg.1 _ _ ((h.2.2.1 j hj).2 v hv)⟩,
    fun v hv => hg.1 _ _ (h.2.2.2.1 v hv), fun v hv => hg.1 _ _ (h.2.2.2.2 v hv)⟩

private theorem grows_afoldl (l : Array Nat) (pos w : Nat) (m : Std.HashMap Nat Info) :
    Grows m (l.foldl (fun b a => b.insert a (Info.extend b[a]? pos w)) m) := by
  rw [← Array.foldl_toList]
  exact grows_foldl _ pos w m

private theorem covers_afoldl {l : Array Nat} {v : Nat} (hv : v ∈ l) (pos w : Nat)
    (m : Std.HashMap Nat Info) :
    Covers (l.foldl (fun b a => b.insert a (Info.extend b[a]? pos w)) m) v pos := by
  rw [← Array.foldl_toList]
  exact covers_foldl (Array.mem_toList_iff.mpr hv) pos w m

/-- The instruction loop of one block of `infos`. -/
private def instrsFold (w : Nat) (l : List (Instr Nat)) (s : Std.HashMap Nat Info × Nat) :
    Std.HashMap Nat Info × Nat :=
  l.foldl (fun b i =>
    ((instrDefs i).foldl (fun b₁ v => b₁.insert v (Info.extend b₁[v]? (2 * b.2 + 1) w))
      ((instrUses i).foldl (fun b₁ v => b₁.insert v (Info.extend b₁[v]? (2 * b.2) w)) b.1),
      b.2 + 1)) s

private theorem instrsFold_spec (w : Nat) :
    ∀ (l : List (Instr Nat)) (m : Std.HashMap Nat Info) (p : Nat),
      (instrsFold w l (m, p)).2 = p + l.length ∧ Grows m (instrsFold w l (m, p)).1 ∧
      ∀ j (hj : j < l.length),
        (∀ v ∈ instrUses l[j], Covers (instrsFold w l (m, p)).1 v (2 * (p + j))) ∧
        (∀ v ∈ instrDefs l[j], Covers (instrsFold w l (m, p)).1 v (2 * (p + j) + 1)) := by
  intro l
  induction l with
  | nil => intro m p; exact ⟨rfl, Grows.refl m, fun j hj => absurd hj (by simp)⟩
  | cons i l ih =>
    intro m p
    obtain ⟨h₁, h₂, h₃⟩ := ih ((instrDefs i).foldl
      (fun b₁ v => b₁.insert v (Info.extend b₁[v]? (2 * p + 1) w))
      ((instrUses i).foldl (fun b₁ v => b₁.insert v (Info.extend b₁[v]? (2 * p) w)) m)) (p + 1)
    have hu := grows_foldl (instrUses i) (2 * p) w m
    have hd := grows_foldl (instrDefs i) (2 * p + 1) w
      ((instrUses i).foldl (fun b₁ v => b₁.insert v (Info.extend b₁[v]? (2 * p) w)) m)
    refine ⟨?_, hu.trans (hd.trans h₂), ?_⟩
    · show (instrsFold w l _).2 = _
      rw [h₁]; simp; omega
    · intro j hj
      cases j with
      | zero =>
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · exact h₂.1 _ _ (hd.1 _ _ (by simpa using covers_foldl hv (2 * p) w m))
        · exact h₂.1 _ _ (by simpa using covers_foldl hv (2 * p + 1) w _)
      | succ j =>
        have := h₃ j (by simpa using hj)
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · have h := this.1 v (by simpa using hv)
          rw [show p + 1 + j = p + (j + 1) by omega] at h
          exact h
        · have h := this.2 v (by simpa using hv)
          rw [show p + 1 + j = p + (j + 1) by omega] at h
          exact h

/-- One block of `infos` after its header: instructions, terminator uses, live-out set. -/
private def blockTail (w : Nat) (blk : Block Nat) (lo : Array Nat) (m : Std.HashMap Nat Info)
    (p : Nat) : Std.HashMap Nat Info × Nat :=
  (lo.foldl (fun b v => b.insert v (Info.extend b[v]? (2 * (instrsFold w blk.instrs (m, p + 1)).2 + 1) 0))
    ((termUses blk.term).foldl
      (fun b v => b.insert v (Info.extend b[v]? (2 * (instrsFold w blk.instrs (m, p + 1)).2) w))
      (instrsFold w blk.instrs (m, p + 1)).1),
    (instrsFold w blk.instrs (m, p + 1)).2 + 1)

private theorem blockTail_spec (w : Nat) (blk : Block Nat) (lo : Array Nat)
    (m : Std.HashMap Nat Info) (p : Nat) :
    (blockTail w blk lo m p).2 = p + (blk.instrs.length + 2) ∧ Grows m (blockTail w blk lo m p).1 ∧
    (∀ j (hj : j < blk.instrs.length),
      (∀ v ∈ instrUses blk.instrs[j], Covers (blockTail w blk lo m p).1 v (2 * (p + 1 + j))) ∧
      (∀ v ∈ instrDefs blk.instrs[j], Covers (blockTail w blk lo m p).1 v (2 * (p + 1 + j) + 1))) ∧
    (∀ v ∈ termUses blk.term,
      Covers (blockTail w blk lo m p).1 v (2 * (p + 1 + blk.instrs.length))) ∧
    (∀ v ∈ lo, Covers (blockTail w blk lo m p).1 v (2 * (p + 1 + blk.instrs.length) + 1)) := by
  obtain ⟨h₁, h₂, h₃⟩ := instrsFold_spec w blk.instrs m (p + 1)
  have ht := grows_foldl (termUses blk.term) (2 * (instrsFold w blk.instrs (m, p + 1)).2) w
    (instrsFold w blk.instrs (m, p + 1)).1
  have hl := grows_afoldl lo (2 * (instrsFold w blk.instrs (m, p + 1)).2 + 1) 0
    ((termUses blk.term).foldl
      (fun b v => b.insert v (Info.extend b[v]? (2 * (instrsFold w blk.instrs (m, p + 1)).2) w))
      (instrsFold w blk.instrs (m, p + 1)).1)
  refine ⟨?_, h₂.trans (ht.trans hl), fun j hj => ⟨fun v hv => ?_, fun v hv => ?_⟩,
    fun v hv => ?_, fun v hv => ?_⟩
  · simp only [blockTail, h₁]; omega
  · exact hl.1 _ _ (ht.1 _ _ ((h₃ j hj).1 v hv))
  · exact hl.1 _ _ (ht.1 _ _ ((h₃ j hj).2 v hv))
  · have := hl.1 _ _ (covers_foldl hv (2 * (instrsFold w blk.instrs (m, p + 1)).2) w
      (instrsFold w blk.instrs (m, p + 1)).1)
    obtain ⟨i, hi, hs, he⟩ := this
    exact ⟨i, hi, by omega, by omega⟩
  · have := covers_afoldl hv (2 * (instrsFold w blk.instrs (m, p + 1)).2 + 1) 0
      ((termUses blk.term).foldl
        (fun b v => b.insert v (Info.extend b[v]? (2 * (instrsFold w blk.instrs (m, p + 1)).2) w))
        (instrsFold w blk.instrs (m, p + 1)).1)
    obtain ⟨i, hi, hs, he⟩ := this
    exact ⟨i, hi, by omega, by omega⟩

private theorem blockPos_succ {blocks : Array (Block Nat)} {a : Nat} (ha : a < blocks.size) :
    blockPos blocks (a + 1) = blockPos blocks a + (blocks[a].instrs.length + 2) := by
  simp [blockPos, List.take_add_one, getElem?_pos blocks a ha]

/-- The induction step of `infos` at block `a`, from the map after its live-in set (and its
parameters, at the entry). -/
private theorem block_step (fn : Func Nat) (blocks : Array (Block Nat)) (LI LO : Array (Array Nat))
    (a : Nat) (ha : a < blocks.size) (st : Std.HashMap Nat Info × Nat) (m₂ : Std.HashMap Nat Info)
    (w : Nat)
    (hst : st.2 = blockPos blocks a ∧ InfoWF st.1 ∧
      ∀ b (hb : b < blocks.size), b < a → BlockFacts fn blocks LI LO st.1 b hb)
    (hg : Grows st.1 m₂)
    (hin : ∀ v ∈ LI[a]!, Covers m₂ v (2 * st.2))
    (hpar : a = fn.entry → ∀ v ∈ locRegs fn.params, Covers m₂ v (2 * st.2 + 1)) :
    (blockTail w blocks[a] LO[a]! m₂ st.2).2 = blockPos blocks (a + 1) ∧
      InfoWF (blockTail w blocks[a] LO[a]! m₂ st.2).1 ∧
      ∀ b (hb : b < blocks.size), b < a + 1 →
        BlockFacts fn blocks LI LO (blockTail w blocks[a] LO[a]! m₂ st.2).1 b hb := by
  obtain ⟨hp, hwf, hfacts⟩ := hst
  obtain ⟨t₁, t₂, t₃, t₄, t₅⟩ := blockTail_spec w blocks[a] LO[a]! m₂ st.2
  refine ⟨by rw [t₁, blockPos_succ ha, hp], t₂.2 (hg.2 hwf), fun b hb hba => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hba with hlt | rfl
  · exact (hfacts b hb hlt).mono (hg.trans t₂)
  · unfold BlockFacts
    rw [← hp]
    exact ⟨fun v hv => t₂.1 _ _ (hin v hv), fun he v hv => t₂.1 _ _ (hpar he v hv), t₃, t₄, t₅⟩

/-- The parameter fix-up at the end of `infos` inserts only absent registers. -/
private theorem fixup_grows (params : List Nat) (m : Std.HashMap Nat Info) (q : Nat) :
    Grows m (forIn (m := Id) params m fun v s =>
      if (!s.contains v) = true then pure (ForInStep.yield (s.insert v ⟨q, q, 0⟩))
      else pure (ForInStep.yield s)).run := by
  refine forIn_inv (I := fun _ s => Grows m s) (Grows.refl m) fun j _ s hs => ?_
  split
  · next hc =>
    refine ⟨_, rfl, hs.trans ⟨fun u q' ⟨i, hi, h₁, h₂⟩ => ?_, fun h u i hi => ?_⟩⟩
    · have hn : s[params[j]]? = none := by simpa using hc
      rw [Covers, Std.HashMap.getElem?_insert]
      by_cases hu : params[j] = u
      · subst hu; rw [hn] at hi; cases hi
      · simp only [beq_iff_eq, hu, ↓reduceIte]; exact ⟨i, hi, h₁, h₂⟩
    · rw [Std.HashMap.getElem?_insert] at hi
      by_cases hu : params[j] = u
      · subst hu; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hi; subst hi
        exact Nat.le_refl q
      · simp only [beq_iff_eq, hu, ↓reduceIte] at hi; exact h u i hi
  · exact ⟨_, rfl, hs⟩

private theorem infos_spec (fn : Func Nat) (blocks : Array (Block Nat)) (LI LO : Array (Array Nat)) :
    InfoWF (infos fn blocks LI LO) ∧
      ∀ b (hb : b < blocks.size), BlockFacts fn blocks LI LO (infos fn blocks LI LO) b hb := by
  unfold infos
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hR : (forIn' (m := Id) (List.range' _ _) ((∅ : Std.HashMap Nat Info), (0:Nat)) _ :
    Id (Std.HashMap Nat Info × Nat)) = R
  have hRinv : R.run.2 = blockPos blocks blocks.size ∧ InfoWF R.run.1 ∧
      ∀ b (hb : b < blocks.size), b < blocks.size → BlockFacts fn blocks LI LO R.run.1 b hb := by
    rw [← hR]
    refine forIn'_range0_inv (I := fun a (st : Std.HashMap Nat Info × Nat) => st.2 = blockPos blocks a ∧
        InfoWF st.1 ∧
        ∀ b (hb : b < blocks.size), b < a → BlockFacts fn blocks LI LO st.1 b hb) ?_ ?_
    · exact ⟨rfl, fun v i h => by simp at h, fun b _ h => absurd h (Nat.not_lt_zero b)⟩
    · intro a ha st hst
      have ha' : a < blocks.size := by simpa using ha
      simp only [List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl,
        pure_bind]
      have g₁ := grows_afoldl LI[a]! (2 * st.2) 0 st.1
      have c₁ := fun v (hv : v ∈ LI[a]!) => covers_afoldl hv (2 * st.2) 0 st.1
      split
      · have g₂ := grows_foldl (locRegs fn.params) (2 * st.2 + 1) 1
          (LI[a]!.foldl (fun b v => b.insert v (Info.extend b[v]? (2 * st.2) 0)) st.1)
        exact ⟨blockTail (8 ^ min (loopDepth blocks)[a]! 4) blocks[a] LO[a]!
          ((locRegs fn.params).foldl (fun b v => b.insert v (Info.extend b[v]? (2 * st.2 + 1) 1))
            (LI[a]!.foldl (fun b v => b.insert v (Info.extend b[v]? (2 * st.2) 0)) st.1)) st.2, rfl,
          block_step fn blocks LI LO a ha' st _ _ hst (g₁.trans g₂) (fun v hv => g₂.1 _ _ (c₁ v hv))
            (fun _ v hv => covers_foldl hv (2 * st.2 + 1) 1 _)⟩
      · next he =>
        exact ⟨blockTail (8 ^ min (loopDepth blocks)[a]! 4) blocks[a] LO[a]!
          (LI[a]!.foldl (fun b v => b.insert v (Info.extend b[v]? (2 * st.2) 0)) st.1) st.2, rfl,
          block_step fn blocks LI LO a ha' st _ _ hst g₁ c₁
            (fun h => absurd (beq_iff_eq.mpr h) he)⟩
  have hfin := fixup_grows (locRegs fn.params) R.run.1 (2 * R.run.2)
  exact ⟨hfin.2 hRinv.2.1, fun b hb => (hRinv.2.2 b hb hb).mono hfin⟩

theorem infos_wf (fn : Func Nat) (blocks : Array (Block Nat)) (LI LO : Array (Array Nat))
    {v : Nat} {i : Info} (h : (infos fn blocks LI LO)[v]? = some i) : i.start ≤ i.stop :=
  (infos_spec fn blocks LI LO).1 v i h

theorem infos_cover (fn : Func Nat) (blocks : Array (Block Nat)) (LI LO : Array (Array Nat))
    (b : Nat) (hb : b < blocks.size) :
    (∀ v ∈ LI[b]!, Covers (infos fn blocks LI LO) v (2 * blockPos blocks b)) ∧
    (b = fn.entry → ∀ v ∈ locRegs fn.params,
      Covers (infos fn blocks LI LO) v (2 * blockPos blocks b + 1)) ∧
    (∀ j (hj : j < blocks[b].instrs.length),
      (∀ v ∈ instrUses blocks[b].instrs[j],
        Covers (infos fn blocks LI LO) v (2 * (blockPos blocks b + 1 + j))) ∧
      (∀ v ∈ instrDefs blocks[b].instrs[j],
        Covers (infos fn blocks LI LO) v (2 * (blockPos blocks b + 1 + j) + 1))) ∧
    (∀ v ∈ termUses blocks[b].term,
      Covers (infos fn blocks LI LO) v (2 * (blockPos blocks b + 1 + blocks[b].instrs.length))) ∧
    (∀ v ∈ LO[b]!,
      Covers (infos fn blocks LI LO) v
        (2 * (blockPos blocks b + 1 + blocks[b].instrs.length) + 1)) :=
  (infos_spec fn blocks LI LO).2 b hb

end Silmaril.Compile.Target.RegAlloc
