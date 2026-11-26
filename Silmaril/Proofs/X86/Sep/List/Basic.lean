module

public import Silmaril.X86.Sep.List.Defs
public import Silmaril.X86.Sep.Thms
public import Silmaril.X86.Ext.Semantics

/-!
# Proofs: list segments, their laws, and reading and writing them in memory

Behind `Silmaril/X86/Sep/List/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.List

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (loadN storeN leBytes leValue)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

/-! ## Fragments (small local copies of the PCM facts) -/

theorem isSome_union {a b : Frag} {l : Loc} :
    (union a b l).isSome ↔ (a l).isSome ∨ (b l).isSome := by
  unfold union; cases a l <;> simp

theorem le_union_left {a b s : Frag} (h : Le (union a b) s) : Le a s := fun l v hl =>
  h l v (by simp [union, hl])

theorem le_union_right {a b s : Frag} (hd : Disjoint a b) (h : Le (union a b) s) : Le b s :=
  fun l v hl => h l v (by
    rcases hd l with e | e
    · simp [union, e, hl]
    · rw [e] at hl; cases hl)

theorem le_trans {a b c : Frag} (h₁ : Le a b) (h₂ : Le b c) : Le a c :=
  fun l v e => h₂ l v (h₁ l v e)

theorem not_both {a b : Frag} (h : Disjoint a b) {l : Loc} (ha : (a l).isSome)
    (hb : (b l).isSome) : False := by
  rcases h l with e | e <;> simp_all

theorem reval_of_le {h s : Frag} (hl : Le h s) : reval h s = h := by
  funext l
  unfold reval
  cases e : h l with
  | none => simp
  | some v => simp [hl l v e]

/-! ## Memory-only fragments -/

theorem memOnly_empty : MemOnly Frag.empty := fun _ h => by simp [Frag.empty] at h

theorem memOnly_union {a b : Frag} (ha : MemOnly a) (hb : MemOnly b) : MemOnly (union a b) :=
  fun l h => (isSome_union.mp h).elim (ha l) (hb l)

theorem memOnly_sep {P Q : SProp} (hP : ∀ f, P f → MemOnly f) (hQ : ∀ f, Q f → MemOnly f) :
    ∀ f, (P ∗ Q) f → MemOnly f := by
  rintro _ ⟨a, b, -, rfl, ha, hb⟩
  exact memOnly_union (hP a ha) (hQ b hb)

theorem memOnly_spure (φ : Prop) : ∀ f, (⌜φ⌝ : SProp) f → MemOnly f := by
  rintro f ⟨rfl, -⟩; exact memOnly_empty

theorem memOnly_bytesAt {need : Silmaril.Process.Permissions → Prop} :
    ∀ (a : Nat) (bs : List Byte) (f : Frag), bytesAt need a bs f → MemOnly f
  | _, [], f, h => by rw [show f = Frag.empty from h]; exact memOnly_empty
  | a, b :: bs, f, h => by
    refine memOnly_sep (P := byteAt need a b) (Q := bytesAt need (a + 1) bs) ?_
      (memOnly_bytesAt (a + 1) bs) f h
    rintro g ⟨-, p, -, rfl⟩ l hl
    by_cases e : l = .mem a
    · exact ⟨a, e⟩
    · simp [Frag.single, e] at hl

theorem memOnly_nodePt (p v n : Word) : ∀ f, nodePt p v n f → MemOnly f :=
  memOnly_sep (memOnly_bytesAt _ _) (memOnly_bytesAt _ _)

theorem memOnly_lseg : ∀ (xs : List Word) (p q : Word) (f : Frag), lseg p q xs f → MemOnly f
  | [], p, q, f, h => memOnly_spure (p = q) f h
  | x :: xs, p, q, f, ⟨n, h⟩ =>
    memOnly_sep (memOnly_spure _) (memOnly_sep (memOnly_nodePt p x n) (memOnly_lseg xs n q)) f h

/-! ## Re-reading fragments in a memory -/

theorem memFrag_le (d : Frag) (m : MState) : Le (memFrag d m.memory) (toFrag m) := by
  intro l v h
  cases l with
  | mem a =>
    simp only [memFrag] at h
    split at h
    · cases h; rfl
    · cases h
  | _ => simp [memFrag] at h

theorem reval_eq_memFrag {d : Frag} (hd : MemOnly d) (m : MState) :
    reval d (toFrag m) = memFrag d m.memory := by
  funext l
  unfold reval
  cases l with
  | mem a => simp only [memFrag]; split <;> rfl
  | _ =>
    simp only [memFrag]
    split
    · next h => obtain ⟨_, e⟩ := hd _ h; cases e
    · rfl

theorem memFrag_of_le {d : Frag} (hd : MemOnly d) {m : MState} (hl : Le d (toFrag m)) :
    memFrag d m.memory = d := by
  rw [← reval_eq_memFrag hd, reval_of_le hl]

theorem memFrag_isSome {d : Frag} {mem : Memory} {a : Nat} :
    (memFrag d mem (.mem a)).isSome = (d (.mem a)).isSome := by
  simp only [memFrag]; split <;> simp_all

/-! ## Segment laws -/

theorem lseg_append (p q : Word) (xs ys : List Word) :
    lseg p q (xs ++ ys) = sexists fun r => lseg p r xs ∗ lseg r q ys := by
  induction xs generalizing p with
  | nil =>
    funext h
    apply propext
    constructor
    · intro hp
      exact ⟨p, (spure_sep_apply _ _ _).mpr ⟨rfl, hp⟩⟩
    · rintro ⟨r, hr⟩
      obtain ⟨rfl, hr⟩ := (spure_sep_apply _ _ _).mp hr
      exact hr
  | cons x xs ih =>
    simp only [List.cons_append, lseg, ih, sep_sexists, sexists_sep, sep_assoc]
    funext h
    simp only [sexists]
    exact propext exists_comm

theorem lseg_snoc {p r q : Word} {xs : List Word} {y : Word} :
    (lseg p r xs ∗ ⌜r ≠ 0⌝ ∗ nodePt r y q) ⊢ₛ lseg p q (xs ++ [y]) := by
  rw [lseg_append]
  refine sexists_intro r (sep_mono_right _ ?_)
  intro h hh
  refine ⟨q, ?_⟩
  simp only [lseg, spure_true_emp, sep_emp]
  exact hh

theorem llist_null {xs : List Word} {h : Frag} (hp : llist 0 xs h) : xs = [] ∧ h = Frag.empty := by
  cases xs with
  | nil => exact ⟨rfl, hp.1⟩
  | cons x xs =>
    obtain ⟨n, hn⟩ := hp
    exact absurd rfl ((spure_sep_apply _ _ _).mp hn).1

theorem llist_nonnull {p : Word} (hp0 : p ≠ 0) {xs : List Word} {h : Frag} (hp : llist p xs h) :
    ∃ x xs' n, xs = x :: xs' ∧ (nodePt p x n ∗ llist n xs') h := by
  cases xs with
  | nil => exact absurd hp.2 hp0
  | cons x xs =>
    obtain ⟨n, hn⟩ := hp
    exact ⟨x, xs, n, rfl, ((spure_sep_apply _ _ _).mp hn).2⟩

theorem llist_cons_intro {p n x : Word} {xs : List Word} (hp0 : p ≠ 0) :
    (nodePt p x n ∗ llist n xs) ⊢ₛ llist (p) (x :: xs) := fun _ hh =>
  ⟨n, (spure_sep_apply _ _ _).mpr ⟨hp0, hh⟩⟩

theorem llist_nil (h : Frag) : llist 0 [] h ↔ h = Frag.empty :=
  ⟨fun hp => hp.1, fun e => ⟨e, rfl⟩⟩

/-! ## Reading words -/

theorem toNat_ofNat_of_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem wordPt_bound {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) : a + 8 ≤ 2 ^ 64 := by
  obtain ⟨f, -, hf, -, hlf, -⟩ := sep_le hp (memFrag_le d m)
  have := (bytesAt_le hf hlf 7 (by simp)).1
  simp [addressLimit] at this; omega

theorem leValue_encode (w : Word) :
    leValue (Silmaril.Machine.LittleEndian.encodeWords [w]) = w.toNat := by
  rw [← Silmaril.X86.Ext.leBytes_eight, Silmaril.X86.Ext.leValue_leBytes]
  exact Nat.mod_eq_of_lt w.isLt

/-- A load of an owned word. -/
theorem load_word {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState} {A : Word}
    (hA : A.toNat = a) (hp : (wordPt a w ∗ R) (memFrag d m.memory)) :
    loadN m.memory A 8 = some w := by
  obtain ⟨f, -, hf, -, hlf, -⟩ := sep_le hp (memFrag_le d m)
  have hr := readBytes_of_wordPt hf hlf
  simp only [loadN, hA, hr, Option.map_some, leValue_encode, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- Two encodings of words are equal only for equal words. -/
theorem encode_inj {v w : Word}
    (h : Silmaril.Machine.LittleEndian.encodeWords [v] =
      Silmaril.Machine.LittleEndian.encodeWords [w]) : v = w := by
  have := congrArg Silmaril.X86.wordOfBytes? h
  simp only [Silmaril.X86.wordOfBytes?_encodeWords, Option.some.injEq] at this
  exact this

/-! ## Uniqueness and the remaining-length measure -/

theorem word_unique {a : Nat} {v w : Word} {f g : Frag} {m : MState} (hf : wordPt a v f)
    (hg : wordPt a w g) (hlf : Le f (toFrag m)) (hlg : Le g (toFrag m)) : v = w := by
  have e1 := readBytes_of_wordPt hf hlf
  have e2 := readBytes_of_wordPt hg hlg
  rw [e1] at e2
  exact encode_inj (Option.some.inj e2)

theorem node_unique {p x y n n' : Word} {f g : Frag} {m : MState} (hf : nodePt p x n f)
    (hg : nodePt p y n' g) (hlf : Le f (toFrag m)) (hlg : Le g (toFrag m)) : x = y ∧ n = n' := by
  obtain ⟨f1, f2, _, rfl, h1, h2⟩ := hf
  obtain ⟨g1, g2, hdg, rfl, k1, k2⟩ := hg
  exact ⟨word_unique h1 k1 (le_union_left hlf) (le_union_left hlg),
    word_unique h2 k2 (le_union_right ‹_› hlf) (le_union_right hdg hlg)⟩

/-- **A list is determined by its head pointer and the memory.** -/
theorem llist_unique : ∀ {xs ys : List Word} {p : Word} {f g : Frag} {m : MState},
    llist p xs f → llist p ys g → Le f (toFrag m) → Le g (toFrag m) → xs = ys
  | [], ys, p, f, g, m, hf, hg, _, _ => by
    have hp : p = 0 := hf.2
    subst hp
    exact (llist_null hg).1.symm
  | x :: xs, ys, p, f, g, m, hf, hg, hlf, hlg => by
    obtain ⟨n, hn⟩ := hf
    obtain ⟨hp0, hn⟩ := (spure_sep_apply _ _ _).mp hn
    obtain ⟨y, ys', n', rfl, hg'⟩ := llist_nonnull hp0 hg
    obtain ⟨f1, f2, hdf, rfl, hf1, hf2⟩ := hn
    obtain ⟨g1, g2, hdg, rfl, hg1, hg2⟩ := hg'
    obtain ⟨rfl, rfl⟩ := node_unique hf1 hg1 (le_union_left hlf) (le_union_left hlg)
    rw [llist_unique hf2 hg2 (le_union_right hdf hlf) (le_union_right hdg hlg)]

theorem rem_eq {p : Word} {xs : List Word} {f : Frag} {m : MState} (hp : llist p xs f)
    (hl : Le f (toFrag m)) : rem m p = xs.length := by
  have hex : ∃ zs : List Word, ∃ f, llist p zs f ∧ Le f (toFrag m) := ⟨xs, f, hp, hl⟩
  unfold rem
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨g, hg, hlg⟩ := Classical.choose_spec hex
  rw [llist_unique hg hp hlg hl]

theorem le_toFrag_congr {f : Frag} (hf : MemOnly f) {m m' : MState}
    (h : m'.memory = m.memory) (hl : Le f (toFrag m)) : Le f (toFrag m') := by
  intro l v e
  obtain ⟨a, rfl⟩ := hf l (by simp [e])
  rw [← hl _ _ e]; simp [toFrag, h]

/-- `rem` depends on the memory only. -/
theorem rem_congr {m m' : MState} (h : m'.memory = m.memory) (p : Word) : rem m' p = rem m p := by
  by_cases hex : ∃ zs : List Word, ∃ f, llist p zs f ∧ Le f (toFrag m)
  · obtain ⟨zs, f, hf, hl⟩ := hex
    rw [rem_eq hf hl, rem_eq hf (le_toFrag_congr (memOnly_lseg _ _ _ _ hf) h hl)]
  · have hex' : ¬ ∃ zs : List Word, ∃ f, llist p zs f ∧ Le f (toFrag m') :=
      fun ⟨zs, f, hf, hl⟩ => hex ⟨zs, f, hf, le_toFrag_congr (memOnly_lseg _ _ _ _ hf) h.symm hl⟩
    simp only [rem, hex, hex', dite_false]

theorem rem_of_sep {P : SProp} {p : Word} {xs : List Word} {d : Frag} {m : MState}
    (h : (P ∗ llist p xs) (memFrag d m.memory)) : rem m p = xs.length := by
  obtain ⟨_, b, _, hb, _, hlb, -⟩ := sep_le h (memFrag_le d m)
  exact rem_eq hb hlb

theorem rem_mk_of_sep {P : SProp} {p : Word} {xs : List Word} {d : Frag} {mem : Memory}
    (h : (P ∗ llist p xs) (memFrag d mem)) (c : State) : rem ⟨c, mem⟩ p = xs.length :=
  rem_of_sep (m := ⟨c, mem⟩) h

theorem sep_llist_null {P : SProp} {zs : List Word} {f : Frag} (h : (P ∗ llist 0 zs) f) :
    zs = [] ∧ P f := by
  obtain ⟨a, b, -, rfl, ha, hb⟩ := h
  obtain ⟨rfl, rfl⟩ := llist_null hb
  refine ⟨rfl, ?_⟩
  have : union a Frag.empty = a := by
    funext l; unfold union; cases a l <;> rfl
  rw [this]; exact ha

/-- The bytes of an owned word are in the domain of the viewed fragment. -/
theorem memDom_of_wordPt {a : Nat} {w : Word} {R : SProp} {d : Frag} {mem : Memory}
    (hp : (wordPt a w ∗ R) (memFrag d mem)) {x : Nat} (h₁ : a ≤ x) (h₂ : x < a + 8) :
    memDom d x := by
  obtain ⟨f, g, -, he, hf, -⟩ := hp
  have hx := bytesAt_dom hf (x - a) (by simp; omega)
  rw [show a + (x - a) = x by omega] at hx
  have : (memFrag d mem (.mem x)).isSome := by rw [he]; exact isSome_union.mpr (.inl hx)
  rw [memFrag_isSome] at this
  exact this

/-! ## Writing words -/

theorem permitted_of_wordPt {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) : m.memory.Permitted .write a 8 := by
  obtain ⟨f, -, hf, -, hlf, -⟩ := sep_le hp (memFrag_le d m)
  exact permitted_of_blockAny (.inr rfl) (by decide) (wordPt_blockAny a w f hf) hlf

theorem storeN_eight {mem : Memory} {A : Word} {v : Word}
    (hp : mem.Permitted .write A.toNat 8) : storeN mem A 8 v = some (store8 mem A.toNat v) := by
  simp only [storeN, Memory.writeBytes, Silmaril.X86.Ext.length_leBytes]
  simp only [show mem.checkSpan .write A.toNat 8 = true from hp, ite_true]; rfl

theorem store8_writesWithin (mem : Memory) (a : Nat) (v : Word) :
    mem.WritesWithin (store8 mem a v) (fun x => a ≤ x ∧ x < a + 8) :=
  ⟨rfl, fun x hx => Memory.install_outside _ _ _ _ (by simp; omega)⟩

theorem permsAt_store8 (mem : Memory) (a : Nat) (v : Word) (x : Nat) :
    permsAt (store8 mem a v) x = permsAt mem x := rfl

/-- **Storing into an owned word**: the word changes and the rest of the assertion is
untouched. -/
theorem store_word {a : Nat} {w v : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) :
    (wordPt a v ∗ R) (memFrag d (store8 m.memory a v)) := by
  generalize hmem : m.memory = mem at hp
  obtain ⟨f1, f2, hd, he, h1, h2⟩ := hp
  -- the two pieces as subfragments of the old view
  have hl : Le (union f1 f2) (memFrag d mem) := by rw [he]; exact fun _ _ e => e
  have hl1 := le_union_left hl
  have hl2 := le_union_right hd hl
  -- the new view is the re-valuation of the old one
  let m' : MState := ⟨m.core, store8 mem a v⟩
  have hview : reval (memFrag d mem) (toFrag m') = memFrag d (store8 mem a v) := by
    funext l
    cases l with
    | mem x => simp only [reval, memFrag]; split <;> simp_all [toFrag, m']
    | _ => simp [reval, memFrag]
  have own : ∀ i < 8, (f1 (.mem (a + i))).isSome := fun i hi => bytesAt_dom h1 i (by simp; omega)
  rw [← hview]
  rw [he] at hview ⊢
  refine sep_reval (P := fun f => wordPt a w f ∧ f = f1) (Q := fun f => R f ∧ f = f2) _
    ⟨f1, f2, hd, rfl, ⟨h1, rfl⟩, ⟨h2, rfl⟩⟩ ?_ ?_
  · intro f hf; rw [hf.2]
    refine bytesAt_reval h1 (by simp) fun i hi => ⟨?_, ?_⟩
    · simp only [m', store8]
      rw [Memory.install_get _ _ _ i (by simpa using hi)]
      simp only [Silmaril.X86.Ext.leBytes_eight]
    · have hb := bytesAt_le h1 (le_trans hl1 (by rw [← hmem]; exact memFrag_le d m)) i (by simpa using hi)
      show RW (permsAt (store8 mem a v) (a + i))
      rw [permsAt_store8, ← hmem]; exact hb.2.2
  · intro f hf; rw [hf.2]
    suffices hs : reval f2 (toFrag m') = f2 by rw [hs]; exact h2
    funext l
    unfold reval
    cases e : f2 l with
    | none => simp
    | some val =>
      have hm := hl2 l val e
      cases l with
      | mem x =>
        have hx : ¬ (a ≤ x ∧ x < a + 8) := by
          rintro ⟨h₁, h₂⟩
          have := own (x - a) (by omega)
          rw [show a + (x - a) = x by omega] at this
          exact not_both hd this (by simp [e])
        simp only [Option.isSome_some, ite_true]
        rw [← hm]
        simp only [memFrag, toFrag, m']
        have hs : (memFrag d mem (.mem x)).isSome := by rw [hm]; rfl
        rw [memFrag_isSome] at hs
        simp only [hs, ite_true]
        rw [ (store8_writesWithin mem a v).2 x hx, permsAt_store8]
      | _ => simp [memFrag] at hm

/-! ## Satisfiability: list assertions from memory contents -/

/-- The fragment of `m` on the byte addresses `[a, a + n)`. -/
def cellsOf (m : MState) (a n : Nat) : Frag
  | .mem x => if a ≤ x ∧ x < a + n then toFrag m (.mem x) else none
  | _ => none

theorem cellsOf_le (m : MState) (a n : Nat) : Le (cellsOf m a n) (toFrag m) := by
  intro l v h
  cases l with
  | mem x => simp only [cellsOf] at h; split at h <;> simp_all
  | _ => simp [cellsOf] at h

theorem bytesPt_cellsOf {m : MState} : ∀ {a : Nat} {bs : List Byte},
    (∀ i (hi : i < bs.length), a + i < addressLimit ∧ RW (permsAt m.memory (a + i)) ∧
      m.memory.bytes.get? (a + i) = some bs[i]) → bytesPt a bs (cellsOf m a bs.length)
  | a, [], _ => by
    show cellsOf m a 0 = Frag.empty
    funext l; cases l <;> simp [cellsOf, Frag.empty]
  | a, b :: bs, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    refine ⟨Frag.single (.mem a) (.cell ⟨some b, permsAt m.memory a⟩), cellsOf m (a + 1) bs.length,
      ?_, ?_, ⟨h0.1, _, h0.2.1, rfl⟩,
      bytesPt_cellsOf fun i hi => by
        have := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show a + 1 + i = a + (i + 1) by omega]; exact this⟩
    · intro l
      cases l with
      | mem x =>
        by_cases e : x = a
        · subst e; right; simp [cellsOf]
        · left; simp [Frag.single, e]
      | _ => left; simp [Frag.single]
    · funext l
      cases l with
      | mem x =>
        simp only [cellsOf, union, Frag.single, List.length_cons]
        by_cases e : x = a
        · subst e; simp only [toFrag, ite_true]; simp; simpa using h0.2.2
        · simp only [Loc.mem.injEq, e, ite_false]
          by_cases hx : a + 1 ≤ x ∧ x < a + 1 + bs.length
          · simp only [hx, show a ≤ x ∧ x < a + (bs.length + 1) from by omega, and_self, ite_true]
          · simp only [hx, show ¬ (a ≤ x ∧ x < a + (bs.length + 1)) from by omega, ite_false]
      | _ => simp [cellsOf, union, Frag.single]

/-- **A one-node list holds** in every state whose memory has the node's sixteen bytes,
readable and writable. -/
theorem llist_single_holds {m : MState} {p v : Word} (hp0 : p ≠ 0)
    (hmem : ∀ i < 16, p.toNat + i < addressLimit ∧ RW (permsAt m.memory (p.toNat + i)) ∧
      m.memory.bytes.get? (p.toNat + i) = (Silmaril.Machine.LittleEndian.encodeWords [v, 0])[i]?) :
    Holds (llist p [v]) m := by
  have he : Silmaril.Machine.LittleEndian.encodeWords [v, 0] =
      Silmaril.Machine.LittleEndian.encodeWords [v] ++ Silmaril.Machine.LittleEndian.encodeWords [0] :=
    Silmaril.Machine.LittleEndian.encodeWords_append [v] [0]
  have hb := bytesPt_cellsOf (m := m) (a := p.toNat)
    (bs := Silmaril.Machine.LittleEndian.encodeWords [v, 0]) fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hmem i (by simpa using hi)
      exact ⟨h1, h2, by rw [h3, List.getElem?_eq_getElem hi]⟩
  have hn : nodePt p v 0 (cellsOf m p.toNat 16) := by
    have : (Silmaril.Machine.LittleEndian.encodeWords [v, 0]).length = 16 := by simp
    rw [this, he] at hb
    unfold bytesPt at hb
    rw [bytesAt_append] at hb
    simpa [nodePt, wordPt, bytesPt] using hb
  refine ⟨cellsOf m p.toNat 16, ⟨0, (spure_sep_apply _ _ _).mpr ⟨hp0, ?_⟩⟩, cellsOf_le m _ _⟩
  show (nodePt p v 0 ∗ ⌜(0 : Word) = 0⌝) _
  rw [show ((0 : Word) = 0) = True from eq_true rfl, spure_true_emp, sep_emp]
  exact hn

end Silmaril.Proofs.X86.Sep.List
