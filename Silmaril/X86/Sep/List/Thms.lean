module

public import Silmaril.X86.Sep.List.Defs
public import Silmaril.X86.Sep.SysV.Thms
import Silmaril.Proofs.X86.Sep.List.Basic
import Silmaril.Proofs.X86.Sep.List.Sat

/-!
# Linked lists: laws, memory reading and writing, and the System V bridge

**Segment laws** (pure separation logic, no machine):

* `lseg_nil`, `lseg_cons` (unfolding), `llist_nil`, `llist_null` (a null list is empty and
  owns nothing), `llist_nonnull` (a non-null list is a node and a list), `llist_cons_intro`;
* `lseg_append`: `lseg p q (xs ++ ys) = ∃ r, lseg p r xs ∗ lseg r q ys` (both directions);
  `lseg_snoc`: a segment extended by one node at its end;
* `llist_unique`: a list is determined by its head pointer and the memory (so `rem m p`,
  the length of the list at `p`, is a termination measure for pointer-chasing loops);
* `memOnly_lseg`: list assertions own memory locations only.

The frame rule is the generic `Triple.frame`/`SPEC.frame` of `Sep/Spec` and the frame built
into `FnSpec.Sat`; nothing list-specific is needed for it.

**Memory** (a list invariant `P (memFrag d mem)` of a loop over the entry fragment `d`):
`memFrag_le`, `reval_eq_memFrag`, `memFrag_of_le`; `load_word` (a load of an owned word),
`wordPt_bound`; `permitted_of_wordPt`, `storeN_eight`, `store8_writesWithin` and **`store_word`**
(a store into an owned word changes that word and nothing else of the assertion).

**The System V bridge** `FnSpec.sat_of_family`: a spec from state-level contracts that may
depend on the call's logical arguments and on the fragment the caller hands over.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.Ext (loadN storeN)
open Silmaril.Process (Memory)
open Frag (union Disjoint Le reval)

/-! ## Fragment helpers

A few facts of the fragment PCM, exported here so that clients need not import a `Proofs`
module (track A, known problem 5). -/

theorem Frag.isSome_union {a b : Frag} {l : Loc} :
    (union a b l).isSome ↔ (a l).isSome ∨ (b l).isSome :=
  Silmaril.Proofs.X86.Sep.List.isSome_union

theorem Frag.le_of_union_left {a b s : Frag} (h : Le (union a b) s) : Le a s :=
  Silmaril.Proofs.X86.Sep.List.le_union_left h

theorem Frag.le_of_union_right {a b s : Frag} (hd : Disjoint a b) (h : Le (union a b) s) :
    Le b s :=
  Silmaril.Proofs.X86.Sep.List.le_union_right hd h

theorem Frag.Disjoint.not_both {a b : Frag} (h : Disjoint a b) {l : Loc} (ha : (a l).isSome)
    (hb : (b l).isSome) : False :=
  Silmaril.Proofs.X86.Sep.List.not_both h ha hb

theorem Frag.dom_left {P Q : SProp} {h : Frag} (hpq : (P ∗ Q) h) {l : Loc}
    (k : ∀ a, P a → (a l).isSome) : (h l).isSome := by
  obtain ⟨a, b, _, rfl, ha, _⟩ := hpq
  exact Frag.isSome_union.mpr (.inl (k a ha))

theorem Frag.dom_right {P Q : SProp} {h : Frag} (hpq : (P ∗ Q) h) {l : Loc}
    (k : ∀ b, Q b → (b l).isSome) : (h l).isSome := by
  obtain ⟨a, b, _, rfl, _, hb⟩ := hpq
  exact Frag.isSome_union.mpr (.inr (k b hb))

/-! ## Segment laws -/

theorem lseg_nil (p q : Word) : lseg p q [] = ⌜p = q⌝ := rfl

theorem lseg_cons (p q x : Word) (xs : List Word) :
    lseg p q (x :: xs) = sexists fun n : Word => ⌜p ≠ 0⌝ ∗ nodePt p x n ∗ lseg n q xs := rfl

theorem lseg_append (p q : Word) (xs ys : List Word) :
    lseg p q (xs ++ ys) = sexists fun r => lseg p r xs ∗ lseg r q ys :=
  Silmaril.Proofs.X86.Sep.List.lseg_append p q xs ys

theorem lseg_snoc {p r q : Word} {xs : List Word} {y : Word} :
    (lseg p r xs ∗ ⌜r ≠ 0⌝ ∗ nodePt r y q) ⊢ₛ lseg p q (xs ++ [y]) :=
  Silmaril.Proofs.X86.Sep.List.lseg_snoc

theorem llist_nil (h : Frag) : llist 0 [] h ↔ h = Frag.empty :=
  Silmaril.Proofs.X86.Sep.List.llist_nil h

theorem llist_null {xs : List Word} {h : Frag} (hp : llist 0 xs h) : xs = [] ∧ h = Frag.empty :=
  Silmaril.Proofs.X86.Sep.List.llist_null hp

theorem llist_nonnull {p : Word} (hp0 : p ≠ 0) {xs : List Word} {h : Frag} (hp : llist p xs h) :
    ∃ x xs' n, xs = x :: xs' ∧ (nodePt p x n ∗ llist n xs') h :=
  Silmaril.Proofs.X86.Sep.List.llist_nonnull hp0 hp

theorem llist_cons_intro {p n x : Word} {xs : List Word} (hp0 : p ≠ 0) :
    (nodePt p x n ∗ llist n xs) ⊢ₛ llist p (x :: xs) :=
  Silmaril.Proofs.X86.Sep.List.llist_cons_intro hp0

theorem memOnly_lseg {xs : List Word} {p q : Word} {f : Frag} (h : lseg p q xs f) : MemOnly f :=
  Silmaril.Proofs.X86.Sep.List.memOnly_lseg xs p q f h

theorem llist_unique {xs ys : List Word} {p : Word} {f g : Frag} {m : MState}
    (hf : llist p xs f) (hg : llist p ys g) (hlf : Le f (toFrag m)) (hlg : Le g (toFrag m)) :
    xs = ys :=
  Silmaril.Proofs.X86.Sep.List.llist_unique hf hg hlf hlg

theorem rem_eq {p : Word} {xs : List Word} {f : Frag} {m : MState} (hp : llist p xs f)
    (hl : Le f (toFrag m)) : rem m p = xs.length :=
  Silmaril.Proofs.X86.Sep.List.rem_eq hp hl

theorem rem_of_sep {P : SProp} {p : Word} {xs : List Word} {d : Frag} {m : MState}
    (h : (P ∗ llist p xs) (memFrag d m.memory)) : rem m p = xs.length :=
  Silmaril.Proofs.X86.Sep.List.rem_of_sep h

/-- `rem` depends on the memory only. -/
theorem rem_congr {m m' : MState} (h : m'.memory = m.memory) (p : Word) : rem m' p = rem m p :=
  Silmaril.Proofs.X86.Sep.List.rem_congr h p

theorem rem_mk_of_sep {P : SProp} {p : Word} {xs : List Word} {d : Frag} {mem : Memory}
    (h : (P ∗ llist p xs) (memFrag d mem)) (c : Silmaril.X86.State) :
    rem ⟨c, mem⟩ p = xs.length :=
  Silmaril.Proofs.X86.Sep.List.rem_mk_of_sep h c

/-- A null list at the end of a separating conjunction is empty and owns nothing. -/
theorem sep_llist_null {P : SProp} {zs : List Word} {f : Frag} (h : (P ∗ llist 0 zs) f) :
    zs = [] ∧ P f :=
  Silmaril.Proofs.X86.Sep.List.sep_llist_null h

/-! ## Memory views -/

theorem memFrag_le (d : Frag) (m : MState) : Le (memFrag d m.memory) (toFrag m) :=
  Silmaril.Proofs.X86.Sep.List.memFrag_le d m

theorem reval_eq_memFrag {d : Frag} (hd : MemOnly d) (m : MState) :
    reval d (toFrag m) = memFrag d m.memory :=
  Silmaril.Proofs.X86.Sep.List.reval_eq_memFrag hd m

theorem memFrag_of_le {d : Frag} (hd : MemOnly d) {m : MState} (hl : Le d (toFrag m)) :
    memFrag d m.memory = d :=
  Silmaril.Proofs.X86.Sep.List.memFrag_of_le hd hl

theorem memFrag_isSome {d : Frag} {mem : Memory} {a : Nat} :
    (memFrag d mem (.mem a)).isSome = (d (.mem a)).isSome :=
  Silmaril.Proofs.X86.Sep.List.memFrag_isSome

/-- **A load of an owned word.** -/
theorem load_word {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState} {A : Word}
    (hA : A.toNat = a) (hp : (wordPt a w ∗ R) (memFrag d m.memory)) :
    loadN m.memory A 8 = some w :=
  Silmaril.Proofs.X86.Sep.List.load_word hA hp

theorem wordPt_bound {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) : a + 8 ≤ 2 ^ 64 :=
  Silmaril.Proofs.X86.Sep.List.wordPt_bound hp

theorem memDom_of_wordPt {a : Nat} {w : Word} {R : SProp} {d : Frag} {mem : Memory}
    (hp : (wordPt a w ∗ R) (memFrag d mem)) {x : Nat} (h₁ : a ≤ x) (h₂ : x < a + 8) :
    memDom d x :=
  Silmaril.Proofs.X86.Sep.List.memDom_of_wordPt hp h₁ h₂

theorem permitted_of_wordPt {a : Nat} {w : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) : m.memory.Permitted .write a 8 :=
  Silmaril.Proofs.X86.Sep.List.permitted_of_wordPt hp

theorem storeN_eight {mem : Memory} {A : Word} {v : Word}
    (hp : mem.Permitted .write A.toNat 8) : storeN mem A 8 v = some (store8 mem A.toNat v) :=
  Silmaril.Proofs.X86.Sep.List.storeN_eight hp

theorem store8_writesWithin (mem : Memory) (a : Nat) (v : Word) :
    mem.WritesWithin (store8 mem a v) (fun x => a ≤ x ∧ x < a + 8) :=
  Silmaril.Proofs.X86.Sep.List.store8_writesWithin mem a v

/-- **A store into an owned word** changes that word and leaves the rest of the assertion. -/
theorem store_word {a : Nat} {w v : Word} {R : SProp} {d : Frag} {m : MState}
    (hp : (wordPt a w ∗ R) (memFrag d m.memory)) :
    (wordPt a v ∗ R) (memFrag d (store8 m.memory a v)) :=
  Silmaril.Proofs.X86.Sep.List.store_word hp

/-! ## Satisfiability -/

/-- **Non-vacuity of the list precondition**: a one-node list holds in every state whose
memory has the node's sixteen bytes (`val = v`, `next = NULL`), readable and writable. -/
theorem llist_single_holds {m : MState} {p v : Word} (hp0 : p ≠ 0)
    (hmem : ∀ i < 16, p.toNat + i < Silmaril.Process.addressLimit ∧
      RW (permsAt m.memory (p.toNat + i)) ∧
      m.memory.bytes.get? (p.toNat + i) = (Silmaril.Machine.LittleEndian.encodeWords [v, 0])[i]?) :
    Holds (llist p [v]) m :=
  Silmaril.Proofs.X86.Sep.List.llist_single_holds hp0 hmem

/-! ## The System V bridge -/

/-- **A System V spec from a family of state-level contracts**, one per call: the contract
may depend on the logical arguments and the precondition's fragment `hu`; its footprint is
inside `hu`, and its postcondition gives the spec's on `hu` re-read in the final memory. -/
theorem FnSpec.sat_of_family {S : FnSpec} {C : SProp} {entry : Word}
    (hmo : ∀ x f, S.pre x f → MemOnly f)
    (h : ∀ x sp ret (m : MState) (hc ht hu : Frag), FnSpec.EntryAligned sp →
      S.stack ≤ sp.toNat → C hc → S.SysVEntry x entry sp ret ht → S.pre x hu →
      Disjoint hc (union ht hu) → Disjoint ht hu → Le (union hc (union ht hu)) (toFrag m) →
      ∃ K : Silmaril.X86.FnContract.Spec MState, K.Total Silmaril.X86.Open.isa ∧
        K.entry m ∧ (∀ a, K.footprint m a → memDom hu a) ∧
        ∀ fin, K.post m fin → S.post x (fin.core.read .rax) (memFrag hu fin.memory)) :
    S.Sat Silmaril.X86.Open.isa C entry :=
  Silmaril.Proofs.X86.Sep.List.sat_of_family hmo h

end Silmaril.X86.Sep
