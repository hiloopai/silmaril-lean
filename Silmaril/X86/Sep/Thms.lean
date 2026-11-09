module

public import Silmaril.X86.Sep.Defs
import Silmaril.Proofs.X86.Sep.Algebra

/-!
# Separation-logic laws and the bridge from atoms to the machine

* **Algebra.** `sep` is associative and commutative with unit `emp` (`sep_assoc`,
  `sep_comm`, `emp_sep`, `sep_emp`), registered as `Std.Associative`, `Std.Commutative` and
  `Std.LawfulIdentity` instances so that `ac_rfl` and `ac_nf` rearrange `∗`-chains. Monotonicity
  (`sep_mono`), existentials (`sexists_sep`, `sexists_intro`, `sexists_elim`), pure facts
  (`spure_sep_apply`, `spure_sep_intro`, `spure_sep_elim`) and the wand adjunction
  (`wand_intro`, `wand_elim`). The pure/sep/wand fragment is a boolean BI; no BI instance is
  given.
* **Splitting.** `bytesAt_append` (`bytesPt_split`), `blockAny_add` (`blockAny_split`),
  `bytesPt_blockAny`.
* **Reading the machine.** For a fragment contained in `toFrag m`: register, `rip`, flag and
  mapping values (`regPt_le`, …), and `Memory.readBytes`/`fetchBytes`/`Permitted` from byte
  atoms (`readBytes_of_bytesPt`, `fetchBytes_of_codePt`, `readBytes_of_wordPt`,
  `permitted_of_blockAny`).
* **Domains and re-valuation** (used to build triples from runs): the locations an atom owns
  (`bytesAt_dom`, `regPt_dom`, `ripPt_dom`, `flagsAny_dom`, …), re-valuation distributing over
  disjoint unions (`Frag.reval_union`, `Frag.reval_disjoint`), and an atom re-valued in a later
  state (`sep_reval`, `regPt_reval`, `ripPt_reval`, `flagsAny_reval`, `bytesAt_reval`,
  `blockAny_reval`, …).
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.Process (Memory Region Permissions Access addressLimit)
open Frag (union Disjoint Le reval)

/-! ## Algebra -/

theorem sep_comm (P Q : SProp) : (P ∗ Q) = (Q ∗ P) := Silmaril.Proofs.X86.Sep.sep_comm P Q
theorem sep_assoc (P Q R : SProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) :=
  Silmaril.Proofs.X86.Sep.sep_assoc P Q R
theorem emp_sep (P : SProp) : (emp ∗ P) = P := Silmaril.Proofs.X86.Sep.emp_sep P
theorem sep_emp (P : SProp) : (P ∗ emp) = P := Silmaril.Proofs.X86.Sep.sep_emp P

/-- Rearrangement of `∗`-chains by `ac_rfl`/`ac_nf`. -/
instance : Std.Associative sep := ⟨sep_assoc⟩
instance : Std.Commutative sep := ⟨sep_comm⟩
instance : Std.LawfulIdentity sep emp where
  left_id := emp_sep
  right_id := sep_emp

theorem sep_left_comm (P Q R : SProp) : (P ∗ Q ∗ R) = (Q ∗ P ∗ R) := by
  rw [← sep_assoc, sep_comm P Q, sep_assoc]

theorem entails_refl (P : SProp) : P ⊢ₛ P := fun _ h => h
theorem entails_trans {P Q R : SProp} (h₁ : P ⊢ₛ Q) (h₂ : Q ⊢ₛ R) : P ⊢ₛ R :=
  fun h hp => h₂ h (h₁ h hp)
theorem entails_of_eq {P Q : SProp} (e : P = Q) : P ⊢ₛ Q := by subst e; exact entails_refl P

theorem sep_mono {P P' Q Q' : SProp} (hp : P ⊢ₛ P') (hq : Q ⊢ₛ Q') : (P ∗ Q) ⊢ₛ (P' ∗ Q') :=
  Silmaril.Proofs.X86.Sep.sep_mono hp hq
theorem sep_mono_left {P P' : SProp} (Q : SProp) (hp : P ⊢ₛ P') : (P ∗ Q) ⊢ₛ (P' ∗ Q) :=
  sep_mono hp (entails_refl Q)
theorem sep_mono_right (P : SProp) {Q Q' : SProp} (hq : Q ⊢ₛ Q') : (P ∗ Q) ⊢ₛ (P ∗ Q') :=
  sep_mono (entails_refl P) hq

theorem sexists_sep {α : Sort _} (P : α → SProp) (Q : SProp) :
    (sexists P ∗ Q) = sexists (fun x => P x ∗ Q) :=
  Silmaril.Proofs.X86.Sep.sexists_sep P Q
theorem sep_sexists {α : Sort _} (P : SProp) (Q : α → SProp) :
    (P ∗ sexists Q) = sexists (fun x => P ∗ Q x) :=
  Silmaril.Proofs.X86.Sep.sep_sexists P Q
theorem sexists_intro {α : Sort _} {P : SProp} {Q : α → SProp} (x : α) (h : P ⊢ₛ Q x) :
    P ⊢ₛ sexists Q := fun f hp => ⟨x, h f hp⟩
theorem sexists_elim {α : Sort _} {P : α → SProp} {Q : SProp} (h : ∀ x, P x ⊢ₛ Q) :
    sexists P ⊢ₛ Q := fun f ⟨x, hx⟩ => h x f hx

theorem spure_sep_apply (φ : Prop) (P : SProp) (h : Frag) : (⌜φ⌝ ∗ P) h ↔ φ ∧ P h :=
  Silmaril.Proofs.X86.Sep.spure_sep_apply φ P h
theorem spure_sep_intro {φ : Prop} {P Q : SProp} (hφ : φ) (h : P ⊢ₛ Q) : P ⊢ₛ (⌜φ⌝ ∗ Q) :=
  Silmaril.Proofs.X86.Sep.spure_sep_intro hφ h
theorem spure_sep_elim {φ : Prop} {P Q : SProp} (h : φ → P ⊢ₛ Q) : (⌜φ⌝ ∗ P) ⊢ₛ Q :=
  Silmaril.Proofs.X86.Sep.spure_sep_elim h
theorem spure_true_emp : ⌜True⌝ = emp := Silmaril.Proofs.X86.Sep.spure_true_emp

theorem wand_intro {P Q R : SProp} (h : (P ∗ Q) ⊢ₛ R) : P ⊢ₛ (Q -∗ R) :=
  Silmaril.Proofs.X86.Sep.wand_intro h
theorem wand_elim {P Q R : SProp} (h : P ⊢ₛ (Q -∗ R)) : (P ∗ Q) ⊢ₛ R :=
  Silmaril.Proofs.X86.Sep.wand_elim h

/-! ## Splitting and weakening -/

/-- `bytesPt_split` and its permission variants. -/
theorem bytesAt_append {need : Permissions → Prop} (a : Nat) (xs ys : List Byte) :
    bytesAt need a (xs ++ ys) = (bytesAt need a xs ∗ bytesAt need (a + xs.length) ys) :=
  Silmaril.Proofs.X86.Sep.bytesAt_append a xs ys

/-- `blockAny_split`. -/
theorem blockAny_add (a m n : Nat) : blockAny a (m + n) = (blockAny a m ∗ blockAny (a + m) n) :=
  Silmaril.Proofs.X86.Sep.blockAny_add a m n

theorem bytesAt_mono {need need' : Permissions → Prop} (hn : ∀ p, need p → need' p) (a : Nat)
    (bs : List Byte) : bytesAt need a bs ⊢ₛ bytesAt need' a bs :=
  Silmaril.Proofs.X86.Sep.bytesAt_mono hn a bs

theorem bytesPt_blockAny (a : Nat) (bs : List Byte) : bytesPt a bs ⊢ₛ blockAny a bs.length :=
  Silmaril.Proofs.X86.Sep.bytesPt_blockAny a bs

theorem wordPt_blockAny (a : Nat) (w : Word) : wordPt a w ⊢ₛ blockAny a 8 := by
  have := bytesPt_blockAny a (Silmaril.Machine.LittleEndian.encodeWords [w])
  simp only [Silmaril.X86.length_encodeWords_singleton] at this
  exact this

/-! ## Reading the machine -/

theorem holds_sep {P Q : SProp} {m : MState} (h : Holds (P ∗ Q) m) : Holds P m ∧ Holds Q m :=
  Silmaril.Proofs.X86.Sep.holds_sep h

theorem holds_mono {P Q : SProp} {m : MState} (h : P ⊢ₛ Q) (hp : Holds P m) : Holds Q m :=
  Silmaril.Proofs.X86.Sep.holds_mono h hp

theorem toFrag_isSome (m : MState) (l : Loc) : (toFrag m l).isSome :=
  Silmaril.Proofs.X86.Sep.toFrag_isSome m l

theorem sep_le {P Q : SProp} {h s : Frag} (hpq : (P ∗ Q) h) (hl : Le h s) :
    ∃ a b, P a ∧ Q b ∧ Le a s ∧ Le b s ∧ Disjoint a b ∧ h = union a b :=
  Silmaril.Proofs.X86.Sep.sep_le hpq hl

theorem regPt_le {r : Reg} {v : Word} {h : Frag} {m : MState} (hp : regPt r v h)
    (hl : Le h (toFrag m)) : m.core.read r = v := Silmaril.Proofs.X86.Sep.regPt_le hp hl
theorem ripPt_le {v : Word} {h : Frag} {m : MState} (hp : ripPt v h) (hl : Le h (toFrag m)) :
    m.core.rip = v := Silmaril.Proofs.X86.Sep.ripPt_le hp hl
theorem flagsPt_le {f : Flags} {h : Frag} {m : MState} (hp : flagsPt f h)
    (hl : Le h (toFrag m)) : m.core.flags = f := Silmaril.Proofs.X86.Sep.flagsPt_le hp hl
theorem regionsPt_le {rs : List Region} {h : Frag} {m : MState} (hp : regionsPt rs h)
    (hl : Le h (toFrag m)) : m.memory.regions = rs := Silmaril.Proofs.X86.Sep.regionsPt_le hp hl

theorem bytesAt_le {need : Permissions → Prop} {a : Nat} {bs : List Byte} {h : Frag}
    {m : MState} (hp : bytesAt need a bs h) (hl : Le h (toFrag m)) (i : Nat)
    (hi : i < bs.length) : a + i < addressLimit ∧
      m.memory.bytes.get? (a + i) = some bs[i] ∧ need (permsAt m.memory (a + i)) :=
  Silmaril.Proofs.X86.Sep.bytesAt_le hp hl i hi

theorem blockAny_le {a n : Nat} {h : Frag} {m : MState} (hp : blockAny a n h)
    (hl : Le h (toFrag m)) (i : Nat) (hi : i < n) :
    a + i < addressLimit ∧ RW (permsAt m.memory (a + i)) :=
  Silmaril.Proofs.X86.Sep.blockAny_le hp hl i hi

theorem readBytes_of_bytesPt {a : Nat} {bs : List Byte} {h : Frag} {m : MState} (hne : bs ≠ [])
    (hp : bytesPt a bs h) (hl : Le h (toFrag m)) : m.memory.readBytes a bs.length = some bs :=
  Silmaril.Proofs.X86.Sep.readBytes_of_bytesPt hne hp hl

theorem readBytes_of_bytesPtRO {a : Nat} {bs : List Byte} {h : Frag} {m : MState}
    (hne : bs ≠ []) (hp : bytesPtRO a bs h) (hl : Le h (toFrag m)) :
    m.memory.readBytes a bs.length = some bs :=
  Silmaril.Proofs.X86.Sep.readBytes_of_bytesPtRO hne hp hl

theorem fetchBytes_of_codePt {a : Nat} {bs : List Byte} {h : Frag} {m : MState} (hne : bs ≠ [])
    (hp : codePt a bs h) (hl : Le h (toFrag m)) : m.memory.fetchBytes a bs.length = some bs :=
  Silmaril.Proofs.X86.Sep.fetchBytes_of_codePt hne hp hl

theorem readBytes_of_wordPt {a : Nat} {w : Word} {h : Frag} {m : MState} (hp : wordPt a w h)
    (hl : Le h (toFrag m)) :
    m.memory.readBytes a 8 = some (Silmaril.Machine.LittleEndian.encodeWords [w]) :=
  Silmaril.Proofs.X86.Sep.readBytes_of_wordPt hp hl

theorem permitted_of_blockAny {access : Access} (hacc : access = .read ∨ access = .write)
    {a n : Nat} {h : Frag} {m : MState} (hn : 0 < n) (hp : blockAny a n h)
    (hl : Le h (toFrag m)) : m.memory.Permitted access a n :=
  Silmaril.Proofs.X86.Sep.permitted_of_blockAny hacc hn hp hl

/-! ## Domains and re-valuation -/

theorem bytesAt_dom {need : Permissions → Prop} {a : Nat} {bs : List Byte} {h : Frag}
    (hp : bytesAt need a bs h) (i : Nat) (hi : i < bs.length) : (h (.mem (a + i))).isSome :=
  Silmaril.Proofs.X86.Sep.bytesAt_dom hp i hi

theorem blockAny_dom {a n : Nat} {h : Frag} (hp : blockAny a n h) (i : Nat) (hi : i < n) :
    (h (.mem (a + i))).isSome :=
  Silmaril.Proofs.X86.Sep.blockAny_dom hp i hi

theorem regPt_dom {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) : (h (.reg r)).isSome :=
  Silmaril.Proofs.X86.Sep.regPt_dom hp
theorem ripPt_dom {v : Word} {h : Frag} (hp : ripPt v h) : (h .rip).isSome :=
  Silmaril.Proofs.X86.Sep.ripPt_dom hp
theorem flagsAny_dom {h : Frag} (hp : flagsAny h) : (h .flags).isSome :=
  Silmaril.Proofs.X86.Sep.flagsAny_dom hp

theorem Frag.reval_union (a b s : Frag) : reval (union a b) s = union (reval a s) (reval b s) :=
  Silmaril.Proofs.X86.Sep.Frag.reval_union a b s
theorem Frag.reval_disjoint {a b : Frag} (h : Disjoint a b) (s : Frag) :
    Disjoint (reval a s) (reval b s) :=
  Silmaril.Proofs.X86.Sep.Frag.reval_disjoint h s

theorem sep_reval {P Q P' Q' : SProp} {h : Frag} (s : Frag) (hpq : (P ∗ Q) h)
    (hp : ∀ a, P a → P' (reval a s)) (hq : ∀ b, Q b → Q' (reval b s)) :
    (P' ∗ Q') (reval h s) :=
  Silmaril.Proofs.X86.Sep.sep_reval s hpq hp hq

theorem regPt_reval {r : Reg} {v : Word} {h : Frag} (m : MState) (hp : regPt r v h) :
    regPt r (m.core.read r) (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.regPt_reval m hp

theorem ripPt_reval {v : Word} {h : Frag} (m : MState) (hp : ripPt v h) :
    ripPt m.core.rip (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.ripPt_reval m hp

theorem flagsAny_reval {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsAny (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.flagsAny_reval m hp

theorem bytesAt_reval {need need' : Permissions → Prop} {a : Nat} {bs bs' : List Byte}
    {h : Frag} {m : MState} (hp : bytesAt need a bs h) (hlen : bs'.length = bs.length)
    (hv : ∀ i (hi : i < bs'.length), m.memory.bytes.get? (a + i) = some bs'[i] ∧
      need' (permsAt m.memory (a + i))) :
    bytesAt need' a bs' (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.bytesAt_reval hp hlen hv

theorem blockAny_reval {a n : Nat} {h : Frag} {m : MState} (hp : blockAny a n h)
    (hv : ∀ i < n, RW (permsAt m.memory (a + i))) : blockAny a n (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.blockAny_reval hp hv

end Silmaril.X86.Sep
