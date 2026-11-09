module

public import Silmaril.X86.Safe.Exc.Defs
public import Silmaril.X86.Safe.Thms
public import Silmaril.X86.Sep.Extra.Thms
public import Silmaril.X86.Sep.SysV.Thms
import Silmaril.Proofs.X86.Safe.Exc

/-!
# Two-exit triples: theorems

For every segment-VC machine `I`:

* `safeN_now`, `safeN_live`; `Exc.mono`, `Exc.frame`, `exc_of_at`.
* Index: `STripleX.zero`, `STripleX.le`, `STripleX.mono`.
* Entry: `STriple.toX` (an ordinary triple is a two-exit triple for every `k`, `E`),
  `STripleX.toSTriple` (no payload: an ordinary triple), `STripleX.throw`.
* Structure: `STripleX.conseq`/`pre`/`post`, `STripleX.frameF` (a frame leaked on the
  exceptional exit), `STripleX.frameG` (a frame kept, as payload), `STripleX.seq`,
  `STripleX.progress_seq`, `STripleX.triple_seq`, `STripleX.seq_triple`,
  `STripleX.sexists_pre`, `STripleX.spure_pre`.
* `STripleX.lift`: along `E : I.Extends J`, a two-exit triple of `I` is one of `J`.
* **`xcall_rule`** (`Ex : Open.isa.Extends I`): a `call rel32` to a callee with a two-exit
  triple.
* **`catch_rule`**: `STripleX I n P Q k E` and, for every `v ≠ 0`,
  `STriple I n (AtCont k v ∗ E v) Q'` give `STriple I n P (sor Q (Q' ∗ strue))`.
* **`stable_iff_strue`**: `(strue ∗ F) (toFrag m) ↔ Holds F m`.

`setjmp`/`longjmp` themselves and the `jmp_buf` assertion are in `Sep/JmpBuf`.

Not proved: a rule for a protected region that the continuation re-enters in a loop (a
`setjmp` inside a loop whose body `longjmp`s back to it). `catch_rule` uses one `safeN_bind`
at the same index, which covers code that leaves the protected region once.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (MState Word Insn)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

variable {σ τ : Type} {I : Isa σ} {n : Nat} {k : Cont} {E E' : Word → SProp}
  {P P' Q Q' R : SProp}

/-- A state that meets the target is safe at every index. -/
theorem safeN_now {Q : σ → Prop} {m : σ} (h : Q m) (n : Nat) : SafeN I Q n m :=
  Silmaril.Proofs.X86.SafeExc.safeN_now h n

/-- Every state a `SafeN` run reaches from a live state is live. -/
theorem safeN_live {Q : σ → Prop} {m : σ} (hl : I.live m) (h : SafeN I Q n m) :
    SafeN I (fun t => I.live t ∧ Q t) n m :=
  Silmaril.Proofs.X86.SafeExc.safeN_live hl h

/-! ## `Exc` -/

theorem Exc.mono (he : ∀ v, E v ⊢ₛ E' v) (G : SProp) : Exc k E G ⊢ₛ Exc k E' G :=
  Silmaril.Proofs.X86.SafeExc.Exc.mono he G

/-- The exceptional exit with the survivor frame `R ∗ G` is the one with payload `E v ∗ R`
and survivor frame `G`. -/
theorem Exc.frame (R G : SProp) : Exc k E (R ∗ G) = Exc k (fun v => E v ∗ R) G := by
  simp only [Exc, sep_assoc]

/-- An exceptional state from a state at the continuation: the rest is garbage. -/
theorem exc_of_at (F G : SProp) :
    ((sexists fun v => ⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v) ∗ F ∗ G) ⊢ₛ Exc k E G :=
  Silmaril.Proofs.X86.SafeExc.exc_of_at F G

/-! ## Index -/

theorem STripleX.zero (P Q : SProp) (k : Cont) (E : Word → SProp) : STripleX I 0 P Q k E :=
  fun _ _ _ _ _ => trivial

theorem STripleX.le {k' : Nat} (hk : k' ≤ n) (h : STripleX I n P Q k E) :
    STripleX I k' P Q k E :=
  fun F G m hl hm => safeN_le hk (h F G m hl hm)

theorem STripleX.mono (h : STripleX I (n + 1) P Q k E) : STripleX I n P Q k E :=
  STripleX.le (Nat.le_succ n) h

/-! ## Entry -/

/-- **An ordinary triple is a two-exit triple** for every continuation and payload. -/
theorem STriple.toX (h : STriple I n P Q) (k : Cont) (E : Word → SProp) :
    STripleX I n P Q k E :=
  fun F G m hl hm => safeN_post (fun _ h' => .inl h') (h (F ∗ G) m hl hm)

/-- **No payload, no exceptional exit**: a two-exit triple with `E = fun _ => False` is an
ordinary triple. -/
theorem STripleX.toSTriple (h : STripleX I n P Q k (fun _ => fun _ => False)) :
    STriple I n P Q :=
  Silmaril.Proofs.X86.SafeExc.STripleX.toSTriple h

/-- **Throw**: a precondition at the continuation exits exceptionally at once. -/
theorem STripleX.throw (h : P ⊢ₛ sexists fun v => ⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v) (Q : SProp) :
    STripleX I n P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.throw h Q

/-! ## Structural rules -/

theorem STripleX.conseq (hp : P' ⊢ₛ P) (h : STripleX I n P Q k E) (hq : Q ⊢ₛ Q')
    (he : ∀ v, E v ⊢ₛ E' v) : STripleX I n P' Q' k E' :=
  Silmaril.Proofs.X86.SafeExc.STripleX.conseq hp h hq he

theorem STripleX.pre (hp : P' ⊢ₛ P) (h : STripleX I n P Q k E) : STripleX I n P' Q k E :=
  STripleX.conseq hp h (entails_refl _) (fun _ => entails_refl _)

theorem STripleX.post (h : STripleX I n P Q k E) (hq : Q ⊢ₛ Q') : STripleX I n P Q' k E :=
  STripleX.conseq (entails_refl _) h hq (fun _ => entails_refl _)

/-- **A frame kept on the normal exit and leaked on the exceptional one.** -/
theorem STripleX.frameF (h : STripleX I n P Q k E) (R : SProp) :
    STripleX I n (P ∗ R) (Q ∗ R) k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.frameF h R

/-- **A frame that survives both exits**; on the exceptional one it joins the payload. -/
theorem STripleX.frameG (h : STripleX I n P Q k E) (R : SProp) :
    STripleX I n (P ∗ R) (Q ∗ R) k (fun v => E v ∗ R) :=
  Silmaril.Proofs.X86.SafeExc.STripleX.frameG h R

/-- **Sequencing**: the exceptional exit of the first part is final. -/
theorem STripleX.seq (h₁ : STripleX I n P R k E) (h₂ : STripleX I n R Q k E) :
    STripleX I n P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.seq h₁ h₂

/-- A step pays for the index. -/
theorem STripleX.progress_seq (h₁ : Progress I P R) (h₂ : STripleX I n R Q k E) :
    STripleX I (n + 1) P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.progress_seq h₁ h₂

/-- A total triple, then a two-exit one. -/
theorem STripleX.triple_seq (h₁ : Triple I P R) (h₂ : STripleX I n R Q k E) :
    STripleX I n P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.triple_seq h₁ h₂

/-- A two-exit triple, then a total one on the normal exit. -/
theorem STripleX.seq_triple (h₁ : STripleX I n P R k E) (h₂ : Triple I R Q) :
    STripleX I n P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.seq_triple h₁ h₂

theorem STripleX.sexists_pre {α : Sort _} {P : α → SProp}
    (h : ∀ x, STripleX I n (P x) Q k E) : STripleX I n (sexists P) Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.sexists_pre h

theorem STripleX.spure_pre {φ : Prop} (h : φ → STripleX I n P Q k E) :
    STripleX I n (⌜φ⌝ ∗ P) Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.spure_pre h

/-- **A two-exit triple of `I` is one of every machine extending `I`.** -/
theorem STripleX.lift {J : Isa τ} (Ex : I.Extends J) (h : STripleX I n P Q k E) :
    STripleX J n P Q k E :=
  Silmaril.Proofs.X86.SafeExc.STripleX.lift Ex h

/-! ## Calls -/

/-- **`xcall_rule`**: a `call rel32` at `pc` to `f`, whose callee meets a two-exit triple
when entered with the return address `pc + 5` pushed below `s`, is a two-exit triple of the
call site with the same continuation. The call instruction's code survives the exceptional
exit, as part of the payload. -/
theorem xcall_rule (Ex : Open.isa.Extends I) {pc s f : Word} {rel : BitVec 32}
    (hs : 8 ≤ s.toNat) (hf : pc + 5#64 + rel.signExtend 64 = f)
    (hS : STripleX I n (ripPt f ∗ regPt .rsp (s - 8#64) ∗ wordPt (s.toNat - 8) (pc + 5#64) ∗ P)
      Q k E) :
    STripleX I n
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ ripPt pc ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8 ∗ P)
      (codePt pc.toNat (Insn.encode (.call rel)) ∗ Q) k
      (fun v => E v ∗ codePt pc.toNat (Insn.encode (.call rel))) :=
  Silmaril.Proofs.X86.SafeExc.xcall_rule Ex hs hf hS

/-! ## Catch -/

/-- **`catch_rule`**: seal the exceptional exit. If the protected code meets a two-exit triple
for the continuation `k`, and from every exceptional state (`v ≠ 0`) the handler meets an
ordinary triple, the whole is an ordinary triple: it returns normally, or through the
handler with the abandoned frames as garbage. Both parts use the same index. -/
theorem catch_rule (h₁ : STripleX I n P Q k E)
    (h₂ : ∀ v, v ≠ 0 → STriple I n (AtCont k v ∗ E v) Q') :
    STriple I n P (sor Q (Q' ∗ strue)) :=
  Silmaril.Proofs.X86.SafeExc.catch_rule h₁ h₂

/-! ## `strue` and stability -/

/-- **`stable_iff_strue`**: `strue ∗ F` holds of the whole state exactly when `F` holds of
part of it. -/
theorem stable_iff_strue (F : SProp) (m : MState) : (strue ∗ F) (toFrag m) ↔ Holds F m :=
  Silmaril.Proofs.X86.SafeExc.stable_iff_strue F m

end Silmaril.X86.Safe
