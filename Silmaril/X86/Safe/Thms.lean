module

public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Sep.Spec.Thms
import Silmaril.Proofs.X86.Safe.Basic

/-!
# Step-indexed safety and triples: theorems

For every segment-VC machine `I`:

* `SafeN`: `safeN_succ`, `safeN_mono`, `safeN_le`, `safeN_post`, `run_succ_some`,
  `safeN_of_run`, `safeN_of_reaches`, `safeN_prefix` (`k` steps add `k` to the index),
  `safeN_bind` (sequencing).
* `STriple`: `zero`, `mono`, `le`, `frame`, `conseq`, `of_triple` (a total triple is safe
  at every index), `triple_seq`, `seq_triple`, `progress_seq` (one step pays for the
  index), `sexists_pre`, `spure_pre`.
* `Progress`: `frame`, `conseq`; `rsp_of_sep`, `progress_of_rsp` (a total triple that moves
  `rsp` takes a step).
* **Extensions**: `SafeN.lift`, `STriple.lift`, `Progress.lift`: along `E : I.Extends J`,
  safety on `I` from the view is safety on `J`.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep

variable {σ τ : Type} {I : Isa σ} {Q Q₁ Q₂ : σ → Prop}

/-! ## `SafeN` -/

theorem safeN_succ {n : Nat} {m : σ} :
    SafeN I Q (n + 1) m ↔ Q m ∨ ∃ m', I.step m = some m' ∧ SafeN I Q n m' :=
  Iff.rfl

theorem safeN_mono {n : Nat} {m : σ} (h : SafeN I Q (n + 1) m) : SafeN I Q n m :=
  Silmaril.Proofs.X86.Safe.safeN_mono h

theorem safeN_le {k n : Nat} {m : σ} (hk : k ≤ n) (h : SafeN I Q n m) : SafeN I Q k m :=
  Silmaril.Proofs.X86.Safe.safeN_le hk h

theorem safeN_post (hq : ∀ m, Q₁ m → Q₂ m) {n : Nat} {m : σ} (h : SafeN I Q₁ n m) :
    SafeN I Q₂ n m :=
  Silmaril.Proofs.X86.Safe.safeN_post hq h

theorem run_succ_some {k : Nat} {m m' : σ} (h : run I.step (k + 1) m = some m') :
    ∃ m₁, I.step m = some m₁ ∧ run I.step k m₁ = some m' :=
  Silmaril.Proofs.X86.Safe.run_succ_some h

/-- A run that reaches `Q` is safe at every index. -/
theorem safeN_of_run {k : Nat} {m m' : σ} (h : run I.step k m = some m') (hq : Q m')
    (n : Nat) : SafeN I Q n m :=
  Silmaril.Proofs.X86.Safe.safeN_of_run h hq n

theorem safeN_of_reaches {m m' : σ} (h : Reaches I.step m m') (hq : Q m') (n : Nat) :
    SafeN I Q n m :=
  Silmaril.Proofs.X86.Safe.safeN_of_reaches h hq n

/-- `k` steps of a run add `k` to the index. -/
theorem safeN_prefix {k n : Nat} {m m' : σ} (h : run I.step k m = some m')
    (hs : SafeN I Q n m') : SafeN I Q (n + k) m :=
  Silmaril.Proofs.X86.Safe.safeN_prefix h hs

/-- **Sequencing**: run to `Q₁`, then from every `Q₁` state on. -/
theorem safeN_bind {n : Nat} {m : σ} (h : SafeN I Q₁ n m)
    (hk : ∀ m', Q₁ m' → SafeN I Q₂ n m') : SafeN I Q₂ n m :=
  Silmaril.Proofs.X86.Safe.safeN_bind h hk

/-- **Safety moves up a machine extension.** -/
theorem SafeN.lift {J : Isa τ} (E : I.Extends J) {n : Nat} {x : τ}
    (h : SafeN I Q n (E.view x)) : SafeN J (fun y => Q (E.view y)) n x :=
  Silmaril.Proofs.X86.Safe.safeN_lift E h

/-! ## `STriple` -/

variable {n : Nat} {P P' Q' R : SProp}

theorem STriple.zero (P Q : SProp) : STriple I 0 P Q := fun _ _ _ _ => trivial

theorem STriple.mono {P Q : SProp} (h : STriple I (n + 1) P Q) : STriple I n P Q :=
  fun F m hl hm => safeN_mono (h F m hl hm)

theorem STriple.le {k : Nat} {P Q : SProp} (hk : k ≤ n) (h : STriple I n P Q) :
    STriple I k P Q :=
  fun F m hl hm => safeN_le hk (h F m hl hm)

/-- **The frame rule.** -/
theorem STriple.frame {P Q : SProp} (h : STriple I n P Q) (R : SProp) :
    STriple I n (P ∗ R) (Q ∗ R) :=
  Silmaril.Proofs.X86.Safe.striple_frame h R

/-- **Consequence.** -/
theorem STriple.conseq {P Q : SProp} (hp : P' ⊢ₛ P) (h : STriple I n P Q) (hq : Q ⊢ₛ Q') :
    STriple I n P' Q' :=
  Silmaril.Proofs.X86.Safe.striple_conseq hp h hq

/-- A total triple is safe at every index. -/
theorem STriple.of_triple {P Q : SProp} (h : Triple I P Q) : STriple I n P Q :=
  Silmaril.Proofs.X86.Safe.striple_of_triple h

/-- A total triple, then a step-indexed one. -/
theorem STriple.triple_seq {P Q : SProp} (h₁ : Triple I P R) (h₂ : STriple I n R Q) :
    STriple I n P Q :=
  Silmaril.Proofs.X86.Safe.striple_triple_seq h₁ h₂

/-- A step-indexed triple, then a total one. -/
theorem STriple.seq_triple {P Q : SProp} (h₁ : STriple I n P R) (h₂ : Triple I R Q) :
    STriple I n P Q :=
  Silmaril.Proofs.X86.Safe.striple_seq_triple h₁ h₂

/-- **One step pays for the index**: a total triple that takes a step, then a triple at `n`,
is a triple at `n + 1`. -/
theorem STriple.progress_seq {P Q : SProp} (h₁ : Progress I P R) (h₂ : STriple I n R Q) :
    STriple I (n + 1) P Q :=
  Silmaril.Proofs.X86.Safe.striple_progress_seq h₁ h₂

theorem STriple.sexists_pre {α : Sort _} {P : α → SProp} {Q : SProp}
    (h : ∀ x, STriple I n (P x) Q) : STriple I n (sexists P) Q :=
  Silmaril.Proofs.X86.Safe.striple_sexists_pre h

theorem STriple.spure_pre {φ : Prop} {P Q : SProp} (h : φ → STriple I n P Q) :
    STriple I n (⌜φ⌝ ∗ P) Q :=
  Silmaril.Proofs.X86.Safe.striple_spure_pre h

/-- **A step-indexed triple of `I` is one of every machine extending `I`.** -/
theorem STriple.lift {J : Isa τ} (E : I.Extends J) {P Q : SProp} (h : STriple I n P Q) :
    STriple J n P Q :=
  Silmaril.Proofs.X86.Safe.striple_lift E h

/-! ## `Progress` -/

theorem Progress.frame {P R : SProp} (h : Progress I P R) (F : SProp) :
    Progress I (P ∗ F) (R ∗ F) :=
  Silmaril.Proofs.X86.Safe.progress_frame h F

theorem Progress.conseq {P P' R R' : SProp} (hp : P' ⊢ₛ P) (h : Progress I P R)
    (hr : R ⊢ₛ R') : Progress I P' R' :=
  Silmaril.Proofs.X86.Safe.progress_conseq hp h hr

theorem Progress.lift {J : Isa τ} (E : I.Extends J) {P R : SProp} (h : Progress I P R) :
    Progress J P R :=
  Silmaril.Proofs.X86.Safe.progress_lift E h

/-- The value of `rsp` in a state whose fragment starts with `rsp ↦ s`. -/
theorem rsp_of_sep {s : Word} {P F : SProp} {m : σ}
    (h : ((regPt .rsp s ∗ P) ∗ F) (frag I m)) : (I.core m).read .rsp = s :=
  Silmaril.Proofs.X86.Safe.rsp_of_sep h

/-- A total triple that moves `rsp` takes a step. -/
theorem progress_of_rsp {s s' : Word} {P Q : SProp} (hne : s ≠ s')
    (h : Triple I (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q)) :
    Progress I (regPt .rsp s ∗ P) (regPt .rsp s' ∗ Q) :=
  Silmaril.Proofs.X86.Safe.progress_of_rsp hne h

end Silmaril.X86.Safe
