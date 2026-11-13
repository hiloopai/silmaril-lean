module

public import Silmaril.Proofs.X86.Sep.Xmm.Algebra
public import Silmaril.X86.Safe.Open9.Thms
public import Silmaril.X86.Sse9.Thms
/-!
# Proofs: lifting `SProp`s, `XSafeN`/`XSTriple`, and the bridge from `Open9` triples

Behind `Silmaril/Machine/X86/Sep/Xmm/Thms.lean`.

* `lift` is a homomorphism: `lift_sep`, `lift_emp`, `lift_spure`, `lift_sexists`, `lift_mono`.
* `XSafeN`: `xsafeN_succ`, `xsafeN_post`, `xsafeN_of_post`, `xsafeN_of_step`, `xsafeN_of_run`,
  `xsafeN_of_reaches`.
* `XSTriple`: `zero`, `mono`, `frame`, `conseq`.
* `ExtendsOpen9X`: `run_of_open9X`, `reaches_of_open9X`, `xsafeN_of_safeN`,
  `xsafeN_of_total`/`reaches_of_total` (a total `FnContract` on `Open9.isa`), and
  **`xstriple_of_striple`**: an `Open9` triple is a triple of every XMM machine that extends
  `Open9`, for the lifted assertions, with an arbitrary XMM-level frame. The XMM part of the
  frame is pinned to the XMM file of the start state, which an `Open9` run does not change.
* `instExtendsOpen9XSse9 : ExtendsOpen9X Sse9.isa`, from `Sse9.extendsOpen9` (`ExtendsOpen9X.of_extends`).
-/

@[expose] public section

namespace Silmaril.X86.Sep.Xmm

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sse9 (XState XFile)
open Silmaril.X86.Sep
open Silmaril.X86.Safe (SafeN STriple)

/-! ## `lift` -/

theorem lift_sep (P Q : SProp) : lift (P ∗ Q) = (lift P ∗ₓ lift Q) := by
  funext h
  apply propext
  constructor
  · rintro ⟨⟨a, b, hd, he, ha, hb⟩, h2⟩
    refine ⟨(a, PMap.empty), (b, PMap.empty), ⟨hd, PMap.disjoint_empty_left _⟩, ?_,
      ⟨ha, rfl⟩, ⟨hb, rfl⟩⟩
    exact Prod.ext (he.trans (frag_union a b)) (h2.trans (PMap.empty_union _).symm)
  · rintro ⟨a, b, hd, rfl, ⟨ha, ha2⟩, ⟨hb, hb2⟩⟩
    refine ⟨⟨a.1, b.1, hd.1, (frag_union a.1 b.1).symm, ha, hb⟩, ?_⟩
    show PMap.union a.2 b.2 = PMap.empty
    rw [ha2, hb2, PMap.empty_union]

theorem lift_emp : lift emp = xemp := by
  funext h
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact Prod.ext (h1.trans frag_empty) h2
  · rintro rfl
    exact ⟨frag_empty.symm, rfl⟩

theorem lift_spure (φ : Prop) : lift ⌜φ⌝ = ⌜φ⌝ₓ := by
  funext h
  apply propext
  constructor
  · rintro ⟨⟨h1, hφ⟩, h2⟩
    exact ⟨Prod.ext (h1.trans frag_empty) h2, hφ⟩
  · rintro ⟨rfl, hφ⟩
    exact ⟨⟨frag_empty.symm, hφ⟩, rfl⟩

theorem lift_sexists {α : Sort _} (P : α → SProp) :
    lift (sexists P) = xsexists fun a => lift (P a) := by
  funext h
  apply propext
  constructor
  · rintro ⟨⟨a, ha⟩, h2⟩
    exact ⟨a, ha, h2⟩
  · rintro ⟨a, ha, h2⟩
    exact ⟨⟨a, ha⟩, h2⟩

theorem lift_mono {P Q : SProp} (h : P ⊢ₛ Q) : lift P ⊢ₓ lift Q :=
  fun _ ⟨hp, h2⟩ => ⟨h _ hp, h2⟩

/-! ## `XSafeN` -/

section XSafe

variable {M : Silmaril.X86.SegVC.Isa XState} {Q Q₁ Q₂ : XState → Prop}

theorem xsafeN_succ {n : Nat} {x : XState} :
    XSafeN M Q (n + 1) x ↔ Q x ∨ ∃ x', M.step x = some x' ∧ XSafeN M Q n x' := Iff.rfl

theorem xsafeN_post (hq : ∀ x, Q₁ x → Q₂ x) :
    ∀ {n : Nat} {x : XState}, XSafeN M Q₁ n x → XSafeN M Q₂ n x
  | 0, _, _ => trivial
  | n + 1, x, h => by
    rcases xsafeN_succ.mp h with h | ⟨x', hs, h⟩
    · exact xsafeN_succ.mpr (.inl (hq x h))
    · exact xsafeN_succ.mpr (.inr ⟨x', hs, xsafeN_post hq h⟩)

theorem xsafeN_mono : ∀ {n : Nat} {x : XState}, XSafeN M Q (n + 1) x → XSafeN M Q n x
  | 0, _, _ => trivial
  | n + 1, x, h => by
    rcases xsafeN_succ.mp h with h | ⟨x', hs, h⟩
    · exact xsafeN_succ.mpr (.inl h)
    · exact xsafeN_succ.mpr (.inr ⟨x', hs, xsafeN_mono h⟩)

theorem xsafeN_le {k n : Nat} {x : XState} (hk : k ≤ n) (h : XSafeN M Q n x) :
    XSafeN M Q k x := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih (xsafeN_mono h)

/-- A state satisfying the postcondition is safe at every index. -/
theorem xsafeN_of_post {x : XState} (hq : Q x) : ∀ n, XSafeN M Q n x
  | 0 => trivial
  | _ + 1 => .inl hq

/-- One step to a state satisfying the postcondition. -/
theorem xsafeN_of_step {x x' : XState} (hs : M.step x = some x') (hq : Q x') :
    ∀ n, XSafeN M Q n x
  | 0 => trivial
  | n + 1 => .inr ⟨x', hs, xsafeN_of_post hq n⟩

theorem xsafeN_of_run : ∀ {k : Nat} {x x' : XState}, run M.step k x = some x' →
    Q x' → ∀ n, XSafeN M Q n x
  | 0, x, x', h, hq, n => by
    simp only [run, Option.some.injEq] at h
    subst h
    exact xsafeN_of_post hq n
  | k + 1, x, x', h, hq, n => by
    simp only [run] at h
    cases hs : M.step x with
    | none => rw [hs] at h; cases h
    | some x₁ =>
      rw [hs] at h
      cases n with
      | zero => trivial
      | succ n => exact .inr ⟨x₁, hs, xsafeN_of_run h hq n⟩

theorem xsafeN_of_reaches {x x' : XState} (h : Reaches M.step x x') (hq : Q x') (n : Nat) :
    XSafeN M Q n x :=
  let ⟨_, hk⟩ := h; xsafeN_of_run hk hq n

end XSafe

/-! ## `XSTriple` -/

section XTriple

variable {M : Silmaril.X86.SegVC.Isa XState} {n : Nat}

theorem XSTriple.zero (P Q : XSProp) : XSTriple M 0 P Q := fun _ _ _ => trivial

theorem XSTriple.mono {P Q : XSProp} (h : XSTriple M (n + 1) P Q) : XSTriple M n P Q :=
  fun F x hx => xsafeN_mono (h F x hx)

theorem XSTriple.le {k : Nat} {P Q : XSProp} (hk : k ≤ n) (h : XSTriple M n P Q) :
    XSTriple M k P Q :=
  fun F x hx => xsafeN_le hk (h F x hx)

theorem XSTriple.frame {P Q : XSProp} (h : XSTriple M n P Q) (R : XSProp) :
    XSTriple M n (P ∗ₓ R) (Q ∗ₓ R) := by
  intro F x hx
  rw [xsep_assoc] at hx
  exact xsafeN_post (fun y hy => by rwa [xsep_assoc]) (h (R ∗ₓ F) x hx)

theorem XSTriple.conseq {P P' Q Q' : XSProp} (hp : P' ⊢ₓ P) (h : XSTriple M n P Q)
    (hq : Q ⊢ₓ Q') : XSTriple M n P' Q' :=
  fun F x hx => xsafeN_post (fun _ hy => xsep_mono hq (xentails_refl F) _ hy)
    (h F x (xsep_mono hp (xentails_refl F) _ hx))

theorem XSTriple.xsexists_pre {α : Sort _} {P : α → XSProp} {Q : XSProp}
    (h : ∀ a, XSTriple M n (P a) Q) : XSTriple M n (xsexists P) Q := by
  intro F x hx
  rw [xsexists_sep] at hx
  obtain ⟨a, ha⟩ := hx
  exact h a F x ha

end XTriple

/-! ## Machines that extend `Open9` -/

section Extends

variable {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M]

theorem run_of_open9X (xs : XFile) : ∀ (k : Nat) {a b : MState},
    run Silmaril.X86.Open9.step k a = some b → run M.step k ⟨a, xs⟩ = some ⟨b, xs⟩
  | 0, a, b, h => by simp only [run, Option.some.injEq] at h ⊢; rw [h]
  | k + 1, a, b, h => by
    simp only [run] at h ⊢
    cases hs : Silmaril.X86.Open9.step a with
    | none => rw [hs] at h; cases h
    | some a' =>
      rw [hs] at h
      simp only [Option.bind_some] at h
      rw [ExtendsOpen9X.ext (M := M) (x := ⟨a, xs⟩) hs]
      exact run_of_open9X xs k h

theorem reaches_of_open9X (xs : XFile) {a b : MState}
    (h : Reaches Silmaril.X86.Open9.step a b) : Reaches M.step ⟨a, xs⟩ ⟨b, xs⟩ :=
  let ⟨k, hk⟩ := h; ⟨k, run_of_open9X xs k hk⟩

/-- **`Open9` safety is safety of the XMM machine**, with the XMM file unchanged. -/
theorem xsafeN_of_safeN {Q : MState → Prop} (xs : XFile) :
    ∀ {n : Nat} {m : MState}, SafeN Silmaril.X86.Open9.isa Q n m →
      XSafeN M (fun y => Q y.m ∧ y.xmm = xs) n ⟨m, xs⟩
  | 0, _, _ => trivial
  | n + 1, m, h => by
    rcases h with h | ⟨m', hs, h⟩
    · exact .inl ⟨h, rfl⟩
    · exact .inr ⟨⟨m', xs⟩, ExtendsOpen9X.ext (x := ⟨m, xs⟩) hs, xsafeN_of_safeN xs h⟩

/-- **The bridge**: every `Open9` triple is a triple of every XMM machine that extends
`Open9`, between the lifted assertions, against an arbitrary XMM-level frame. -/
theorem xstriple_of_striple {n : Nat} {P Q : SProp}
    (h : STriple Silmaril.X86.Open9.isa n P Q) : XSTriple M n (lift P) (lift Q) := by
  intro F x hx
  obtain ⟨a, b, hd, he, ⟨ha, ha2⟩, hb⟩ := hx
  have hb2 : b.2 = XMap.all x.xmm := by
    have e := congrArg Prod.snd he
    simp only [toXFrag, XFrag.union, ha2, PMap.empty_union] at e
    exact e.symm
  let F' : SProp := fun g => F (g, XMap.all x.xmm)
  have hpre : (P ∗ F') (toFrag x.m) := by
    refine ⟨a.1, b.1, hd.1, (congrArg Prod.fst he).trans (frag_union a.1 b.1).symm, ha, ?_⟩
    show F (b.1, XMap.all x.xmm)
    rw [← hb2]
    exact hb
  refine xsafeN_post ?_ (xsafeN_of_safeN (M := M) x.xmm (h F' x.m trivial hpre))
  rintro y ⟨⟨c, d, hcd, hce, hc, hd'⟩, hy⟩
  refine ⟨(c, PMap.empty), (d, XMap.all x.xmm), ⟨hcd, PMap.disjoint_empty_left _⟩, ?_,
    ⟨hc, rfl⟩, hd'⟩
  refine Prod.ext (hce.trans (frag_union c d)) ?_
  show XMap.all y.xmm = PMap.union PMap.empty (XMap.all x.xmm)
  rw [PMap.empty_union, hy]

/-- Track A's total `Open` triples reach every XMM machine that extends `Open9`. -/
theorem xstriple_of_triple {n : Nat} {P Q : SProp} (h : Triple Silmaril.X86.Open.isa P Q) :
    XSTriple M n (lift P) (lift Q) :=
  xstriple_of_striple
    (Silmaril.X86.Safe.STriple.lift Silmaril.X86.Open9.extendsOpen (Silmaril.X86.Safe.STriple.of_triple h))

/-- **A total `Open9` contract is safe on the XMM machine** at every index, from every entry
state, with the XMM file unchanged. -/
theorem xsafeN_of_total {S : Silmaril.X86.FnContract.Spec MState}
    (h : S.Total Silmaril.X86.Open9.isa) (x : XState)
    (habi : Silmaril.X86.FnContract.AbiEntry x.m.core x.m.memory) (he : S.entry x.m)
    (n : Nat) :
    XSafeN M (fun y => S.Result Silmaril.X86.Open9.isa x.m y.m ∧ y.xmm = x.xmm) n x := by
  obtain ⟨t, hr, res⟩ := h x.m trivial habi he
  exact xsafeN_of_reaches (reaches_of_open9X (M := M) x.xmm hr) ⟨res, rfl⟩ n

/-- The same as a run: a total `Open9` contract reaches its result on the XMM machine. -/
theorem reaches_of_total {S : Silmaril.X86.FnContract.Spec MState}
    (h : S.Total Silmaril.X86.Open9.isa) (x : XState)
    (habi : Silmaril.X86.FnContract.AbiEntry x.m.core x.m.memory) (he : S.entry x.m) :
    ∃ y, Reaches M.step x y ∧ y.xmm = x.xmm ∧ S.Result Silmaril.X86.Open9.isa x.m y.m := by
  obtain ⟨t, hr, res⟩ := h x.m trivial habi he
  exact ⟨⟨t, x.xmm⟩, reaches_of_open9X (M := M) x.xmm hr, rfl, res⟩

end Extends

/-- **`Sse9` extends `Open9`.** -/
instance instExtendsOpen9XSse9 : ExtendsOpen9X Silmaril.X86.Sse9.isa :=
  ExtendsOpen9X.of_extends Silmaril.X86.Sse9.extendsOpen9 (fun _ => rfl) (fun _ _ => rfl)

end Silmaril.X86.Sep.Xmm
