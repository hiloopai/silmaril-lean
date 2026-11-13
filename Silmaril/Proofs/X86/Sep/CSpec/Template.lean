module

public import Silmaril.X86.Sep.CSpec.Defs
public import Silmaril.X86.Sep.Xmm.Thms
public import Silmaril.X86.Sep.Thms
public import Silmaril.X86.Safe.Thms
/-!
# Proofs: sequencing on XMM machines, the template, and refinement of `CSpec`s

Behind `Silmaril/Machine/X86/Sep/CSpec/Thms.lean`. Imports only headers.

* `XSafeN`/`XSTriple` sequencing: `xsafeN_bind`, `xsafeN_prefix`, `XSTriple.seq`,
  `XSTriple.progress_seq` (one step pays for the index);
* `XProgress`: `frame`, `conseq`, and `xprogress_of_progress` (an `Open9` progress law is one
  of every XMM machine extending `Open9`);
* words as bytes: `wordBytes_inj`, `chunksPt_gp8` (a one-word GP chunk is a register atom);
* the template: `ctlIn_split`, `ctlOut_split` (a larger budget is a smaller one and a block);
* `SatN`: `zero`, `mono`, `code_frame`, `sub` (refinement); `Sub.refl`, `Sub.trans`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.SepCSpec

open Silmaril.X86 (Reg XReg Word Byte MState)
open Silmaril.Machine.Execution (run)
open Silmaril.X86.Sse9 (Xmm XState)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Xmm
open Silmaril.X86.Sep.Plan
open Silmaril.X86.Sep.CSpec
open Silmaril.X86.Safe (Progress)

/-! ## Sequencing on XMM machines -/

section Seq

variable {M : Silmaril.X86.SegVC.Isa XState} {Q R : XState → Prop}

theorem xsafeN_bind : ∀ {n : Nat} {x : XState}, XSafeN M Q n x →
    (∀ y, Q y → XSafeN M R n y) → XSafeN M R n x
  | 0, _, _, _ => trivial
  | n + 1, x, h, hk => by
    rcases h with h | ⟨x', hs, h⟩
    · exact hk x h
    · exact .inr ⟨x', hs, xsafeN_bind h fun y hy => xsafeN_mono (hk y hy)⟩

theorem xsafeN_prefix {n : Nat} : ∀ {k : Nat} {x x' : XState}, run M.step k x = some x' →
    XSafeN M Q n x' → XSafeN M Q (n + k) x
  | 0, x, x', h, hq => by
    simp only [run, Option.some.injEq] at h
    subst h
    exact hq
  | k + 1, x, x', h, hq => by
    simp only [run] at h
    cases hs : M.step x with
    | none => rw [hs] at h; cases h
    | some x₁ =>
      rw [hs] at h
      exact .inr ⟨x₁, hs, xsafeN_prefix h hq⟩

variable {n : Nat}

theorem XSTriple.seq {P Q R : XSProp} (h₁ : XSTriple M n P Q) (h₂ : XSTriple M n Q R) :
    XSTriple M n P R :=
  fun F x hx => xsafeN_bind (h₁ F x hx) fun y hy => h₂ F y hy

theorem XSTriple.progress_seq {P R Q : XSProp} (h₁ : XProgress M P R)
    (h₂ : XSTriple M n R Q) : XSTriple M (n + 1) P Q := by
  intro F x hx
  obtain ⟨k, x', hk, hr⟩ := h₁ F x hx
  exact xsafeN_le (by omega) (xsafeN_prefix hk (h₂ F x' hr))

theorem XProgress.frame {P R : XSProp} (h : XProgress M P R) (G : XSProp) :
    XProgress M (P ∗ₓ G) (R ∗ₓ G) := by
  intro F x hx
  rw [xsep_assoc] at hx
  obtain ⟨k, x', hk, hr⟩ := h (G ∗ₓ F) x hx
  exact ⟨k, x', hk, by rwa [xsep_assoc]⟩

theorem XProgress.conseq {P P' R R' : XSProp} (hp : P' ⊢ₓ P) (h : XProgress M P R)
    (hr : R ⊢ₓ R') : XProgress M P' R' := by
  intro F x hx
  obtain ⟨k, x', hk, h'⟩ := h F x (xsep_mono hp (xentails_refl F) _ hx)
  exact ⟨k, x', hk, xsep_mono hr (xentails_refl F) _ h'⟩

theorem XSTriple.pure_pre {φ : Prop} {P Q : XSProp} (h : φ → XSTriple M n P Q) :
    XSTriple M n (⌜φ⌝ₓ ∗ₓ P) Q := by
  intro F x hx
  rw [xsep_assoc, xspure_sep_apply] at hx
  exact h hx.1 F x hx.2

end Seq

/-- **An `Open9` progress law is one of every XMM machine extending `Open9`** (lifted
assertions, arbitrary XMM-level frame). -/
theorem xprogress_of_progress {M : Silmaril.X86.SegVC.Isa XState} [ExtendsOpen9X M]
    {P R : SProp} (h : Progress Silmaril.X86.Open9.isa P R) :
    XProgress M (lift P) (lift R) := by
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
  obtain ⟨k, m', hk, c, d, hcd, hce, hc, hd'⟩ := h F' x.m trivial hpre
  refine ⟨k, ⟨m', x.xmm⟩, run_of_open9X (M := M) x.xmm (k + 1) hk,
    (c, PMap.empty), (d, XMap.all x.xmm), ⟨hcd, PMap.disjoint_empty_left _⟩, ?_, ⟨hc, rfl⟩, hd'⟩
  refine Prod.ext (hce.trans (frag_union c d)) ?_
  show XMap.all x.xmm = PMap.union PMap.empty (XMap.all x.xmm)
  rw [PMap.empty_union]

/-! ## Words as bytes -/

theorem wordBytes_inj {v w : Word} (h : wordBytes v = wordBytes w) : v = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < 8 := by omega
  have e := congrArg (fun l => l[i / 8]?) h
  simp only [wordBytes, byteSlice, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.some.injEq, Nat.zero_add] at e
  have e2 := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) e
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true,
    Bool.true_and] at e2
  rwa [show 8 * (i / 8) + i % 8 = i by omega] at e2

theorem slice_wordBytes (w : Word) : slice (wordBytes w) 0 8 = wordBytes w := by
  simp [slice, wordBytes, byteSlice]

theorem wordBytes_length (w : Word) : (wordBytes w).length = 8 := by
  simp [wordBytes, byteSlice]

/-- **A one-word GP chunk is a register atom.** -/
theorem chunksPt_gp8 (r : Reg) (w : Word) :
    chunksPt (wordBytes w) [⟨0, 8, .gp r⟩] = ↑ₓ(regPt r w) := by
  funext h
  apply propext
  constructor
  · rintro ⟨g, v, rfl, hc⟩
    obtain ⟨-, -, he⟩ := hc _ (List.mem_singleton_self _)
    have hg : g r = w := wordBytes_inj (he.trans (slice_wordBytes w))
    refine ⟨?_, ?_⟩
    · show regsFrag (gpRegs [⟨0, 8, .gp r⟩]) g = Frag.single (.reg r) (.word w)
      funext l
      cases l with
      | reg r' =>
        by_cases e : r' = r
        · subst e; simp [regsFrag, gpRegs, Frag.single, hg]
        · simp [regsFrag, gpRegs, Frag.single, e]
      | _ => simp [regsFrag, Frag.single]
    · funext r'
      simp [xmmsMap, xRegs, PMap.empty]
  · rintro ⟨h1, h2⟩
    refine ⟨fun _ => w, fun _ => 0, Prod.ext ?_ ?_, ?_⟩
    · rw [h1]
      funext l
      cases l <;> simp [regsFrag, gpRegs, Frag.single]
    · rw [h2]
      funext r'
      simp [xmmsMap, xRegs, PMap.empty]
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      refine ⟨by simp [modelled], by simp [wordBytes_length], ?_⟩
      exact (slice_wordBytes w).symm

/-! ## Assertion helpers -/

theorem xentails_of_eq {P Q : XSProp} (e : P = Q) : P ⊢ₓ Q := by subst e; exact xentails_refl P

theorem xsep_xsexists {α : Sort _} (P : XSProp) (Q : α → XSProp) :
    (P ∗ₓ xsexists Q) = xsexists fun a => P ∗ₓ Q a := by
  rw [xsep_comm, xsexists_sep]
  congr 1
  funext a
  exact xsep_comm _ _

theorem xsexists_mono {α : Sort _} {P Q : α → XSProp} (h : ∀ a, P a ⊢ₓ Q a) :
    xsexists P ⊢ₓ xsexists Q := fun g ⟨a, ha⟩ => ⟨a, h a g ha⟩

theorem xsexists_intro {α : Sort _} {P : XSProp} {Q : α → XSProp} (a : α) (h : P ⊢ₓ Q a) :
    P ⊢ₓ xsexists Q := fun g hp => ⟨a, h g hp⟩

theorem xsexists_elim {α : Sort _} {P : α → XSProp} {Q : XSProp} (h : ∀ a, P a ⊢ₓ Q) :
    xsexists P ⊢ₓ Q := fun g ⟨a, ha⟩ => h a g ha

/-! ## The template -/

theorem toNat_sub_eight {s : Word} (hs : 8 ≤ s.toNat) : (s - 8#64).toNat = s.toNat - 8 := by
  bv_omega

theorem blockAny_split {a t u k : Nat} (htu : t ≤ u) (hu : u ≤ a) :
    blockAny (a - u) (u + k) = (blockAny (a - u) (u - t) ∗ blockAny (a - t) (t + k)) := by
  rw [show u + k = (u - t) + (t + k) by omega, blockAny_add,
    show a - u + (u - t) = a - t by omega]

theorem ctlIn_split {t u : Nat} {entry : Word} {fr : Frame} (htu : t ≤ u)
    (hu : u ≤ fr.sp.toNat) :
    CtlIn u entry fr = (CtlIn t entry fr ∗ blockAny (fr.sp.toNat - u) (u - t)) := by
  have := blockAny_split (k := 0) htu hu
  simp only [Nat.add_zero] at this
  simp only [CtlIn, this]
  ac_rfl

theorem ctlOut_split {t u : Nat} {fr : Frame} (htu : t ≤ u) (hu : u ≤ fr.sp.toNat) :
    CtlOut u fr = (CtlOut t fr ∗ blockAny (fr.sp.toNat - u) (u - t)) := by
  simp only [CtlOut, blockAny_split (k := 8) htu hu]
  ac_rfl

/-! ## `SatN` -/

section SatN

variable {M : Silmaril.X86.SegVC.Isa XState} {C : XSProp} {entry : Word}

theorem SatN.zero (S : CSpec) : S.SatN M 0 C entry :=
  fun _ _ _ _ => XSTriple.zero _ _

theorem SatN.mono {n : Nat} {S : CSpec} (h : S.SatN M (n + 1) C entry) :
    S.SatN M n C entry :=
  fun x fr hA hst => (h x fr hA hst).mono

theorem SatN.code_frame {n : Nat} {S : CSpec} (h : S.SatN M n C entry) (D : XSProp) :
    S.SatN M n (C ∗ₓ D) entry := by
  intro x fr hA hst
  have h' := (h x fr hA hst).frame D
  refine XSTriple.conseq (xentails_of_eq ?_) h' (xentails_of_eq ?_) <;> ac_rfl

theorem sub_pre_shape {C Ct B AI TP SP R : XSProp} (h : TP ⊢ₓ (SP ∗ₓ R)) :
    (C ∗ₓ ((Ct ∗ₓ B) ∗ₓ AI) ∗ₓ TP) ⊢ₓ ((C ∗ₓ (Ct ∗ₓ AI) ∗ₓ SP) ∗ₓ (B ∗ₓ R)) := by
  refine xentails_trans (xsep_mono (xentails_refl _) (xsep_mono (xentails_refl _) h))
    (xentails_of_eq ?_)
  ac_rfl

theorem sub_post_shape {β : Type} {C A B R : XSProp} {RO SP TP : β → XSProp}
    (h : ∀ rb, (SP rb ∗ₓ R) ⊢ₓ TP rb) :
    ((C ∗ₓ xsexists fun rb => (A ∗ₓ RO rb) ∗ₓ SP rb) ∗ₓ (B ∗ₓ R)) ⊢ₓ
      (C ∗ₓ xsexists fun rb => ((A ∗ₓ B) ∗ₓ RO rb) ∗ₓ TP rb) := by
  rw [xsep_xsexists, xsexists_sep, xsep_xsexists]
  refine xsexists_mono fun rb => ?_
  refine xentails_trans (xentails_of_eq ?_)
    (xsep_mono (xentails_refl C) (xsep_mono (xentails_refl ((A ∗ₓ B) ∗ₓ RO rb)) (h rb)))
  ac_rfl

/-- **Refinement**: code meeting `S` for `n` steps meets every `T` with `S ⊑ T`. -/
theorem SatN.sub {n : Nat} {S T : CSpec} (h : S.SatN M n C entry) (hsub : S.Sub T) :
    T.SatN M n C entry := by
  intro y fr hA hst
  obtain ⟨x, hsh, hle, hR⟩ := hsub.arg y
  obtain ⟨R, hpre, hpost⟩ := hR fr
  have h' := (h x fr hA (le_trans hle hst)).frame
    (↑ₓ(blockAny (fr.sp.toNat - T.stack y) (T.stack y - S.stack x)) ∗ₓ R)
  refine XSTriple.conseq ?_ h' ?_
  · simp only [CSpec.Pre, CSpec.Entry, EntryOf, ← hsh, ctlIn_split hle hst, lift_sep]
    exact sub_pre_shape hpre
  · simp only [CSpec.Post, CSpec.Exit, ExitOf, ← hsh, ctlOut_split hle hst, lift_sep]
    exact sub_post_shape hpost

end SatN

theorem Sub.refl (S : CSpec) : S.Sub S :=
  ⟨fun y => ⟨y, rfl, le_refl _, fun _ => ⟨xemp, xentails_of_eq (xsep_emp _).symm,
    fun _ => xentails_of_eq (xsep_emp _)⟩⟩⟩

theorem Sub.trans {S T U : CSpec} (h₁ : S.Sub T) (h₂ : T.Sub U) : S.Sub U := by
  refine ⟨fun z => ?_⟩
  obtain ⟨y, hy, hley, hR₂⟩ := h₂.arg z
  obtain ⟨x, hx, hlex, hR₁⟩ := h₁.arg y
  refine ⟨x, hx.trans hy, le_trans hlex hley, fun fr => ?_⟩
  obtain ⟨R₂, hpre₂, hpost₂⟩ := hR₂ fr
  obtain ⟨R₁, hpre₁, hpost₁⟩ := hR₁ fr
  refine ⟨R₁ ∗ₓ R₂, ?_, fun rb => ?_⟩
  · refine xentails_trans hpre₂ (xentails_trans (xsep_mono hpre₁ (xentails_refl R₂)) ?_)
    exact xentails_of_eq (xsep_assoc _ _ _)
  · refine xentails_trans (xentails_of_eq (xsep_assoc _ _ _).symm) ?_
    exact xentails_trans (xsep_mono (hpost₁ rb) (xentails_refl R₂)) (hpost₂ rb)

end Silmaril.Proofs.X86.SepCSpec
