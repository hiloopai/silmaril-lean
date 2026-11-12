module

public import Silmaril.Libc.AllocElf.Defs
public import Silmaril.Libc.AllocSig.Thms

/-!
# Allocator contracts over an ELF file: reducts and strengths

* `reduct`: **a contract at signature `s'` gives the contract at every `s ≤ s'`** (the same
  entries and witness): the reduct along the inclusions of the hierarchy
  `mf ⊂ mfc ⊂ mfcr ⊂ full`. `PosixSafe.reduct`, and the three steps `full_mfcr`, `mfcr_mfc`,
  `mfc_mf`.
* `mono`: a stronger relation gives the weaker contract (`Rel.Le`); so every strength above
  `loose` gives `PosixSafe` (`posixSafe_of`).
* `exports_of`: a contract gives the binding part (`Exports`), which rows check on the file.

Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Libc.AllocElf

open Silmaril.Libc.AllocSig
open Silmaril.X86.Link (Blob)

/-- **Reduct along `s ≤ s'`.** -/
theorem reduct {T : Rel} {LM : LoadModel} {s s' : Sig} {F : Blob} {S : Syms} (hle : s ≤ s')
    (h : Contract T LM s' F S) : Contract T LM s F S :=
  let ⟨v, hb, W, hs, hd, hc⟩ := h
  ⟨v, fun op ho => hb op (ops_mono hle ho), W, hs, hd, fun op ho => hc op (ops_mono hle ho)⟩

theorem PosixSafe.reduct {LM : LoadModel} {s s' : Sig} {F : Blob} {S : Syms} (hle : s ≤ s')
    (h : PosixSafe LM s' F S) : PosixSafe LM s F S :=
  AllocElf.reduct hle h

theorem full_mfcr {LM : LoadModel} {F : Blob} {S : Syms} (h : PosixSafe LM .full F S) :
    PosixSafe LM .mfcr F S := PosixSafe.reduct (by decide) h

theorem mfcr_mfc {LM : LoadModel} {F : Blob} {S : Syms} (h : PosixSafe LM .mfcr F S) :
    PosixSafe LM .mfc F S := PosixSafe.reduct (by decide) h

theorem mfc_mf {LM : LoadModel} {F : Blob} {S : Syms} (h : PosixSafe LM .mfc F S) :
    PosixSafe LM .mf F S := PosixSafe.reduct (by decide) h

theorem must_mono {σ : Type} {A : Silmaril.X86.RelIsa σ} {R Q Q' : σ → Prop}
    (hq : ∀ y, Q y → Q' y) {x : σ} (h : Silmaril.X86.RelIsa.Must A R Q x) :
    Silmaril.X86.RelIsa.Must A R Q' x := by
  induction h with
  | done hQ => exact .done (hq _ hQ)
  | step hR hs _ ih => exact .step hR hs ih

/-- **A stronger relation gives the weaker contract.** -/
theorem mono {R T : Rel} {LM : LoadModel} {s : Sig} {F : Blob} {S : Syms} (hRT : R.Le T)
    (h : Contract R LM s F S) : Contract T LM s F S := by
  obtain ⟨v, hb, W, hs, hd, hc⟩ := h
  refine ⟨v, hb, W, hs, hd, fun op ho b St x hp hi hrip he => ?_⟩
  refine must_mono (fun y hy => ?_) (hc op ho b St x hp hi hrip he)
  obtain ⟨h1, h2, S', q, h3, h4, h5, h6, h7⟩ := hy
  exact ⟨h1, h2, S', q, h3, h4, hRT _ _ _ _ _ h5, h6, h7⟩

/-- Every strength above `loose` gives the POSIX-safe contract. -/
theorem posixSafe_of {R : Rel} {LM : LoadModel} {s : Sig} {F : Blob} {S : Syms}
    (hR : R.Le loose) (h : Contract R LM s F S) : PosixSafe LM s F S := mono hR h

/-- **A contract binds its functions.** -/
theorem exports_of {T : Rel} {LM : LoadModel} {s : Sig} {F : Blob} {S : Syms}
    (h : Contract T LM s F S) : Exports s F S :=
  let ⟨v, hb, _⟩ := h
  fun op ho => ⟨v op, hb op ho⟩

/-- **The exports of the whole API exist** when each of the seven functions is bound. -/
theorem exports_full (S : Syms) (F : Blob)
    (h1 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .malloc) v)
    (h2 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .free) v)
    (h3 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .calloc) v)
    (h4 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .realloc) v)
    (h5 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .alignedAlloc) v)
    (h6 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .posixMemalign) v)
    (h7 : ∃ v, Silmaril.Elf.Link.ElfBind.Bound F (S.sel .usableSize) v) :
    Exports .full F S := by
  intro op ho
  simp only [Sig.ops, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4, h5, h6, h7]

/-- The exports of a level exist when those of the whole API do. -/
theorem Exports.reduct {s s' : Sig} {F : Blob} {S : Syms} (hle : s ≤ s') (h : Exports s' F S) :
    Exports s F S :=
  fun op ho => h op (ops_mono hle ho)

end Silmaril.Libc.AllocElf
