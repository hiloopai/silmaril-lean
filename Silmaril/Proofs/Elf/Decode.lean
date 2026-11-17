module

public import Silmaril.Elf.Decode.Defs

/-! # Proofs of `Silmaril.Elf.Decode` -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Decode

open Silmaril.Elf
open Silmaril.Elf.Decode
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.X86.Link (Blob)

theorem runD_whole {α : Type} (F : Blob) (p : Rd α) :
    (runD (whole F) p).toOption = p.run (blobRead F) := by
  induction p with
  | pure a => rfl
  | fail => rfl
  | read o w k ih =>
    simp only [runD, Rd.run, whole]
    cases blobRead F o w with
    | none => rfl
    | some n => exact ih n

theorem runD_whole_final {α : Type} (F : Blob) (p : Rd α) : (runD (whole F) p).Final := by
  induction p with
  | pure a => trivial
  | fail => trivial
  | read o w k ih =>
    simp only [runD, whole]
    cases blobRead F o w with
    | none => trivial
    | some n => exact ih n

theorem runD_ne_unsupported {α : Type} (r : ASrc) (p : Rd α) (u : Unsupported) :
    runD r p ≠ .unsupported u := by
  induction p with
  | pure a => simp [runD]
  | fail => simp [runD]
  | read o w k ih =>
    simp only [runD]
    cases r o w with
    | val n => exact ih n
    | eof => simp
    | unknown => simp

theorem runD_refines {α : Type} {v w : ASrc} (h : Refines v w) (p : Rd α)
    (hf : (runD v p).Final) : runD w p = runD v p := by
  induction p with
  | pure a => rfl
  | fail => rfl
  | read o n k ih =>
    simp only [runD] at hf ⊢
    cases hv : v o n with
    | unknown => rw [hv] at hf; exact hf.elim
    | val m =>
      rw [h o n (by rw [hv]; exact Avail.noConfusion), hv]
      rw [hv] at hf
      exact ih m hf
    | eof => rw [h o n (by rw [hv]; exact Avail.noConfusion), hv]

theorem verdict_ne_ok (i : Ident) (why : Invalid) (A : File) :
    i.verdict.getD (.invalid why) ≠ .ok A := by
  unfold Ident.verdict
  split_ifs <;> simp

theorem verdict_final (i : Ident) (why : Invalid) : (i.verdict.getD (.invalid why)).Final := by
  unfold Ident.verdict
  split_ifs <;> trivial

theorem diagnose_ne_ok (why : Invalid) (d : Decoded (Option Ident)) (A : File) :
    diagnose why d ≠ .ok A := by
  cases d with
  | ok i =>
    cases i with
    | none => simp [diagnose]
    | some i => exact verdict_ne_ok i why A
  | _ => simp [diagnose]

theorem diagnose_final (why : Invalid) {d : Decoded (Option Ident)} (h : d.Final) :
    (diagnose why d).Final := by
  cases d with
  | ok i =>
    cases i with
    | none => trivial
    | some i => exact verdict_final i why
  | incomplete o w => exact h.elim
  | _ => trivial

theorem decode_eq (r : ASrc) : decode r = match parseD r with
    | .invalid why => diagnose why (runD r readIdent)
    | d => d := rfl

theorem decode_ok {r : ASrc} {A : File} : decode r = .ok A ↔ parseD r = .ok A := by
  rw [decode_eq]
  cases hp : parseD r with
  | invalid why => simp only; exact ⟨fun h => absurd h (diagnose_ne_ok why _ A), fun h => nomatch h⟩
  | ok B => simp
  | unsupported u => simp
  | incomplete o w => simp

theorem decode_whole_ok_iff (F : Blob) (A : File) : decode (whole F) = .ok A ↔ Parses F A := by
  rw [decode_ok, parseD, Parses, parse, ← runD_whole]
  cases runD (whole F) read <;> simp [Decoded.toOption]

theorem decode_whole_final (F : Blob) : (decode (whole F)).Final := by
  have h1 := runD_whole_final F read
  rw [decode_eq]
  cases hp : parseD (whole F) with
  | invalid why => exact diagnose_final why (runD_whole_final F readIdent)
  | ok B => trivial
  | unsupported u => trivial
  | incomplete o w => rw [parseD] at hp; rw [hp] at h1; exact h1.elim

theorem decode_refines {v w : ASrc} (h : Refines v w) (hf : (decode v).Final) :
    decode w = decode v := by
  rw [decode_eq] at hf ⊢
  rw [decode_eq]
  cases hp : parseD v with
  | ok A =>
    have : parseD w = parseD v := runD_refines h read (by rw [parseD] at hp; rw [hp]; trivial)
    rw [this, hp]
  | unsupported u => exact absurd hp (runD_ne_unsupported v read u)
  | incomplete o n =>
    rw [hp] at hf; exact hf.elim
  | invalid why =>
    have hpw : parseD w = parseD v := runD_refines h read (by rw [parseD] at hp; rw [hp]; trivial)
    rw [hpw, hp]
    rw [hp] at hf
    simp only at hf ⊢
    cases hi : runD v readIdent with
    | incomplete o n => rw [hi] at hf; exact hf.elim
    | unsupported u => exact absurd hi (runD_ne_unsupported v readIdent u)
    | _ =>
      have : runD w readIdent = runD v readIdent := runD_refines h readIdent (by rw [hi]; trivial)
      rw [this, hi]

theorem prefixOf_refines (F : Blob) (k : Nat) : Refines (prefixOf F k) (whole F) := by
  intro o n hne
  simp only [prefixOf] at hne ⊢
  split
  · rfl
  · rename_i hk; simp [hk] at hne

theorem windows_refines (F : Blob) (ws : List Span) :
    Refines (windows ws (blobRead F)) (whole F) := by
  intro o n hne
  simp only [windows] at hne ⊢
  split
  · rfl
  · rename_i hk; simp [hk] at hne

end Silmaril.Proofs.Elf.Decode
