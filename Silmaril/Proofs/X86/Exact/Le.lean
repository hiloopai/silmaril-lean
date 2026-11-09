module

public import Silmaril.X86.Exact.Defs
public import Silmaril.X86.Institution.Thms

/-!
# Proofs: a concrete machine is below the top of a signature it tightens

The header is `Silmaril/X86/Exact/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Exact

open Silmaril.X86 (State Word Byte RelIsa)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.RelIsa (Views Res ofIsa Le)
open Silmaril.X86.Loose (FormSpec DTable DEntry AtEntry)
open Silmaril.X86.Institution (Sig)
open Silmaril.X86.Exact

variable {σ Φ : Type}

/-- **A machine is below the top of a signature whose forms its exact forms tighten**, at
every listed entry. -/
theorem le_top_of_tightens (I : Isa σ) (G : Sig Φ)
    (h : ∀ e ∈ G.table, ∃ i, I.decode e.bytes = some (i, e.bytes.length) ∧
      ∀ F, G.forms e.form = some F → F.Tightens (FormSpec.exact I i)) :
    Le (ofIsa I) (G.top (Views.ofIsa I)) where
  views := rfl
  step {s r} hl hs := by
    refine ⟨fun e he hat F hF => ?_, fun t ht => (ofIsa I).live_step hl (ht ▸ hs)⟩
    obtain ⟨i, hdec, htight⟩ := h e he
    have hsub := htight F hF
    by_cases hx : ∃ c' m', I.exec i (I.core s) (I.mem s) e.bytes.length = .ok c' m' ∧
        I.ok i c' ∧ c'.fsBase = (I.core s).fsBase
    · obtain ⟨c', m', hex, hok, hfs⟩ := hx
      refine ⟨.ok c' m', hsub _ _ _ _ (Or.inr ⟨c', m', rfl, hex, hok, hfs⟩), ?_⟩
      intro c m hcm
      cases hcm
      have hL : Silmaril.X86.Ext.Loaded (I.mem s) (I.core s).rip e.bytes := hat
      have hstep := I.step_of (o := 0) (l := e.bytes.length) hl hL (by simp) (by simp)
        (by simpa using hdec) hex hok
      have : (ofIsa I).step s r := hs
      simp only [ofIsa, hstep] at this
      exact this
    · exact ⟨.trap, hsub _ _ _ _ (Or.inl hx), fun _ _ h => by cases h⟩

/-- **`Open9` is below the top of `Σexact`** over a table of `Open9` forms. -/
theorem open9_le_exact {D : DTable Silmaril.X86.Str9.Instr} (hD : DTable.okOpen9 D = true) :
    Le (ofIsa Silmaril.X86.Open9.isa) ((Sig.exact D).top RelIsa.Views.mstate) := by
  refine le_top_of_tightens Silmaril.X86.Open9.isa (Sig.exact D) fun e he => ?_
  have h := List.all_eq_true.1 hD e he
  obtain ⟨bytes, form⟩ := e
  cases form with
  | str _ => simp at h
  | ext9 i =>
    refine ⟨i, by simpa using h, fun F hF => ?_⟩
    cases hF
    exact fun _ _ _ _ h => h

end Silmaril.Proofs.X86.Exact
