module

public import Silmaril.Proofs.X86.MemEvent.Ext

/-!
# Locality of the SSE forms (`Sse9.exec`)

`Sse9.exec` returns an `XResult` (core, XMM file and memory, or a data or alignment fault),
viewed by `sse9View`. The alignment check depends only on the core, so it is the same on both
memories. The 128-bit loads go through `Memory.readBytes` (`readX_agree`), and the stores
through `Memory.writeBytes` (`store128`), `storeN` and `writeRM`; a store's two outcomes are
matched by case analysis on the two related outcomes.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Ext (loadN storeN RM Sz readRM writeRM)
open Silmaril.X86.Sse9 (Instr XRM XFile XResult exec readX load128 store128 binop
  misaligned)
open Silmaril.X86.MemEvent

theorem sse9View_dataFault {W : Nat → Prop} {m m' : Memory} :
    Rel W m m' (sse9View .dataFault) (sse9View .dataFault) := rfl

theorem sse9View_alignFault {W : Nat → Prop} {m m' : Memory} :
    Rel W m m' (sse9View .alignFault) (sse9View .alignFault) := rfl

theorem sse9View_ok_pure {W : Nat → Prop} {m m' : Memory} (hW : ∀ a, ¬ W a) (c : State)
    (x : XFile) : Rel W m m' (sse9View (.ok c x m)) (sse9View (.ok c x m')) :=
  ⟨rfl, Patched.none hW⟩

theorem readX_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {src : XRM}
    {s : State} {x : XFile} {next : Word} (hs : ∀ a, xrmSpan 16 src s next a → R a) :
    readX src s x m' next = readX src s x m next := by
  cases src with
  | reg r => rfl
  | mem a =>
    simp only [readX, load128]
    rw [readBytes_agree h (fun o ho => hs _ ⟨by omega, by simpa using ho⟩)]

theorem store128_rel {W : Nat → Prop} {m m' : Memory} {a : Word} {v : Silmaril.X86.Sse9.Xmm}
    (hW : ∀ x, W x ↔ a.toNat ≤ x ∧ x < a.toNat + 16) (h : m.regions = m'.regions) :
    OptRel W m m' ((store128 m a v).map fun m₁ => ((), m₁))
      ((store128 m' a v).map fun m₁ => ((), m₁)) :=
  writeBytes_rel (by simpa [Silmaril.X86.Sse9.le128] using hW) h ()

theorem binop_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m')
    {f : Silmaril.X86.Sse9.Xmm → Silmaril.X86.Sse9.Xmm → Silmaril.X86.Sse9.Xmm}
    {dst : Silmaril.X86.XReg} {src : XRM} {s : State} {x : XFile} {next : Word}
    (hR : ∀ a, xrmSpan 16 src s next a → R a) (hW : ∀ a, ¬ W a) :
    Rel W m m' (sse9View (binop f dst src s x m next)) (sse9View (binop f dst src s x m' next)) := by
  unfold binop
  rw [readX_agree hA hR]
  split
  · rfl
  · cases readX src s x m next with
    | none => rfl
    | some v => exact sse9View_ok_pure hW _ _

section
attribute [local irreducible] storeN loadN readRM writeRM readX store128 binop

/-- **`Sse9.exec` is local** for `sse9Accesses`, for every XMM file. -/
theorem sse9_local (i : Instr) (s : State) (x : XFile) (next : Word) :
    Local sse9View (fun m => exec i s x m next) (sse9Accesses i s next) := by
  constructor
  intro m m' hA
  cases i <;> simp only [exec, sse9Accesses] at hA ⊢
  case load k dst src =>
    rw [readX_agree hA (by mev_span)]
    split
    · rfl
    · cases readX src s x m next with
      | none => rfl
      | some v => exact sse9View_ok_pure (by mev_span) _ _
  case store k dst src =>
    cases dst with
    | reg r => exact sse9View_ok_pure (by mev_span) _ _
    | mem a =>
      dsimp only
      split
      · rfl
      · have h := store128_rel (m := m) (m' := m') (a := a.addr s next) (v := x src)
          (W := writeSet (xrmEv .store 16 (.mem a) s next)) (by mev_span) hA.1
        revert h
        cases store128 m (a.addr s next) (x src) <;>
          cases store128 m' (a.addr s next) (x src) <;> intro h
        · rfl
        · cases h
        · cases h
        · exact ⟨rfl, h.2⟩
  case movToX sz dst src =>
    rw [readRM_agree hA (by mev_span)]
    cases readRM sz src s m next with
    | none => rfl
    | some v => exact sse9View_ok_pure (by mev_span) _ _
  case movFromX sz dst src =>
    have h := writeRM_rel (m := m) (m' := m') (sz := sz) (op := dst)
      (v := (x src).setWidth sz.bits) (s := s) (next := next)
      (W := writeSet (rmEv .store false sz.bytes dst s next)) (by mev_span) hA.1
    revert h
    cases writeRM sz dst ((x src).setWidth sz.bits) s m next with
    | none => cases writeRM sz dst ((x src).setWidth sz.bits) s m' next with
      | none => intro _; rfl
      | some _ => intro h; cases h
    | some p => cases writeRM sz dst ((x src).setWidth sz.bits) s m' next with
      | none => intro h; cases h
      | some p' =>
        intro h
        obtain ⟨t, mm⟩ := p; obtain ⟨t', mm'⟩ := p'
        obtain ⟨e, hp⟩ := h
        simp only at e; subst e
        exact ⟨rfl, hp⟩
  case movqLoad dst src =>
    cases src with
    | reg r => exact sse9View_ok_pure (by mev_span) _ _
    | mem a =>
      dsimp only
      rw [loadN_agree hA (by mev_span)]
      cases loadN m (a.addr s next) 8 with
      | none => rfl
      | some v => exact sse9View_ok_pure (by mev_span) _ _
  case movqStore dst src =>
    cases dst with
    | reg r => exact sse9View_ok_pure (by mev_span) _ _
    | mem a =>
      dsimp only
      have h := storeN_rel (m := m) (m' := m') (a := a.addr s next) (k := 8)
        (v := (x src).setWidth 64) (W := writeSet (xrmEv .store 8 (.mem a) s next)) (by mev_span)
        hA.1 ()
      revert h
      cases storeN m (a.addr s next) 8 ((x src).setWidth 64) <;>
        cases storeN m' (a.addr s next) 8 ((x src).setWidth 64) <;> intro h
      · rfl
      · cases h
      · cases h
      · exact ⟨rfl, h.2⟩
  all_goals exact binop_rel hA (by mev_span) (by mev_span)

end

end Silmaril.Proofs.X86.MemEvent
