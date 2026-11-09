module

public import Silmaril.Proofs.X86.MemEvent.Ext

/-!
# Locality of `Ext8`: the byte forms

`Ext8.execNew` adds the byte `r/m8` forms (`RM8.read`, `RM8.write`, `alu8`). Their relational
lemmas are added to `mev_leaf`; `ext8_execNew_local` is one `mev_rel` per constructor (the
shift splits on its masked count, on which the access list depends: a zero count writes
nothing), and `ext8_local` combines it with `ext_local`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Ext (Result retire loadN storeN)
open Silmaril.X86.Ext8 (RM8 New alu8 execNew)
open Silmaril.X86.MemEvent

theorem rm8Read_agree {R : Nat → Prop} {m m' : Memory} (h : Agree R m m') {op : RM8}
    {s : State} {next : Word} (hs : ∀ x, rm8Span op s next x → R x) :
    op.read s m' next = op.read s m next := by
  cases op with
  | reg r => rfl
  | mem a => simp only [RM8.read]; rw [loadN_agree h hs]

theorem rm8Write_rel {W : Nat → Prop} {m m' : Memory} {op : RM8} {v : BitVec 8} {s : State}
    {next : Word} (hW : ∀ x, W x ↔ rm8Span op s next x) (h : m.regions = m'.regions) :
    OptRel W m m' (op.write v s m next) (op.write v s m' next) := by
  cases op with
  | reg r => exact OptRel.pure (fun a ha => by simpa using (hW a).1 ha) _
  | mem a => exact storeN_rel (by simpa using hW) h s

theorem alu8_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m')
    {op : Silmaril.X86.AluOp} {dst : RM8} {y : BitVec 8} {s : State} {next : Word}
    (hR : ∀ x, rm8Span dst s next x → R x)
    (hW : ∀ x, W x ↔ op ≠ .cmp ∧ rm8Span dst s next x) :
    OptRel W m m' (alu8 op dst y s m next) (alu8 op dst y s m' next) := by
  unfold alu8
  rw [rm8Read_agree hA hR]
  cases dst.read s m next with
  | none => trivial
  | some x =>
    by_cases hc : op = .cmp
    · simp only [hc, ite_true]
      exact OptRel.pure (fun a ha => by simpa [hc] using (hW a).1 ha) _
    · simp only [hc, ite_false]
      exact OptRel.map (rm8Write_rel (fun a => by simpa [hc] using hW a) hA.1) _
        (fun _ => rfl) (fun _ _ _ => rfl)

macro_rules
  | `(tactic| mev_leaf $hA) =>
    `(tactic| (rw [rm8Read_agree $hA]; rotate_left; mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply alu8_rel $hA <;> mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply rm8Write_rel _ ($hA).1; mev_span))

section
attribute [local irreducible] Silmaril.X86.pushWord Silmaril.X86.popWord
  Silmaril.X86.Ext.writeRM Silmaril.X86.Ext.writeNarrow Silmaril.X86.Ext.writeRM8 storeN loadN
  Silmaril.X86.Ext.aluStep Silmaril.X86.Ext.aluStepR Silmaril.X86.Ext.readRM
  Silmaril.X86.Ext.readNarrow RM8.read RM8.write alu8

/-- **`Ext8.execNew` is local** for `ext8NewAccesses`. -/
theorem ext8_execNew_local (i : New) (s : State) (next : Word) :
    Local extView (fun m => execNew i s m next) (ext8NewAccesses i s next) := by
  constructor
  intro m m' hA
  cases i
  case shift op dst count =>
    by_cases hc : (count.raw s).toNat % 32 = 0
    · simp only [execNew, ext8NewAccesses, hc, ite_true] at hA ⊢; mev_rel hA
    · simp only [execNew, ext8NewAccesses, hc, ite_false] at hA ⊢; mev_rel hA
  all_goals (simp only [execNew, ext8NewAccesses] at hA ⊢; mev_rel hA)

end

/-- **`Ext8.exec` is local** for `ext8Accesses`. -/
theorem ext8_local (i : Silmaril.X86.Ext8.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Silmaril.X86.Ext8.exec i s m len) (ext8Accesses i s len) := by
  cases i with
  | base i => exact ext_local i s len
  | new i => exact ext8_execNew_local i s _

end Silmaril.Proofs.X86.MemEvent
