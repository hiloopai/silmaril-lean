module

public import Silmaril.Proofs.X86.MemEvent.Ext8

/-!
# Locality of `Ext9`

`Ext9.execNew` adds the `adc`/`sbb` family (`carryStep`, a whole `Result`), the 16-bit ALU and
TEST forms (`alu16`, `test16`), indirect calls and jumps, `push imm`, `bsf`/`bsr`, the
one-operand `imul` and `bt`. Their relational lemmas are added to `mev_leaf`;
`ext9_execNew_local` is one `mev_rel` per constructor except `callInd` (a read followed by a
push whose two outcomes are matched separately), and `ext9_local` combines it with
`ext8_local`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemEvent

open Silmaril.X86 (State MState Word Reg Byte)
open Silmaril.Process (Memory addressLimit)
open Silmaril.X86.Ext (Result retire loadN storeN RM Sz readRM writeRM readNarrow writeNarrow)
open Silmaril.X86.Ext9 (New carryStep alu16 test16 execNew)
open Silmaril.X86.MemEvent

theorem carryStep_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m') {sz : Sz}
    {sub : Bool} {dst : RM} {y : BitVec sz.bits} {s : State} {next : Word}
    (hR : ∀ x, rmSpan sz.bytes dst s next x → R x)
    (hW : ∀ x, W x ↔ rmSpan sz.bytes dst s next x) :
    Rel W m m' (extView (carryStep sz sub dst y s m next))
      (extView (carryStep sz sub dst y s m' next)) := by
  unfold carryStep
  rw [readRM_agree hA hR]
  cases readRM sz dst s m next with
  | none => rfl
  | some x =>
    dsimp only
    cases s.flags.carry with
    | none => rfl
    | some c =>
      exact retire_rel (OptRel.map (writeRM_rel hW hA.1) _ (fun _ => rfl) (fun _ _ _ => rfl))

theorem alu16_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m')
    {op : Silmaril.X86.AluOp} {dst : RM} {y : BitVec 16} {s : State} {next : Word}
    (hR : ∀ x, rmSpan 2 dst s next x → R x)
    (hW : ∀ x, W x ↔ op ≠ .cmp ∧ rmSpan 2 dst s next x) :
    OptRel W m m' (alu16 op dst y s m next) (alu16 op dst y s m' next) := by
  unfold alu16
  rw [readNarrow_agree (n := .w) hA hR]
  cases readNarrow .w dst s m next with
  | none => trivial
  | some x =>
    by_cases hc : op = .cmp
    · simp only [hc, ite_true]
      exact OptRel.pure (fun a ha => by simpa [hc] using (hW a).1 ha) _
    · simp only [hc, ite_false]
      exact OptRel.map (writeNarrow_rel (fun a => by simpa [hc] using hW a) hA.1) _
        (fun _ => rfl) (fun _ _ _ => rfl)

theorem test16_rel {R W : Nat → Prop} {m m' : Memory} (hA : Agree R m m') {dst : RM}
    {y : BitVec 16} {s : State} {next : Word} (hR : ∀ x, rmSpan 2 dst s next x → R x)
    (hW : ∀ x, ¬ W x) :
    OptRel W m m' (test16 dst y s m next) (test16 dst y s m' next) := by
  unfold test16
  rw [readNarrow_agree (n := .w) hA hR]
  exact OptRel.read hW _ _

macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply carryStep_rel $hA <;> mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply alu16_rel $hA <;> mev_span))
macro_rules
  | `(tactic| mev_leaf $hA) => `(tactic| (apply test16_rel $hA <;> mev_span))

section
attribute [local irreducible] Silmaril.X86.pushWord Silmaril.X86.popWord
  Silmaril.X86.Ext.writeRM Silmaril.X86.Ext.writeNarrow Silmaril.X86.Ext.writeRM8 storeN loadN
  Silmaril.X86.Ext.aluStep Silmaril.X86.Ext.aluStepR Silmaril.X86.Ext.readRM
  Silmaril.X86.Ext.readNarrow Silmaril.X86.Ext8.RM8.read Silmaril.X86.Ext8.RM8.write
  Silmaril.X86.Ext8.alu8 carryStep alu16 test16

/-- **`Ext9.execNew` is local** for `ext9NewAccesses`. -/
theorem ext9_execNew_local (i : New) (s : State) (next : Word) :
    Local extView (fun m => execNew i s m next) (ext9NewAccesses i s next) := by
  constructor
  intro m m' hA
  cases i
  case callInd src =>
    simp only [execNew, ext9NewAccesses] at hA ⊢
    rw [readRM_agree hA (by mev_span)]
    cases readRM .q src s m next with
    | none => rfl
    | some v =>
      dsimp only
      rcases OptRel.cases (pushWord_rel (s := s) (v := next)
        (W := writeSet (rmEv .load false 8 src s next ++ pushEv s)) (by mev_span) hA.1) with
        ⟨h1, h2⟩ | ⟨t, m₁, m₁', h1, h2, hp⟩
      · rw [h1, h2]; rfl
      · rw [h1, h2]; exact ⟨rfl, hp⟩
  case repRet =>
    simp only [execNew, ext9NewAccesses] at hA ⊢
    exact (ext_local .ret s 2).congr m m' hA
  all_goals (simp only [execNew, ext9NewAccesses] at hA ⊢; mev_rel hA)

end

/-- **`Ext9.exec` is local** for `ext9Accesses`. -/
theorem ext9_local (i : Silmaril.X86.Ext9.Instr) (s : State) (len : Nat) :
    Local extView (fun m => Silmaril.X86.Ext9.exec i s m len) (ext9Accesses i s len) := by
  cases i with
  | ext8 i => exact ext8_local i s len
  | new i => exact ext9_execNew_local i s _

end Silmaril.Proofs.X86.MemEvent
