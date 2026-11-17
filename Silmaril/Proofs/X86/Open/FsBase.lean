module

public import Silmaril.X86.Open9.Defs

/-!
# No open-machine step writes the FS base

`State.fsBase` is read by `fs:` operands (`Ext.Base.value .fs`) and written by nothing: no
instruction of `X86.Ext`, `Ext8` or `Ext9` has a `wrfsbase` or MSR-write case. This module
proves it, one state helper at a time, and then for `Open.step` and `Open9.step`.

`KeepsO b o` / `KeepsR b r` say that the state an optional state-and-memory or an execution
result carries (if any) has FS base `b`. The helper lemmas are `simp` lemmas; the instruction
cases are closed by `split` and `simp`, with an explicit `exact` where the operand type is
`BitVec sz.bits` and `simp` cannot match up to instances transparency.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Open.FsBase

open Silmaril.X86 (State MState Word Reg)
open Silmaril.Process (Memory)

/-- The state an optional state-and-memory carries, if any, has FS base `b`. -/
def KeepsO (b : Word) : Option (State × Memory) → Prop
  | some (t, _) => t.fsBase = b
  | none => True

/-- The state of a successful result, if any, has FS base `b`. -/
def KeepsR (b : Word) : Silmaril.X86.Ext.Result → Prop
  | .ok t _ => t.fsBase = b
  | _ => True

@[simp] theorem keepsO_some (b : Word) (t : State) (m : Memory) :
    KeepsO b (some (t, m)) ↔ t.fsBase = b := Iff.rfl
@[simp] theorem keepsO_none (b : Word) : KeepsO b none := trivial
@[simp] theorem keepsR_ok (b : Word) (t : State) (m : Memory) :
    KeepsR b (.ok t m) ↔ t.fsBase = b := Iff.rfl
@[simp] theorem keepsR_dataFault (b : Word) : KeepsR b .dataFault := trivial
@[simp] theorem keepsR_divideError (b : Word) : KeepsR b .divideError := trivial
@[simp] theorem keepsR_undefinedCondition (b : Word) (c : Silmaril.X86.Ext.Cond) :
    KeepsR b (.undefinedCondition c) := trivial
@[simp] theorem keepsR_trap (b : Word) : KeepsR b .trap := trivial

theorem keepsO_map_of {α : Type} {b : Word} {o : Option α} {f : α → State × Memory}
    (h : ∀ a, (f a).1.fsBase = b) : KeepsO b (o.map f) := by
  cases o <;> simp [KeepsO, h]

@[simp] theorem keepsO_map_flags (b : Word) (o : Option (State × Memory))
    (c : Silmaril.X86.Flags) :
    KeepsO b (o.map fun r => ({ r.1 with flags := c }, r.2)) ↔ KeepsO b o := by
  match o with
  | some (_, _) => exact Iff.rfl
  | none => exact Iff.rfl

@[simp] theorem keepsR_retire (b next : Word) (o : Option (State × Memory)) :
    KeepsR b (Silmaril.X86.Ext.retire next o) ↔ KeepsO b o := by
  match o with
  | some (_, _) => exact Iff.rfl
  | none => exact Iff.rfl

/-! ## State helpers -/

@[simp] theorem sz_write_fsBase (sz : Silmaril.X86.Ext.Sz) (s : State) (r : Reg)
    (v : BitVec sz.bits) : (sz.write s r v).fsBase = s.fsBase := rfl

@[simp] theorem writeByte_fsBase (s : State) (r : Reg) (v : BitVec 8) :
    (Silmaril.X86.Ext.writeByte s r v).fsBase = s.fsBase := rfl

@[simp] theorem bReg_write_fsBase (s : State) (b : Silmaril.X86.Ext8.BReg) (v : BitVec 8) :
    (b.write s v).fsBase = s.fsBase := by
  cases b <;> rfl

@[simp] theorem writeRM_keeps (sz op v s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext.writeRM sz op v s memory next) := by
  cases op
  · rfl
  · exact keepsO_map_of fun _ => rfl

@[simp] theorem writeNarrow_keeps (n op v s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext.writeNarrow n op v s memory next) := by
  cases op
  · rfl
  · exact keepsO_map_of fun _ => rfl

@[simp] theorem writeRM8_keeps (op v s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext.writeRM8 op v s memory next) := by
  cases op
  · rfl
  · exact keepsO_map_of fun _ => rfl

@[simp] theorem rm8_write_keeps (op : Silmaril.X86.Ext8.RM8) (v s memory next) :
    KeepsO s.fsBase (op.write v s memory next) := by
  cases op
  · exact bReg_write_fsBase _ _ _
  · exact keepsO_map_of fun _ => rfl

@[simp] theorem pushWord_keeps (s : State) (memory : Memory) (v : Word) :
    KeepsO s.fsBase (Silmaril.X86.pushWord s memory v) :=
  keepsO_map_of fun _ => rfl

theorem pushWord_fsBase {s : State} {memory memory' : Memory} {v : Word} {t : State}
    (h : Silmaril.X86.pushWord s memory v = some (t, memory')) : t.fsBase = s.fsBase := by
  have := pushWord_keeps s memory v
  rwa [h] at this

theorem popWord_fsBase {s : State} {memory : Memory} {v : Word} {t : State}
    (h : Silmaril.X86.popWord s memory = some (v, t)) : t.fsBase = s.fsBase := by
  simp only [Silmaril.X86.popWord, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, -, rfl⟩ := h
  rfl

theorem popWord_map_keeps {b : Word} {s : State} {memory : Memory}
    {g : Word × State → State × Memory} (hb : s.fsBase = b)
    (hg : ∀ r, (g r).1.fsBase = r.2.fsBase) :
    KeepsO b ((Silmaril.X86.popWord s memory).map g) := by
  cases h : Silmaril.X86.popWord s memory with
  | none => trivial
  | some r =>
    obtain ⟨v, t⟩ := r
    show (g (v, t)).1.fsBase = b
    rw [hg, ← hb]
    exact popWord_fsBase h

@[simp] theorem aluStep_keeps (sz op dst y s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext.aluStep sz op dst y s memory next) := by
  unfold Silmaril.X86.Ext.aluStep
  split
  · trivial
  · split <;> simp

@[simp] theorem aluStepR_keeps (sz op dst src s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext.aluStepR sz op dst src s memory next) := by
  unfold Silmaril.X86.Ext.aluStepR
  split
  · trivial
  · split <;> simp

@[simp] theorem alu8_keeps (op dst y s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext8.alu8 op dst y s memory next) := by
  unfold Silmaril.X86.Ext8.alu8
  split
  · trivial
  · split <;> simp

@[simp] theorem alu16_keeps (op dst y s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext9.alu16 op dst y s memory next) := by
  unfold Silmaril.X86.Ext9.alu16
  split
  · trivial
  · split <;> simp

@[simp] theorem test16_keeps (dst y s memory next) :
    KeepsO s.fsBase (Silmaril.X86.Ext9.test16 dst y s memory next) :=
  keepsO_map_of fun _ => rfl

@[simp] theorem carryStep_keeps (sz sub dst y s memory next) :
    KeepsR s.fsBase (Silmaril.X86.Ext9.carryStep sz sub dst y s memory next) := by
  unfold Silmaril.X86.Ext9.carryStep
  split
  · trivial
  · split <;> simp

/-- Closes the goals left by splitting an instruction's semantics. -/
local macro "keeps_close" : tactic => `(tactic| first
  | rfl
  | exact keepsO_map_of fun _ => rfl
  | exact keepsO_map_of fun _ => bReg_write_fsBase _ _ _
  | exact popWord_map_keeps rfl fun _ => rfl
  | exact pushWord_keeps _ _ _
  | exact pushWord_fsBase ‹_›
  | exact popWord_fsBase ‹_›
  | exact alu16_keeps _ _ _ _ _ _)

/-! ## Instruction semantics -/

theorem extExec_keeps (i : Silmaril.X86.Ext.Instr) (s : State) (memory : Memory) (length : Nat) :
    KeepsR s.fsBase (Silmaril.X86.Ext.exec i s memory length) := by
  simp only [Silmaril.X86.Ext.exec]
  split <;> (repeat' split) <;> simp <;> keeps_close

theorem ext8ExecNew_keeps (i : Silmaril.X86.Ext8.New) (s : State) (memory : Memory) (next : Word) :
    KeepsR s.fsBase (Silmaril.X86.Ext8.execNew i s memory next) := by
  simp only [Silmaril.X86.Ext8.execNew]
  split <;> (repeat' split) <;> simp <;> keeps_close

theorem ext9ExecNew_keeps (i : Silmaril.X86.Ext9.New) (s : State) (memory : Memory) (next : Word) :
    KeepsR s.fsBase (Silmaril.X86.Ext9.execNew i s memory next) := by
  simp only [Silmaril.X86.Ext9.execNew]
  split <;> (repeat' split) <;> (try simp) <;> first | keeps_close | exact extExec_keeps _ _ _ _

/-! ## The open machines -/

theorem ofResult_fsBase {b : Word} {r : Silmaril.X86.Ext.Result} {m' : MState}
    (k : KeepsR b r) (h : Silmaril.X86.Open.ofResult r = some m') : m'.core.fsBase = b := by
  cases r <;> simp only [Silmaril.X86.Open.ofResult, reduceCtorEq, Option.some.injEq] at h
  subst h
  exact k

/-- No step of the open machine writes the FS base. -/
theorem openStep_fsBase (m m' : MState) (h : Silmaril.X86.Open.step m = some m') :
    m'.core.fsBase = m.core.fsBase := by
  unfold Silmaril.X86.Open.step at h
  split at h
  · exact ofResult_fsBase (extExec_keeps _ _ _ _) h
  · exact ofResult_fsBase (ext8ExecNew_keeps _ _ _ _) h
  · simp at h

/-- No step of the open machine over `Ext9` writes the FS base. -/
theorem open9Step_fsBase (m m' : MState) (h : Silmaril.X86.Open9.step m = some m') :
    m'.core.fsBase = m.core.fsBase := by
  unfold Silmaril.X86.Open9.step at h
  split at h
  · split at h
    · exact ofResult_fsBase (ext9ExecNew_keeps _ _ _ _) h
    · simp at h
  · exact openStep_fsBase m m' h

end Silmaril.Proofs.X86.Open.FsBase
