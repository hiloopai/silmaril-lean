module

public import Silmaril.X86.Ext.Machine

/-! # `X86.Ext.exec` is monotone in the definedness of the flags (VERIFIED)

The LPS machine `x86WithFlagOracle` completes the undefined status flags at every `syscall`
(the completed flags supply R11), while the CLI model `X86Linux.isa` leaves them as they are
(and R11 unspecified). After a system call the two cores therefore agree except that the LPS
flags are at least as defined. This file shows that this relation, `CoreLe`, is preserved by
every instruction: if the less defined core retires, the more defined one retires to the same
memory with a core that is again `CoreLe`-related (`exec_mono`).

Flags are read by `exec` only through `Cond.eval` (Kleene three-valued, hence monotone), the
CF preserved by INC/DEC and the flags a zero-count shift or a rotate preserves; every other
flag result is a function of the operands alone.

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono

open Silmaril.X86 (Flags State Reg Word)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

/-- `b` is at least as defined as `a` and agrees with it where `a` is defined. -/
def OptLe (a b : Option Bool) : Prop := a = none ∨ a = b

theorem OptLe.refl (a : Option Bool) : OptLe a a := .inr rfl

theorem OptLe.some_eq {a b : Option Bool} (h : OptLe a b) {v : Bool} (hv : a = some v) :
    b = some v := by
  rcases h with h | h
  · rw [h] at hv; cases hv
  · rw [← h, hv]

theorem kNot_mono {a b : Option Bool} (h : OptLe a b) : OptLe (kNot a) (kNot b) := by
  rcases h with rfl | rfl
  · exact .inl rfl
  · exact .refl _

theorem kOr_mono {a b c d : Option Bool} (h₁ : OptLe a b) (h₂ : OptLe c d) :
    OptLe (kOr a c) (kOr b d) := by
  unfold OptLe
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    first
    | (right; rfl)
    | (rcases b with _ | ⟨_ | _⟩ <;> rcases d with _ | ⟨_ | _⟩ <;> simp [kOr])
    | (rcases a with _ | ⟨_ | _⟩ <;> rcases d with _ | ⟨_ | _⟩ <;> simp [kOr])
    | (rcases b with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;> simp [kOr])

theorem kXor_mono {a b c d : Option Bool} (h₁ : OptLe a b) (h₂ : OptLe c d) :
    OptLe (kXor a c) (kXor b d) := by
  unfold OptLe
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · left; rfl
  · left; cases c <;> rfl
  · left; cases a <;> rfl
  · right; rfl

/-- Flag-wise `OptLe`. -/
structure FlagsLe (f g : Flags) : Prop where
  carry : OptLe f.carry g.carry
  parity : OptLe f.parity g.parity
  adjust : OptLe f.adjust g.adjust
  zero : OptLe f.zero g.zero
  sign : OptLe f.sign g.sign
  overflow : OptLe f.overflow g.overflow

theorem FlagsLe.refl (f : Flags) : FlagsLe f f :=
  ⟨.refl _, .refl _, .refl _, .refl _, .refl _, .refl _⟩

theorem Cond.eval_mono {f g : Flags} (h : FlagsLe f g) (c : Cond) :
    OptLe (c.eval f) (c.eval g) := by
  obtain ⟨hc, hp, -, hz, hs, ho⟩ := h
  cases c <;> simp only [Cond.eval] <;>
    first
    | assumption
    | exact kNot_mono ‹_›
    | exact kOr_mono hc hz
    | exact kNot_mono (kOr_mono hc hz)
    | exact kXor_mono hs ho
    | exact kNot_mono (kXor_mono hs ho)
    | exact kOr_mono hz (kXor_mono hs ho)
    | exact kNot_mono (kOr_mono hz (kXor_mono hs ho))

theorem Cond.eval_mono_some {f g : Flags} (h : FlagsLe f g) (c : Cond) {v : Bool}
    (hv : c.eval f = some v) : c.eval g = some v :=
  (Cond.eval_mono h c).some_eq hv

theorem incFlagsN_mono {n : Nat} (x : BitVec n) {f g : Flags} (h : FlagsLe f g) :
    FlagsLe (incFlagsN x f) (incFlagsN x g) :=
  ⟨h.carry, .refl _, .refl _, .refl _, .refl _, .refl _⟩

theorem decFlagsN_mono {n : Nat} (x : BitVec n) {f g : Flags} (h : FlagsLe f g) :
    FlagsLe (decFlagsN x f) (decFlagsN x g) :=
  ⟨h.carry, .refl _, .refl _, .refl _, .refl _, .refl _⟩

theorem ShiftOp.flags_mono {n : Nat} (op : ShiftOp) (x : BitVec n) (c : Nat) {f g : Flags}
    (h : FlagsLe f g) : FlagsLe (op.flags x c f) (op.flags x c g) := by
  by_cases zero : c = 0
  · simp only [ShiftOp.flags, zero, ite_true]; exact h
  · cases op <;> simp only [ShiftOp.flags, zero, ite_false] <;>
      first
      | exact .refl _
      | exact ⟨.refl _, h.parity, h.adjust, h.zero, h.sign, .refl _⟩

/-- Equal cores up to more defined flags. -/
def CoreLe (s t : State) : Prop := t = { s with flags := t.flags } ∧ FlagsLe s.flags t.flags

theorem CoreLe.refl (s : State) : CoreLe s s := ⟨rfl, .refl _⟩

theorem CoreLe.withFlags (s : State) {g : Flags} (h : FlagsLe s.flags g) :
    CoreLe s { s with flags := g } := ⟨rfl, h⟩

/-! ## The operand helpers do not read the flags -/

section Helpers

variable (s : State) (g : Flags) (memory : Memory) (next : Word)

@[simp] theorem read_withFlags (r : Reg) : ({ s with flags := g } : State).read r = s.read r := rfl

@[simp] theorem write_withFlags (r : Reg) (v : Word) :
    ({ s with flags := g } : State).write r v = { s.write r v with flags := g } := rfl

@[simp] theorem szRead_withFlags (sz : Sz) (r : Reg) :
    sz.read ({ s with flags := g } : State) r = sz.read s r := rfl

@[simp] theorem szWrite_withFlags (sz : Sz) (r : Reg) (v : BitVec sz.bits) :
    sz.write ({ s with flags := g } : State) r v = { sz.write s r v with flags := g } := rfl

@[simp] theorem writeByte_withFlags (r : Reg) (v : BitVec 8) :
    writeByte ({ s with flags := g } : State) r v = { writeByte s r v with flags := g } := rfl

@[simp] theorem addr_withFlags (m : Mem) :
    m.addr ({ s with flags := g } : State) next = m.addr s next := by
  cases m with
  | mk base index disp =>
    cases base <;> cases index <;> rfl

@[simp] theorem countRaw_withFlags (count : Count) :
    count.raw ({ s with flags := g } : State) = count.raw s := by
  cases count <;> rfl

@[simp] theorem readRM_withFlags (sz : Sz) (op : RM) :
    readRM sz op ({ s with flags := g } : State) memory next = readRM sz op s memory next := by
  cases op <;> simp [readRM]

@[simp] theorem readNarrow_withFlags (n : Narrow) (op : RM) :
    readNarrow n op ({ s with flags := g } : State) memory next =
      readNarrow n op s memory next := by
  cases op <;> simp [readNarrow]

@[simp] theorem writeRM_withFlags (sz : Sz) (op : RM) (v : BitVec sz.bits) :
    writeRM sz op v ({ s with flags := g } : State) memory next =
      (writeRM sz op v s memory next).map fun r => ({ r.1 with flags := g }, r.2) := by
  cases op with
  | reg r => rfl
  | mem m =>
    simp only [writeRM, addr_withFlags, Option.map_map]
    cases storeN memory (m.addr s next) sz.bytes (v.setWidth 64) <;> rfl

@[simp] theorem writeNarrow_withFlags (n : Narrow) (op : RM) (v : BitVec n.bits) :
    writeNarrow n op v ({ s with flags := g } : State) memory next =
      (writeNarrow n op v s memory next).map fun r => ({ r.1 with flags := g }, r.2) := by
  cases op with
  | reg r => rfl
  | mem m =>
    simp only [writeNarrow, addr_withFlags, Option.map_map]
    cases storeN memory (m.addr s next) n.bytes (v.setWidth 64) <;> rfl

@[simp] theorem writeRM8_withFlags (op : RM) (v : BitVec 8) :
    writeRM8 op v ({ s with flags := g } : State) memory next =
      (writeRM8 op v s memory next).map fun r => ({ r.1 with flags := g }, r.2) := by
  cases op with
  | reg r => rfl
  | mem m =>
    simp only [writeRM8, addr_withFlags, Option.map_map]
    cases storeN memory (m.addr s next) 1 (v.setWidth 64) <;> rfl

@[simp] theorem pushWord_withFlags (v : Word) :
    X86.pushWord ({ s with flags := g } : State) memory v =
      (X86.pushWord s memory v).map fun r => ({ r.1 with flags := g }, r.2) := by
  simp only [X86.pushWord, read_withFlags, Option.map_map]
  cases memory.writeBytes (s.read .rsp - 8#64).toNat
    (Silmaril.Machine.LittleEndian.encodeWords [v]) <;> rfl

@[simp] theorem popWord_withFlags :
    X86.popWord ({ s with flags := g } : State) memory =
      (X86.popWord s memory).map fun r => (r.1, { r.2 with flags := g }) := by
  unfold X86.popWord
  cases h : memory.readBytes (s.read .rsp).toNat 8 with
  | none => simp [h]
  | some bytes =>
    cases h' : X86.wordOfBytes? bytes <;> simp [h, h']

end Helpers

/-! ## Instructions -/

/-- Replace the flags of a retired core. -/
def withFlagsR (g : Flags) : Result → Result
  | .ok core memory => .ok { core with flags := g } memory
  | r => r

@[simp] theorem retire_map_withFlags (next : Word) (g : Flags) (o : Option (State × Memory)) :
    retire next (o.map fun r => ({ r.1 with flags := g }, r.2)) =
      withFlagsR g (retire next o) := by
  cases o with
  | none => rfl
  | some r => rfl

@[simp] theorem retire_some_withFlags (next : Word) (g : Flags) (x : State) (memory : Memory) :
    retire next (some (({ x with flags := g } : State), memory)) =
      withFlagsR g (retire next (some (x, memory))) := rfl

theorem retire_map_fun_withFlags {α : Type} (next : Word) (g : Flags) (o : Option α)
    (F : α → State) (M : α → Memory) :
    retire next (o.map fun v => (({ F v with flags := g } : State), M v)) =
      withFlagsR g (retire next (o.map fun v => (F v, M v))) := by
  cases o <;> rfl

@[simp] theorem aluStep_withFlags (sz : Sz) (op : X86.AluOp) (dst : RM) (s : State) (g : Flags)
    (y : BitVec sz.bits) (memory : Memory) (next : Word) :
    aluStep sz op dst y ({ s with flags := g } : State) memory next = aluStep sz op dst y s memory next := by
  unfold aluStep
  rw [readRM_withFlags]
  cases readRM sz dst s memory next with
  | none => rfl
  | some x =>
    simp only [writeRM_withFlags, Option.map_map]
    split
    · rfl
    · rfl

@[simp] theorem aluStepR_withFlags (sz : Sz) (op : X86.AluOp) (dst : Reg) (src : RM) (s : State)
    (g : Flags) (memory : Memory) (next : Word) :
    aluStepR sz op dst src ({ s with flags := g } : State) memory next =
      aluStepR sz op dst src s memory next := by
  unfold aluStepR
  rw [readRM_withFlags]
  cases readRM sz src s memory next with
  | none => rfl
  | some y => rfl

/-- How an instruction uses the flags: not at all for its result (`overwrites`), only by
carrying them (`preserves`), or through a monotone function. -/
theorem exec_cases (i : Instr) :
    (∀ (s : State) g memory length,
      exec i ({ s with flags := g } : State) memory length = exec i s memory length) ∨
    (∀ (s : State) g memory length,
      exec i ({ s with flags := g } : State) memory length = withFlagsR g (exec i s memory length)) ∨
    (∃ sz dec dst, i = .incdec sz dec dst) ∨ (∃ sz op dst count, i = .shift sz op dst count) ∨
    (∃ sz c dst src, i = .cmov sz c dst src) ∨ (∃ c dst, i = .setcc c dst) ∨
    (∃ c rel, i = .jcc8 c rel) ∨ (∃ c rel, i = .jcc c rel) := by
  cases i
  case unary sz op dst =>
    cases op
    · left; intro s g memory length
      simp only [exec, readRM_withFlags, writeRM_withFlags, Option.map_map]
      cases readRM sz dst s memory _ <;> rfl
    · right; left; intro s g memory length
      simp only [exec, readRM_withFlags, writeRM_withFlags]
      cases readRM sz dst s memory _ with
      | none => rfl
      | some value => simp only [retire_map_withFlags]
  case cxe sz =>
    right; left; intro s g memory length
    cases sz <;> rfl
  case movI16 dst imm =>
    right; left; intro s g memory length
    cases dst with
    | reg r => rfl
    | mem m =>
      simp only [exec, addr_withFlags]
      cases storeN memory (m.addr s _) 2 (imm.setWidth 64) <;> rfl
  case mov8 dst src =>
    right; left; intro s g memory length
    simp only [exec, readNarrow_withFlags]
    cases readNarrow .b src s memory _ <;> rfl
  case pushRM src =>
    right; left; intro s g memory length
    simp only [exec, readRM_withFlags]
    cases readRM .q src s memory _ with
    | none => rfl
    | some v =>
      dsimp only
      exact (congrArg (retire _) (pushWord_withFlags s g memory v)).trans
        (retire_map_withFlags _ _ _)
  case call rel =>
    right; left; intro s g memory length
    simp only [exec, pushWord_withFlags]
    cases X86.pushWord s memory _ <;> rfl
  case ret =>
    right; left; intro s g memory length
    simp only [exec, popWord_withFlags]
    cases X86.popWord s memory <;> rfl
  case pop dst =>
    right; left; intro s g memory length
    simp only [exec, popWord_withFlags, Option.map_map]
    cases X86.popWord s memory <;> rfl
  case leave =>
    right; left; intro s g memory length
    simp only [exec, read_withFlags, write_withFlags, popWord_withFlags, Option.map_map]
    cases X86.popWord (s.write .rsp (s.read .rbp)) memory <;> rfl
  all_goals first
    | (right; right; simp; done)
    | (left; intro s g memory length; simp only [exec, readRM_withFlags, writeRM_withFlags,
        readNarrow_withFlags, writeNarrow_withFlags, writeRM8_withFlags, aluStep_withFlags,
        aluStepR_withFlags, szRead_withFlags, szWrite_withFlags, read_withFlags,
        addr_withFlags, retire_map_withFlags]; done)
    | (right; left; intro s g memory length; simp only [exec, readRM_withFlags, writeRM_withFlags,
        readNarrow_withFlags, writeNarrow_withFlags, writeRM8_withFlags,
        szRead_withFlags, szWrite_withFlags, read_withFlags,
        addr_withFlags, retire_map_withFlags, pushWord_withFlags,
        write_withFlags, retire_some_withFlags]
       first
        | done
        | rfl
        | rw [retire_map_fun_withFlags])

theorem retire_map_ok {α : Type} {next : Word} {o : Option α} {f : α → State × Memory}
    {s' : State} {memory' : Memory} (e : retire next (o.map f) = .ok s' memory') :
    ∃ r, o = some r ∧ retire next (some (f r)) = .ok s' memory' := by
  cases o with
  | none => cases e
  | some r => exact ⟨r, rfl, e⟩

theorem retire_some_ok {next : Word} {a : State} {m : Memory} {s' : State} {memory' : Memory}
    (e : retire next (some (a, m)) = .ok s' memory') : s' = { a with rip := next } ∧ memory' = m := by
  simp only [retire, Result.ok.injEq] at e
  exact ⟨e.1.symm, e.2.symm⟩

theorem coreLe_rip {a : State} {g : Flags} (next : Word) (h : FlagsLe a.flags g) :
    CoreLe { a with rip := next } { a with flags := g, rip := next } := ⟨rfl, h⟩

/-- **Flag monotonicity.** A core with more defined flags retires whenever the less defined
one does, to the same memory and a `CoreLe`-related core. -/
theorem exec_mono (i : Instr) {s t : State} (memory : Memory) (length : Nat) (h : CoreLe s t)
    {s' : State} {memory' : Memory} (e : exec i s memory length = .ok s' memory') :
    ∃ t', exec i t memory length = .ok t' memory' ∧ CoreLe s' t' := by
  obtain ⟨teq, hf⟩ := h
  rw [teq]
  generalize t.flags = g at hf
  rcases exec_cases i with same | keep | ⟨sz, dec, dst, rfl⟩ | ⟨sz, op, dst, count, rfl⟩ |
    ⟨sz, c, dst, src, rfl⟩ | ⟨c, dst, rfl⟩ | ⟨c, rel, rfl⟩ | ⟨c, rel, rfl⟩
  · rw [same]; exact ⟨s', e, .refl _⟩
  · rw [keep, e]
    refine ⟨_, rfl, rfl, ?_⟩
    have preserved := keep s s.flags memory length
    rw [show ({ s with flags := s.flags } : State) = s from rfl, e] at preserved
    simp only [withFlagsR, Result.ok.injEq] at preserved
    have flags : s'.flags = s.flags := by rw [preserved.1]
    rw [flags]; exact hf
  · simp only [exec, readRM_withFlags, writeRM_withFlags, Option.map_map] at e ⊢
    split at e
    · cases e
    · rename_i x hx
      try rw [hx]
      obtain ⟨⟨a, m⟩, hw, e⟩ := retire_map_ok e
      rw [hw]
      obtain ⟨rfl, rfl⟩ := retire_some_ok e
      simp only [Option.map_some, Function.comp_apply]
      refine ⟨_, rfl, rfl, ?_⟩
      cases dec
      · exact incFlagsN_mono x hf
      · exact decFlagsN_mono x hf
  · simp only [exec, readRM_withFlags, writeRM_withFlags, countRaw_withFlags, Option.map_map]
      at e ⊢
    split at e
    · cases e
    · rename_i x hx
      try rw [hx]
      obtain ⟨⟨a, m⟩, hw, e⟩ := retire_map_ok e
      rw [hw]
      obtain ⟨rfl, rfl⟩ := retire_some_ok e
      simp only [Option.map_some, Function.comp_apply]
      exact ⟨_, rfl, rfl, ShiftOp.flags_mono op x _ hf⟩
  · simp only [exec, readRM_withFlags, szRead_withFlags, szWrite_withFlags] at e ⊢
    split at e
    · cases e
    · rename_i value hv
      try rw [hv]
      split at e
      · cases e
      · rename_i taken ht
        rw [Cond.eval_mono_some hf c ht]
        obtain ⟨rfl, rfl⟩ := retire_some_ok e
        exact ⟨_, rfl, rfl, hf⟩
  · simp only [exec, writeRM8_withFlags] at e ⊢
    split at e
    · cases e
    · rename_i v hv
      rw [Cond.eval_mono_some hf c hv]
      obtain ⟨⟨a, m⟩, hw, e⟩ := retire_map_ok (o := writeRM8 dst _ s memory _) (f := id)
        (by simpa using e)
      dsimp only
      rw [hw]
      obtain ⟨rfl, rfl⟩ := retire_some_ok e
      refine ⟨_, rfl, rfl, ?_⟩
      have := writeRM8_withFlags s s.flags memory (s.rip + BitVec.ofNat 64 length) dst
        (if v then 1#8 else 0#8)
      rw [show ({ s with flags := s.flags } : State) = s from rfl, hw] at this
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      rw [this.1]; exact hf
  · simp only [exec] at e ⊢
    split at e
    · cases e
    · rename_i hv; rw [Cond.eval_mono_some hf c hv]
      simp only [Result.ok.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, rfl, rfl, hf⟩
    · rename_i hv; rw [Cond.eval_mono_some hf c hv]
      simp only [Result.ok.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, rfl, rfl, hf⟩
  · simp only [exec] at e ⊢
    split at e
    · cases e
    · rename_i hv; rw [Cond.eval_mono_some hf c hv]
      simp only [Result.ok.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, rfl, rfl, hf⟩
    · rename_i hv; rw [Cond.eval_mono_some hf c hv]
      simp only [Result.ok.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨_, rfl, rfl, hf⟩

end Silmaril.Process.LPS.Problems.Sha256Cli.FlagMono
