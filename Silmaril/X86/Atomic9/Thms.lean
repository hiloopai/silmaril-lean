module

public import Silmaril.X86.Atomic9.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Safe.Open9.Thms
import Silmaril.Proofs.X86.Atomic9.Decode
import Silmaril.Proofs.X86.Atomic9.Step
import Silmaril.Proofs.X86.Atomic9.Semantics
import Silmaril.Proofs.X86.Atomic9.Prefix

/-!
# `Atomic9`: what is proved

All statements are PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Atomic9/{Decode,Step,Semantics}.lean`); the decoder facts are
`decide`.

**Conservative extension.**
* `step_of_open9`: every `Open9` step is an `Atomic9` step. `run_of_open9`,
  `reaches_of_open9`: so is every `Open9` run.
* `step_cases`: every `Atomic9` step is such a step, or (when `Open9` has no step) an atomic
  form fetched at the program counter.
* `FnContract.toAtomic9`: every `FnContract Open9.isa` is a contract of `Atomic9.isa`.

**The listing laws.**
* `isa : SegVC.Isa MState` over `Atomic9.Instr` (`Ext9` forms and atomic forms) with the
  listing decoder `decode`; its law is `step_of_listed`.
* `step_of_fetch_new`, `step_of_listed_new`: a listed atomic form (`decodeL`) at the program
  counter that executes is one step.

**Semantics.**
* `lockOr_rsp_zero_fence`: gcc's SEQ_CST fence `f0 48 83 0c 24 00` (84 sites in sqlite-O2) is
  one step that changes only `rip` (by 6) and the flags (`or` of the stack word with 0); the
  memory is **equal** to the old one.
* `execNew_fence`, `execNew_pause`: they only advance `rip`.
* `tag_*`: the tags of the forms.

**Decoder facts (`decide`).**
* `decode_nop66`: `66 90` (`xchg ax,ax`, padding) still decodes as the `Ext` `nop`, and
  `decode` agrees with `Open9.decode` there.
* `sse9_opcodes_not_atomic`, `atomic_samples_listed`: **opcode disjointness with `Sse9`**.
  Every `Sse9` opcode (`0F xx`) with each legacy prefix (none, `66`, `F3`, `F2`, `F0`) and a
  register or memory ModRM is rejected by `decodeNew`; and one sample encoding of every
  atomic opcode is accepted by `decodeL`, rejected by `Sse9.decodeL` and by `Open9.decode`.
* `decodeL_*`: regressions on census encodings (and libc's short `xchg`).

What is **not** claimed: the semantics is a handwritten model of the SDM, tested against the
host CPU (`tools/ext9-difftest`, family `atomic9`), not proved to match hardware. It is a
sequential (SC, single-thread) model: the tags record what a TSO model will need, but nothing
here says anything about concurrent executions. No certificate kind (`Cert`, `BlockCert`,
Bir) has atomic blocks yet.
-/

@[expose] public section

namespace Silmaril.X86.Atomic9

open Silmaril.X86 (State MState Word Byte)
open Silmaril.X86.Ext (Loaded Mem)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)

/-! ## Conservative extension -/

/-- **Every `Open9` step is an `Atomic9` step.** -/
theorem step_of_open9 {m m' : MState} (h : Open9.step m = some m') : step m = some m' :=
  Silmaril.Proofs.X86.Atomic9.step_of_open9 h

/-- **Every step is an `Open9` step, or an atomic step.** -/
theorem step_cases {m m' : MState} (h : step m = some m') :
    Open9.step m = some m' ∨
      (Open9.step m = none ∧ ∃ i n, fetchNew m.memory m.core.rip.toNat = some (some (i, n)) ∧
        Open.ofResult (execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 n)) = some m') :=
  Silmaril.Proofs.X86.Atomic9.step_cases h

theorem run_of_open9 (k : Nat) {a b : MState} (h : run Open9.step k a = some b) :
    run step k a = some b :=
  Silmaril.Proofs.X86.Atomic9.run_of_open9 k h

theorem reaches_of_open9 {a b : MState} (h : Reaches Open9.step a b) : Reaches step a b :=
  Silmaril.Proofs.X86.Atomic9.reaches_of_open9 h

/-- Every open step is an `Atomic9` step. -/
theorem step_of_open {m m' : MState} (h : Open.step m = some m') : step m = some m' :=
  step_of_open9 (Open9.step_of_open h)

/-! ## The listing laws -/

/-- What a listed atomic form is. -/
theorem decodeL_spec {bytes : List Byte} {i : New} {n : Nat} (h : decodeL bytes = some (i, n)) :
    Silmaril.X86.Ext.decode bytes = none ∧ Open9.newBad bytes = true ∧
      Open9.rawNotEof bytes = true ∧ Sse9.ext9Bad bytes = true ∧ decodeNew bytes = some (i, n) ∧
      0 < n ∧ n ≤ Silmaril.X86.maxInstrLength :=
  Silmaril.Proofs.X86.Atomic9.decodeL_spec h

/-- **The listing decoder is prefix-stable**: a reading of `decode` survives any
bytes appended to the window. Every layer is (`Ext.decode` reads canonical encodings; the
new-form parsers of `Ext8`, `Ext9` and `Atomic9` have the `Good` prefix laws), and the side
conditions of the listing decoders (`Ext.decode = none`, `newBad`, `rawNotEof`, `ext9Bad`) make
the earlier layers' failures persist. -/
theorem decode_append {w : List Byte} {i : Instr} {n : Nat} (h : decode w = some (i, n))
    (more : List Byte) : decode (w ++ more) = some (i, n) :=
  Silmaril.Proofs.X86.Atomic9.decode_append h more

/-- Nothing decodes from no bytes. -/
theorem decode_nil : decode [] = none := Silmaril.Proofs.X86.Atomic9.decode_nil

/-- A decoded atomic form keeps its reading whatever bytes follow. -/
theorem decodeNew_append {bytes : List Byte} {i : New} {n : Nat}
    (h : decodeNew bytes = some (i, n)) (more : List Byte) :
    decodeNew (bytes ++ more) = some (i, n) :=
  Silmaril.Proofs.X86.Atomic9.decodeNew_append h more

/-- **The fetch form of the atomic law.** -/
theorem step_of_fetch_new {m : MState} {l : Nat} {w : List Byte} {i : New} {c : State}
    {mem : Memory} (fetched : m.memory.fetchBytes m.core.rip.toNat l = some w)
    (hdec : decodeL w = some (i, l))
    (hx : execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Atomic9.step_of_fetch_new fetched hdec hx

/-- **The atomic listing law.** -/
theorem step_of_listed_new {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : New}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decodeL ((code.drop o).take l) = some (i, l))
    (hx : execNew i m.core m.memory (m.core.rip + BitVec.ofNat 64 l) = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Atomic9.step_of_listed_new hl hrip hfit hdec hx

/-- **The listing law of the machine.** -/
theorem step_of_listed {m : MState} {base : Word} {code : List Byte} {o l : Nat} {i : Instr}
    {c : State} {mem : Memory} (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (hfit : o + l ≤ code.length)
    (hdec : decode ((code.drop o).take l) = some (i, l))
    (hx : exec i m.core m.memory l = .ok c mem) :
    step m = some ⟨c, mem⟩ :=
  Silmaril.Proofs.X86.Atomic9.step_of_listed hl hrip hfit hdec hx

/-- **The atomic machine as a segment-VC instance**, over `Ext9` and the atomic forms. -/
@[reducible] def isa : Silmaril.X86.SegVC.Isa MState where
  Instr := Instr
  instDecEq := inferInstance
  decode := decode
  exec := exec
  core := MState.core
  mem := MState.memory
  upd := fun _ c m => ⟨c, m⟩
  core_upd := fun _ _ _ => rfl
  mem_upd := fun _ _ _ => rfl
  upd_self := fun _ => rfl
  ok := fun _ _ => True
  live := fun _ => True
  step := step
  live_step := fun _ _ => trivial
  step_of := fun _ hl hrip hfit hdec hx _ => step_of_listed hl hrip hfit hdec hx

@[simp] theorem isa_step : isa.step = step := rfl

/-! ## Semantics -/

/-- The SQLite fence `f0 48 83 0c 24 00` is `lock or qword ptr [rsp], 0`. -/
theorem decodeL_lockOr_rsp :
    decodeL [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00] =
      some (.lockAluI .q .or (Ext.Mem.ofReg .rsp none 0) 0, 6) :=
  Silmaril.Proofs.X86.Atomic9.decodeL_lockOr_rsp

/-- **gcc's SEQ_CST fence `lock or qword ptr [rsp], 0` changes only `rip` and the flags**;
memory is unchanged. The stack word must be readable and writable (a locked RMW writes). -/
theorem lockOr_rsp_zero_fence {m : MState} {bs : List Byte}
    (hf : m.memory.fetchBytes m.core.rip.toNat 6 = some [0xf0, 0x48, 0x83, 0x0c, 0x24, 0x00])
    (hr : m.memory.readBytes (m.core.read .rsp).toNat 8 = some bs)
    (hw : m.memory.Permitted .write (m.core.read .rsp).toNat 8) :
    step m = some ⟨{ m.core with
        rip := m.core.rip + BitVec.ofNat 64 6
        flags := Silmaril.X86.Ext.AluOp.flagsN .or (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue bs))
          0#64 },
      m.memory⟩ :=
  Silmaril.Proofs.X86.Atomic9.lockOr_rsp_zero_fence hf hr hw

/-- Storing the 8-byte value just loaded leaves memory equal. -/
theorem storeN_self {memory : Memory} {a : Word} {bs : List Byte}
    (hr : memory.readBytes a.toNat 8 = some bs) (hw : memory.Permitted .write a.toNat 8) :
    Silmaril.X86.Ext.storeN memory a 8 (BitVec.ofNat 64 (Silmaril.X86.Ext.leValue bs)) =
      some memory :=
  Silmaril.Proofs.X86.Atomic9.storeN_self hr hw

/-- A fence only advances `rip`. -/
theorem execNew_fence (k : FenceKind) (s : State) (memory : Memory) (next : Word) :
    execNew (.fence k) s memory next = .ok { s with rip := next } memory := rfl

/-- `pause` only advances `rip`. -/
theorem execNew_pause (s : State) (memory : Memory) (next : Word) :
    execNew .pause s memory next = .ok { s with rip := next } memory := rfl

/-! ## Tags -/

/-- The SQLite fence is a locked access and no explicit fence. -/
theorem tag_lockOr : tag (.lockAluI .q .or (Ext.Mem.ofReg .rsp none 0) 0) = ⟨true, none⟩ := rfl

/-- Every `lock`-prefixed RMW form is locked. -/
theorem tag_lockAlu (sz : Silmaril.X86.Ext.Sz) (op : Silmaril.X86.AluOp) (d : Ext.Mem)
    (r : Silmaril.X86.Reg) : (tag (.lockAlu sz op d r)).locked = true := rfl

/-- `cmpxchg`/`xadd` are locked exactly when prefixed. -/
theorem tag_cmpxchg (sz : Silmaril.X86.Ext.Sz) (l : Bool) (d : Silmaril.X86.Ext.RM)
    (r : Silmaril.X86.Reg) : tag (.cmpxchg sz l d r) = ⟨l, none⟩ := rfl

theorem tag_xadd (sz : Silmaril.X86.Ext.Sz) (l : Bool) (d : Silmaril.X86.Ext.RM)
    (r : Silmaril.X86.Reg) : tag (.xadd sz l d r) = ⟨l, none⟩ := rfl

/-- `xchg` with a memory operand is implicitly locked (SDM Vol. 3A §9.1.2.1). -/
theorem tag_xchg_mem (sz : Silmaril.X86.Ext.Sz) (m : Ext.Mem) (r : Silmaril.X86.Reg) :
    tag (.xchg sz (.mem m) r) = ⟨true, none⟩ := rfl

/-- `xchg` between registers is not a memory access. -/
theorem tag_xchg_reg (sz : Silmaril.X86.Ext.Sz) (d r : Silmaril.X86.Reg) :
    tag (.xchg sz (.reg d) r) = ⟨false, none⟩ := rfl

/-- A fence carries its kind and is not locked. -/
theorem tag_fence (k : FenceKind) : tag (.fence k) = ⟨false, some k⟩ := rfl

theorem tag_pause : tag .pause = ⟨false, none⟩ := rfl

/-! ## Decoder facts -/

/-- `66 90` (`xchg ax,ax`, the padding `nop`) is unchanged: the `Ext` two-byte `nop`, as in
`Open9.decode`. -/
theorem decode_nop66 :
    decode [0x66, 0x90] = some (.open9 (.ext8 (.base (.nop 1))), 2) ∧
      Open9.decode [0x66, 0x90] = some (.ext8 (.base (.nop 1)), 2) := by
  decide

/-- `90` (`nop`) is unchanged too. -/
theorem decode_nop : decode [0x90] = some (.open9 (.ext8 (.base (.nop 0))), 1) := by decide

/-- **No `Sse9` opcode is an atomic form**: each `0F xx` of `Sse9`'s table, with no legacy
prefix or with `66`, `F3`, `F2` or `F0`, and a register (`C0`) or memory (`00`, `[rax]`)
ModRM, is rejected by `decodeNew` (and so by `decodeL` and `fetchNew`). -/
theorem sse9_opcodes_not_atomic :
    ([[], [0x66], [0xF3], [0xF2], [0xF0]] : List (List Byte)).all (fun p =>
      sse9Opcodes.all fun op =>
        (decodeNew (p ++ [0x0F, op, 0xC0])).isNone && (decodeNew (p ++ [0x0F, op, 0x00])).isNone)
      = true := by
  decide

/-- One sample encoding of every atomic opcode (register and memory operands where both
exist). -/
def atomicSamples : List (List Byte) :=
  [ [0xF0, 0x01, 0x07], [0xF0, 0x48, 0x09, 0x07], [0xF0, 0x21, 0x07], [0xF0, 0x29, 0x07],
    [0xF0, 0x31, 0x07], [0xF0, 0x81, 0x07, 1, 0, 0, 0], [0xF0, 0x48, 0x83, 0x0c, 0x24, 0x00],
    [0xF0, 0x80, 0x0F, 0x01], [0xF0, 0xFF, 0x07], [0xF0, 0x48, 0xFF, 0x0F],
    [0xF0, 0x48, 0x0F, 0xBA, 0x2F, 0x03], [0x87, 0x07], [0x48, 0x87, 0xD8], [0xF0, 0x87, 0x07],
    [0x86, 0x07], [0x86, 0xC4], [0x0F, 0xC1, 0x07], [0xF0, 0x48, 0x0F, 0xC1, 0x07],
    [0x0F, 0xC1, 0xC8], [0x0F, 0xB1, 0x0A], [0xF0, 0x48, 0x0F, 0xB1, 0x0A], [0x0F, 0xB1, 0xCA],
    [0xF0, 0x0F, 0xB0, 0x0A], [0x0F, 0xB0, 0xCA], [0x0F, 0xAE, 0xF0], [0x0F, 0xAE, 0xE8],
    [0x0F, 0xAE, 0xF8], [0xF3, 0x90], [0x91], [0x48, 0x97], [0x41, 0x90], [0x49, 0x92] ]

/-- **Every atomic opcode is a listed atomic form, and neither `Sse9` nor `Open9` reads
it.** -/
theorem atomic_samples_listed :
    atomicSamples.all (fun bs =>
      (decodeL bs).isSome && (Sse9.decodeL bs).isNone && (Open9.decode bs).isNone) = true := by
  decide

/-- `lock` on a register destination, `lock cmp`, a repeated `F0`, the FS override and `66`
are rejected. -/
theorem decodeL_rejects :
    decodeL [0xF0, 0x01, 0xC0] = none ∧ decodeL [0xF0, 0x83, 0x3F, 0x01] = none ∧
      decodeL [0xF0, 0xF0, 0x01, 0x07] = none ∧ decodeL [0x64, 0xF0, 0x01, 0x07] = none ∧
      decodeL [0xF0, 0x64, 0x01, 0x07] = none ∧ decodeL [0x66, 0xF0, 0x01, 0x07] = none ∧
      decodeL [0xF0, 0x66, 0x01, 0x07] = none ∧ decodeL [0x0F, 0xAE, 0x00] = none := by
  decide

/-- `xchg rbx, r13` (`49 87 dd`, the one register `xchg` in sqlite-O2). -/
theorem decodeL_xchg_rbx_r13 :
    decodeL [0x49, 0x87, 0xDD] = some (.xchg .q (.reg .r13) .rbx, 3) := by decide

/-- The short `xchg`: `91` is `xchg ecx, eax`, `49 90` is `xchg r8, rax`; `48 90` (no REX.B)
is not read. -/
theorem decodeL_xchg_short :
    decodeL [0x91] = some (.xchg .d (.reg .rcx) .rax, 1) ∧
      decodeL [0x49, 0x90] = some (.xchg .q (.reg .r8) .rax, 2) ∧
      decodeL [0x48, 0x90] = none ∧ decodeL [0xF0, 0x91] = none := by
  decide

/-- `lock cmpxchg qword ptr [rdx], rcx` (`f0 48 0f b1 0a`). -/
theorem decodeL_lock_cmpxchg :
    decodeL [0xF0, 0x48, 0x0F, 0xB1, 0x0A] =
      some (.cmpxchg .q true (.mem (Ext.Mem.ofReg .rdx none 0)) .rcx, 5) := by decide

/-- `mfence` (`0f ae f0`). -/
theorem decodeL_mfence : decodeL [0x0F, 0xAE, 0xF0] = some (.fence .mfence, 3) := by decide

/-- `pause` (`f3 90`). -/
theorem decodeL_pause : decodeL [0xF3, 0x90] = some (.pause, 2) := by decide

end Silmaril.X86.Atomic9

namespace Silmaril.X86.FnContract

/-- A total spec on the `Ext9` open machine is total on the atomic one. -/
theorem Spec.Total.toAtomic9 {S : Spec Silmaril.X86.MState} (h : S.Total Open9.isa) :
    S.Total Atomic9.isa :=
  fun s hl ha he => by
    obtain ⟨t, hr, res⟩ := h s hl ha he
    exact ⟨t, Atomic9.reaches_of_open9 hr, res.silent, res.abi, res.frame, res.post⟩

/-- **Every `Open9` contract is an `Atomic9` contract**, with the same spec. -/
def toAtomic9 (C : FnContract Open9.isa) : FnContract Atomic9.isa :=
  ⟨C.toSpec, C.total.toAtomic9⟩

@[simp] theorem toAtomic9_toSpec (C : FnContract Open9.isa) : C.toAtomic9.toSpec = C.toSpec :=
  rfl

end Silmaril.X86.FnContract
