module

public import Silmaril.X86.Sep.Ind.Defs
public import Silmaril.X86.Open9.Thms
public import Silmaril.X86.Safe.Thms
import Silmaril.Proofs.X86.Sep.Ind
import Silmaril.Proofs.X86.Sep.Ind.Witness

/-!
# Indirect `call`/`jmp` step laws

* Decoding through `Open9.decode`, for every register and every `disp8`: `decode_encCallR`,
  `decode_encCallM`, `decode_encJmpR`, `decode_encJmpM`. The concrete gcc encodings
  `FF D0` (`call *%rax`), `FF 53 08` (`call *0x8(%rbx)`) and `FF 67 38` (`jmp *0x38(%rdi)`)
  are checked by `decide` against both the encoders and `Open9.decode`.
* Generic laws on `Open9.isa` for any operand: `callInd_progress`, `jmpInd_progress`, and a
  one-step `Progress` from a local step on any machine, `progress_of_local`.
* **The step laws** on every machine `I` with `E : Open9.isa.Extends I` (pass
  `Isa.Extends.refl _` or `Str9.extendsOpen9`), as `Progress` (one step at least):
  `callR_progress` (`call *%r`), `callM_progress` (`call *d8(%base)`), `jmpR_progress`
  (`jmp *%r`) and `jmpM_progress` (`jmp *d8(%base)`).
* **Non-vacuity**: `jmpM_nonvacuous`, `callM_nonvacuous`: concrete states meet the
  preconditions of the memory forms and `Open9` reaches the target.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Ind

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.X86.Ext (RM Mem readRM)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Process (Permissions)
open Silmaril.X86.Safe (Progress)
open Silmaril.X86.Sep.Frag (Le)

variable {σ : Type} {I : Isa σ}

/-! ## Decoding -/

theorem decode_encCallR (r : Reg) :
    Open9.decode (encCallR r) = some (.new (.callInd (.reg r)), (encCallR r).length) :=
  Silmaril.Proofs.X86.Sep.Ind.decode_encCallR r

theorem decode_encJmpR (r : Reg) :
    Open9.decode (encJmpR r) = some (.new (.jmpInd (.reg r)), (encJmpR r).length) :=
  Silmaril.Proofs.X86.Sep.Ind.decode_encJmpR r

theorem decode_encCallM (base : Reg) (d : BitVec 8) :
    Open9.decode (encCallM base d) =
      some (.new (.callInd (memOp base d)), (encCallM base d).length) :=
  Silmaril.Proofs.X86.Sep.Ind.decode_encCallM base d

theorem decode_encJmpM (base : Reg) (d : BitVec 8) :
    Open9.decode (encJmpM base d) =
      some (.new (.jmpInd (memOp base d)), (encJmpM base d).length) :=
  Silmaril.Proofs.X86.Sep.Ind.decode_encJmpM base d

/-! ### Concrete encodings -/

/-- `call *%rax` is `FF D0`. -/
theorem encCallR_rax : encCallR .rax = [0xFF#8, 0xD0#8] := by decide
/-- `call *0x8(%rbx)` is `FF 53 08`. -/
theorem encCallM_rbx_8 : encCallM .rbx 0x08#8 = [0xFF#8, 0x53#8, 0x08#8] := by decide
/-- `jmp *0x38(%rdi)` is `FF 67 38`. -/
theorem encJmpM_rdi_38 : encJmpM .rdi 0x38#8 = [0xFF#8, 0x67#8, 0x38#8] := by decide

theorem decode_FF_D0 :
    Open9.decode [0xFF#8, 0xD0#8] = some (.new (.callInd (.reg .rax)), 2) := by decide
theorem decode_FF_53_08 :
    Open9.decode [0xFF#8, 0x53#8, 0x08#8] = some (.new (.callInd (memOp .rbx 0x08#8)), 3) := by
  decide
theorem decode_FF_67_38 :
    Open9.decode [0xFF#8, 0x67#8, 0x38#8] = some (.new (.jmpInd (memOp .rdi 0x38#8)), 3) := by
  decide

/-! ## Generic laws on `Open9` -/

/-- **`call r/m64` on `Open9`** for any operand whose value `X` pins to `p`. -/
theorem callInd_progress {X : SProp} {bs : List Byte} {op : RM} {pc s p : Word}
    (hs : 8 ≤ s.toNat) (hne : bs ≠ [])
    (hdec : Open9.decode bs = some (.new (.callInd op), bs.length))
    (hread : ∀ (m : MState) hx, X hx → Le hx (toFrag m) → ∀ next,
      readRM .q op m.core m.memory next = some p) :
    Progress Open9.isa
      (codePt pc.toNat bs ∗ ripPt pc ∗ X ∗ regPt .rsp s ∗ blockAny (s.toNat - 8) 8)
      (codePt pc.toNat bs ∗ ripPt p ∗ X ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc bs)) :=
  Silmaril.Proofs.X86.Sep.Ind.callInd_progress hs hne hdec hread

/-- **`jmp r/m64` on `Open9`** for any operand whose value `X` pins to `p`. -/
theorem jmpInd_progress {X : SProp} {bs : List Byte} {op : RM} {pc p : Word}
    (hne : bs ≠ [])
    (hdec : Open9.decode bs = some (.new (.jmpInd op), bs.length))
    (hread : ∀ (m : MState) hx, X hx → Le hx (toFrag m) → ∀ next,
      readRM .q op m.core m.memory next = some p) :
    Progress Open9.isa (codePt pc.toNat bs ∗ ripPt pc ∗ X)
      (codePt pc.toNat bs ∗ ripPt p ∗ X) :=
  Silmaril.Proofs.X86.Sep.Ind.jmpInd_progress hne hdec hread

/-- A one-step `Progress` from a local step, on any machine. -/
theorem progress_of_local {P Q : SProp}
    (h : ∀ m h₁, I.live m → P h₁ → Le h₁ (frag I m) →
      ∃ m', I.step m = some m' ∧ (∀ l, h₁ l = none → frag I m' l = frag I m l) ∧
        Q (Frag.reval h₁ (frag I m'))) :
    Progress I P Q :=
  Silmaril.Proofs.X86.Sep.Ind.progress_of_local h

/-! ## The step laws -/

/-- **`call *%r`**: push the address of the next instruction and jump to `r`. -/
theorem callR_progress (E : Open9.isa.Extends I) (r : Reg) (pc s p : Word)
    (hs : 8 ≤ s.toNat) :
    Progress I
      (codePt pc.toNat (encCallR r) ∗ ripPt pc ∗ regPt r p ∗ regPt .rsp s ∗
        blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (encCallR r) ∗ ripPt p ∗ regPt r p ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc (encCallR r))) :=
  (Silmaril.Proofs.X86.Sep.Ind.callR_open9 r pc s p hs).lift E

/-- **`call *d(%base)`** (method tables, `strm->zalloc`): the target is read before the
push. -/
theorem callM_progress (E : Open9.isa.Extends I) {need : Permissions → Prop}
    (hneed : ∀ q, need q → RO q) (base : Reg) (d : BitVec 8) (pc s v p : Word)
    (hs : 8 ≤ s.toNat) :
    Progress I
      (codePt pc.toNat (encCallM base d) ∗ ripPt pc ∗ regPt base v ∗
        wordAt need (ea v d).toNat p ∗ regPt .rsp s ∗ blockAny (s.toNat - 8) 8)
      (codePt pc.toNat (encCallM base d) ∗ ripPt p ∗ regPt base v ∗
        wordAt need (ea v d).toNat p ∗ regPt .rsp (s - 8#64) ∗
        wordPt (s.toNat - 8) (nextPc pc (encCallM base d))) :=
  (Silmaril.Proofs.X86.Sep.Ind.callM_open9 hneed base d pc s v p hs).lift E

/-- **`jmp *%r`** (tail calls). -/
theorem jmpR_progress (E : Open9.isa.Extends I) (r : Reg) (pc p : Word) :
    Progress I (codePt pc.toNat (encJmpR r) ∗ ripPt pc ∗ regPt r p)
      (codePt pc.toNat (encJmpR r) ∗ ripPt p ∗ regPt r p) :=
  (Silmaril.Proofs.X86.Sep.Ind.jmpR_open9 r pc p).lift E

/-- **`jmp *d(%base)`** (`jmp *0x38(%rdi)` in `longjmp`). -/
theorem jmpM_progress (E : Open9.isa.Extends I) {need : Permissions → Prop}
    (hneed : ∀ q, need q → RO q) (base : Reg) (d : BitVec 8) (pc v p : Word) :
    Progress I
      (codePt pc.toNat (encJmpM base d) ∗ ripPt pc ∗ regPt base v ∗ wordAt need (ea v d).toNat p)
      (codePt pc.toNat (encJmpM base d) ∗ ripPt p ∗ regPt base v ∗
        wordAt need (ea v d).toNat p) :=
  (Silmaril.Proofs.X86.Sep.Ind.jmpM_open9 hneed base d pc v p).lift E

/-! ## Non-vacuity -/

/-- **The `jmp *d8(%base)` law is not vacuous**: a concrete state meets its precondition for
`jmp *0x38(%rdi)` (`rdi = 0x6000`, the word `0x405678` at `0x6038`), and `Open9` reaches
`rip = 0x405678`. -/
theorem jmpM_nonvacuous : ∃ m : MState,
    (∃ h, (codePt (0x400000 : Word).toNat (encJmpM .rdi 0x38#8) ∗ ripPt 0x400000 ∗
      regPt .rdi 0x6000 ∗ wordAt RO (ea 0x6000 0x38#8).toNat 0x405678) h ∧
      Le h (toFrag m)) ∧
    ∃ k m', Silmaril.Machine.Execution.run Open9.step (k + 1)
      m = some m' ∧ m'.core.rip = 0x405678 :=
  ⟨_, Silmaril.Proofs.X86.Sep.Ind.Witness.jmpM_pre,
    Silmaril.Proofs.X86.Sep.Ind.Witness.jmpM_run⟩

/-- **The `call *d8(%base)` law is not vacuous**: a concrete state meets its precondition for
`call *0x8(%rbx)` (`rbx = 0x6000`, the word `0x401234` at `0x6008`, `rsp = 0x7000`), and
`Open9` reaches `rip = 0x401234`, `rsp = 0x6ff8`, with the return address `0x400003` at
`0x6ff8`. -/
theorem callM_nonvacuous : ∃ m : MState,
    (∃ h, (codePt (0x400000 : Word).toNat (encCallM .rbx 0x08#8) ∗ ripPt 0x400000 ∗
      regPt .rbx 0x6000 ∗ wordAt RO (ea 0x6000 0x08#8).toNat 0x401234 ∗ regPt .rsp 0x7000 ∗
      blockAny ((0x7000 : Word).toNat - 8) 8) h ∧
      Le h (toFrag m)) ∧
    ∃ k m', Silmaril.Machine.Execution.run Open9.step (k + 1)
      m = some m' ∧ m'.core.rip = 0x401234 ∧
      m'.core.read .rsp = 0x6ff8 ∧ ∀ i (hi : i < 8), m'.memory.bytes.get? (0x6ff8 + i) =
        some (Silmaril.Machine.LittleEndian.encodeWords [0x400003])[i] :=
  ⟨_, Silmaril.Proofs.X86.Sep.Ind.Witness.callM_pre,
    Silmaril.Proofs.X86.Sep.Ind.Witness.callM_run⟩

end Silmaril.X86.Sep.Ind
