module

public import Silmaril.X86.Sep.Insn.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.X86.Ext.SymExec
import Silmaril.Proofs.X86.Sep.Insn

/-!
# Single-instruction triples for `X86.Ext` forms

Total triples for register, flag, branch and memory forms of `X86.Ext`, proved on `Open.isa`
and stated on every machine `I` with `E : Open.isa.Extends I` (pass `Isa.Extends.refl _`,
`Open9.extendsOpen` or `Str9.extendsOpen`):

| triple | form |
| --- | --- |
| `movI32_step` | `mov $imm32, %r32` |
| `movD_step` | `mov %src32, %dst32` (zero-extending) |
| `xorSelf_step`, `xorSelf_any` | `xor %r32, %r32` |
| `testSelf_step` | `test %r32, %r32` (flags `testFlags v`) |
| `jcc8_step`, `jcc8_taken`, `jcc8_not_taken` | `jcc rel8` on owned flags |
| `storeQ_step` | `mov %src, disp(%base)` (into an owned eight-byte block) |
| `loadQ_step` | `mov disp(%base), %dst` (of an owned word) |
| `leaQ_step` | `lea disp(%base), %dst` |

**Building more.** `insn_triple` is the generic form: an open step from every state whose
`rip` is `pc` and whose memory holds the instruction, that leaves every location outside the
operands' fragment and `rip` unchanged and re-values the fragment into `Y`, is a triple that
returns the code. `open_of_ext` gives that open step from an `Ext` step of a loaded
instruction (`len_of_dec`, `ne_nil_of_dec` read the decoder). The fragment helpers
(`union_none`, `two_regs`, `toFrag_write_other`, `regPt_frag`, …) discharge its frame and
re-valuation conditions; `loadN_of_wordPt` reads an owned word.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Insn

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Mem Sz)
open Silmaril.Process (Memory)
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

variable {σ : Type} {I : Isa σ}

/-! ## Fragment helpers -/

theorem union_none {a b : Frag} {l : Loc} (h : union a b l = none) : a l = none ∧ b l = none :=
  Silmaril.Proofs.X86.Sep.Insn.union_none h

theorem reval_agree {h s s' : Frag} (hl : Le h s) (hag : ∀ l, (h l).isSome → s' l = s l) :
    reval h s' = h :=
  Silmaril.Proofs.X86.Sep.Insn.reval_agree hl hag

theorem isSome_of_disjoint {a b : Frag} (hd : Disjoint a b) {l : Loc} (hb : (b l).isSome) :
    a l = none :=
  Silmaril.Proofs.X86.Sep.Insn.isSome_of_disjoint hd hb

theorem single_none {l l' : Loc} {v : Val} (h : Frag.single l v l' = none) : l' ≠ l :=
  Silmaril.Proofs.X86.Sep.Insn.single_none h

theorem regPt_frag {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) :
    h = Frag.single (.reg r) (.word v) :=
  Silmaril.Proofs.X86.Sep.Insn.regPt_frag hp

theorem flagsAny_reval_exact {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsPt m.core.flags (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.Insn.flagsAny_reval_exact m hp

theorem flagsPt_reval {f : Flags} {h : Frag} (m : MState) (hp : flagsPt f h) :
    flagsPt m.core.flags (reval h (toFrag m)) :=
  Silmaril.Proofs.X86.Sep.Insn.flagsPt_reval m hp

/-- Locations other than `rip`, register `r` and the flags agree after a register write. -/
theorem toFrag_write_other {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) (hf : c.flags = m.core.flags) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l :=
  Silmaril.Proofs.X86.Sep.Insn.toFrag_write_other hc hf h1 h2

/-- Same, also allowing the flags to change. -/
theorem toFrag_write_other' {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) (h3 : l ≠ .flags) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l :=
  Silmaril.Proofs.X86.Sep.Insn.toFrag_write_other' hc h1 h2 h3

/-- Only `rip` and the flags change. -/
theorem toFrag_flags_other {m : MState} {c : State} (hc : ∀ q, c.read q = m.core.read q) {l : Loc}
    (h1 : l ≠ .rip) (h3 : l ≠ .flags) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l :=
  Silmaril.Proofs.X86.Sep.Insn.toFrag_flags_other hc h1 h3

/-- Two register atoms, read back. -/
theorem two_regs {m : MState} {hX : Frag} {r₁ : Reg} {v₁ : Word} {Q : SProp}
    (hXP : (regPt r₁ v₁ ∗ Q) hX) (hlX : Le hX (toFrag m)) :
    ∃ h₁ h₂, Disjoint h₁ h₂ ∧ hX = union h₁ h₂ ∧ regPt r₁ v₁ h₁ ∧ Q h₂ ∧ Le h₂ (toFrag m) ∧
      m.core.read r₁ = v₁ :=
  Silmaril.Proofs.X86.Sep.Insn.two_regs hXP hlX

/-- A byte-list atom owns memory locations only. -/
theorem bytesAt_nonmem {need : Silmaril.Process.Permissions → Prop} {a : Nat} {bs : List Byte}
    {h : Frag} (hp : bytesAt need a bs h) (l : Loc) (hl : ∀ x, l ≠ .mem x) : h l = none :=
  Silmaril.Proofs.X86.Sep.Insn.bytesAt_nonmem hp l hl

/-! ## Building instruction triples -/

/-- **A generic single-instruction triple.** -/
theorem insn_triple (E : Open.isa.Extends I)
    {pc pc' : Word} {bytes : List Byte} {X Y : SProp} (hne : bytes ≠ [])
    (h : ∀ (m : MState) (hX : Frag), X hX → Le hX (toFrag m) → m.core.rip = pc →
      Silmaril.X86.Ext.Loaded m.memory pc bytes →
      ∃ m', Silmaril.X86.Open.step m = some m' ∧ m'.core.rip = pc' ∧
        (∀ l, l ≠ .rip → hX l = none → toFrag m' l = toFrag m l) ∧
        Y (reval hX (toFrag m'))) :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ X) (codePt pc.toNat bytes ∗ ripPt pc' ∗ Y) :=
  (Silmaril.Proofs.X86.Sep.Insn.insn_triple hne h).lift E

/-- An `Ext` step from a loaded instruction is an open step. -/
theorem open_of_ext {m : MState} {pc : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    {core : State} {memory : Memory} (hl : Silmaril.X86.Ext.Loaded m.memory pc bytes)
    (hrip : m.core.rip = pc) (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length))
    (hnr : i ≠ .ret) (hx : Silmaril.X86.Ext.exec i m.core m.memory = .ok core memory) :
    Silmaril.X86.Open.step m = some ⟨core, memory⟩ :=
  Silmaril.Proofs.X86.Sep.Insn.open_of_ext hl hrip hdec hnr hx

theorem len_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) : i.length = bytes.length :=
  Silmaril.Proofs.X86.Sep.Insn.len_of_dec hdec

theorem ne_nil_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, n)) : bytes ≠ [] :=
  Silmaril.Proofs.X86.Sep.Insn.ne_nil_of_dec hdec

theorem memAt_addr (base : Reg) (disp : BitVec 32) (s : State) (next : Word) :
    (memAt base disp).addr s next = s.read base + disp.signExtend 64 :=
  Silmaril.Proofs.X86.Sep.Insn.memAt_addr base disp s next

/-- An owned word, read by an eight-byte load. -/
theorem loadN_of_wordPt {a : Nat} {w : Word} {h : Frag} {m : MState} {A : Word}
    (hA : A.toNat = a) (hp : wordPt a w h) (hl : Le h (toFrag m)) :
    Silmaril.X86.Ext.loadN m.memory A 8 = some w :=
  Silmaril.Proofs.X86.Sep.Insn.loadN_of_wordPt hA hp hl

/-! ## Register forms -/

/-- **`mov $imm32, %r32`.** -/
theorem movI32_step (E : Open.isa.Extends I)
    {pc pc' : Word} {bytes : List Byte} {r : Reg} {imm : BitVec 32}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.movI32 r imm, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r (imm.setWidth 64)) :=
  (Silmaril.Proofs.X86.Sep.Insn.movI32_step hdec hnext).lift E

/-- **`mov %src32, %dst32`** (zero-extending). -/
theorem movD_step (E : Open.isa.Extends I)
    {pc pc' v : Word} {bytes : List Byte} {dst src : Reg} (hne : dst ≠ src)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.mov .d (.reg dst) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt src v ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt src v ∗
        regPt dst ((v.setWidth 32).setWidth 64)) :=
  (Silmaril.Proofs.X86.Sep.Insn.movD_step hne hdec hnext).lift E

/-- **`xor %r32, %r32`**: zero the register. -/
theorem xorSelf_step (E : Open.isa.Extends I)
    {pc pc' v : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.alu .d .xor (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r 0 ∗ flagsAny) :=
  (Silmaril.Proofs.X86.Sep.Insn.xorSelf_step hdec hnext).lift E

/-- **`xor %r32, %r32`** from an unknown value. -/
theorem xorSelf_any (E : Open.isa.Extends I)
    {pc pc' : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.alu .d .xor (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r 0 ∗ flagsAny) :=
  (Silmaril.Proofs.X86.Sep.Insn.xorSelf_any hdec hnext).lift E

/-! ## Flags and branches -/

/-- **`test %r32, %r32`.** -/
theorem testSelf_step (E : Open.isa.Extends I)
    {pc pc' v : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.test .d (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r v ∗ flagsPt (testFlags v)) :=
  (Silmaril.Proofs.X86.Sep.Insn.testSelf_step hdec hnext).lift E

/-- **`jcc rel8`** on owned flags whose condition is defined. -/
theorem jcc8_step (E : Open.isa.Extends I)
    {pc : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    {f : Flags} {b : Bool} (hev : c.eval f = some b)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length)) :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗
        ripPt (if b then pc + BitVec.ofNat 64 bytes.length + rel.signExtend 64
          else pc + BitVec.ofNat 64 bytes.length) ∗ flagsPt f) :=
  (Silmaril.Proofs.X86.Sep.Insn.jcc8_step hev hdec).lift E

/-- A taken `jcc rel8`. -/
theorem jcc8_taken (E : Open.isa.Extends I)
    {pc pc' : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond}
    {rel : BitVec 8} {f : Flags} (hev : c.eval f = some true)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length))
    (hpc : pc + BitVec.ofNat 64 bytes.length + rel.signExtend 64 = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ flagsPt f) :=
  (Silmaril.Proofs.X86.Sep.Insn.jcc8_taken hev hdec hpc).lift E

/-- A `jcc rel8` that falls through. -/
theorem jcc8_not_taken (E : Open.isa.Extends I)
    {pc pc' : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond}
    {rel : BitVec 8} {f : Flags} (hev : c.eval f = some false)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length))
    (hpc : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ flagsPt f) :=
  (Silmaril.Proofs.X86.Sep.Insn.jcc8_not_taken hev hdec hpc).lift E

/-- `jne` after `test %r32, %r32` on `v`: taken exactly when the low half of `v` is not zero. -/
theorem eval_ne_testFlags (v : Word) :
    Silmaril.X86.Ext.Cond.ne.eval (testFlags v) = some (!(v.setWidth 32 == 0#32)) :=
  Silmaril.Proofs.X86.Sep.Insn.eval_ne_testFlags v

/-! ## Memory forms -/

/-- **`mov %src, disp(%base)`** (64-bit store into an owned eight-byte block). -/
theorem storeQ_step (E : Open.isa.Extends I)
    {pc pc' b v : Word} {bytes : List Byte} {base src : Reg} {disp : BitVec 32}
    {a : Nat} (ha : (b + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.mov .q (.mem (memAt base disp)) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ regPt src v ∗ blockAny a 8)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗ regPt src v ∗ wordPt a v) :=
  (Silmaril.Proofs.X86.Sep.Insn.storeQ_step ha hdec hnext).lift E

/-- **`lea disp(%base), %dst`** (64-bit). -/
theorem leaQ_step (E : Open.isa.Extends I)
    {pc pc' b : Word} {bytes : List Byte} {base dst : Reg} {disp : BitVec 32}
    (hne : dst ≠ base)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.lea .q dst (memAt base disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗
        regPt dst (b + disp.signExtend 64)) :=
  (Silmaril.Proofs.X86.Sep.Insn.leaQ_step hne hdec hnext).lift E

/-- **`mov disp(%base), %dst`** (64-bit load of an owned word). -/
theorem loadQ_step (E : Open.isa.Extends I)
    {pc pc' b w : Word} {bytes : List Byte} {base dst : Reg} {disp : BitVec 32}
    {a : Nat} (ha : (b + disp.signExtend 64).toNat = a) (hne : dst ≠ base)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.load .q dst (memAt base disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple I (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ wordPt a w ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗ wordPt a w ∗ regPt dst w) :=
  (Silmaril.Proofs.X86.Sep.Insn.loadQ_step ha hne hdec hnext).lift E

end Silmaril.X86.Sep.Insn
