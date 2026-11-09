module

public import Silmaril.X86.Sep.Insn.Defs
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.Proofs.X86.Sep.Bridge
public import Silmaril.Proofs.X86.Sep.Algebra
public import Silmaril.X86.Ext.SymExec

/-!
# Proofs: single-instruction triples on the open machine

Total triples on `Open.isa` for `X86.Ext` forms (the instructions of `setjmp`/`longjmp` in
`Sep/JmpBuf`, among others):

| lemma | form | `setjmp`/`longjmp` use |
| --- | --- | --- |
| `storeQ_step` | `mov %src, disp(%base)` | `movq %rbx, 0(%rdi)` … `movq %rdx, 56(%rdi)` |
| `loadQ_step` | `mov disp(%base), %dst` | `movq (%rsp), %rdx`, `movq 0(%rdi), %rbx` … `movq 48(%rdi), %rsp` |
| `leaQ_step` | `lea disp(%base), %dst` | `leaq 8(%rsp), %rdx` |
| `xorSelf_step` | `xor %r32, %r32` | `xorl %eax, %eax` |
| `movD_step` | `mov %src32, %dst32` | `movl %esi, %eax` |
| `movI32_step` | `mov $imm32, %r32` | `movl $1, %eax` |
| `testSelf_step` | `test %r32, %r32` | `testl %eax, %eax` |
| `jcc8_step` | `jcc rel8` on owned flags | `jnz 1f` |

`insn_triple` is the generic form: an open step from every state containing the operands'
fragment, that changes nothing but `rip` outside it, is a triple with the code returned.
`open_of_ext` turns an `Ext` step of a loaded instruction into an open step. `ret` and
`call rel32` are `Sep.ret_step` and `Sep.call_step` (`Sep/SysV/Thms.lean`); `jmp *56(%rdi)`
is an `Ext9` form and goes through `Sep.Ind.jmpM_progress`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Sep.Insn

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.X86.Ext (Mem Sz)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Insn (memAt testFlags)
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)
open Silmaril.Proofs.X86.Sep (toFrag_isSome)

/-! ## Fragment helpers -/

theorem union_none {a b : Frag} {l : Loc} (h : union a b l = none) : a l = none ∧ b l = none :=
  Silmaril.Proofs.X86.Sep.Frag.union_eq_none.mp h

theorem reval_agree {h s s' : Frag} (hl : Le h s) (hag : ∀ l, (h l).isSome → s' l = s l) :
    reval h s' = h := by
  rw [Silmaril.Proofs.X86.Sep.Frag.reval_eq_of_agree hl hag]

theorem isSome_of_disjoint {a b : Frag} (hd : Disjoint a b) {l : Loc} (hb : (b l).isSome) :
    a l = none := by
  rcases hd l with e | e
  · exact e
  · rw [e] at hb; cases hb

theorem single_none {l l' : Loc} {v : Val} (h : Frag.single l v l' = none) : l' ≠ l := by
  rintro rfl; simp [Frag.single] at h

theorem regPt_frag {r : Reg} {v : Word} {h : Frag} (hp : regPt r v h) :
    h = Frag.single (.reg r) (.word v) := hp

theorem flagsAny_reval_exact {h : Frag} (m : MState) (hp : flagsAny h) :
    flagsPt m.core.flags (reval h (toFrag m)) := by
  obtain ⟨f, rfl⟩ := hp
  exact Silmaril.Proofs.X86.Sep.Frag.reval_single _ _ _ rfl

theorem flagsPt_reval {f : Flags} {h : Frag} (m : MState) (hp : flagsPt f h) :
    flagsPt m.core.flags (reval h (toFrag m)) :=
  flagsAny_reval_exact m ⟨f, hp⟩

/-! ## The generic single-instruction triple -/

/-- **A generic single-instruction triple.** -/
theorem insn_triple {pc pc' : Word} {bytes : List Byte} {X Y : SProp} (hne : bytes ≠ [])
    (h : ∀ (m : MState) (hX : Frag), X hX → Le hX (toFrag m) → m.core.rip = pc →
      Silmaril.X86.Ext.Loaded m.memory pc bytes →
      ∃ m', Silmaril.X86.Open.step m = some m' ∧ m'.core.rip = pc' ∧
        (∀ l, l ≠ .rip → hX l = none → toFrag m' l = toFrag m l) ∧
        Y (reval hX (toFrag m'))) :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ X) (codePt pc.toNat bytes ∗ ripPt pc' ∗ Y) := by
  apply Silmaril.Proofs.X86.Sep.triple_of_local_mstate (fun _ => rfl) (fun _ => rfl)
  intro m h₁ hP hl
  obtain ⟨hc, r1, hcP, hr1, hlc, hlr1, hd1, rfl⟩ := sep_le hP hl
  obtain ⟨hrip, hX, hripP, hXP, hlrip, hlX, hd2, rfl⟩ := sep_le hr1 hlr1
  have erip := ripPt_le hripP hlrip
  have fetch := fetchBytes_of_codePt hne hcP hlc
  obtain ⟨m', hstep, hrip', hsame, hY⟩ := h m hX hXP hlX erip fetch
  have hripS := Silmaril.Proofs.X86.Sep.ripPt_dom hripP
  refine ⟨m', ⟨1, by simp [run, hstep]⟩, fun l hl0 => ?_, ?_⟩
  · obtain ⟨-, hrest⟩ := union_none hl0
    obtain ⟨n1, n2⟩ := union_none hrest
    exact hsame l (by rintro rfl; rw [n1] at hripS; cases hripS) n2
  have hcode : reval hc (toFrag m') = hc := by
    refine reval_agree hlc fun l hs => ?_
    have hn := isSome_of_disjoint (fun l => (hd1 l).symm) hs
    obtain ⟨n1, n2⟩ := union_none hn
    exact hsame l (by rintro rfl; rw [n1] at hripS; cases hripS) n2
  rw [Silmaril.Proofs.X86.Sep.Frag.reval_union, Silmaril.Proofs.X86.Sep.Frag.reval_union,
    hcode]
  refine ⟨_, _, ?_, rfl, hcP, _, _, ?_, rfl, ?_, hY⟩
  · rw [← hcode, ← Silmaril.Proofs.X86.Sep.Frag.reval_union]
    exact Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd1 _
  · exact Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd2 _
  · have := Silmaril.Proofs.X86.Sep.ripPt_reval m' hripP
    rwa [hrip'] at this

/-- An `Ext` step from a loaded instruction is an open step. -/
theorem open_of_ext {m : MState} {pc : Word} {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    {core : State} {memory : Memory} (hl : Silmaril.X86.Ext.Loaded m.memory pc bytes)
    (hrip : m.core.rip = pc) (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length))
    (hnr : i ≠ .ret) (hx : Silmaril.X86.Ext.exec i m.core m.memory = .ok core memory) :
    Silmaril.X86.Open.step m = some ⟨core, memory⟩ := by
  have hE := Silmaril.X86.Ext.stepOpt_of_loaded (exit := 0) (offset := 0) (len := bytes.length)
    hl (by rw [hrip]; simp) (by omega)
    (by rw [List.drop_zero, List.take_of_length_le (by omega)]; exact hdec) hnr hx
  exact Silmaril.X86.Open.step_of_ext8_stepOpt (Silmaril.X86.Ext8.stepOpt_of_ext hE)

theorem len_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, bytes.length)) : i.length = bytes.length :=
  (Silmaril.X86.Ext.decode_length hdec).1.symm

theorem ne_nil_of_dec {bytes : List Byte} {i : Silmaril.X86.Ext.Instr} {n : Nat}
    (hdec : Silmaril.X86.Ext.decode bytes = some (i, n)) : bytes ≠ [] := by
  rintro rfl; cases hdec

/-- Locations other than `rip`, register `r` and the flags agree after a register write. -/
theorem toFrag_write_other {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) (hf : c.flags = m.core.flags) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l := by
  cases l with
  | reg q =>
    have hq : q ≠ r := fun e => h2 (e ▸ rfl)
    simp only [toFrag]; rw [hc q hq]
  | rip => exact absurd rfl h1
  | flags => simp only [toFrag]; rw [hf]
  | mem a => rfl
  | regions => rfl

/-- Same, also allowing the flags to change. -/
theorem toFrag_write_other' {m : MState} {c : State} {r : Reg}
    (hc : ∀ q, q ≠ r → c.read q = m.core.read q) {l : Loc}
    (h1 : l ≠ .rip) (h2 : l ≠ .reg r) (h3 : l ≠ .flags) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l := by
  cases l with
  | reg q =>
    have hq : q ≠ r := fun e => h2 (e ▸ rfl)
    simp only [toFrag]; rw [hc q hq]
  | rip => exact absurd rfl h1
  | flags => exact absurd rfl h3
  | mem a => rfl
  | regions => rfl

/-- Only `rip` and the flags change. -/
theorem toFrag_flags_other {m : MState} {c : State} (hc : ∀ q, c.read q = m.core.read q) {l : Loc}
    (h1 : l ≠ .rip) (h3 : l ≠ .flags) :
    toFrag ⟨c, m.memory⟩ l = toFrag m l := by
  cases l with
  | reg q => simp only [toFrag]; rw [hc q]
  | rip => exact absurd rfl h1
  | flags => exact absurd rfl h3
  | mem a => rfl
  | regions => rfl

/-! ## Memory operands -/

theorem memAt_addr (base : Reg) (disp : BitVec 32) (s : State) (next : Word) :
    (memAt base disp).addr s next = s.read base + disp.signExtend 64 := by
  simp [Mem.addr, memAt]

/-! ## Register-only forms -/

/-- **`mov $imm32, %r32`.** -/
theorem movI32_step {pc pc' : Word} {bytes : List Byte} {r : Reg} {imm : BitVec 32}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.movI32 r imm, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r (imm.setWidth 64)) := by
  have hne := ne_nil_of_dec hdec
  refine insn_triple hne fun m hX ⟨v, hXP⟩ hlX hrip hl => ?_
  have hlen := len_of_dec hdec
  set c : State := { Silmaril.X86.Ext.Sz.d.write m.core r imm with
    rip := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.movI32 r imm).length }
  have hx : Silmaril.X86.Ext.exec (.movI32 r imm) m.core m.memory = .ok c m.memory := rfl
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · rw [regPt_frag hXP] at h2
    exact toFrag_write_other (m := m) (c := c) (fun q hq => by
      show (Silmaril.X86.Ext.Sz.d.write m.core r imm).read q = _
      simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]) rfl h1 (single_none h2)
  · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hXP
    have e : c.read r = imm.setWidth 64 := by
      show (Silmaril.X86.Ext.Sz.d.write m.core r imm).read r = _
      simp [Silmaril.X86.Ext.Sz.write, State.read_write_same]
    rwa [e] at this

/-- Two register atoms, read back. -/
theorem two_regs {m : MState} {hX : Frag} {r₁ : Reg} {v₁ : Word} {Q : SProp}
    (hXP : (regPt r₁ v₁ ∗ Q) hX) (hlX : Le hX (toFrag m)) :
    ∃ h₁ h₂, Disjoint h₁ h₂ ∧ hX = union h₁ h₂ ∧ regPt r₁ v₁ h₁ ∧ Q h₂ ∧ Le h₂ (toFrag m) ∧
      m.core.read r₁ = v₁ := by
  obtain ⟨h₁, h₂, hP₁, hP₂, hl₁, hl₂, hd, rfl⟩ := sep_le hXP hlX
  exact ⟨h₁, h₂, hd, rfl, hP₁, hP₂, hl₂, regPt_le hP₁ hl₁⟩

/-- **`mov %src32, %dst32`** (zero-extending). -/
theorem movD_step {pc pc' v : Word} {bytes : List Byte} {dst src : Reg} (hne : dst ≠ src)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.mov .d (.reg dst) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt src v ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt src v ∗
        regPt dst ((v.setWidth 32).setWidth 64)) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, ⟨w, hP₂⟩, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set c : State := { Sz.d.write m.core dst (Sz.d.read m.core src) with
    rip := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.mov .d (.reg dst) src).length }
  have hx : Silmaril.X86.Ext.exec (.mov .d (.reg dst) src) m.core m.memory = .ok c m.memory := rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (Sz.d.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    rw [regPt_frag hP₂] at n2
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n2)
  · rw [Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read src = v by rw [hcr src (Ne.symm hne), ev]] at this
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₂
      have e : c.read dst = (v.setWidth 32).setWidth 64 := by
        show (Sz.d.write m.core dst _).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read, State.read_write_same, ev]
      rwa [e] at this

/-- **`xor %r32, %r32`**: zero the register. -/
theorem xorSelf_step {pc pc' v : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.alu .d .xor (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r 0 ∗ flagsAny) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, -, ev⟩ := two_regs hXP hlX
  have hE := Silmaril.X86.Ext.stepOpt_alu_reg_mk (exit := 0) (offset := 0) (len := bytes.length)
    (result := 0) hl (by rw [hrip]; simp) (by omega)
    (by rw [List.drop_zero, List.take_of_length_le (by omega)]; exact hdec) (by decide)
    (by simp only [Silmaril.X86.Ext.AluOp.resultN]; rw [BitVec.xor_self]; rfl)
  have hstep := Silmaril.X86.Open.step_of_ext8_stepOpt (Silmaril.X86.Ext8.stepOpt_of_ext hE)
  set c : State := { m.core.write r 0 with
    flags := Silmaril.X86.Ext.AluOp.flagsN .xor (Silmaril.X86.Ext.Sz.d.read m.core r)
      (Silmaril.X86.Ext.Sz.d.read m.core r),
    rip := pc + BitVec.ofNat 64 (0 + bytes.length) }
  have hcr : ∀ q, q ≠ r → c.read q = m.core.read q := fun q hq => by
    show (m.core.write r 0).read q = _
    exact State.read_write_other _ _ _ _ hq
  refine ⟨⟨c, m.memory⟩, hstep, ?_, fun l h1 h2 => ?_, ?_⟩
  · show pc + _ = pc'; rw [Nat.zero_add, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    refine toFrag_write_other' (m := m) (c := c) hcr h1 (single_none n1) ?_
    rintro rfl
    have := Silmaril.Proofs.X86.Sep.flagsAny_dom hP₂; rw [n2] at this; cases this
  · rw [Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _, rfl, ?_,
      Silmaril.Proofs.X86.Sep.flagsAny_reval _ hP₂⟩
    have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₁
    rwa [show c.read r = 0 from State.read_write_same _ _ _] at this

/-- **`xor %r32, %r32`** from an unknown value. -/
theorem xorSelf_any {pc pc' : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.alu .d .xor (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r 0 ∗ flagsAny) := by
  rw [show (codePt pc.toNat bytes ∗ ripPt pc ∗ regAny r ∗ flagsAny) =
      sexists fun v => codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny by
    simp only [regAny, sexists_sep, sep_sexists]]
  exact Triple.sexists fun v => xorSelf_step hdec hnext

/-! ## Flags and branches -/

/-- **`test %r32, %r32`.** -/
theorem testSelf_step {pc pc' v : Word} {bytes : List Byte} {r : Reg}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.test .d (.reg r) r, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt r v ∗ flagsPt (testFlags v)) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, hP₂, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.test .d (.reg r) r).length
  set c : State := { m.core with flags := testFlags v, rip := nx }
  have hx : Silmaril.X86.Ext.exec (.test .d (.reg r) r) m.core m.memory = .ok c m.memory := by
    simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.retire, c, testFlags,
      Silmaril.X86.Ext.Sz.read, ev, nx]
    exact congrArg _ BitVec.and_self
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨n1, n2⟩ := union_none h2
    rw [regPt_frag hP₁] at n1
    refine toFrag_flags_other (m := m) (c := c) (fun q => rfl) h1 ?_
    rintro rfl
    have := Silmaril.Proofs.X86.Sep.flagsAny_dom hP₂; rw [n2] at this; cases this
  · rw [Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read r = v from ev] at this
    · exact flagsAny_reval_exact ⟨c, m.memory⟩ hP₂

/-- **`jcc rel8`** on owned flags whose condition is defined. -/
theorem jcc8_step {pc : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    {f : Flags} {b : Bool} (hev : c.eval f = some b)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length)) :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗
        ripPt (if b then pc + BitVec.ofNat 64 bytes.length + rel.signExtend 64
          else pc + BitVec.ofNat 64 bytes.length) ∗ flagsPt f) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  have ef := flagsPt_le hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.jcc8 c rel).length
  set core : State := { m.core with rip := if b then nx + rel.signExtend 64 else nx }
  have hx : Silmaril.X86.Ext.exec (.jcc8 c rel) m.core m.memory = .ok core m.memory := by
    cases b <;> simp [Silmaril.X86.Ext.exec, ef, hev, core, nx]
  refine ⟨⟨core, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 _ => ?_, ?_⟩
  · show (if b then nx + _ else nx) = _
    rw [show nx = pc + BitVec.ofNat 64 bytes.length by rw [← hrip, ← hlen]]
  · exact toFrag_flags_other (m := m) (c := core) (fun _ => rfl) h1 (by
      rintro rfl
      exact absurd (show hX .flags = none by assumption) (by rw [hXP]; simp [Frag.single]))
  · have := flagsPt_reval ⟨core, m.memory⟩ hXP
    rwa [show core.flags = f from ef] at this

/-- A taken `jcc rel8`. -/
theorem jcc8_taken {pc pc' : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond}
    {rel : BitVec 8} {f : Flags} (hev : c.eval f = some true)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length))
    (hpc : pc + BitVec.ofNat 64 bytes.length + rel.signExtend 64 = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ flagsPt f) := by
  have h := jcc8_step (pc := pc) hev hdec
  simp only [↓reduceIte] at h
  rw [hpc] at h
  exact h

/-- A `jcc rel8` that falls through. -/
theorem jcc8_not_taken {pc pc' : Word} {bytes : List Byte} {c : Silmaril.X86.Ext.Cond}
    {rel : BitVec 8} {f : Flags} (hev : c.eval f = some false)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.jcc8 c rel, bytes.length))
    (hpc : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ flagsPt f)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ flagsPt f) := by
  have h := jcc8_step (pc := pc) hev hdec
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [hpc] at h
  exact h

/-- `jne` after `test %r32, %r32` on `v`: taken exactly when the low half of `v` is not zero. -/
theorem eval_ne_testFlags (v : Word) :
    Silmaril.X86.Ext.Cond.ne.eval (testFlags v) = some (!(v.setWidth 32 == 0#32)) := rfl

/-! ## Memory forms -/

/-- A byte-list atom owns memory locations only. -/
theorem bytesAt_nonmem {need : Silmaril.Process.Permissions → Prop} :
    ∀ {a : Nat} {bs : List Byte} {h : Frag}, bytesAt need a bs h →
      ∀ l, (∀ x, l ≠ .mem x) → h l = none
  | _, [], h, hp, l, _ => by rw [show h = Frag.empty from hp]; rfl
  | a, b :: bs, h, hp, l, hl => by
    obtain ⟨h₁, h₂, -, rfl, ⟨-, p, -, rfl⟩, hr⟩ := hp
    have e1 : Frag.single (.mem a) (.cell ⟨some b, p⟩) l = none := by
      simp [Frag.single, hl a]
    simp only [Frag.union, e1]
    exact bytesAt_nonmem hr l hl

/-- **`mov %src, disp(%base)`** (64-bit store into an owned eight-byte block). -/
theorem storeQ_step {pc pc' b v : Word} {bytes : List Byte} {base src : Reg} {disp : BitVec 32}
    {a : Nat} (ha : (b + disp.signExtend 64).toNat = a)
    (hdec : Silmaril.X86.Ext.decode bytes =
      some (.mov .q (.mem (memAt base disp)) src, bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ regPt src v ∗ blockAny a 8)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗ regPt src v ∗ wordPt a v) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, r₁, hd, rfl, hP₁, hR, hlR, eb⟩ := two_regs hXP hlX
  obtain ⟨h₂, h₃, hd₂, rfl, hP₂, hP₃, hl₃, ev⟩ := two_regs hR hlR
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.mov .q (.mem (memAt base disp)) src).length
  have perm := permitted_of_blockAny (.inr rfl) (by omega) hP₃ hl₃
  obtain ⟨after, hst, stored⟩ := Silmaril.X86.Ext.storeN_isSome (k := 8) (v := v)
    (memory := m.memory) (address := b + disp.signExtend 64) (by rw [ha]; exact perm)
  have hx : Silmaril.X86.Ext.exec (.mov .q (.mem (memAt base disp)) src) m.core m.memory =
      .ok { m.core with rip := nx } after := by
    show Silmaril.X86.Ext.retire nx (Silmaril.X86.Ext.writeRM .q (.mem (memAt base disp))
      (Sz.q.read m.core src) m.core m.memory nx) = _
    have hv : (Sz.q.read m.core src).setWidth 64 = v := by
      rw [← ev]; exact BitVec.setWidth_eq _
    simp only [Silmaril.X86.Ext.writeRM, memAt_addr, eb, Sz.bytes, hv, hst, Option.map_some]
    rfl
  rw [ha] at stored
  have hregions : after.regions = m.memory.regions := stored.frame.1
  have hperms : ∀ x, permsAt after x = permsAt m.memory x := by
    intro x; simp [permsAt, Silmaril.Process.Memory.permits, hregions]
  have outside : ∀ x, h₃ (.mem x) = none → toFrag ⟨{ m.core with rip := nx }, after⟩ (.mem x) =
      toFrag m (.mem x) := by
    intro x n3
    have hx' : x < a ∨ a + (Silmaril.X86.Ext.leBytes v 8).length ≤ x := by
      rw [Silmaril.X86.Ext.length_leBytes]
      by_contra hc
      have := blockAny_dom hP₃ (x - a) (by omega)
      rw [show a + (x - a) = x by omega, n3] at this; cases this
    simp only [toFrag]
    rw [hperms x, stored.frame.2 x hx']
  refine ⟨⟨{ m.core with rip := nx }, after⟩, open_of_ext hl hrip hdec (by simp) hx, ?_,
    fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    obtain ⟨-, n3⟩ := union_none n2
    cases l with
    | reg q => rfl
    | rip => exact absurd rfl h1
    | flags => rfl
    | mem x => exact outside x n3
    | regions => simp only [toFrag]; rw [hregions]
  · have hagR : ∀ (h : Frag) (r : Reg) (w : Word), regPt r w h →
        reval h (toFrag ⟨{ m.core with rip := nx }, after⟩) = reval h (toFrag m) := by
      intro h r w hp
      rw [regPt_frag hp]
      funext l
      by_cases e : l = .reg r
      · subst e; simp [reval, Frag.single, toFrag]
      · simp [reval, Frag.single, e]
    rw [Silmaril.Proofs.X86.Sep.Frag.reval_union, Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, ?_, rfl, ?_, _, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd₂ _, rfl,
      ?_, ?_⟩
    · rw [← Silmaril.Proofs.X86.Sep.Frag.reval_union]
      exact Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _
    · rw [hagR _ _ _ hP₁]
      have := Silmaril.Proofs.X86.Sep.regPt_reval m hP₁
      rwa [eb] at this
    · rw [hagR _ _ _ hP₂]
      have := Silmaril.Proofs.X86.Sep.regPt_reval m hP₂
      rwa [ev] at this
    · refine Silmaril.Proofs.X86.Sep.blockAny_reval_bytes hP₃ (by simp) (fun i hi => ⟨?_, ?_⟩)
      · have := stored.installed i (by simpa using hi)
        rw [this]
        simp [Silmaril.X86.Ext.leBytes_eight]
      · rw [hperms]
        exact (blockAny_le hP₃ hl₃ i (by simpa using hi)).2

/-- **`lea disp(%base), %dst`** (64-bit). -/
theorem leaQ_step {pc pc' b : Word} {bytes : List Byte} {base dst : Reg} {disp : BitVec 32}
    (hne : dst ≠ base)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.lea .q dst (memAt base disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗
        regPt dst (b + disp.signExtend 64)) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, h₂, hd, rfl, hP₁, ⟨w, hP₂⟩, -, ev⟩ := two_regs hXP hlX
  have hlen := len_of_dec hdec
  set nx := m.core.rip + BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.lea .q dst (memAt base disp)).length
  set c : State := { Sz.q.write m.core dst (((memAt base disp).addr m.core nx).setWidth 64) with
    rip := nx }
  have hx : Silmaril.X86.Ext.exec (.lea .q dst (memAt base disp)) m.core m.memory =
      .ok c m.memory := rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (Sz.q.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    rw [regPt_frag hP₂] at n2
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n2)
  · rw [Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _, rfl, ?_, ?_⟩
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read base = b by rw [hcr base (Ne.symm hne), ev]] at this
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₂
      have e : c.read dst = b + disp.signExtend 64 := by
        show (Sz.q.write m.core dst _).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, State.read_write_same, memAt_addr, ev]
      rwa [e] at this

/-- An owned word, read by an eight-byte load. -/
theorem loadN_of_wordPt {a : Nat} {w : Word} {h : Frag} {m : MState} {A : Word}
    (hA : A.toNat = a) (hp : wordPt a w h) (hl : Le h (toFrag m)) :
    Silmaril.X86.Ext.loadN m.memory A 8 = some w := by
  apply Silmaril.X86.Ext.loadN_of_holdsLE_eight
  rw [Silmaril.X86.Ext.HoldsLE, Silmaril.X86.Ext.leBytes_eight, hA]
  exact readBytes_of_wordPt hp hl

/-- **`mov disp(%base), %dst`** (64-bit load of an owned word). -/
theorem loadQ_step {pc pc' b w : Word} {bytes : List Byte} {base dst : Reg} {disp : BitVec 32}
    {a : Nat} (ha : (b + disp.signExtend 64).toNat = a) (hne : dst ≠ base)
    (hdec : Silmaril.X86.Ext.decode bytes = some (.load .q dst (memAt base disp), bytes.length))
    (hnext : pc + BitVec.ofNat 64 bytes.length = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt base b ∗ wordPt a w ∗ regAny dst)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗ regPt base b ∗ wordPt a w ∗ regPt dst w) := by
  refine insn_triple (ne_nil_of_dec hdec) fun m hX hXP hlX hrip hl => ?_
  obtain ⟨h₁, r₁, hd, rfl, hP₁, hR, hlR, eb⟩ := two_regs hXP hlX
  obtain ⟨h₂, h₃, hP₂, ⟨u, hP₃⟩, hl₂, -, hd₂, rfl⟩ := sep_le hR hlR
  have hlen := len_of_dec hdec
  set nx := m.core.rip +
    BitVec.ofNat 64 (Silmaril.X86.Ext.Instr.load .q dst (memAt base disp)).length
  have hload : Silmaril.X86.Ext.loadN m.memory ((memAt base disp).addr m.core nx) 8 = some w := by
    rw [memAt_addr, eb]; exact loadN_of_wordPt ha hP₂ hl₂
  set c : State := { Sz.q.write m.core dst w with rip := nx }
  have hx : Silmaril.X86.Ext.exec (.load .q dst (memAt base disp)) m.core m.memory =
      .ok c m.memory := by
    show Silmaril.X86.Ext.retire nx ((Silmaril.X86.Ext.readRM .q (.mem (memAt base disp)) m.core
      m.memory nx).map fun v => (Sz.q.write m.core dst v, m.memory)) = _
    simp only [Silmaril.X86.Ext.readRM, Sz.bytes, hload, Option.map_some]
    rfl
  have hcr : ∀ q, q ≠ dst → c.read q = m.core.read q := fun q hq => by
    show (Sz.q.write m.core dst _).read q = _
    simp [Silmaril.X86.Ext.Sz.write, State.read_write_other _ _ _ _ hq]
  refine ⟨⟨c, m.memory⟩, open_of_ext hl hrip hdec (by simp) hx, ?_, fun l h1 h2 => ?_, ?_⟩
  · show m.core.rip + _ = pc'; rw [hrip, hlen, hnext]
  · obtain ⟨-, n2⟩ := union_none h2
    obtain ⟨-, n3⟩ := union_none n2
    rw [regPt_frag hP₃] at n3
    exact toFrag_write_other (m := m) (c := c) hcr rfl h1 (single_none n3)
  · have hag : ∀ l, (h₂ l).isSome → toFrag ⟨c, m.memory⟩ l = toFrag m l := by
      intro l hs
      have n3 : h₃ l = none := isSome_of_disjoint (fun l => (hd₂ l).symm) hs
      rw [regPt_frag hP₃] at n3
      refine toFrag_write_other (m := m) (c := c) hcr rfl ?_ (single_none n3)
      rintro rfl
      rw [bytesAt_nonmem hP₂ .rip (fun _ => by simp)] at hs
      cases hs
    rw [Silmaril.Proofs.X86.Sep.Frag.reval_union, Silmaril.Proofs.X86.Sep.Frag.reval_union]
    refine ⟨_, _, ?_, rfl, ?_, _, _, Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd₂ _, rfl,
      ?_, ?_⟩
    · rw [← Silmaril.Proofs.X86.Sep.Frag.reval_union]
      exact Silmaril.Proofs.X86.Sep.Frag.reval_disjoint hd _
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₁
      rwa [show c.read base = b by rw [hcr base (Ne.symm hne), eb]] at this
    · rw [reval_agree hl₂ hag]; exact hP₂
    · have := Silmaril.Proofs.X86.Sep.regPt_reval ⟨c, m.memory⟩ hP₃
      have e : c.read dst = w := by
        show (Sz.q.write m.core dst w).read dst = _
        simp [Silmaril.X86.Ext.Sz.write, State.read_write_same]
      rwa [e] at this

end Silmaril.Proofs.X86.Sep.Insn
