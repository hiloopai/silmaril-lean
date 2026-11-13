module

public import Silmaril.Compiler.Core.Verified.PrintExpr.Defs
/-! # A linked runtime expression with a decimal format

The link evaluates the integer expression in Lir and writes its decimal digits
between literal bytes. Its correctness holds over every argument block. This
is a target-side building block; it does not enable a source fragment.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintExprLink

open Silmaril.Machine Silmaril.Compile
open Spec Backend PrintLink

/-- Literal bytes surrounding one runtime signed-int expression. -/
def formatOps (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) : List Op :=
  (pre.map Item.byte).flatMap itemOps ++ PrintExpr.closedDecimalOps t ++
    (suffix.map Item.byte).flatMap itemOps

/-- Specification only: the output of the expression. -/
def output (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) : List UInt8 :=
  pre ++ Item.render (.int (t.val 0)) ++ suffix

def Fits (pre suffix : List UInt8) : Prop :=
  outBase + pre.length + 11 + suffix.length ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase

instance (pre suffix : List UInt8) : Decidable (Fits pre suffix) := by
  unfold Fits; infer_instance

theorem bytes_render (bs : List UInt8) : render (bs.map Item.byte) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [render, Item.render] using congrArg (b :: ·) ih

theorem bytes_room (bs : List UInt8) : ((bs.map Item.byte).map Item.room).sum = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [Item.room, Nat.add_comm] using ih

theorem bytes_small (bs : List UInt8) : ∀ it ∈ bs.map Item.byte, it.small = true := by
  intro it hi
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hi
  rfl

theorem output_length {t : IntExpr.Term} (range : ConvInt.IsInt (t.val 0)) (pre suffix : List UInt8) :
    (output pre t suffix).length ≤ pre.length + 11 + suffix.length := by
  have small : (t.val 0).natAbs < 10 ^ 10 := by obtain ⟨lo, hi⟩ := range; omega
  have := render_int_length (t.val 0) small
  simp only [output, List.length_append]
  omega

/-- The expression and both literal parts append to the current output. -/
theorem format_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (hs : size < 2 ^ 64) (pre suffix : List UInt8) {t : IntExpr.Term}
    (ok : t.Ok 0) (range : ConvInt.IsInt (t.val 0))
    (room : outBase + out.length + pre.length + 11 + suffix.length ≤ size) (rest : List Op) :
    ∃ fr' m', Lir.execOps (formatOps pre t suffix ++ rest) fr m = Lir.execOps rest fr' m' ∧
      Inv size fr' m' (out ++ output pre t suffix) := by
  obtain ⟨fr1, m1, run1, inv1⟩ := items_exec hs (pre.map Item.byte) (bytes_small pre) inv
    (by rw [bytes_room]; omega)
    (PrintExpr.closedDecimalOps t ++ ((suffix.map Item.byte).flatMap itemOps ++ rest))
  rw [bytes_render] at inv1
  obtain ⟨fr2, m2, run2, inv2⟩ := PrintExpr.closedDecimal_exec inv1
    (by simp only [List.length_append]; omega) hs ok range ((suffix.map Item.byte).flatMap itemOps ++ rest)
  have small : (t.val 0).natAbs < 10 ^ 10 := by obtain ⟨lo, hi⟩ := range; omega
  have len := render_int_length (t.val 0) small
  obtain ⟨fr3, m3, run3, inv3⟩ := items_exec hs (suffix.map Item.byte) (bytes_small suffix) inv2
    (by rw [bytes_room]; simp only [List.length_append]; omega) rest
  refine ⟨fr3, m3, ?_, ?_⟩
  · simpa only [formatOps, List.append_assoc, run1, run2] using run3
  · simpa only [bytes_render, output, List.append_assoc] using inv3

/-- The control words and exit value follow the runtime computation. -/
def ops (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) (w : Lir.Word) : List Op :=
  prologue ++ formatOps pre t suffix ++
    [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen, .store .b8 rCtl 48 rBase,
      .store .b8 rCtl 56 rLen, .const 0 w]

def startFunc (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) (w : Lir.Word) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := [⟨(ops pre t suffix w).map .op, .ret [.reg 0]⟩] }

def link (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) (w : Lir.Word) : Mir.Linked where
  prog := ⟨[startFunc pre t suffix w]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

theorem ops_exec {pre suffix : List UInt8} {t : IntExpr.Term} (fits : Fits pre suffix)
    (ok : t.Ok 0) (range : ConvInt.IsInt (t.val 0)) (w : Lir.Word) (fr0 : Lir.Frame Mir.Reg)
    (m0 : Lir.Memory) (hsize : m0.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ fr m, Lir.execOps (ops pre t suffix w) fr0 m0 = some (fr, m) ∧ fr.get 0 = some w ∧
      memWord m (ctlAddr + 24) = (output pre t suffix).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (output pre t suffix) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  have hroom : outBase + pre.length + 11 + suffix.length ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase := fits
  have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
  have hab : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  let epi : List Op := [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen,
    .store .b8 rCtl 48 rBase, .store .b8 rCtl 56 rLen, .const 0 w]
  obtain ⟨fr1, hx1, inv1⟩ := prologue_exec fr0 m0 (formatOps pre t suffix ++ epi)
  rw [hsize] at inv1
  obtain ⟨fr2, m2, hx2, inv2⟩ := format_exec inv1 hs pre suffix ok range (by simp; omega) epi
  simp only [List.nil_append] at inv2
  have hlen := output_length range pre suffix
  let L := (output pre t suffix).length
  have hL : L < 2 ^ 64 := by omega
  let fr3 := fr2.set rCtl (BitVec.ofNat 64 ctlAddr)
  have hctl : fr3.get rCtl = some (BitVec.ofNat 64 ctlAddr) := get_set_eq _ _ _
  have hlen3 : fr3.get rLen = some (BitVec.ofNat 64 L) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.len
  have hbase3 : fr3.get rBase = some (BitVec.ofNat 64 outBase) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.base
  have hc : (BitVec.ofNat 64 ctlAddr).toNat = ctlAddr := by decide
  have hsz2 := inv2.size
  let m3 : Lir.Memory := ⟨m2.size, Lir.writeLE m2.bytes (ctlAddr + 24) 8 (BitVec.ofNat 64 L)⟩
  have hst3 : m2.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 24) (BitVec.ofNat 64 L) = some m3 := by
    rw [hc, store_some (by simp [Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m4 : Lir.Memory := ⟨m3.size, Lir.writeLE m3.bytes (ctlAddr + 48) 8 (BitVec.ofNat 64 outBase)⟩
  have hst4 : m3.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 48) (BitVec.ofNat 64 outBase) = some m4 := by
    rw [hc, store_some (by simp [m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m5 : Lir.Memory := ⟨m4.size, Lir.writeLE m4.bytes (ctlAddr + 56) 8 (BitVec.ofNat 64 L)⟩
  have hst5 : m4.store .b8 ((BitVec.ofNat 64 ctlAddr).toNat + 56) (BitVec.ofNat 64 L) = some m5 := by
    rw [hc, store_some (by simp [m4, m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  rw [hc] at hst3 hst4 hst5
  refine ⟨fr3.set 0 w, m5, ?_, get_set_eq _ _ _, ?_, ?_, ?_, by simp [m5, m4, m3, hsz2]⟩
  · rw [ops, List.append_assoc, hx1, hx2, exec_const,
      exec_store _ hctl hlen3 (by rw [hc]; exact hst3),
      exec_store _ hctl hbase3 (by rw [hc]; exact hst4),
      exec_store _ hctl hlen3 (by rw [hc]; exact hst5), exec_const]
    rfl
  · rw [memWord_outside hst5 (by left; decide), memWord_outside hst4 (by left; decide),
      memWord_store hst3, toNat_ofNat_lt hL]
  · rw [memWord_outside hst5 (by left; decide), memWord_store hst4, toNat_ofNat_lt (by decide)]
  · intro i hi
    rw [store_bytes_outside hst5 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
      store_bytes_outside hst4 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
      store_bytes_outside hst3 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega)]
    exact inv2.buf i hi

theorem link_funcs (pre : List UInt8) (t : IntExpr.Term) (suffix : List UInt8) (w : Lir.Word) :
    (link pre t suffix w).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The Lir run of `__ccomp_start` returns `[w]` with the output written. -/
theorem link_returns {pre suffix : List UInt8} {t : IntExpr.Term} (fits : Fits pre suffix)
    (ok : t.Ok 0) (range : ConvInt.IsInt (t.val 0)) (w argc argv : Lir.Word)
    (mem : Lir.Memory) (hsize : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ s m, (link pre t suffix w).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link pre t suffix w).prog s (.returned [w] m) ∧
      memWord m (ctlAddr + 24) = (output pre t suffix).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (output pre t suffix) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  obtain ⟨fr, m, hx, hw, h24, h48, hbuf, hm⟩ :=
    ops_exec fits ok range w ((Lir.Frame.empty.set 1 argc).set 2 argv) mem hsize
  refine ⟨⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩, m, rfl, ?_, h24, h48, hbuf, hm⟩
  have hb : (link pre t suffix w).prog.block? 0 0 = some ⟨(ops pre t suffix w).map .op, .ret [.reg 0]⟩ := rfl
  have steps := Lir.steps_execOps (p := (link pre t suffix w).prog) (os := ops pre t suffix w)
    (s := ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  refine ⟨_, steps, ?_⟩
  have hf : (link pre t suffix w).prog.fetch ⟨0, 0, (ops pre t suffix w).length⟩ = some (.term (.ret [.reg 0])) :=
    Lir.Prog.fetch_eq_term (pt := ⟨0, 0, (ops pre t suffix w).length⟩) hb (by simp)
  have hr' : fr.regs 0 = some w := hw
  simp [Lir.step, hf, Lir.Frame.readAll, Lir.Frame.read, hr']

/-- Every machine observation agrees with the runtime expression and its format. -/
theorem link_sound {pre suffix : List UInt8} {t : IntExpr.Term} (fits : Fits pre suffix)
    (ok : t.Ok 0) (range : ConvInt.IsInt (t.val 0)) {w : Lir.Word} {a : Artifact}
    (h : artifactOf (link pre t suffix w) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) (output pre t suffix) := by
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  have hsize : (a.lmem args).size = Silmaril.Compile.Forks.CoreComp.Target.memSize := artifact_memSize h
  obtain ⟨s', m, hs', hret, h24, h48, hbuf, hm⟩ := link_returns fits ok range w
    (BitVec.ofNat 64 args.length) (BitVec.ofNat 64 a.argBase) (a.lmem args) hsize
  rw [hs] at hs'
  cases hs'
  have hroom : outBase + (output pre t suffix).length ≤ m.size := by
    have := output_length range pre suffix
    have : outBase + pre.length + 11 + suffix.length ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase := fits
    have : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
    omega
  rcases ho with ho | hstuck | ⟨b, hb', hobs⟩
  · exact .inl ho
  · cases Lir.Behaves.unique hstuck hret
  · right
    cases Lir.Behaves.unique hb' hret
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    rw [hk w rfl]
    have outEq := PrintLink.stdout_eq (items := (output pre t suffix).map Item.byte)
      (by simpa only [bytes_render] using h24) (by exact h48)
      (by simpa only [bytes_render] using hbuf) (by simpa only [bytes_render] using hroom) hout
    rw [outEq, bytes_render]

end Silmaril.Compile.Core.Verified.PrintExprLink
