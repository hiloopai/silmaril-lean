module

public import Silmaril.Compiler.Core.Verified.CfgOut.Defs
public import Silmaril.Compiler.Core.Verified.PrintStateLink.Defs
public import Silmaril.Machine.X86.Lir.LinMem.Defs

/-! # A print block of the control-flow graph

`PrintLink` writes its output in one block that starts from an empty buffer and keeps the length
in a register. A block of the control-flow graph runs any number of times, after other blocks
have printed, so its print block keeps the buffer's state in Lir's memory (`CfgOut.OutMem`):

* `prologue`: the length from control word 3 into `PrintLink.rLen`, and `PrintLink`'s constants;
* the parts (`Part.ops`): a byte as `PrintLink` writes it, or the decimal of the `int` word in a
  register below 10 (moved to `PrintLink.rVal`, then `PrintLink.decimalOps`);
* `epilogue`: the length and the buffer's address back in control words 3, 6 and 7.

`ops_exec`: from a memory that holds the output `s`, with room below the argument block for the
parts, the block ends in a memory that holds `s ++ t`, where `t`'s bytes are the parts' rendering
(`PrintLink.render`), and keeps the registers below 10 (where the graph keeps its slots). -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPrint

open Silmaril.Machine
open Spec Backend
open PrintLink (Op Item rBase rLen rPtr rOne rZero rTen rChar0 rByte rVal rFlag rAbs rPow rDig rCtl
  outBase Buf Inv inv_set itemOps decimalOps get_set_eq get_set_ne exec_const exec_store store_some
  toNat_ofNat_lt)
open PrintStateLink (dst execOps_keep exec_move split_exec)
open CfgOut (OutMem)

/-! ## The code -/

/-- What a print block writes: a byte, or the decimal of the `int` word in a register. -/
inductive Part where
  | byte (b : UInt8)
  | dec (r : Mir.Reg)

def Part.ops : Part → List Op
  | .byte b => itemOps (.byte b)
  | .dec r => .move rVal r :: decimalOps

/-- The length of the buffer from control word 3, and the constants of `PrintLink`'s code. -/
def prologue : List Op :=
  [.const rCtl (BitVec.ofNat 64 ctlAddr), .load .b8 .zero rLen rCtl 24,
    .const rBase (BitVec.ofNat 64 outBase), .const rOne (BitVec.ofNat 64 1),
    .const rZero (BitVec.ofNat 64 0), .const rTen (BitVec.ofNat 64 10),
    .const rChar0 (BitVec.ofNat 64 48)]

/-- The length and the address back in control words 3, 6 and 7. -/
def epilogue : List Op :=
  [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen, .store .b8 rCtl 48 rBase,
    .store .b8 rCtl 56 rLen]

def ops (ps : List Part) : List Op := prologue ++ ps.flatMap Part.ops ++ epilogue

/-- The parts denote the items in the frame `fr`: a decimal part's register, below 10, holds its
integer. -/
inductive Denote (fr : Lir.Frame Mir.Reg) : List Part → List Item → Prop where
  | nil : Denote fr [] []
  | byte {ps : List Part} {items : List Item} (b : UInt8) :
      Denote fr ps items → Denote fr (.byte b :: ps) (.byte b :: items)
  | dec {ps : List Part} {items : List Item} {r : Nat} {n : Int} :
      r < 10 → fr.get r = some (BitVec.ofInt 64 n) →
      Denote fr ps items → Denote fr (.dec r :: ps) (.int n :: items)

/-! ## Words of the memory -/

theorem leNat_leValue : ∀ l : List X86.Byte, leNat l = X86.Ext.leValue l
  | [] => rfl
  | b :: bs => by simp [leNat, X86.Ext.leValue, leNat_leValue bs]

/-- A word load reads the word of the memory. -/
theorem load_word {lm : Lir.Memory} {x : Nat} (hin : x + 8 ≤ lm.size) :
    lm.load .b8 .zero x = some (BitVec.ofNat 64 (memWord lm x)) := by
  unfold Lir.Memory.load
  simp only [Lir.Memory.InBounds, Lir.Width.bytes, hin, ↓reduceIte, Lir.extend]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have e := X86.Backend.readLE_toNat lm.bytes 8 x (by norm_num)
  have hlt := (Lir.readLE lm.bytes x 8).isLt
  rw [BitVec.toNat_ofNat, e, memWord, leNat_leValue]
  rw [e] at hlt
  exact (Nat.mod_eq_of_lt hlt).symm

theorem exec_load {w : Lir.Width} {e : Lir.Ext} {d base : Mir.Reg} {off : Nat} {a z : Lir.Word}
    (os : List Op) {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} (ha : fr.get base = some a)
    (hz : m.load w e (a.toNat + off) = some z) :
    Lir.execOps (.load w e d base off :: os) fr m = Lir.execOps os (fr.set d z) m := by
  simp [Lir.execOps_cons, Lir.Op.exec, ha, hz]

/-! ## Running the code -/

/-- A part writes only registers from 10 on. -/
theorem Part.dst_ge (p : Part) : ∀ o ∈ p.ops, ∀ d : Nat, dst o = some d → 10 ≤ d := by
  have hdec : decimalOps.all (fun o => match dst o with | some d => decide (10 ≤ d) | none => true) =
      true := by decide
  intro o ho d hd
  cases p with
  | byte b =>
    simp only [Part.ops, itemOps, PrintLink.emit, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;>
      first | (simp only [dst, Option.some.injEq] at hd; subst hd; decide) | simp [dst] at hd
  | dec r =>
    simp only [Part.ops, List.mem_cons] at ho
    rcases ho with rfl | ho
    · simp only [dst, Option.some.injEq] at hd; subst hd; decide
    · have := List.all_eq_true.mp hdec o ho
      rw [hd] at this
      simpa using this

theorem Part.keeps (p : Part) {r : Nat} (hr : r < 10) :
    (p.ops.all fun o => dst o != some r) = true := by
  apply List.all_eq_true.mpr
  intro o ho
  simp only [bne_iff_ne, ne_eq]
  intro e
  have := p.dst_ge o ho r e
  omega

/-- **The parts**, from the buffer holding `out`: the buffer holds `out` and the items, and the
registers below 10 are kept. -/
theorem parts_exec {fr0 : Lir.Frame Mir.Reg} :
    ∀ {ps : List Part} {items : List Item}, Denote fr0 ps items → (∀ it ∈ items, it.small = true) →
    ∀ {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}, Inv Silmaril.Compile.Forks.CoreComp.Target.memSize fr m out →
    (∀ r : Nat, r < 10 → fr.get r = fr0.get r) →
    outBase + out.length + (items.map Item.room).sum ≤ Silmaril.Compile.Forks.CoreComp.Target.memSize → ∀ (os : List Op),
    ∃ fr' m', Lir.execOps (ps.flatMap Part.ops ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv Silmaril.Compile.Forks.CoreComp.Target.memSize fr' m' (out ++ PrintLink.render items) ∧
      ∀ r : Nat, r < 10 → fr'.get r = fr0.get r
  | [], [], .nil, _, fr, m, out, inv, keep, _, os => ⟨fr, m, rfl, by simpa [PrintLink.render] using inv, keep⟩
  | .byte b :: ps, .byte _ :: items, .byte _ den, small, fr, m, out, inv, keep, room, os => by
    have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
    simp only [List.map_cons, List.sum_cons, Item.room] at room
    obtain ⟨fr1, m1, hx, inv1⟩ := PrintLink.byte_exec inv (by omega) hs b []
    obtain ⟨-, hx1⟩ := split_exec hx []
    have keep1 : ∀ r : Nat, r < 10 → fr1.get r = fr0.get r := fun r hr =>
      (execOps_keep _ hx1 ((Part.byte b).keeps hr)).trans (keep r hr)
    obtain ⟨fr2, m2, hx2, inv2, keep2⟩ := parts_exec den
      (fun it h => small it (List.mem_cons_of_mem _ h)) inv1 keep1 (by simp; omega) os
    refine ⟨fr2, m2, ?_, by simpa [PrintLink.render, Item.render, List.append_assoc] using inv2, keep2⟩
    rw [List.flatMap_cons, List.append_assoc, Part.ops, (split_exec hx _).1]
    exact hx2
  | .dec r :: ps, .int n :: items, .dec hr hv den, small, fr, m, out, inv, keep, room, os => by
    have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
    simp only [List.map_cons, List.sum_cons, Item.room] at room
    have hn : n.natAbs < 10 ^ 10 := by
      simpa [Item.small] using small _ List.mem_cons_self
    have inv1 := inv_set inv (r := rVal) (by decide) (BitVec.ofInt 64 n)
    obtain ⟨fr1, m1, hx, inv1'⟩ := PrintLink.decimal_exec inv1 (by omega) hs hn (get_set_eq _ _ _) []
    obtain ⟨-, hx1⟩ := split_exec hx []
    have hget : fr.get r = some (BitVec.ofInt 64 n) := (keep r hr).trans hv
    have keep1 : ∀ q : Nat, q < 10 → fr1.get q = fr0.get q := fun q hq => by
      have := execOps_keep _ hx1 (r := q) (by
        have := (Part.dec r).keeps hq
        simp only [Part.ops, List.all_cons, Bool.and_eq_true] at this
        exact this.2)
      have hq' : q ≠ rVal := by unfold rVal; omega
      rw [this, get_set_ne _ hq']
      exact keep q hq
    have hlen := PrintLink.render_int_length n hn
    obtain ⟨fr2, m2, hx2, inv2, keep2⟩ := parts_exec den
      (fun it h => small it (List.mem_cons_of_mem _ h)) inv1' keep1 (by simp; omega) os
    refine ⟨fr2, m2, ?_, by simpa [PrintLink.render, List.append_assoc] using inv2, keep2⟩
    rw [List.flatMap_cons, List.append_assoc, Part.ops, List.cons_append, exec_move _ hget,
      (split_exec hx _).1]
    exact hx2

theorem coreBytes_append (s t : String) : coreBytes (s ++ t) = coreBytes s ++ coreBytes t := by
  simp [coreBytes]

/-- **A print block.** From a memory that holds the output `s`, with room below the argument
block for the items the parts denote, the block ends in a memory that holds `s ++ t`, where `t`'s
bytes are the items' rendering, and keeps the registers below 10. -/
theorem ops_exec {ps : List Part} {items : List Item} {fr : Lir.Frame Mir.Reg} {mem : Lir.Memory}
    {s t : String} (h : OutMem mem s) (den : Denote fr ps items)
    (small : ∀ it ∈ items, it.small = true)
    (room : outBase + (coreBytes s).length + (items.map Item.room).sum ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (ht : coreBytes t = PrintLink.render items) :
    ∃ fr' mem', Lir.execOps (ops ps) fr mem = some (fr', mem') ∧ OutMem mem' (s ++ t) ∧
      ∀ r : Nat, r < 10 → fr'.get r = fr.get r := by
  obtain ⟨buf, h24, -⟩ := h.toBuf
  have hsize := h.size
  have hab : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
  let L := (coreBytes s).length
  have hc : (BitVec.ofNat 64 ctlAddr).toNat = ctlAddr := by decide
  have hload : mem.load .b8 .zero ((BitVec.ofNat 64 ctlAddr).toNat + 24) = some (BitVec.ofNat 64 L) := by
    rw [hc, load_word (by rw [hsize]; decide), h24]
  let fr1 := ((((((fr.set rCtl (BitVec.ofNat 64 ctlAddr)).set rLen (BitVec.ofNat 64 L)).set rBase
    (BitVec.ofNat 64 outBase)).set rOne (BitVec.ofNat 64 1)).set rZero (BitVec.ofNat 64 0)).set rTen
    (BitVec.ofNat 64 10)).set rChar0 (BitVec.ofNat 64 48)
  have hx1 (rest : List Op) : Lir.execOps (prologue ++ rest) fr mem = Lir.execOps rest fr1 mem := by
    simp only [prologue, List.cons_append, List.nil_append]
    rw [exec_const, exec_load _ (get_set_eq _ _ _) hload]
    rfl
  have inv1 : Inv Silmaril.Compile.Forks.CoreComp.Target.memSize fr1 mem (coreBytes s) := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, buf, hsize⟩ <;>
      simp [fr1, L, rBase, rLen, rOne, rZero, rTen, rChar0, rCtl]
  have keep1 : ∀ r : Nat, r < 10 → fr1.get r = fr.get r := by
    intro r hr
    have h1 : r ≠ rChar0 := by unfold rChar0; omega
    have h2 : r ≠ rTen := by unfold rTen; omega
    have h3 : r ≠ rZero := by unfold rZero; omega
    have h4 : r ≠ rOne := by unfold rOne; omega
    have h5 : r ≠ rBase := by unfold rBase; omega
    have h6 : r ≠ rLen := by unfold rLen; omega
    have h7 : r ≠ rCtl := by unfold rCtl; omega
    simp [fr1, h1, h2, h3, h4, h5, h6, h7]
  have hsum : outBase + (coreBytes s).length + (items.map Item.room).sum ≤ Silmaril.Compile.Forks.CoreComp.Target.memSize := by omega
  obtain ⟨fr2, m2, hx2, inv2, keep2⟩ := parts_exec den small inv1 keep1 hsum epilogue
  have hlen := PrintLink.render_length items small
  let out := coreBytes s ++ PrintLink.render items
  have hL : out.length < 2 ^ 64 := by simp only [out, List.length_append]; omega
  have hroom : outBase + out.length ≤ Silmaril.Compile.Forks.CoreComp.Target.memSize := by simp only [out, List.length_append]; omega
  let fr3 := fr2.set rCtl (BitVec.ofNat 64 ctlAddr)
  have hctl : fr3.get rCtl = some (BitVec.ofNat 64 ctlAddr) := get_set_eq _ _ _
  have hlen3 : fr3.get rLen = some (BitVec.ofNat 64 out.length) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.len
  have hbase3 : fr3.get rBase = some (BitVec.ofNat 64 outBase) := by
    rw [get_set_ne _ (by decide)]; exact inv2.regs.base
  have hsz2 := inv2.size
  let m3 : Lir.Memory := ⟨m2.size, Lir.writeLE m2.bytes (ctlAddr + 24) 8 (BitVec.ofNat 64 out.length)⟩
  have hst3 : m2.store .b8 (ctlAddr + 24) (BitVec.ofNat 64 out.length) = some m3 := by
    rw [store_some (by simp [Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m4 : Lir.Memory := ⟨m3.size, Lir.writeLE m3.bytes (ctlAddr + 48) 8 (BitVec.ofNat 64 outBase)⟩
  have hst4 : m3.store .b8 (ctlAddr + 48) (BitVec.ofNat 64 outBase) = some m4 := by
    rw [store_some (by simp [m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  let m5 : Lir.Memory := ⟨m4.size, Lir.writeLE m4.bytes (ctlAddr + 56) 8 (BitVec.ofNat 64 out.length)⟩
  have hst5 : m4.store .b8 (ctlAddr + 56) (BitVec.ofNat 64 out.length) = some m5 := by
    rw [store_some (by simp [m4, m3, Lir.Width.bytes, hsz2, ctlAddr, Silmaril.Compile.Forks.CoreComp.Target.memSize])]; rfl
  have hsz5 : m5.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by simp [m5, m4, m3, hsz2]
  refine ⟨fr3, m5, ?_, ?_, ?_⟩
  · rw [ops, List.append_assoc, hx1, hx2, epilogue, exec_const,
      exec_store _ hctl hlen3 (by rw [hc]; exact hst3),
      exec_store _ hctl hbase3 (by rw [hc]; exact hst4),
      exec_store _ hctl hlen3 (by rw [hc]; exact hst5)]
    rfl
  · have hout : coreBytes (s ++ t) = out := by rw [coreBytes_append, ht]
    apply CfgOut.ofBuf
    · rw [hout, PrintLink.memWord_outside hst5 (by left; decide),
        PrintLink.memWord_outside hst4 (by left; decide), PrintLink.memWord_store hst3, toNat_ofNat_lt hL]
    · rw [PrintLink.memWord_outside hst5 (by left; decide), PrintLink.memWord_store hst4,
        toNat_ofNat_lt (by decide)]
    · rw [hout]
      intro i hi
      rw [PrintLink.store_bytes_outside hst5 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
        PrintLink.store_bytes_outside hst4 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega),
        PrintLink.store_bytes_outside hst3 (by right; simp only [Lir.Width.bytes, outBase, ctlAddr]; omega)]
      exact inv2.buf i hi
    · rw [hout, hsz5]; exact hroom
    · exact hsz5
  · intro r hr
    have h7 : r ≠ rCtl := by unfold rCtl; omega
    rw [get_set_ne _ h7, keep2 r hr]

end Silmaril.Compile.Core.Verified.CfgPrint
