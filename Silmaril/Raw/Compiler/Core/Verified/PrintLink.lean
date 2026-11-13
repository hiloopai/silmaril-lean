module

public import Silmaril.Compiler.Core.Verified.ConstLink.Defs

/-! # The link of a `main` that writes output and returns a constant

Compiled programs make no system calls: the startup code writes the output buffer that the
control block names (word 6 its address, word 3 its length) when `__ccomp_start` returns
(`Spec.observe`, `Target.Runtime`). `link items w` is the whole linked program of a `main` that
writes `items`, then returns the word `w`: one Lir function, `__ccomp_start`, whose single block

* sets up the buffer at `outBase` (just after the control block) with length 0 in a register;
* writes each item at run time: a byte (`Item.byte`), or the decimal digits of a signed integer
  (`Item.int`, `%d`), computed by the machine code from the integer's word with unsigned
  division and remainder by the powers of ten (no branch: each digit is stored at the end of the
  buffer and the length advances by the flag `value ≥ 10ⁱ`, so a digit that is not part of the
  number is overwritten by the next one);
* stores the length and the buffer's address in control words 3 and 6, and the length again in
  word 7 (the buffer's capacity, at which crt0 caps what it writes; `Spec.observe` does not
  read it, so the link makes the cap harmless), and returns `w`.

`link_sound`: when the items fit in the linear memory (`Fits`), every observation of the artifact
of `link items w` is exhaustion or `exit (w mod 256) (render items)`, where `render` is the
output of Cerberus's `printf`: the byte itself, or the characters of `toString n` (`Int.repr`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintLink

open Silmaril.Machine
open Spec Backend

/-! ## The code -/

/-- The output buffer: just after the control block (`Target.Runtime`'s map puts data objects
there; these links have none). -/
def outBase : Nat := ctlAddr + 64

/-- What `main` writes: one byte, or the decimal digits of an integer (`printf`'s `%d`). -/
inductive Item where
  | byte (b : UInt8)
  | int (n : Int)
  deriving DecidableEq, Repr

/-- The output of an item: Cerberus's `printf` appends the characters of `toString n` for `%d`. -/
def Item.render : Item → List UInt8
  | .byte b => [b]
  | .int n => (toString n).toList.map fun c => c.toNat.toUInt8

def render (items : List Item) : List UInt8 := items.flatMap Item.render

/-- The registers of the generated code. -/
def rBase : Mir.Reg := 10
def rLen : Mir.Reg := 11
def rPtr : Mir.Reg := 12
def rOne : Mir.Reg := 13
def rZero : Mir.Reg := 14
def rTen : Mir.Reg := 15
def rChar0 : Mir.Reg := 16
def rByte : Mir.Reg := 17
def rVal : Mir.Reg := 18
def rFlag : Mir.Reg := 19
def rAbs : Mir.Reg := 20
def rPow : Mir.Reg := 21
def rDig : Mir.Reg := 22
def rCtl : Mir.Reg := 23

abbrev Op := Lir.Op Mir.Reg

/-- Store the byte in `rb` at the end of the buffer, then add the flag in `rf` (0 or 1) to the
length. -/
def emit (rb rf : Mir.Reg) : List Op :=
  [.binary .add rPtr rBase rLen, .store .b1 rPtr 0 rb, .binary .add rLen rLen rf]

/-- The buffer at `outBase`, empty, and the constants of the code. -/
def prologue : List Op :=
  [.const rBase (BitVec.ofNat 64 outBase), .const rLen (BitVec.ofNat 64 0), .const rOne (BitVec.ofNat 64 1),
    .const rZero (BitVec.ofNat 64 0), .const rTen (BitVec.ofNat 64 10), .const rChar0 (BitVec.ofNat 64 48)]

/-- The digit of `10ⁱ` of the absolute value in `rAbs`, counted when the value is at least `10ⁱ`. -/
def digitOps (i : Nat) : List Op :=
  [.const rPow (BitVec.ofNat 64 (10 ^ i)), .binary .divu rDig rAbs rPow, .binary .remu rDig rDig rTen,
    .binary .add rDig rDig rChar0, .binary (.cmp .geu) rFlag rAbs rPow] ++ emit rDig rFlag

/-- The digits of `10ᵏ`, …, `10¹`. -/
def digitsOps : Nat → List Op
  | 0 => []
  | k + 1 => digitOps (k + 1) ++ digitsOps k

/-- The decimal of the integer word in `rVal` (at most ten digits): a minus sign counted when it is
negative, its absolute value, then its digits, the last one always counted. -/
def decimalOps : List Op :=
  [.binary (.cmp .lts) rFlag rVal rZero, .const rByte (BitVec.ofNat 64 45)] ++ emit rByte rFlag ++
  [.binary .mul rAbs rVal rFlag, .binary .add rAbs rAbs rAbs, .binary .sub rAbs rVal rAbs] ++
  digitsOps 9 ++ [.binary .remu rDig rAbs rTen, .binary .add rDig rDig rChar0] ++ emit rDig rOne

def itemOps : Item → List Op
  | .byte b => .const rByte (BitVec.ofNat 64 b.toNat) :: emit rByte rOne
  | .int n => .const rVal (BitVec.ofInt 64 n) :: decimalOps

/-- The whole block before the return: the prologue, the items, the control words, `r0 := w`. -/
def ops (items : List Item) (w : Lir.Word) : List Op :=
  prologue ++ items.flatMap itemOps ++
    [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen, .store .b8 rCtl 48 rBase,
      .store .b8 rCtl 56 rLen, .const 0 w]

/-- `__ccomp_start(argc, argv)`: write the items, return `w`. -/
def startFunc (items : List Item) (w : Lir.Word) : Lir.Func Mir.Reg :=
  { params := [.reg 1, .reg 2], entry := 0, blocks := [⟨(ops items w).map .op, .ret [.reg 0]⟩] }

/-- The linked program of a `main` that writes `items` and returns `w`. -/
def link (items : List Item) (w : Lir.Word) : Mir.Linked where
  prog := ⟨[startFunc items w]⟩
  funcs := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.startSymbol 0
  data := (∅ : Std.HashMap Mir.Symbol Nat).insert Silmaril.Compile.Forks.CoreComp.Target.ctlSymbol ctlAddr
  dataBase := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  dataEnd := Silmaril.Compile.Forks.CoreComp.Target.dataBase
  image := .empty

/-- At most how many bytes an item writes beyond the length it counts. -/
def Item.room : Item → Nat
  | .byte _ => 1
  | .int _ => 11

/-- An integer item has at most ten digits. -/
def Item.small : Item → Bool
  | .byte _ => true
  | .int n => decide (n.natAbs < 10 ^ 10)

/-- The items fit: their integers have at most ten digits, and their output fits below the
argument block. -/
def Fits (items : List Item) : Prop :=
  (∀ it ∈ items, it.small = true) ∧ outBase + (items.map Item.room).sum ≤ Silmaril.Compile.Forks.CoreComp.Target.argBase

theorem Fits.int {items : List Item} (h : Fits items) {n : Int} (hn : Item.int n ∈ items) :
    n.natAbs < 10 ^ 10 := by
  simpa [Item.small] using h.1 _ hn

instance (items : List Item) : Decidable (Fits items) := by
  unfold Fits; infer_instance

/-! ## Words -/

section Words

theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem udiv_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a / BitVec.ofNat 64 b = BitVec.ofNat 64 (a / b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofNat_lt ha, toNat_ofNat_lt hb,
    toNat_ofNat_lt (lt_of_le_of_lt (Nat.div_le_self a b) ha)]

theorem umod_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a % BitVec.ofNat 64 b = BitVec.ofNat 64 (a % b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, toNat_ofNat_lt ha, toNat_ofNat_lt hb,
    toNat_ofNat_lt (lt_of_le_of_lt (Nat.mod_le a b) ha)]

theorem ofNat_ne_zero {a : Nat} (ha : a < 2 ^ 64) (h : 0 < a) : BitVec.ofNat 64 a ≠ 0 := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [toNat_ofNat_lt ha] at this
  simp at this
  omega

theorem divu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : 0 < b) :
    Lir.Binop.eval .divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = some (BitVec.ofNat 64 (a / b)) := by
  simp only [Lir.Binop.eval, Lir.divOp, ofNat_ne_zero hb h, Bool.false_eq_true,
    ↓reduceIte, udiv_ofNat ha hb]

theorem remu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : 0 < b) :
    Lir.Binop.eval .remu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = some (BitVec.ofNat 64 (a % b)) := by
  simp only [Lir.Binop.eval, Lir.divOp, ofNat_ne_zero hb h, Bool.false_eq_true,
    ↓reduceIte, umod_ofNat ha hb]

theorem geu_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Lir.Binop.eval (.cmp .geu) (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      some (BitVec.ofNat 64 (if b ≤ a then 1 else 0)) := by
  simp only [Lir.Binop.eval, Lir.Cond.eval, toNat_ofNat_lt ha, toNat_ofNat_lt hb, Lir.ofBool]
  by_cases h : b ≤ a <;> simp [h]

/-- The sign test of an integer word. -/
theorem lts_ofInt {n : Int} (h : n.natAbs < 2 ^ 63) :
    Lir.Binop.eval (.cmp .lts) (BitVec.ofInt 64 n) (BitVec.ofNat 64 0) =
      some (BitVec.ofNat 64 (if n < 0 then 1 else 0)) := by
  have ht : (BitVec.ofInt 64 n).toInt = n := by
    rw [BitVec.toInt_ofInt, Int.bmod_eq_emod]
    split <;> omega
  have hz : (BitVec.ofNat 64 0).toInt = 0 := by decide
  simp only [Lir.Binop.eval, Lir.Cond.eval, Lir.ofBool, ht, hz]
  by_cases hn : n < 0 <;> simp [hn]

/-- `v - 2·v·flag` is the absolute value. -/
theorem abs_ofInt {n : Int} (h : n.natAbs < 2 ^ 63) :
    BitVec.ofInt 64 n - (BitVec.ofInt 64 n * BitVec.ofNat 64 (if n < 0 then 1 else 0) +
      BitVec.ofInt 64 n * BitVec.ofNat 64 (if n < 0 then 1 else 0)) = BitVec.ofNat 64 n.natAbs := by
  apply BitVec.eq_of_toNat_eq
  by_cases hn : n < 0
  · simp only [hn, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega
  · simp only [hn, ↓reduceIte, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul,
      BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    omega

end Words

/-! ## Decimal digits -/

section Digits

/-- The digits of `10ᵏ`, …, `10¹` of `a` that are part of its decimal representation. -/
def digs : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, a => (if 10 ^ (k + 1) ≤ a then [a / 10 ^ (k + 1) % 10] else []) ++ digs k a

theorem digs_succ (k a : Nat) :
    digs (k + 1) a = if 10 ≤ a then digs k (a / 10) ++ [a / 10 % 10] else [] := by
  induction k with
  | zero => simp [digs]
  | succ k ih =>
    rw [digs, ih]
    by_cases h : 10 ≤ a
    · have hle : 10 ^ (k + 2) ≤ a ↔ 10 ^ (k + 1) ≤ a / 10 := by
        rw [Nat.le_div_iff_mul_le (by decide), pow_succ]
      have hdiv : a / 10 ^ (k + 2) = a / 10 / 10 ^ (k + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      simp only [h, ite_true, digs, hle, hdiv, List.append_assoc]
    · have : ¬ 10 ^ (k + 2) ≤ a := by
        have : 10 ≤ 10 ^ (k + 2) := Nat.le_self_pow (by omega) 10 |>.trans' (by norm_num)
        omega
      simp [h, this]

/-- The decimal digits of `a < 10ᵏ⁺¹`. -/
theorem digs_toDigits : ∀ (k a : Nat), a < 10 ^ (k + 1) →
    (digs k a ++ [a % 10]).map Nat.digitChar = Nat.toDigits 10 a
  | 0, a, h => by
    simp only [digs, List.nil_append, List.map_cons, List.map_nil]
    rw [Nat.toDigits_of_lt_base (by simpa using h), Nat.mod_eq_of_lt (by simpa using h)]
  | k + 1, a, h => by
    rw [digs_succ, Nat.toDigits_eq_ite (by decide)]
    by_cases ha : 10 ≤ a
    · have hlt : a / 10 < 10 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        rw [pow_succ] at h
        exact h
      rw [ite_pos ha, ite_neg (by omega), ← digs_toDigits k (a / 10) hlt]
      simp
    · rw [ite_neg ha, ite_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      simp

/-- The characters of `toString n`: a minus sign when `n` is negative, then the digits of `|n|`. -/
theorem toString_int (n : Int) :
    (toString n).toList = (if n < 0 then ['-'] else []) ++ Nat.toDigits 10 n.natAbs := by
  show (Int.repr n).toList = _
  rw [Int.repr_eq_ite]
  by_cases hn : 0 ≤ n
  · rw [ite_pos hn, ite_neg (by omega), Nat.toList_repr]
    simp only [List.nil_append]
    congr 1
    omega
  · rw [ite_neg hn, ite_pos (by omega)]
    simp only [String.toList_append, Nat.toList_repr]
    congr 2
    omega

theorem digitChar_byte {d : Nat} (h : d < 10) :
    (Nat.digitChar d).toNat.toUInt8 = (d + 48).toUInt8 := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Nat.digitChar_eq_zero.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_one.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_two.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_three.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_four.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_five.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_six.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_seven.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_eight.mpr rfl]; rfl
  · rw [Nat.digitChar_eq_nine.mpr rfl]; rfl

end Digits

/-! ## Running the code -/

section Run

/-! ### One operation at a time -/

theorem get_set_eq (fr : Lir.Frame Mir.Reg) (r : Mir.Reg) (w : Lir.Word) :
    (fr.set r w).get r = some w := by simp

theorem get_set_ne (fr : Lir.Frame Mir.Reg) {r r' : Mir.Reg} (h : r' ≠ r) (w : Lir.Word) :
    (fr.set r w).get r' = fr.get r' := by simp [h]

theorem exec_const (d : Mir.Reg) (v : Lir.Word) (os : List Op) (fr : Lir.Frame Mir.Reg)
    (m : Lir.Memory) : Lir.execOps (.const d v :: os) fr m = Lir.execOps os (fr.set d v) m := rfl

theorem exec_binary {op : Lir.Binop} {d a b : Mir.Reg} {x y z : Lir.Word} (os : List Op)
    {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} (ha : fr.get a = some x) (hb : fr.get b = some y)
    (he : op.eval x y = some z) :
    Lir.execOps (.binary op d a b :: os) fr m = Lir.execOps os (fr.set d z) m := by
  simp [Lir.execOps_cons, Lir.Op.exec, ha, hb, he]

theorem exec_store {w : Lir.Width} {base src : Mir.Reg} {off : Nat} {a x : Lir.Word}
    (os : List Op) {fr : Lir.Frame Mir.Reg} {m m' : Lir.Memory} (ha : fr.get base = some a)
    (hx : fr.get src = some x) (hm : m.store w (a.toNat + off) x = some m') :
    Lir.execOps (.store w base off src :: os) fr m = Lir.execOps os fr m' := by
  simp [Lir.execOps_cons, Lir.Op.exec, ha, hx, hm]

theorem store_some {m : Lir.Memory} {w : Lir.Width} {addr : Nat} (h : addr + w.bytes ≤ m.size)
    (v : Lir.Word) : m.store w addr v = some ⟨m.size, Lir.writeLE m.bytes addr w.bytes v⟩ := by
  simp only [Lir.Memory.store, Lir.Memory.InBounds, h, ↓reduceIte]

theorem add_ofNat (a b : Nat) :
    Lir.Binop.eval .add (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = some (BitVec.ofNat 64 (a + b)) := by
  simp only [Lir.Binop.eval, ofNat_add]

theorem wordByte_ofNat (b : Nat) :
    LittleEndian.wordByte (BitVec.ofNat 64 b) 0 = BitVec.ofNat 8 (b.toUInt8).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [LittleEndian.wordByte, Nat.toUInt8]

/-! ### The buffer -/

/-- The output buffer at `outBase` holds `out`. -/
def Buf (m : Lir.Memory) (out : List UInt8) : Prop :=
  ∀ i (h : i < out.length), m.bytes (outBase + i) = BitVec.ofNat 8 out[i].toNat

/-- What the code keeps in its registers while it writes: the buffer, its length and the
constants. -/
structure Regs (fr : Lir.Frame Mir.Reg) (len : Nat) : Prop where
  base : fr.get rBase = some (BitVec.ofNat 64 outBase)
  len : fr.get rLen = some (BitVec.ofNat 64 len)
  one : fr.get rOne = some (BitVec.ofNat 64 1)
  zero : fr.get rZero = some (BitVec.ofNat 64 0)
  ten : fr.get rTen = some (BitVec.ofNat 64 10)
  char0 : fr.get rChar0 = some (BitVec.ofNat 64 48)

/-- The memory has size `size` and the buffer holds `out`. -/
structure Inv (size : Nat) (fr : Lir.Frame Mir.Reg) (m : Lir.Memory) (out : List UInt8) : Prop where
  regs : Regs fr out.length
  buf : Buf m out
  size : m.size = size

/-- A register the invariant does not name. -/
def Free (r : Mir.Reg) : Prop :=
  r ≠ rBase ∧ r ≠ rLen ∧ r ≠ rOne ∧ r ≠ rZero ∧ r ≠ rTen ∧ r ≠ rChar0

instance (r : Mir.Reg) : Decidable (Free r) := by unfold Free; infer_instance

theorem inv_set {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) {r : Mir.Reg} (hr : Free r) (w : Lir.Word) :
    Inv size (fr.set r w) m out := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, buf, size⟩ := inv
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hr
  exact ⟨⟨by rw [get_set_ne _ (Ne.symm n1)]; exact h1, by rw [get_set_ne _ (Ne.symm n2)]; exact h2,
    by rw [get_set_ne _ (Ne.symm n3)]; exact h3, by rw [get_set_ne _ (Ne.symm n4)]; exact h4,
    by rw [get_set_ne _ (Ne.symm n5)]; exact h5, by rw [get_set_ne _ (Ne.symm n6)]; exact h6⟩,
    buf, size⟩

/-- **Writing one byte.** The byte in `rb` is stored at the end of the buffer; when `c` holds
(the flag in `rf` is 1) it is counted. Only `rPtr`, `rLen` and the memory change. -/
theorem emit_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (room : outBase + out.length + 1 ≤ size) (hs : size < 2 ^ 64)
    {rb rf : Mir.Reg} {b : Nat} {c : Prop} [Decidable c]
    (hrb : fr.get rb = some (BitVec.ofNat 64 b))
    (hrf : fr.get rf = some (BitVec.ofNat 64 (if c then 1 else 0)))
    (hb : rb ≠ rPtr) (hf : rf ≠ rPtr) (os : List Op) :
    ∃ fr' m', Lir.execOps (emit rb rf ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (if c then out ++ [b.toUInt8] else out) ∧
      ∀ r, r ≠ rPtr → r ≠ rLen → fr'.get r = fr.get r := by
  obtain ⟨regs, buf, hsize⟩ := inv
  let L := out.length
  have hp : (BitVec.ofNat 64 (outBase + L)).toNat + 0 = outBase + L := by
    rw [toNat_ofNat_lt (by omega)]; rfl
  let m1 : Lir.Memory := ⟨m.size, Lir.writeLE m.bytes (outBase + L) 1 (BitVec.ofNat 64 b)⟩
  have hst : m.store .b1 ((BitVec.ofNat 64 (outBase + L)).toNat + 0) (BitVec.ofNat 64 b) = some m1 := by
    rw [hp, store_some (by simp only [Lir.Width.bytes]; omega)]; rfl
  let fr1 := fr.set rPtr (BitVec.ofNat 64 (outBase + L))
  let out' := if c then out ++ [b.toUInt8] else out
  have hlen' : L + (if c then 1 else 0) = out'.length := by
    by_cases hc : c <;> simp [out', L, hc]
  refine ⟨fr1.set rLen (BitVec.ofNat 64 out'.length), m1, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp only [emit, List.cons_append, List.nil_append]
    rw [exec_binary _ regs.base regs.len (add_ofNat _ _),
      exec_store _ (get_set_eq _ _ _) (by rw [get_set_ne _ hb]; exact hrb) hst,
      exec_binary _ (by rw [get_set_ne _ (by decide)]; exact regs.len)
        (by rw [get_set_ne _ hf]; exact hrf) (by rw [add_ofNat, hlen'])]
  · rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact regs.base
  · exact get_set_eq _ _ _
  · rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact regs.one
  · rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact regs.zero
  · rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact regs.ten
  · rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact regs.char0
  · intro i hi
    show Lir.writeLE m.bytes (outBase + L) 1 (BitVec.ofNat 64 b) (outBase + i) = _
    simp only [Lir.writeLE]
    by_cases hlt : i < L
    · rw [ite_neg (by omega), buf i hlt]
      congr 2
      by_cases hc : c
      · simp only [hc, ↓reduceIte, List.getElem_append_left hlt]
      · simp only [hc, ↓reduceIte]
    · have hc : c := by
        by_contra hc
        simp only [hc, ↓reduceIte] at hi
        omega
      have hi' : i = L := by simp [hc] at hi; omega
      subst hi'
      rw [ite_pos (by omega), Nat.sub_self, wordByte_ofNat]
      congr 2
      simp [hc, L]
  · exact hsize
  · intro r h1 h2
    rw [get_set_ne _ h2, get_set_ne _ h1]

/-- The prologue sets up an empty buffer, from any frame. -/
theorem prologue_exec (fr : Lir.Frame Mir.Reg) (m : Lir.Memory) (os : List Op) :
    ∃ fr', Lir.execOps (prologue ++ os) fr m = Lir.execOps os fr' m ∧ Inv m.size fr' m [] := by
  refine ⟨_, rfl, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun i h => absurd h (by simp), rfl⟩⟩ <;>
    simp [rBase, rLen, rOne, rZero, rTen, rChar0]

/-- **Writing a byte.** -/
theorem byte_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (room : outBase + out.length + 1 ≤ size) (hs : size < 2 ^ 64)
    (b : UInt8) (os : List Op) :
    ∃ fr' m', Lir.execOps (itemOps (.byte b) ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ [b]) := by
  have inv1 := inv_set inv (r := rByte) (by decide) (BitVec.ofNat 64 b.toNat)
  obtain ⟨fr', m', hx, inv', -⟩ := emit_exec inv1 room hs (rb := rByte) (rf := rOne) (b := b.toNat)
    (c := True) (get_set_eq _ _ _) (by rw [get_set_ne _ (by decide)]; exact inv.regs.one)
    (by decide) (by decide) os
  refine ⟨fr', m', ?_, by simpa using inv'⟩
  rw [itemOps, List.cons_append, exec_const]
  exact hx

/-- The digit of `10ⁱ` of the value `a` in `rAbs`, counted when `a ≥ 10ⁱ`. -/
theorem digitOps_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (room : outBase + out.length + 1 ≤ size) (hs : size < 2 ^ 64)
    {a i : Nat} (ha : a < 2 ^ 63) (hi : 10 ^ i < 2 ^ 63)
    (habs : fr.get rAbs = some (BitVec.ofNat 64 a)) (os : List Op) :
    ∃ fr' m', Lir.execOps (digitOps i ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ if 10 ^ i ≤ a then [(a / 10 ^ i % 10 + 48).toUInt8] else []) ∧
      fr'.get rAbs = some (BitVec.ofNat 64 a) := by
  have hpos : 0 < 10 ^ i := Nat.pow_pos (by decide)
  have hd : a / 10 ^ i < 2 ^ 63 := lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hd10 : a / 10 ^ i % 10 < 10 := Nat.mod_lt _ (by decide)
  let fr1 := fr.set rPow (BitVec.ofNat 64 (10 ^ i))
  let fr2 := fr1.set rDig (BitVec.ofNat 64 (a / 10 ^ i))
  let fr3 := fr2.set rDig (BitVec.ofNat 64 (a / 10 ^ i % 10))
  let fr4 := fr3.set rDig (BitVec.ofNat 64 (a / 10 ^ i % 10 + 48))
  let fr5 := fr4.set rFlag (BitVec.ofNat 64 (if 10 ^ i ≤ a then 1 else 0))
  have inv5 : Inv size fr5 m out :=
    inv_set (inv_set (inv_set (inv_set (inv_set inv (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  have hab1 : fr1.get rAbs = some (BitVec.ofNat 64 a) := by
    rw [get_set_ne _ (by decide)]; exact habs
  have hab4 : fr4.get rAbs = some (BitVec.ofNat 64 a) := by
    rw [get_set_ne _ (by decide), get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact hab1
  have hpow4 : fr4.get rPow = some (BitVec.ofNat 64 (10 ^ i)) := by
    rw [get_set_ne _ (by decide), get_set_ne _ (by decide), get_set_ne _ (by decide)]
    exact get_set_eq _ _ _
  obtain ⟨fr', m', hx, inv', keep⟩ := emit_exec inv5 room hs (rb := rDig) (rf := rFlag)
    (b := a / 10 ^ i % 10 + 48) (c := 10 ^ i ≤ a)
    (by rw [get_set_ne _ (by decide)]; exact get_set_eq _ _ _) (get_set_eq _ _ _)
    (by decide) (by decide) os
  have e : (if 10 ^ i ≤ a then out ++ [(a / 10 ^ i % 10 + 48).toUInt8] else out) =
      out ++ if 10 ^ i ≤ a then [(a / 10 ^ i % 10 + 48).toUInt8] else [] := by
    split <;> simp
  refine ⟨fr', m', ?_, e ▸ inv', ?_⟩
  · simp only [digitOps, List.cons_append, List.append_assoc]
    rw [exec_const,
      exec_binary _ hab1 (get_set_eq _ _ _) (divu_ofNat (by omega) (by omega) hpos),
      exec_binary _ (get_set_eq _ _ _)
        (by rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact inv.regs.ten)
        (remu_ofNat (by omega) (by decide) (by decide)),
      exec_binary _ (get_set_eq _ _ _)
        (by rw [get_set_ne _ (by decide), get_set_ne _ (by decide), get_set_ne _ (by decide)]
            exact inv.regs.char0)
        (add_ofNat _ _),
      exec_binary _ hab4 hpow4 (geu_ofNat (by omega) (by omega))]
    exact hx
  · rw [keep rAbs (by decide) (by decide), get_set_ne _ (by decide)]
    exact hab4

theorem digs_length : ∀ (k a : Nat), (digs k a).length ≤ k
  | 0, _ => by simp [digs]
  | k + 1, a => by
    have := digs_length k a
    simp only [digs, List.length_append]
    split <;> simp <;> omega

theorem digs_lt : ∀ (k a : Nat), ∀ d ∈ digs k a, d < 10
  | 0, _, d, h => by simp [digs] at h
  | k + 1, a, d, h => by
    simp only [digs, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; exact Nat.mod_lt _ (by decide)
      · cases h
    · exact digs_lt k a d h

/-- The digits of `10ᵏ`, …, `10¹`. -/
theorem digitsOps_exec {size : Nat} {a : Nat} (ha : a < 2 ^ 63) (hs : size < 2 ^ 64) :
    ∀ (k : Nat), 10 ^ k < 2 ^ 63 → ∀ {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8},
    Inv size fr m out → outBase + out.length + k ≤ size →
    fr.get rAbs = some (BitVec.ofNat 64 a) → ∀ (os : List Op),
    ∃ fr' m', Lir.execOps (digitsOps k ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ (digs k a).map fun d => (d + 48).toUInt8) ∧
      fr'.get rAbs = some (BitVec.ofNat 64 a)
  | 0, _, fr, m, out, inv, _, habs, os => ⟨fr, m, rfl, by simpa [digs] using inv, habs⟩
  | k + 1, hk, fr, m, out, inv, room, habs, os => by
    have hk' : 10 ^ k < 2 ^ 63 := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) hk
    obtain ⟨fr1, m1, hx1, inv1, habs1⟩ := digitOps_exec inv (by omega) hs ha hk habs
      (digitsOps k ++ os)
    have hlen : (out ++ if 10 ^ (k + 1) ≤ a then [(a / 10 ^ (k + 1) % 10 + 48).toUInt8] else []).length
        ≤ out.length + 1 := by split <;> simp
    obtain ⟨fr2, m2, hx2, inv2, habs2⟩ := digitsOps_exec ha hs k hk' inv1 (by omega) habs1 os
    refine ⟨fr2, m2, ?_, ?_, habs2⟩
    · rw [digitsOps, List.append_assoc, hx1, hx2]
    · have e : (out ++ if 10 ^ (k + 1) ≤ a then [(a / 10 ^ (k + 1) % 10 + 48).toUInt8] else []) ++
          (digs k a).map (fun d => (d + 48).toUInt8) =
          out ++ (digs (k + 1) a).map (fun d => (d + 48).toUInt8) := by
        simp only [digs, List.map_append, List.append_assoc]
        split <;> simp
      rw [← e]; exact inv2

/-- The absolute value of `n` has at most ten digits. -/
theorem natAbs_lt {n : Int} (h : n.natAbs < 10 ^ 10) : n.natAbs < 2 ^ 63 :=
  lt_of_lt_of_le h (by norm_num)

/-- The bytes of the decimal of `n`. -/
theorem render_int (n : Int) (h : n.natAbs < 10 ^ 10) :
    Item.render (.int n) = (if n < 0 then [(45 : Nat).toUInt8] else []) ++
      ((digs 9 n.natAbs).map fun d => (d + 48).toUInt8) ++ [(n.natAbs % 10 + 48).toUInt8] := by
  simp only [Item.render, toString_int, List.map_append]
  rw [← digs_toDigits 9 n.natAbs (by simpa using h)]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.append_assoc]
  congr 1
  · split <;> rfl
  · congr 1
    · apply List.map_congr_left
      intro d hd
      exact digitChar_byte (digs_lt 9 _ d hd)
    · rw [digitChar_byte (Nat.mod_lt _ (by decide))]

theorem render_int_length (n : Int) (h : n.natAbs < 10 ^ 10) : (Item.render (.int n)).length ≤ 11 := by
  rw [render_int n h]
  have := digs_length 9 n.natAbs
  simp only [List.length_append, List.length_map, List.length_singleton]
  split <;> simp <;> omega

/-- **Writing the decimal of an integer** whose word is in `rVal`. -/
theorem decimal_exec {size : Nat} {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}
    (inv : Inv size fr m out) (room : outBase + out.length + 11 ≤ size) (hs : size < 2 ^ 64)
    {n : Int} (hn : n.natAbs < 10 ^ 10) (hval : fr.get rVal = some (BitVec.ofInt 64 n))
    (os : List Op) :
    ∃ fr' m', Lir.execOps (decimalOps ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ Item.render (.int n)) := by
  have hn63 := natAbs_lt hn
  let f : Nat := if n < 0 then 1 else 0
  let a := n.natAbs
  let fr1 := (fr.set rFlag (BitVec.ofNat 64 f)).set rByte (BitVec.ofNat 64 45)
  have inv1 : Inv size fr1 m out := inv_set (inv_set inv (by decide) _) (by decide) _
  -- the tail after the sign
  let tail : List Op := [.binary .mul rAbs rVal rFlag, .binary .add rAbs rAbs rAbs,
    .binary .sub rAbs rVal rAbs] ++ digitsOps 9 ++ [.binary .remu rDig rAbs rTen,
    .binary .add rDig rDig rChar0] ++ emit rDig rOne ++ os
  obtain ⟨fr2, m2, hx2, inv2, keep2⟩ := emit_exec inv1 (by omega) hs (rb := rByte) (rf := rFlag)
    (b := 45) (c := n < 0) (get_set_eq _ _ _)
    (by rw [get_set_ne _ (by decide)]; exact get_set_eq _ _ _) (by decide) (by decide) tail
  have hval2 : fr2.get rVal = some (BitVec.ofInt 64 n) := by
    rw [keep2 rVal (by decide) (by decide), get_set_ne _ (by decide), get_set_ne _ (by decide)]
    exact hval
  have hflag2 : fr2.get rFlag = some (BitVec.ofNat 64 f) := by
    rw [keep2 rFlag (by decide) (by decide), get_set_ne _ (by decide)]
    exact get_set_eq _ _ _
  let out2 := if n < 0 then out ++ [(45 : Nat).toUInt8] else out
  let x := BitVec.ofInt 64 n * BitVec.ofNat 64 f
  let fr3 := ((fr2.set rAbs x).set rAbs (x + x)).set rAbs (BitVec.ofNat 64 a)
  have inv3 : Inv size fr3 m2 out2 :=
    inv_set (inv_set (inv_set inv2 (by decide) _) (by decide) _) (by decide) _
  have hlen2 : out2.length ≤ out.length + 1 := by simp only [out2]; split <;> simp
  let tail2 : List Op := [.binary .remu rDig rAbs rTen, .binary .add rDig rDig rChar0] ++
    emit rDig rOne ++ os
  obtain ⟨fr4, m4, hx4, inv4, habs4⟩ := digitsOps_exec hn63 hs 9 (by norm_num) inv3 (by omega)
    (get_set_eq _ _ _) tail2
  let out4 := out2 ++ (digs 9 a).map fun d => (d + 48).toUInt8
  have hlen4 : out4.length ≤ out.length + 10 := by
    have := digs_length 9 a
    simp only [out4, List.length_append, List.length_map]
    omega
  have hd : a % 10 < 10 := Nat.mod_lt _ (by decide)
  let fr5 := (fr4.set rDig (BitVec.ofNat 64 (a % 10))).set rDig (BitVec.ofNat 64 (a % 10 + 48))
  have inv5 : Inv size fr5 m4 out4 := inv_set (inv_set inv4 (by decide) _) (by decide) _
  obtain ⟨fr6, m6, hx6, inv6, -⟩ := emit_exec inv5 (by omega) hs (rb := rDig) (rf := rOne)
    (b := a % 10 + 48) (c := True) (get_set_eq _ _ _)
    (by rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; simpa using inv4.regs.one)
    (by decide) (by decide) os
  refine ⟨fr6, m6, ?_, ?_⟩
  · have e1 : decimalOps ++ os = .binary (.cmp .lts) rFlag rVal rZero ::
        .const rByte (BitVec.ofNat 64 45) :: (emit rByte rFlag ++ tail) := by
      simp [decimalOps, tail]
    have e2 : tail = .binary .mul rAbs rVal rFlag :: .binary .add rAbs rAbs rAbs ::
        .binary .sub rAbs rVal rAbs :: (digitsOps 9 ++ tail2) := by
      simp [tail, tail2]
    have e3 : tail2 = .binary .remu rDig rAbs rTen :: .binary .add rDig rDig rChar0 ::
        (emit rDig rOne ++ os) := by
      simp [tail2]
    calc Lir.execOps (decimalOps ++ os) fr m
        = Lir.execOps (emit rByte rFlag ++ tail) fr1 m := by
          rw [e1, exec_binary _ hval inv.regs.zero (lts_ofInt hn63), exec_const]
      _ = Lir.execOps tail fr2 m2 := hx2
      _ = Lir.execOps (digitsOps 9 ++ tail2) fr3 m2 := by
          rw [e2, exec_binary _ hval2 hflag2 rfl, exec_binary _ (get_set_eq _ _ _) (get_set_eq _ _ _) rfl,
            exec_binary _ (by rw [get_set_ne _ (by decide), get_set_ne _ (by decide)]; exact hval2)
              (get_set_eq _ _ _) (by rw [Lir.Binop.eval, abs_ofInt hn63])]
      _ = Lir.execOps tail2 fr4 m4 := hx4
      _ = Lir.execOps (emit rDig rOne ++ os) fr5 m4 := by
          rw [e3, exec_binary _ habs4 inv4.regs.ten (remu_ofNat (by omega) (by decide) (by decide)),
            exec_binary _ (get_set_eq _ _ _)
              (by rw [get_set_ne _ (by decide)]; exact inv4.regs.char0) (add_ofNat _ _)]
      _ = Lir.execOps os fr6 m6 := hx6
  · have e : out4 ++ (if True then [(a % 10 + 48).toUInt8] else []) = out ++ Item.render (.int n) := by
      rw [render_int n hn]
      simp only [out4, out2, ↓reduceIte, List.append_assoc]
      split <;> simp [a]
    rw [← e]
    simpa using inv6

/-- **Writing the items.** -/
theorem items_exec {size : Nat} (hs : size < 2 ^ 64) :
    ∀ (items : List Item), (∀ it ∈ items, it.small = true) →
    ∀ {fr : Lir.Frame Mir.Reg} {m : Lir.Memory} {out : List UInt8}, Inv size fr m out →
    outBase + out.length + (items.map Item.room).sum ≤ size → ∀ (os : List Op),
    ∃ fr' m', Lir.execOps (items.flatMap itemOps ++ os) fr m = Lir.execOps os fr' m' ∧
      Inv size fr' m' (out ++ render items)
  | [], _, fr, m, out, inv, _, os => ⟨fr, m, rfl, by simpa [render] using inv⟩
  | it :: items, hsmall, fr, m, out, inv, room, os => by
    have hsmall' : ∀ it ∈ items, it.small = true := fun it h => hsmall it (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.sum_cons] at room
    have step : ∃ fr' m', Lir.execOps (itemOps it ++ (items.flatMap itemOps ++ os)) fr m =
          Lir.execOps (items.flatMap itemOps ++ os) fr' m' ∧
        Inv size fr' m' (out ++ it.render) ∧ (out ++ it.render).length ≤ out.length + it.room := by
      cases it with
      | byte b =>
        obtain ⟨fr', m', hx, inv'⟩ := byte_exec inv (by simp only [Item.room] at room; omega) hs b _
        exact ⟨fr', m', hx, inv', by simp [Item.render, Item.room]⟩
      | int n =>
        have hn : n.natAbs < 10 ^ 10 := by simpa [Item.small] using hsmall _ List.mem_cons_self
        have inv1 := inv_set inv (r := rVal) (by decide) (BitVec.ofInt 64 n)
        obtain ⟨fr', m', hx, inv'⟩ := decimal_exec inv1 (by simp only [Item.room] at room; omega) hs hn
          (get_set_eq _ _ _) (items.flatMap itemOps ++ os)
        refine ⟨fr', m', ?_, inv', ?_⟩
        · rw [itemOps, List.cons_append, exec_const]; exact hx
        · have := render_int_length n hn
          simp only [List.length_append, Item.room]
          omega
    obtain ⟨fr1, m1, hx1, inv1, hlen1⟩ := step
    obtain ⟨fr2, m2, hx2, inv2⟩ := items_exec hs items hsmall' inv1 (by omega) os
    refine ⟨fr2, m2, ?_, by simpa [render, List.append_assoc] using inv2⟩
    rw [List.flatMap_cons, List.append_assoc, hx1, hx2]

theorem render_length : ∀ (items : List Item), (∀ it ∈ items, it.small = true) →
    (render items).length ≤ (items.map Item.room).sum
  | [], _ => by simp [render]
  | it :: items, h => by
    have ih := render_length items (fun it' h' => h it' (List.mem_cons_of_mem _ h'))
    have h1 : it.render.length ≤ it.room := by
      cases it with
      | byte b => simp [Item.render, Item.room]
      | int n =>
        have hn : n.natAbs < 10 ^ 10 := by simpa [Item.small] using h _ List.mem_cons_self
        exact render_int_length n hn
    simp only [render, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    omega

end Run

/-! ## The control block and the observation -/

section Observe

theorem leNat_bytes (x : Nat) : ∀ n : Nat,
    leNat (List.ofFn fun i : Fin n => BitVec.ofNat 8 (x / 256 ^ i.val)) = x % 256 ^ n
  | 0 => by simp [leNat, Nat.mod_one]
  | n + 1 => by
    rw [List.ofFn_succ, leNat]
    have ih := leNat_bytes (x / 256) n
    have e : (List.ofFn fun i : Fin n => BitVec.ofNat 8 (x / 256 ^ (i.succ : Fin (n + 1)).val)) =
        List.ofFn fun i : Fin n => BitVec.ofNat 8 (x / 256 / 256 ^ i.val) := by
      congr 1
      funext i
      rw [Fin.val_succ, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [e, ih, Fin.val_zero, pow_zero, Nat.div_one, BitVec.toNat_ofNat,
      show (2 : Nat) ^ 8 = 256 by norm_num, pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem leNat_wordBytes (v : Lir.Word) :
    leNat (List.ofFn fun i : Fin 8 => LittleEndian.wordByte v i.val) = v.toNat := by
  have e : (List.ofFn fun i : Fin 8 => LittleEndian.wordByte v i.val) =
      List.ofFn fun i : Fin 8 => BitVec.ofNat 8 (v.toNat / 256 ^ i.val) := by
    congr 1
    funext i
    apply BitVec.eq_of_toNat_eq
    simp only [LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, pow_mul]
    norm_num
  rw [e, leNat_bytes]
  exact Nat.mod_eq_of_lt (by simpa using v.isLt)

theorem writeLE_in (bytes : Nat → Lir.Byte) {addr n a : Nat} (v : Lir.Word) (h1 : addr ≤ a)
    (h2 : a < addr + n) : Lir.writeLE bytes addr n v a = LittleEndian.wordByte v (a - addr) := by
  unfold Lir.writeLE
  rw [ite_pos ⟨h1, h2⟩]

/-- The word stored at `addr` is read back by `memWord`. -/
theorem memWord_store {m m' : Lir.Memory} {addr : Nat} {v : Lir.Word}
    (h : m.store .b8 addr v = some m') : memWord m' addr = v.toNat := by
  unfold Lir.Memory.store at h
  split at h
  · cases h
    simp only [memWord]
    rw [← leNat_wordBytes v]
    congr 1
    apply List.ofFn_inj.mpr
    funext i
    have := i.isLt
    rw [writeLE_in _ _ (by omega) (by simp only [Lir.Width.bytes]; omega)]
    congr 1
    omega
  · cases h

theorem store_bytes_outside {m m' : Lir.Memory} {w : Lir.Width} {addr : Nat} {v : Lir.Word}
    (h : m.store w addr v = some m') {i : Nat} (hi : i < addr ∨ addr + w.bytes ≤ i) :
    m'.bytes i = m.bytes i := by
  unfold Lir.Memory.store at h
  split at h
  · cases h
    simp only [Lir.writeLE]
    rw [ite_neg (by omega)]
  · cases h

theorem memWord_outside {m m' : Lir.Memory} {w : Lir.Width} {addr a : Nat} {v : Lir.Word}
    (h : m.store w addr v = some m') (ha : a + 8 ≤ addr ∨ addr + w.bytes ≤ a) :
    memWord m' a = memWord m a := by
  simp only [memWord]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  have := i.isLt
  exact store_bytes_outside h (by omega)

/-- The memory size of every artifact of the backend. -/
theorem artifact_memSize {l : Mir.Linked} {a : Artifact} (h : artifactOf l = .ok a) :
    a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  unfold artifactOf at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rfl

/-- The whole block, from any frame: the final memory holds the output, and control words 3
and 6 name it. -/
theorem ops_exec {items : List Item} (fits : Fits items) (w : Lir.Word) (fr0 : Lir.Frame Mir.Reg)
    (m0 : Lir.Memory) (hsize : m0.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ fr m, Lir.execOps (ops items w) fr0 m0 = some (fr, m) ∧ fr.get 0 = some w ∧
      memWord m (ctlAddr + 24) = (render items).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (render items) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  have hroom := fits.2
  have hs : Silmaril.Compile.Forks.CoreComp.Target.memSize < 2 ^ 64 := by decide
  have hab : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
  let epi : List Op := [.const rCtl (BitVec.ofNat 64 ctlAddr), .store .b8 rCtl 24 rLen,
    .store .b8 rCtl 48 rBase, .store .b8 rCtl 56 rLen, .const 0 w]
  obtain ⟨fr1, hx1, inv1⟩ := prologue_exec fr0 m0 (items.flatMap itemOps ++ epi)
  rw [hsize] at inv1
  obtain ⟨fr2, m2, hx2, inv2⟩ := items_exec hs items fits.1 inv1 (by simp; omega) epi
  simp only [List.nil_append] at inv2
  have hlen := render_length items fits.1
  let L := (render items).length
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

theorem link_funcs (items : List Item) (w : Lir.Word) :
    (link items w).funcs[Silmaril.Compile.Forks.CoreComp.Target.startSymbol]? = some 0 := by
  simp [link]

/-- The Lir run of `__ccomp_start` returns `[w]` with the output written. -/
theorem link_returns {items : List Item} (fits : Fits items) (w argc argv : Lir.Word)
    (mem : Lir.Memory) (hsize : mem.size = Silmaril.Compile.Forks.CoreComp.Target.memSize) :
    ∃ s m, (link items w).prog.start 0 [argc, argv] mem = some s ∧
      Lir.Behaves (link items w).prog s (.returned [w] m) ∧
      memWord m (ctlAddr + 24) = (render items).length ∧ memWord m (ctlAddr + 48) = outBase ∧
      Buf m (render items) ∧ m.size = Silmaril.Compile.Forks.CoreComp.Target.memSize := by
  obtain ⟨fr, m, hx, hw, h24, h48, hbuf, hm⟩ :=
    ops_exec fits w ((Lir.Frame.empty.set 1 argc).set 2 argv) mem hsize
  refine ⟨⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩, m, rfl, ?_, h24, h48, hbuf, hm⟩
  have hb : (link items w).prog.block? 0 0 = some ⟨(ops items w).map .op, .ret [.reg 0]⟩ := rfl
  have steps := Lir.steps_execOps (p := (link items w).prog) (os := ops items w)
    (s := ⟨⟨0, 0, 0⟩, (Lir.Frame.empty.set 1 argc).set 2 argv, [], mem⟩) (rest := []) hb
    (by rw [List.append_nil]; rfl) hx
  refine ⟨_, steps, ?_⟩
  have hf : (link items w).prog.fetch ⟨0, 0, (ops items w).length⟩ = some (.term (.ret [.reg 0])) :=
    Lir.Prog.fetch_eq_term (pt := ⟨0, 0, (ops items w).length⟩) hb (by simp)
  have hr' : fr.regs 0 = some w := hw
  simp [Lir.step, hf, Lir.Frame.readAll, Lir.Frame.read, hr']

/-- The output buffer of the final memory is the rendered items. -/
theorem stdout_eq {m : Lir.Memory} {items : List Item}
    (h24 : memWord m (ctlAddr + 24) = (render items).length) (h48 : memWord m (ctlAddr + 48) = outBase)
    (hbuf : Buf m (render items)) (hroom : outBase + (render items).length ≤ m.size)
    {out : List UInt8} (ho : StdoutOf m out) : out = render items := by
  apply ho
  simp only [memStdout?, h24, h48, hroom, ↓reduceIte, Option.some.injEq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, Fin.val_cast]
  rw [hbuf i h2]
  simp [Nat.toUInt8]

/-- **The output link is correct.** Every observation of the loaded artifact of `link items w` is
exhaustion or the exit with status `w mod 256` after writing `render items`. -/
theorem link_sound {items : List Item} (fits : Fits items) {w : Lir.Word} {a : Artifact}
    (h : artifactOf (link items w) = .ok a)
    {S : X86.Backend.Space} {exit : X86.Word} {E0 : Nat} (hl : Loaded a S exit E0)
    {saved : X86.Reg → X86.Word} {init : X86.State} {args : List String} {o : Obs}
    (hb : MachineBeh a S exit E0 saved init args o) :
    o = .exhausted ∨ o = .exit (w.toNat % 256) (render items) := by
  obtain ⟨start, s, hstart, hs, ho⟩ := artifactOf_sound h hl hb
  rw [link_funcs] at hstart
  cases hstart
  have hsize : (a.lmem args).size = Silmaril.Compile.Forks.CoreComp.Target.memSize := artifact_memSize h
  obtain ⟨s', m, hs', hret, h24, h48, hbuf, hm⟩ := link_returns fits w
    (BitVec.ofNat 64 args.length) (BitVec.ofNat 64 a.argBase) (a.lmem args) hsize
  rw [hs] at hs'
  cases hs'
  have hroom : outBase + (render items).length ≤ m.size := by
    have := render_length items fits.1
    have := fits.2
    have : Silmaril.Compile.Forks.CoreComp.Target.argBase < Silmaril.Compile.Forks.CoreComp.Target.memSize := by decide
    omega
  rcases ho with ho | hstuck | ⟨b, hb', hobs⟩
  · exact .inl ho
  · cases Lir.Behaves.unique hstuck hret
  · right
    cases Lir.Behaves.unique hb' hret
    obtain ⟨k, out, rfl, hk, hout⟩ := hobs
    rw [hk w rfl, stdout_eq h24 h48 hbuf hroom hout]

end Observe

end Silmaril.Compile.Core.Verified.PrintLink
