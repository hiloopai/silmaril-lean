module

public import Silmaril.Compiler.Core.Verified.ArgvAbortLink.Defs
/-! # Register-indexed argument character loads

The existing argv fragment uses constant load offsets. These operations compute
both indices at run time, using registers below a fresh temporary register.
The execution theorem works for arbitrary linear memory, so later CFG proofs
can use it after stores that preserve the two argument loads.

This is a target-side lemma, not a new accepted compiler fragment. In particular
the caller must prove source pointer bounds and preservation of argument objects.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvIndexLir

open Silmaril.Machine
open Spec

/-- Load `argv[i][j]` into `d`, with the base and both indices in registers.
Only `d` is overwritten; the indices may share registers with each other. -/
def ops (base i j d : Mir.Reg) : List (Lir.Op Mir.Reg) :=
  [.const d 8, .binary .mul d i d, .binary .add d base d,
    .load .b8 .zero d d 0, .binary .add d d j, .load .b1 .zero d d 0]

/-- Execute the two loads with runtime indices. The bounds exclude address
wraparound, and memory and all other registers are preserved. -/
theorem ops_exec (base ri rj d : Mir.Reg) (fr : Lir.Frame Mir.Reg) (mem : Lir.Memory)
    (b i j p : Nat) (c : Lir.Word)
    (hb : base < d) (hi : ri < d) (hj : rj < d)
    (rb : fr.get base = some (BitVec.ofNat 64 b))
    (rhi : fr.get ri = some (BitVec.ofNat 64 i))
    (rhj : fr.get rj = some (BitVec.ofNat 64 j))
    (slotBound : b + 8 * i < 2 ^ 64) (charBound : p + j < 2 ^ 64)
    (slot : mem.load .b8 .zero (b + 8 * i) = some (BitVec.ofNat 64 p))
    (char : mem.load .b1 .zero (p + j) = some c) :
    ∃ fr', Lir.execOps (ops base ri rj d) fr mem = some (fr', mem) ∧
      fr'.get d = some c ∧ ∀ r, r ≠ d → fr'.get r = fr.get r := by
  have nb : base ≠ d := Nat.ne_of_lt hb
  have ni : ri ≠ d := Nat.ne_of_lt hi
  have nj : rj ≠ d := Nat.ne_of_lt hj
  have mul : BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (8 * i) := by
    rw [Nat.mul_comm]
    exact (BitVec.ofNat_mul i 8).symm
  have add : BitVec.ofNat 64 b + BitVec.ofNat 64 (8 * i) =
      BitVec.ofNat 64 (b + 8 * i) := (BitVec.ofNat_add b (8 * i)).symm
  have add' : BitVec.ofNat 64 p + BitVec.ofNat 64 j =
      BitVec.ofNat 64 (p + j) := (BitVec.ofNat_add p j).symm
  refine ⟨(((((fr.set d 8).set d (BitVec.ofNat 64 (8 * i))).set d
    (BitVec.ofNat 64 (b + 8 * i))).set d (BitVec.ofNat 64 p)).set d
    (BitVec.ofNat 64 (p + j))).set d c, ?_, by simp, ?_⟩
  · simp only [ops, Lir.execOps, Lir.Op.exec, Lir.Frame.get_set,
      nb, ni, nj, ↓reduceIte, rb, rhi, rhj, Option.bind_some,
      Lir.Binop.eval, Option.map_some, mul, add, add', BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt slotBound, Nat.mod_eq_of_lt charBound, Nat.add_zero, slot, char]
  · intro r hr
    simp [hr]

/-- The register-indexed loader reads the frozen argument block, including a
string's terminating NUL. The null argv slot is deliberately excluded: a
source simulation must handle its UB before using this theorem. -/
theorem artifact_exec {a : Artifact} (hbase : a.argBase = Silmaril.Compile.Forks.CoreComp.Target.argBase)
    (hsize : a.memSize = Silmaril.Compile.Forks.CoreComp.Target.memSize) (himg : a.image = .empty)
    {args : List String} (ha : ArgsOk args) {i j : Nat}
    (hi : i < args.length) (hj : j ≤ args[i].length)
    (base ri rj d : Mir.Reg) (fr : Lir.Frame Mir.Reg)
    (hb : base < d) (hri : ri < d) (hrj : rj < d)
    (rb : fr.get base = some (BitVec.ofNat 64 a.argBase))
    (rhi : fr.get ri = some (BitVec.ofNat 64 i))
    (rhj : fr.get rj = some (BitVec.ofNat 64 j)) :
    ∃ fr', Lir.execOps (ops base ri rj d) fr (a.lmem args) = some (fr', a.lmem args) ∧
      fr'.get d = some (BitVec.ofNat 64 (ArgvChar.charOfArgs args i j).toNat) ∧
      ∀ r, r ≠ d → fr'.get r = fr.get r := by
  have room := ArgvReloc.room_of_argsOk ha
  have roomNonneg : 0 ≤ Silmaril.Cerberus.Core.StartupArgs.strRoom args := Int.natCast_nonneg _
  have str := ArgvAbortLink.strAddr_lt ha a.argBase hi
  have start := ArgvReloc.le_strAddr a.argBase args i
  have length := (ArgvAbortLink.block_length ha a.argBase).2
  have jlt : j < 4096 := by omega
  have sw : ArgvAbortLink.slotWord a.argBase args i = ArgBlock.strAddr a.argBase args i := by
    simp [ArgvAbortLink.slotWord, hi]
  have bc : a.argBase < 2 ^ 32 := by rw [hbase]; decide
  apply ops_exec base ri rj d fr (a.lmem args) a.argBase i j
    (ArgvAbortLink.slotWord a.argBase args i) _ hb hri hrj rb rhi rhj
  · omega
  · rw [sw]; omega
  · exact ArgvAbortLink.load_slot hbase hsize ha (Nat.le_of_lt hi)
  · exact ArgvAbortLink.load_char hbase hsize himg ha (Nat.le_of_lt hi) (fun _ => hj) jlt

end Silmaril.Compile.Core.Verified.ArgvIndexLir
