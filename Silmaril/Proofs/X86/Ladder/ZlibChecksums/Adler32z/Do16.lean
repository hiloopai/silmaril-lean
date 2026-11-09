module

public import Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z.Next
import Mathlib.Tactic.Ring

/-!
# `adler32_z`: pieces for the two `DO16` loop VCs

* `pre x r i`, `tri x r i`: the running `s1` (`r + x 0 + … + x (i-1)`, in the order the machine
  adds) and the running `s2` increment (`pre 1 + … + pre i`) of one `DO16` block over abstract
  bytes `x`. `seg_vc9` rewrites each machine sum into one of these atoms
  (`pre_succ`, `tri_succ`, …), so the symbolic state of a block stays small.
* `wpN_one`: one listed instruction that executes, stated for a *variable* offset. It is used
  for the read-modify-write `add %rax, -0x20(%rsp)` (`rmw`), the one instruction of the loops
  whose `seg_vc9` proof the kernel cannot check: unfolding `wpN` at a literal offset lets
  the kernel (and the elaborator) evaluate the listing lookup and then the instruction itself,
  and for this memory operand that evaluation runs into unary arithmetic on 64-bit literals
  ("deep recursion"). With the offset a variable nothing can be evaluated.
* arithmetic for the chunk loop's exits: `modWN'` (`modWN` in the operand order of the
  `0x80` loop), `p_addL`, `red_R1`/`red_R2`, `subNMAX`, `rdxA`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext
open Silmaril.X86.SegVC
open Silmaril.X86
open Silmaril.X86.Ladder.ZlibChecksums

/-! ## The sums of one `DO16` block -/

/-- The running `s1` of a `DO16` block: `r + x 0 + … + x (i-1)`, as the machine adds. -/
def pre (x : Nat → Word) (r : Word) : Nat → Word
  | 0 => r
  | i + 1 => x i + pre x r i

/-- The running `s2` increment of a `DO16` block: `pre 1 + … + pre i`. -/
def tri (x : Nat → Word) (r : Word) : Nat → Word
  | 0 => 0
  | i + 1 => tri x r i + pre x r (i + 1)

theorem pre_succ (x : Nat → Word) (r : Word) (i : Nat) : x i + pre x r i = pre x r (i + 1) := rfl
theorem pre_one (x : Nat → Word) (r : Word) : x 0 + r = pre x r 1 := rfl
theorem tri_two (x : Nat → Word) (r : Word) : pre x r 1 + pre x r 2 = tri x r 2 := by
  simp [tri]
theorem tri_succ (x : Nat → Word) (r : Word) (i : Nat) :
    tri x r (i + 2) + pre x r (i + 3) = tri x r (i + 3) := rfl

theorem pre16 (x : Nat → Word) (r : Word) :
    pre x r 16 = r + x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 + x 8 + x 9 + x 10 + x 11 +
      x 12 + x 13 + x 14 + x 15 := by
  simp only [pre]; ac_rfl

theorem tri16 (x : Nat → Word) (r : Word) :
    tri x r 16 = 16 * r + 16 * x 0 + 15 * x 1 + 14 * x 2 + 13 * x 3 + 12 * x 4 + 11 * x 5 +
      10 * x 6 + 9 * x 7 + 8 * x 8 + 7 * x 9 + 6 * x 10 + 5 * x 11 + 4 * x 12 + 3 * x 13 +
      2 * x 14 + 1 * x 15 := by
  simp only [tri, pre]; ring

/-- Reassociating the `s2` update of one block. -/
theorem add17 (q a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 : Word) :
    q + (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17) =
      q + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 := by
  simp only [BitVec.add_assoc]

/-- A slot fact (as an equation of loads) survives a store into another slot. -/
theorem keep' {c : Ctx} {mem after : Silmaril.Process.Memory} {A B : Word} {oa ob : Nat}
    (hD : ∀ B j, B.toNat + j ≤ A.toNat ∨ A.toNat + 8 ≤ B.toNat → loadN after B j = loadN mem B j)
    (hA : A.toNat = c.lo + oa) (hB : B.toNat = c.lo + ob) (hd : ob + 8 ≤ oa ∨ oa + 8 ≤ ob) :
    loadN after B 8 = loadN mem B 8 := hD B 8 (by rw [hA, hB]; omega)

/-! ## One instruction at a variable offset -/

/-- One listed instruction that executes (`wpN` unfolded once), for a variable offset. -/
theorem wpN_one {cuts : List (Nat × Cut (σ := MState))} {stops : List (Nat × (MState → Prop))}
    {base : Word} {μ : Option Nat} {k o : Nat} {s : MState} {i : Ext9.Instr} {l : Nat}
    {c : State} {m : Silmaril.Process.Memory}
    (hlk : List.lookup (β := Ext9.Instr × Nat) o adlerListing = some (i, l))
    (hex : Ext9.exec i s.core s.memory l = .ok c m)
    (hL : Loaded m base adler32zCode)
    (hnext : nextAt cuts stops μ (wpN Open9.isa adler32zCode adlerListing cuts stops [] [] base μ k)
      (offOf base c) ⟨c, m⟩) :
    wpN Open9.isa adler32zCode adlerListing cuts stops [] [] base μ (k + 1) o s := by
  rw [wpN_succ, hlk]
  show onOk _ (Ext9.exec i s.core s.memory l)
  rw [hex]
  exact ⟨trivial, hL, hnext⟩

/-- `add %src, mem` (64-bit): a load, then a store of the sum. -/
theorem exec_add_mem (s : State) (m : Silmaril.Process.Memory) (l : Nat) (mm : Mem) (src : Reg) :
    Silmaril.X86.Ext.exec (.alu .q .add (.mem mm) src) s m l =
      retire (s.rip + BitVec.ofNat 64 l) ((loadN m (mm.addr s (s.rip + BitVec.ofNat 64 l)) 8).bind
        fun v => (storeN m (mm.addr s (s.rip + BitVec.ofNat 64 l)) 8 (v + s.read src)).map
          fun after => ({ s with flags := addFlagsN v (s.read src) }, after)) := by
  simp only [Silmaril.X86.Ext.exec, aluStep, readRM, writeRM, Sz.bytes]
  rcases h : loadN m (mm.addr s (s.rip + BitVec.ofNat 64 l)) 8 with _ | v
  · rfl
  · simp only [Option.map_some, Option.bind_some, reduceCtorEq, ite_false, Option.map_map,
      Function.comp_def, Sz.bits, BitVec.setWidth_eq, AluOp.resultN, AluOp.flagsN, Sz.read]
    rfl

/-- **The read-modify-write `add %rax, -0x20(%rsp)`** (offsets `0x146` and `0x39e`), at a
variable offset `o`: the `s2` spill becomes `q + A`, and the path continues at `o + 5`. -/
theorem rmw (c : Ctx) (μ : Option Nat) (K o : Nat) (s : MState) (A q : Word)
    (hlk : List.lookup (β := Ext9.Instr × Nat) o adlerListing =
      some (.ext8 (.base (.alu .q (.add) (.mem (Mem.ofReg .rsp none 0xffffffe0#32)) .rax)), 5))
    (ho : o + 5 < 2 ^ 64) (hcut : (cuts c).lookup (o + 5) = none)
    (hstop : (stops c).lookup (o + 5) = none)
    (hrip : s.core.rip = c.base + BitVec.ofNat 64 o) (hsp : s.core.read .rsp = c.sp)
    (hA : s.core.read .rax = A)
    (hq : loadN s.memory (c.sp + 18446744073709551584#64) 8 = some q)
    (hperm : s.memory.Permitted .write (c.sp + 18446744073709551584#64).toNat 8)
    (hk : ∀ after, storeN s.memory (c.sp + 18446744073709551584#64) 8 (q + A) = some after →
      Loaded after c.base adler32zCode ∧
      wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ K (o + 5)
        ⟨{ s.core with rip := c.base + BitVec.ofNat 64 (o + 5), flags := addFlagsN q A }, after⟩) :
    wpN Open9.isa adler32zCode adlerListing (cuts c) (stops c) [] [] c.base μ (K + 1) o s := by
  obtain ⟨after, hst, -⟩ := storeN_isSome (v := q + A) hperm
  obtain ⟨hL, hw⟩ := hk after hst
  have haddr : (Mem.ofReg .rsp none 0xffffffe0#32).addr s.core (s.core.rip + BitVec.ofNat 64 5) =
      c.sp + 18446744073709551584#64 := by
    simp only [Mem.ofReg, Mem.addr, Base.value, hsp, Option.map_none, Option.getD_none,
      BitVec.add_zero]
    rfl
  have hrip' : s.core.rip + BitVec.ofNat 64 5 = c.base + BitVec.ofNat 64 (o + 5) := by
    rw [hrip, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine wpN_one (c := { s.core with rip := c.base + BitVec.ofNat 64 (o + 5), flags := addFlagsN q A })
    hlk ?_ hL ?_
  · rw [Silmaril.X86.SegVC9.exec9_base, exec_add_mem, haddr, hq, Option.bind_some, hA, hst,
      Option.map_some, hrip', retire_some]
  · rw [offOf_of_rip (o := o + 5) rfl, Nat.mod_eq_of_lt ho,
      Silmaril.X86.SegVC9.nextAt_cont hcut hstop]
    exact hw

/-! ## Arithmetic of the chunk loop's exits -/

/-- `modWN` in the operand order of the `0x80` loop's reductions (`mul`, then `imul`). -/
theorem modWN' (y : Nat) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 y - (BitVec.ofNat 64 (4223091239536077 * (y % 18446744073709551616) / 18446744073709551616) +
      (BitVec.ofNat 64 y - BitVec.ofNat 64 (4223091239536077 * (y % 18446744073709551616) /
        18446744073709551616)) >>> 1) >>> 15 * 65521#64 = BitVec.ofNat 64 (y % 65521) := by
  have := modW (BitVec.ofNat 64 y) _ rfl
  simp only [BitVec.toNat_ofNat, MAGIC, Nat.reducePow] at this
  rw [Nat.mul_comm (y % 18446744073709551616)] at this
  rw [this, Nat.mod_eq_of_lt (show y < 18446744073709551616 from hy)]

theorem p_addL (c : Ctx) (x y : Nat) :
    c.p + (BitVec.ofNat 64 x + BitVec.ofNat 64 y) = c.p + BitVec.ofNat 64 (x + y) := by
  rw [← BitVec.ofNat_add]

theorem red_R1 (c : Ctx) (k j : Nat) : (c.R k j).1 % 65521 = (c.S (k + j)).1 := by
  have := red_R c.bs c.a k j
  simp only [Silmaril.X86.Stencils.AccumFold.red, BASE] at this
  exact congrArg Prod.fst this

theorem red_R2 (c : Ctx) (k j : Nat) : (c.R k j).2 % 65521 = (c.S (k + j)).2 := by
  have := red_R c.bs c.a k j
  simp only [Silmaril.X86.Stencils.AccumFold.red, BASE] at this
  exact congrArg Prod.snd this

/-- `lea -0x15b0(%rax), %r8` after `NMAX` was added. -/
theorem subNMAX (x : Nat) :
    BitVec.ofNat 64 (x + 5552) + 18446744073709546064#64 = BitVec.ofNat 64 x := by
  rw [BitVec.ofNat_add, BitVec.add_assoc,
    show (BitVec.ofNat 64 5552 + 18446744073709546064#64 : Word) = 0#64 by decide, BitVec.add_zero]

/-- The tail end pointer of the `rem ≤ 15` exit of the chunk loop (`0x463`, `0x3db`). -/
theorem rdxA (c : Ctx) (n kk : Nat) (hk : kk ≤ n) :
    c.p + (BitVec.ofNat 64 kk + (BitVec.ofNat 64 (n - kk + 5552) - 5553#64 + 1#64)) =
      c.p + BitVec.ofNat 64 n := by
  have e : BitVec.ofNat 64 n = BitVec.ofNat 64 kk + BitVec.ofNat 64 (n - kk) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [e, BitVec.ofNat_add (n - kk)]
  have h1 : (BitVec.ofNat 64 5552 : Word) = 5552 := rfl
  have h2 : (5553#64 : Word) = 5553 := rfl
  have h3 : (1#64 : Word) = 1 := rfl
  simp only [h1, h2, h3]; ring

end Silmaril.Proofs.X86.Ladder.ZlibChecksums.Adler32z
