module

public import Silmaril.X86.Sep.Alloc.Defs
public import Silmaril.X86.Sep.Extra.Thms
public import Silmaril.X86.Sep.SysV.Thms
import Silmaril.Proofs.X86.Sep.Alloc

/-!
# The allocator interface: laws and non-vacuity

* **Splitting and weakening.** `fresh_split` (a fresh block of `m + n` bytes is a fresh
  block's first `m` bytes and `n` more unknown bytes, the token still covering `m + n`),
  `free_of_bytesPt` (written contents may be forgotten before `free`), `fresh_weaken` and
  `mallocSpec_sub_weaken` (an allocator aligning to `A.align` serves a client that needs only
  `d ∣ A.align`), `freeSpec_sub_weaken`.
* **Non-vacuity and looseness.** `never_malloc_sat`: the four bytes `xor rax, rax; ret`
  meet `mallocSpec Iface.never` under the System V ABI on `Open.isa` (and so, by
  `FnSpec.Sat.lift`, on `Open9.isa` and `Str9.isa`), and `never_free_sat`: `ret` meets
  `freeSpec Iface.never`. So the interface is satisfiable and failure is always a correct
  answer. Non-vacuity of the *success* branch (`Fresh`) needs a real allocator and is not
  shown here.

`strue_absorb`, `sor_sep`, `entails_strue` and the other `sor`/`strue` laws are in
`Sep/Extra/Thms.lean`, re-exported here.
-/

@[expose] public section

namespace Silmaril.X86.Sep.Alloc

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-- A fresh block of `m + n` bytes splits into its first `m` bytes (with the token for the
whole block) and the remaining `n` unknown bytes. -/
theorem fresh_split (A : Iface) (p : Word) (m n : Nat) :
    A.Fresh p (m + n) ⊢ₛ
      ((⌜p ≠ 0 ∧ p.toNat % A.align = 0⌝ ∗ A.tok p (m + n) ∗ blockAny p.toNat m) ∗
        blockAny (p.toNat + m) n) :=
  Silmaril.Proofs.X86.SepAlloc.fresh_split A p m n

theorem fresh_split_eq (A : Iface) (p : Word) (m n : Nat) :
    A.Fresh p (m + n) =
      ((⌜p ≠ 0 ∧ p.toNat % A.align = 0⌝ ∗ A.tok p (m + n) ∗ blockAny p.toNat m) ∗
        blockAny (p.toNat + m) n) :=
  Silmaril.Proofs.X86.SepAlloc.fresh_split_eq A p m n

/-- Initialised contents may be forgotten, e.g. before `free`. -/
theorem free_of_bytesPt (A : Iface) (p : Word) (bs : List Byte) :
    (A.tok p bs.length ∗ bytesPt p.toNat bs) ⊢ₛ
      (A.tok p bs.length ∗ blockAny p.toNat bs.length) :=
  Silmaril.Proofs.X86.SepAlloc.free_of_bytesPt A p bs

theorem fresh_weaken (A : Iface) {d : Nat} (h : d ∣ A.align) (p : Word) (n : Nat) :
    A.Fresh p n ⊢ₛ (A.weaken d).Fresh p n :=
  Silmaril.Proofs.X86.SepAlloc.fresh_weaken A h p n

/-- **Alignment weakening**: `malloc` of an allocator aligning to `A.align` is a `malloc` of
the same allocator promising only `d ∣ A.align`. -/
theorem mallocSpec_sub_weaken (A : Iface) {d : Nat} (h : d ∣ A.align) :
    (mallocSpec A).Sub (mallocSpec (A.weaken d)) :=
  Silmaril.Proofs.X86.SepAlloc.mallocSpec_sub_weaken A h

theorem freeSpec_sub_weaken (A : Iface) (d : Nat) :
    (freeSpec A).Sub (freeSpec (A.weaken d)) :=
  Silmaril.Proofs.X86.SepAlloc.freeSpec_sub_weaken A d

/-- **The interface is satisfiable**: `xor rax, rax; ret` meets `mallocSpec Iface.never`. -/
theorem never_malloc_sat (e : Word) :
    (mallocSpec Iface.never).Sat Open.isa (codePt e.toNat neverMallocBytes) e :=
  Silmaril.Proofs.X86.SepAlloc.never_malloc_sat e

/-- `ret` meets `freeSpec Iface.never`. -/
theorem never_free_sat (e : Word) :
    (freeSpec Iface.never).Sat Open.isa (codePt e.toNat neverFreeBytes) e :=
  Silmaril.Proofs.X86.SepAlloc.never_free_sat e

end Silmaril.X86.Sep.Alloc
