-- Imported from an earlier development
-- Source: Silmaril/X86/Spec/EnsuresSysV.lean; sha256=465a0589fd1eede6a07c8cdb807faaa8198c2d85cca9afe60f813d5bc5f79205
-- Reproduce with tools/mor/examples/import_c.rs; declaration namespaces retained.
module

public import Silmaril.Machine.X86.Spec.Ensures.Defs
public import Silmaril.X86.CallingConvention
public import Silmaril.Machine.CSupport.Crypto.X86.Contract.Defs

/-!
# The System V AMD64 reading of the footprint vocabulary

Recommendation R2 of `docs/projects/wasm-wasi.md` asks for An earlier change theorem
shape to be stated *per calling convention*. Everything a subroutine theorem
needs beyond `Silmaril/X86/Spec/Ensures.lean` is read off
`Silmaril.X86.sysv64` (`Silmaril/X86/CallingConvention.lean`) rather than
re-spelled here:

* `CArguments` indexes `sysv64.intArgRegs`, so "the first three integer
  arguments" is `CArguments [a, b, c]` and never a hand-written
  `rdi/rsi/rdx` triple. This is s2n-bignum's `C_ARGUMENTS`.
* `CalleeSavedPreserved` quantifies over `sysv64.calleeSaved`, and
  `calleeSavedPreserved_of_mayChange` derives it from the *absence* of those
  registers from a `MayChange` list — the survey's point 1, made concrete.
* `StackRestored` uses `sysv64.linkSize` (= 8) for the `rsp` a `ret` leaves
  behind.
* `redZone` uses `sysv64.redZone` (= 128). A leaf function's stack footprint
  is a sub-range of it, and `MayChange.widen_range` turns the precise
  footprint into the ABI-level "only the red zone" claim.
* `abiMayChange` is s2n-bignum's `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`:
  the nine caller-saved integer registers, `rip`, and all six flags.
  `calleeSaved_notMem_abiMayChange` is the one-line reason callee-saved
  preservation is implicit.

## The bridge to the existing `Regions.Disjoint`

`Silmaril/Crypto/X86/Contract.lean` already has a `Region` and a
`Regions.Disjoint` for the older register-only model. That file is left
untouched; `separate_iff_regionsDisjoint` here proves that the wrap-aware
`Spec.Separate` and that interval test agree, for nonempty ranges that stay
strictly below `2 ^ 64`. The strictness is not slack: a range ending exactly
at `2 ^ 64` has `base + size = 0` as a `BitVec`, so the `BitVec`-level test
`Regions.Disjoint` reads as `0 ≤ other`, which is vacuously true. That is the
precise reason this vocabulary states separation semantically.

## What is *not* here: the `Implements` wrapper

`Silmaril.Machine.Behaviour.Refinement.Implements` is stated over two
`Machine.Behaviour.Semantics` records and a `Represents` relation, neither of
which exists yet for `X86.Ext` (`Silmaril/X86/Ext/Machine.lean` exports
`step`/`Returns`, not a `Semantics`). The subroutine theorem in
`Silmaril/X86/Spec/Md5Memcpy.lean` is therefore stated as an `Ensures`, with
every hypothesis and conclusion phrased in the `sysv64` vocabulary above, so
that an `Implements sysv64` wrapper is a matter of supplying

1. a `Semantics` whose `Beh` is `Ext.Returns exit`, and
2. a `Represents c t` that is exactly this theorem's precondition
   (`CArguments`, `ProgramAt`, the stack facts),

with `ob` reading the output buffer. Both are an earlier change work items, not
footprint work; nothing in this file or in the benchmark proof would change.

## Proof style

Everything here is `decide` (register and location membership, all finite) or
`omega` (the interval bridge). Nothing is hand-sequenced.
-/

@[expose] public section

namespace Silmaril.X86.Spec

open Silmaril.X86 (Reg Word Byte State MState sysv64)

/-! ## `C_ARGUMENTS` -/

/-- The System V AMD64 integer argument registers hold `args`, in the order
`sysv64.intArgRegs` gives them. s2n-bignum's `C_ARGUMENTS`. -/
def CArguments (args : List Word) (m : MState) : Prop :=
  args.length ≤ sysv64.intArgRegs.length ∧
    ∀ (i : Nat) (r : Reg) (v : Word),
      sysv64.intArgRegs[i]? = some r → args[i]? = some v → m.core.read r = v

/-- The three-argument case, as the benchmark uses it. -/
theorem CArguments.three {a b c : Word} {m : MState} (h : CArguments [a, b, c] m) :
    m.core.read .rdi = a ∧ m.core.read .rsi = b ∧ m.core.read .rdx = c :=
  ⟨h.2 0 _ _ rfl rfl, h.2 1 _ _ rfl rfl, h.2 2 _ _ rfl rfl⟩

/-- The two-argument case. -/
theorem CArguments.two {a b : Word} {m : MState} (h : CArguments [a, b] m) :
    m.core.read .rdi = a ∧ m.core.read .rsi = b :=
  ⟨h.2 0 _ _ rfl rfl, h.2 1 _ _ rfl rfl⟩

/-- …and its constructor. -/
theorem CArguments.of_three {a b c : Word} {m : MState} (ha : m.core.read .rdi = a)
    (hb : m.core.read .rsi = b) (hc : m.core.read .rdx = c) : CArguments [a, b, c] m := by
  have hregs : sysv64.intArgRegs = [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9] := rfl
  refine ⟨(by decide : (3 : Nat) ≤ 6), ?_⟩
  rintro (_ | _ | _ | i) r v h₁ h₂ <;> rw [hregs] at h₁ <;> simp_all

/-! ## Callee-saved registers and the stack -/

/-- The callee-saved registers of `sysv64` hold their entry values. The
vocabulary never *assumes* this; it is always derived from a `MayChange`. -/
def CalleeSavedPreserved (before after : MState) : Prop :=
  ∀ r ∈ sysv64.calleeSaved, after.core.read r = before.core.read r

/-- Preservation is the absence of those registers from the footprint. This
single lemma is the survey's "callee-saved preservation is implicit". -/
theorem calleeSavedPreserved_of_mayChange {locs : List Loc} {a b : MState}
    (h : MayChange locs a b) (hdis : ∀ r ∈ sysv64.calleeSaved, Loc.reg r ∉ locs) :
    CalleeSavedPreserved a b := fun r hr => h.reg_eq (hdis r hr)

/-- After the `ret`, `rsp` is the entry `rsp` plus `sysv64.linkSize` — the
eight bytes of return address the `call` pushed. -/
def StackRestored (before after : MState) : Prop :=
  after.core.read .rsp = before.core.read .rsp + BitVec.ofNat 64 sysv64.linkSize

/-- The System V red zone below a stack pointer: `sysv64.redZone` bytes a leaf
function may use without adjusting `rsp`. -/
def redZone (sp : Word) : Range :=
  ⟨sp - BitVec.ofNat 64 sysv64.redZone, sysv64.redZone⟩

@[simp] theorem redZone_len (sp : Word) : (redZone sp).len = 128 := rfl

/-- A leaf frame of `n ≤ 128` bytes immediately below `sp` sits inside the red
zone, so `MayChange.widen_range` lifts a precise stack footprint to the ABI
one. -/
theorem frame_subset_redZone {sp : Word} {n : Nat} (hn : n ≤ 128) (hlo : 128 ≤ sp.toNat) :
    (Range.mk (sp - BitVec.ofNat 64 n) n).Subset (redZone sp) := by
  have hsub : ∀ k : Nat, k ≤ 128 → (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
    intro k hk
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
    omega
  have hsp := sp.isLt
  have hrz : redZone sp = Range.mk (sp - BitVec.ofNat 64 128) 128 := rfl
  rw [hrz]
  refine Range.subset_of_interval ?_ ?_ ?_ ?_
  · show (sp - BitVec.ofNat 64 n).toNat + n ≤ 2 ^ 64
    rw [hsub n hn]; omega
  · show (sp - BitVec.ofNat 64 128).toNat + 128 ≤ 2 ^ 64
    rw [hsub 128 (le_refl 128)]; omega
  · show (sp - BitVec.ofNat 64 128).toNat ≤ (sp - BitVec.ofNat 64 n).toNat
    rw [hsub n hn, hsub 128 (le_refl 128)]; omega
  · show (sp - BitVec.ofNat 64 n).toNat + n ≤ (sp - BitVec.ofNat 64 128).toNat + 128
    rw [hsub n hn, hsub 128 (le_refl 128)]; omega

/-! ## The ABI's may-change set -/

/-- The integer registers System V lets a callee clobber: everything except
the six callee-saved registers and `rsp`. -/
def abiScratchRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]

/-- s2n-bignum's `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`: the caller-saved
integer registers, `rip`, and every flag. A subroutine theorem's footprint is
this list plus the memory ranges the routine writes. -/
def abiMayChange : List Loc := abiScratchRegs.map Loc.reg ++ (Loc.rip :: Loc.allFlags)

theorem calleeSaved_notMem_abiMayChange {r : Reg} (h : r ∈ sysv64.calleeSaved) :
    Loc.reg r ∉ abiMayChange := by
  revert h; cases r <;> decide

/-- `rsp` is not in the ABI may-change set either: its discipline is
`StackRestored`, not clobbering. -/
theorem rsp_notMem_abiMayChange : Loc.reg .rsp ∉ abiMayChange := by decide

theorem flag_mem_abiMayChange (f : FlagName) : Loc.flag f ∈ abiMayChange := by
  cases f <;> decide

theorem rip_mem_abiMayChange : Loc.rip ∈ abiMayChange := by decide

/-- Any footprint built from `abiMayChange`, `rsp` and memory ranges preserves
the callee-saved registers. -/
theorem calleeSavedPreserved_of_abi {rest : List Loc} {a b : MState}
    (h : MayChange (abiMayChange ++ Loc.reg .rsp :: rest) a b)
    (hrest : ∀ r ∈ sysv64.calleeSaved, Loc.reg r ∉ rest) : CalleeSavedPreserved a b := by
  refine calleeSavedPreserved_of_mayChange h ?_
  intro r hr hmem
  rcases List.mem_append.mp hmem with hin | hin
  · exact calleeSaved_notMem_abiMayChange hr hin
  · rcases List.mem_cons.mp hin with heq | hin'
    · exact absurd (Loc.reg.inj heq ▸ hr) (by decide)
    · exact hrest r hr hin'

/-! ## The bridge to `Crypto.X86.Regions.Disjoint` -/

/-- A `Spec.Range` as the older model's `Region`. -/
def Range.toRegion (r : Range) : Crypto.X86.Region := ⟨r.base, r.len⟩

/-- For ranges that stay strictly below `2 ^ 64`, the `BitVec`-level interval
test of `Silmaril/Crypto/X86/Contract.lean` is the `Nat`-level one. -/
theorem regionsDisjoint_iff {r s : Range} (hr : r.base.toNat + r.len < 2 ^ 64)
    (hs : s.base.toNat + s.len < 2 ^ 64) :
    Crypto.X86.Regions.Disjoint r.toRegion s.toRegion ↔ r.Disjoint s := by
  have hrb : (r.base + BitVec.ofNat 64 r.len).toNat = r.base.toNat + r.len :=
    toNat_add_ofNat hr
  have hsb : (s.base + BitVec.ofNat 64 s.len).toNat = s.base.toNat + s.len :=
    toNat_add_ofNat hs
  simp only [Crypto.X86.Regions.Disjoint, Range.toRegion, Range.Disjoint, BitVec.le_def,
    hrb, hsb]

/-- `Separate` is the existing `Regions.Disjoint`, for nonempty ranges below
the top of the address space. This is the "proved equivalence" of survey R1. -/
theorem separate_iff_regionsDisjoint {r s : Range} (hr : r.base.toNat + r.len < 2 ^ 64)
    (hs : s.base.toNat + s.len < 2 ^ 64) (hrpos : 0 < r.len) (hspos : 0 < s.len) :
    Separate r s ↔ Crypto.X86.Regions.Disjoint r.toRegion s.toRegion :=
  (separate_iff_disjoint (by unfold Range.NoWrap; omega) (by unfold Range.NoWrap; omega)
    hrpos hspos).trans (regionsDisjoint_iff hr hs).symm

end Silmaril.X86.Spec
