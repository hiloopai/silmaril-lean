module

public import Silmaril.Process.LPS.Sys.Mmap
public import Silmaril.Process.LPS.Uapi
public import Silmaril.Process.LPS.Uaccess
public import Silmaril.Process.LPS.StateHelpers
public import Silmaril.Process.LPS.Arm

/-!
# LPS in Lean: `mremap`, `mprotect`, `madvise`, and the x86-64 memory-management arms

Translations from LPS (upstream commit `f1006fe8`):

* `Sys/Mm/Mremap.v`: `mremap_spec` (number 216) over the `MREMAP_MAYMOVE` shape: equal size
  (a deterministic no-op), shrink in place, grow in place or by moving (an `alt`, since the
  kernel's in-place test reads state the ledger does not have), every resizing call beside
  the injected `ENOMEM`; and its budget mark, which reads both growth gates, the move's
  through the destination-free charge `mremapMoveCharge`;
* `Sys/Mm/Mprotect.v`: `mprotect_spec` (226): the four argument gates in the kernel's order,
  then `PROT_READ|PROT_WRITE` only, either exposing one contained `PROT_NONE` range (zeros,
  budget-gated, beside the injected `ENOMEM`) or a no-op on an already-rw range; and its
  budget mark;
* `Sys/Mm/Madvise.v`: `madvise_spec` (233): `MADV_DONTNEED` over a range inside one live
  read-write anonymous mapping, which zero-fills the range and gives back its first-touch
  charges; no injected failure.

Every other shape is `unmodeled` exactly where LPS has it so.

## x86-64

The three specifications are generic `mm/` code and read no ISA constant, so the x86-64
arms (`mremap` 25, `mprotect` 10, `madvise` 28, `arch/x86/entry/syscalls/syscall_64.tbl`)
use them unchanged. Checked against x86-64: `untagged_addr` is the identity unless the
process enabled LAM (`arch_prctl(ARCH_ENABLE_TAGGED_ADDR)`), which no modelled call does;
x86-64 selects `ARCH_HAS_PKEYS`, but `mprotect` passes `pkey = -1` and
`arch_override_mprotect_pkey` keeps the VMA's key, so an rw-over-rw `mprotect` still has
`newflags == oldflags`; `arch_validate_prot` and `arch_validate_flags` are the generic ones;
`MADV_DONTNEED`, `MREMAP_MAYMOVE`, `PROT_GROWSDOWN` and `PROT_GROWSUP` have the
`asm-generic` values.

The one memory-management arm that reads an address-space constant is `munmap`
(`Sys/Mm/Mmap.v:2224`), whose `-EINVAL` bound is `TASK_SIZE`: LPS's is the riscv64 Sv48
`0x800000000000`, x86-64's with four-level paging is `TASK_SIZE_MAX = 2^47 - 4096`
(`taskSizeMaxX86`). `munmapSpecWith` takes the bound, `munmapSpec` is its LPS instance
(`munmapSpecWith_taskSize`) and `munmapSpecX86` the x86-64 one. `brk` and `mmap` read only
`alloc_top` (derived from the initial stack pointer), so their x86-64 arms (12, 9) are the
LPS specifications; the x86-only `MAP_32BIT`/`MAP_ABOVE4G` bits are outside every modelled
`mmap` flag shape and stay `unmodeled`, as every unknown bit does in LPS.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Mm/Mmap.v:744` `mmap_fd_none`: the `fd` an anonymous `mmap` passes (`-1`); under
`MAP_ANONYMOUS` Linux never reads it, and no `mmap` shape tests it. -/
def mmapFdNone : Word := zw (-1)

/-! ## `mremap` (`Sys/Mm/Mremap.v`) -/

/-- LPS `Sys/Mm/Mremap.v:115` `mremap_errnos`: a resizing call may fail for lack of memory. -/
def mremapErrnos : List Int := [ENOMEM]

/-- LPS `Sys/Mm/Mremap.v:120` `mremap_maps_next`: replace the mapping based at `old` with
`(dst, newN)`; the no-access ledger is carried over verbatim. -/
def mremapMapsNext (h : VmMaps) (old dst newN : Word) : VmMaps :=
  { h with maps := (dst, newN) :: mapRemove h.maps old }

/-- LPS `Sys/Mm/Mremap.v:129` `mremap_backing_uniform_b`: the source is wholly lazy or wholly
eager. -/
def mremapBackingUniformB (m : Model) (old oldN : Word) : Bool :=
  mapContains m.vmLazy old oldN || regionFree m.vmLazy old oldN

/-- LPS `Sys/Mm/Mremap.v:133` `mremap_source_lazy_b`. -/
def mremapSourceLazyB (m : Model) (old oldN : Word) : Bool :=
  mapContains m.vmLazy old oldN

/-- LPS `Sys/Mm/Mremap.v:140` `mremap_model_next`: ownership and sparse backing move as one
transition. -/
def mremapModelNext (m : Model) (old oldN dst newN : Word) : Model :=
  vmResizeBacking (mremapSourceLazyB m old oldN) old oldN dst newN
    (m.withVmmaps (mremapMapsNext m.vmmaps old dst newN))

/-- LPS `Sys/Mm/Mremap.v:159` `mremap_tail`: the grown delta, read as fresh zeros. -/
def mremapTail (base oldN : Word) (oldNZ newNZ : Int) : List (Word × Word) :=
  if oldNZ < newNZ then [(base + oldN, zw (newNZ - oldNZ))] else []

/-- LPS `Sys/Mm/Mremap.v:176` `page_align_is0_b`: the kernel's wrapping `PAGE_ALIGN(len)` is
zero. -/
def pageAlignIs0B (len : Word) : Bool :=
  wIs0 len || decide (twoPow64 ≤ pageRoundUp (uns len))

/-- LPS `Sys/Mm/Mremap.v:202` `mremap_source_b`: the source is exactly one tracked mapping,
clear of the image and of `PROT_NONE` ranges, below `alloc_top`. -/
def mremapSourceB (h : VmMaps) (old oldN : Word) (oldNZ : Int) : Bool :=
  decide (uns old + oldNZ ≤ allocTop h) && regionFree h.reserved old oldN &&
    mapHas h.maps old oldN && regionFree h.noaccess old oldN

/-- LPS `Sys/Mm/Mremap.v:220` `mremap_final_budget_b`: the complete post-state fits the
budget. -/
def mremapFinalBudgetB (m : Model) (old oldN dst newN : Word) : Bool :=
  vmBackingWithinLimit (mremapModelNext m old oldN dst newN)

/-- LPS `Sys/Mm/Mremap.v:251` `mremap_inplace_grow_b`. -/
def mremapInplaceGrowB (m : Model) (old oldN newN : Word) (_oldNZ newNZ : Int) : Bool :=
  let h := m.vmmaps
  decide (uns old + newNZ ≤ allocTop h) &&
    regionFree (h.reserved ++ mapRemove h.maps old) old newN &&
    mremapFinalBudgetB m old oldN old newN

/-- LPS `Sys/Mm/Mremap.v:341` `mremap_fresh_b`: a moved destination is a preference-free
placement, distinct from the source. -/
def mremapFreshB (m : Model) (_oldNZ newNZ : Int) (old oldN dst newN : Word) : Bool :=
  let h := m.vmmaps
  !(dst == old) && uns dst % pageSize == 0 && decide (0 < uns dst) &&
    decide (uns dst + newNZ ≤ allocTop h) && regionFree (h.reserved ++ h.maps) dst newN &&
    mremapFinalBudgetB m old oldN dst newN

/-- LPS `Sys/Mm/Mremap.v:416` `mremap_inplace_effect`: a shrink unmaps the tail, a grow
zero-fills the delta. -/
def mremapInplaceEffect (old oldN newN : Word) (oldNZ newNZ : Int) : SyscallEffect :=
  if newNZ < oldNZ then
    { ret := old, writes := [], zeros := [], unmaps := [(old + newN, zw (oldNZ - newNZ))] }
  else mkEffect old [] (mremapTail old oldN oldNZ newNZ)

/-- LPS `Sys/Mm/Mremap.v:443` `mremap_move_effect`: copy the whole source from the pre-effect
snapshot, unmap it, and zero-fill the grown tail. -/
def mremapMoveEffect (old oldN dst : Word) (oldNZ newNZ : Int) : SyscallEffect :=
  { ret := dst, writes := [], zeros := mremapTail dst oldN oldNZ newNZ,
    unmaps := [(old, oldN)], copies := [⟨old, dst, oldN⟩] }

/-- LPS `Sys/Mm/Mremap.v:610` `mremap_spec`: `mremap(old, old_size, new_size,
MREMAP_MAYMOVE)` over one tracked read-write anonymous mapping. The flag gate declines every
other flag word (including `flags = 0`, which Linux serves); the equal-size answer has no
injected failure; a growth is in place or moved, and the moved destination is a free
choice. -/
def mremapSpec (old oldSize newSize flags : Word) : Sys SyscallEffect :=
  if !(uns flags == MREMAP_MAYMOVE) then unmodeled
  else if !(uns old % pageSize == 0) then errRet EINVAL
  else if pageAlignIs0B newSize then errRet EINVAL
  else if pageAlignIs0B oldSize then unmodeled
  else do
    let m ← getModel
    let h := m.vmmaps
    let oldNZ := pageRoundUp (uns oldSize)
    let newNZ := pageRoundUp (uns newSize)
    let oldN := zw oldNZ
    let newN := zw newNZ
    if !(mremapSourceB h old oldN oldNZ && mremapBackingUniformB m old oldN) then unmodeled
    else if oldNZ == newNZ then retOnly old
    else
      Sys.alt
        (do
          let e ← errnoFrom mremapErrnos
          errRet e)
        (if newNZ < oldNZ then do
          modify fun _ => mremapModelNext m old oldN old newN
          Sys.pure (mremapInplaceEffect old oldN newN oldNZ newNZ)
         else
          let move : Sys SyscallEffect := do
            let dst ← Sys.choose fun dst => mremapFreshB m oldNZ newNZ old oldN dst newN = true
            modify fun _ => mremapModelNext m old oldN dst newN
            Sys.pure (mremapMoveEffect old oldN dst oldNZ newNZ)
          if mremapInplaceGrowB m old oldN newN oldNZ newNZ then
            Sys.alt
              (do
                modify fun _ => mremapModelNext m old oldN old newN
                Sys.pure (mremapInplaceEffect old oldN newN oldNZ newNZ))
              move
          else move)

/-- LPS `Sys/Mm/Mremap.v:694` `mremap_move_charge`: the moved post-state's charge, which is
the same at every fresh destination. -/
def mremapMoveCharge (m : Model) (old oldN newN : Word) : Int :=
  let h := m.vmmaps
  let oldLo := uns old
  let oldHi := oldLo + uns oldN
  let sourceLazy := mremapSourceLazyB m old oldN
  let keptLazy := mapsSubtract m.vmLazy oldLo oldHi
  let keptPages := m.vmMaterialized.filter (pageOutsideRange oldLo oldHi)
  let movedPages :=
    if sourceLazy then
      m.vmMaterialized.filter fun p =>
        pageInHalfOpen oldLo oldHi p && decide (uns p - oldLo < uns newN)
    else []
  liveBytes (mapsSubtractAll (mapsSubtractAll (mapRemove h.maps old) h.noaccess) keptLazy)
    + (if sourceLazy then 0 else uns newN)
    + ((movedPages.length + keptPages.length : Nat) : Int) * pageSize

/-- LPS `Sys/Mm/Mremap.v:718` `mremap_move_budget_b`: the move's budget gate, without the
destination. -/
def mremapMoveBudgetB (m : Model) (old oldN newN : Word) : Bool :=
  decide (mremapMoveCharge m old oldN newN ≤ m.vmmaps.limit)

/-- LPS `Sys/Mm/Mremap.v:774` `mremap_budget_refused_b`: a growth one of whose two budget
gates refuses (an over-approximation, the safe direction for a premise). -/
def mremapBudgetRefusedB (old oldSize newSize flags : Word) (m : Model) : Bool :=
  if !(uns flags == MREMAP_MAYMOVE) then false
  else if !(uns old % pageSize == 0) then false
  else if pageAlignIs0B newSize then false
  else if pageAlignIs0B oldSize then false
  else
    let h := m.vmmaps
    let oldNZ := pageRoundUp (uns oldSize)
    let newNZ := pageRoundUp (uns newSize)
    let oldN := zw oldNZ
    let newN := zw newNZ
    if !(mremapSourceB h old oldN oldNZ && mremapBackingUniformB m old oldN) then false
    else if newNZ ≤ oldNZ then false
    else !(mremapFinalBudgetB m old oldN old newN && mremapMoveBudgetB m old oldN newN)

/-! ## `mprotect` (`Sys/Mm/Mprotect.v`) -/

/-- LPS `Sys/Mm/Mprotect.v:78` `mprotect_errnos`. -/
def mprotectErrnos : List Int := [ENOMEM]

/-- LPS `Sys/Mm/Mprotect.v:189` `mprotect_modeled_b`: exactly `PROT_READ|PROT_WRITE`, over
the whole 64-bit `prot` word. -/
def mprotectModeledB (prot : Word) : Bool := uns prot == PROT_READ + PROT_WRITE

/-- LPS `Sys/Mm/Mprotect.v:197` `mprotect_grows_conflict_b`: both stack-extension bits. -/
def mprotectGrowsConflictB (prot : Word) : Bool :=
  prot.toNat &&& PROT_GROWSDOWN.toNat != 0 && prot.toNat &&& PROT_GROWSUP.toNat != 0

/-- LPS `Sys/Mm/Mprotect.v:205` `mprotect_model_next`: expose one protected range; lazy
provenance and materialized pages are carried over. -/
def mprotectModelNext (m : Model) (addr n : Word) : Model :=
  let h := m.vmmaps
  m.withVmmaps { h with noaccess := mapsSubtract h.noaccess (uns addr) (uns addr + uns n) }

/-- LPS `Sys/Mm/Mprotect.v:230` `mprotect_budget_ok`. -/
def mprotectBudgetOk (m : Model) (addr n : Word) : Bool :=
  vmBackingWithinLimit (mprotectModelNext m addr n)

/-- LPS `Sys/Mm/Mprotect.v:233` `mprotect_spec`: the grows conflict, the alignment, the zero
length and the wrapping end are answered first (in the kernel's order); then only
`PROT_READ|PROT_WRITE` over one tracked range is modelled. -/
def mprotectSpec (addr len prot : Word) : Sys SyscallEffect :=
  if mprotectGrowsConflictB prot then errRet EINVAL
  else if !(uns addr % pageSize == 0) then errRet EINVAL
  else if wIs0 len then retOnly 0
  else if twoPow64 ≤ uns addr + pageRoundUp (uns len) then errRet ENOMEM
  else if mprotectModeledB prot then do
    let m ← getModel
    let h := m.vmmaps
    let nZ := pageRoundUp (uns len)
    let n := zw nZ
    if mapContains h.noaccess addr n && mapContains h.maps addr n then
      Sys.alt
        (do
          let e ← errnoFrom mprotectErrnos
          errRet e)
        (do
          let _ ← Sys.choose fun _ : Unit => mprotectBudgetOk m addr n = true
          modify fun _ => mprotectModelNext m addr n
          Sys.pure (mkEffect 0 [] [(addr, n)]))
    else if mapContains h.maps addr n && regionFree h.noaccess addr n then retOnly 0
    else unmodeled
  else unmodeled

/-- LPS `Sys/Mm/Mprotect.v:330` `mprotect_budget_refused_b`. -/
def mprotectBudgetRefusedB (addr len prot : Word) (m : Model) : Bool :=
  if mprotectGrowsConflictB prot then false
  else if !(uns addr % pageSize == 0) then false
  else if wIs0 len then false
  else if twoPow64 ≤ uns addr + pageRoundUp (uns len) then false
  else if mprotectModeledB prot then
    let h := m.vmmaps
    let nZ := pageRoundUp (uns len)
    let n := zw nZ
    if mapContains h.noaccess addr n && mapContains h.maps addr n then
      !mprotectBudgetOk m addr n
    else false
  else false

/-! ## `madvise` (`Sys/Mm/Madvise.v`) -/

/-- LPS `Sys/Mm/Madvise.v:166` `madvise_dontneed_b` (`advice` arrives narrowed by `int32`). -/
def madviseDontneedB (advice : Word) : Bool := uns advice == MADV_DONTNEED

/-- LPS `Sys/Mm/Madvise.v:171` `madvise_dontneed_ok`: inside one live anonymous mapping,
clear of the image, every page read-write. -/
def madviseDontneedOk (h : VmMaps) (addr n : Word) : Bool :=
  regionFree h.reserved addr n && mapContains h.maps addr n && regionFree h.noaccess addr n

/-- LPS `Sys/Mm/Madvise.v:238` `madvise_dontneed_next`: give back the range's first-touch
charges; nothing else moves. -/
def madviseDontneedNext (m : Model) (addr n : Word) : Model :=
  m.withVmBacking m.vmLazy
    (m.vmMaterialized.filter (pageOutsideRange (uns addr) (uns addr + uns n)))

/-- LPS `Sys/Mm/Madvise.v:245` `madvise_spec`: a misaligned address is `EINVAL` for every
advice; only `MADV_DONTNEED` is modelled past it. -/
def madviseSpec (addr len advice : Word) : Sys SyscallEffect :=
  if !(uns addr % pageSize == 0) then errRet EINVAL
  else if !madviseDontneedB advice then unmodeled
  else if wIs0 len then retOnly 0
  else if twoPow64 ≤ uns addr + pageRoundUp (uns len) then errRet EINVAL
  else do
    let m ← getModel
    let h := m.vmmaps
    let nZ := pageRoundUp (uns len)
    let n := zw nZ
    if madviseDontneedOk h addr n then do
      modify fun _ => madviseDontneedNext m addr n
      Sys.pure (mkEffect 0 [] [(addr, n)])
    else unmodeled

/-- LPS `State.v:4417` `entries_nonzero`: every entry of a ledger list names a byte. -/
def EntriesNonzero (maps : List (Word × Word)) : Prop := ∀ a n, (a, n) ∈ maps → 0 < uns n

/-- LPS `State.v:4901` `vm_noaccess_entries_nonzero`. -/
def VmNoaccessEntriesNonzero (h : VmMaps) : Prop := EntriesNonzero h.noaccess

/-- LPS `State.v:4313` `region_free_false`: a region that is not free meets some entry. -/
theorem regionFree_false {maps : List (Word × Word)} {lo n : Word}
    (h : regionFree maps lo n = false) : ∃ a sz, (a, sz) ∈ maps ∧ ivOverlap lo n a sz = true := by
  induction maps with
  | nil => simp [regionFree] at h
  | cons p r ih =>
    obtain ⟨a, sz⟩ := p
    cases hov : ivOverlap lo n a sz with
    | true => exact ⟨a, sz, List.mem_cons_self .., hov⟩
    | false =>
      simp only [regionFree, hov, Bool.not_false, Bool.true_and] at h
      obtain ⟨b, s, hb, hbov⟩ := ih h
      exact ⟨b, s, List.mem_cons_of_mem _ hb, hbov⟩

/-- LPS `Sys/Mm/Madvise.v:213` `madvise_noaccess_decline_names_a_protected_byte`: under the
nonzero-entries invariant, a decline attributed to `vm_noaccess` exhibits a protected byte the
request covers. -/
theorem madvise_noaccess_decline_names_a_protected_byte (h : VmMaps) (addr n : Word)
    (hnz : VmNoaccessEntriesNonzero h) (hn : 0 < uns n)
    (hfree : regionFree h.noaccess addr n = false) :
    ∃ a sz x, (a, sz) ∈ h.noaccess ∧ 0 < uns sz ∧ (uns a ≤ x ∧ x < uns a + uns sz) ∧
      (uns addr ≤ x ∧ x < uns addr + uns n) := by
  obtain ⟨a, sz, hin, hov⟩ := regionFree_false hfree
  have hsz := hnz a sz hin
  simp only [ivOverlap, Bool.and_eq_true, decide_eq_true_eq] at hov
  rcases le_total (uns a) (uns addr) with hle | hle
  · exact ⟨a, sz, uns addr, hin, hsz, ⟨hle, by omega⟩, ⟨le_refl _, by omega⟩⟩
  · exact ⟨a, sz, uns a, hin, hsz, ⟨le_refl _, by omega⟩, ⟨hle, by omega⟩⟩

/-- LPS `Sys/Mm/Mmap.v:708` `mmap_flags_core_id`: without `MAP_NORESERVE` the core flags are
the flags. -/
theorem mmap_flags_core_id (flags : Word) (h : flags.toNat &&& MAP_NORESERVE.toNat = 0) :
    mmapFlagsCore flags = uns flags := by
  simp [mmapFlagsCore, h, uns]

/-! ## The protected ledger names real bytes (`State.v:4417-4510`, `Sys/Mm/Mmap.v:420-583`,
`Sys/Mm/Mprotect.v:220`)

Each writer of `vm_noaccess` keeps every entry nonempty: the shrinking writers by
`mapsSubtract_nonzero`, the growing ones because the request's page-rounded length is
positive (`mmap_request_len_nonzero`). As in LPS, the composition over every reachable model
is not stated. -/

/-- LPS `State.v:4420` `entries_nonzero_nil`. -/
theorem entriesNonzero_nil : EntriesNonzero [] := fun _ _ h => by simp at h

/-- LPS `State.v:4437` `entries_nonzero_cons`. -/
theorem entriesNonzero_cons {a n : Word} {r : List (Word × Word)} (hn : 0 < uns n)
    (hr : EntriesNonzero r) : EntriesNonzero ((a, n) :: r) := by
  intro b s hin
  rcases List.mem_cons.mp hin with heq | hin
  · cases heq; exact hn
  · exact hr b s hin

/-- LPS `State.v:4450` `bv_unsigned_range_u64`. -/
theorem uns_range (w : Word) : 0 ≤ uns w ∧ uns w < twoPow64 := by
  have e : twoPow64 = 18446744073709551616 := by unfold twoPow64; decide
  have hb : w.toNat < 18446744073709551616 := w.isLt
  rw [e]; unfold uns; omega

/-- LPS `State.v:4457` `bv_unsigned_Z_to_bv_u64`. -/
theorem uns_zw {z : Int} (h0 : 0 ≤ z) (h1 : z < twoPow64) : uns (zw z) = z := by
  unfold twoPow64 at h1
  show ((BitVec.ofInt 64 z).toNat : Int) = z
  rw [BitVec.toNat_ofInt,
    Int.emod_eq_of_lt h0 (show z < ((2 ^ 64 : Nat) : Int) by exact_mod_cast h1),
    Int.toNat_of_nonneg h0]

/-- LPS `State.v:4466` `iv_subtract_nonzero`: cutting a nonempty entry leaves nonempty
remnants. -/
theorem ivSubtract_nonzero (a sz : Word) (lo hi : Int) (hsz : 0 < uns sz) :
    EntriesNonzero (ivSubtract a sz lo hi) := by
  intro b s hin
  obtain ⟨ha0, ha1⟩ := uns_range a
  obtain ⟨hs0, hs1⟩ := uns_range sz
  simp only [ivSubtract, List.mem_append] at hin
  rcases hin with hin | hin
  · split at hin
    · simp only [List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨-, rfl⟩ := hin
      rw [Int.min_def]
      split <;> rw [uns_zw] <;> omega
    · simp at hin
  · split at hin
    · simp only [List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨-, rfl⟩ := hin
      rw [Int.max_def]
      split <;> rw [uns_zw] <;> omega
    · simp at hin

/-- LPS `State.v:4488` `maps_subtract_nonzero`. -/
theorem mapsSubtract_nonzero {maps : List (Word × Word)} (lo hi : Int)
    (h : EntriesNonzero maps) : EntriesNonzero (mapsSubtract maps lo hi) := by
  induction maps with
  | nil => exact entriesNonzero_nil
  | cons p r ih =>
    obtain ⟨a, sz⟩ := p
    intro b s hin
    rcases List.mem_append.mp hin with hin | hin
    · exact ivSubtract_nonzero a sz lo hi (h a sz (List.mem_cons_self ..)) b s hin
    · exact ih (fun x y hx => h x y (List.mem_cons_of_mem _ hx)) b s hin

/-- LPS `State.v:4501` `maps_subtract_all_nonzero`. -/
theorem mapsSubtractAll_nonzero (cuts : List (Word × Word)) {maps : List (Word × Word)}
    (h : EntriesNonzero maps) : EntriesNonzero (mapsSubtractAll maps cuts) := by
  induction cuts generalizing maps with
  | nil => exact h
  | cons c rest ih =>
    obtain ⟨a, n⟩ := c
    exact ih (mapsSubtract_nonzero _ _ h)

/-- LPS `State.v:5396` `init_model_noaccess_nonzero`. -/
theorem initModel_noaccess_nonzero (reserved : List (Word × Word)) (brk0 mbase sp : Word)
    (lim : Int) (inp : ProcInput) :
    VmNoaccessEntriesNonzero (initModel reserved brk0 mbase sp lim inp).vmmaps :=
  entriesNonzero_nil

/-- LPS `Sys/Mm/Mmap.v:467` `maps_subtract_ranges_nonzero`. -/
theorem mapsSubtractRanges_nonzero (ranges : List (Word × Word)) {maps : List (Word × Word)}
    (h : EntriesNonzero maps) : EntriesNonzero (mapsSubtractRanges maps ranges) := by
  unfold mapsSubtractRanges
  induction ranges generalizing maps with
  | nil => exact h
  | cons p rest ih => exact ih (mapsSubtract_nonzero _ _ h)

/-- LPS `Sys/Mm/Mmap.v:481` `mmap_request_len_nonzero`: a nonzero length whose rounding
stays below `2^64` rounds to a positive word. -/
theorem mmap_request_len_nonzero (len : Word) (h0 : wIs0 len = false)
    (hfit : pageRoundUp (uns len) < twoPow64) : 0 < uns (zw (pageRoundUp (uns len))) := by
  have hne : len ≠ 0 := by
    intro h'; subst h'; exact absurd h0 (by decide)
  have hnz : len.toNat ≠ 0 := fun h' => hne (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
  have hpos : 0 < uns len := by unfold uns; omega
  have hpage : pageSize ≤ pageRoundUp (uns len) := by
    unfold pageRoundUp pageSize at *; omega
  rw [uns_zw (z := pageRoundUp (uns len)) (by unfold pageSize at hpage; omega) hfit]
  unfold pageSize at hpage; omega

/-- LPS `Sys/Mm/Mmap.v:518` `mmap_noaccess_grant_inline_nonzero`: the record of the three
`PROT_NONE` grant arms. -/
theorem mmap_noaccess_grant_inline_nonzero (h : VmMaps) (a len n : Word) (h0 : wIs0 len = false)
    (hfit : pageRoundUp (uns len) < twoPow64) (hn : n = zw (pageRoundUp (uns len)))
    (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero
      { h with maps := (a, n) :: h.maps, noaccess := (a, n) :: h.noaccess } :=
  entriesNonzero_cons (by subst hn; exact mmap_request_len_nonzero len h0 hfit) hnz

/-- LPS `Sys/Mm/Mmap.v:537` `mmap_fixed_noaccess_inline_nonzero`: the record of the contained
`PROT_NONE` `MAP_FIXED` arm. -/
theorem mmap_fixed_noaccess_inline_nonzero (h : VmMaps) (addr len n : Word)
    (h0 : wIs0 len = false) (hfit : pageRoundUp (uns len) < twoPow64)
    (hn : n = zw (pageRoundUp (uns len))) (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero
      { h with noaccess := (addr, n) :: mapsSubtract h.noaccess (uns addr) (uns addr + uns n) } :=
  entriesNonzero_cons (by subst hn; exact mmap_request_len_nonzero len h0 hfit)
    (mapsSubtract_nonzero _ _ hnz)

/-- LPS `Sys/Mm/Mmap.v:562` `munmap_inline_nonzero`: the record of `munmap`'s whole-mapping
removal. -/
theorem munmap_inline_nonzero (h : VmMaps) (addr n : Word) (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero
      { h with maps := mapRemove h.maps addr
               noaccess := mapsSubtract h.noaccess (uns addr) (uns addr + uns n) } :=
  mapsSubtract_nonzero _ _ hnz

/-- LPS `Sys/Mm/Mmap.v:577` `brk_model_next_noaccess_nonzero`. -/
theorem brkModelNext_noaccess_nonzero (h : VmMaps) (req r : Word)
    (hnz : VmNoaccessEntriesNonzero h) : VmNoaccessEntriesNonzero (brkModelNext h req r) :=
  mapsSubtractRanges_nonzero _ hnz

/-- LPS `Sys/Mm/Mmap.v:1082` `mmap_fixed_rw_next_noaccess_nonzero`. -/
theorem mmapFixedRwNext_noaccess_nonzero (h : VmMaps) (addr n : Word)
    (hnz : VmNoaccessEntriesNonzero h) : VmNoaccessEntriesNonzero (mmapFixedRwNext h addr n) :=
  mapsSubtract_nonzero _ _ hnz

/-- LPS `Sys/Mm/Mmap.v:1153` `mmap_fixed_destroyed_next_noaccess_nonzero`. -/
theorem mmapFixedDestroyedNext_noaccess_nonzero (h : VmMaps) (addr n : Word)
    (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero (mmapFixedDestroyedNext h addr n) :=
  mapsSubtract_nonzero _ _ hnz

/-- LPS `Sys/Mm/Mmap.v:1174` `mmap_fixed_rw_span_next_noaccess_nonzero`. -/
theorem mmapFixedRwSpanNext_noaccess_nonzero (h : VmMaps) (addr n : Word)
    (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero (mmapFixedRwSpanNext h addr n) :=
  mapsSubtract_nonzero _ _ hnz

/-- LPS `Sys/Mm/Mmap.v:1204` `mmap_fixed_noaccess_span_next_noaccess_nonzero`: the one named
post-state that grows the protected list needs a nonzero request. -/
theorem mmapFixedNoaccessSpanNext_noaccess_nonzero (h : VmMaps) (addr n : Word)
    (hn : 0 < uns n) (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero (mmapFixedNoaccessSpanNext h addr n) :=
  entriesNonzero_cons hn (mapsSubtract_nonzero _ _ hnz)

/-- LPS `Sys/Mm/Mmap.v:1220` `mmap_fixed_noaccess_span_next_noaccess_nonzero_of_len`. -/
theorem mmapFixedNoaccessSpanNext_noaccess_nonzero_of_len (h : VmMaps) (addr len n : Word)
    (h0 : wIs0 len = false) (hfit : pageRoundUp (uns len) < twoPow64)
    (hn : n = zw (pageRoundUp (uns len))) (hnz : VmNoaccessEntriesNonzero h) :
    VmNoaccessEntriesNonzero (mmapFixedNoaccessSpanNext h addr n) :=
  mmapFixedNoaccessSpanNext_noaccess_nonzero h addr n
    (by subst hn; exact mmap_request_len_nonzero len h0 hfit) hnz

/-- LPS `Sys/Mm/Mprotect.v:220` `mprotect_model_next_noaccess_nonzero`. -/
theorem mprotectModelNext_noaccess_nonzero (m : Model) (addr n : Word)
    (hnz : VmNoaccessEntriesNonzero m.vmmaps) :
    VmNoaccessEntriesNonzero (mprotectModelNext m addr n).vmmaps :=
  mapsSubtract_nonzero _ _ hnz

/-! ## `mremap` destinations avoid protected memory (`Sys/Mm/Mremap.v:376`) -/

/-- LPS `State.v:61` `page_round_down_Z_within`. -/
theorem pageRoundDown_within (lo hi x : Int) (hlo : lo % pageSize = 0) (hhi : hi % pageSize = 0)
    (hx : lo ≤ x ∧ x < hi) : lo ≤ pageRoundDown x ∧ pageRoundDown x + pageSize ≤ hi := by
  unfold pageRoundDown pageSize at *
  omega

/-- LPS `State.v:4282` `region_free_In`: a free region misses every entry. -/
theorem regionFree_mem {maps : List (Word × Word)} {lo n a sz : Word}
    (h : regionFree maps lo n = true) (hin : (a, sz) ∈ maps) : ivOverlap lo n a sz = false := by
  induction maps with
  | nil => simp at hin
  | cons p r ih =>
    obtain ⟨b, s⟩ := p
    have h' : (!ivOverlap lo n b s && regionFree r lo n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.mp hin with heq | hin
    · cases heq
      cases hov : ivOverlap lo n a sz <;> simp_all
    · exact ih h'.2 hin

/-- LPS `State.v:4298` `region_free_intro`. -/
theorem regionFree_intro {maps : List (Word × Word)} {lo n : Word}
    (h : ∀ a sz, (a, sz) ∈ maps → ivOverlap lo n a sz = false) : regionFree maps lo n = true := by
  induction maps with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨b, s⟩ := p
    show (!ivOverlap lo n b s && regionFree r lo n) = true
    rw [h b s (List.mem_cons_self ..), Bool.not_false, Bool.true_and]
    exact ih fun a sz hin => h a sz (List.mem_cons_of_mem _ hin)

/-- LPS `State.v:4857` `noaccess_pages_owned`: every page a protected range touches meets a
live mapping (the page-granular form of `vm_noaccess ⊆ vm_maps`, which survives the
same-page `brk` shrink). -/
def NoaccessPagesOwned (h : VmMaps) : Prop :=
  ∀ a n, (a, n) ∈ h.noaccess →
    0 < uns n ∧ ∀ x, uns a ≤ x ∧ x < uns a + uns n →
      ∃ b s, (b, s) ∈ h.maps ∧ uns b < pageRoundDown x + pageSize ∧
        pageRoundDown x < uns b + uns s

/-- LPS `Sys/Mm/Mremap.v:376` `mremap_fresh_avoids_noaccess`: given the ledger invariant, a
destination `mremap_fresh_b` accepts is disjoint from `vm_noaccess`, the conjunct its
definition leaves out. -/
theorem mremap_fresh_avoids_noaccess (m : Model) (oldNZ newNZ : Int) (old oldN dst newN : Word)
    (hown : NoaccessPagesOwned m.vmmaps) (hpos : 0 < uns newN) (hmod : uns newN % pageSize = 0)
    (hfresh : mremapFreshB m oldNZ newNZ old oldN dst newN = true) :
    regionFree m.vmmaps.noaccess dst newN = true := by
  simp only [mremapFreshB, Bool.and_eq_true] at hfresh
  have halign : uns dst % pageSize = 0 := by simpa using hfresh.1.1.1.1.2
  have hrf : regionFree (m.vmmaps.reserved ++ m.vmmaps.maps) dst newN = true := hfresh.1.2
  have hhi : (uns dst + uns newN) % pageSize = 0 := by
    unfold pageSize at *
    omega
  apply regionFree_intro
  intro a n hin
  obtain ⟨hn, hpage⟩ := hown a n hin
  cases hov : ivOverlap dst newN a n with
  | false => rfl
  | true =>
    exfalso
    simp only [ivOverlap, Bool.and_eq_true, decide_eq_true_eq] at hov
    have key : ∀ x, uns dst ≤ x → x < uns dst + uns newN → uns a ≤ x → x < uns a + uns n →
        False := by
      intro x hx1 hx2 hx3 hx4
      obtain ⟨b, s, hinm, hb1, hb2⟩ := hpage x ⟨hx3, hx4⟩
      obtain ⟨hf1, hf2⟩ := pageRoundDown_within _ _ x halign hhi ⟨hx1, hx2⟩
      have hno := regionFree_mem hrf (List.mem_append_right _ hinm)
      simp only [ivOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_lt] at hno
      rcases hno with hno | hno <;> omega
    rcases le_total (uns dst) (uns a) with hle | hle
    · exact key (uns a) hle (by omega) (le_refl _) (by omega)
    · exact key (uns dst) (le_refl _) (by omega) hle (by omega)

/-! ## `munmap` with the address-space bound as a parameter -/

/-- LPS `Sys/Mm/Mmap.v:2224` `munmap_spec`, with `TASK_SIZE` as the parameter `taskSz`
(`do_vmi_munmap`'s `start > TASK_SIZE || len > TASK_SIZE - start`). -/
def munmapSpecWith (taskSz : Int) (addr len : Word) : Sys SyscallEffect :=
  if uns addr % pageSize ≠ 0 || wIs0 len then errRet EINVAL
  else do
    let h ← getVmmaps
    let nZ := pageRoundUp (uns len)
    if taskSz < uns addr + nZ then errRet EINVAL
    else
      let n := zw nZ
      if mapHas h.maps addr n then do
        modify (·.withVmmaps { h with maps := mapRemove h.maps addr
                                      noaccess := mapsSubtract h.noaccess (uns addr)
                                        (uns addr + uns n) })
        modify (vmForgetRange (uns addr) (uns addr + uns n))
        Sys.pure { ret := 0, writes := [], zeros := [], unmaps := [(addr, n)] }
      else if munmapFreeOk h addr nZ then retOnly 0
      else unmodeled

/-- The LPS `munmap` is the instance at the riscv64 Sv48 `TASK_SIZE`. -/
theorem munmapSpecWith_taskSize : munmapSpecWith taskSize = munmapSpec := rfl

/-- x86-64 `munmap`: `TASK_SIZE` is `TASK_SIZE_MAX = 2^47 - 4096` with four-level paging
(`arch/x86/include/asm/page_64_types.h`), so a range ending in the last page below `2^47` is
`-EINVAL` on x86-64 where LPS's Sv48 bound lets it reach the ledger. -/
def munmapSpecX86 (addr len : Word) : Sys SyscallEffect :=
  munmapSpecWith taskSizeMaxX86 addr len

/-! ## Arms -/

/-- The memory-management arms of the LPS table (asm-generic numbers, LPS order:
`Sys/SyscallTable.v:119-125`). `brk`, `munmap` and `mmap` are also rows of `specTable`. -/
def mmLpsArms : List SpecArm :=
  [ arm 214 "brk" (fun i => brkSpec (i.arg 0)),
    arm 215 "munmap" (fun i => munmapSpec (i.arg 0) (i.arg 1)),
    arm 216 "mremap" (fun i => mremapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 222 "mmap" (fun i => mmapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 226 "mprotect" (fun i => mprotectSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 233 "madvise" (fun i => madviseSpec (i.arg 0) (i.arg 1) (int32 (i.arg 2))) ]

/-- The memory-management arms at their native x86-64 numbers
(`arch/x86/entry/syscalls/syscall_64.tbl`): `mmap` 9, `mprotect` 10, `munmap` 11 (with the
x86-64 `TASK_SIZE`), `brk` 12, `mremap` 25, `madvise` 28. -/
def mmX86Arms : List SpecArm :=
  [ arm 9 "mmap" (fun i => mmapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5)),
    arm 10 "mprotect" (fun i => mprotectSpec (i.arg 0) (i.arg 1) (i.arg 2)),
    arm 11 "munmap" (fun i => munmapSpecX86 (i.arg 0) (i.arg 1)),
    arm 12 "brk" (fun i => brkSpec (i.arg 0)),
    arm 25 "mremap" (fun i => mremapSpec (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3)),
    arm 28 "madvise" (fun i => madviseSpec (i.arg 0) (i.arg 1) (int32 (i.arg 2))) ]

end Silmaril.Process.LPS
