module

public import Silmaril.Process.LPS.Syscall

/-!
# LPS in Lean: `brk`, `mmap`, `munmap` and the allocation budget

Translation of LPS `Sys/Mm/Mmap.v` (upstream commit `f1006fe8`), the specification of Linux
`mm/mmap.c` for anonymous private mappings and the program break.

Memory budgets: every backed byte is charged against `VmMaps.limit` (the run's allocation
limit, 16 GiB for a source and 512 GiB for a target by default). A request over the budget is
refused (`brk` returns the old break, `mmap` returns `-ENOMEM`). `MAP_NORESERVE` mappings are
lazy: their pages are charged on first touch, by `materializeModelAccesses` in the run
semantics. `brkBudgetRefusedB` and `mmapBudgetRefusedB` say when a call is refused *for
budget*; the `*_budgets` statements exclude inputs on which the source reaches such a call.

`mmap` may also fail with `ENOMEM` without cause (`mmap_errnos`), which is one of the
injected failures that a `SpuriousCfg` can filter.
-/

@[expose] public section

namespace Silmaril.Process.LPS

open Sys

/-- LPS `Sys/Mm/Mmap.v:141` `min_brk`. -/
def minBrk (h : VmMaps) : Word := h.startBrk

/-- LPS `Sys/Mm/Mmap.v:154` `brk_is_grow`. -/
def brkIsGrow (req r old : Word) : Bool :=
  !wIs0 req && decide (0 < uns old) && decide (uns old < uns r)

/-- LPS `Sys/Mm/Mmap.v:165` `brk_grants`. -/
def brkGrants (req r old : Word) : List (Word × Word) :=
  if brkIsGrow req r old then [(old, r - old)] else []

/-- LPS `Sys/Mm/Mmap.v:173` `brk_page_range`. -/
def brkPageRange (lo hi : Int) : List (Word × Word) :=
  if lo < hi then [(zw lo, zw (hi - lo))] else []

/-- LPS `Sys/Mm/Mmap.v:185` `brk_zeros`: the fresh pages a growing break maps. -/
def brkZeros (req r old : Word) : List (Word × Word) :=
  if brkIsGrow req r old then brkPageRange (pageRoundUp (uns old)) (pageRoundUp (uns r)) else []

/-- LPS `Sys/Mm/Mmap.v:208` `brk_unmaps`: the pages a shrinking break unmaps. -/
def brkUnmaps (r old : Word) : List (Word × Word) :=
  if 0 < uns old then brkPageRange (pageRoundUp (uns r)) (pageRoundUp (uns old)) else []

/-- LPS `Sys/Mm/Mmap.v:339` `brk_budget_ok`. -/
def brkBudgetOk (m : Model) (r : Word) : Bool :=
  decide (vmBackingUsed m + uns (r - m.vmmaps.brk) ≤ m.vmmaps.limit)

/-- LPS `Sys/Mm/Mmap.v:343` `brk_grow_ok`. -/
def brkGrowOk (m : Model) (_req r : Word) : Bool :=
  let h := m.vmmaps
  if 0 < uns h.brk ∧ uns h.brk < uns r then
    let lo := pageRoundUp (uns h.brk)
    let hi := pageRoundUp (uns r)
    (if lo < hi then
      decide (hi ≤ allocTop h) &&
        regionFree (h.reserved ++ h.maps) (zw lo) (zw (hi + pageSize - lo))
     else true) && brkBudgetOk m r
  else true

/-- LPS `Sys/Mm/Mmap.v:360` `brk_r_ok`: the admissible results of `brk(req)`. -/
def brkROk (m : Model) (req r : Word) : Bool :=
  let h := m.vmmaps
  let b := h.brk
  if wIs0 req || decide (uns req < uns (minBrk h)) then r == b
  else if uns req < uns b then r == req || r == b
  else (r == req || r == b) && brkGrowOk m req r

/-- LPS `Sys/Mm/Mmap.v:381` `brk_maps_next`. -/
def brkMapsNext (h : VmMaps) (req r : Word) : List (Word × Word) :=
  if 0 < uns h.brk ∧ uns r < uns h.brk then mapsSubtract h.maps (uns r) (uns h.brk)
  else brkGrants req r h.brk ++ h.maps

/-- LPS `Sys/Mm/Mmap.v:396` `maps_subtract_ranges`. -/
def mapsSubtractRanges (maps ranges : List (Word × Word)) : List (Word × Word) :=
  ranges.foldl (fun acc p => mapsSubtract acc (uns p.1) (uns p.1 + uns p.2)) maps

/-- LPS `Sys/Mm/Mmap.v:403` `brk_model_next`. -/
def brkModelNext (h : VmMaps) (req r : Word) : VmMaps :=
  { h with maps := brkMapsNext h req r
           noaccess := mapsSubtractRanges h.noaccess (brkUnmaps r h.brk)
           brk := r }

/-- LPS `Sys/Mm/Mmap.v:585` `forget_vm_ranges`. -/
def forgetVmRanges : List (Word × Word) → Model → Model
  | [], m => m
  | (a, n) :: rest, m => forgetVmRanges rest (vmForgetRange (uns a) (uns a + uns n) m)

/-- LPS `Sys/Mm/Mmap.v:593` `with_brk_next`. -/
def withBrkNext (m : Model) (req r : Word) : Model :=
  forgetVmRanges (brkUnmaps r m.vmmaps.brk) (m.withVmmaps (brkModelNext m.vmmaps req r))

/-- LPS `Sys/Mm/Mmap.v:598` `brk_spec`. -/
def brkSpec (req : Word) : Sys SyscallEffect := do
  let m ← getModel
  let h := m.vmmaps
  let r ← Sys.choose fun r => brkROk m req r = true
  modify fun _ => withBrkNext m req r
  Sys.pure { ret := r, writes := [], zeros := brkZeros req r h.brk, unmaps := brkUnmaps r h.brk }

/-- LPS `Sys/Mm/Mmap.v:637` `brk_budget_refused_b`. -/
def brkBudgetRefusedB (m : Model) (req : Word) : Bool :=
  let h := m.vmmaps
  !(wIs0 req || decide (uns req < uns (minBrk h))) && decide (0 < uns h.brk) &&
    decide (uns h.brk < uns req) && !brkBudgetOk m req

/-- LPS `Sys/Mm/Mmap.v:645` `mmap_errnos`: refusals without cause. -/
def mmapErrnos : List Int := [ENOMEM]

/-- LPS `Sys/Mm/Mmap.v:687` `mmap_flags_core`: the flags without `MAP_NORESERVE`. -/
def mmapFlagsCore (flags : Word) : Int :=
  Int.ofNat (flags.toNat - (flags.toNat &&& MAP_NORESERVE.toNat))
/-- LPS `Sys/Mm/Mmap.v:690` `mmap_noreserve_b`. -/
def mmapNoreserveB (flags : Word) : Bool := flags.toNat &&& MAP_NORESERVE.toNat != 0
/-- LPS `Sys/Mm/Mmap.v:693` `with_mmap_backing`. -/
def withMmapBacking (flags a n : Word) (m : Model) : Model :=
  if mmapNoreserveB flags then vmAddLazy a n m else m
/-- LPS `Sys/Mm/Mmap.v:696` `with_mmap_replacement`. -/
def withMmapReplacement (flags a n : Word) (m : Model) : Model :=
  withMmapBacking flags a n (vmForgetRange (uns a) (uns a + uns n) m)
/-- LPS `Sys/Mm/Mmap.v:703` `with_mmap_destroyed`. -/
def withMmapDestroyed (a n : Word) (h' : VmMaps) (m : Model) : Model :=
  vmForgetRange (uns a) (uns a + uns n) (m.withVmmaps h')
/-- LPS `Sys/Mm/Mmap.v:761` `mmap_anon_b`. -/
def mmapAnonB (flags : Word) : Bool := flags.toNat &&& MAP_ANONYMOUS.toNat != 0
/-- LPS `Sys/Mm/Mmap.v:780` `mmap_off_aligned_b`. -/
def mmapOffAlignedB (off : Word) : Bool := uns off % pageSize == 0
/-- LPS `Sys/Mm/Mmap.v:816` `mmap_pglen_ok_b`. -/
def mmapPglenOkB (len : Word) : Bool := decide (pageRoundUp (uns len) < twoPow64)
/-- LPS `Sys/Mm/Mmap.v:890` `mmap_plain_anon_b`. -/
def mmapPlainAnonB (flags : Word) : Bool :=
  mmapAnonB flags && flags.toNat &&& MAP_HUGETLB.toNat == 0
/-- LPS `Sys/Mm/Mmap.v:999` `mmap_modeled_b`: `PROT_READ|PROT_WRITE` and
`MAP_PRIVATE|MAP_ANONYMOUS`. -/
def mmapModeledB (prot flags off : Word) : Bool :=
  uns prot == PROT_READ + PROT_WRITE && mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS &&
    wIs0 off
/-- LPS `Sys/Mm/Mmap.v:1009` `mmap_noaccess_b`. -/
def mmapNoaccessB (prot flags off : Word) : Bool :=
  uns prot == PROT_NONE && mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS && wIs0 off
/-- LPS `Sys/Mm/Mmap.v:1017` `mmap_fixed_noaccess_b`. -/
def mmapFixedNoaccessB (prot flags off : Word) : Bool :=
  uns prot == PROT_NONE && mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED &&
    wIs0 off
/-- LPS `Sys/Mm/Mmap.v:1065` `mmap_fixed_rw_b`. -/
def mmapFixedRwB (prot flags off : Word) : Bool :=
  uns prot == PROT_READ + PROT_WRITE &&
    mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED && wIs0 off

/-- LPS `Sys/Mm/Mmap.v:1074` `mmap_fixed_rw_next`. -/
def mmapFixedRwNext (h : VmMaps) (addr n : Word) : VmMaps :=
  { h with noaccess := mapsSubtract h.noaccess (uns addr) (uns addr + uns n) }
/-- LPS `Sys/Mm/Mmap.v:1143` `mmap_fixed_destroyed_next`. -/
def mmapFixedDestroyedNext (h : VmMaps) (addr n : Word) : VmMaps :=
  { h with maps := mapsSubtract h.maps (uns addr) (uns addr + uns n)
           noaccess := mapsSubtract h.noaccess (uns addr) (uns addr + uns n) }
/-- LPS `Sys/Mm/Mmap.v:1164` `mmap_fixed_rw_span_next`. -/
def mmapFixedRwSpanNext (h : VmMaps) (addr n : Word) : VmMaps :=
  { h with maps := (addr, n) :: mapsSubtract h.maps (uns addr) (uns addr + uns n)
           noaccess := mapsSubtract h.noaccess (uns addr) (uns addr + uns n) }
/-- LPS `Sys/Mm/Mmap.v:1190` `mmap_fixed_noaccess_span_next`. -/
def mmapFixedNoaccessSpanNext (h : VmMaps) (addr n : Word) : VmMaps :=
  { h with maps := (addr, n) :: mapsSubtract h.maps (uns addr) (uns addr + uns n)
           noaccess := (addr, n) :: mapsSubtract h.noaccess (uns addr) (uns addr + uns n) }

/-- LPS `Sys/Mm/Mmap.v:1233` `mmap_noreserve_backed_ok`: a reserving mapping must fit the
budget now. -/
def mmapNoreserveBackedOk (flags : Word) (m : Model) (nZ : Int) : Bool :=
  if mmapNoreserveB flags then true else decide (vmBackingUsed m + nZ ≤ m.vmmaps.limit)

/-- LPS `Sys/Mm/Mmap.v:1238` `mmap_fixed_rw_budget_ok`. -/
def mmapFixedRwBudgetOk (flags : Word) (m : Model) (addr n : Word) : Bool :=
  vmBackingWithinLimit
    (withMmapReplacement flags addr n (m.withVmmaps (mmapFixedRwNext m.vmmaps addr n)))

/-- LPS `Sys/Mm/Mmap.v:1255` `mmap_fixed_rw_span_budget_ok`. -/
def mmapFixedRwSpanBudgetOk (flags : Word) (m : Model) (addr n : Word) : Bool :=
  vmBackingWithinLimit
    (withMmapReplacement flags addr n (m.withVmmaps (mmapFixedRwSpanNext m.vmmaps addr n)))

/-- LPS `Sys/Mm/Mmap.v:1384` `mmap_noreplace_flags_b`. -/
def mmapNoreplaceFlagsB (flags : Word) : Bool :=
  mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED_NOREPLACE ||
    mmapFlagsCore flags == MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED + MAP_FIXED_NOREPLACE
/-- LPS `Sys/Mm/Mmap.v:1396` `mmap_noreplace_rw_b`. -/
def mmapNoreplaceRwB (prot flags off : Word) : Bool :=
  uns prot == PROT_READ + PROT_WRITE && mmapNoreplaceFlagsB flags && wIs0 off
/-- LPS `Sys/Mm/Mmap.v:1400` `mmap_noreplace_noaccess_b`. -/
def mmapNoreplaceNoaccessB (prot flags off : Word) : Bool :=
  uns prot == PROT_NONE && mmapNoreplaceFlagsB flags && wIs0 off

/-- The refusal without cause that every granting arm of `mmap` sits beside. -/
def mmapRefused : Sys SyscallEffect := do
  let e ← errnoFrom mmapErrnos
  errRet e

/-- A refusal without cause that still destroys the old mapping (LPS
`Sys/Mm/Mmap.v:1725-1728`): Linux unmaps before the new mapping can fail. -/
def mmapDestroyedRefusal (addr n : Word) (h : VmMaps) : Sys SyscallEffect := do
  let e ← errnoFrom mmapErrnos
  modify fun m => withMmapDestroyed addr n (mmapFixedDestroyedNext h addr n) m
  Sys.pure { ret := errnoRet e, writes := [], zeros := [], unmaps := [(addr, n)] }

/-- The bounds every `MAP_FIXED`-family arm runs first (LPS `Sys/Mm/Mmap.v:1644-1651`). -/
def mmapFixedBounds (addr len : Word) (k : Model → VmMaps → Int → Word → Sys SyscallEffect) :
    Sys SyscallEffect :=
  let nZ := pageRoundUp (uns len)
  if twoPow64 ≤ uns addr + nZ then errRet ENOMEM
  else do
    let m ← getModel
    let h := m.vmmaps
    if !decide (uns addr + nZ ≤ allocTop h) then unmodeled
    else if uns addr % pageSize ≠ 0 then errRet EINVAL
    else if !decide (0 < uns addr) then unmodeled
    else k m h nZ (zw nZ)

/-- LPS `Sys/Mm/Mmap.v:1470` `mmap_spec`: anonymous private mappings, fresh or fixed,
read-write or `PROT_NONE`; file mappings are `unmodeled`. A fresh mapping may land at any
free page-aligned address below `alloc_top` (wider than any one kernel's policy). -/
def mmapSpec (addr len prot flags _fd off : Word) : Sys SyscallEffect :=
  if !mmapOffAlignedB off then (if mmapPglenOkB len then errRet EINVAL else unmodeled)
  else if !mmapAnonB flags then unmodeled
  else if wIs0 len then (if mmapPlainAnonB flags then errRet EINVAL else unmodeled)
  else if mmapModeledB prot flags off then
    Sys.alt mmapRefused do
      let m ← getModel
      let h := m.vmmaps
      let nZ := pageRoundUp (uns len)
      let n := zw nZ
      let a ← Sys.choose fun a : Word =>
        uns a % pageSize = 0 ∧ 0 < uns a ∧ uns a + nZ ≤ allocTop h ∧
          regionFree (h.reserved ++ h.maps) a n = true ∧ mmapNoreserveBackedOk flags m nZ = true
      modify fun _ => withMmapBacking flags a n (m.withVmmaps { h with maps := (a, n) :: h.maps })
      Sys.pure (mkEffect a [] [(a, n)])
  else if mmapNoaccessB prot flags off then
    Sys.alt mmapRefused do
      let m ← getModel
      let h := m.vmmaps
      let nZ := pageRoundUp (uns len)
      let n := zw nZ
      let a ← Sys.choose fun a : Word =>
        uns a % pageSize = 0 ∧ 0 < uns a ∧ uns a + nZ ≤ allocTop h ∧
          regionFree (h.reserved ++ h.maps) a n = true
      modify fun _ => withMmapBacking flags a n
        (m.withVmmaps { h with maps := (a, n) :: h.maps, noaccess := (a, n) :: h.noaccess })
      Sys.pure { ret := a, writes := [], zeros := [], unmaps := [(a, n)] }
  else if mmapFixedNoaccessB prot flags off then
    mmapFixedBounds addr len fun m h _ n =>
      if regionFree h.reserved addr n && mapContains h.maps addr n then
        Sys.alt mmapRefused
          (Sys.alt
            (do
              modify fun _ => withMmapReplacement flags addr n
                (m.withVmmaps { h with noaccess :=
                  (addr, n) :: mapsSubtract h.noaccess (uns addr) (uns addr + uns n) })
              Sys.pure { ret := addr, writes := [], zeros := [], unmaps := [(addr, n)] })
            (mmapDestroyedRefusal addr n h))
      else if regionFree (h.reserved ++ h.maps) addr n then
        Sys.alt mmapRefused do
          let a ← Sys.choose fun a : Word => a = addr
          modify fun _ => withMmapBacking flags a n
            (m.withVmmaps { h with maps := (a, n) :: h.maps, noaccess := (a, n) :: h.noaccess })
          Sys.pure { ret := a, writes := [], zeros := [], unmaps := [(a, n)] }
      else if regionFree h.reserved addr n then
        Sys.alt mmapRefused
          (Sys.alt
            (do
              modify fun _ => withMmapReplacement flags addr n
                (m.withVmmaps (mmapFixedNoaccessSpanNext h addr n))
              Sys.pure { ret := addr, writes := [], zeros := [], unmaps := [(addr, n)] })
            (mmapDestroyedRefusal addr n h))
      else unmodeled
  else if mmapFixedRwB prot flags off then
    mmapFixedBounds addr len fun m h nZ n =>
      if regionFree h.reserved addr n && mapContains h.maps addr n then
        Sys.alt mmapRefused
          (Sys.alt
            (do
              let _ ← Sys.choose fun _ : Unit => mmapFixedRwBudgetOk flags m addr n = true
              modify fun _ => withMmapReplacement flags addr n
                (m.withVmmaps (mmapFixedRwNext h addr n))
              Sys.pure (mkEffect addr [] [(addr, n)]))
            (mmapDestroyedRefusal addr n h))
      else if regionFree (h.reserved ++ h.maps) addr n then
        Sys.alt mmapRefused do
          let a ← Sys.choose fun a : Word => a = addr ∧ mmapNoreserveBackedOk flags m nZ = true
          modify fun _ => withMmapBacking flags a n
            (m.withVmmaps { h with maps := (a, n) :: h.maps })
          Sys.pure (mkEffect a [] [(a, n)])
      else if regionFree h.reserved addr n then
        Sys.alt mmapRefused
          (Sys.alt
            (do
              let _ ← Sys.choose fun _ : Unit => mmapFixedRwSpanBudgetOk flags m addr n = true
              modify fun _ => withMmapReplacement flags addr n
                (m.withVmmaps (mmapFixedRwSpanNext h addr n))
              Sys.pure (mkEffect addr [] [(addr, n)]))
            (mmapDestroyedRefusal addr n h))
      else unmodeled
  else if mmapNoreplaceNoaccessB prot flags off then
    mmapFixedBounds addr len fun m h _ n =>
      if regionFree (h.reserved ++ h.maps) addr n then
        Sys.alt mmapRefused do
          let a ← Sys.choose fun a : Word => a = addr
          modify fun _ => withMmapBacking flags a n
            (m.withVmmaps { h with maps := (a, n) :: h.maps, noaccess := (a, n) :: h.noaccess })
          Sys.pure { ret := a, writes := [], zeros := [], unmaps := [(a, n)] }
      else Sys.alt mmapRefused (errRet EEXIST)
  else if mmapNoreplaceRwB prot flags off then
    mmapFixedBounds addr len fun m h nZ n =>
      if regionFree (h.reserved ++ h.maps) addr n then
        Sys.alt mmapRefused do
          let a ← Sys.choose fun a : Word => a = addr ∧ mmapNoreserveBackedOk flags m nZ = true
          modify fun _ => withMmapBacking flags a n
            (m.withVmmaps { h with maps := (a, n) :: h.maps })
          Sys.pure (mkEffect a [] [(a, n)])
      else Sys.alt mmapRefused (errRet EEXIST)
  else unmodeled

/-- LPS `Sys/Mm/Mmap.v:2119` `mmap_budget_refused_b`: this `mmap` is refused for budget. -/
def mmapBudgetRefusedB (addr len prot flags _fd off : Word) (m : Model) : Bool :=
  if !mmapOffAlignedB off then false
  else if !mmapAnonB flags then false
  else if wIs0 len then false
  else
    let h := m.vmmaps
    let nZ := pageRoundUp (uns len)
    let n := zw nZ
    let fixedBounds : Bool :=
      decide (uns addr + nZ < twoPow64) && decide (uns addr + nZ ≤ allocTop h) &&
        uns addr % pageSize == 0 && decide (0 < uns addr)
    if mmapModeledB prot flags off then !mmapNoreserveBackedOk flags m nZ
    else if mmapNoaccessB prot flags off then false
    else if mmapFixedNoaccessB prot flags off then false
    else if mmapFixedRwB prot flags off then
      if !fixedBounds then false
      else if regionFree h.reserved addr n && mapContains h.maps addr n then
        !mmapFixedRwBudgetOk flags m addr n
      else if regionFree (h.reserved ++ h.maps) addr n then !mmapNoreserveBackedOk flags m nZ
      else if regionFree h.reserved addr n then !mmapFixedRwSpanBudgetOk flags m addr n
      else false
    else if mmapNoreplaceNoaccessB prot flags off then false
    else if mmapNoreplaceRwB prot flags off then
      if !fixedBounds then false
      else if regionFree (h.reserved ++ h.maps) addr n then !mmapNoreserveBackedOk flags m nZ
      else false
    else false

/-- LPS `Sys/Mm/Mmap.v:2220` `munmap_free_ok`. -/
def munmapFreeOk (h : VmMaps) (addr : Word) (nZ : Int) : Bool :=
  regionFree (h.reserved ++ h.maps) addr (zw nZ) && decide (uns addr + nZ ≤ allocTop h)

/-- LPS `Sys/Mm/Mmap.v:2224` `munmap_spec`: only whole recorded mappings, or free ranges, are
modelled. -/
def munmapSpec (addr len : Word) : Sys SyscallEffect :=
  if uns addr % pageSize ≠ 0 || wIs0 len then errRet EINVAL
  else do
    let h ← getVmmaps
    let nZ := pageRoundUp (uns len)
    if taskSize < uns addr + nZ then errRet EINVAL
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

end Silmaril.Process.LPS
