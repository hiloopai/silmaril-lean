module

public import Silmaril.Libc.Ptmalloc.Sim.Defs
public import Silmaril.X86.Str9K.Thms

/-!
# ptmalloc x86sim: the machine memory as a `MemView`, and the two machines as `Mach`

Version- and block-independent glue between silmaril's process memory and the layered model's
abstract byte memory (`Silmaril.Data.MemView`):

* `memView m`: a byte is visible when it is below `2^64`, readable and backed; writable when it
  is below `2^64` and writable. So a `Cell` that holds is a successful `loadN` (`cell_load`).
* `memView_storeN`: a (readable) `storeN` is `MemView.store` of the cell it writes, so the
  stores of a block become `MemView.storeAll`, the form of the representation's leaf lemmas.
* `within_of_ww`: silmaril's `WritesWithin` is `Mach.Within`.
* `fsMach` (`Str9Fs`, no system calls) and `str9kMach` (`Str9K`, the process machine of the
  allocator proofs): `Mach` instances. Blocks are proved on `fsMach` (their code makes no system
  call) and lifted by `Triple.liftK`/`BlockSim.liftK` (`Str9K.fs_lift`).

Nothing here depends on glibc or on a version.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.X86sim

open Silmaril.Data
open Silmaril.Process (Memory Access addressLimit)
open Silmaril.X86 (MState Word Byte)
open Silmaril.X86.Ext (loadN storeN leValue leBytes)
open Silmaril.Machine.Execution (Reaches)

/-- **The memory as a `MemView`.** -/
def memView (m : Memory) : MemView where
  byte a := if a < addressLimit ∧ m.permits .read a = true then (m.bytes.get? a).map (·.toNat)
    else none
  writable a := decide (a < addressLimit) && m.permits .write a

theorem byte_memView_some {m : Memory} {a b : Nat} (h : (memView m).byte a = some b) :
    a < addressLimit ∧ m.permits .read a = true ∧ ∃ x, m.bytes.get? a = some x ∧ x.toNat = b := by
  simp only [memView] at h
  split at h
  · rename_i hc
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨hc.1, hc.2, x, hx, rfl⟩
  · cases h

theorem load_memView {m : Memory} : ∀ (k a v : Nat), (memView m).load a k = some v →
    (∀ i < k, a + i < addressLimit ∧ m.permits .read (a + i) = true) ∧
      (Memory.readBacking m.bytes a k).map leValue = some v
  | 0, a, v, h => by
    simp only [MemView.load, Option.some.injEq] at h
    subst h; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
  | k + 1, a, v, h => by
    simp only [MemView.load] at h
    cases hb : (memView m).byte a with
    | none => simp [hb] at h
    | some b =>
      cases hr : (memView m).load (a + 1) k with
      | none => simp [hb, hr] at h
      | some r =>
        simp only [hb, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨h1, h2, x, hx, rfl⟩ := byte_memView_some hb
        obtain ⟨ih1, ih2⟩ := load_memView k (a + 1) r hr
        refine ⟨fun i hi => ?_, ?_⟩
        · rcases i with _ | i
          · exact ⟨by simpa using h1, by simpa using h2⟩
          · rw [show a + (i + 1) = a + 1 + i by omega]; exact ih1 i (by omega)
        · obtain ⟨bs, hbs, hv⟩ := Option.map_eq_some_iff.1 ih2
          simp only [Std.ExtHashMap.get?_eq_getElem?] at hx
          simp [Memory.readBacking, hx, hbs, leValue, hv, ← h]

theorem leValue_lt : ∀ bs : List Byte, leValue bs < 2 ^ (8 * bs.length)
  | [] => by simp [leValue]
  | b :: bs => by
    have := leValue_lt bs
    have hb := b.isLt
    simp only [leValue, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by omega, Nat.pow_add]
    have : 256 * leValue bs + 256 ≤ 256 * 2 ^ (8 * bs.length) := by omega
    omega

/-- **A cell that holds is a load**: its bytes are below `2^64`, readable, writable, and the
`loadN` of its width at its address returns its value. -/
theorem cell_load {m : Memory} {c : Cell} (h : c.Holds (memView m)) (hk : 0 < c.width) :
    loadN m (BitVec.ofNat 64 c.addr) c.width = some (BitVec.ofNat 64 c.val) ∧
      c.addr + c.width ≤ addressLimit ∧ m.Permitted .read c.addr c.width ∧
      m.Permitted .write c.addr c.width ∧ c.val < 2 ^ (8 * c.width) := by
  obtain ⟨hl, hw⟩ := h
  obtain ⟨hp, hv⟩ := load_memView c.width c.addr c.val hl
  have hlast := (hp (c.width - 1) (by omega)).1
  have hbound : c.addr + c.width ≤ addressLimit := by omega
  have ha : c.addr < addressLimit := by omega
  have hrd : m.Permitted .read c.addr c.width := by
    simp only [Memory.Permitted, Memory.checkSpan_iff]
    exact ⟨ha, hbound, fun i hi => (hp i hi).2⟩
  have hwr : m.Permitted .write c.addr c.width := by
    simp only [Memory.Permitted, Memory.checkSpan_iff]
    refine ⟨ha, hbound, fun i hi => ?_⟩
    have := hw i hi
    simp only [memView, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  obtain ⟨bs, hbs, hbv⟩ := Option.map_eq_some_iff.1 hv
  have hlen := Memory.readBacking_length hbs
  refine ⟨?_, hbound, hrd, hwr, by rw [← hbv, ← hlen]; exact leValue_lt bs⟩
  have hmod : (BitVec.ofNat 64 c.addr).toNat = c.addr := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa [addressLimit] using ha)
  simp only [loadN, hmod, Memory.readBytes, Memory.readWith]
  simp only [show m.checkSpan .read c.addr c.width = true from hrd, ↓reduceIte, hbs,
    Option.map_some, hbv]

/-! ## Stores -/

theorem div_mod_256 (x k j : Nat) (hj : j < k) :
    x % 2 ^ (8 * k) / 256 ^ j % 256 = x / 256 ^ j % 256 := by
  have e : 2 ^ (8 * k) = 256 ^ j * 2 ^ (8 * (k - j)) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (by
    rw [show 8 * (k - j) = 8 + 8 * (k - j - 1) by omega, Nat.pow_add]; exact Nat.dvd_mul_right _ _)

theorem wordByte_toNat (w : Word) (j : Nat) :
    (Silmaril.Machine.LittleEndian.wordByte w j).toNat = w.toNat / 256 ^ j % 256 := by
  simp only [Silmaril.Machine.LittleEndian.wordByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]

/-- **A store is `MemView.store`** of the cell it writes (value: the low `k` bytes), when the
stored bytes were readable. -/
theorem memView_storeN {m m' : Memory} {A w : Word} {k : Nat} (h : storeN m A k w = some m')
    (hr : m.Permitted .read A.toNat k) :
    memView m' = (memView m).store ⟨A.toNat, k, w.toNat % 2 ^ (8 * k)⟩ := by
  have wo := Silmaril.X86.Ext.storeN_writesOnly h
  have hperm : ∀ acc a, m'.permits acc a = m.permits acc a := by
    intro acc a; unfold Memory.permits; rw [wo.1]
  simp only [MemView.store, memView]
  congr 1
  · funext a
    simp only [hperm]
    by_cases hin : A.toNat ≤ a ∧ a < A.toNat + k
    · simp only [hin.1, hin.2, and_self, ↓reduceIte]
      have hc : m.Permitted .read A.toNat k := hr
      simp only [Memory.Permitted, Memory.checkSpan_iff] at hc
      have hlim : a < addressLimit := by omega
      have hrd := hc.2.2 (a - A.toNat) (by omega)
      rw [show A.toNat + (a - A.toNat) = a by omega] at hrd
      simp only [hlim, hrd, and_self, ↓reduceIte]
      have hg := Memory.writeBytes_get h (a - A.toNat) (by simp; omega)
      rw [show A.toNat + (a - A.toNat) = a by omega] at hg
      rw [hg]
      simp only [leBytes, List.getElem_ofFn, Option.map_some, wordByte_toNat]
      rw [div_mod_256 _ _ _ (by omega)]
    · simp only [hin, ↓reduceIte]
      have := wo.2 a (by omega)
      rw [this]
  · funext a; simp only [hperm]

/-! ## Footprints -/

/-- **`WritesWithin` is `Within`** on the views. -/
theorem within_of_ww {m m' : Memory} {fp : Nat → Prop} (h : m.WritesWithin m' fp) (a : Nat)
    (ha : ¬ fp a) :
    (memView m).byte a = (memView m').byte a ∧ (memView m).writable a = (memView m').writable a := by
  have hp : ∀ acc, m'.permits acc a = m.permits acc a := fun acc => h.permits acc a
  have hb := h.2 a ha
  simp only [Std.ExtHashMap.get?_eq_getElem?] at hb
  refine ⟨?_, ?_⟩
  · simp [memView, hp, hb]
  · simp [memView, hp]

/-! ## The machines -/

/-- **`Str9Fs` as a `Mach`**: the user-mode machine without system calls (where blocks are
proved). -/
def fsMach : Mach where
  St := MState
  pc s := s.core.rip.toNat
  view s := memView s.memory
  reach := Reaches Silmaril.X86.Str9Fs.step
  refl s := Reaches.refl _ s
  trans h₁ h₂ := Reaches.trans h₁ h₂

/-- **`Str9K` as a `Mach`**: the process machine of the allocator proofs (`Str9G` with the
system calls, the kernel's answers as an oracle). -/
def str9kMach : Mach where
  St := Silmaril.X86.Str9K.KState
  pc x := x.s.x.m.core.rip.toNat
  view x := memView x.s.x.m.memory
  reach := Reaches Silmaril.X86.Str9K.isa.step
  refl s := Reaches.refl _ s
  trans h₁ h₂ := Reaches.trans h₁ h₂

/-- The `MState` of a `Str9K` state. -/
def projK (x : Silmaril.X86.Str9K.KState) : MState := x.s.x.m

/-- **A `Str9Fs` triple is a `Str9K` triple** (the run makes no system call: `fs_lift`). -/
theorem Triple.liftK {P Q : MState → Prop} {fp : Nat → Prop} (h : fsMach.Triple P Q fp) :
    str9kMach.Triple (fun x => P (projK x)) (fun x => Q (projK x)) fp := by
  intro x hx
  obtain ⟨m', hr, hq, hw⟩ := h (projK x) hx
  obtain ⟨y, hy, rfl, -⟩ := Silmaril.X86.Str9K.fs_lift hr
  exact ⟨y, hy, hq, hw⟩

/-- A block on `Str9Fs`, read on `Str9K`. -/
def liftBlock {A : Type} (b : Block fsMach A) : Block str9kMach A where
  entry := b.entry
  exits := b.exits
  pre a x := b.pre a (projK x)
  post a x := b.post a (projK x)
  fp := b.fp

/-- **Block simulations lift to `Str9K`** for any relation that reads the machine state through
its `MState` (as `LocalAt` does: it reads only the memory view). -/
theorem BlockSim.liftK {A : Type} {R : A → MState → Prop} {R' : A → str9kMach.St → Prop}
    (hR : ∀ a x, R' a x ↔ R a (projK x)) {step : A → A → Prop} {b : Block fsMach A}
    (h : BlockSim (M := fsMach) R step b) : BlockSim (M := str9kMach) R' step (liftBlock b) := by
  intro a
  have := Triple.liftK (h a)
  refine Mach.Triple.conseq this (fun x hx => ?_) (fun x hx => ?_) (fun _ h => h)
  · exact ⟨(hR a x).1 hx.1, hx.2.1, hx.2.2⟩
  · obtain ⟨h1, a', h2, h3, h4⟩ := hx
    exact ⟨h1, a', h2, (hR a' x).2 h3, h4⟩

/-- `LocalAt` on `Str9K` reads the `MState`. -/
theorem localAt_k (C : Config) (P : RepAt) (a : AState) (x : str9kMach.St) :
    LocalAt C P str9kMach a x ↔ LocalAt C P fsMach a (projK x) := Iff.rfl

end Silmaril.Libc.Ptmalloc.X86sim
