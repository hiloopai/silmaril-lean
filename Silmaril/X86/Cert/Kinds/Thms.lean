module

public import Silmaril.X86.Cert.Thms
public import Silmaril.X86.BlockCert.Store.Thms
public import Silmaril.X86.BlockCert.Ext8.Thms
public import Silmaril.X86.BlockCert.Calls.Thms
public import Silmaril.X86.BlockCert9.Thms
import Silmaril.Proofs.X86.Cert.Kinds.Within

/-!
# The six existing certificates as instances of the generic `Cert`

Block kinds (`Silmaril.X86.Cert.Kinds`), each with its soundness from a bridge that keeps
every step inside the code (`Proofs/.../Cert/Kinds/Within.lean`):

| kind | machine | block data | check | run |
|---|---|---|---|---|
| `bir` | `Open.isa` | Bir9 listing | `BlockCert.listingAt` (no write) | `BlockCert.runL` |
| `store` | `Open.isa` | Bir9 listing | `BlockCert.listingAtW` (last instruction may write) | `BlockCert.runL` |
| `ext8` | `Open.isa` | `Ext8` listing | `BlockCert8.listing8` | `BlockCert8.run8` |
| `ext9` | `Open9.isa` | `BlockCert9.Code` | `Code.check` | `Code.run` |
| `calls` | `Open.isa` | `store ⊕ call store` | as `CallCert.checked` | listing, or `call` + callee contract |

All listing kinds are **local** (`Admits = BlockKind.Local`: any run predicate containing the
code region) and their WP ignores the run predicate.

**Bridges** (each per-kind certificate maps to a `Cert`, its checks and VC carry over, and the
generic theorems re-derive its `total` and add the first-return reading):

* `BlockCert.FunCert.toCert`, `checked_toCert`, `vc_toCert`, `total_generic`, `totalIn`,
  `strict`;
* `BlockCert.FunCert.toCertW`, `checkedW_toCertW`, `vcW_toCertW`, `totalW_generic`, `totalInW`,
  `strictW` (libmini's writing certificates);
* `BlockCert8.Cert.toCert`, …, `total_generic`, `totalIn`, `strict`;
* `BlockCert9.FunCert9.toCert`, …, `total_generic`, `totalIn`, `strict` (on `Open9.isa`);
* `BlockCert.CallCert.toCert`, `checked_toCert`, `vc_toCert`, `total_generic`. The old call VC
  takes callees as plain total contracts (`Callee.ofContract`), whose runs are unconstrained,
  so a `CallCert` gives `Spec.Total` only; first return for a caller needs callees with a
  `TotalIn` run predicate (`Callee`, for instance `InCode` of the callee's code from its own
  certificate's `totalIn`) and the generic `Cert.strict`.
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.Bir9 (LInstr)
open FnContract (RunsIn InCode AbiEntry Spec Returned RetOutside runsIn_mono)

namespace Cert.Kinds

open Silmaril.Proofs.X86.Cert.Kinds

/-- **The block bridge inside the code**: a checked no-write Bir9 listing that runs takes
every step inside the code, memory unchanged (exported for kinds on other machines). -/
theorem runL_within {code : List Byte} {base : Word} {L : List (LInstr × Nat)} {o : Nat}
    {m m' : MState} (hok : BlockCert.listingAt code o L = true) (hl : Loaded m.memory base code)
    (hrip : m.core.rip = base + BitVec.ofNat 64 o) (h : BlockCert.runL L m = some m') :
    RunsIn Open.isa (InCode Open.isa base code.length) m m' ∧ m'.memory = m.memory :=
  Silmaril.Proofs.X86.Cert.Kinds.runL_within hok hl hrip h

/-! Soundness of the listing kinds (each from a bridge inside the code). -/

theorem bir_sound {code : List Byte} {base : Word} {o : Nat} {L : List (LInstr × Nat)}
    {R : MState → Prop} {s : MState} {Q : MState → Prop} (hok : BlockCert.listingAt code o L = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open.isa base code.length R)
    (hwp : ∃ t, BlockCert.runL L s = some t ∧ Q t) : ∃ t, RunsIn Open.isa R s t ∧ Q t := by
  obtain ⟨t, ht, hq⟩ := hwp
  exact ⟨t, runsIn_mono hadm
    (Silmaril.Proofs.X86.Cert.Kinds.runL_within hok hl hrip ht).1, hq⟩

theorem store_sound {code : List Byte} {base : Word} {o : Nat} {L : List (LInstr × Nat)}
    {R : MState → Prop} {s : MState} {Q : MState → Prop}
    (hok : BlockCert.listingAtW code o L = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open.isa base code.length R)
    (hwp : ∃ t, BlockCert.runL L s = some t ∧ Q t) : ∃ t, RunsIn Open.isa R s t ∧ Q t := by
  obtain ⟨t, ht, hq⟩ := hwp
  exact ⟨t, runsIn_mono hadm (runLW_within hok hl hrip ht), hq⟩

theorem ext8_sound {code : List Byte} {base : Word} {o : Nat} {L : List BlockCert8.LI}
    {R : MState → Prop} {s : MState} {Q : MState → Prop}
    (hok : BlockCert8.listing8 code o L = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open.isa base code.length R)
    (hwp : ∃ t, BlockCert8.run8 L s = some t ∧ Q t) : ∃ t, RunsIn Open.isa R s t ∧ Q t := by
  obtain ⟨t, ht, hq⟩ := hwp
  exact ⟨t, runsIn_mono hadm (run8_within L _ _ _ hok hl hrip ht).1, hq⟩

theorem ext9_sound {code : List Byte} {base : Word} {o : Nat} {c : BlockCert9.Code}
    {R : MState → Prop} {s : MState} {Q : MState → Prop} (hok : c.check code o = true)
    (hl : Loaded s.memory base code) (hrip : s.core.rip = base + BitVec.ofNat 64 o)
    (hadm : BlockKind.Local Open9.isa base code.length R)
    (hwp : ∃ t, c.run s = some t ∧ Q t) : ∃ t, RunsIn Open9.isa R s t ∧ Q t := by
  obtain ⟨t, ht, hq⟩ := hwp
  exact ⟨t, runsIn_mono hadm (code_run_within hok hl hrip ht).1, hq⟩

/-- Bir9 listings that write no memory, on the open machine. -/
def bir : BlockKind Open.isa where
  B := List (LInstr × Nat)
  check := BlockCert.listingAt
  WP L _ s Q := ∃ t, BlockCert.runL L s = some t ∧ Q t
  Admits := BlockKind.Local Open.isa
  admits_top _ _ _ _ := trivial
  sound hok _ hl hrip hadm hwp := bir_sound hok hl hrip hadm hwp

/-- Bir9 listings whose last instruction may write memory, on the open machine. -/
def store : BlockKind Open.isa where
  B := List (LInstr × Nat)
  check := BlockCert.listingAtW
  WP L _ s Q := ∃ t, BlockCert.runL L s = some t ∧ Q t
  Admits := BlockKind.Local Open.isa
  admits_top _ _ _ _ := trivial
  sound hok _ hl hrip hadm hwp := store_sound hok hl hrip hadm hwp

/-- `Ext8` listings with checked runs, on the open machine. -/
def ext8 : BlockKind Open.isa where
  B := List BlockCert8.LI
  check := BlockCert8.listing8
  WP L _ s Q := ∃ t, BlockCert8.run8 L s = some t ∧ Q t
  Admits := BlockKind.Local Open.isa
  admits_top _ _ _ _ := trivial
  sound hok _ hl hrip hadm hwp := ext8_sound hok hl hrip hadm hwp

/-- Bir9 or `Ext9` block code, on the `Ext9` open machine. -/
def ext9 : BlockKind Open9.isa where
  B := BlockCert9.Code
  check code o c := c.check code o
  WP c _ s Q := ∃ t, c.run s = some t ∧ Q t
  Admits := BlockKind.Local Open9.isa
  admits_top _ _ _ _ := trivial
  sound hok _ hl hrip hadm hwp := ext9_sound hok hl hrip hadm hwp

/-- Writing listings and call blocks (a `call rel32` listing, then the callee). -/
def calls : BlockKind Open.isa := BlockKind.sum store (BlockKind.call store)

end Cert.Kinds

open Cert.Kinds

/-! ## `BlockCert.FunCert` (no writes) -/

namespace BlockCert.FunCert

/-- A function certificate as a generic certificate of `bir` blocks. -/
def toCert (F : FunCert) : Cert Open.isa bir :=
  ⟨F.code, F.base, F.blocks.map fun b => ⟨b.off, b.instrs⟩, F.ann, F.measure⟩

theorem mem_toCert {F : FunCert} {b : Blk} (hb : b ∈ F.blocks) :
    (⟨b.off, b.instrs⟩ : CBlock bir) ∈ F.toCert.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem checked_toCert {F : FunCert} (hc : F.checked = true) : F.toCert.checked = true := by
  simp only [Cert.checked, toCert, List.all_map]
  exact hc

theorem vc_toCert {F : FunCert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) : F.toCert.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  obtain ⟨m', hr, hn⟩ := hvc b0 hb0 s0 m ha hrip hl
  have hmem := (runL_open (List.all_eq_true.mp hc b0 hb0) hl hrip hr).2
  refine ⟨m', hr, ?_⟩
  rcases hn with hq | ⟨b', hb', hrip', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCert hb', hrip', by show Loaded m'.memory _ _; rw [hmem]; exact hl,
      ha', hlt⟩

/-- **`FunCert.total`, re-derived from the generic `Cert.total`.** -/
theorem total_generic {F : FunCert} (S : Spec MState) {entry : Blk} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Cert.total (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc) (vc_toCert hc hvc) hpre

/-- A function certificate's run takes every step inside the function's code (the generic
form of `Abi.OpenMachine.totalIn_of_funCert`). -/
theorem totalIn {F : FunCert} (S : Spec MState) {entry : Blk} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.TotalIn Open.isa fun _ => InCode Open.isa F.base F.code.length :=
  Cert.totalIn (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc)
    (Cert.vcIn_of_vc _ (fun _ _ _ _ h => h) (vc_toCert hc hvc)) (fun _ _ _ _ _ h => h) hpre

/-- **First return from a function certificate**, on entries whose return address lies
outside the code. -/
theorem strict {F : FunCert} (S : Spec MState) {entry : Blk} (hentry : entry ∈ F.blocks)
    (hc : F.checked = true) (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    (S.restrict (RetOutside Open.isa F.base F.code.length)).Strict Open.isa :=
  Cert.strict_of_local (F := F.toCert) S (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (mem_toCert hentry) (checked_toCert hc) (vc_toCert hc hvc) hpre

/-! ## `BlockCert.FunCert` with writing blocks (`checkedW`, `VCW`) -/

/-- A function certificate with writing blocks as a generic certificate of `store` blocks. -/
def toCertW (F : FunCert) : Cert Open.isa store :=
  ⟨F.code, F.base, F.blocks.map fun b => ⟨b.off, b.instrs⟩, F.ann, F.measure⟩

theorem mem_toCertW {F : FunCert} {b : Blk} (hb : b ∈ F.blocks) :
    (⟨b.off, b.instrs⟩ : CBlock store) ∈ F.toCertW.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem checkedW_toCertW {F : FunCert} (hc : F.checkedW = true) : F.toCertW.checked = true := by
  simp only [Cert.checked, toCertW, List.all_map]
  exact hc

theorem vcW_toCertW {F : FunCert} {Q : MState → MState → Prop} (hvc : F.VCW Q) :
    F.toCertW.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  obtain ⟨m', hr, hn⟩ := hvc b0 hb0 s0 m ha hrip hl
  refine ⟨m', hr, ?_⟩
  rcases hn with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCertW hb', hrip', hl', ha', hlt⟩

/-- **`FunCert.totalW`, re-derived from the generic `Cert.total`.** -/
theorem totalW_generic {F : FunCert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Cert.total (F := F.toCertW) S (mem_toCertW hentry) (checkedW_toCertW hc) (vcW_toCertW hvc) hpre

theorem totalInW {F : FunCert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.TotalIn Open.isa fun _ => InCode Open.isa F.base F.code.length :=
  Cert.totalIn (F := F.toCertW) S (mem_toCertW hentry) (checkedW_toCertW hc)
    (Cert.vcIn_of_vc _ (fun _ _ _ _ h => h) (vcW_toCertW hvc)) (fun _ _ _ _ _ h => h) hpre

/-- **First return from a function certificate with writing blocks.** -/
theorem strictW {F : FunCert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checkedW = true)
    (hvc : F.VCW fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    (S.restrict (RetOutside Open.isa F.base F.code.length)).Strict Open.isa :=
  Cert.strict_of_local (F := F.toCertW) S (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (mem_toCertW hentry) (checkedW_toCertW hc) (vcW_toCertW hvc) hpre

end BlockCert.FunCert

/-! ## `BlockCert8.Cert` -/

namespace BlockCert8.Cert

def toCert (F : BlockCert8.Cert) : Silmaril.X86.Cert Open.isa ext8 :=
  ⟨F.code, F.base, F.blocks.map fun b => ⟨b.off, b.instrs⟩, F.ann, F.measure⟩

theorem mem_toCert {F : BlockCert8.Cert} {b : Blk} (hb : b ∈ F.blocks) :
    (⟨b.off, b.instrs⟩ : CBlock ext8) ∈ F.toCert.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem checked_toCert {F : BlockCert8.Cert} (hc : F.checked = true) :
    F.toCert.checked = true := by
  simp only [Silmaril.X86.Cert.checked, toCert, List.all_map]
  exact hc

theorem vc_toCert {F : BlockCert8.Cert} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) : F.toCert.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  obtain ⟨m', hr, hn⟩ := hvc b0 hb0 s0 m ha hrip hl
  have hmem := (run8_open (List.all_eq_true.mp hc b0 hb0) hl hrip hr).2
  refine ⟨m', hr, ?_⟩
  rcases hn with hq | ⟨b', hb', hrip', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCert hb', hrip', by show Loaded m'.memory _ _; rw [hmem]; exact hl,
      ha', hlt⟩

/-- **`BlockCert8.Cert.total`, re-derived from the generic `Cert.total`.** -/
theorem total_generic {F : BlockCert8.Cert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Silmaril.X86.Cert.total (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc)
    (vc_toCert hc hvc) hpre

theorem totalIn {F : BlockCert8.Cert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.TotalIn Open.isa fun _ => InCode Open.isa F.base F.code.length :=
  Silmaril.X86.Cert.totalIn (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc)
    (Silmaril.X86.Cert.vcIn_of_vc _ (fun _ _ _ _ h => h) (vc_toCert hc hvc))
    (fun _ _ _ _ _ h => h) hpre

theorem strict {F : BlockCert8.Cert} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    (S.restrict (RetOutside Open.isa F.base F.code.length)).Strict Open.isa :=
  Silmaril.X86.Cert.strict_of_local (F := F.toCert) S (fun _ _ _ h => h)
    (fun _ _ _ _ h => h) (mem_toCert hentry) (checked_toCert hc) (vc_toCert hc hvc) hpre

end BlockCert8.Cert

/-! ## `BlockCert9.FunCert9` (on `Open9.isa`) -/

namespace BlockCert9.FunCert9

def toCert (F : FunCert9) : Cert Open9.isa ext9 :=
  ⟨F.code, F.base, F.blocks.map fun b => ⟨b.off, b.code⟩, F.ann, F.measure⟩

theorem mem_toCert {F : FunCert9} {b : Blk} (hb : b ∈ F.blocks) :
    (⟨b.off, b.code⟩ : CBlock ext9) ∈ F.toCert.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem checked_toCert {F : FunCert9} (hc : F.checked = true) : F.toCert.checked = true := by
  simp only [Cert.checked, toCert, List.all_map]
  exact hc

theorem vc_toCert {F : FunCert9} {Q : MState → MState → Prop} (hc : F.checked = true)
    (hvc : F.VC Q) : F.toCert.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
  obtain ⟨m', hr, hn⟩ := hvc b0 hb0 s0 m ha hrip hl
  have hmem := (Code.run_open9 (List.all_eq_true.mp hc b0 hb0) hl hrip hr).2
  refine ⟨m', hr, ?_⟩
  rcases hn with hq | ⟨b', hb', hrip', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCert hb', hrip', by show Loaded m'.memory _ _; rw [hmem]; exact hl,
      ha', hlt⟩

/-- **`FunCert9.total`, re-derived from the generic `Cert.total`.** -/
theorem total_generic {F : FunCert9} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open9.isa :=
  Cert.total (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc) (vc_toCert hc hvc) hpre

theorem totalIn {F : FunCert9} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.TotalIn Open9.isa fun _ => InCode Open9.isa F.base F.code.length :=
  Cert.totalIn (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc)
    (Cert.vcIn_of_vc _ (fun _ _ _ _ h => h) (vc_toCert hc hvc)) (fun _ _ _ _ _ h => h) hpre

/-- **First return for `Ext9` certificates** (none had a `TotalIn` theorem before). -/
theorem strict {F : FunCert9} (S : Spec MState) {entry : Blk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open9.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    (S.restrict (RetOutside Open9.isa F.base F.code.length)).Strict Open9.isa :=
  Cert.strict_of_local (F := F.toCert) S (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (mem_toCert hentry) (checked_toCert hc) (vc_toCert hc hvc) hpre

end BlockCert9.FunCert9

/-! ## `BlockCert.CallCert` -/

namespace BlockCert.CallCert

/-- A call-certificate block as a `calls` block. -/
def blockOf (b : CBlk) : CBlock calls :=
  match b.kind with
  | .plain L => ⟨b.off, .inl L⟩
  | .call rel C => ⟨b.off, .inr ([(.ext (.call rel), 5)], BlockKind.Callee.ofContract C)⟩

@[simp] theorem blockOf_off (b : CBlk) : (blockOf b).off = b.off := by
  unfold blockOf; split <;> rfl

/-- A certificate with contract calls as a generic certificate of `calls` blocks. -/
def toCert (F : CallCert) : Cert Open.isa calls :=
  ⟨F.code, F.base, F.blocks.map blockOf, F.ann, F.measure⟩

theorem mem_toCert {F : CallCert} {b : CBlk} (hb : b ∈ F.blocks) :
    blockOf b ∈ F.toCert.blocks :=
  List.mem_map.mpr ⟨b, hb, rfl⟩

theorem check_blockOf (code : List Byte) (b : CBlk) :
    calls.check code (blockOf b).off (blockOf b).blk = listingAtW code b.off b.kind.listing := by
  obtain ⟨off, k⟩ := b
  cases k <;> rfl

theorem checked_toCert {F : CallCert} (hc : F.checked = true) : F.toCert.checked = true := by
  simp only [Cert.checked, toCert, List.all_map, Function.comp_def, check_blockOf]
  exact hc

theorem next_toCert {F : CallCert} {Q : MState → MState → Prop} {m0 m' : MState} {μ : Nat}
    (h : F.NextC Q m0 μ m') : F.toCert.Next Q m0 μ m' := by
  rcases h with hq | ⟨b', hb', hrip', hl', ha', hlt⟩
  · exact .inl hq
  · exact .inr ⟨_, mem_toCert hb', by rw [blockOf_off]; exact hrip', hl',
      by rw [blockOf_off]; exact ha', by rw [blockOf_off]; exact hlt⟩

theorem vc_toCert {F : CallCert} {Q : MState → MState → Prop} (hvc : F.VC Q) :
    F.toCert.VC Q := by
  intro b hb s0 m ha _ hrip hl
  obtain ⟨⟨off, k⟩, hb0, rfl⟩ := List.mem_map.mp hb
  have hv := hvc _ hb0
  cases k with
  | plain L =>
    obtain ⟨m', hr, hn⟩ := hv s0 m ha hrip hl
    exact ⟨m', hr, next_toCert hn⟩
  | call rel C =>
    obtain ⟨⟨m1, hm1⟩, hpost⟩ := hv s0 m ha hrip hl
    obtain ⟨hab, he, hres⟩ := hpost m1 hm1
    exact ⟨m1, hm1, hab, he, fun _ _ => trivial, fun t ht => next_toCert (hres t ht)⟩

/-- **`CallCert.total`, re-derived from the generic `Cert.total`** (call blocks through the
generic `BlockKind.call`). -/
theorem total_generic {F : CallCert} (S : Spec MState) {entry : CBlk}
    (hentry : entry ∈ F.blocks) (hc : F.checked = true)
    (hvc : F.VC fun m0 t => S.Result Open.isa m0 t)
    (hpre : ∀ m, AbiEntry m.core m.memory → S.entry m →
      Loaded m.memory F.base F.code ∧ m.core.rip = F.base + BitVec.ofNat 64 entry.off ∧
        F.ann entry.off m m) :
    S.Total Open.isa :=
  Cert.total (F := F.toCert) S (mem_toCert hentry) (checked_toCert hc) (vc_toCert hvc)
    (fun m hab he => by rw [blockOf_off]; exact hpre m hab he)

end BlockCert.CallCert

end Silmaril.X86
