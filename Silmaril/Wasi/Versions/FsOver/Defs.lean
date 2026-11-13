module

public import Silmaril.Wasi.Versions.FsMore.Defs
public import Silmaril.Wasi.Versions.FwdT.Defs

@[expose] public section

/-!
# Filesystem 0.3 over 0.2, with translated codes

A forwarder (`Silmaril.Wasi.Versions.FwdT`) from the 0.3 functions `get-directories`, `open-at`,
`stat`, `stat-at` and `get-type` to their 0.2 counterparts, translating what differs between
`specs/wasi/0.2.12/filesystem/types.wit` and `specs/wasi/0.3.2/filesystem/types.wit`:

* `descriptor-type`: the 0.2 enum `{unknown, block-device, character-device, directory, fifo,
  symbolic-link, regular-file, socket}` becomes the 0.3 variant without `unknown` and with
  `other(option<string>)`: case `k + 1` becomes case `k`, `unknown` becomes `other(none)`
  (`kind2to3`).
* `error-code`: 0.3 drops `would-block` (case 1) and adds `other(option<string>)` (case 36):
  `0` stays, `1` becomes `other(none)`, `k + 2` becomes `k + 1` (`fsE2to3`, `fsEcV3`).
* `descriptor-stat`: the timestamps are `option<datetime>` (seconds `u64`) in 0.2 and
  `option<instant>` (seconds `s64`) in 0.3; the seconds keep their bits (`tsTr`).

The answers the 0.2 theory `FsMore.fsTh2 T` constrains are translated so that the 0.3 theory
`fsTh3 T` accepts them (`FsOver.Thms.fs3Over2_model`); ill-shaped `stat` and `get-type` answers
become traps, other `open-at` answers are passed unchanged.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.FsOver

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (fwdT)
open Silmaril.Wasi.Versions.FsMore

/-- The 0.3 functions exported. -/
def fsX3 : Set FnName := {v3.getDirs, v3.openAt, v3.stat, v3.statAt, v3.getType}

/-- The 0.2 functions imported. -/
def fsI2 : Set FnName := {v2.getDirs, v2.openAt, v2.stat, v2.statAt, v2.getType}

/-- The 0.2 function of a 0.3 one. -/
def fsTo (f : FnName) : FnName :=
  if f = v3.getDirs then v2.getDirs
  else if f = v3.openAt then v2.openAt
  else if f = v3.stat then v2.stat
  else if f = v3.statAt then v2.statAt
  else v2.getType

theorem fsTo_mem : ∀ f ∈ fsX3, fsTo f ∈ fsI2 := by
  intro f hf
  simp only [fsX3, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> simp [fsTo, fsI2, FsVer.getDirs, FsVer.openAt,
    FsVer.stat, FsVer.statAt, FsVer.getType, v2, v3]

/-- 0.3 `error-code.other`. -/
abbrev fsOther3 : Nat := 36

/-- A 0.2 filesystem error code as a 0.3 one. -/
def fsE2to3 : Nat → Nat
  | 0 => 0
  | 1 => fsOther3
  | k + 2 => k + 1

/-- The value of a 0.3 filesystem `error-code` (`other` carries `none`). -/
def fsEcV3 (k : Nat) : Val :=
  if k = fsOther3 then .variant k (some (.variant 0 none)) else .variant k none

/-- A 0.2 `descriptor-type` case as a 0.3 `descriptor-type` value. -/
def kind2to3 : Nat → Val
  | 0 => .variant 7 (some (.variant 0 none))
  | k + 1 => .variant k none

/-- A 0.2 timestamp as a 0.3 one (`option<datetime>` to `option<instant>`). -/
def tsTr : Val → Val
  | .variant 1 (some (.record [.u64 s, .u32 ns])) => .variant 1 (some (.record [.s64 s, .u32 ns]))
  | v => v

/-- The 0.3 error answer of a 0.2 error code. -/
def errTr (k : Nat) : Option (List Val) := some [.variant 1 (some (fsEcV3 (fsE2to3 k)))]

/-- The translation of an `open-at` answer: an error code is translated, the rest passed. -/
def openTr : Option (List Val) → Option (List Val)
  | some [.variant 1 (some (.variant k none))] => errTr k
  | r => r

/-- The translation of a `stat`/`stat-at` answer. -/
def statTr : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.record (.variant k none :: lc :: .u64 sz :: ts)))] =>
    some [.variant 0 (some (.record (kind2to3 k :: lc :: .u64 sz :: ts.map tsTr)))]
  | some [.variant 1 (some (.variant k none))] => errTr k
  | _ => none

/-- The translation of a `get-type` answer. -/
def typeTr : Option (List Val) → Option (List Val)
  | some [.variant 0 (some (.variant k none))] => some [.variant 0 (some (kind2to3 k))]
  | some [.variant 1 (some (.variant k none))] => errTr k
  | _ => none

/-- The translation of the answer of `f`. -/
def fsTr (f : FnName) (r : Option (List Val)) : Option (List Val) :=
  if f = v3.getDirs then r
  else if f = v3.openAt then openTr r
  else if f = v3.stat ∨ f = v3.statAt then statTr r
  else typeTr r

/-- **Filesystem 0.3 over 0.2.** -/
def fs3Over2 := fwdT fsX3 fsI2 fsTo fsTo_mem fsTr

end Silmaril.Wasi.Versions.FsOver
