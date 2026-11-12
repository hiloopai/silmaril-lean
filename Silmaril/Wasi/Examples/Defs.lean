module

public import Silmaril.Wasi.Comp.Defs
public import Silmaril.Wasi.Theory.Defs

@[expose] public section

/-!
# Example WASI components

Three components, given by their bodies (`Silmaril.Wasi.Comp`), whose imports are uninterpreted:

* `checker` (world `clocksWorld`): the export `check` reads the monotonic clock twice and
  returns whether the second instant is not smaller than the first. Under the clock theory it
  always returns `true` (`Silmaril.Wasi.Examples.Thms`).
* `hello` (world `stdoutWorld`): `run` gets stdout, writes `hi`, drops the stream and returns
  `ok`; if `get-stdout` answers something else than a handle, it returns `error`.
* `writeFile` (world `fsWorld`): `run` gets the preopened directories, opens `out.txt` in the
  first one, writes `hi` at offset `0`, drops the file descriptor and returns `ok`; it returns
  `error` when an answer does not have the expected shape.

They are written directly as programs over the imports (the shape of a component after
lifting), not compiled from Wasm modules.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Examples

open Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-! ## The clock checker -/

/-- The clock world's import `now`. -/
def nowOp : (nsig clocksWorld.imports).Op := (⟨clockNow, rfl⟩, [])

/-- Is the second instant not smaller than the first? -/
def le2 : Option (List Val) → Option (List Val) → Bool
  | some [.u64 x], some [.u64 y] => decide (x ≤ y)
  | _, _ => false

/-- After both instants. -/
def checkK2 (a : Option (List Val)) : Option (List Val) → BProg clocksWorld.imports :=
  fun b => .pure (some [.bool (le2 a b)])

/-- After the first instant. -/
def checkK1 : Option (List Val) → BProg clocksWorld.imports := fun a => .call nowOp (checkK2 a)

/-- The program of `check`. -/
def checkProg : BProg clocksWorld.imports := .call nowOp checkK1

/-- **The clock checker.** -/
def checker : Body clocksWorld.imports clocksWorld.exports := fun _ => checkProg

/-! ## Hello on stdout -/

/-- The bytes of `hi`. -/
def hiBytes : List (BitVec 8) := [0x68, 0x69]

/-- `get-stdout()`. -/
def getOp : (nsig stdoutWorld.imports).Op := (⟨getStdout, Or.inl rfl⟩, [])

/-- `blocking-write-and-flush(hd, "hi")`. -/
def writeOp (hd : BitVec 32) : (nsig stdoutWorld.imports).Op :=
  (⟨streamWrite, Or.inr (Or.inl rfl)⟩, [.u32 hd, bytesV hiBytes])

/-- `[resource-drop]output-stream(hd)`. -/
def dropOp (hd : BitVec 32) : (nsig stdoutWorld.imports).Op :=
  (⟨streamDrop, Or.inr (Or.inr rfl)⟩, [.u32 hd])

/-- After the drop. -/
def helloK3 : Option (List Val) → BProg stdoutWorld.imports := fun _ => .pure (some [okV none])

/-- After the write. -/
def helloK2 (hd : BitVec 32) : Option (List Val) → BProg stdoutWorld.imports :=
  fun _ => .call (dropOp hd) helloK3

/-- After `get-stdout`. -/
def helloK1 : Option (List Val) → BProg stdoutWorld.imports
  | some [.u32 hd] => .call (writeOp hd) (helloK2 hd)
  | _ => .pure (some [errV none])

/-- The program of `run`. -/
def helloProg : BProg stdoutWorld.imports := .call getOp helloK1

/-- **Hello on stdout.** -/
def hello : Body stdoutWorld.imports stdoutWorld.exports := fun _ => helloProg

/-! ## Writing a file -/

/-- `get-directories()`. -/
def dirsOp : (nsig fsWorld.imports).Op := (⟨getDirs, Or.inl rfl⟩, [])

/-- `open-at(d, "out.txt")`. -/
def openOp (d : BitVec 32) : (nsig fsWorld.imports).Op :=
  (⟨openAt, Or.inr (Or.inl rfl)⟩, [.u32 d, strV "out.txt"])

/-- `write(f, "hi", 0)`. -/
def fwriteOp (f : BitVec 32) : (nsig fsWorld.imports).Op :=
  (⟨fdWrite, Or.inr (Or.inr (Or.inl rfl))⟩, [.u32 f, bytesV hiBytes, .u64 0])

/-- `[resource-drop]descriptor(f)`. -/
def fdropOp (f : BitVec 32) : (nsig fsWorld.imports).Op :=
  (⟨fdDrop, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩, [.u32 f])

/-- After the drop. -/
def wfK4 : Option (List Val) → BProg fsWorld.imports := fun _ => .pure (some [okV none])

/-- After the write. -/
def wfK3 (f : BitVec 32) : Option (List Val) → BProg fsWorld.imports :=
  fun _ => .call (fdropOp f) wfK4

/-- After `open-at`. -/
def wfK2 : Option (List Val) → BProg fsWorld.imports
  | some [.variant 0 (some (.u32 f))] => .call (fwriteOp f) (wfK3 f)
  | _ => .pure (some [errV none])

/-- After `get-directories`. -/
def wfK1 : Option (List Val) → BProg fsWorld.imports
  | some [.record (.record [.u32 d, _] :: _)] => .call (openOp d) wfK2
  | _ => .pure (some [errV none])

/-- The program of `run`. -/
def wfProg : BProg fsWorld.imports := .call dirsOp wfK1

/-- **Writing a file.** -/
def writeFile : Body fsWorld.imports fsWorld.exports := fun _ => wfProg

end Silmaril.Wasi.Examples
