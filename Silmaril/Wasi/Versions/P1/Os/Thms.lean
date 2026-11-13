module

public import Silmaril.Wasi.Versions.P1.Os.Defs
public import Silmaril.Wasi.Versions.P1.Theory.Thms
public import Silmaril.Wasi.Runtime.Thms

@[expose] public section

/-!
# Preview1 hosts over `IoSpec`: theorems

* `osEv_write`: the image of `fd_write(1, [bs])` answered `ok(|bs|)` is `bs` on `ch`, so an x86
  write loop (`Silmaril.Wasi.Runtime.WriteLoop`, `ioSafe_writeLoop`) refines that answer.
* `helloP1_th`: the answers of the preview1 `hello` satisfy the preview1 theory (they are
  answers of the loose preview1 host).
* `helloP1_os`, `helloP1_os_eq`: its OS image is `hi` on `ch`, the image of the 0.2 `hello` run
  `helloRun` of `Silmaril.Wasi.Os`.
* **`helloLoop_p1`**, **`helloImg_psafe8_p1`**: every x86 runtime of `hello`
  (`Silmaril.Wasi.Runtime.HelloLoop`), and the concrete 42-byte program on the bridge's release
  machine, are safe for "a prefix of the OS image of the preview1 `hello`, then `exit 0`".
-/

namespace Silmaril.Wasi.Versions.P1

open Silmaril.Wasi Silmaril.Wasi.Os Silmaril.Wasi.Runtime
open Silmaril.Wasm.Component (Val)
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec

/-- **One `fd_write(1, [bs])` answered `ok(|bs|)`** writes exactly `bs`. -/
theorem osEv_write (ch : Word) {bs : List (BitVec 8)} (hl : bs.length < 2 ^ 32) :
    osEv ch (.imp (fn "fd_write") [.u32 1, .record [bytesV bs]]
      (okAns (some (.u32 (BitVec.ofNat 32 bs.length))))) = bs.map (.writeEv ch) := by
  have hn : (BitVec.ofNat 32 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl
  simp [osEv, okAns, okV, iovBytes, bytesOf_bytesV, hn]

/-- The answers of the preview1 `hello` satisfy the preview1 theory. -/
theorem helloP1_th : th.Accepts helloP1 :=
  (Silmaril.Wasm.Resource.Protocol.acceptsB_iff th helloP1).1 (by decide)

/-- The OS image of the preview1 `hello` is `hi`. -/
theorem helloP1_os (ch : Word) : osTrace ch helloP1 = hiOut ch := by
  simp [osTrace, helloP1, osEv, okAns, okV, iovBytes, bytesOf_bytesV, hiOut,
    Silmaril.Wasi.Examples.hiBytes]

/-- **The OS images of the preview1 and 0.2 `hello` runs agree.** -/
theorem helloP1_os_eq (ch : Word) : osTrace ch helloP1 = Os.osTrace ch (wtrace helloRun) := by
  rw [helloP1_os, helloRun_os]

variable {c : Silmaril.X86.MState → Option Silmaril.X86.MState} {segs : List Segment} {ch : Word}
  {e : Silmaril.Process.LPS.Model}

/-- **Every x86 runtime of `hello` refines the preview1 `hello`.** -/
theorem helloLoop_p1 (R : HelloLoop c segs ch e) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.start e
      (fun tr => tr <+: osTrace ch helloP1 ++ [.exitEv 0 e.fs]) := by
  rw [helloP1_os]
  exact helloLoop_ioSafe R

/-- **The concrete 42-byte runtime** is LPS process-safe for the OS image of the preview1
`hello` on the bridge's release machine. -/
theorem helloImg_psafe8_p1 {oracle : Oracle} {refused : RefusalFilter}
    {cfg : Config (machine oracle)} (al : Aligned cfg helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused (fun tr => tr <+: osTrace ch helloP1 ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [helloP1_os_eq]
  exact helloImg_psafe8 al hfd hch

end Silmaril.Wasi.Versions.P1
