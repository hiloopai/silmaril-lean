module

public import Silmaril.Wasi.Versions.P2.Os.Defs
public import Silmaril.Wasi.Versions.P2.Host.Thms
public import Silmaril.Wasi.Os.Thms
public import Silmaril.Wasi.Runtime.Thms
public import Silmaril.Wasi.Runtime.Fs.Thms

@[expose] public section

/-!
# WASI 0.2 hosts over `IoSpec`: the base WASI theory's runs and runtimes, and `hello2`

* `osEv2_eq_osEv`, `osTrace2_eq_osTrace`: on events other than successful `write`,
  `write-zeroes` and `blocking-write-zeroes-and-flush` answers, the WASI 0.2 OS image is the base WASI theory's.
* **the base WASI theory's runs are runs against the WASI 0.2 host**: `helloRun_follows_p2`,
  `wfRun_follows_p2` (the answers of `hello`'s and `writeFile`'s runs follow `p2Impl`), with
  the same OS images (`helloRun_os2`). Hence the base WASI theory's x86 runtimes realize them:
  `helloImg_psafe8_p2` (the 42-byte `hello` program, LPS process-safe on the bridge's release
  machine for the OS image of `hello`'s run against the WASI 0.2 host) and
  `redirectImg_e2e_p2` (the 46-byte file runtime, `IoSafeN` for the `fsOs` image of
  `writeFile`'s run against the WASI 0.2 host).
* **`hello2`, through the non-blocking protocol**: `hello2Run_mem` (a play of `hello2`),
  `hello2Run_follows` (its answers follow `p2Impl`, so the strict WASI 0.2 theory holds of
  them: `hello2Run_strict`), `hello2Run_os` (its OS image is `hi`, the same as `hello`'s), and
  `hello2Img_psafe8`: the same x86 program is LPS process-safe for the OS image of `hello2`'s
  run.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Games
open Silmaril.Wasi
open Silmaril.Wasi.Os
open Silmaril.Wasi.Examples
open Silmaril.Wasm.Component (Val)

/-! ## The OS image extends the base WASI theory's -/

/-- **The WASI 0.2 OS image is the base WASI theory's** on events that are not successful `write`,
`write-zeroes` or `blocking-write-zeroes-and-flush` answers. -/
theorem osEv2_eq_osEv (ch : Word) {e : WEv}
    (he : ∀ f a, e = .imp f a (some [.variant 0 none]) → f ≠ osWrite ∧ f ≠ osWriteZeroes ∧ f ≠ osBwzf) :
    osEv2 ch e = osEv ch e := by
  unfold osEv2 osEv
  split
  · rename_i f a
    obtain ⟨h1, h2, h3⟩ := he f a rfl
    by_cases hw : f = streamWrite
    · subst hw
      cases a with
      | nil => simp [contentsOf]
      | cons x a => cases a <;> simp [contentsOf]
    · cases a with
      | nil => simp [h1, h2, h3, hw]
      | cons x a => cases a <;> simp [h1, h2, h3, hw]
  · rename_i hn
    split
    · rename_i f x buf rest
      exact absurd rfl (hn f (x :: buf :: rest))
    · rfl

/-- **The WASI 0.2 OS image of a trace is the base WASI theory's**, when the trace has no successful `write`,
`write-zeroes` or `blocking-write-zeroes-and-flush` answer. -/
theorem osTrace2_eq_osTrace (ch : Word) {t : List WEv}
    (ht : ∀ e ∈ t, ∀ f a, e = .imp f a (some [.variant 0 none]) →
      f ≠ osWrite ∧ f ≠ osWriteZeroes ∧ f ≠ osBwzf) :
    osTrace2 ch t = osTrace ch t := by
  unfold osTrace2 osTrace
  exact List.flatMap_congr fun e he => osEv2_eq_osEv ch (ht e he)

/-! ## the base WASI theory's runs against the WASI 0.2 host -/

/-- **The answers of `hello`'s run follow the WASI 0.2 host.** -/
theorem helloRun_follows_p2 : Follows p2Impl (hostView (wtrace helloRun)) := by
  have h1 := follows_snoc (follows_nil p2Impl) (f := getStdout) (a := []) (r := some [.u32 0]) rfl
  have h2 := follows_snoc h1 (f := streamWrite) (a := [.u32 0, bytesV hiBytes])
    (r := some [okV none]) rfl
  exact follows_snoc h2 (f := streamDrop) (a := [.u32 0]) (r := some []) rfl

/-- The answers of `hello`'s run satisfy the strict WASI 0.2 theory. -/
theorem helloRun_strict : (p2Th .strict).Accepts (hostView (wtrace helloRun)) :=
  p2Impl_accepts helloRun_follows_p2

/-- **The WASI 0.2 OS image of `hello`'s run is `hi`**, as the base WASI theory's. -/
theorem helloRun_os2 (ch : Word) : osTrace2 ch (wtrace helloRun) = hiOut ch := by
  rw [← helloRun_os ch]
  rfl

/-- **the base WASI theory's x86 `hello` program realizes `hello`'s run against the WASI 0.2 host**: LPS
process-safe on the bridge's release machine for a prefix of its WASI 0.2 OS image, then
`exit 0`. -/
theorem helloImg_psafe8_p2 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {ch : Word} {cfg : Config (machine oracle)} (al : Aligned cfg Silmaril.Wasi.Runtime.helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused
      (fun tr => tr <+: osTrace2 ch (wtrace helloRun) ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [helloRun_os2, ← helloRun_os ch]
  exact Silmaril.Wasi.Runtime.helloImg_psafe8 al hfd hch

/-- **The answers of `writeFile`'s run follow the WASI 0.2 host.** -/
theorem wfRun_follows_p2 : Follows p2Impl (hostView (wtrace wfRun)) := by
  have h1 := follows_snoc (follows_nil p2Impl) (f := getDirs) (a := []) (r := preopens) rfl
  have h2 := follows_snoc h1 (f := openAt) (a := [.u32 0, strV "out.txt"])
    (r := some [okV (some (.u32 2))]) rfl
  have h3 := follows_snoc h2 (f := fdWrite) (a := [.u32 2, bytesV hiBytes, .u64 0])
    (r := some [okV (some (.u64 2))]) rfl
  exact follows_snoc h3 (f := fdDrop) (a := [.u32 2]) (r := some []) rfl

/-- **the base WASI theory's x86 file runtime realizes `writeFile`'s run against the WASI 0.2 host**: `IoSafeN`
with the sound `fsEnv`, the exit's file system being the `fsOs` image of a run whose answers
follow `p2Impl` (`wfRun_follows_p2`). -/
theorem redirectImg_e2e_p2 {segs : List Segment} {e : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e.fds Silmaril.Wasi.Runtime.Fs.outFd = some (.fileW outPath 0))
    (hfs : Fs.lookup e.fs outPath = some []) :
    Follows p2Impl (hostView (wtrace wfRun)) ∧
    ∀ n, IoSafeN Silmaril.Machine.X86.Open.step (fsEnv segs) (fun _ _ _ => False) n
      Silmaril.Wasi.Runtime.Fs.fsStart e
      (fun tr => tr = [] ∨ tr = [.exitEv 0 (fsOs e.fs (hostView (wtrace wfRun)))]) :=
  ⟨wfRun_follows_p2, Silmaril.Wasi.Runtime.Fs.redirectImg_e2e hfd hfs⟩

/-! ## `hello2` -/

/-- **`hello2Run` is a play of `hello2`.** -/
theorem hello2Run_mem : hello2Run ∈ ofBody hello2 := by
  have h1 := (Reach.nil (h := hello2)).snoc (CStep.ask runQ2)
  have h2 := h1.snoc (CStep.call runQ2 getOp2 h2Got)
  have h3 := h2.snoc (CStep.reply runQ2 getOp2 h2Got (some [.u32 0]))
  have h4 := h3.snoc (CStep.call (h := hello2) runQ2 (cwOp 0) (h2Write 0))
  have h5 := h4.snoc (CStep.reply runQ2 (cwOp 0) (h2Write 0) (some [okV (some (.u64 4096))]))
  have h6 := h5.snoc (CStep.call (h := hello2) runQ2 (wrOp 0) (h2Flush 0))
  have h7 := h6.snoc (CStep.reply runQ2 (wrOp 0) (h2Flush 0) (some [okV none]))
  have h8 := h7.snoc (CStep.call (h := hello2) runQ2 (bfOp 0) (h2Drop 0))
  have h9 := h8.snoc (CStep.reply runQ2 (bfOp 0) (h2Drop 0) (some [okV none]))
  have h10 := h9.snoc (CStep.call (h := hello2) runQ2 (dropOp2 0) h2Done)
  have h11 := h10.snoc (CStep.reply runQ2 (dropOp2 0) h2Done (some []))
  exact ⟨_, h11.snoc (CStep.ret (h := hello2) runQ2 (some [okV none]))⟩

/-- **The answers of `hello2Run` follow the WASI 0.2 host.** -/
theorem hello2Run_follows : Follows p2Impl (hostView (wtrace hello2Run)) := by
  have h1 := follows_snoc (follows_nil p2Impl) (f := getStdout) (a := []) (r := some [.u32 0]) rfl
  have h2 := follows_snoc h1 (f := osCheckWrite) (a := [.u32 0])
    (r := some [okV (some (.u64 4096))]) rfl
  have h3 := follows_snoc h2 (f := osWrite) (a := [.u32 0, bytesV hi2]) (r := some [okV none]) rfl
  have h4 := follows_snoc h3 (f := osBflush) (a := [.u32 0]) (r := some [okV none]) rfl
  exact follows_snoc h4 (f := streamDrop) (a := [.u32 0]) (r := some []) rfl

/-- The answers of `hello2Run` satisfy the strict WASI 0.2 theory. -/
theorem hello2Run_strict : (p2Th .strict).Accepts (hostView (wtrace hello2Run)) :=
  p2Impl_accepts hello2Run_follows

/-- **The OS image of `hello2Run` is `hi`**: the same as `hello`'s. -/
theorem hello2Run_os (ch : Word) : osTrace2 ch (wtrace hello2Run) = hiOut ch := by
  simp [osTrace2, wtrace, hello2Run, wev, osEv2, getOp2, cwOp, wrOp, bfOp, dropOp2, runQ2, okV,
    osWrite, osBflush, streamWrite, osWriteZeroes, osBwzf, ioStreams, contentsOf, bytesOf_bytesV,
    hiOut]

/-- **`hello2` and `hello` have the same OS image** (one through the non-blocking protocol, the
other through `blocking-write-and-flush`). -/
theorem hello2Run_os_eq (ch : Word) : osTrace2 ch (wtrace hello2Run) = osTrace ch (wtrace helloRun) := by
  rw [hello2Run_os, helloRun_os]

/-- **the base WASI theory's x86 `hello` program realizes `hello2`'s run against the WASI 0.2 host.** -/
theorem hello2Img_psafe8 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {ch : Word} {cfg : Config (machine oracle)} (al : Aligned cfg Silmaril.Wasi.Runtime.helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused
      (fun tr => tr <+: osTrace2 ch (wtrace hello2Run) ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [hello2Run_os_eq]
  exact Silmaril.Wasi.Runtime.helloImg_psafe8 al hfd hch

end Silmaril.Wasi.Versions.P2
