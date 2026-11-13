module

public import Silmaril.Wasi.Versions.P2OverP3.Os.Defs
public import Silmaril.Wasi.Versions.P2OverP3.Sep.Thms
public import Silmaril.Wasi.Versions.P3.Thms

@[expose] public section

/-!
# WASI 0.2 over 0.3: the OS image of a run (header)

PROVED:

* `helloPlay_mem`: `helloPlay` is a play of `p2OverP3 4096`; `helloPlay_hostView` lists its
  WASI 0.3 answers, which follow the concrete stdout host `stdout3Impl` (`helloPlay_follows`)
  and are accepted by `p3Th` (`helloPlay_p3`).
* **`helloPlay_os3`**: the WASI 0.3 OS image (`osTrace3`) of the run is the write of `hi`;
  **`helloPlay_os2`**: so is the WASI 0.2 OS image (the base WASI theory's `osTrace`) of the composite's answers,
  read as a WASI 0.2 host. The two observations agree (`helloPlay_os_eq`).
* **`helloPlayImg_psafe8`**: through `Silmaril.Machine.Process.IoSpec`, the 42-byte x86 runtime of
  `Silmaril.Wasi.Runtime` is LPS process-safe for this OS image (as for WASI 0.2's `hello` and
  WASI 0.3's `hello3`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Os (hiOut osTrace follows_snoc follows_nil)

/-- **`helloPlay` is a play of the component.** -/
theorem helloPlay_mem : helloPlay ∈ p2OverP3 4096 := by
  have hs : (session (body 4096) St.init helloCalls).isSome = true := by decide +kernel
  obtain ⟨⟨ms, s'⟩, hms⟩ := Option.isSome_iff_exists.1 hs
  have hp : helloPlay = ms := by simp [helloPlay, hms]
  rw [hp]
  exact session_mem hms

/-- The WASI 0.3 answers of `helloPlay`. -/
theorem helloPlay_hostView : hostView (wtrace helloPlay) =
    [.imp cStreamNew [] (some [natV 1, natV 2]), .imp stdoutWrite3 [natV 1] (some [natV 3]),
     .imp cStreamWrite [natV 2, bytesV Silmaril.Wasi.Examples.hiBytes]
       (some [natV (packCopy .completed 2)])] := by
  rfl

/-- **They follow the concrete stdout host.** -/
theorem helloPlay_follows : Follows stdout3Impl (hostView (wtrace helloPlay)) := by
  rw [helloPlay_hostView]
  have h1 := follows_snoc (follows_nil stdout3Impl) (f := cStreamNew) (a := [])
    (r := some [natV 1, natV 2]) rfl
  have h2 := follows_snoc h1 (f := stdoutWrite3) (a := [natV 1]) (r := some [natV 3]) rfl
  exact follows_snoc h2 (f := cStreamWrite) (a := [natV 2, bytesV Silmaril.Wasi.Examples.hiBytes])
    (r := some [natV (packCopy .completed 2)]) rfl

/-- They are accepted by the WASI 0.3 theory. -/
theorem helloPlay_p3 : p3Th.Accepts (hostView (wtrace helloPlay)) :=
  (Protocol.acceptsB_iff _ _).1 (by decide +kernel)

/-- **The WASI 0.3 OS image of the run is the write of `hi`.** -/
theorem helloPlay_os3 (ch : Silmaril.Process.LPS.Word) :
    osTrace3 ch (wtrace helloPlay) = hiOut ch := by
  rfl

/-- **The WASI 0.2 OS image of the composite's answers is the write of `hi`.** -/
theorem helloPlay_os2 (ch : Silmaril.Process.LPS.Word) :
    osTrace ch (retAsImp (wtrace helloPlay)) = hiOut ch := by
  rfl

/-- The two observations agree. -/
theorem helloPlay_os_eq (ch : Silmaril.Process.LPS.Word) :
    osTrace3 ch (wtrace helloPlay) = osTrace ch (retAsImp (wtrace helloPlay)) := by
  rw [helloPlay_os3, helloPlay_os2]

open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Machine.Process.LpsBridge
  Silmaril.Machine.Process.IoSpec in
/-- **The x86 runtime of `hello` also runs WASI 0.2 over 0.3's `hello`**, through `IoSpec`. -/
theorem helloPlayImg_psafe8 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {ch : Word} {cfg : Config (machine oracle)} (al : Aligned cfg Silmaril.Wasi.Runtime.helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused
      (fun tr => tr <+: osTrace3 ch (wtrace helloPlay) ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [helloPlay_os3, ← hello3Run_os]
  exact hello3Img_psafe8 al hfd hch

end Silmaril.Wasi.Versions.P2OverP3
