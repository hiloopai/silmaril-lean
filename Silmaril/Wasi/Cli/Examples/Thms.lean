module

public import Silmaril.Wasi.Cli.Examples.Defs
public import Silmaril.Wasi.Cli.Thms

/-!
# CLI views of the runs of the WASI example components: checks

* `helloRun_*`, `hello2Run_*` (WASI 0.2, `p2View`), `hello3Run_*` (WASI 0.3, `p3View`): each
  recorded run is seen as stdout `hi`, nothing on stderr, no stdin consumed, no file read or
  written, no refusal, exit `0`, finished (kernel evaluation); so it is a partial view of a run `hiSpec` allows
  (`helloRun_hi`, `hello2Run_hi`, `hello3Run_hi`) on every invocation.
* `teeRun_view`, `teeRun_theory`, **`teeRun_tee`**: a WASI 0.2 run that reads stdin and writes a
  file under a preopen is read as consuming `hi` and writing `/work/out.txt`; its host meets
  `cliTh2 teeIn`, and `teeSpec` allows it.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Examples

open Silmaril.Cli Silmaril.Wasi.Versions

/-- A view that sees exactly `hi`, exit `0`, and nothing else, sees a run `hiSpec` allows. -/
theorem hi_of {V : View} {t : List WEv} (i : Input) (ho : V.stdout t = hiOut)
    (he : V.stderr t = []) (hc : V.code t = some 0) (hi : V.stdin t = []) (hr : V.reads t = [])
    (hw : V.writes t = []) : hiSpec.Partial i (V.seen i t) := by
  refine View.partial_of ?_
  simp [hiSpec, Spec.pure, View.obs, ho, he, hc, hi, hr, hw, applyWrites]

theorem helloRun_hi (i : Input) : hiSpec.Partial i (p2View.seen i (wtrace Os.helloRun)) :=
  hi_of i (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hello2Run_hi (i : Input) : hiSpec.Partial i (p2View.seen i (wtrace P2.hello2Run)) :=
  hi_of i (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem hello3Run_hi (i : Input) : hiSpec.Partial i ((p3View).seen i (wtrace P3.hello3Run)) :=
  hi_of i (by decide) rfl (by decide) rfl rfl rfl

/-! ## stdin and files -/

/-- What `p2View` reads off `teeRun`: stdin delivered `hi`, one write of `hi` at offset `0` to
`/work/out.txt`, no file read, no refusal, exit `0`. -/
theorem teeRun_view : p2View.stdin teeRun = hiOut ∧ p2View.stdout teeRun = hiOut ∧
    p2View.stderr teeRun = [] ∧ p2View.reads teeRun = [] ∧
    p2View.writes teeRun = [(teeOut, 0, hiOut)] ∧ p2View.refused teeRun = false ∧
    p2View.code teeRun = some 0 := by
  decide +kernel

/-- **The host of `teeRun` satisfies the CLI theory of `teeIn`**: preopens, and stdin delivering
`teeIn.stdin` in order (no `get-arguments` or `get-environment` call to check). -/
theorem teeRun_theory : (cliTh2 teeIn).Accepts (hostView teeRun) := by
  unfold Silmaril.Wasm.Resource.Protocol.Accepts
  decide +kernel

/-- **`teeSpec` allows `teeRun` on `teeIn`.** -/
theorem teeRun_tee : teeSpec.Partial teeIn (p2View.seen teeIn teeRun) := by
  obtain ⟨hi, ho, he, hr, hw, -, hc⟩ := teeRun_view
  refine View.partial_of ?_
  have hfs : applyWrites teeIn.fs [(teeOut, 0, hiOut)] = teeIn.fs.set teeOut (some teeIn.stdin) := by
    funext q
    simp [applyWrites, Fs.set, Fs.empty, writeAt, teeIn]
  exact ⟨ho, he, by simp [View.obs, hc], by simp [View.obs, hi, teeIn], hr,
    by simp only [View.obs, hw]; exact hfs⟩

end Silmaril.Wasi.Cli.Examples

end
