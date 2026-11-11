module

public import Silmaril.Cli.Footprint.Thms

/-!
# File footprints: examples

`echo 1 > x | echo 2 > y` as specs `writeTo xPath [49]` and `writeTo yPath [50]`: framed
(`framed_writeTo`), within their own paths, so separate (`separate_xy`).

* **`not_pipe_le_pipeSeq`**: the plain `pipe ≤ pipeSeq` is false even here: the pipe may log
  `y`'s write first (`yFirst`), and `pipeSeq` fixes the log to `x`'s write, then `y`'s.
* `pipe_xy_le`: up to the order of the log it holds (`pipe_le_pipeSeq`).
* **`pipe_xy_writesBoth`**: whatever the schedule, the pipe ends with both files written,
  proved on the sequential schedule only (`pipe_le_of_pipeSeq`, `writesBoth` being log-blind).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Examples.Footprint

open Silmaril.Cli Silmaril.Cli.Spec

/-- The file `x` in the current directory. -/
def xPath : FPath := ⟨".", ["x"]⟩

/-- The file `y` in the current directory. -/
def yPath : FPath := ⟨".", ["y"]⟩

/-- `echo … > p` as a spec: write `c` to `p`, logged. -/
def writeTo (p : FPath) (c : Bytes) : Spec := fun i o =>
  o = { fs := i.fs.set p (some c), log := [.write p (some c)] }

theorem framed_writeTo (p : FPath) (c : Bytes) : (writeTo p c).Framed := by
  rintro i o fs f rfl hf
  have hf' : some (fs.set p (some c)) = some f := hf
  rw [← Option.some.inj hf']
  rfl

theorem within_writeTo (p : FPath) (c : Bytes) : (writeTo p c).Within (· = p) := by
  rintro i o rfl e he
  rw [List.mem_singleton.1 he]
  rfl

theorem xPath_ne_yPath : xPath ≠ yPath := by decide

/-- **`x` and `y` are separate footprints.** -/
theorem separate_xy : (writeTo xPath [49]).Separate (writeTo yPath [50]) :=
  separate_of_within (within_writeTo _ _) (within_writeTo _ _)
    fun _ hx hy => xPath_ne_yPath (hx.symm.trans hy)

/-- The run of the pipe that writes `y` first. -/
def yFirst : Obs :=
  { fs := (Fs.empty.set yPath (some [50])).set xPath (some [49]),
    log := [.write yPath (some [50]), .write xPath (some [49])] }

theorem pipe_yFirst : pipe (writeTo xPath [49]) (writeTo yPath [50]) {} yFirst :=
  ⟨⟨_, _, Fs.empty, Fs.empty, rfl, rfl, rfl, .nil, rfl, rfl, rfl, .right (.left .nil), rfl⟩, rfl⟩

/-- `pipeSeq` logs `x`'s write first. -/
theorem not_pipeSeq_yFirst : ¬ pipeSeq (writeTo xPath [49]) (writeTo yPath [50]) {} yFirst := by
  rintro ⟨o₁, o₂, rfl, rfl, -, -, -, -, -, -, -, hl⟩
  exact absurd hl (by decide)

/-- **The plain `pipe ≤ pipeSeq` is false for separate footprints**: the order of the log. -/
theorem not_pipe_le_pipeSeq :
    ¬ pipe (writeTo xPath [49]) (writeTo yPath [50]) ≤
      pipeSeq (writeTo xPath [49]) (writeTo yPath [50]) :=
  fun h => not_pipeSeq_yFirst (h _ _ pipe_yFirst)

/-- Up to the order of the log, it holds. -/
theorem pipe_xy_le :
    pipe (writeTo xPath [49]) (writeTo yPath [50]) ≤
      relog (pipeSeq (writeTo xPath [49]) (writeTo yPath [50])) :=
  pipe_le_pipeSeq (framed_writeTo _ _) (framed_writeTo _ _) separate_xy

/-- Both files written, in any order of the log. -/
def writesBoth : Spec := fun i o => o.fs = (i.fs.set xPath (some [49])).set yPath (some [50])

/-- **Whatever the schedule, the pipe ends with both files written**: checked on the sequential
schedule only. -/
theorem pipe_xy_writesBoth : pipe (writeTo xPath [49]) (writeTo yPath [50]) ≤ writesBoth :=
  pipe_le_of_pipeSeq (framed_writeTo _ _) (framed_writeTo _ _) separate_xy
    (logBlind_of fun _ _ _ h => h) fun _ _ ⟨_, _, h₁, h₂, _, _, _, _, _, hf, _⟩ => by
      subst h₁ h₂
      exact hf

end Silmaril.Cli.Examples.Footprint
