module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs
public import Silmaril.Wasi.Versions.P2.World.Thms

/-!
# Proofs: the fixed `wasi:cli`/`wasi:clocks` answers are well typed

`cliOk_dflt`: `cliDflt f` satisfies `cliOk f`. Split out of
`Silmaril.Proofs.Wasi.Versions.P2OverP3.Cli`: the earlier proof used `split_ifs`, whose
simplification of the eleven nested conditions took 8 s of the module's time; this one decides
each named function with `decide +kernel` and rewrites both `if` chains for the others.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P2

/-! ## Each named function -/

theorem dfltExit : cliOk cliExit (cliDflt cliExit) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltEnv : cliOk getEnv (cliDflt getEnv) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltArgs : cliOk getArgs (cliDflt getArgs) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltCwd : cliOk initialCwd (cliDflt initialCwd) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltStdin : cliOk getStdin (cliDflt getStdin) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltStdout : cliOk getStdout (cliDflt getStdout) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltStderr : cliOk getStderr (cliDflt getStderr) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltSubI : cliOk monoSubInstant (cliDflt monoSubInstant) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltSubD : cliOk monoSubDuration (cliDflt monoSubDuration) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltTIn : cliOk getTermStdin (cliDflt getTermStdin) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltTOut : cliOk getTermStdout (cliDflt getTermStdout) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltTErr : cliOk getTermStderr (cliDflt getTermStderr) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltRes : cliOk monoRes (cliDflt monoRes) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltWNow : cliOk wallNow (cliDflt wallNow) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltWRes : cliOk wallRes (cliDflt wallRes) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltRS : cliOk fdReadStream (cliDflt fdReadStream) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltWS : cliOk fdWriteStream (cliDflt fdWriteStream) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltAS : cliOk fdAppendStream (cliDflt fdAppendStream) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltGT : cliOk fdGetType (cliDflt fdGetType) = true := by
  rw [cliOk_eq_hand]; decide +kernel
theorem dfltDrop : cliOk streamDrop (cliDflt streamDrop) = true := by
  rw [cliOk_eq_hand]; decide +kernel

/-! ## The other functions -/

section
variable {f : FnName} (h1 : f ≠ cliExit) (h2 : f ≠ getEnv) (h3 : f ≠ getArgs)
  (h4 : f ≠ initialCwd)
  (h5 : ¬ (f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
    f = monoSubDuration))
  (h6 : ¬ (f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr)) (h7 : f ≠ monoRes)
  (h8 : ¬ (f = wallNow ∨ f = wallRes))
  (h9 : ¬ (f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream)) (h10 : f ≠ fdGetType)
  (h11 : f ≠ streamDrop)
include h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem cliDflt_else : cliDflt f = some [] := by
  unfold cliDflt
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
    ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10,
    ite_eq_right h11]

theorem cliOk_else : cliOk f (some []) = true := by
  rw [cliOk_eq_hand]
  unfold cliOkH
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5,
    ite_eq_right h6, ite_eq_right h7, ite_eq_right h8, ite_eq_right h9, ite_eq_right h10,
    ite_eq_right h11]

end

/-- **The fixed answer is well typed** (case split on the conditions of `cliDflt`). -/
theorem cliOk_dflt (f : FnName) : cliOk f (cliDflt f) = true :=
  if h1 : f = cliExit then h1 ▸ dfltExit else
  if h2 : f = getEnv then h2 ▸ dfltEnv else
  if h3 : f = getArgs then h3 ▸ dfltArgs else
  if h4 : f = initialCwd then h4 ▸ dfltCwd else
  if h5 : f = getStdin ∨ f = getStdout ∨ f = getStderr ∨ f = monoSubInstant ∨
      f = monoSubDuration then
    h5.elim (· ▸ dfltStdin) fun h => h.elim (· ▸ dfltStdout) fun h => h.elim (· ▸ dfltStderr)
      fun h => h.elim (· ▸ dfltSubI) (· ▸ dfltSubD) else
  if h6 : f = getTermStdin ∨ f = getTermStdout ∨ f = getTermStderr then
    h6.elim (· ▸ dfltTIn) fun h => h.elim (· ▸ dfltTOut) (· ▸ dfltTErr) else
  if h7 : f = monoRes then h7 ▸ dfltRes else
  if h8 : f = wallNow ∨ f = wallRes then h8.elim (· ▸ dfltWNow) (· ▸ dfltWRes) else
  if h9 : f = fdReadStream ∨ f = fdWriteStream ∨ f = fdAppendStream then
    h9.elim (· ▸ dfltRS) fun h => h.elim (· ▸ dfltWS) (· ▸ dfltAS) else
  if h10 : f = fdGetType then h10 ▸ dfltGT else
  if h11 : f = streamDrop then h11 ▸ dfltDrop else
  (cliDflt_else h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) ▸
    cliOk_else h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

end Silmaril.Wasi.Versions.P2OverP3
