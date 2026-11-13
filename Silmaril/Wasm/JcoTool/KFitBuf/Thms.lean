module

public import Silmaril.Wasm.JcoTool.KFitBuf.Defs
public import Silmaril.Wasm.JcoTool.KFit.Thms
public import Silmaril.Proofs.Wasm.JcoTool.KFitBuf.Rechunk
public import Silmaril.Proofs.Wasm.JcoTool.KFitBuf.Lines

/-!
# Buffered kernels: `kRechunk` fits, `kLines` cannot, `kLinesS` replaces it

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KFitBuf.{Rechunk,Lines}`.

* **`rechunk_fits`**: `KFits (kRechunk n) N` for `1 ≤ n ≤ 255`, `N ≤ 256`. So
  `rechunk_notrap` (the `KRead` pipe module never traps), `rechunk_reads` (it reads as its
  transformer) and every liveness theorem of `KLive` hold for `kRechunk n` with no hypothesis.
* **`lines_not_fits`** (a refutation): `KFits (kLines nl) N` is false for every `N ≥ 1`: a line of
  `CAP` bytes fills the module's buffer and the next byte traps it, by design.
* **`linesS_run`**: `kLinesS nl`, the unbuffered lines kernel, has the same run as `kLines nl` on
  every byte stream; it is small (`linesS_small`), so `linesS_fits`, `linesS_notrap`,
  `linesS_reads` hold with no hypothesis, and a chain or tee of generated modules computes
  `(kLines nl).tr.run` on every input, with no bound on line length.
* **`toolKernel_fits`**: every kernel the tools generate (`KFitBuf.toolKernel`: `KCore.kernelByName`
  with `lines` as `kLinesS 10`) fits at every read size up to `256`; `toolKernel_run`: it computes
  what `kernelByName`'s kernel computes. `kernelByName_fits`: of `kernelByName`'s kernels, all but
  `kLines 10` fit.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KFitBuf

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Kernel (KM kRechunk kLines Bytes)
open Silmaril.Wasm.JcoTool.KCore (trV byteOf)
open Silmaril.Wasm.JcoTool.KLive (KFits)

/-- **`kRechunk n` fits.** -/
theorem rechunk_fits (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) {N : Nat} (hN : N ≤ 256) :
    KFits (kRechunk n) N :=
  Silmaril.Proofs.Wasm.JcoTool.KFitBuf.rechunk_fits n h1 h2 hN

theorem rechunk_flushNil (n : Nat) : Silmaril.Wasm.JcoTool.KRead.FlushNil (kRechunk n) :=
  fun _ h => by cases h

/-- The pipe module of `kRechunk n` never traps. -/
theorem rechunk_notrap (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) {N : Nat} (hN : 0 < N ∧ N ≤ 256) :
    Silmaril.Wasm.JcoTool.KRead.NoTrapAt (kRechunk n) N :=
  KLive.genD_notrap_fits hN (rechunk_fits n h1 h2 hN.2)

/-- The pipe module of `kRechunk n` reads as its transformer. -/
theorem rechunk_reads (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) {N : Nat} (hN : 0 < N ∧ N ≤ 256) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs (kRechunk n) N).Reads (trV (kRechunk n)) :=
  KLive.genD_reads_fits hN (rechunk_fits n h1 h2 hN.2) (rechunk_flushNil n)

/-- **Refutation: `kLines nl` does not fit**, for any read size. -/
theorem lines_not_fits (nl : Nat) (hnl : nl < 256) {N : Nat} (hN : 0 < N) : ¬ KFits (kLines nl) N :=
  Silmaril.Proofs.Wasm.JcoTool.KFitBuf.lines_not_fits nl hnl hN

theorem linesS_small (nl : Nat) : KFit.Small (kLinesS nl) = true := rfl

/-- **The unbuffered lines kernel has the runs of `kLines`.** -/
theorem linesS_run (nl : Nat) (hnl : nl < 256) (bs : List Nat) (hb : Bytes bs) :
    (kLinesS nl).tr.run bs = (kLines nl).tr.run bs :=
  Silmaril.Proofs.Wasm.JcoTool.KFitBuf.linesS_run nl hnl bs hb

theorem linesS_fits (nl : Nat) {N : Nat} (hN : N ≤ 256) : KFits (kLinesS nl) N :=
  KFit.small_fits (linesS_small nl) hN

theorem linesS_flushNil (nl : Nat) : Silmaril.Wasm.JcoTool.KRead.FlushNil (kLinesS nl) :=
  fun _ h => by cases h

theorem linesS_notrap (nl : Nat) {N : Nat} (hN : 0 < N ∧ N ≤ 256) :
    Silmaril.Wasm.JcoTool.KRead.NoTrapAt (kLinesS nl) N :=
  KFit.small_notrap (linesS_small nl) hN

theorem linesS_reads (nl : Nat) {N : Nat} (hN : 0 < N ∧ N ≤ 256) :
    (Silmaril.Wasm.JcoTool.KRead.dropObs (kLinesS nl) N).Reads (trV (kLinesS nl)) :=
  KFit.small_reads (linesS_small nl) hN (linesS_flushNil nl)

theorem byteOf_lt (v : Val) : byteOf v < 256 := by
  cases v
  case u8 x => exact x.isLt
  all_goals exact (by decide : (0 : Nat) < 256)

/-- `trV` of the two lines kernels: the same runs on every stream of values. -/
theorem linesS_trV_run (nl : Nat) (hnl : nl < 256) (xs : List Val) :
    (trV (kLinesS nl)).run xs = (trV (kLines nl)).run xs := by
  have hb : Bytes (xs.map byteOf) := fun b hb => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
    exact byteOf_lt v
  rw [KCore.run_trV, KCore.run_trV, linesS_run nl hnl _ hb]

end Silmaril.Wasm.JcoTool.KFitBuf

namespace Silmaril.Wasm.JcoTool.KFitBuf

open Silmaril.Wasm.Component.Streams.Kernel (KM kRechunk kLines kInc kNoDigit kTake)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KLive (KFits)

/-- **Every kernel the tools generate fits, except `lines`**: `wasm-jco kcore`, `wasm-kdrop`,
`wasm-kappa` and `wasm-wac-kbytes` take their kernels from `KCore.kernelByName`; all of them but
`kLines 10` satisfy `KFits` at every read size up to `256`, so the no-trap and liveness theorems
hold for them with no hypothesis. -/
theorem kernelByName_fits {s : String} {k : KM} (h : Silmaril.Wasm.JcoTool.KCore.kernelByName s = some k) :
    k = kLines 10 ∨ ∀ N, N ≤ 256 → KFits k N := by
  unfold Silmaril.Wasm.JcoTool.KCore.kernelByName at h
  split_ifs at h with h1 h2 h3 h4 h5
  · cases h; exact .inr fun N hN => KFit.small_fits KFit.kInc_small hN
  · cases h; exact .inr fun N hN => KFit.small_fits KFit.kNoDigit_small hN
  · cases h; exact .inl rfl
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr fun N hN => KFit.small_fits (KFit.kTake_small n) hN
  · obtain ⟨n, -, hn⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at hn with hr
    cases hn
    exact .inr fun N hN => rechunk_fits n hr.1 hr.2 hN

/-- **Every kernel of the tools fits**, at every read size up to `256`: so every no-trap and
liveness theorem of `KLive`/`KRead` holds for the modules the tools generate, with no hypothesis. -/
theorem toolKernel_fits {s : String} {k : KM} (h : toolKernel s = some k) {N : Nat} (hN : N ≤ 256) :
    KFits k N := by
  unfold toolKernel at h
  split_ifs at h with hl
  · cases h; exact linesS_fits 10 hN
  · unfold Silmaril.Wasm.JcoTool.KCore.kernelByName at h
    split_ifs at h with h1 h2 h3 h4
    · cases h; exact KFit.small_fits KFit.kInc_small hN
    · cases h; exact KFit.small_fits KFit.kNoDigit_small hN
    · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact KFit.small_fits (KFit.kTake_small n) hN
    · obtain ⟨n, -, hn⟩ := Option.bind_eq_some_iff.mp h
      split_ifs at hn with hr
      cases hn
      exact rechunk_fits n hr.1 hr.2 hN

/-- The tools' kernels compute what `KCore.kernelByName`'s do, on every stream. -/
theorem toolKernel_run {s : String} {k : KM} (h : toolKernel s = some k) :
    ∃ k', Silmaril.Wasm.JcoTool.KCore.kernelByName s = some k' ∧ ∀ xs, (trV k).run xs = (trV k').run xs := by
  unfold toolKernel at h
  split_ifs at h with hl
  · cases h
    simp only [beq_iff_eq] at hl
    subst hl
    exact ⟨kLines 10, rfl, linesS_trV_run 10 (by decide)⟩
  · exact ⟨k, h, fun _ => rfl⟩

end Silmaril.Wasm.JcoTool.KFitBuf
