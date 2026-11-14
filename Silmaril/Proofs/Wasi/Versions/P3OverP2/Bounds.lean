module

public import Silmaril.Wasi.Versions.P3OverP2.Bounds.Defs
public import Silmaril.Wasi.Versions.P3.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# Proofs: the bounds of `host3_fsReadTh3w` are needed

`host3_fsReadTh3w` assumes runs of fewer than `2^31` answers and files shorter than `2^28`
bytes. `wrapRun` (`2^31 + 2` answers, one-byte files) and `bigRun` (two answers, files of
`2^28` bytes) are runs of `host3` that `fsReadTh3w` rejects.

The runs are long, so no proof here evaluates them: the `2^31 - 1` fillers are handled by
induction (`follows_fill`, `deliveredOn_fill`, `run_fill`) and the `2^28` bytes by the lemmas of
`List.replicate`; the answers that do get evaluated are stated for every file contents `F`
(`remaining_ev0`, `run_ev0`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Os (follows_snoc follows_nil)

/-! ## The fillers -/

/-- `host3` answers a filler with `[]`. -/
theorem host3_fill (F : BitVec 32 → List (BitVec 8)) (p : List WEv) :
    some [] = host3 F p cStreamDropR [] := by
  simp [host3, cStreamDropR, readVia3, cStreamRead, now3, waitFor3, canon]

/-- Fillers follow `host3`. -/
theorem follows_fill (F : BitVec 32 → List (BitVec 8)) {p : List WEv}
    (hp : Follows (host3 F) p) : ∀ n, Follows (host3 F) (p ++ List.replicate n fillEv)
  | 0 => by simpa using hp
  | n + 1 => by
    rw [List.replicate_succ', ← List.append_assoc]
    exact follows_snoc (follows_fill F hp n) (host3_fill F _)

/-- Fillers deliver nothing. -/
theorem deliveredOn_fill (r : Nat) (t : List WEv) :
    ∀ n, deliveredOn r (List.replicate n fillEv ++ t) = deliveredOn r t
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact deliveredOn_fill r t n

/-- `fsReadTh3w` accepts fillers and keeps its state. -/
theorem run_fill (F : BitVec 32 → List (BitVec 8)) (q : RdSt) :
    ∀ n, (fsReadTh3w F).run q (List.replicate n fillEv) = some q
  | 0 => rfl
  | n + 1 => by
    have hstep : (fsReadTh3w F).step q fillEv = some q := by
      simp [fsReadTh3w, fillEv, rdShaped, rdStepZ, cStreamDropR, readVia3, cStreamRead, canon]
    rw [List.replicate_succ, Protocol.run_cons, hstep, Option.bind_some]
    exact run_fill F q n

/-! ## The first `read-via-stream`, for every file contents -/

/-- The source of `1` after `wrapEv0` is the descriptor `0` at offset `0`. -/
theorem srcOf_ev0 (t : List WEv) : srcOf 1 (wrapEv0 :: t) = some (0, 0) := rfl

/-- `wrapEv0` delivers nothing. -/
theorem deliveredOn_ev0 (t : List WEv) : deliveredOn 1 (wrapEv0 :: t) = deliveredOn 1 t := rfl

/-- After `wrapEv0`, the readable end `1` has the whole file `0` to deliver. -/
theorem remaining_ev0 (F : BitVec 32 → List (BitVec 8)) : remaining F [wrapEv0] 1 = F 0 := rfl

/-- `fsReadTh3w F` after `wrapEv0`. -/
theorem run_ev0 (F : BitVec 32 → List (BitVec 8)) :
    (fsReadTh3w F).run [] [wrapEv0] = some [(1, F 0)] := rfl

/-- `wrapEv0` follows `host3`. -/
theorem follows_ev0 (F : BitVec 32 → List (BitVec 8)) : Follows (host3 F) [wrapEv0] :=
  follows_snoc (follows_nil _) rfl

/-! ## The wrap-around run -/

/-- The answers before the second `read-via-stream`: `2^31`. -/
theorem wrapPre_len : ([wrapEv0] ++ List.replicate (2 ^ 31 - 1) fillEv).length = 2 ^ 31 := by
  rw [List.length_append, List.length_replicate]
  rfl

/-- **`wrapRun` has `2^31 + 2` answers.** -/
theorem wrapRun_length : wrapRun.length = 2 ^ 31 + 2 := by
  rw [wrapRun, List.length_append, wrapPre, List.length_append, wrapPre_len]
  rfl

/-- The files of `wrapRun` are short. -/
theorem wrapFile_short (d : BitVec 32) : (wrapFile d).length < 2 ^ 28 := by
  unfold wrapFile
  split <;> simp

/-- `host3` still reads the first file on `1`. -/
theorem remaining_wrapPre : remaining wrapFile wrapPre 1 = [0] := by
  have hd : deliveredOn 1 wrapPre = 0 := by
    rw [wrapPre, List.append_assoc, List.singleton_append, deliveredOn_ev0, deliveredOn_fill]
    rfl
  have hsrc : srcOf 1 wrapPre = some (0, 0) := by
    rw [wrapPre, List.append_assoc, List.singleton_append, srcOf_ev0]
  unfold remaining
  rw [hsrc, hd]
  rfl

/-- `host3`'s answer to `stream.read(1, 1)` after `wrapPre`. -/
theorem host3_wrapRead : host3 wrapFile wrapPre cStreamRead [natV 1, natV 1] =
    some [natV (packCopy .completed 1), bytesV [0]] := by
  have hh : host3 wrapFile wrapPre cStreamRead [natV 1, natV 1] =
      some [natV (readCode wrapFile wrapPre [natV 1, natV 1]),
        bytesV (readItems wrapFile wrapPre [natV 1, natV 1])] := by
    simp only [host3, fsRead3Impl, or_true, ↓reduceIte, show ¬ cStreamRead = readVia3 by decide]
  have hr : remaining wrapFile wrapPre (readArgs [natV 1, natV 1]).1 = [0] := remaining_wrapPre
  have hn : (readArgs [natV 1, natV 1]).2 = 1 := rfl
  rw [hh, readCode, readItems, hr, hn]
  rfl

/-- **`wrapRun` follows `host3 wrapFile`.** -/
theorem wrapRun_follows : Follows (host3 wrapFile) wrapRun := by
  have h1 := follows_fill wrapFile (follows_ev0 wrapFile) (2 ^ 31 - 1)
  have h2 : Follows (host3 wrapFile) wrapPre := by
    refine follows_snoc h1 ?_
    have hh : host3 wrapFile ([wrapEv0] ++ List.replicate (2 ^ 31 - 1) fillEv) readVia3
        [.u32 1, .u64 0] = some [.record
          [natV (2 * ([wrapEv0] ++ List.replicate (2 ^ 31 - 1) fillEv).length + 1),
           natV (2 * ([wrapEv0] ++ List.replicate (2 ^ 31 - 1) fillEv).length + 2)]] := by
      simp only [host3, fsRead3Impl, true_or, ↓reduceIte]
    rw [hh, wrapPre_len]
  exact follows_snoc h2 host3_wrapRead.symm

/-- **`fsReadTh3w wrapFile` rejects `wrapRun`**: it expects the byte of the second file. -/
theorem wrapRun_rejected : ¬ (fsReadTh3w wrapFile).Accepts wrapRun := by
  have h : (fsReadTh3w wrapFile).run [] wrapRun = none := by
    rw [wrapRun, wrapPre, List.append_assoc, List.append_assoc, Protocol.run_append, run_ev0,
      Option.bind_some, Protocol.run_append, run_fill, Option.bind_some]
    rfl
  unfold Protocol.Accepts
  rw [show (fsReadTh3w wrapFile).init = [] from rfl, h]
  exact Bool.false_ne_true

/-! ## The packed-count run -/

/-- **`bigRun` follows `host3 bigFile`.** -/
theorem bigRun_follows : Follows (host3 bigFile) bigRun := by
  refine follows_snoc (follows_ev0 bigFile) ?_
  have hh : host3 bigFile [wrapEv0] cStreamRead [natV 1, natV (2 ^ 28)] =
      some [natV (readCode bigFile [wrapEv0] [natV 1, natV (2 ^ 28)]),
        bytesV (readItems bigFile [wrapEv0] [natV 1, natV (2 ^ 28)])] := by
    simp only [host3, fsRead3Impl, or_true, ↓reduceIte, show ¬ cStreamRead = readVia3 by decide]
  have hr : remaining bigFile [wrapEv0] (readArgs [natV 1, natV (2 ^ 28)]).1 =
      List.replicate (2 ^ 28) 0 := remaining_ev0 bigFile
  have hn : (readArgs [natV 1, natV (2 ^ 28)]).2 = 2 ^ 28 := rfl
  have hne : List.replicate (2 ^ 28) (0 : BitVec 8) ≠ [] := by
    rw [Ne, List.replicate_eq_nil_iff]
    decide
  rw [hh, readCode, readItems, hr, hn, List.take_replicate, Nat.min_self]
  simp only [hne, ↓reduceIte, List.length_replicate]

/-- `fsReadTh3w` rejects `COMPLETED 0` for a read of `n ≠ 0` items. -/
theorem zeroCopy_rejected (F : BitVec 32 → List (BitVec 8)) (bs : List (BitVec 8)) (items : Val)
    (n : Nat) (hn0 : n ≠ 0) (hn : n < 2 ^ 32) :
    (fsReadTh3w F).step [(1, bs)] (.imp cStreamRead [natV 1, natV n] (some [.u32 0, items])) =
      none := by
  have hnat : natOf (natV n) = some n := by
    simpa [natOf, natV] using hn
  have hne : ¬ cStreamRead = readVia3 := by decide
  have hsh : rdShaped (.imp cStreamRead [natV 1, natV n] (some [.u32 0, items])) = true := by
    simp [rdShaped, hne, hnat]
  have hc : (natOf (.u32 0) >>= copyOf) = some (some (.completed, 0)) := rfl
  have hr : (natOf (natV 1) >>= rest [(1, bs)]) = some bs := rfl
  change (if rdShaped (.imp cStreamRead [natV 1, natV n] (some [.u32 0, items])) then
    rdStepZ F [(1, bs)] (.imp cStreamRead [natV 1, natV n] (some [.u32 0, items]))
    else some [(1, bs)]) = none
  simp only [hsh, ↓reduceIte]
  simp only [rdStepZ, hne, ↓reduceIte, hr, hnat, hc]
  simp [hn0]

/-- **`fsReadTh3w bigFile` rejects `bigRun`**: the count `2^28` wraps to `COMPLETED 0`. -/
theorem bigRun_rejected : ¬ (fsReadTh3w bigFile).Accepts bigRun := by
  have h : (fsReadTh3w bigFile).run [] bigRun = none := by
    rw [bigRun, show [wrapEv0, bigEv1] = [wrapEv0] ++ [bigEv1] from rfl, Protocol.run_append,
      run_ev0, Option.bind_some]
    have hv : natV (packCopy .completed (2 ^ 28)) = .u32 0 := rfl
    rw [bigEv1, hv, Protocol.run_cons, zeroCopy_rejected _ _ _ _ (by decide) (by decide)]
    rfl
  unfold Protocol.Accepts
  rw [show (fsReadTh3w bigFile).init = [] from rfl, h]
  exact Bool.false_ne_true

/-! ## The bounds are needed -/

/-- **REFUTED without the length bound**: with files shorter than `2^28` bytes, a run of
`2^31 + 2` answers of `host3` is rejected by `fsReadTh3w`. -/
theorem host3_fsReadTh3w_needs_len :
    (∀ d, (wrapFile d).length < 2 ^ 28) ∧ Follows (host3 wrapFile) wrapRun ∧
      wrapRun.length = 2 ^ 31 + 2 ∧ ¬ (fsReadTh3w wrapFile).Accepts wrapRun :=
  ⟨wrapFile_short, wrapRun_follows, wrapRun_length, wrapRun_rejected⟩

/-- **REFUTED without the file bound**: with files of `2^28` bytes, a run of two answers of
`host3` is rejected by `fsReadTh3w`. -/
theorem host3_fsReadTh3w_needs_file :
    (∀ d, (bigFile d).length = 2 ^ 28) ∧ Follows (host3 bigFile) bigRun ∧
      bigRun.length < 2 ^ 31 ∧ ¬ (fsReadTh3w bigFile).Accepts bigRun :=
  ⟨fun _ => List.length_replicate, bigRun_follows, by decide, bigRun_rejected⟩

end Silmaril.Wasi.Versions.P3OverP2
