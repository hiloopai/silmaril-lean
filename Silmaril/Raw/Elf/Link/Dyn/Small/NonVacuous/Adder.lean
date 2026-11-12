module

public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Basic
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderGccMain
public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Stdio

/-! # The adders: the hypotheses of `_sum` are satisfiable

For `adderClang` and `adderGcc`, a concrete process (`NonVacuous.Basic`) with `stdin` = `"2 3\n"`:

* `_nonvacuous`: it meets every hypothesis of `_sum` with `x = 2`, `y = 3` (`ChunksOf`,
  `ExeLoaded`, `AdderPlaced`/`AdderGccPlaced`, `AtEntry`, for gcc `TlsAt` with the guard at
  `fs0 + 0x28`, the `int` ranges, `stdin`, empty `stdout`);
* `_s0`: `_sum` for it, with reliable writes: every run ends with exit status `0` and
  `stdout` = `"5\n"`;
* `_run`: **an actual run** of it does so (`proc_progress`, with `stdioNamed_total`: the
  stdio contracts always allow an outcome).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Small.NonVacuous

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.DynElf.Elf
open Silmaril.Elf.Link.Dyn.Glibc
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Crt
open Silmaril.Elf.Link.Dyn.Stdio

/-- `libc.so.6` and `ld.so` holding the pinned chunks of the small executables. -/
def FcS : Blob := blobOf libcChunksS
def FlS : Blob := blobOf ldChunksS

theorem hFcS : ChunksOf FcS libcChunksS := by unfold ChunksOf; decide +kernel
theorem hFlS : ChunksOf FlS ldChunksS := by unfold ChunksOf; decide +kernel

theorem digitsOf_lt {n : Nat} (h : n < 10) {c : Char} (hc : n.digitChar = c) :
    digitsOf n = [BitVec.ofNat 8 c.toNat] := by
  simp [digitsOf, Nat.toDigits_of_lt_base h, hc]

/-- `stdin`: `"2 3\n"`. -/
def inp0 : List Byte := decStr 2 ++ [32#8] ++ decStr 3 ++ [10#8]

theorem inp0_text : inp0 = [0x32#8, 0x20#8, 0x33#8, 0x0a#8] := by
  rw [inp0, decStr_of_nonneg (by decide), decStr_of_nonneg (by decide),
    digitsOf_lt (n := Int.toNat 2) (by decide) (Nat.digitChar_eq_two.mpr rfl),
    digitsOf_lt (n := Int.toNat 3) (by decide) (Nat.digitChar_eq_three.mpr rfl)]
  decide

/-- `"5\n"`. -/
theorem out5 : decStr (2 + 3) ++ [10#8] = [0x35#8, 0x0a#8] := by
  rw [decStr_of_nonneg (by decide),
    digitsOf_lt (n := Int.toNat (2 + 3)) (by decide) (Nat.digitChar_eq_five.mpr rfl)]
  decide

/-! ## `adderClang` -/

def adderClangT : List (Nat × Option Word) := tableOf adderClangSlots
theorem adderClang_T : adderClangSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some adderClangT := by decide +kernel
theorem adderClang_tab : tableOk adderClangFile adderClangInfo adderClangT adderClangLayout.size = true := by decide +kernel
theorem adderClang_placed : AdderPlaced adderClangLayout b0 lb0 gate0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try constructor) <;> (try unfold Img) <;> decide +kernel

/-- The start state of `adderClang`, `stdin` = `"2 3\n"`. -/
def adderClangS0 : PState := sOf (memOf adderClangFile adderClangInfo adderClangT adderClangLayout.size) adderClangLayout.start inp0

theorem adderClang_loaded :
    ExeLoaded [adderClangFile, FcS, FlS] [b0, lb0, ldb0] ifn0 false res0 adderClangS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, adderClang_info, fun h => absurd h (by decide), adderClang_slots hFcS hFlS,
    adderClang_T, imageOk_of_table (by decide) adderClang_tab⟩

theorem adderClang_entry (rel : Bool) : AtEntry adderClangLayout (adderClangWorld b0 lb0 gate0 rel) b0 adderClangS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the concrete process meets every hypothesis of `adderClang_sum`. -/
theorem adderClang_nonvacuous (rel : Bool) :
    ChunksOf FcS libcChunksS ∧ ChunksOf FlS ldChunksS ∧
    ExeLoaded [adderClangFile, FcS, FlS] [b0, lb0, ldb0] ifn0 false res0 adderClangS0.m.memory ∧
    AdderPlaced adderClangLayout b0 lb0 gate0 ∧
    AtEntry adderClangLayout (adderClangWorld b0 lb0 gate0 rel) b0 adderClangS0 ∧
    inInt32 2 = true ∧ inInt32 3 = true ∧ inInt32 (2 + 3) = true ∧
    adderClangS0.g.inp = decStr 2 ++ [32#8] ++ decStr 3 ++ [10#8] ∧ adderClangS0.g.out = [] :=
  ⟨hFcS, hFlS, adderClang_loaded, adderClang_placed, adderClang_entry rel, by decide, by decide,
    by decide, rfl, rfl⟩

/-- **`adderClang` on `"2 3\n"`**: every run of the concrete process ends with exit status
`0` and `stdout` = `"5\n"` (with reliable writes). -/
theorem adderClang_s0 :
    MustQ (adderClangWorld b0 lb0 gate0 true)
      (fun u => u.g.done = some (0, [0x35#8, 0x0a#8])) adderClangS0 := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderClang_sum hFcS hFlS adderClang_loaded adderClang_placed (adderClang_entry true)
      (x := 2) (y := 3) (by decide) (by decide) (by decide) rfl rfl)
  rintro u ⟨w, hd, -, hw⟩
  rw [hd, hw rfl, out5]

/-! ## `adderGcc` -/

def adderGccT : List (Nat × Option Word) := tableOf adderGccSlots
theorem adderGcc_T : adderGccSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some adderGccT := by decide +kernel
theorem adderGcc_tab : tableOk adderGccFile adderGccInfo adderGccT adderGccLayout.size = true := by decide +kernel
theorem adderGcc_placed : AdderGccPlaced b0 lb0 gate0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try constructor) <;> (try unfold Img) <;> decide +kernel

/-- The start state of `adderGcc`, `stdin` = `"2 3\n"`. -/
def adderGccS0 : PState := sOf (memOf adderGccFile adderGccInfo adderGccT adderGccLayout.size) adderGccLayout.start inp0

theorem adderGcc_loaded :
    ExeLoaded [adderGccFile, FcS, FlS] [b0, lb0, ldb0] ifn0 false res0 adderGccS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, adderGcc_info, fun h => absurd h (by decide), adderGcc_slots hFcS hFlS,
    adderGcc_T, imageOk_of_table (by decide) adderGcc_tab⟩

theorem adderGcc_entry (rel : Bool) : AtEntry adderGccLayout (adderGccWorld b0 lb0 gate0 fs0 rel) b0 adderGccS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun a h => by left; simp only [Guard] at h; rw [fs0_toNat] at h; rw [sp0_toNat]; omega))

theorem adderGcc_tls : TlsAt fs0 adderGccS0 :=
  ⟨rfl, by rw [fs0_toNat]; decide, ⟨0#64, guard0 (by decide)⟩⟩

/-- **Non-vacuity**: the concrete process meets every hypothesis of `adderGcc_sum`. -/
theorem adderGcc_nonvacuous (rel : Bool) :
    ChunksOf FcS libcChunksS ∧ ChunksOf FlS ldChunksS ∧
    ExeLoaded [adderGccFile, FcS, FlS] [b0, lb0, ldb0] ifn0 false res0 adderGccS0.m.memory ∧
    AdderGccPlaced b0 lb0 gate0 ∧
    AtEntry adderGccLayout (adderGccWorld b0 lb0 gate0 fs0 rel) b0 adderGccS0 ∧
    TlsAt fs0 adderGccS0 ∧
    inInt32 2 = true ∧ inInt32 3 = true ∧ inInt32 (2 + 3) = true ∧
    adderGccS0.g.inp = decStr 2 ++ [32#8] ++ decStr 3 ++ [10#8] ∧ adderGccS0.g.out = [] :=
  ⟨hFcS, hFlS, adderGcc_loaded, adderGcc_placed, adderGcc_entry rel, adderGcc_tls, by decide,
    by decide, by decide, rfl, rfl⟩

/-- **`adderGcc` on `"2 3\n"`**: every run of the concrete process ends with exit status `0`
and `stdout` = `"5\n"` (with reliable writes); the stack guard check passes. -/
theorem adderGcc_s0 :
    MustQ (adderGccWorld b0 lb0 gate0 fs0 true)
      (fun u => u.g.done = some (0, [0x35#8, 0x0a#8])) adderGccS0 := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderGcc_sum hFcS hFlS adderGcc_loaded adderGcc_placed (adderGcc_entry true) adderGcc_tls
      (x := 2) (y := 3) (by decide) (by decide) (by decide) rfl rfl)
  rintro u ⟨w, hd, -, hw⟩
  rw [hd, hw rfl, out5]

/-! ## Runs -/

/-- **A run of `adderClang` exists**: on `"2 3\n"` it exits `0` having written `"5\n"`. -/
theorem adderClang_run :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (adderClangWorld b0 lb0 gate0 true)) (fun _ => True)
      adderClangS0 t ∧ t.g.done = some (0, [0x35#8, 0x0a#8]) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun _ h => absurd h id) (stdioNamed_total _ _)) trivial adderClang_s0

/-- **A run of `adderGcc` exists**: on `"2 3\n"` it exits `0` having written `"5\n"`. -/
theorem adderGcc_run :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (adderGccWorld b0 lb0 gate0 fs0 true)) (fun _ => True)
      adderGccS0 t ∧ t.g.done = some (0, [0x35#8, 0x0a#8]) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun a h => by simp only [Guard] at h; rw [fs0_toNat] at h; omega)
      (stdioNamed_total _ _)) trivial adderGcc_s0

end Silmaril.Elf.Link.Dyn.Small.NonVacuous
