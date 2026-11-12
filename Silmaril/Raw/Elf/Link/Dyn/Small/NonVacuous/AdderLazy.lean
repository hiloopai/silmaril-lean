module

public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Adder
public import Silmaril.Raw.Elf.Link.Dyn.Small.AdderClangLazyMain

/-! # The clang adder under lazy binding: the hypotheses are satisfiable, and a run exists

A concrete process loaded with **lazy** binding (`ExeLoaded … true resL0 …`: the jump slots
hold their PLT entries' `push`, `GOT[2]` the resolver at `resL0`), `stdin` = `"2 3\n"`:
`adderClangL_nonvacuous` (every hypothesis of `adderClangL_sum`), `adderClangL_s0` (every run
exits `0` with `stdout` = `"5\n"`) and `adderClangL_run0` (such a run exists; it goes through
the resolver twice).
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

def adderClangLT : List (Nat × Option Word) := tableOfL adderClangSlotsLazy
theorem adderClangL_T : adderClangSlotsLazy.mapM
    (fun e => (e.2.word [b0, lb0, ldb0] ifn0 resL0).map fun w => (e.1, w)) = some adderClangLT := by
  decide +kernel
theorem adderClangL_tab : tableOk adderClangFile adderClangInfo adderClangLT adderClangLayout.size = true := by
  decide +kernel
theorem adderClangL_placed : AdderPlacedL b0 lb0 gate0 resL0 := by
  refine ⟨adderClang_placed, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold Img) <;> decide +kernel

/-- The start state, lazily bound, `stdin` = `"2 3\n"`. -/
def adderClangLS0 : PState :=
  sOf (memOf adderClangFile adderClangInfo adderClangLT adderClangLayout.size) adderClangLayout.start inp0

theorem adderClangL_loaded :
    ExeLoaded [adderClangFile, FcS, FlS] [b0, lb0, ldb0] ifn0 true resL0 adderClangLS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, adderClang_info, fun _ => adderClang_bindNow,
    adderClang_slots_lazy hFcS hFlS, adderClangL_T, imageOk_of_table (by decide) adderClangL_tab⟩

theorem adderClangL_entry (rel : Bool) :
    AtEntry adderClangLayout (adderClangWorldL b0 lb0 gate0 resL0 rel) b0 adderClangLS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the lazily bound process meets every hypothesis of `adderClangL_sum`. -/
theorem adderClangL_nonvacuous (rel : Bool) :
    ChunksOf FcS libcChunksS ∧ ChunksOf FlS ldChunksS ∧
    ExeLoaded [adderClangFile, FcS, FlS] [b0, lb0, ldb0] ifn0 true resL0 adderClangLS0.m.memory ∧
    AdderPlacedL b0 lb0 gate0 resL0 ∧
    AtEntry adderClangLayout (adderClangWorldL b0 lb0 gate0 resL0 rel) b0 adderClangLS0 ∧
    inInt32 2 = true ∧ inInt32 3 = true ∧ inInt32 (2 + 3) = true ∧
    adderClangLS0.g.inp = decStr 2 ++ [32#8] ++ decStr 3 ++ [10#8] ∧ adderClangLS0.g.out = [] :=
  ⟨hFcS, hFlS, adderClangL_loaded, adderClangL_placed, adderClangL_entry rel, by decide, by decide,
    by decide, rfl, rfl⟩

/-- **`adderClang` lazily bound, on `"2 3\n"`**: every run exits `0` with `stdout` = `"5\n"`. -/
theorem adderClangL_s0 :
    MustQ (adderClangWorldL b0 lb0 gate0 resL0 true)
      (fun u => u.g.done = some (0, [0x35#8, 0x0a#8])) adderClangLS0 := by
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) ?_
    (adderClangL_sum hFcS hFlS adderClangL_loaded adderClangL_placed (adderClangL_entry true)
      (x := 2) (y := 3) (by decide) (by decide) (by decide) rfl rfl)
  rintro u ⟨w, hd, -, hw⟩
  rw [hd, hw rfl, out5]

/-- **A run exists** (through `PLT0` and the resolver for each import's first call). -/
theorem adderClangL_run0 :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (adderClangWorldL b0 lb0 gate0 resL0 true))
      (fun _ => True) adderClangLS0 t ∧ t.g.done = some (0, [0x35#8, 0x0a#8]) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (proc_progress _ (by show b0.toNat + adderClangLayout.size ≤ 2 ^ 62; rw [b0_toNat]; decide)
      (fun a h => by rcases h with h | h <;> exact absurd h id)
      (fun res slots h => by
        simp only [adderClangWorldL, crtWorld, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; simp [adderClangJmp])
      (stdioNamed_total _ _)) trivial adderClangL_s0

end Silmaril.Elf.Link.Dyn.Small.NonVacuous
