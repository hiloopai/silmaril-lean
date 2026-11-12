module

public import Silmaril.Raw.Elf.Link.Dyn.Small.NonVacuous.Basic
public import Silmaril.Raw.Elf.Link.Dyn.Small.Ret

/-! # `return 0` / `return 42`: the hypotheses of `_exits` are satisfiable, and a run exists

For each of the four executables, a concrete process (`NonVacuous.Basic`: the executable at
`b0`, glibc files holding the pinned chunks and zeros elsewhere, a memory holding exactly the
loader relation's image, a stack with `argc = 1`):

* `_nonvacuous`: it meets every hypothesis of `_exits` (`ChunksOf`, `ExeLoaded`, `Placed`,
  `AtEntry`, empty `stdout`);
* `_s0`: `_exits` for it;
* `_run`: **an actual run** of it ends with exit status `0` (resp. `42`) and nothing written
  (`proc_progress`: the machine always has an outcome, so `Must` yields a run).
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

/-- `libc.so.6` and `ld.so` holding the (hello) pinned chunks. -/
def FcR : Blob := blobOf libcChunks
def FlR : Blob := blobOf ldChunks

theorem hFcR : ChunksOf FcR libcChunks := by unfold ChunksOf; decide +kernel
theorem hFlR : ChunksOf FlR ldChunks := by unfold ChunksOf; decide +kernel

/-! ## `ret0Gcc` -/

def ret0GccT : List (Nat × Option Word) := tableOf ret0GccSlots
theorem ret0Gcc_T : ret0GccSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some ret0GccT := by decide +kernel
theorem ret0Gcc_tab : tableOk ret0GccFile ret0GccInfo ret0GccT ret0GccLayout.size = true := by decide +kernel
theorem ret0Gcc_placed : Placed ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 := by
  constructor <;> (try unfold Img) <;> decide +kernel

/-- The start state of `ret0Gcc`. -/
def ret0GccS0 : PState := sOf (memOf ret0GccFile ret0GccInfo ret0GccT ret0GccLayout.size) ret0GccLayout.start []

theorem ret0Gcc_loaded :
    ExeLoaded [ret0GccFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret0GccS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, ret0Gcc_info, fun h => absurd h (by decide), ret0Gcc_slots hFcR hFlR,
    ret0Gcc_T, imageOk_of_table (by decide) ret0Gcc_tab⟩

theorem ret0Gcc_entry (rel : Bool) :
    AtEntry ret0GccLayout (smallWorld ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret0GccS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the concrete process meets every hypothesis of `ret0Gcc_exits`. -/
theorem ret0Gcc_nonvacuous (rel : Bool) :
    ChunksOf FcR libcChunks ∧ ChunksOf FlR ldChunks ∧
    ExeLoaded [ret0GccFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret0GccS0.m.memory ∧
    Placed ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 ∧
    AtEntry ret0GccLayout (smallWorld ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret0GccS0 ∧
    ret0GccS0.g.out = [] :=
  ⟨hFcR, hFlR, ret0Gcc_loaded, ret0Gcc_placed, ret0Gcc_entry rel, rfl⟩

theorem ret0Gcc_s0 (rel : Bool) :
    MustQ (smallWorld ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel)
      (fun u => u.g.done = some (0, [])) ret0GccS0 :=
  ret0Gcc_exits hFcR hFlR ret0Gcc_loaded ret0Gcc_placed (ret0Gcc_entry rel) rfl

/-- **A run exists**: the concrete process runs to exit status `0` with nothing written. -/
theorem ret0Gcc_run (rel : Bool) :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (smallWorld ret0GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel))
      (fun _ => True) ret0GccS0 t ∧ t.g.done = some (0, []) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun _ h => absurd h id) (fun _ _ => ⟨.stop, rfl⟩)) trivial (ret0Gcc_s0 rel)

/-! ## `ret0Clang` -/

def ret0ClangT : List (Nat × Option Word) := tableOf ret0ClangSlots
theorem ret0Clang_T : ret0ClangSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some ret0ClangT := by decide +kernel
theorem ret0Clang_tab : tableOk ret0ClangFile ret0ClangInfo ret0ClangT ret0ClangLayout.size = true := by decide +kernel
theorem ret0Clang_placed : Placed ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 := by
  constructor <;> (try unfold Img) <;> decide +kernel

/-- The start state of `ret0Clang`. -/
def ret0ClangS0 : PState := sOf (memOf ret0ClangFile ret0ClangInfo ret0ClangT ret0ClangLayout.size) ret0ClangLayout.start []

theorem ret0Clang_loaded :
    ExeLoaded [ret0ClangFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret0ClangS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, ret0Clang_info, fun h => absurd h (by decide), ret0Clang_slots hFcR hFlR,
    ret0Clang_T, imageOk_of_table (by decide) ret0Clang_tab⟩

theorem ret0Clang_entry (rel : Bool) :
    AtEntry ret0ClangLayout (smallWorld ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret0ClangS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the concrete process meets every hypothesis of `ret0Clang_exits`. -/
theorem ret0Clang_nonvacuous (rel : Bool) :
    ChunksOf FcR libcChunks ∧ ChunksOf FlR ldChunks ∧
    ExeLoaded [ret0ClangFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret0ClangS0.m.memory ∧
    Placed ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 ∧
    AtEntry ret0ClangLayout (smallWorld ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret0ClangS0 ∧
    ret0ClangS0.g.out = [] :=
  ⟨hFcR, hFlR, ret0Clang_loaded, ret0Clang_placed, ret0Clang_entry rel, rfl⟩

theorem ret0Clang_s0 (rel : Bool) :
    MustQ (smallWorld ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel)
      (fun u => u.g.done = some (0, [])) ret0ClangS0 :=
  ret0Clang_exits hFcR hFlR ret0Clang_loaded ret0Clang_placed (ret0Clang_entry rel) rfl

/-- **A run exists**: the concrete process runs to exit status `0` with nothing written. -/
theorem ret0Clang_run (rel : Bool) :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (smallWorld ret0ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel))
      (fun _ => True) ret0ClangS0 t ∧ t.g.done = some (0, []) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun _ h => absurd h id) (fun _ _ => ⟨.stop, rfl⟩)) trivial (ret0Clang_s0 rel)

/-! ## `ret42Gcc` -/

def ret42GccT : List (Nat × Option Word) := tableOf ret42GccSlots
theorem ret42Gcc_T : ret42GccSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some ret42GccT := by decide +kernel
theorem ret42Gcc_tab : tableOk ret42GccFile ret42GccInfo ret42GccT ret42GccLayout.size = true := by decide +kernel
theorem ret42Gcc_placed : Placed ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 := by
  constructor <;> (try unfold Img) <;> decide +kernel

/-- The start state of `ret42Gcc`. -/
def ret42GccS0 : PState := sOf (memOf ret42GccFile ret42GccInfo ret42GccT ret42GccLayout.size) ret42GccLayout.start []

theorem ret42Gcc_loaded :
    ExeLoaded [ret42GccFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret42GccS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, ret42Gcc_info, fun h => absurd h (by decide), ret42Gcc_slots hFcR hFlR,
    ret42Gcc_T, imageOk_of_table (by decide) ret42Gcc_tab⟩

theorem ret42Gcc_entry (rel : Bool) :
    AtEntry ret42GccLayout (smallWorld ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret42GccS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the concrete process meets every hypothesis of `ret42Gcc_exits`. -/
theorem ret42Gcc_nonvacuous (rel : Bool) :
    ChunksOf FcR libcChunks ∧ ChunksOf FlR ldChunks ∧
    ExeLoaded [ret42GccFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret42GccS0.m.memory ∧
    Placed ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 ∧
    AtEntry ret42GccLayout (smallWorld ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret42GccS0 ∧
    ret42GccS0.g.out = [] :=
  ⟨hFcR, hFlR, ret42Gcc_loaded, ret42Gcc_placed, ret42Gcc_entry rel, rfl⟩

theorem ret42Gcc_s0 (rel : Bool) :
    MustQ (smallWorld ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel)
      (fun u => u.g.done = some (42, [])) ret42GccS0 :=
  ret42Gcc_exits hFcR hFlR ret42Gcc_loaded ret42Gcc_placed (ret42Gcc_entry rel) rfl

/-- **A run exists**: the concrete process runs to exit status `42` with nothing written. -/
theorem ret42Gcc_run (rel : Bool) :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (smallWorld ret42GccLayout b0 lb0 gate0 0x2a200 0x472c0 rel))
      (fun _ => True) ret42GccS0 t ∧ t.g.done = some (42, []) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun _ h => absurd h id) (fun _ _ => ⟨.stop, rfl⟩)) trivial (ret42Gcc_s0 rel)

/-! ## `ret42Clang` -/

def ret42ClangT : List (Nat × Option Word) := tableOf ret42ClangSlots
theorem ret42Clang_T : ret42ClangSlots.mapM (fun e => (e.2.word [b0, lb0, ldb0] ifn0 res0).map fun w => (e.1, w)) =
    some ret42ClangT := by decide +kernel
theorem ret42Clang_tab : tableOk ret42ClangFile ret42ClangInfo ret42ClangT ret42ClangLayout.size = true := by decide +kernel
theorem ret42Clang_placed : Placed ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 := by
  constructor <;> (try unfold Img) <;> decide +kernel

/-- The start state of `ret42Clang`. -/
def ret42ClangS0 : PState := sOf (memOf ret42ClangFile ret42ClangInfo ret42ClangT ret42ClangLayout.size) ret42ClangLayout.start []

theorem ret42Clang_loaded :
    ExeLoaded [ret42ClangFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret42ClangS0.m.memory :=
  ⟨_, _, _, _, _, rfl, rfl, ret42Clang_info, fun h => absurd h (by decide), ret42Clang_slots hFcR hFlR,
    ret42Clang_T, imageOk_of_table (by decide) ret42Clang_tab⟩

theorem ret42Clang_entry (rel : Bool) :
    AtEntry ret42ClangLayout (smallWorld ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret42ClangS0 :=
  atEntry0 (by decide) _ _ _ (crt_kept_stack (by decide) (fun _ h => absurd h id))

/-- **Non-vacuity**: the concrete process meets every hypothesis of `ret42Clang_exits`. -/
theorem ret42Clang_nonvacuous (rel : Bool) :
    ChunksOf FcR libcChunks ∧ ChunksOf FlR ldChunks ∧
    ExeLoaded [ret42ClangFile, FcR, FlR] [b0, lb0, ldb0] ifn0 false res0 ret42ClangS0.m.memory ∧
    Placed ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 ∧
    AtEntry ret42ClangLayout (smallWorld ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel) b0 ret42ClangS0 ∧
    ret42ClangS0.g.out = [] :=
  ⟨hFcR, hFlR, ret42Clang_loaded, ret42Clang_placed, ret42Clang_entry rel, rfl⟩

theorem ret42Clang_s0 (rel : Bool) :
    MustQ (smallWorld ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel)
      (fun u => u.g.done = some (42, [])) ret42ClangS0 :=
  ret42Clang_exits hFcR hFlR ret42Clang_loaded ret42Clang_placed (ret42Clang_entry rel) rfl

/-- **A run exists**: the concrete process runs to exit status `42` with nothing written. -/
theorem ret42Clang_run (rel : Bool) :
    ∃ t, Silmaril.X86.RelIsa.RunsInR (proc (smallWorld ret42ClangLayout b0 lb0 gate0 0x2a200 0x472c0 rel))
      (fun _ => True) ret42ClangS0 t ∧ t.g.done = some (42, []) :=
  Silmaril.X86.RelIsa.Must.exists_run
    (crt_progress (by decide) (fun _ h => absurd h id) (fun _ _ => ⟨.stop, rfl⟩)) trivial (ret42Clang_s0 rel)

end Silmaril.Elf.Link.Dyn.Small.NonVacuous
