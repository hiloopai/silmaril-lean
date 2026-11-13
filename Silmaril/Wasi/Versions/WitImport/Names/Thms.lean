module

public import Silmaril.Wasi.Versions.WitImport.Compare.Defs
public import Silmaril.Wasi.Versions.Random.Defs
public import Silmaril.Wasi.Versions.P2.World.Defs

/-!
# The imported WASI names equal the hand-written ones

The hand-written function sets of `Silmaril.Wasi.Versions` against the tables of
`Silmaril.Wasi.Versions.WitImport.Tables` (computed by the WIT importer from `vendor/wasi`):

* all of a package: `rand3Fns_iff`, `rand2Fns_iff` (`wasi:random`; the worlds `rand3World_eq`,
  `rand2World_eq`), `ioImports_iff` (`wasi:io`
  0.2 with its four resource drops), `clockImports_iff` (`wasi:clocks` 0.2);
* slices: `cliImports_sub`, `fsImports_sub` (0.2), `wasiFns3_sub`, `run3_mem` (0.3);
* `async3`: `wait-for` and `open-at` are the functions of the 0.3 slice the WIT marks `async`
  (`P3.asyncFns3`); the hand-written names are the importer's `plainName`s, without the
  `[async]` marker of `Binary.Func.mangled`.

Generic lemmas on tables: `lookup_none`, `lookup_restrict`, `witOk_none`.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component.Binary (PrimValType)
open Silmaril.Wasi.Versions.Random

/-! ## Generic lemmas -/

theorem lookup_none {T : Table} {f : FnName} (h : f ∉ names T) : T.lookup f = none := by
  induction T with
  | nil => rfl
  | cons x T ih =>
    simp only [names, List.map_cons, List.mem_cons, not_or] at h
    simp [List.lookup, beq_false_of_ne h.1, ih h.2]

theorem lookup_restrict (T : Table) (L : List FnName) (f : FnName) :
    (restrict T L).lookup f = if f ∈ L then T.lookup f else none := by
  induction T with
  | nil => simp [restrict]
  | cons x T ih =>
    by_cases hx : x.1 ∈ L
    · by_cases hf : f = x.1
      · subst hf; simp [restrict, List.filter, hx, List.lookup]
      · simp only [restrict] at ih ⊢
        simp [List.filter, hx, List.lookup, beq_false_of_ne hf, ih]
    · simp only [restrict] at ih ⊢
      by_cases hf : f = x.1
      · subst hf; simp [List.filter, hx, ih]
      · simp [List.filter, hx, List.lookup, beq_false_of_ne hf, ih]

theorem witOk_none {T : Table} {f : FnName} (h : T.lookup f = none) (a : List Val)
    (r : Option (List Val)) : witOk T (.imp f a r) = true := by
  simp [witOk, h]

/-- A value is a list of `u8`. -/
theorem tyAll_u8 (vs : List Val) : tyAll (.prim .u8) vs = allU8 (.record vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => cases v <;> simp_all [tyAll, tyOk, primOk, allU8]

theorem tyOk_bytes (v : Val) : tyOk (.list (.prim .u8)) v = allU8 v := by
  cases v <;> simp [tyOk, allU8, tyAll_u8]

theorem argsOk_u64 (n : String) (res : Option Binary.Ty) (a : List Val) :
    argsOk ⟨false, [(n, .prim .u64)], res⟩ a = (match a with | [.u64 _] => true | _ => false) := by
  rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩ <;> try cases v
  all_goals simp [argsOk, tysOk, tyOk, primOk]

theorem argsOk_nil (res : Option Binary.Ty) (a : List Val) :
    argsOk ⟨false, [], res⟩ a = a.isEmpty := by
  cases a <;> rfl

/-! ## Names -/

theorem rand3_names : names rand3T = [insSeed3, insBytes3, insU64_3, randBytes3, randU64_3] := by
  decide +kernel

theorem rand2_names : names rand2T = [insSeed2, insBytes2, insU64_2, randBytes2, randU64_2] := by
  decide +kernel

theorem rand3_perm :
    (names rand3T).Perm [randBytes3, randU64_3, insBytes3, insU64_3, insSeed3] := by
  rw [rand3_names]; decide +kernel

theorem rand2_perm :
    (names rand2T).Perm [randBytes2, randU64_2, insBytes2, insU64_2, insSeed2] := by
  rw [rand2_names]; decide +kernel

/-- **`wasi:random` 0.3: the hand-written functions are the imported ones.** -/
theorem rand3Fns_iff (f : FnName) : f ∈ rand3Fns ↔ f ∈ names rand3T := by
  rw [rand3_perm.mem_iff]; simp [rand3Fns_eq]

/-- **`wasi:random` 0.2: the hand-written functions are the imported ones.** -/
theorem rand2Fns_iff (f : FnName) : f ∈ rand2Fns ↔ f ∈ names rand2T := by
  rw [rand2_perm.mem_iff]; simp [rand2Fns_eq]

/-- **The `wasi:random` 0.3 world is the imported one.** -/
theorem rand3World_eq : rand3World = ⟨{f | f ∈ names rand3T}, ∅⟩ := by
  simp only [rand3World, World.mk.injEq, and_true]
  exact Set.ext rand3Fns_iff

/-- **The `wasi:random` 0.2 world is the imported one.** -/
theorem rand2World_eq : rand2World = ⟨{f | f ∈ names rand2T}, ∅⟩ := by
  simp only [rand2World, World.mk.injEq, and_true]
  exact Set.ext rand2Fns_iff

open Silmaril.Wasi.Versions.P2 in
theorem io2_names : names io2T ++ io2D =
    [errDebug, pollReady, pollBlock, pollPoll, isRead, isBread, isSkip, isBskip, isSubscribe,
     osCheckWrite, osWrite, osBwf, osFlush, osBflush, osSubscribe, osWriteZeroes, osBwzf,
     osSplice, osBsplice, errDrop, pollDrop, isDrop, osDrop] := by
  decide +kernel

open Silmaril.Wasi.Versions.P2 in
theorem io2_perm : (names io2T ++ io2D).Perm
    [osCheckWrite, osWrite, osBwf, osFlush, osBflush, osSubscribe, osWriteZeroes, osBwzf, osSplice,
     osBsplice, osDrop, isRead, isBread, isSkip, isBskip, isSubscribe, isDrop, pollReady, pollBlock,
     pollPoll, pollDrop, errDebug, errDrop] := by
  rw [io2_names]; decide +kernel

open Silmaril.Wasi.Versions.P2 in
/-- **`wasi:io` 0.2: the hand-written imports are the imported functions and drops.** -/
theorem ioImports_iff (f : FnName) : f ∈ ioImports ↔ f ∈ names io2T ++ io2D := by
  rw [io2_perm.mem_iff]; simp [ioImports_eq]

open Silmaril.Wasi.Versions.P2 in
theorem clocks2_names :
    names clocks2T = [clockNow, monoRes, monoSubInstant, monoSubDuration, wallNow, wallRes] := by
  decide +kernel

open Silmaril.Wasi.Versions.P2 in
theorem clocks2_perm : (names clocks2T).Perm
    [clockNow, monoRes, monoSubInstant, monoSubDuration, wallNow, wallRes] := by
  rw [clocks2_names]

open Silmaril.Wasi.Versions.P2 in
/-- **`wasi:clocks` 0.2: the hand-written imports are the imported functions.** -/
theorem clockImports_iff (f : FnName) : f ∈ clockImports ↔ f ∈ names clocks2T := by
  rw [clocks2_perm.mem_iff]; simp [clockImports_eq]

open Silmaril.Wasi.Versions.P2 in
theorem cliImports_list : ∀ f ∈ [getEnv, getArgs, initialCwd, cliExit, getStdin, getStdout,
    getStderr, getTermStdin, getTermStdout, getTermStderr], f ∈ names cli2T := by
  decide +kernel

open Silmaril.Wasi.Versions.P2 in
/-- The hand-written `wasi:cli` 0.2 slice consists of imported functions. -/
theorem cliImports_sub : cliImports ⊆ {f | f ∈ names cli2T} := by
  intro f hf
  exact cliImports_list f (by simpa [cliImports_eq] using hf)

open Silmaril.Wasi.Versions.P2 in
theorem fsImports_list : ∀ f ∈ [getDirs, openAt, fdWrite, fdRead, fdDrop, fdReadStream,
    fdWriteStream, fdAppendStream, fdGetType], f ∈ names fs2T ++ fs2D := by
  decide +kernel

open Silmaril.Wasi.Versions.P2 in
/-- The hand-written `wasi:filesystem` 0.2 slice consists of imported functions and drops. -/
theorem fsImports_sub : fsImports ⊆ {f | f ∈ names fs2T ++ fs2D} := by
  intro f hf
  exact fsImports_list f (by simpa [fsImports_eq] using hf)

theorem wasiFns3_list : ∀ f ∈ [P3.stdoutWrite3, P3.stdinRead3, P3.now3, P3.waitFor3,
    P3.getDirs3, P3.openAt3, P3.readVia3], f ∈ names p3T := by
  decide +kernel

/-- The hand-written WASI 0.3 slice consists of imported functions. -/
theorem wasiFns3_sub : P3.wasiFns3 ⊆ {f | f ∈ names p3T} := by
  intro f hf
  exact wasiFns3_list f (by simpa [P3.wasiFns3_eq] using hf)

/-- The export `wasi:cli/run.run` of the 0.3 slice is imported (`run: async func() -> result`). -/
theorem run3_mem : P3.run3 ∈ names cli3T := by decide +kernel

/-- **The async functions of the 0.3 slice are those the WIT marks `async`.** -/
theorem async3 : [P3.stdoutWrite3, P3.stdinRead3, P3.now3, P3.waitFor3, P3.getDirs3, P3.openAt3,
    P3.readVia3].filter (fun f => (p3T.lookup f).any (·.async)) = [P3.waitFor3, P3.openAt3] := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
