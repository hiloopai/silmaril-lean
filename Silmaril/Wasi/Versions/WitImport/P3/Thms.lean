module

public import Silmaril.Wasi.Versions.WitImport.Names.Thms
public import Silmaril.Wasi.Versions.P3.Thms
public import Silmaril.Wasi.Theory.Thms

/-!
# The hand-written WASI 0.3 typing against the imported signatures

`p3_sigs`: the imported 0.3.2 signatures of the functions of the hand-written slice
(`P3.wasiFns3`; `error-code`, `mark`, `duration`, `filesize`, `descriptor` are named types of
their interfaces).

* **`p3_ok3_wit`**: the hand-written typing `P3.ok3` implies the imported WIT typing
  `witOk (restrict p3T p3L)` for every event, for the functions `p3L` of the slice except
  `get-directories`. Consequently `host3_wit`: the concrete 0.3 host `P3.host3 F` answers with
  the imported WIT types.
* **REFUTED for `get-directories`** (`getDirs3_not_wit`): `P3.ok3` accepts a preopen whose name
  is not a `string` (it checks only the `u32` descriptor, `preopenOk`). The WIT type is
  `list<tuple<descriptor, string>>`.
* `openAt3_slice_untyped`: the slice calls `open-at(self, path)` with two arguments; the WIT
  `open-at` has five parameters (`self`, `path-flags`, `path`, `open-flags`, `flags`), so these
  calls are not WIT-typed and `witOk` does not constrain their answers (a documented deviation of
  the slice, see `Silmaril.Wasi.Versions.P3`).

The other direction does not hold: `tyOk` leaves named types unconstrained (`mark`), so `witOk`
accepts answers `P3.ok3` rejects.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions.P3

/-- **The imported signatures of the 0.3 slice.** -/
theorem p3_sigs :
    p3T.lookup stdoutWrite3 = some ⟨false, [("data", .stream (some (.prim .u8)))],
      some (.future (some (.result none (some (lref "error-code")))))⟩ ∧
    p3T.lookup stdinRead3 = some ⟨false, [], some tStreamFut⟩ ∧
    p3T.lookup now3 = some ⟨false, [], some (lref "mark")⟩ ∧
    p3T.lookup waitFor3 = some ⟨true, [("how-long", lref "duration")], none⟩ ∧
    p3T.lookup openAt3 = some ⟨true, [("self", .borrow ⟨.local, "descriptor"⟩),
      ("path-flags", lref "path-flags"), ("path", .prim .string), ("open-flags", lref "open-flags"),
      ("flags", lref "descriptor-flags")],
      some (.result (some (.own ⟨.local, "descriptor"⟩)) (some (lref "error-code")))⟩ ∧
    p3T.lookup readVia3 = some ⟨false, [("self", .borrow ⟨.local, "descriptor"⟩),
      ("offset", lref "filesize")], some tStreamFut⟩ ∧
    p3T.lookup getDirs3 = some ⟨false, [],
      some (.list (.tuple [.own ⟨.local, "descriptor"⟩, .prim .string]))⟩ := by
  decide +kernel

/-- The hand-written answers of `f` are well typed for the imported signature of `f`. -/
def ResOk (f : FnName) : Prop :=
  ∃ s, p3T.lookup f = some s ∧ ∀ a r, ok3 (.imp f a r) = true → resOk s r = true

theorem resOk_stdout : ResOk stdoutWrite3 := ⟨_, p3_sigs.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | simp at h⟩

theorem resOk_stdin : ResOk stdinRead3 := ⟨_, p3_sigs.2.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | simp at h⟩

theorem resOk_now : ResOk now3 := ⟨_, p3_sigs.2.2.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | simp at h⟩

theorem resOk_waitFor : ResOk waitFor3 := ⟨_, p3_sigs.2.2.2.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | simp at h⟩

theorem resOk_openAt : ResOk openAt3 := ⟨_, p3_sigs.2.2.2.2.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | (simp at h; done) | simp [resOk, tyOk, tyOpt]⟩

theorem resOk_readVia : ResOk readVia3 := ⟨_, p3_sigs.2.2.2.2.2.1, fun a r h => by
  simp +decide [ok3_eq_hand, ok3H] at h
  split at h <;> first | rfl | simp at h⟩

theorem resOk_p3L : ∀ f ∈ p3L, ResOk f := by
  intro f hf
  simp only [p3L, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [resOk_stdout, resOk_stdin, resOk_now, resOk_waitFor, resOk_openAt, resOk_readVia]

/-- **The hand-written 0.3 typing implies the imported WIT typing** (except `get-directories`). -/
theorem p3_ok3_wit (e : WEv) (h : ok3 e = true) : witOk (restrict p3T p3L) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f ∈ p3L
    · obtain ⟨s, hs, hok⟩ := resOk_p3L f hf
      simp [witOk, lookup_restrict, hf, hs, hok a r h]
    · simp [witOk, lookup_restrict, hf]
  | _ => rfl

/-- **The concrete 0.3 host answers with the imported WIT types** (the functions `p3L`). -/
theorem host3_wit {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (F : BitVec 32 → List (BitVec 8)) :
    (hostSat (witTh (restrict p3T p3L)).Accepts).holds (concrete (Y := Y) (I := I) (host3 F)) := by
  intro s hs
  have h := (pointwise_accepts_iff _ _).1 (host3_typed (Y := Y) (I := I) F s hs)
  exact (pointwise_accepts_iff _ _).2 fun e he => p3_ok3_wit e (h e he)

/-- A preopen answer with a non-string name. -/
def badDirs : WEv := .imp getDirs3 [] (some [.record [.record [.u32 0, .u64 0]]])

/-- **REFUTED for `get-directories`**: `P3.ok3` accepts a preopen name that is not a string. -/
theorem getDirs3_not_wit :
    ok3 badDirs = true ∧ witOk (restrict p3T [getDirs3]) badDirs = false := by
  rw [ok3_eq_hand]
  decide +kernel

/-- The slice's `open-at(self, path)` calls are not WIT-typed calls. -/
theorem openAt3_slice_untyped (s : Binary.Sig) (hs : p3T.lookup openAt3 = some s) (d : BitVec 32)
    (p : String) : argsOk s [.u32 d, strV p] = false := by
  rw [p3_sigs.2.2.2.2.1] at hs
  cases hs
  simp [argsOk, tysOk, tyOk]

end Silmaril.Wasi.Versions.WitImport
