module

public import Silmaril.Wasi.Versions.WitImport.RFree.Thms
public import Silmaril.Wasi.Versions.WitImport.RTables3.Defs
public import Silmaril.Wasi.Versions.WitImport.RCli2.Thms
public import Silmaril.Wasi.Versions.WitImport.P3.Thms
public import Silmaril.Wasi.Versions.WitImport.Compare.Thms
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs
public import Silmaril.Wasi.Versions.P3.Wit.Thms

/-!
# The hand-written WASI 0.3 slice and `wasi:random` against the resolved WIT typing

`p3P = cli3P ++ clocks3P ++ fs3P` (tables and environments appended); `p3P_strip`: its table is
`p3T`. The other resolved 0.3 tables strip to the old ones too (`rand3P_strip`,
`rand2P_strip`, `http3P_strip`).

Resolved, `mark = u64` (`mark_eq`) and the filesystem `error-code` is a `variant` of 37 cases
whose last, `other`, carries an `option<string>` (`fsErr_eq`).

* **Equal** (`ok3_eqR`): for `write-via-stream`, `read-via-stream`, `now`, `wait-for` and
  `[method]descriptor.read-via-stream` (`p3E`), `P3.ok3` *is* the resolved result check, for
  every argument list. So the sound direction (`ok3_witR`) holds on these, and
  `host3_witR`: the concrete host `P3.host3 F` answers with the resolved WIT types.
* **Converse** (`witR_ok3`): for all seven slice functions (`p3C`), a resolved-typed answer to
  a call with resolved-typed arguments passes `P3.ok3`.
* **REFUTED sound direction** for `open-at` (`openAt3_not_witR`: `P3.ok3` accepts
  `error(true)`, where the resolved `error-code` is a variant) and, as before resolution, for
  `get-directories` (`getDirs3_not_witR`). Unresolved, `open-at` was sound
  (`p3_ok3_wit`): resolution is what exposes it.
* **`wasi:random`** has no named types (`rand3P_free`, `rand2P_free`), so its comparisons move
  unchanged (`witROk_free`): `ok3R_eq : Random.ok3 e = (witROk rand3P e && len3 e)` and
  `ok2R_eq`.

Since the switch (`wf-p2-switch`), `p3P` is defined in `WitImport.RSlices`, `p3E` in
`P3.Defs`, and the per-function comparisons (`p3_sigsR`, `mark_eq`, `ok3_stdoutR`, …,
`ok3H_eqR`, `ok3_eqR`) and `P3.ok3_eq_hand` in `Silmaril.Wasi.Versions.P3.Wit`, below `P3.Thms`.
`P3.ok3` is now the WIT-derived check; the results here are stated for it.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions.P3

theorem p3P_strip : strip p3P.1 = p3T := by decide +kernel
theorem http3P_strip : strip http3P.1 = http3T := by decide +kernel

/-! ## `wasi:random` -/


/-- **`Random.ok3` is the resolved WIT typing plus the short-read condition.** -/
theorem ok3R_eq (e : WEv) : Random.ok3 e = (witROk rand3P e && len3 e) := rfl

/-- **`Random.ok2` is the resolved WIT typing plus the exact-length condition.** -/
theorem ok2R_eq (e : WEv) : Random.ok2 e = (witROk rand2P e && len2 e) := rfl

/-- **Sound direction on `p3E`: `P3.ok3` implies the resolved WIT typing.** -/
theorem ok3_witR (e : WEv) (h : ok3 e = true) : witROk (rrestrict p3P p3E) e = true := by
  cases e with
  | imp f a r =>
    simp only [witROk, lookup_rrestrict]
    by_cases hf : f ∈ p3E
    · obtain ⟨i, s, hl, hok⟩ := ok3_eqR f hf
      simp [rrestrict_snd, hf, hl, ← hok a r, h]
    · simp [hf]
  | _ => rfl

/-- **The concrete 0.3 host answers with the resolved WIT types** (the functions `p3E`). -/
theorem host3_witR {Y : Silmaril.Games.Sig.{0}} {I : Set FnName} (F : BitVec 32 → List (BitVec 8)) :
    (hostSat (witRTh (rrestrict p3P p3E)).Accepts).holds (concrete (Y := Y) (I := I) (host3 F)) := by
  intro s hs
  have h := (pointwise_accepts_iff _ _).1 (host3_typed (Y := Y) (I := I) F s hs)
  exact (pointwise_accepts_iff _ _).2 fun e he => ok3_witR e (h e he)

/-! ## The converse -/

theorem witR_openAt (a : List Val) (r : Option (List Val))
    (h : resOkR p3P.2 (iface3 "filesystem" "types") sOpenAt r = true) :
    ok3 (.imp openAt3 a r) = true := by
  rw [resOkR_one, fuel_eq] at h
  simp +decide only [ok3_eq_hand, ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try exact absurd h Bool.false_ne_true
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | x⟩
  all_goals try first | rfl | exact absurd h Bool.false_ne_true
  cases x <;> first | rfl | exact absurd h Bool.false_ne_true

theorem preopenOk_of_zip {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (v : Val)
    (h : tyOkR E (n + 1 + 1) c (.tuple [.own ⟨.local, "descriptor"⟩, .prim .string]) v = true) :
    preopenOk v = true := by
  cases v <;> try exact absurd h Bool.false_ne_true
  rename_i vs
  rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> simp [tyOkR_tuple, zipOk] at h
  cases x <;> simp_all [tyOkR_own, isU32, preopenOk]

theorem witR_getDirs (a : List Val) (r : Option (List Val))
    (h : resOkR p3P.2 (iface3 "filesystem" "preopens") sDirs r = true) :
    ok3 (.imp getDirs3 a r) = true := by
  rw [resOkR_one, fuel_eq] at h
  simp +decide only [ok3_eq_hand, ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try exact absurd h Bool.false_ne_true
  cases v <;> try exact absurd h Bool.false_ne_true
  rename_i ds
  simp only [tyOkR_list, recV, List.all_eq_true] at h
  simp only [List.all_eq_true]
  exact fun d hd => preopenOk_of_zip d (h d hd)

/-- All seven functions of the slice. -/
def p3C : List FnName := p3E ++ [openAt3, getDirs3]

/-- **Converse: a resolved-typed answer to a resolved-typed call passes `P3.ok3`** (all seven
slice functions). -/
theorem witR_ok3 (f : FnName) (hf : f ∈ p3C) (a : List Val) (r : Option (List Val))
    (ha : ∀ i s, p3P.1.lookup f = some (i, s) → argsOkR p3P.2 i s a = true)
    (h : witROk (rrestrict p3P p3C) (.imp f a r) = true) : ok3 (.imp f a r) = true := by
  obtain ⟨-, -, -, -, -, h6, h7⟩ := p3_sigsR
  have hres : ∀ i s, p3P.1.lookup f = some (i, s) → resOkR p3P.2 i s r = true := by
    intro i s hl
    simpa [witROk, lookup_rrestrict, rrestrict_snd, hf, hl, ha i s hl] using h
  simp only [p3C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | rfl | rfl
  · obtain ⟨i, s, hl, hok⟩ := ok3_eqR f hf
    rw [hok]
    exact hres i s hl
  · exact witR_openAt a r (hres _ _ h6)
  · exact witR_getDirs a r (hres _ _ h7)

/-! ## Refutations -/

/-- An `open-at` call with resolved-typed arguments answered `error(true)`. -/
def openAtBad : WEv :=
  .imp openAt3 [.u32 0, .record [.bool false], strV "a",
    .record [.bool false, .bool false, .bool false, .bool false],
    .record [.bool true, .bool false, .bool false, .bool false, .bool false, .bool false]]
    (some [errV (some (.bool true))])

/-- **REFUTED sound direction for `open-at`**: `P3.ok3` accepts an `error` payload that is not a
resolved `error-code`, on a call whose arguments are resolved-typed. -/
theorem openAt3_not_witR :
    ok3 openAtBad = true ∧ witROk (rrestrict p3P [openAt3]) openAtBad = false := by
  rw [ok3_eq_hand]
  decide +kernel

/-- **REFUTED for `get-directories`, resolved**: as `getDirs3_not_wit`. -/
theorem getDirs3_not_witR :
    ok3 badDirs = true ∧ witROk (rrestrict p3P [getDirs3]) badDirs = false := by
  rw [ok3_eq_hand]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
