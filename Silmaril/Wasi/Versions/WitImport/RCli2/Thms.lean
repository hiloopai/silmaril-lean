module

public import Silmaril.Wasi.Versions.WitImport.RIo2.Thms
public import Silmaril.Wasi.Versions.WitImport.Cli2.Thms

/-!
# The hand-written `wasi:cli`, `wasi:clocks` and `wasi:filesystem` 0.2 typing against the
resolved WIT typing

`p2P = cli2P ++ clocks2P ++ fs2P` (tables and environments appended); `p2P_strip`: its table is
`p2W`. `cliIface f`: the interface of `f`, written out and checked with the result types
(`cli2_resultsR`).

The named types in the results of the `cliOk` functions resolve to:
`duration = u64` (`duration_eq`), `datetime = record { seconds: u64, nanoseconds: u32 }`
(`datetime_eq`), `error-code`: an enum of 37 cases (`errorCode_eq`), `descriptor-type`: an
enum of 8 cases (`descType_eq`).

* **Equal** (`cliOkH_eqR`): for the eleven functions of `cli2E` and
  `monotonic-clock.resolution` (`cli2X`), the hand-written `P2.cliOkH f r` *is* the resolved
  result check. Before resolution only the
  eleven were equal (`cliOk_eq`): `resolution` answering `true` was WIT-typed (`badRes`), and
  resolved it is not (`badRes_not_witR`).
* **Converse** (`witR_cliOk`): for every `cliOk` function except `exit` and the two wall-clock
  functions (`cli2C`), a resolved-typed answer passes `P2.cliOk`. `witR_p2Ok`: on
  resolved-typed arguments, `witROk` implies `P2.p2Ok` for these functions.
* **Sound direction** (`cliOk_witR`, `p2Ok_witR`): `P2.cliOk` implies the resolved typing
  (traps admitted) for every `cliOk` function except the three `*-via-stream` functions and
  `get-type` (`cli2S`).
* **REFUTED**:
  - converse for the wall clock and `exit` (`witR_not_p2Ok`): `nanoseconds = 10^9` is a
    resolved `datetime` and rejected by `P2.datetimeOk`; `exit` returning is typed;
  - sound direction for `read-via-stream` and `get-type` (`cliOk_not_witR`): `P2.handleResOk`
    accepts `error(x)` for every `x`, and `get-type` any case number, where the resolved
    `error-code` and `descriptor-type` are enums.

**The switch** (`wf-p2-switch`). `P2.cliOk` is now defined from the import (`p2P`, `cli2X`,
both moved below `P2.World`): on `cli2X` it looks the signature up in `p2P` and runs the
resolved check. With `cliOkH_eqR` and `resOkR_cli` (the looked-up entry is the written-out
`cliIface`/`cliRes`), **`P2.cliOk_eq_hand : cliOk = cliOkH`**, and so `P2.p2Ok_eq_hand`,
`P2.p2Th_eq_hand`. `cliOk_eqR` keeps its statement, now about the switched `P2.cliOk`; the
other results below are stated for the switched definitions too.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/-- The resolved table of `p2P` is `p2W`. -/
theorem p2P_strip : strip p2P.1 = p2W := by decide +kernel

/-- An interface of `wasi:<p>@0.2.12`. -/
abbrev iface2 (p i : String) : Binary.IfaceName := ⟨⟨"wasi", p, some "0.2.12"⟩, i⟩

/-- The interfaces of the `cliOk` functions. -/
def cliIface (f : FnName) : Binary.IfaceName :=
  if f = P2.monoRes ∨ f = P2.monoSubInstant ∨ f = P2.monoSubDuration then
    iface2 "clocks" "monotonic-clock"
  else if f = P2.wallNow ∨ f = P2.wallRes then iface2 "clocks" "wall-clock"
  else if f = P2.fdReadStream ∨ f = P2.fdWriteStream ∨ f = P2.fdAppendStream ∨ f = P2.fdGetType
    then iface2 "filesystem" "types"
  else if f = P2.getEnv ∨ f = P2.getArgs ∨ f = P2.initialCwd then iface2 "cli" "environment"
  else if f = P2.cliExit then iface2 "cli" "exit"
  else if f = P2.getStdin then iface2 "cli" "stdin"
  else if f = getStdout then iface2 "cli" "stdout"
  else if f = P2.getStderr then iface2 "cli" "stderr"
  else if f = P2.getTermStdin then iface2 "cli" "terminal-stdin"
  else if f = P2.getTermStdout then iface2 "cli" "terminal-stdout"
  else iface2 "cli" "terminal-stderr"

/-- The resolved entry of `f` has the interface `i` and the result `t`. -/
def ResIsR (P : RPkg) (f : FnName) (i : Binary.IfaceName) (t : Option Binary.Ty) : Bool :=
  (P.1.lookup f).any fun x => x.1 == i && decide (x.2.result = t)

/-- **The resolved entries have the written-out result types.** -/
theorem cli2_resultsR : cli2L.all (fun f => ResIsR p2P f (cliIface f) (cliRes f)) = true := by
  decide +kernel

/-! ## Named types -/

/-- A `u64`. -/
def isU64 : Val → Bool
  | .u64 _ => true
  | _ => false

/-- A `record { u64, u32 }`. -/
def dtV : Val → Bool
  | .record [.u64 _, .u32 _] => true
  | _ => false

/-- A case of an enum of `k` cases. -/
def enumV (k : Nat) : Val → Bool
  | .variant i none => decide (i < k)
  | _ => false

/-- The number of cases of an enum definition. -/
def enumLen : Option (Binary.IfaceName × Binary.TyDefKind) → Option Nat
  | some (_, .enum cs) => some cs.length
  | _ => none

theorem tyOkR_enum {E : TyEnv} {n : Nat} {c : Binary.IfaceName} {r : Binary.TyRef} {k : Nat}
    (h : enumLen (findTy E c r) = some k) (v : Val) :
    tyOkR E (n + 1) c (.ref r) v = enumV k v := by
  cases hf : findTy E c r with
  | none => simp [hf, enumLen] at h
  | some x =>
    obtain ⟨j, kd⟩ := x
    cases kd <;> simp [hf, enumLen] at h
    subst h
    rw [tyOkR_ref hf]
    rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨i, _ | w⟩ <;> rfl

theorem duration_eq (n : Nat) (v : Val) :
    tyOkR p2P.2 (n + 2) (iface2 "clocks" "monotonic-clock") (refT "duration") v = isU64 v := by
  have h : findTy p2P.2 (iface2 "clocks" "monotonic-clock") ⟨.local, "duration"⟩ =
      some (iface2 "clocks" "monotonic-clock", .type (.prim .u64)) := by decide +kernel
  rw [tyOkR_ref h]
  cases v <;> rfl

theorem datetime_eq (n : Nat) (v : Val) :
    tyOkR p2P.2 (n + 2) (iface2 "clocks" "wall-clock") (refT "datetime") v = dtV v := by
  have h : findTy p2P.2 (iface2 "clocks" "wall-clock") ⟨.local, "datetime"⟩ =
      some (iface2 "clocks" "wall-clock",
        .record [⟨"seconds", .prim .u64, none⟩, ⟨"nanoseconds", .prim .u32, none⟩]) := by
    decide +kernel
  rw [tyOkR_ref h]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | vs | _ <;> try rfl
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩ <;> try rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · cases a <;> cases b <;> rfl

theorem datetime_fuel (v : Val) :
    tyOkR p2P.2 fuel (iface2 "clocks" "wall-clock") (refT "datetime") v = dtV v :=
  datetime_eq 30 v

theorem errorCode_eq (n : Nat) (v : Val) :
    tyOkR p2P.2 (n + 1) (iface2 "filesystem" "types") (refT "error-code") v = enumV 37 v :=
  tyOkR_enum (by decide +kernel) v

theorem descType_eq (n : Nat) (v : Val) :
    tyOkR p2P.2 (n + 1) (iface2 "filesystem" "types") (refT "descriptor-type") v = enumV 8 v :=
  tyOkR_enum (by decide +kernel) v

/-! ## Anonymous types -/

theorem all_charR {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (cs : List Val) :
    (tyOkR E (n + 1) c tStr (.record cs)) = P2.strOk (.record cs) := by
  simp only [tyOkR_prim, primOk_string]

theorem tyOkR_str {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (v : Val) :
    tyOkR E (n + 1) c tStr v = P2.strOk v := by
  simp only [tyOkR_prim, primOk_string]

theorem tyOkR_envE {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (v : Val) :
    tyOkR E (n + 2) c (.tuple [tStr, tStr]) v = P2.envEntryOk v := by
  cases v <;> try rfl
  rename_i vs
  rcases vs with _ | ⟨k, _ | ⟨w, _ | ⟨x, vs⟩⟩⟩ <;>
    simp [tyOkR_tuple, zipOk, P2.envEntryOk, tyOkR_str]

theorem tyOkR_envE_fun {E : TyEnv} {n : Nat} {c : Binary.IfaceName} :
    tyOkR E (n + 2) c (.tuple [tStr, tStr]) = P2.envEntryOk := funext tyOkR_envE

theorem tyOkR_str_fun {E : TyEnv} {n : Nat} {c : Binary.IfaceName} :
    tyOkR E (n + 1) c tStr = P2.strOk := funext tyOkR_str

theorem tyOkR_optStr {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (v : Val) :
    tyOkR E (n + 2) c (.option tStr) v = P2.optStrOk v := by
  rw [tyOkR_option]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | w⟩ <;>
    simp [optV, P2.optStrOk, tyOkR_str]

theorem tyOkR_optOwn {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (m : String) (v : Val) :
    tyOkR E (n + 2) c (.option (ownT m)) v = P2.optHandleOk v := by
  rw [tyOkR_option]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | w⟩ <;>
    try rfl
  cases w <;> rfl

theorem all_congr' {α : Type} {f g : α → Bool} (h : ∀ x, f x = g x) (l : List α) :
    l.all f = l.all g := by
  simp [funext h]

/-! ## Per function -/

theorem cli2X_sub : ∀ f ∈ cli2X, f ∈ cli2L := by decide +kernel

theorem resOkR_cli {f : FnName} (hf : f ∈ cli2L) {i : Binary.IfaceName} {s : Binary.Sig}
    (hl : p2P.1.lookup f = some (i, s)) (r : Option (List Val)) :
    resOkR p2P.2 i s r = resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r := by
  have h := List.all_eq_true.1 cli2_resultsR f hf
  simp only [ResIsR, hl, Option.any_some, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨rfl, hr⟩ := h
  rcases s with ⟨b, ps, t⟩
  simp only at hr
  subst hr
  rfl

/-- **On `cli2X` the hand-written check is the resolved result check.** -/
theorem cliOkH_eqR (f : FnName) (hf : f ∈ cli2X) (r : Option (List Val)) :
    P2.cliOkH f r = resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r := by
  simp only [cli2X, cli2E, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide only [P2.cliOkH, cliRes, cliIface, ite_true, ite_false]
  all_goals rw [resOkR_one, fuel_eq]
  all_goals rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals first
    | (simp only [duration_eq]; cases v <;> rfl)
    | (simp only [tyOkR_optStr]; done)
    | (simp only [tyOkR_optOwn]; done)
    | (cases v <;> rfl)
    | (cases v <;> simp [tyOkR_list, recV, tyOkR_envE_fun, tyOkR_str_fun])

/-- Every function of `cli2X` has an entry in the imported table. -/
theorem cli2X_found : ∀ f ∈ cli2X, (p2P.1.lookup f).isSome = true := by decide +kernel

end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.P2

open Silmaril.Wasi.Versions.WitImport in
/-- **The WIT-derived `cliOk` is the hand-written check.** -/
theorem cliOk_eq_hand : cliOk = cliOkH := by
  funext f r
  unfold cliOk
  by_cases hf : f ∈ cli2X
  · obtain ⟨⟨i, s⟩, hl⟩ := Option.isSome_iff_exists.1 (cli2X_found f hf)
    simp only [hf, ↓reduceIte, hl]
    rw [resOkR_cli (cli2X_sub f hf) hl, cliOkH_eqR f hf r]
  · simp only [hf, ↓reduceIte]

/-- **The WIT-derived `p2Ok` is the hand-written check.** -/
theorem p2Ok_eq_hand : p2Ok = p2OkH := by
  funext e
  cases e <;> simp only [p2Ok, p2OkH, cliOk_eq_hand]

/-- **The WIT-derived WASI 0.2 theory is the hand-written one.** -/
theorem p2Th_eq_hand (r : Reading) : p2Th r = p2ThH r := by
  simp only [p2Th, p2ThH, p2Ok_eq_hand]

end Silmaril.Wasi.Versions.P2

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/-- **On `cli2X` the (WIT-derived) `P2.cliOk` is the resolved result check.** -/
theorem cliOk_eqR (f : FnName) (hf : f ∈ cli2X) (r : Option (List Val)) :
    P2.cliOk f r = resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r := by
  rw [P2.cliOk_eq_hand]
  exact cliOkH_eqR f hf r

/-- The `cliOk` functions whose resolved-typed answers pass `P2.cliOk`. -/
def cli2C : List FnName :=
  cli2X ++ [P2.fdReadStream, P2.fdWriteStream, P2.fdAppendStream, P2.fdGetType]

/-- The `cliOk` functions whose `P2.cliOk` answers are resolved-typed (or traps). -/
def cli2S : List FnName := cli2X ++ [P2.cliExit, P2.wallNow, P2.wallRes]

theorem cli2C_sub : ∀ f ∈ cli2C, f ∈ cli2L := by decide +kernel
theorem cli2S_sub : ∀ f ∈ cli2S, f ∈ cli2L := by decide +kernel

theorem handleRes_witR (f : FnName) (hf : f = P2.fdReadStream ∨ f = P2.fdWriteStream ∨
    f = P2.fdAppendStream) (r : Option (List Val))
    (h : resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r = true) : P2.handleResOk r = true := by
  have hi : cliIface f = iface2 "filesystem" "types" := by
    rcases hf with rfl | rfl | rfl <;> decide +kernel
  have hr : ∃ m, cliRes f = some (.result (some (ownT m)) (some (refT "error-code"))) := by
    rcases hf with rfl | rfl | rfl
    exacts [⟨"input-stream", by decide +kernel⟩, ⟨"output-stream", by decide +kernel⟩,
      ⟨"output-stream", by decide +kernel⟩]
  obtain ⟨m, hr⟩ := hr
  rw [hi, hr, resOkR_one, fuel_eq] at h
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try exact absurd h Bool.false_ne_true
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
  all_goals try exact absurd h Bool.false_ne_true
  · cases e <;> first | rfl | exact absurd h Bool.false_ne_true
  · rfl

theorem getType_witR (r : Option (List Val))
    (h : resOkR p2P.2 (cliIface P2.fdGetType) ⟨false, [], cliRes P2.fdGetType⟩ r = true) :
    P2.cliOk P2.fdGetType r = true := by
  have hi : cliIface P2.fdGetType = iface2 "filesystem" "types" := by decide +kernel
  have hr : cliRes P2.fdGetType =
      some (.result (some (refT "descriptor-type")) (some (refT "error-code"))) := by decide +kernel
  rw [hi, hr, resOkR_one, fuel_eq] at h
  simp +decide only [P2.cliOk_eq_hand, P2.cliOkH, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try exact absurd h Bool.false_ne_true
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
  all_goals try exact absurd h Bool.false_ne_true
  · simp only [tyOkR_result, resV, optOk, descType_eq] at h
    rcases e with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨j, _ | x⟩
    all_goals first | rfl | exact absurd h Bool.false_ne_true
  · rfl

/-- **Converse: a resolved-typed answer passes `P2.cliOk`** (the functions `cli2C`). -/
theorem witR_cliOk (f : FnName) (hf : f ∈ cli2C) (r : Option (List Val))
    (h : resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r = true) : P2.cliOk f r = true := by
  simp only [cli2C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | rfl | rfl | rfl | rfl
  · rw [cliOk_eqR f hf]; exact h
  all_goals first
    | exact getType_witR r h
    | (have := handleRes_witR _ (by simp) r h
       simpa +decide [P2.cliOk_eq_hand, P2.cliOkH] using this)

/-- **Sound direction: `P2.cliOk` answers are resolved-typed or traps** (the functions
`cli2S`). -/
theorem cliOk_witR (f : FnName) (hf : f ∈ cli2S) (r : Option (List Val))
    (h : P2.cliOk f r = true) :
    r.isNone = true ∨ resOkR p2P.2 (cliIface f) ⟨false, [], cliRes f⟩ r = true := by
  simp only [cli2S, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | rfl | rfl | rfl
  · exact .inr ((cliOk_eqR f hf r).symm.trans h)
  · simp +decide only [P2.cliOk_eq_hand, P2.cliOkH, ite_true] at h
    exact .inl h
  all_goals
    right
    simp +decide only [P2.cliOk_eq_hand, P2.cliOkH, cliRes, cliIface, ite_true, ite_false] at h ⊢
    rw [resOkR_one]
    rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try exact absurd h Bool.false_ne_true
    dsimp only at h ⊢
    rw [datetime_fuel]
    unfold P2.datetimeOk at h
    split at h
    · rfl
    · exact absurd h Bool.false_ne_true

/-! ## The theory -/

theorem rrestrict_snd (P : RPkg) (L : List FnName) : (rrestrict P L).2 = P.2 := rfl

theorem resOkR_entry {f : FnName} (hf : f ∈ cli2L) :
    ∃ i s, p2P.1.lookup f = some (i, s) ∧ i = cliIface f ∧ s.result = cliRes f := by
  have h := List.all_eq_true.1 cli2_resultsR f hf
  simp only [ResIsR] at h
  cases hl : p2P.1.lookup f with
  | none => simp [hl] at h
  | some x =>
    simp only [hl, Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨x.1, x.2, rfl, h.1, h.2⟩

theorem resOkR_result {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} {t : Option Binary.Ty}
    (h : s.result = t) (r : Option (List Val)) : resOkR E i s r = resOkR E i ⟨false, [], t⟩ r := by
  rcases s with ⟨b, ps, t'⟩
  simp only at h
  subst h
  rfl

/-- **`P2.p2Ok` implies the resolved WIT typing (traps admitted) for the functions `cli2S`.** -/
theorem p2Ok_witR (e : WEv) (h : P2.p2Ok e = true) : witRTrapOk (rrestrict p2P cli2S) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f ∈ cli2S
    · have hL := cli2S_sub f hf
      have ho : P2.ioOp f = .other := by simpa using List.all_eq_true.1 cli2_other f hL
      simp only [P2.p2Ok, ho, ite_true] at h
      obtain ⟨i, s, hl, rfl, hr⟩ := resOkR_entry hL
      simp only [witRTrapOk, lookup_rrestrict, rrestrict_snd, hf, ite_true, hl, resOkR_result hr]
      rcases cliOk_witR f hf r h with h | h <;> simp [h]
    · simp [witRTrapOk, lookup_rrestrict, hf]
  | _ => rfl

/-- **Converse for the theory**: on resolved-typed arguments, the resolved WIT typing implies
`P2.p2Ok` for the functions `cli2C`. -/
theorem witR_p2Ok (f : FnName) (hf : f ∈ cli2C) (a : List Val) (r : Option (List Val))
    (ha : ∀ i s, p2P.1.lookup f = some (i, s) → argsOkR p2P.2 i s a = true)
    (h : witROk (rrestrict p2P cli2C) (.imp f a r) = true) : P2.p2Ok (.imp f a r) = true := by
  have hL := cli2C_sub f hf
  have ho : P2.ioOp f = .other := by simpa using List.all_eq_true.1 cli2_other f hL
  obtain ⟨i, s, hl, rfl, hr⟩ := resOkR_entry hL
  simp only [witROk, lookup_rrestrict, rrestrict_snd, hf, ite_true, hl, ha _ _ hl, Bool.not_true,
    Bool.false_or, resOkR_result hr] at h
  simp only [P2.p2Ok, ho, ite_true]
  exact witR_cliOk f hf r h

/-! ## Refutations -/

/-- **`resolution` answering `true` is rejected once `duration` is resolved.** -/
theorem badRes_not_witR : witROk (rrestrict p2P cli2L) badRes = false := by decide +kernel

/-- **REFUTED converse for the wall clock and `exit`.** -/
theorem witR_not_p2Ok :
    (witROk (rrestrict p2P cli2L) badWall = true ∧ P2.p2Ok badWall = false) ∧
    (witROk (rrestrict p2P cli2L) exitReturns = true ∧ P2.p2Ok exitReturns = false) := by
  rw [P2.p2Ok_eq_hand]
  decide +kernel

/-- `read-via-stream` answering `error(true)`. -/
def badViaStream : WEv := .imp P2.fdReadStream [.u32 0, .u64 0] (some [errV (some (.bool true))])
/-- `get-type` answering `ok(case 99)`. -/
def badGetType : WEv := .imp P2.fdGetType [.u32 0] (some [okV (some (.variant 99 none))])

/-- **REFUTED sound direction for `read-via-stream` and `get-type`**: `P2.p2Ok` accepts
answers that the resolved typing rejects (on resolved-typed arguments). -/
theorem cliOk_not_witR :
    (P2.p2Ok badViaStream = true ∧ witROk (rrestrict p2P cli2L) badViaStream = false) ∧
    (P2.p2Ok badGetType = true ∧ witROk (rrestrict p2P cli2L) badGetType = false) := by
  rw [P2.p2Ok_eq_hand]
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
