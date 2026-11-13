module

public import Silmaril.Wasi.Versions.WitImport.Io2.Thms
public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasm.Resource.Protocol.Thms

/-!
# The hand-written `wasi:cli`, `wasi:clocks` and `wasi:filesystem` 0.2 typing against the
imported signatures

`p2W = cli2T ++ clocks2T ++ fs2T`. `cli2L`: the nineteen functions `P2.cliOkH` constrains that
have a signature (the resource drop `[resource-drop]output-stream` has none). `cliRes f`: the
WIT result type of `f`, written out; `cli2_results` checks it against the imported table.

* **`p2Ok_wit`**: `P2.p2OkH e` implies `witTrapOk (restrict p2W cli2L) e` (a trap is admitted
  for `exit`, which `P2.cliOkH` requires to trap).
* **Equal on named-type-free results** (`cliOk_eq`): for the eleven functions of `cli2E`
  (`get-environment`, `get-arguments`, `initial-cwd`, `get-std{in,out,err}`,
  `get-terminal-std{in,out,err}`, `subscribe-{instant,duration}`), `P2.cliOkH f r` *is*
  `resOk s r` for the imported signature `s`; `p2Ok_eq_wit`: on WIT-typed arguments the
  hand-written check and the imported WIT check agree.
* **REFUTED converse** for the named results (`wit_not_p2Ok`): `resolution` answering
  `true` (`duration` is a named `u64`), `wall-clock.now` answering a `datetime` with
  `nanoseconds = 10^9`, and `exit` returning: WIT-typed, rejected by `P2.p2OkH`.
* `fsOk` (the base WASI theory's `fsTyped`): **`fsOk_wit`**: implies the WIT typing for `open-at` and
  `write`; **REFUTED** for `get-directories` (the preopen name is not checked, as in 0.3) and for
  `read` (`fsOk` does not check that the bytes are `u8`): `fsOk_not_wit`.
* `clockTh`: **`clockTh_wit`**: monotonic `now` answers are WIT-typed (`instant` is named, any
  single value is typed; the theory requires a `u64`).
* **`p2Th_wit`**: every trace of the hand-written 0.2 theory `P2.p2ThH r` is accepted by the
  WIT typing theories (traps admitted) of `wasi:io`, of the `cliOk` functions, of the clock and
  of the two typed filesystem functions.

Since the switch (`wf-p2-switch`), `P2.cliOk` is defined from the resolved WIT import and the
hand-written check is `P2.cliOkH`; this module compares the hand-written variants (`P2.cliOkH`,
`P2.p2OkH`, `P2.p2ThH`). `WitImport.RCli2` proves them equal to the switched definitions
(`P2.cliOk_eq_hand`, `P2.p2Ok_eq_hand`, `P2.p2Th_eq_hand`). `cli2E` now lives in
`Silmaril.Wasi.Versions.P2.World.Defs`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/-! ## Tables and expected results -/

/-- The 0.2.12 `cli`, `clocks` and `filesystem` tables. -/
def p2W : Table := cli2T ++ clocks2T ++ fs2T

/-- A local named type. -/
abbrev refT (n : String) : Binary.Ty := .ref ⟨.local, n⟩
/-- A local `own`. -/
abbrev ownT (n : String) : Binary.Ty := .own ⟨.local, n⟩
/-- `string`. -/
abbrev tStr : Binary.Ty := .prim .string

/-- The functions `P2.cliOkH` constrains that have a WIT signature. -/
def cli2L : List FnName :=
  [P2.getEnv, P2.getArgs, P2.initialCwd, P2.cliExit, P2.getStdin, getStdout, P2.getStderr,
   P2.getTermStdin, P2.getTermStdout, P2.getTermStderr, P2.monoRes, P2.monoSubInstant,
   P2.monoSubDuration, P2.wallNow, P2.wallRes, P2.fdReadStream, P2.fdWriteStream,
   P2.fdAppendStream, P2.fdGetType]

/-- The WIT result types of `cli2L`, written out. -/
def cliRes (f : FnName) : Option Binary.Ty :=
  if f = P2.getEnv then some (.list (.tuple [tStr, tStr]))
  else if f = P2.getArgs then some (.list tStr)
  else if f = P2.initialCwd then some (.option tStr)
  else if f = P2.getStdin then some (ownT "input-stream")
  else if f = getStdout ∨ f = P2.getStderr then some (ownT "output-stream")
  else if f = P2.getTermStdin then some (.option (ownT "terminal-input"))
  else if f = P2.getTermStdout ∨ f = P2.getTermStderr then some (.option (ownT "terminal-output"))
  else if f = P2.monoRes then some (refT "duration")
  else if f = P2.monoSubInstant ∨ f = P2.monoSubDuration then some (ownT "pollable")
  else if f = P2.wallNow ∨ f = P2.wallRes then some (refT "datetime")
  else if f = P2.fdReadStream then some (.result (some (ownT "input-stream")) (some (refT "error-code")))
  else if f = P2.fdWriteStream ∨ f = P2.fdAppendStream then
    some (.result (some (ownT "output-stream")) (some (refT "error-code")))
  else if f = P2.fdGetType then
    some (.result (some (refT "descriptor-type")) (some (refT "error-code")))
  else none

/-- The result type of `f` in `T` is `t`. -/
def ResIs (T : Table) (f : FnName) (t : Option Binary.Ty) : Bool :=
  (T.lookup f).any fun s => decide (s.result = t)

/-- **The written-out result types are the imported ones.** -/
theorem cli2_results : cli2L.all (fun f => ResIs p2W f (cliRes f)) = true := by decide +kernel

/-- `P2.p2OkH` applies `P2.cliOkH` to every function of `cli2L`. -/
theorem cli2_other : cli2L.all (fun f => P2.ioOp f == .other) = true := by decide +kernel

/-! ## Generic lemmas -/

theorem resOk_congr {s : Binary.Sig} {t : Option Binary.Ty} (h : s.result = t)
    (r : Option (List Val)) : resOk s r = resOk ⟨false, [], t⟩ r := by
  cases s; cases h; rfl

theorem witTrapOk_of {T : Table} {L : List FnName} {f : FnName} {t : Option Binary.Ty}
    (hf : f ∈ L) (hT : ResIs T f t = true) {a : List Val} {r : Option (List Val)}
    (h : r.isNone = true ∨ resOk ⟨false, [], t⟩ r = true) :
    witTrapOk (restrict T L) (.imp f a r) = true := by
  unfold ResIs at hT
  cases hl : T.lookup f with
  | none => simp [hl] at hT
  | some s =>
    simp only [hl, Option.any_some, decide_eq_true_eq] at hT
    simp only [witTrapOk, lookup_restrict, hf, ite_true, hl, resOk_congr hT]
    rcases h with h | h <;> simp [h]

theorem witOk_of {T : Table} {L : List FnName} {f : FnName} {t : Option Binary.Ty}
    (hf : f ∈ L) (hT : ResIs T f t = true) {a : List Val} {r : Option (List Val)}
    (h : resOk ⟨false, [], t⟩ r = true) : witOk (restrict T L) (.imp f a r) = true := by
  unfold ResIs at hT
  cases hl : T.lookup f with
  | none => simp [hl] at hT
  | some s =>
    simp only [hl, Option.any_some, decide_eq_true_eq] at hT
    simp [witOk, lookup_restrict, hf, hl, resOk_congr hT, h]

/-! ## Value types -/

theorem tyAll_eq (t : Binary.Ty) : ∀ vs : List Val, tyAll t vs = vs.all (tyOk t)
  | [] => rfl
  | v :: vs => by simp [tyAll, tyAll_eq t vs]

theorem primOk_string (v : Val) : primOk .string v = P2.strOk v := by
  cases v <;> simp only [primOk, P2.strOk]
  congr 1

theorem tyOk_string (v : Val) : tyOk tStr v = P2.strOk v := by
  simp only [tyOk, primOk_string]

theorem tyOk_env (v : Val) : tyOk (.tuple [tStr, tStr]) v = P2.envEntryOk v := by
  cases v <;> try rfl
  rename_i vs
  rcases vs with _ | ⟨k, _ | ⟨w, _ | ⟨x, vs⟩⟩⟩ <;>
    simp [tyOk, tysOk, P2.envEntryOk, primOk_string]

theorem tyOk_env_fun : tyOk (.tuple [tStr, tStr]) = P2.envEntryOk := funext tyOk_env

theorem tyOk_string_fun : tyOk tStr = P2.strOk := funext tyOk_string

theorem tyOk_optStr (v : Val) : tyOk (.option tStr) v = P2.optStrOk v := by
  cases v with
  | variant c p =>
    rcases c with _ | _ | c <;> rcases p with _ | w <;> simp [tyOk, P2.optStrOk, primOk_string]
  | _ => rfl

theorem tyOk_optOwn (n : String) (v : Val) : tyOk (.option (ownT n)) v = P2.optHandleOk v := by
  cases v with
  | variant c p =>
    rcases c with _ | _ | c <;> rcases p with _ | w <;> try rfl
    cases w <;> rfl
  | _ => rfl

/-! ## `wasi:cli`, `wasi:clocks`, `wasi:filesystem` streams -/

theorem cliOk_res (f : FnName) (hf : f ∈ cli2L) (r : Option (List Val))
    (h : P2.cliOkH f r = true) : r.isNone = true ∨ resOk ⟨false, [], cliRes f⟩ r = true := by
  simp only [cli2L, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide only [P2.cliOkH, cliRes, ite_true, ite_false] at h ⊢
  all_goals first
    | exact .inl h
    | (right; split at h <;> simp_all [resOk, tyOk, tyOk_env, tyOk_optStr, tyOk_optOwn, tyOpt,
        tyAll_eq, primOk_string])
    | (right; unfold P2.handleResOk at h; split at h <;> simp_all [resOk, tyOk, tyOpt])

/-- **`P2.p2OkH` implies the imported WIT typing (traps admitted) for the `cliOk` functions.** -/
theorem p2Ok_wit (e : WEv) (h : P2.p2OkH e = true) : witTrapOk (restrict p2W cli2L) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f ∈ cli2L
    · have ho : P2.ioOp f = .other := by simpa using List.all_eq_true.1 cli2_other f hf
      simp only [P2.p2OkH, ho, ite_true] at h
      exact witTrapOk_of hf (List.all_eq_true.1 cli2_results f hf) (cliOk_res f hf r h)
    · exact witTrapOk_restrict_not hf a r
  | _ => rfl

theorem cli2E_sub : ∀ f ∈ cli2E, f ∈ cli2L := by decide +kernel

/-- **On named-type-free results the hand-written check is the WIT result check.** -/
theorem cliOk_eq (f : FnName) (hf : f ∈ cli2E) (r : Option (List Val)) :
    P2.cliOkH f r = resOk ⟨false, [], cliRes f⟩ r := by
  simp only [cli2E, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide only [P2.cliOkH, cliRes, ite_true, ite_false]
  all_goals rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals first
    | (simp [resOk, tyOk_optStr, tyOk_optOwn]; done)
    | (cases v <;> simp [resOk, tyOk, tyAll_eq, tyOk_env_fun, tyOk_string_fun])

/-- **On WIT-typed arguments, `P2.p2OkH` and the imported WIT typing agree** (the functions
`cli2E`). -/
theorem p2Ok_eq_wit (f : FnName) (hf : f ∈ cli2E) (s : Binary.Sig) (hs : p2W.lookup f = some s)
    (a : List Val) (ha : argsOk s a = true) (r : Option (List Val)) :
    P2.p2OkH (.imp f a r) = witOk (restrict p2W cli2E) (.imp f a r) := by
  have hL := cli2E_sub f hf
  have ho : P2.ioOp f = .other := by simpa using List.all_eq_true.1 cli2_other f hL
  have hr := List.all_eq_true.1 cli2_results f hL
  simp only [ResIs, hs, Option.any_some, decide_eq_true_eq] at hr
  simp [P2.p2OkH, ho, witOk, lookup_restrict, hf, hs, ha, resOk_congr hr, cliOk_eq f hf]

/-- `resolution` answering `true` (`duration` is a named `u64`). -/
def badRes : WEv := .imp P2.monoRes [] (some [.bool true])
/-- `wall-clock.now` answering `nanoseconds = 10^9`. -/
def badWall : WEv := .imp P2.wallNow [] (some [.record [.u64 0, .u32 1000000000]])
/-- `exit(ok)` returning. -/
def exitReturns : WEv := .imp P2.cliExit [okV none] (some [])

/-- **REFUTED converse**: answers the imported WIT typing accepts and `P2.p2OkH` rejects. -/
theorem wit_not_p2Ok :
    (witOk (restrict p2W cli2L) badRes = true ∧ P2.p2OkH badRes = false) ∧
    (witOk (restrict p2W cli2L) badWall = true ∧ P2.p2OkH badWall = false) ∧
    (witOk (restrict p2W cli2L) exitReturns = true ∧ P2.p2OkH exitReturns = false) := by
  decide +kernel

/-! ## the base WASI theory's filesystem typing and the clock -/

/-- The imported results of `open-at` and `write`, and of `now`. -/
theorem fs2_results :
    ResIs fs2T openAt (some (.result (some (ownT "descriptor")) (some (refT "error-code")))) ∧
    ResIs fs2T fdWrite (some (.result (some (refT "filesize")) (some (refT "error-code")))) ∧
    ResIs clocks2T clockNow (some (refT "instant")) := by
  decide +kernel

/-- **`fsOk` implies the imported WIT typing for `open-at` and `write`.** -/
theorem fsOk_wit (e : WEv) (h : fsOk e = true) : witOk (restrict fs2T [openAt, fdWrite]) e = true := by
  cases e with
  | imp f a r =>
    by_cases ho : f = openAt
    · subst ho
      refine witOk_of (by simp) fs2_results.1 ?_
      simp +decide only [fsOk, ite_true, ite_false] at h
      split at h <;> simp_all [resOk, tyOk, tyOpt]
    by_cases hw : f = fdWrite
    · subst hw
      refine witOk_of (by simp) fs2_results.2.1 ?_
      simp +decide only [fsOk, ite_true, ite_false] at h
      split at h <;> simp_all [resOk, tyOk, tyOpt]
    simp [witOk, lookup_restrict, ho, hw]
  | _ => rfl

/-- `get-directories` with a preopen name that is not a string. -/
def badDirs2 : WEv := .imp getDirs [] (some [.record [.record [.u32 0, .u64 0]]])
/-- `read` answering a byte list holding a `bool`. -/
def badRead2 : WEv :=
  .imp fdRead [.u32 0, .u64 1, .u64 0] (some [okV (some (.record [.record [.bool true], .bool true]))])

/-- **REFUTED for `get-directories` and `read`**: `fsOk` accepts answers that are not
WIT-typed. -/
theorem fsOk_not_wit :
    (fsOk badDirs2 = true ∧ witOk (restrict fs2T [getDirs]) badDirs2 = false) ∧
    (fsOk badRead2 = true ∧ witOk (restrict fs2T [fdRead]) badRead2 = false) := by
  decide +kernel

theorem clockStep_wit {q q' : Option (BitVec 64)} {e : WEv} (h : clockStep q e = some q') :
    witOk (restrict clocks2T [clockNow]) e = true := by
  cases e with
  | imp f a r =>
    by_cases hf : f = clockNow
    · subst hf
      refine witOk_of (by simp) fs2_results.2.2 ?_
      simp only [clockStep, ite_true, nowStep] at h
      split at h <;> simp_all [resOk, tyOk]
    · simp [witOk, lookup_restrict, hf]
  | _ => rfl

/-! ## The 0.2 theory -/

theorem pointwise_mono {ok ok' : WEv → Bool} (h : ∀ e, ok e = true → ok' e = true)
    {t : List WEv} (ht : (pointwise ok).Accepts t) : (pointwise ok').Accepts t := by
  refine accepts_pointwise _ _ (fun q e q' hs => h e ?_) ht
  simp only [pointwise] at hs
  split at hs
  · assumption
  · cases hs

/-- **The hand-written WASI 0.2 theory implies the imported WIT typing** of `wasi:io`, of the
`cliOk` functions (traps admitted), of `now`, `open-at` and `write`. -/
theorem p2Th_wit (r : P2.Reading) {t : List WEv} (h : (P2.p2ThH r).Accepts t) :
    (witTrapTh (restrict io2T io2L)).Accepts t ∧ (witTrapTh (restrict p2W cli2L)).Accepts t ∧
    (witTh (restrict clocks2T [clockNow])).Accepts t ∧
    (witTh (restrict fs2T [openAt, fdWrite])).Accepts t := by
  obtain ⟨hio, h⟩ := (Protocol.accepts_prod_iff _ _ _).1 h
  obtain ⟨hcl, h⟩ := (Protocol.accepts_prod_iff _ _ _).1 h
  obtain ⟨hp2, hfs⟩ := (Protocol.accepts_prod_iff _ _ _).1 h
  refine ⟨ioTh_wit r hio, pointwise_mono p2Ok_wit hp2, ?_, pointwise_mono fsOk_wit hfs⟩
  exact accepts_pointwise _ _ (fun _ _ _ hs => clockStep_wit hs) hcl

end Silmaril.Wasi.Versions.WitImport
