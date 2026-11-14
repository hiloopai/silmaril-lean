module

public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Wasi.Versions.WitImport.RCli2.Thms

/-!
# The WASI 0.3 slice: the WIT-derived typing is the hand-written one

`P3.ok3` is defined from the resolved WIT import (`WitImport.p3P`, restricted to the five
functions `WitImport.p3E`). This module proves it equal to the hand-written check `P3.ok3H`
(**`P3.ok3_eq_hand`**, and so **`P3.typed3_eq_hand`**). It sits below `P3.Thms`, which
rewrites with it; its comparisons were in `WitImport.RP3`, which imports `P3.Thms` (moved here
as `Random.Wit` did for `wasi:random`).

* `p3_sigsR`: the resolved entries (interface and signature) of the seven slice functions;
  `mark_eq`: `mark` resolves to `u64`; `findTy_fsErr`, `fsErrCases_len`: the filesystem
  `error-code` is a variant of 37 cases.
* `ok3_stdoutR`, `ok3_stdinR`, `ok3_readViaR`, `ok3_nowR`, `ok3_waitR`: per function, the
  hand-written `ok3H` is the resolved result check, for every argument list;
  **`ok3H_eqR`**: on `p3E`, `ok3H` is the resolved check of the function's entry.
* **`P3.ok3_eq_hand : ok3 = ok3H`**, `P3.typed3_eq_hand : typed3 = typed3H`.
* **`ok3_eqR`**: the same statement as before the switch, now about the WIT-derived `P3.ok3`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasi.Versions.P3

/-- An interface of `wasi:<p>@0.3.2`. -/
abbrev iface3 (p i : String) : Binary.IfaceName := ⟨⟨"wasi", p, some "0.3.2"⟩, i⟩

/-! ## Signatures and named types of the 0.3 slice -/

/-- `future<result<_, error-code>>`. -/
abbrev tFutErr : Binary.Ty := .future (some (.result none (some (lref "error-code"))))

/-- The signature of `write-via-stream`. -/
abbrev sStdout : Binary.Sig := ⟨false, [("data", .stream (some (.prim .u8)))], some tFutErr⟩
/-- The signature of `stdin.read-via-stream`. -/
abbrev sStdin : Binary.Sig := ⟨false, [], some tStreamFut⟩
/-- The signature of `now`. -/
abbrev sNow : Binary.Sig := ⟨false, [], some (lref "mark")⟩
/-- The signature of `wait-for`. -/
abbrev sWait : Binary.Sig := ⟨true, [("how-long", lref "duration")], none⟩
/-- The signature of `[method]descriptor.read-via-stream`. -/
abbrev sReadVia : Binary.Sig :=
  ⟨false, [("self", .borrow ⟨.local, "descriptor"⟩), ("offset", lref "filesize")], some tStreamFut⟩
/-- The signature of `[method]descriptor.open-at`. -/
abbrev sOpenAt : Binary.Sig := ⟨true, [("self", .borrow ⟨.local, "descriptor"⟩),
  ("path-flags", lref "path-flags"), ("path", .prim .string), ("open-flags", lref "open-flags"),
  ("flags", lref "descriptor-flags")],
  some (.result (some (.own ⟨.local, "descriptor"⟩)) (some (lref "error-code")))⟩
/-- The signature of `get-directories`. -/
abbrev sDirs : Binary.Sig :=
  ⟨false, [], some (.list (.tuple [.own ⟨.local, "descriptor"⟩, .prim .string]))⟩

/-- **The resolved entries of the 0.3 slice**: interface and signature. -/
theorem p3_sigsR :
    p3P.1.lookup stdoutWrite3 = some (iface3 "cli" "stdout", sStdout) ∧
    p3P.1.lookup stdinRead3 = some (iface3 "cli" "stdin", sStdin) ∧
    p3P.1.lookup now3 = some (iface3 "clocks" "monotonic-clock", sNow) ∧
    p3P.1.lookup waitFor3 = some (iface3 "clocks" "monotonic-clock", sWait) ∧
    p3P.1.lookup readVia3 = some (iface3 "filesystem" "types", sReadVia) ∧
    p3P.1.lookup openAt3 = some (iface3 "filesystem" "types", sOpenAt) ∧
    p3P.1.lookup getDirs3 = some (iface3 "filesystem" "preopens", sDirs) := by
  decide +kernel

theorem findTy_mark : findTy p3P.2 (iface3 "clocks" "monotonic-clock") ⟨.local, "mark"⟩ =
    some (iface3 "clocks" "monotonic-clock", .type (.prim .u64)) := by decide +kernel

/-- The case labels of the filesystem `error-code`, without the payload of `other`. -/
def fsErrCases : List (Binary.Labeled (Option Binary.Ty)) :=
  match findTy p3P.2 (iface3 "filesystem" "types") ⟨.local, "error-code"⟩ with
  | some (_, .variant cs) => cs
  | _ => []

theorem findTy_fsErr : findTy p3P.2 (iface3 "filesystem" "types") ⟨.local, "error-code"⟩ =
    some (iface3 "filesystem" "types", .variant fsErrCases) := by decide +kernel

theorem fsErrCases_len : fsErrCases.length = 37 := by decide +kernel

theorem mark_eq (n : Nat) (v : Val) :
    tyOkR p3P.2 (n + 2) (iface3 "clocks" "monotonic-clock") (lref "mark") v = isU64 v := by
  rw [tyOkR_ref findTy_mark]
  cases v <;> rfl

/-- `error(true)` is not a resolved filesystem `error-code`. -/
theorem fsErr_bool (n : Nat) (b : Bool) :
    tyOkR p3P.2 (n + 1) (iface3 "filesystem" "types") (lref "error-code") (.bool b) = false := by
  rw [tyOkR_ref findTy_fsErr]
  rfl

/-! ## Per function -/

/-- A pair of handles. -/
def isPair : Val → Bool
  | .record [.u32 _, .u32 _] => true
  | _ => false

/-- A one-value answer `[.u32 _]`. -/
def u32Ans : Option (List Val) → Bool
  | some [v] => isU32 v
  | _ => false

/-- A one-value answer `[.record [.u32 _, .u32 _]]`. -/
def pairAns : Option (List Val) → Bool
  | some [v] => isPair v
  | _ => false

set_option linter.unusedTactic false in
theorem resOkR_u32 {E : TyEnv} {i : Binary.IfaceName} {b : Bool}
    {ps : List (String × Binary.Ty)} {t : Option Binary.Ty} (r : Option (List Val)) :
    resOkR E i ⟨b, ps, some (.future t)⟩ r = u32Ans r := by
  rw [resOkR_one, fuel_eq]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl

set_option linter.unusedTactic false in
theorem resOkR_pair {E : TyEnv} {i : Binary.IfaceName} {b : Bool}
    {ps : List (String × Binary.Ty)} (r : Option (List Val)) :
    resOkR E i ⟨b, ps, some tStreamFut⟩ r = pairAns r := by
  rw [resOkR_one, fuel_eq]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals (cases v <;> try rfl)
  all_goals (rename_i vs; rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> try rfl)
  all_goals (cases x <;> try rfl)
  all_goals (cases y <;> rfl)

theorem ok3_stdoutR (a : List Val) (r : Option (List Val)) :
    ok3H (.imp stdoutWrite3 a r) = resOkR p3P.2 (iface3 "cli" "stdout") sStdout r := by
  rw [resOkR_u32]
  simp +decide only [ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals (cases v <;> rfl)

theorem ok3_stdinR (a : List Val) (r : Option (List Val)) :
    ok3H (.imp stdinRead3 a r) = resOkR p3P.2 (iface3 "cli" "stdin") sStdin r := by
  rw [resOkR_pair]
  simp +decide only [ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals (cases v <;> try rfl)
  all_goals (rename_i vs; rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> try rfl)
  all_goals (cases x <;> try rfl)
  all_goals (cases y <;> rfl)

theorem ok3_readViaR (a : List Val) (r : Option (List Val)) :
    ok3H (.imp readVia3 a r) = resOkR p3P.2 (iface3 "filesystem" "types") sReadVia r := by
  rw [resOkR_pair]
  simp +decide only [ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  all_goals (cases v <;> try rfl)
  all_goals (rename_i vs; rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> try rfl)
  all_goals (cases x <;> try rfl)
  all_goals (cases y <;> rfl)

theorem ok3_nowR (a : List Val) (r : Option (List Val)) :
    ok3H (.imp now3 a r) = resOkR p3P.2 (iface3 "clocks" "monotonic-clock") sNow r := by
  rw [resOkR_one, fuel_eq]
  simp +decide only [ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try rfl
  · show _ = tyOkR p3P.2 (30 + 2) _ (lref "mark") v
    rw [mark_eq]
    cases v <;> rfl
  · cases v <;> rfl

theorem ok3_waitR (a : List Val) (r : Option (List Val)) :
    ok3H (.imp waitFor3 a r) = resOkR p3P.2 (iface3 "clocks" "monotonic-clock") sWait r := by
  simp +decide only [ok3H, ite_true, ite_false]
  rcases r with _ | ⟨_ | ⟨v, r⟩⟩ <;> rfl

/-- The hand-written check of `f` is the resolved result check of its entry. -/
def ExactRH (f : FnName) : Prop :=
  ∃ i s, p3P.1.lookup f = some (i, s) ∧ ∀ a r, ok3H (.imp f a r) = resOkR p3P.2 i s r

/-- **On `p3E` the hand-written 0.3 check is the resolved result check.** -/
theorem ok3H_eqR : ∀ f ∈ p3E, ExactRH f := by
  intro f hf
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := p3_sigsR
  simp only [p3E, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, _, h1, ok3_stdoutR⟩, ⟨_, _, h2, ok3_stdinR⟩, ⟨_, _, h3, ok3_nowR⟩,
    ⟨_, _, h4, ok3_waitR⟩, ⟨_, _, h5, ok3_readViaR⟩]


end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.P3

open Silmaril.Wasi.Versions.WitImport

/-- **The WIT-derived 0.3 typing is the hand-written check.** -/
theorem ok3_eq_hand : ok3 = ok3H := by
  funext e
  cases e with
  | imp f a r =>
    by_cases hf : f ∈ p3E
    · obtain ⟨i, s, hl, hok⟩ := ok3H_eqR f hf
      have hl' : (rrestrict p3P p3E).1.lookup f = some (i, s) := by
        simp only [lookup_rrestrict, hf, ↓reduceIte, hl]
      simp only [ok3, hl', hok a r]
    · have hl' : (rrestrict p3P p3E).1.lookup f = none := by
        simp only [lookup_rrestrict, hf, ↓reduceIte]
      simp only [ok3, hl']
  | _ => rfl

/-- **The WIT-derived 0.3 typing theory is the hand-written one.** -/
theorem typed3_eq_hand : typed3 = typed3H := by
  simp only [typed3, typed3H, ok3_eq_hand]

end Silmaril.Wasi.Versions.P3

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions.P3

/-- The (WIT-derived) check of `f` is the resolved result check of its entry. -/
def ExactR (f : FnName) : Prop :=
  ∃ i s, p3P.1.lookup f = some (i, s) ∧ ∀ a r, ok3 (.imp f a r) = resOkR p3P.2 i s r

/-- **On `p3E` the (WIT-derived) 0.3 check is the resolved result check.** -/
theorem ok3_eqR : ∀ f ∈ p3E, ExactR f := by
  intro f hf
  obtain ⟨i, s, hl, hok⟩ := ok3H_eqR f hf
  exact ⟨i, s, hl, fun a r => by rw [ok3_eq_hand]; exact hok a r⟩

end Silmaril.Wasi.Versions.WitImport
