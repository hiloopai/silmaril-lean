module

public import Silmaril.Wasi.Versions.WitImport.Names.Thms
public import Silmaril.Wasi.Versions.WitImport.RFree.Thms

/-!
# `wasi:random`: the WIT-derived typing is the hand-written one

`Random.ok2` and `Random.ok3` are defined from the imported WIT (the resolved typing of
`rand2P`/`rand3P` plus the length conditions `len2`/`len3`). This module proves them equal to
the hand-written checks `Random.ok2H`/`Random.ok3H` (**`ok2_eq_hand`**, **`ok3_eq_hand`**):

* `rand3_sigs`, `rand2_sigs`: the imported signatures; `rand_sig_types`: 0.2 and 0.3 have the
  same types (the parameter is renamed `len` → `max-len`, the seed function `insecure-seed` →
  `get-insecure-seed`);
* `ok3H_eq`, `ok2H_eq`: the hand-written checks are the unresolved WIT typing plus the length
  condition;
* `rand3P_free`, `rand2P_free`: `wasi:random` has no named types, so the resolved typing is the
  unresolved one (`witROk_free`), and `rand3P_strip`, `rand2P_strip`: the resolved tables strip
  to the unresolved ones.

`ok3_eq`, `ok2_eq` keep their statements from before the switch (`Random.ok3 e = witOk rand3T e
&& len3 e`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component.Binary (PrimValType)
open Silmaril.Wasi.Versions.Random

/-! ## Signatures of `wasi:random` -/

/-- `u64`. -/
abbrev tU64 : Binary.Ty := .prim .u64
/-- `list<u8>`. -/
abbrev tBytes : Binary.Ty := .list (.prim .u8)

/-- **The imported `wasi:random` 0.3 signatures.** -/
theorem rand3_sigs :
    rand3T.lookup randBytes3 = some ⟨false, [("max-len", tU64)], some tBytes⟩ ∧
    rand3T.lookup insBytes3 = some ⟨false, [("max-len", tU64)], some tBytes⟩ ∧
    rand3T.lookup randU64_3 = some ⟨false, [], some tU64⟩ ∧
    rand3T.lookup insU64_3 = some ⟨false, [], some tU64⟩ ∧
    rand3T.lookup insSeed3 = some ⟨false, [], some (.tuple [tU64, tU64])⟩ := by
  decide +kernel

/-- **The imported `wasi:random` 0.2 signatures.** -/
theorem rand2_sigs :
    rand2T.lookup randBytes2 = some ⟨false, [("len", tU64)], some tBytes⟩ ∧
    rand2T.lookup insBytes2 = some ⟨false, [("len", tU64)], some tBytes⟩ ∧
    rand2T.lookup randU64_2 = some ⟨false, [], some tU64⟩ ∧
    rand2T.lookup insU64_2 = some ⟨false, [], some tU64⟩ ∧
    rand2T.lookup insSeed2 = some ⟨false, [], some (.tuple [tU64, tU64])⟩ := by
  decide +kernel

/-- 0.2 and 0.3 `wasi:random` have the same parameter and result types, function by function. -/
theorem rand_sig_types : rand2T.map (sigTypes ·.2) = rand3T.map (sigTypes ·.2) := by decide +kernel

/-! ## Typing of `wasi:random` -/

theorem resOk_bytes (n : String) (r : Option (List Val)) :
    resOk ⟨false, [(n, tU64)], some tBytes⟩ r = bytesAns (fun _ => true) r := by
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> simp [resOk, bytesAns, tyOk_bytes]

theorem resOk_u64 (r : Option (List Val)) : resOk ⟨false, [], some tU64⟩ r = u64Ans r := by
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try cases v
  all_goals simp [resOk, u64Ans, tyOk, primOk]

set_option linter.unusedTactic false in
theorem resOk_seed (r : Option (List Val)) :
    resOk ⟨false, [], some (.tuple [tU64, tU64])⟩ r = seedAns r := by
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> try cases v
  all_goals try simp [resOk, seedAns, tyOk]
  rename_i vs
  rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, vs⟩⟩⟩ <;> try cases x
  all_goals try cases y
  all_goals simp [tysOk, tyOk, primOk]

/-- A byte call is WIT-typed and has the right length. -/
theorem bytesM_split (P : Nat → Nat → Bool) (n : String) (a : List Val) (r : Option (List Val)) :
    bytesM P a r = ((!argsOk ⟨false, [(n, tU64)], some tBytes⟩ a ||
      resOk ⟨false, [(n, tU64)], some tBytes⟩ r) && lenM P a r) := by
  rw [argsOk_u64, resOk_bytes]
  rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩ <;> try cases v
  all_goals try rfl
  rcases r with _ | ⟨_ | ⟨v, _ | ⟨w, r⟩⟩⟩ <;> simp [bytesM, bytesAns, lenM]

theorem nullM_split (ans : Option (List Val) → Bool) (res : Option Binary.Ty)
    (h : ∀ r, resOk ⟨false, [], res⟩ r = ans r) (a : List Val) (r : Option (List Val)) :
    nullM ans a r = (!argsOk ⟨false, [], res⟩ a || resOk ⟨false, [], res⟩ r) := by
  rw [argsOk_nil, h]; cases a <;> rfl

/-- **The hand-written `Random.ok3H` is the imported WIT typing plus the short-read condition.** -/
theorem ok3H_eq (e : WEv) : Random.ok3H e = (witOk rand3T e && len3 e) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rand3_sigs
  cases e with
  | imp f a r =>
    by_cases hb : f = randBytes3 ∨ f = insBytes3
    · rcases hb with rfl | rfl
      · simp +decide [Random.ok3H, witOk, len3, h1, bytesM_split shortOk "max-len"]
      · simp +decide [Random.ok3H, witOk, len3, h2, bytesM_split shortOk "max-len"]
    by_cases hu : f = randU64_3 ∨ f = insU64_3
    · rcases hu with rfl | rfl
      · simp +decide [Random.ok3H, witOk, len3, h3, nullM_split u64Ans _ resOk_u64]
      · simp +decide [Random.ok3H, witOk, len3, h4, nullM_split u64Ans _ resOk_u64]
    by_cases hs : f = insSeed3
    · subst hs; simp +decide [Random.ok3H, witOk, len3, h5, nullM_split seedAns _ resOk_seed]
    have hn : f ∉ names rand3T := by
      rw [rand3_names]; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    simp only [Random.ok3H, witOk, len3, lookup_none hn, hb, hu, hs, ite_false, Bool.and_self]
  | _ => rfl

/-- **The hand-written `Random.ok2H` is the imported WIT typing plus the exact-length condition.** -/
theorem ok2H_eq (e : WEv) : Random.ok2H e = (witOk rand2T e && len2 e) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rand2_sigs
  cases e with
  | imp f a r =>
    by_cases hb : f = randBytes2 ∨ f = insBytes2
    · rcases hb with rfl | rfl
      · simp +decide [Random.ok2H, witOk, len2, h1, bytesM_split exactOk "len"]
      · simp +decide [Random.ok2H, witOk, len2, h2, bytesM_split exactOk "len"]
    by_cases hu : f = randU64_2 ∨ f = insU64_2
    · rcases hu with rfl | rfl
      · simp +decide [Random.ok2H, witOk, len2, h3, nullM_split u64Ans _ resOk_u64]
      · simp +decide [Random.ok2H, witOk, len2, h4, nullM_split u64Ans _ resOk_u64]
    by_cases hs : f = insSeed2
    · subst hs; simp +decide [Random.ok2H, witOk, len2, h5, nullM_split seedAns _ resOk_seed]
    have hn : f ∉ names rand2T := by
      rw [rand2_names]; simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
    simp only [Random.ok2H, witOk, len2, lookup_none hn, hb, hu, hs, ite_false, Bool.and_self]
  | _ => rfl

/-! ## The resolved packages -/

theorem rand3P_strip : strip rand3P.1 = rand3T := by decide +kernel
theorem rand2P_strip : strip rand2P.1 = rand2T := by decide +kernel

theorem rand3P_free : PkgFree rand3P = true := by decide +kernel
theorem rand2P_free : PkgFree rand2P = true := by decide +kernel

/-- **`Random.ok3` (from the WIT) is the unresolved WIT typing plus the short-read condition.** -/
theorem ok3_eq (e : WEv) : Random.ok3 e = (witOk rand3T e && len3 e) := by
  rw [Random.ok3, witROk_free rand3P_free, rand3P_strip]

/-- **`Random.ok2` (from the WIT) is the unresolved WIT typing plus the exact-length condition.** -/
theorem ok2_eq (e : WEv) : Random.ok2 e = (witOk rand2T e && len2 e) := by
  rw [Random.ok2, witROk_free rand2P_free, rand2P_strip]

end Silmaril.Wasi.Versions.WitImport

namespace Silmaril.Wasi.Versions.Random

/-- **The WIT-derived 0.3 typing is the hand-written check.** -/
theorem ok3_eq_hand : ok3 = ok3H :=
  funext fun e => (WitImport.ok3_eq e).trans (WitImport.ok3H_eq e).symm

/-- **The WIT-derived 0.2 typing is the hand-written check.** -/
theorem ok2_eq_hand : ok2 = ok2H :=
  funext fun e => (WitImport.ok2_eq e).trans (WitImport.ok2H_eq e).symm

end Silmaril.Wasi.Versions.Random
