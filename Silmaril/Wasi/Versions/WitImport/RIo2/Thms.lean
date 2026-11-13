module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Thms
public import Silmaril.Wasi.Versions.WitImport.RTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Io2.Thms

/-!
# The hand-written `wasi:io` 0.2 theory against the resolved WIT typing

`io2P` is the resolved `wasi:io@0.2.12` package (`Silmaril.Wasi.Versions.WitImport.RTables`);
`io2P_strip`: its table is `io2T`.

* **`streamErr_eq`**: resolved, the named type `stream-error` (`variant
  { last-operation-failed(own<error>), closed }`) is exactly `P2.streamErrOk`.
* **`ansOk_witR`**, **`ioTh_witR`**: every admissible answer of `P2.ansOk` (both readings,
  every state) has the *resolved* WIT type or is a trap. This strengthens `ioTh_wit`, which
  used the unresolved typing.
* **Equal on the stateless checks** (`ansOk_eq_witR`): for `subscribe`, `ready`, `block`, and
  for `flush`/`blocking-flush` and the loose `check-write` on a stream that is not closed, the
  hand-written check *is* the resolved result check.
* `badStreamErr_not_witR`: the answer `error(true)` of `wit_not_ioTh` is rejected once
  `stream-error` is resolved. **REFUTED converse** with the resolved typing
  (`witR_not_ioTh`): `write` of one byte with no permit answered `ok` is WIT-typed and rejected
  by `P2.ioTh` (it must trap). The converse fails for a behavioural reason (the permit), not a
  typing one.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/- `P2.streamErrOk` is read from the imported environment; the proofs below rewrite with
`streamErr_eq` instead of unfolding it. -/
attribute [local irreducible] P2.streamErrOk

/-- The resolved table of `wasi:io` is `io2T`. -/
theorem io2P_strip : strip io2P.1 = io2T := by decide +kernel

/-- `wasi:io/streams@0.2.12`. -/
def streamsI : Binary.IfaceName := ⟨⟨"wasi", "io", some "0.2.12"⟩, "streams"⟩
/-- `wasi:io/poll@0.2.12`. -/
def pollI : Binary.IfaceName := ⟨⟨"wasi", "io", some "0.2.12"⟩, "poll"⟩
/-- The local reference `stream-error`. -/
abbrev seT : Binary.Ty := .ref ⟨.local, "stream-error"⟩

theorem findTy_streamErr : findTy io2P.2 streamsI ⟨.local, "stream-error"⟩ =
    some (streamsI, .variant [⟨"last-operation-failed", some (.own ⟨.local, "error"⟩), none⟩,
      ⟨"closed", none, none⟩]) := by
  decide +kernel

/-- **Resolved, `stream-error` is `P2.streamErrOk`.** -/
theorem streamErr_eq (n : Nat) (v : Val) :
    tyOkR io2P.2 (n + 2) streamsI seT v = P2.streamErrOk v := by
  rw [P2.streamErrOk_eq_hand, tyOkR_ref findTy_streamErr]
  rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | w⟩
  all_goals try rfl
  · cases w <;> rfl

theorem fuel_eq : fuel = 29 + 3 := rfl

/-- `resOkR` of a one-value result. -/
theorem resOkR_one {E : TyEnv} {i : Binary.IfaceName} {b : Bool} {ps : List (String × Binary.Ty)}
    {t : Binary.Ty} (res : Option (List Val)) :
    resOkR E i ⟨b, ps, some t⟩ res =
      match res with
      | some [v] => tyOkR E fuel i t v
      | _ => false := by
  rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> rfl

/-- The resolved `result<_, stream-error>` is `P2.unitAns`. -/
theorem resOkR_unit {b : Bool} {ps : List (String × Binary.Ty)} (res : Option (List Val)) :
    resOkR io2P.2 streamsI ⟨b, ps, some (.result none (some seT))⟩ res = P2.unitAns res := by
  rw [P2.unitAns_eq_hand, resOkR_one, fuel_eq]
  rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try rfl
  · rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
    all_goals try rfl
    simp only [tyOkR_result, resV, optOk, streamErr_eq, P2.unitAnsH]
  · rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩ <;> rfl

/-- The resolved `result<u64, stream-error>` contains `P2.natAns`. -/
theorem resOkR_nat {b : Bool} {ps : List (String × Binary.Ty)} {bd : Nat}
    {res : Option (List Val)} (h : P2.natAns bd res = true) :
    resOkR io2P.2 streamsI ⟨b, ps, some (.result (some (.prim .u64)) (some seT))⟩ res = true := by
  rw [resOkR_one, fuel_eq]
  unfold P2.natAns at h
  split at h
  · simp [tyOkR_result, resV, optOk, tyOkR_prim, primOk]
  · simpa [tyOkR_result, resV, optOk, streamErr_eq] using h
  · exact absurd h Bool.false_ne_true

theorem all_u8R {E : TyEnv} {n : Nat} {c : Binary.IfaceName} :
    ∀ vs : List Val, vs.all P2.isU8 = true → vs.all (tyOkR E (n + 1) c (.prim .u8)) = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases v <;> simp_all [P2.isU8, tyOkR_prim, primOk, all_u8R vs h.2]

/-- The resolved `result<list<u8>, stream-error>` contains `P2.bytesAns`. -/
theorem resOkR_bytes {b : Bool} {ps : List (String × Binary.Ty)} {bd : Nat} {ne : Bool}
    {res : Option (List Val)} (h : P2.bytesAns bd ne res = true) :
    resOkR io2P.2 streamsI ⟨b, ps, some (.result (some (.list (.prim .u8))) (some seT))⟩ res =
      true := by
  rw [resOkR_one, fuel_eq]
  unfold P2.bytesAns at h
  split at h
  · simp only [Bool.and_eq_true] at h
    simp [tyOkR_result, resV, optOk, tyOkR_list, recV, all_u8R _ h.1.1]
  · simpa [tyOkR_result, resV, optOk, streamErr_eq] using h
  · exact absurd h Bool.false_ne_true

/-- The resolved `own<pollable>` is `P2.handleAns`. -/
theorem resOkR_handle {i : Binary.IfaceName} {b : Bool} {ps : List (String × Binary.Ty)}
    {x : Binary.TyRef} (res : Option (List Val)) :
    resOkR io2P.2 i ⟨b, ps, some (.own x)⟩ res = P2.handleAns res := by
  rw [P2.handleAns_eq_hand, resOkR_one, fuel_eq]
  rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try rfl
  all_goals cases v <;> rfl

theorem all_idxR {E : TyEnv} {n : Nat} {c : Binary.IfaceName} (k : Nat) :
    ∀ vs : List Val, vs.all (P2.idxOk k) = true → vs.all (tyOkR E (n + 1) c (.prim .u32)) = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases v <;> simp_all [P2.idxOk, tyOkR_prim, primOk, all_idxR k vs h.2]

theorem resOkR_poll {i : Binary.IfaceName} {b : Bool} {n : String} {y : Binary.Ty}
    {a : List Val} {res : Option (List Val)} (h : P2.pollAns a res = true) :
    (!argsOkR io2P.2 i ⟨b, [(n, .list y)], some (.list (.prim .u32))⟩ a || res.isNone ||
      resOkR io2P.2 i ⟨b, [(n, .list y)], some (.list (.prim .u32))⟩ res) = true := by
  rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩
  · simp [argsOkR, zipOk]
  · cases v
    case record ps =>
      simp only [P2.pollAns] at h
      by_cases hp : ps.isEmpty = true
      · simp only [hp, ite_true] at h
        simp [h]
      · simp only [hp, Bool.false_eq_true, ite_false] at h
        rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try simp at h
        cases v <;> simp at h
        rw [resOkR_one, fuel_eq]
        simp [tyOkR_list, recV, all_idxR _ _ (List.all_eq_true.2 h.2)]
    all_goals simp [argsOkR, zipOk, fuel_eq, tyOkR_list, recV]
  · simp [argsOkR, zipOk]

/-- The resolved `result<u64, stream-error>` is `P2.natAns (2 ^ 64)`. -/
theorem resOkR_nat_eq {b : Bool} {ps : List (String × Binary.Ty)} (res : Option (List Val)) :
    resOkR io2P.2 streamsI ⟨b, ps, some (.result (some (.prim .u64)) (some seT))⟩ res =
      P2.natAns (2 ^ 64) res := by
  rw [resOkR_one, fuel_eq]
  rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try rfl
  · rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
    all_goals try rfl
    · cases e <;> simp [tyOkR_result, resV, optOk, tyOkR_prim, primOk, P2.natAns,
        Nat.le_of_lt (BitVec.isLt _)]
    · simp only [tyOkR_result, resV, optOk, streamErr_eq, P2.natAns]
  · rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | i, _ | e⟩
    all_goals try rfl
    cases e <;> rfl

/-! ## Shapes -/

/-- The resolved result shape the class of a `wasi:io` function expects. -/
def ioShapeR : P2.IoOp → Binary.IfaceName × Binary.Sig → Bool
  | .checkWrite,
      (i, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .splice, (i, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bsplice, (i, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .skip, (i, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bskip, (i, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .write, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .writeZeroes, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bwf, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bwzf, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .flush, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bflush, (i, ⟨_, _, some (.result none (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .read,
      (i, ⟨_, _, some (.result (some (.list (.prim .u8))) (some (.ref ⟨.local, "stream-error"⟩)))⟩)
  | .bread,
      (i, ⟨_, _, some (.result (some (.list (.prim .u8))) (some (.ref ⟨.local, "stream-error"⟩)))⟩) =>
    i == streamsI
  | .oSubscribe, (_, ⟨_, _, some (.own _)⟩) | .iSubscribe, (_, ⟨_, _, some (.own _)⟩) => true
  | .ready, (_, ⟨_, _, some (.prim .bool)⟩) => true
  | .block, (_, ⟨_, _, none⟩) => true
  | .poll, (_, ⟨_, [(_, .list _)], some (.list (.prim .u32))⟩) => true
  | _, _ => false

/-- **Each classified function has a resolved signature of the expected shape.** -/
theorem io2_shapesR :
    io2L.all (fun f => (io2P.1.lookup f).any (ioShapeR (P2.ioOp f))) = true := by
  decide +kernel

theorem or_resR {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} {a : List Val}
    {res : Option (List Val)} (h : res.isNone = true ∨ resOkR E i s res = true) :
    (!argsOkR E i s a || res.isNone || resOkR E i s res) = true := by
  rcases h with h | h <;> simp [h]

theorem unit_orR {b : Bool} {ps : List (String × Binary.Ty)}
    {a : List Val} {res : Option (List Val)} (h : res.isNone = true ∨ P2.unitAns res = true) :
    (!argsOkR io2P.2 streamsI ⟨b, ps, some (.result none (some seT))⟩ a || res.isNone ||
      resOkR io2P.2 streamsI ⟨b, ps, some (.result none (some seT))⟩ res) = true :=
  h.elim (fun h => or_resR (.inl h)) (fun h => or_resR (.inr ((resOkR_unit _).trans h)))

/-- An admissible answer of a class is a trap or has the resolved result type of its shape. -/
theorem ansOk_shapeR (r : P2.Reading) (st : P2.IoSt) (o : P2.IoOp) (a : List Val)
    (res : Option (List Val)) (x : Binary.IfaceName × Binary.Sig) (hs : ioShapeR o x = true)
    (h : P2.ansOk r st o a res = true) :
    (!argsOkR io2P.2 x.1 x.2 a || res.isNone || resOkR io2P.2 x.1 x.2 res) = true := by
  unfold ioShapeR at hs
  split at hs
  all_goals try exact absurd hs Bool.false_ne_true
  all_goals (try (simp only [beq_iff_eq] at hs; subst hs))
  all_goals first
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_resR (.inr (resOkR_nat h.1.2)))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_resR (.inr (resOkR_nat h.2)))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact unit_orR (.inr h.2))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_resR (.inr (resOkR_bytes h.2)))
    | (simp only [P2.ansOk] at h; exact or_resR (.inr ((resOkR_handle _).trans h)))
    | (simp only [P2.ansOk] at h; exact resOkR_poll h)
    | (simp only [P2.ansOk] at h; exact unit_orR (ite_unit h))
    | (simp only [P2.ansOk] at h; exact unit_orR (bwf_unit h))
    | (simp only [P2.ansOk, P2.readyAns_eq_hand, P2.readyAnsH] at h; rw [resOkR_one, fuel_eq]
       split at h <;> simp_all [tyOkR_prim, primOk])
    | (simp only [P2.ansOk, P2.blockAns_eq_hand, P2.blockAnsH] at h
       split at h <;> simp_all [resOkR])

/-! ## The theory against the resolved typing -/

/-- **Every admissible `wasi:io` answer has the resolved WIT type or is a trap.** -/
theorem ansOk_witR (r : P2.Reading) (st : P2.IoSt) (f : FnName) (a : List Val)
    (res : Option (List Val)) (h : P2.ansOk r st (P2.ioOp f) a res = true) :
    witRTrapOk (rrestrict io2P io2L) (.imp f a res) = true := by
  by_cases hf : f ∈ io2L
  · have hall := List.all_eq_true.1 io2_shapesR f hf
    cases hl : io2P.1.lookup f with
    | none => simp [hl] at hall
    | some x =>
      simp only [hl, Option.any_some] at hall
      simp only [witRTrapOk, lookup_rrestrict, hf, ite_true, hl]
      exact ansOk_shapeR r st _ a res x hall h
  · simp [witRTrapOk, lookup_rrestrict, hf]

theorem ioStep_witR (r : P2.Reading) {q q' : P2.IoSt} {e : WEv}
    (h : P2.ioStep r q e = some q') : witRTrapOk (rrestrict io2P io2L) e = true := by
  cases e with
  | imp f a res =>
    simp only [P2.ioStep] at h
    split at h
    · exact ansOk_witR r q f a res ‹_›
    · cases h
  | _ => rfl

/-- **The `wasi:io` 0.2 theory implies the resolved WIT typing (traps admitted).** -/
theorem ioTh_witR (r : P2.Reading) {t : List WEv} (h : (P2.ioTh r).Accepts t) :
    (witRTrapTh (rrestrict io2P io2L)).Accepts t :=
  accepts_pointwise _ _ (fun _ _ _ hs => ioStep_witR r hs) h

/-! ## Equal where the check is stateless -/

/-- **On the stateless checks the hand-written answer check is the resolved result check.** -/
theorem ansOk_eq_witR (r : P2.Reading) (st : P2.IoSt) (a : List Val) (res : Option (List Val))
    (i : Binary.IfaceName) {b : Bool} {ps : List (String × Binary.Ty)} {x : Binary.TyRef} :
    P2.ansOk r st .oSubscribe a res = resOkR io2P.2 i ⟨b, ps, some (.own x)⟩ res ∧
    P2.ansOk r st .iSubscribe a res = resOkR io2P.2 i ⟨b, ps, some (.own x)⟩ res ∧
    P2.ansOk r st .ready a res = resOkR io2P.2 i ⟨b, ps, some (.prim .bool)⟩ res ∧
    P2.ansOk r st .block a res = resOkR io2P.2 i ⟨b, ps, none⟩ res ∧
    (st.closed (P2.selfOf a) = false →
      P2.ansOk r st .flush a res =
        resOkR io2P.2 streamsI ⟨b, ps, some (.result none (some seT))⟩ res ∧
      P2.ansOk r st .bflush a res =
        resOkR io2P.2 streamsI ⟨b, ps, some (.result none (some seT))⟩ res ∧
      P2.ansOk .loose st .checkWrite a res =
        resOkR io2P.2 streamsI ⟨b, ps, some (.result (some (.prim .u64)) (some seT))⟩ res) := by
  refine ⟨(resOkR_handle res).symm, (resOkR_handle res).symm, ?_, ?_, fun hc => ?_⟩
  · show P2.readyAns res = _
    rw [P2.readyAns_eq_hand, resOkR_one, fuel_eq]
    rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try rfl
    all_goals cases v <;> rfl
  · show P2.blockAns res = _
    rw [P2.blockAns_eq_hand]
    rcases res with _ | ⟨_ | ⟨v, res⟩⟩ <;> rfl
  · simp [P2.ansOk, P2.stickyOk, hc, resOkR_unit, resOkR_nat_eq]

/-! ## Refutations -/

/-- **`error(true)` is not a resolved `stream-error`.** -/
theorem badStreamErr_not_witR : witROk (rrestrict io2P io2L) badStreamErr = false := by
  decide +kernel

/-- A `write` of one byte with no permit, answered `ok`. -/
def writeOkNoPermit : WEv := .imp P2.osWrite [.u32 0, bytesV [1]] (some [okV none])

/-- **REFUTED converse with the resolved typing**: the answer is resolved-WIT-typed and
`P2.ioTh` rejects it (beyond the permit the write must trap). -/
theorem witR_not_ioTh :
    witROk (rrestrict io2P io2L) writeOkNoPermit = true ∧
      ¬ (P2.ioTh .loose).Accepts [writeOkNoPermit] ∧
      ¬ (P2.ioTh .strict).Accepts [writeOkNoPermit] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.WitImport
