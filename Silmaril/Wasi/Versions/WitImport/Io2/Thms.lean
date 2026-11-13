module

public import Silmaril.Wasi.Versions.WitImport.Typing.Defs
public import Silmaril.Wasi.Versions.WitImport.Names.Thms
public import Silmaril.Wasi.Versions.P2.Io.Defs
public import Silmaril.Wasi.Theory.Thms

/-!
# The hand-written `wasi:io` 0.2 theory against the imported signatures

`io2L`: the eighteen `wasi:io` 0.2 functions `P2.ioOp` classifies (every function of the
imported `io2T` except `error.to-debug-string`, which `P2.ioTh` leaves unconstrained).

* `io2_shapes`: the imported signature of each of them has the result shape its class expects
  (`ioShape`): `result<u64, stream-error>` for `check-write`, `splice`, `skip`;
  `result<_, stream-error>` for the writes and flushes; `result<list<u8>, stream-error>` for
  `read`; `own<pollable>` for `subscribe`; `bool`, nothing and `list<u32>` for `ready`, `block`
  and `poll(in: list<borrow<pollable>>)`.
* **`ansOk_wit`**: every admissible answer of `P2.ansOk` (in both readings, in every state) is
  WIT-typed or a trap: `witTrapOk (restrict io2T io2L)`. **`ioTh_wit`**: every trace accepted
  by `P2.ioTh r` is accepted by `witTrapTh (restrict io2T io2L)`.
* **REFUTED with `witOk` (traps not admitted)**: `ioTh_trap_not_wit`: `P2.ioTh` admits the
  trap of a `write` beyond the permit of `check-write`, which `witOk` rejects. This is the
  reason for `witTrapOk`.
* **REFUTED converse**: `wit_not_ioTh`: `witOk` accepts a `check-write` answer
  `error(x)` for any value `x` (`stream-error` is a named type, `tyOk` does not resolve it),
  which `P2.ansOk` rejects.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Resource (Protocol)

/-! ## Generic lemmas -/

theorem witOk_trap (T : Table) (e : WEv) (h : witOk T e = true) : witTrapOk T e = true := by
  cases e with
  | imp f a r =>
    cases hl : T.lookup f with
    | none => simp [witTrapOk, hl]
    | some s =>
      simp only [witOk, hl] at h
      simp only [witTrapOk, hl]
      cases hA : argsOk s a <;> simp_all
  | _ => rfl

theorem witTrapOk_restrict_not {T : Table} {L : List FnName} {f : FnName} (hf : f ∉ L)
    (a : List Val) (r : Option (List Val)) : witTrapOk (restrict T L) (.imp f a r) = true := by
  simp [witTrapOk, lookup_restrict, hf]

/-- A theory whose steps check `ok` accepts only traces of `pointwise ok`. -/
theorem accepts_pointwise {S : Type} (p : Protocol S WEv) (ok : WEv → Bool)
    (h : ∀ q e q', p.step q e = some q' → ok e = true) {t : List WEv} (ht : p.Accepts t) :
    (pointwise ok).Accepts t := by
  have key : ∀ (t : List WEv) (q : S), (p.run q t).isSome = true → ∀ e ∈ t, ok e = true := by
    intro t
    induction t with
    | nil => intro _ _ e he; cases he
    | cons e t ih =>
      intro q hq e' he'
      cases hs : p.step q e with
      | none => simp [Protocol.run, hs] at hq
      | some q' =>
        simp only [Protocol.run, hs, Option.bind_some] at hq
        rcases List.mem_cons.1 he' with rfl | he'
        · exact h q _ q' hs
        · exact ih q' hq e' he'
  exact (pointwise_accepts_iff ok t).2 (key t p.init ht)

/-- A trap or a WIT-typed answer. -/
theorem or_res {s : Binary.Sig} {a : List Val} {res : Option (List Val)}
    (h : res.isNone = true ∨ resOk s res = true) : (!argsOk s a || res.isNone || resOk s res) = true := by
  rcases h with h | h <;> simp [h]

/-! ## Result shapes -/

theorem tyAll_isU8 : ∀ vs : List Val, vs.all P2.isU8 = true → tyAll (.prim .u8) vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases v <;> simp_all [P2.isU8, tyAll, tyOk, primOk, tyAll_isU8 vs h.2]

theorem tyAll_idx (n : Nat) : ∀ vs : List Val, vs.all (P2.idxOk n) = true →
    tyAll (.prim .u32) vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases v <;> simp_all [P2.idxOk, tyAll, tyOk, primOk, tyAll_idx n vs h.2]

theorem resOk_unit {b : Bool} {ps : List (String × Binary.Ty)} {x : Binary.TyRef}
    {res : Option (List Val)} (h : P2.unitAns res = true) :
    resOk ⟨b, ps, some (.result none (some (.ref x)))⟩ res = true := by
  rw [P2.unitAns_eq_hand] at h
  unfold P2.unitAnsH at h
  split at h <;> simp_all [resOk, tyOk, tyOpt]

theorem resOk_nat {b : Bool} {ps : List (String × Binary.Ty)} {x : Binary.TyRef} {bd : Nat}
    {res : Option (List Val)} (h : P2.natAns bd res = true) :
    resOk ⟨b, ps, some (.result (some (.prim .u64)) (some (.ref x)))⟩ res = true := by
  unfold P2.natAns at h
  split at h <;> simp_all [resOk, tyOk, tyOpt, primOk]

theorem resOk_bytes2 {b : Bool} {ps : List (String × Binary.Ty)} {x : Binary.TyRef} {bd : Nat}
    {ne : Bool} {res : Option (List Val)} (h : P2.bytesAns bd ne res = true) :
    resOk ⟨b, ps, some (.result (some (.list (.prim .u8))) (some (.ref x)))⟩ res = true := by
  unfold P2.bytesAns at h
  split at h
  · simp only [Bool.and_eq_true] at h
    simp [resOk, tyOk, tyOpt, tyAll_isU8 _ h.1.1]
  · simp [resOk, tyOk, tyOpt]
  · exact absurd h (by simp)

theorem resOk_handle {b : Bool} {ps : List (String × Binary.Ty)} {x : Binary.TyRef}
    {res : Option (List Val)} (h : P2.handleAns res = true) :
    resOk ⟨b, ps, some (.own x)⟩ res = true := by
  rw [P2.handleAns_eq_hand] at h
  unfold P2.handleAnsH at h
  split at h <;> simp_all [resOk, tyOk]

theorem ite_unit {c : Prop} [Decidable c] {x : Bool} {res : Option (List Val)}
    (h : (if c then x && P2.unitAns res else res.isNone) = true) :
    res.isNone = true ∨ P2.unitAns res = true := by
  split at h
  · simp only [Bool.and_eq_true] at h; exact .inr h.2
  · exact .inl h

theorem bwf_unit {x y : Bool} {res : Option (List Val)}
    (h : (x && (P2.unitAns res || (y && res.isNone))) = true) :
    res.isNone = true ∨ P2.unitAns res = true := by
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with h | h
  exacts [.inr h, .inl h.2]

theorem resOk_poll {b : Bool} {n : String} {y : Binary.Ty} {a : List Val}
    {res : Option (List Val)} (h : P2.pollAns a res = true) :
    (!argsOk ⟨b, [(n, .list y)], some (.list (.prim .u32))⟩ a || res.isNone ||
      resOk ⟨b, [(n, .list y)], some (.list (.prim .u32))⟩ res) = true := by
  rcases a with _ | ⟨v, _ | ⟨w, a⟩⟩
  · simp [argsOk, tysOk]
  · cases v
    case record ps =>
      simp only [P2.pollAns] at h
      by_cases hp : ps.isEmpty = true
      · simp only [hp, ite_true] at h
        simp [h]
      · simp only [hp, Bool.false_eq_true, ite_false] at h
        rcases res with _ | ⟨_ | ⟨v, _ | ⟨w, res⟩⟩⟩ <;> try simp at h
        cases v <;> simp_all [resOk, tyOk]
        exact .inr (tyAll_idx _ _ (List.all_eq_true.2 h.2))
    all_goals simp [argsOk, tysOk, tyOk]
  · simp [argsOk, tysOk]

/-! ## The shapes of the imported signatures -/

/-- The result shape the class of a `wasi:io` function expects. -/
def ioShape : P2.IoOp → Binary.Sig → Bool
  | .checkWrite, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref _)))⟩
  | .splice, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref _)))⟩
  | .bsplice, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref _)))⟩
  | .skip, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref _)))⟩
  | .bskip, ⟨_, _, some (.result (some (.prim .u64)) (some (.ref _)))⟩ => true
  | .write, ⟨_, _, some (.result none (some (.ref _)))⟩
  | .writeZeroes, ⟨_, _, some (.result none (some (.ref _)))⟩
  | .bwf, ⟨_, _, some (.result none (some (.ref _)))⟩
  | .bwzf, ⟨_, _, some (.result none (some (.ref _)))⟩
  | .flush, ⟨_, _, some (.result none (some (.ref _)))⟩
  | .bflush, ⟨_, _, some (.result none (some (.ref _)))⟩ => true
  | .read, ⟨_, _, some (.result (some (.list (.prim .u8))) (some (.ref _)))⟩
  | .bread, ⟨_, _, some (.result (some (.list (.prim .u8))) (some (.ref _)))⟩ => true
  | .oSubscribe, ⟨_, _, some (.own _)⟩ | .iSubscribe, ⟨_, _, some (.own _)⟩ => true
  | .ready, ⟨_, _, some (.prim .bool)⟩ => true
  | .block, ⟨_, _, none⟩ => true
  | .poll, ⟨_, [(_, .list _)], some (.list (.prim .u32))⟩ => true
  | _, _ => false

/-- The `wasi:io` 0.2 functions the hand-written theory classifies. -/
def io2L : List FnName :=
  [P2.pollReady, P2.pollBlock, P2.pollPoll, P2.isRead, P2.isBread, P2.isSkip, P2.isBskip,
   P2.isSubscribe, P2.osCheckWrite, P2.osWrite, P2.osBwf, P2.osFlush, P2.osBflush,
   P2.osSubscribe, P2.osWriteZeroes, P2.osBwzf, P2.osSplice, P2.osBsplice]

/-- **Each classified function has an imported signature of the expected shape.** -/
theorem io2_shapes : io2L.all (fun f => (io2T.lookup f).any (ioShape (P2.ioOp f))) = true := by
  decide +kernel

/-- `io2L` is the imported `wasi:io` table without `error.to-debug-string`. -/
theorem io2L_eq : io2L = (names io2T).filter (· != P2.errDebug) := by decide +kernel

/-- An admissible answer of a class is a trap or has the result type of its shape. -/
theorem ansOk_shape (r : P2.Reading) (st : P2.IoSt) (o : P2.IoOp) (a : List Val)
    (res : Option (List Val)) (s : Binary.Sig) (hs : ioShape o s = true)
    (h : P2.ansOk r st o a res = true) : (!argsOk s a || res.isNone || resOk s res) = true := by
  unfold ioShape at hs
  split at hs
  all_goals first
    | exact absurd hs Bool.false_ne_true
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_res (.inr (resOk_nat h.1.2)))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_res (.inr (resOk_nat h.2)))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_res (.inr (resOk_unit h.2)))
    | (simp only [P2.ansOk, Bool.and_eq_true] at h; exact or_res (.inr (resOk_bytes2 h.2)))
    | (simp only [P2.ansOk] at h; exact or_res (.inr (resOk_handle h)))
    | (simp only [P2.ansOk] at h; exact resOk_poll h)
    | (simp only [P2.ansOk] at h
       exact (ite_unit h).elim (fun h => or_res (.inl h)) (fun h => or_res (.inr (resOk_unit h))))
    | (simp only [P2.ansOk] at h
       exact (bwf_unit h).elim (fun h => or_res (.inl h)) (fun h => or_res (.inr (resOk_unit h))))
    | (simp only [P2.ansOk, P2.readyAns_eq_hand, P2.blockAns_eq_hand, P2.readyAnsH,
        P2.blockAnsH] at h
       split at h <;> simp_all [resOk, tyOk, primOk])

/-! ## The theory against the WIT typing -/

/-- **Every admissible `wasi:io` answer is WIT-typed or a trap.** -/
theorem ansOk_wit (r : P2.Reading) (st : P2.IoSt) (f : FnName) (a : List Val)
    (res : Option (List Val)) (h : P2.ansOk r st (P2.ioOp f) a res = true) :
    witTrapOk (restrict io2T io2L) (.imp f a res) = true := by
  by_cases hf : f ∈ io2L
  · have hall := List.all_eq_true.1 io2_shapes f hf
    cases hl : io2T.lookup f with
    | none => simp [hl] at hall
    | some s =>
      simp only [hl, Option.any_some] at hall
      simp only [witTrapOk, lookup_restrict, hf, ite_true, hl]
      exact ansOk_shape r st _ a res s hall h
  · exact witTrapOk_restrict_not hf a res

theorem ioStep_wit (r : P2.Reading) {q q' : P2.IoSt} {e : WEv} (h : P2.ioStep r q e = some q') :
    witTrapOk (restrict io2T io2L) e = true := by
  cases e with
  | imp f a res =>
    simp only [P2.ioStep] at h
    split at h
    · exact ansOk_wit r q f a res ‹_›
    · cases h
  | _ => rfl

/-- **The `wasi:io` 0.2 theory implies the imported WIT typing (traps admitted).** -/
theorem ioTh_wit (r : P2.Reading) {t : List WEv} (h : (P2.ioTh r).Accepts t) :
    (witTrapTh (restrict io2T io2L)).Accepts t :=
  accepts_pointwise _ _ (fun _ _ _ hs => ioStep_wit r hs) h

/-! ## Refutations -/

/-- A `write` of one byte with no permit, answered by a trap. -/
def writeTrap : WEv := .imp P2.osWrite [.u32 0, bytesV [1]] none

/-- **REFUTED with `witOk`**: `P2.ioTh` admits the trap of a `write` beyond the permit (both
readings), which the trap-free WIT typing rejects. -/
theorem ioTh_trap_not_wit :
    (P2.ioTh .strict).Accepts [writeTrap] ∧ (P2.ioTh .loose).Accepts [writeTrap] ∧
      witOk (restrict io2T io2L) writeTrap = false := by
  unfold Protocol.Accepts; decide +kernel

/-- A `check-write` answered `error(true)`: `true` is not a `stream-error`. -/
def badStreamErr : WEv := .imp P2.osCheckWrite [.u32 0] (some [errV (some (.bool true))])

/-- **REFUTED converse**: the WIT typing accepts an answer `P2.ioTh` rejects (`tyOk` does not
resolve the named type `stream-error`). -/
theorem wit_not_ioTh :
    witOk (restrict io2T io2L) badStreamErr = true ∧ ¬ (P2.ioTh .loose).Accepts [badStreamErr] ∧
      ¬ (P2.ioTh .strict).Accepts [badStreamErr] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.WitImport
