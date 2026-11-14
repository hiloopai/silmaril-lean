module

public import Silmaril.Wasi.Versions.HttpBody3.Defs
public import Silmaril.Wasi.Versions.HttpBody.Thms
public import Silmaril.Wasi.Versions.Http3.Thms

@[expose] public section

/-!
# WASI 0.3 `wasi:http` response bodies: theorems

PROVED (standard axioms):

* `copy3_completed`, `copy3_dropped`: the packed codes of the concrete host decode back (for at
  most `2^27` items, so the count fits in a `u32`).
* **`body3Impl_sat`**: the concrete host `body3Impl B` is a model of `body3Th B` for every body
  web `B`, with no bound on the body length (reads deliver at most `2^27` bytes each).
* **`body3Th_httpTh3`**: the body theory refines the 0.3 outgoing HTTP theory of the status web.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## Packed codes -/

/-- `COMPLETED c` decodes back for `c ≤ 2^27`. -/
theorem copy3_completed {c : Nat} (hc : c ≤ chunk3) :
    copy3 (BitVec.ofNat 32 (packCopy .completed c)) = some (some (.completed, c)) := by
  have hlt : 16 * c < 2 ^ 32 := by unfold chunk3 at hc; omega
  have hn : (BitVec.ofNat 32 (packCopy .completed c)).toNat = 16 * c := by
    simp only [packCopy, CopyResult.toNat, Nat.zero_add, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  have hb : 16 * c ≠ Silmaril.Wasm.Component.Async.blocked := by
    unfold Silmaril.Wasm.Component.Async.blocked; omega
  simp [copy3, hn, P3.copyOf, hb]

/-- `DROPPED 0` decodes back. -/
theorem copy3_dropped : copy3 (BitVec.ofNat 32 (packCopy .dropped 0)) = some (some (.dropped, 0)) := by
  decide

/-- The 0.3 outgoing HTTP part of the state is the 0.3 outgoing HTTP state. -/
theorem foldl_base3 (p : List WEv) (q : Body3St) :
    (p.foldl body3Next q).base = p.foldl http3Next q.base := by
  induction p generalizing q with
  | nil => rfl
  | cons e p ih => exact ih (body3Next q e)

/-- **The 0.3 body theory refines the 0.3 outgoing HTTP theory** of its status web. -/
theorem body3Th_httpTh3 (B : BWeb) {t : List WEv} (h : (body3Th B).Accepts t) :
    (httpTh3 B.web).Accepts t := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
  have hp := gated_proj (i' := ({} : Http3St)) (n' := http3Next) (ok' := http3Ok B.web)
    Body3St.base (fun _ _ => rfl)
    (fun q e he => by simp only [body3Ok, Bool.and_eq_true] at he; exact he.1) _ t q hq
  exact Option.isSome_iff_exists.2 ⟨_, hp⟩

/-! ## The concrete host -/

/-- Functions other than `send` and `get-status-code` pass the 0.3 outgoing HTTP check. -/
theorem http3Ok_other (W : Web) (q : Http3St) {f : FnName} (h₁ : f ≠ send3) (h₂ : f ≠ getStatus3)
    (a : List Val) (r : Option (List Val)) : http3Ok W q (.imp f a r) = true := by
  unfold http3Ok
  split <;> simp_all

/-- Body functions are not checked by the 0.3 outgoing HTTP theory. -/
theorem bodyFn3_ne {f : FnName} (hb : isBodyFn3 f = true) : f ≠ send3 ∧ f ≠ getStatus3 := by
  simp only [isBodyFn3, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with ((rfl | rfl) | rfl) | rfl <;> decide

/-- Functions other than the body functions pass the body check. -/
theorem body3Check_other (B : BWeb) (q : Body3St) {f : FnName} (hb : isBodyFn3 f = false)
    (a : List Val) (r : Option (List Val)) : body3Check B q (.imp f a r) = true := by
  simp only [isBodyFn3, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hb
  obtain ⟨⟨⟨-, h₂⟩, h₃⟩, h₄⟩ := hb
  unfold body3Check
  split <;> simp_all

/-- A non-empty read answer passes the read check. -/
theorem read3Ok_take (rest : List (BitVec 8)) (n : Nat) :
    read3Ok rest n (some [P3.natV (packCopy .completed (rest.take (min n chunk3)).length),
      bytesV (rest.take (min n chunk3))]) = true := by
  have hc : (rest.take (min n chunk3)).length ≤ chunk3 :=
    (List.length_take_le _ _).trans (Nat.min_le_right _ _)
  have hn : (rest.take (min n chunk3)).length ≤ n :=
    (List.length_take_le _ _).trans (Nat.min_le_left _ _)
  have ht : rest.take (min n chunk3) = rest.take (rest.take (min n chunk3)).length := by
    rw [List.length_take]; exact List.take_eq_take_min
  unfold read3Ok
  simp only [P3.natV, copy3_completed hc, bytesV, u8sOf_map]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hn, ht, trivial⟩

/-- A read answer passes the read check. -/
theorem read3Ok_ans (rest : List (BitVec 8)) (n : Nat) : read3Ok rest n (read3Ans rest n) = true := by
  unfold read3Ans
  by_cases he : rest.isEmpty = true
  · simp only [he, ↓reduceIte, read3Ok, P3.natV, copy3_dropped]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact read3Ok_take rest n

/-- A future answer passes the future check. -/
theorem fut3Ok_ans (t : BitVec 32) (tr : Option Fields) : fut3Ok tr (fut3Ans t tr) = true := by
  cases tr <;> rfl

/-- A read answer of the concrete host passes the body check. -/
theorem body3Ans_read (B : BWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    body3Check B (body3State p)
      (.imp P3.cStreamRead (.u32 h :: a') (body3Ans B p P3.cStreamRead (.u32 h :: a'))) = true := by
  simp only [body3Check, body3Ans, ↓reduceIte, selfH, show P3.cStreamRead ≠ consumeBody3 by decide]
  cases hl : lookup h (body3State p).streams with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some x => exact read3Ok_ans _ _

/-- A future answer of the concrete host passes the body check. -/
theorem body3Ans_fut (B : BWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    body3Check B (body3State p)
      (.imp P3.cFutureRead (.u32 h :: a') (body3Ans B p P3.cFutureRead (.u32 h :: a'))) = true := by
  simp only [body3Check, body3Ans, ↓reduceIte, selfH, show P3.cFutureRead ≠ consumeBody3 by decide,
    show P3.cFutureRead ≠ P3.cStreamRead by decide]
  cases hl : lookup h (body3State p).futs with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some k =>
      show (match B k.1 k.2 with
        | .resp _ => fut3Ok (B.trailers k) (fut3Ans (freshH p) (B.trailers k))
        | .error _ => true) = true
      cases B k.1 k.2 <;> simp [fut3Ok_ans]

/-- A `copy-all` answer of the concrete host passes the body check. -/
theorem body3Ans_copy (B : BWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    body3Check B (body3State p) (.imp copyAll3 (.u32 h :: a') (body3Ans B p copyAll3 (.u32 h :: a'))) =
      true := by
  simp only [body3Check, body3Ans, ↓reduceIte, selfH, show copyAll3 ≠ consumeBody3 by decide,
    show copyAll3 ≠ P3.cStreamRead by decide, show copyAll3 ≠ P3.cFutureRead by decide]
  cases hl : lookup h (body3State p).trs with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some k => exact entriesOk_ans _

/-- Every body answer of the concrete host passes the body check. -/
theorem body3Ans_check (B : BWeb) (p : List WEv) {f : FnName} (hb : isBodyFn3 f = true)
    (a : List Val) : body3Check B (body3State p) (.imp f a (body3Ans B p f a)) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    simp only [isBodyFn3, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((rfl | rfl) | rfl) | rfl
    · simp [body3Check, consumeBody3, copyAll3, P3.cStreamRead, P3.cFutureRead, P3.canon]
    · exact body3Ans_copy B p h a'
    · exact body3Ans_read B p h a'
    · exact body3Ans_fut B p h a'
  all_goals rfl

/-- **Every answer of the concrete 0.3 host passes the check.** -/
theorem body3Impl_ok (B : BWeb) (p : List WEv) (f : FnName) (a : List Val) :
    body3Ok B (p.foldl body3Next {}) (.imp f a (body3Impl B p f a)) = true := by
  have hs : p.foldl body3Next {} = body3State p := rfl
  have hbase : (body3State p).base = p.foldl http3Next {} := foldl_base3 p {}
  rw [hs]
  by_cases hb : isBodyFn3 f = true
  · obtain ⟨h₁, h₂⟩ := bodyFn3_ne hb
    simp only [body3Ok, body3Impl, hb, ↓reduceIte, http3Ok_other B.web _ h₁ h₂, Bool.true_and]
    exact body3Ans_check B p hb a
  · have hb' : isBodyFn3 f = false := by simpa using hb
    simp only [body3Ok, body3Impl, hb', Bool.false_eq_true, ↓reduceIte, body3Check_other B _ hb',
      Bool.and_true, hbase]
    exact httpImpl3_ok B.web p f a

/-- **The concrete 0.3 HTTP host with bodies is a model of `body3Th B`.** -/
theorem body3Impl_sat {Y : Sig.{0}} {I : Set FnName} (B : BWeb) :
    (hostSat (body3Th B).Accepts).holds (concrete (Y := Y) (I := I) (body3Impl B)) :=
  concrete_sat _ fun _ ht => gated_follows (body3Impl_ok B) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
