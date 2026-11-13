module

public import Silmaril.Wasi.Versions.HttpBody.Defs
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# WASI 0.2 `wasi:http` response bodies: theorems

PROVED (standard axioms):

* `fieldsOf_fieldsV`, `u8sOf_map`: the field and byte encodings decode back.
* **`bodyImpl_sat`**: the concrete host `bodyImpl B` is a model of `bodyTh B` for every body
  web `B`.
* **`bodyTh_httpTh`**: the body theory refines the outgoing HTTP theory of the status web: every
  trace accepted by `bodyTh B` is accepted by `httpTh B.web` (the general `gated_proj`).
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Decoding -/

/-- Bytes decode back. -/
@[simp] theorem u8sOf_map (bs : List (BitVec 8)) : u8sOf (bs.map .u8) = some bs := by
  induction bs with
  | nil => rfl
  | cons b t ih => simp [u8sOf, ih]

/-- Characters decode back. -/
@[simp] theorem charsOf_map (cs : List Char) : charsOf (cs.map .char) = some cs := by
  induction cs with
  | nil => rfl
  | cons c t ih => simp [charsOf, ih]

/-- Fields decode back. -/
theorem fieldsOf_fieldsV (l : Fields) : fieldsOf (fieldsV l) = some l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [fieldsV, fieldsOf, List.map_cons, fieldsOfL] at ih ⊢
    rw [ih]
    simp [fieldOf, fieldV, bytesV]

/-! ## Projections of gated theories -/

/-- **A gated run projects** along a map of states that commutes with the next-state functions
and weakens the checks. -/
theorem gated_proj {S S' : Type} {i : S} {n : S → WEv → S} {ok : S → WEv → Bool}
    {i' : S'} {n' : S' → WEv → S'} {ok' : S' → WEv → Bool} (π : S → S')
    (hn : ∀ q e, π (n q e) = n' (π q) e) (hok : ∀ q e, ok q e = true → ok' (π q) e = true) :
    ∀ (q : S) (t : List WEv) (q' : S), (gated i n ok).run q t = some q' →
      (gated i' n' ok').run (π q) t = some (π q')
  | q, [], q', h => by
    have hq : q = q' := Option.some.inj h
    rw [hq]; rfl
  | q, e :: t, q', h => by
    have he : ok q e = true := by
      by_contra hc
      simp [Protocol.run, gated, hc] at h
    have h' : (gated i n ok).run (n q e) t = some q' := by simpa [Protocol.run, gated, he] using h
    have ih := gated_proj (i := i) (i' := i') π hn hok (n q e) t q' h'
    rw [hn] at ih
    simpa [Protocol.run, gated, hok q e he] using ih

/-- **The body theory refines the outgoing HTTP theory** of its status web. -/
theorem bodyTh_httpTh (B : BWeb) {t : List WEv} (h : (bodyTh B).Accepts t) :
    (httpTh B.web).Accepts t := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
  have hp := gated_proj (i' := HttpSt.init) (n' := httpNext) (ok' := httpOk B.web) BodySt.base
    (fun _ _ => rfl) (fun q e he => by simp only [bodyOk, Bool.and_eq_true] at he; exact he.1)
    _ t q hq
  exact Option.isSome_iff_exists.2 ⟨_, hp⟩

/-! ## The concrete host -/

/-- The outgoing HTTP part of the state is the outgoing HTTP state. -/
theorem foldl_base (p : List WEv) (q : BodySt) :
    (p.foldl bodyNext q).base = p.foldl httpNext q.base := by
  induction p generalizing q with
  | nil => rfl
  | cons e p ih => exact ih (bodyNext q e)

/-- Functions other than `get` and `status` pass the outgoing HTTP check. -/
theorem httpOk_other (W : Web) (q : HttpSt) {f : FnName} (h₁ : f ≠ futGet) (h₂ : f ≠ respStatus)
    (a : List Val) (r : Option (List Val)) : httpOk W q (.imp f a r) = true := by
  unfold httpOk
  split <;> simp_all

/-- Body functions are not checked by the outgoing HTTP theory. -/
theorem bodyFn_ne {f : FnName} (hb : isBodyFn f = true) : f ≠ futGet ∧ f ≠ respStatus := by
  simp only [isBodyFn, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl <;> decide

/-- Functions other than the body functions pass the body check. -/
theorem bodyCheck_other (B : BWeb) (q : BodySt) {f : FnName} (hb : isBodyFn f = false)
    (a : List Val) (r : Option (List Val)) : bodyCheck B q (.imp f a r) = true := by
  have hr : isReadFn f = false := by
    simp only [isBodyFn, Bool.or_eq_false_iff] at hb
    simp [isReadFn, hb.2, hb.1.2]
  have ht : f ≠ trGet2 := fun h => by subst h; simp [isBodyFn] at hb
  have he : f ≠ entries2 := fun h => by subst h; simp [isBodyFn] at hb
  unfold bodyCheck
  split <;> simp_all

/-- An `ok(bytes)` read answer passes the read check. -/
theorem readOk_ok (rest : List (BitVec 8)) (len : Nat) :
    readOk rest len (some [okV (some (bytesV (rest.take len)))]) = true := by
  have hl : (rest.take len).length ≤ len := List.length_take_le _ _
  have ht : rest.take len = rest.take (rest.take len).length := by
    rw [List.length_take]; exact List.take_eq_take_min
  unfold readOk
  simp only [okV, bytesV]
  rw [u8sOf_map]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hl, ht⟩

/-- A read answer passes the read check. -/
theorem readOk_ans (rest : List (BitVec 8)) (len : Nat) : readOk rest len (readAns rest len) = true := by
  unfold readAns
  by_cases he : rest.isEmpty = true
  · simp [he, readOk, P2.errClosed, errV]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    exact readOk_ok rest len

/-- A trailer answer passes the trailer check. -/
theorem trailerOk_ans (n : BitVec 32) (tr : Option Fields) : trailerOk tr (trailerAns n tr) = true := by
  cases tr <;> rfl

/-- An `entries` answer passes the `entries` check. -/
theorem entriesOk_ans (tr : Option Fields) : entriesOk tr (some [fieldsV (tr.getD [])]) = true := by
  cases tr with
  | none => rfl
  | some l => simp [entriesOk, fieldsOf_fieldsV]

/-- A read answer of the concrete host passes the body check. -/
theorem bodyAns_read (B : BWeb) (p : List WEv) {f : FnName} (hf : isReadFn f = true)
    (h : BitVec 32) (a' : List Val) :
    bodyCheck B (bodyState p) (.imp f (.u32 h :: a') (bodyAns B p f (.u32 h :: a'))) = true := by
  have h1 : f ≠ consume2 ∧ f ≠ bodyStream2 ∧ f ≠ bodyFinish2 := by
    simp only [isReadFn, Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with rfl | rfl <;> decide
  simp only [bodyCheck, bodyAns, hf, h1.1, h1.2.1, h1.2.2, or_self, ↓reduceIte, selfH]
  cases hl : lookup h (bodyState p).streams with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some x => exact readOk_ans _ _

/-- A trailer-future answer of the concrete host passes the body check. -/
theorem bodyAns_tr (B : BWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    bodyCheck B (bodyState p) (.imp trGet2 (.u32 h :: a') (bodyAns B p trGet2 (.u32 h :: a'))) =
      true := by
  have hr : isReadFn trGet2 = false := by decide
  simp only [bodyCheck, bodyAns, hr, Bool.false_eq_true, ↓reduceIte, selfH,
    show ¬(trGet2 = consume2 ∨ trGet2 = bodyStream2) by decide,
    show trGet2 ≠ bodyFinish2 by decide]
  cases hl : lookup h (bodyState p).ftr with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some k =>
      show (match B k.1 k.2 with
        | .resp _ => trailerOk (B.trailers k) (trailerAns (freshH p) (B.trailers k))
        | .error _ => true) = true
      cases B k.1 k.2 <;> simp [trailerOk_ans]

/-- An `entries` answer of the concrete host passes the body check. -/
theorem bodyAns_entries (B : BWeb) (p : List WEv) (h : BitVec 32) (a' : List Val) :
    bodyCheck B (bodyState p) (.imp entries2 (.u32 h :: a') (bodyAns B p entries2 (.u32 h :: a'))) =
      true := by
  have hr : isReadFn entries2 = false := by decide
  simp only [bodyCheck, bodyAns, hr, Bool.false_eq_true, ↓reduceIte, selfH,
    show ¬(entries2 = consume2 ∨ entries2 = bodyStream2) by decide,
    show entries2 ≠ bodyFinish2 by decide, show entries2 ≠ trGet2 by decide]
  cases hl : lookup h (bodyState p).trs with
  | none => rfl
  | some o => cases o with
    | none => rfl
    | some k => exact entriesOk_ans _

/-- Every body answer of the concrete host passes the body check. -/
theorem bodyAns_check (B : BWeb) (p : List WEv) {f : FnName} (hb : isBodyFn f = true)
    (a : List Val) : bodyCheck B (bodyState p) (.imp f a (bodyAns B p f a)) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    simp only [isBodyFn, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
    · simp [bodyCheck, isReadFn, consume2, trGet2, entries2, P2.isRead, P2.isBread]
    · simp [bodyCheck, isReadFn, bodyStream2, trGet2, entries2, P2.isRead, P2.isBread]
    · simp [bodyCheck, isReadFn, bodyFinish2, trGet2, entries2, P2.isRead, P2.isBread]
    · exact bodyAns_tr B p h a'
    · exact bodyAns_entries B p h a'
    · exact bodyAns_read B p (by decide) h a'
    · exact bodyAns_read B p (by decide) h a'
  all_goals rfl

/-- **Every answer of the concrete host passes the check.** -/
theorem bodyImpl_ok (B : BWeb) (p : List WEv) (f : FnName) (a : List Val) :
    bodyOk B (p.foldl bodyNext {}) (.imp f a (bodyImpl B p f a)) = true := by
  have hs : p.foldl bodyNext {} = bodyState p := rfl
  have hbase : (bodyState p).base = p.foldl httpNext HttpSt.init := foldl_base p {}
  rw [hs]
  by_cases hb : isBodyFn f = true
  · obtain ⟨h₁, h₂⟩ := bodyFn_ne hb
    simp only [bodyOk, bodyImpl, hb, ↓reduceIte, httpOk_other B.web _ h₁ h₂, Bool.true_and]
    exact bodyAns_check B p hb a
  · have hb' : isBodyFn f = false := by simpa using hb
    simp only [bodyOk, bodyImpl, hb', Bool.false_eq_true, ↓reduceIte, bodyCheck_other B _ hb',
      Bool.and_true, hbase]
    exact httpImpl_ok B.web p f a

/-- **The concrete 0.2 HTTP host with bodies is a model of `bodyTh B`.** -/
theorem bodyImpl_sat {Y : Sig.{0}} {I : Set FnName} (B : BWeb) :
    (hostSat (bodyTh B).Accepts).holds (concrete (Y := Y) (I := I) (bodyImpl B)) :=
  concrete_sat _ fun _ ht => gated_follows (bodyImpl_ok B) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

end Silmaril.Wasi.Versions.Net
