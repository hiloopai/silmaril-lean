module

public import Silmaril.Net.WebSocket.Message.Defs

/-!
# WebSocket messages: proofs

For `Silmaril.Net.WebSocket.Message.Thms` (RFC 6455 §5.4, §5.5).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebSocket

open Silmaril.Net.WebSocket

theorem maskOk_of_keys {role : Role} {keys : Nat → Option MaskKey} (hk : KeysFor role keys)
    (i : Nat) (fin : Bool) (op : Nat) (p : List UInt8) :
    (Frame.mk fin 0 op (keys i) p).maskOk role = true := by
  have := hk i
  cases role <;> cases h : keys i <;> simp_all [Frame.maskOk]

theorem complete_ok {op : Nat} {data : List UInt8} (h : op = opText → isUtf8 data = true) :
    complete op data = .ok (.message op data) := by
  unfold complete
  by_cases ho : op = opText
  · simp [ho, h ho]
  · simp [ho]

/-- The frames after the first: continuations, delivered as one message at the end. -/
theorem run_continuations (role : Role) (keys : Nat → Option MaskKey)
    (hk : KeysFor role.peer keys) (op : Nat) :
    ∀ (cs : List (List UInt8)) (i : Nat) (acc : List UInt8),
      (op = opText → isUtf8 (acc ++ cs.flatten) = true) →
      Receiver.run role ⟨some (op, acc)⟩ (fragmentsFrom keys i opContinuation cs) =
        .ok (⟨none⟩, [.message op (acc ++ cs.flatten)])
  | [], i, acc, hu => by
    simp only [List.flatten_nil, List.append_nil] at hu
    simp [fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, isDefinedOpcode,
      isControl, opContinuation, complete_ok hu]
  | [c], i, acc, hu => by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hu ⊢
    simp [fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, isDefinedOpcode,
      isControl, opContinuation, complete_ok hu]
  | c :: c' :: cs, i, acc, hu => by
    have ih := run_continuations role keys hk op (c' :: cs) (i + 1) (acc ++ c)
      (by simpa [List.append_assoc] using hu)
    simp only [fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, isDefinedOpcode, opContinuation,
      isControl] at ih ⊢
    simp only [List.contains, List.elem, BEq.rfl, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, show ¬ (8 ≤ 0) by omega, decide_false]
    rw [ih]
    simp [List.append_assoc]

theorem run_fragments (role : Role) (keys : Nat → Option MaskKey) (hk : KeysFor role.peer keys)
    (op : Nat) (hop : op = opText ∨ op = opBinary) (chunks : List (List UInt8))
    (hu : op = opText → isUtf8 chunks.flatten = true) :
    Receiver.run role {} (fragments keys op chunks) = .ok ({}, [.message op chunks.flatten]) := by
  have hdef : isDefinedOpcode op = true := by
    rcases hop with rfl | rfl <;> rfl
  have hctl : isControl op = false := by
    rcases hop with rfl | rfl <;> rfl
  have hcont : (op == opContinuation) = false := by
    rcases hop with rfl | rfl <;> rfl
  match chunks with
  | [] =>
    simp only [List.flatten_nil] at hu ⊢
    simp [fragments, fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, hdef, hctl,
      hcont, complete_ok hu]
  | [c] =>
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hu ⊢
    simp [fragments, fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, hdef, hctl,
      hcont, complete_ok hu]
  | c :: c' :: cs =>
    have ih := run_continuations role keys hk op (c' :: cs) 1 c (by simpa using hu)
    simp only [fragments, fragmentsFrom, Receiver.run, Receiver.step, maskOk_of_keys hk, hdef,
      hctl, hcont, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false,
      Nat.zero_add] at ih ⊢
    rw [ih]
    simp

/-! ## Keepalive frames do not disturb data messages -/

theorem step_keepalive (role : Role) (r : Receiver) (f : Frame) (h : f.isKeepalive role = true) :
    ∃ d, r.step role f = .ok (r, some d) ∧ dataOnly [d] = [] := by
  simp only [Frame.isKeepalive, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hm, hr⟩, ho⟩, hc⟩ := h
  rcases ho with ho | ho
  · refine ⟨.ping f.payload, ?_, rfl⟩
    simp [Receiver.step, hm, hr, ho, controlDelivery, hc, isDefinedOpcode, isControl, opPing]
  · refine ⟨.pong f.payload, ?_, rfl⟩
    simp [Receiver.step, hm, hr, ho, controlDelivery, hc, isDefinedOpcode, isControl, opPing, opPong]

theorem dataOnly_append (xs ys : List Delivery) :
    dataOnly (xs ++ ys) = dataOnly xs ++ dataOnly ys := by
  simp [dataOnly, List.filter_append]

theorem run_filter_keepalive (role : Role) (r : Receiver) (fs : List Frame) :
    (r.run role fs).map (fun p => (p.1, dataOnly p.2)) =
      (r.run role (fs.filter fun f => !f.isKeepalive role)).map
        (fun p => (p.1, dataOnly p.2)) := by
  induction fs generalizing r with
  | nil => rfl
  | cons f fs ih =>
    by_cases hk : f.isKeepalive role = true
    · obtain ⟨d, hs, hd⟩ := step_keepalive role r f hk
      simp only [List.filter_cons, hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← ih r, Receiver.run, hs]
      simp only
      cases hrun : r.run role fs with
      | error e => rfl
      | ok p =>
        simp only [Except.map, Option.toList_some, List.singleton_append]
        rw [show d :: p.2 = [d] ++ p.2 from rfl, dataOnly_append, hd, List.nil_append]
    · simp only [List.filter_cons, hk, Bool.not_false, ↓reduceIte, Receiver.run]
      cases hs : r.step role f with
      | error e => rfl
      | ok q =>
        obtain ⟨r', d⟩ := q
        simp only
        have ih' := ih r'
        cases h1 : r'.run role fs <;>
          cases h2 : r'.run role (fs.filter fun f => !f.isKeepalive role) <;>
          simp only [h1, h2, Except.map] at ih' ⊢
        · exact ih'
        · cases ih'
        · cases ih'
        · next p q =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at ih' ⊢
          exact ⟨ih'.1, by rw [dataOnly_append, dataOnly_append, ih'.2]⟩

end Silmaril.Proofs.Net.WebSocket
