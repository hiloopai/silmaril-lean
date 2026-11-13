module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Wasm.JcoTool.KCore.Thms

/-!
# `dexec` and `KCore.exec` agree on statements without built-in calls

`dexec` differs from `KCore.exec` only at `call`. On a statement without calls (`noCall`), it is
`KCore.exec` on the same globals, memory, locals and pending read, with the store untouched
(`dexec_up`). So the facts `KCore` proves about the compiled kernel, the feed loop and the flush
(`feed_sound`, `flushOut_sound`, through the header `KCore.Thms`) hold for `dexec`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KDrop

open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

/-- The statement calls no built-in. -/
def noCall : S → Bool
  | .seq a b => noCall a && noCall b
  | .ite _ t e => noCall t && noCall e
  | .block b => noCall b
  | .loop b => noCall b
  | .call .. => false
  | _ => true

/-- The result of a `KCore` run, with the store `d`. -/
def lift (d : DStore) : Option (Out × St) → Option (Out × DSt) :=
  Option.map fun p => (p.1, DSt.up p.2 d)

theorem eval_up (e : E) (t : St) (d : DStore) : e.eval (DSt.up t d).down = e.eval t := by
  induction e with
  | c n => rfl
  | l i => rfl
  | g i => rfl
  | bin o a b iha ihb => simp only [E.eval, iha, ihb]
  | eqz a iha => simp only [E.eval, iha]
  | ld8 a iha => simp only [E.eval, iha]; rfl

theorem dlab_lift (d : DStore) (x : Option (Out × St)) :
    dexec.dlab (lift d x) = lift d (lab x) := by
  rcases x with _ | ⟨o, t⟩
  · rfl
  · rcases o with _ | (_ | k) | v <;> rfl

theorem dloopN_up {body : S} {f : Nat} {d : DStore}
    (ih : ∀ t, dexec body f (DSt.up t d) = lift d (exec body f t)) :
    ∀ n t, dexec.dloopN (dexec body f) n (DSt.up t d) = lift d (loopN (exec body f) n t) := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ihn =>
    intro t
    have hb := ih t
    simp only [dexec.dloopN, loopN, hb]
    rcases exec body f t with _ | ⟨o, t'⟩
    · rfl
    · rcases o with _ | (_ | k) | v
      · rfl
      · exact ihn t'
      · rfl
      · rfl

theorem dexec_seq_up {a b : S} {f : Nat} {d : DStore} {t : St}
    (iha : dexec a f (DSt.up t d) = lift d (exec a f t))
    (ihb : ∀ t', dexec b f (DSt.up t' d) = lift d (exec b f t')) :
    dexec (.seq a b) f (DSt.up t d) = lift d (exec (.seq a b) f t) := by
  simp only [dexec, exec, iha]
  rcases exec a f t with _ | ⟨o, t'⟩
  · rfl
  · rcases o with _ | k | v
    · exact ihb t'
    · rfl
    · rfl

/-- **`dexec` is `KCore.exec` on statements without calls.** -/
theorem dexec_up : ∀ (b : S), noCall b = true → ∀ (f : Nat) (t : St) (d : DStore),
    dexec b f (DSt.up t d) = lift d (exec b f t)
  | .nop, _, _, _, _ => rfl
  | .unreachable, _, _, _, _ => rfl
  | .lset i e, _, _, t, d => by simp only [dexec, exec, eval_up]; rfl
  | .gset i e, _, _, t, d => by simp only [dexec, exec, eval_up]; rfl
  | .st8 a v, _, _, t, d => by simp only [dexec, exec, eval_up]; rfl
  | .mcopy a b c, _, _, t, d => by simp only [dexec, exec, eval_up]; rfl
  | .br k, _, _, _, _ => rfl
  | .brIf k c, _, _, t, d => by
    simp only [dexec, exec, eval_up]
    split <;> rfl
  | .ret e, _, _, t, d => by simp only [dexec, exec, eval_up]; rfl
  | .call .., h, _, _, _ => by simp [noCall] at h
  | .seq a b, h, f, t, d => by
    simp only [noCall, Bool.and_eq_true] at h
    exact dexec_seq_up (dexec_up a h.1 f t d) (fun t' => dexec_up b h.2 f t' d)
  | .ite c a b, h, f, t, d => by
    simp only [noCall, Bool.and_eq_true] at h
    simp only [dexec, exec, eval_up]
    split
    · rw [dexec_up a h.1, dlab_lift]
    · rw [dexec_up b h.2, dlab_lift]
  | .block b, h, f, t, d => by
    simp only [noCall] at h
    simp only [dexec, exec, dexec_up b h, dlab_lift]
  | .loop b, h, f, t, d => by
    simp only [noCall] at h
    exact dloopN_up (fun t' => dexec_up b h f t' d) f t

/-- An invocation state is the lifting of a `KCore` state. -/
theorem up_down (s : DSt) : DSt.up s.down s.st = s := rfl

theorem dexec_down {b : S} (h : noCall b = true) (f : Nat) (s : DSt) :
    dexec b f s = lift s.st (exec b f s.down) :=
  dexec_up b h f s.down s.st

/-- A statement without calls keeps the store. -/
theorem noCall_st {b : S} (hb : noCall b = true) {f : Nat} {s s' : DSt} {o : Out}
    (h : dexec b f s = some (o, s')) : s'.st = s.st := by
  rw [dexec_down hb] at h
  obtain ⟨⟨o', t'⟩, -, hx⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hx
  rw [← hx.2]
  rfl

/-! ## The generated statements without calls -/

theorem noCall_seqs {l : List S} (h : ∀ a ∈ l, noCall a = true) : noCall (seqs l) = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => exact h a (by simp)
    | cons b l =>
      simp only [seqs, noCall, Bool.and_eq_true]
      exact ⟨h a (by simp), ih fun x hx => h x (by simp [hx])⟩

theorem noCall_cS : ∀ c : KStmt, noCall (cS c) = true
  | .skip => rfl
  | .seq p q => by simp only [cS, noCall, noCall_cS p, noCall_cS q, Bool.and_self]
  | .emit _ => rfl
  | .set _ => rfl
  | .push _ => rfl
  | .emitBuf => rfl
  | .clear => rfl
  | .ite _ p q => by simp only [cS, noCall, noCall_cS p, noCall_cS q, Bool.and_self]

theorem noCall_feedLoop (k : KM) : noCall (feedLoop k) = true := by
  simp [feedLoop, seqs, noCall, noCall_cS]

theorem noCall_flushOut (k : KM) : noCall (flushOut k) = true := by
  simp [flushOut, seqs, noCall, noCall_cS]

theorem noCall_onReadD (k : KM) (p : E) : noCall (onReadD k p) = true := by
  simp [onReadD, seqs, noCall, noCall_feedLoop]

theorem noCall_onWriteD (p : E) : noCall (onWriteD p) = true := by
  simp [onWriteD, seqs, noCall]

/-! ## Generic facts of `dexec` -/

theorem dexec_seq_norm {a b : S} {f : Nat} {s s₁ : DSt} (h : dexec a f s = some (.norm, s₁)) :
    dexec (.seq a b) f s = dexec b f s₁ := by
  simp only [dexec, h]

theorem dexec_seq_none {a b : S} {f : Nat} {s : DSt} (h : dexec a f s = none) :
    dexec (.seq a b) f s = none := by
  simp only [dexec, h]

theorem dexec_ite (c : E) (t e : S) (f : Nat) (s : DSt) :
    dexec (.ite c t e) f s = dexec.dlab (if c.eval s.down ≠ 0 then dexec t f s else dexec e f s) := rfl

theorem dlab_ret {x : Option (Out × DSt)} {v : Nat} {s : DSt}
    (h : dexec.dlab x = some (.ret v, s)) : x = some (.ret v, s) := by
  rcases x with _ | ⟨o, t⟩
  · cases h
  · rcases o with _ | (_ | k) | w <;> simp_all [dexec.dlab]

/-- A branch of an `if` that returned. -/
theorem dexec_ite_ret {c : E} {t e : S} {f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (.ite c t e) f s = some (.ret v, s')) :
    (c.eval s.down ≠ 0 ∧ dexec t f s = some (.ret v, s')) ∨
      (c.eval s.down = 0 ∧ dexec e f s = some (.ret v, s')) := by
  rw [dexec_ite] at h
  by_cases hc : c.eval s.down = 0
  · simp only [hc, ne_eq, not_true_eq_false, ↓reduceIte] at h
    exact .inr ⟨hc, dlab_ret h⟩
  · simp only [hc, ne_eq, not_false_eq_true, ↓reduceIte] at h
    exact .inl ⟨hc, dlab_ret h⟩

/-- A sequence that returned: the first part returned, or finished normally and the rest
returned. -/
theorem dexec_seq_ret {a b : S} {f : Nat} {s s' : DSt} {v : Nat}
    (h : dexec (.seq a b) f s = some (.ret v, s')) :
    dexec a f s = some (.ret v, s') ∨ ∃ s₁, dexec a f s = some (.norm, s₁) ∧ dexec b f s₁ = some (.ret v, s') := by
  simp only [dexec] at h
  rcases ha : dexec a f s with _ | ⟨o, s₁⟩
  · rw [ha] at h; cases h
  · rw [ha] at h
    rcases o with _ | k | w
    · exact .inr ⟨s₁, rfl, h⟩
    · cases h
    · exact .inl h

end Silmaril.Proofs.Wasm.JcoTool.KDrop
