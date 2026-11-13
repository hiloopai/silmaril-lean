module

public import Silmaril.Proofs.Wasi.Versions.Adapter.Leaf

/-!
# Proofs: weakest preconditions of the adapter's helper programs

Under the 0.2 theory `p2Th`: the chunked write loop, a blocking read, the error-code query, the
creation of the descriptor table and the drops reach their continuations with valid `errno`s,
and never trap.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P1 (FdSt)

variable {A : Type} {Q : A → Unit × Option (BitVec 64) → Prop}

/-- `stream_error_to_errno` of `last-operation-failed`. -/
theorem wp_lastOp {s : ASt} {err : BitVec 32} {k : Nat → SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hk : ∀ e qT, ValidErr e → Wp p2Th (k e) Q qT) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (lastOpErrno s err k) Q qT := by
  intro n qT' h
  rcases step_errCode h with rfl | ⟨c, rfl⟩
  · intro _ qT'' _; exact hk _ _ ⟨by decide, by decide⟩
  · intro _ qT'' _; exact hk _ _ (validErr_codeErrno _)

/-- **The write loop** reaches `onOk` or `onErr` with a valid `errno`. -/
theorem wp_writeLoop {s : ASt} {h : BitVec 32} {onOk : SProg ASt imports}
    {onErr : Nat → SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hok : ∀ qT, Wp p2Th onOk Q qT) (herr : ∀ e qT, ValidErr e → Wp p2Th (onErr e) Q qT) :
    ∀ (bs : List (BitVec 8)) (qT : Unit × Option (BitVec 64)),
      Wp p2Th (writeLoop s h onOk onErr bs) Q qT
  | bs, qT => by
    rw [writeLoop]
    intro n qT' hn
    rcases step_write hn with rfl | rfl | ⟨err, rfl⟩
    · show Wp p2Th (if _ : bs.length ≤ 4096 then onOk else writeLoop s h onOk onErr (bs.drop 4096))
        Q qT'
      split
      · exact hok qT'
      · exact wp_writeLoop hok herr (bs.drop 4096) qT'
    · exact herr _ _ ⟨by decide, by decide⟩
    · exact wp_lastOp herr qT'
termination_by bs => bs.length
decreasing_by simp only [List.length_drop]; omega

/-- **A blocking read** reaches `onOk` with at most `n` bytes, or `onErr` with a valid
`errno`. -/
theorem wp_readOnce {s : ASt} {h : BitVec 32} {n : Nat} (hn : n < 2 ^ 64)
    {onOk : List Val → SProg ASt imports} {onErr : Nat → SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hok : ∀ bs qT, allU8 bs = true → bs.length ≤ n → Wp p2Th (onOk bs) Q qT)
    (herr : ∀ e qT, ValidErr e → Wp p2Th (onErr e) Q qT) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (readOnce s h n onOk onErr) Q qT := by
  intro r qT' hr
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  rcases step_read hr with ⟨bs, rfl, hu, hl⟩ | rfl | ⟨err, rfl⟩
  · rw [hn'] at hl
    show Wp p2Th (if allU8 bs = true ∧ bs.length ≤ n then onOk bs else trapR s) Q qT'
    simp only [hu, hl, and_self, ite_true]
    exact hok bs qT' hu hl
  · exact hok [] qT' rfl (Nat.zero_le _)
  · exact wp_lastOp herr qT'

/-- `preopens` of a well-typed `get-directories` answer succeeds, with one entry per preopen. -/
theorem preopens_some : ∀ {ps : List Val}, ps.all preopenOk = true →
    ∃ l, preopens ps = some l ∧ l.length = ps.length
  | [], _ => ⟨[], rfl, rfl⟩
  | p :: ps, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨l, hl, hlen⟩ := preopens_some h.2
    unfold preopenOk at h
    split at h
    · rename_i d _
      exact ⟨.file d true 0 none none :: l, by simp [preopens, hl], by simp [hlen]⟩
    · exact absurd h.1 (by simp)

/-- The preopens, after stdin, stdout and stderr. -/
theorem wp_withPreopens {s : ASt} {f : FdSt} (hJ : FdInv s f) (hs : s.table = none)
    {k : ASt → List Desc → SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hk : ∀ s' t qT, s'.table = some t → FdInv s' f → Wp p2Th (k s' t) Q qT)
    (i o e : BitVec 32) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (withPreopens s k i o e) Q qT := by
  intro n4 q4 h4
  obtain ⟨ps, rfl, hps, hlen⟩ := step_dirs h4
  obtain ⟨l, hl, hll⟩ := preopens_some hps
  have hl' : l.length ≤ maxPreopens := hll ▸ hlen
  show Wp p2Th (match preopens ps with
    | some l => if l.length ≤ maxPreopens then k ⟨some ([.stdin i, .stdout o, .stderr e] ++ l),
        s.free⟩ ([.stdin i, .stdout o, .stderr e] ++ l) else trapR s
    | none => trapR s) Q q4
  simp only [hl, hl', ite_true]
  exact hk _ _ q4 rfl (fdInv_withTable hJ hs hl')

/-- **The descriptor table** is created (or already there) and satisfies the invariant. -/
theorem wp_withTable {s : ASt} {f : FdSt} (hJ : FdInv s f) {k : ASt → List Desc → SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hk : ∀ s' t qT, s'.table = some t → FdInv s' f → Wp p2Th (k s' t) Q qT)
    (qT : Unit × Option (BitVec 64)) : Wp p2Th (withTable s k) Q qT := by
  unfold withTable
  split
  · next t ht => exact hk s t qT ht hJ
  · next hs =>
    intro n1 q1 h1
    obtain ⟨i, rfl⟩ := step_u32 (.inl rfl) h1
    intro n2 q2 h2
    obtain ⟨o, rfl⟩ := step_u32 (.inr (.inl rfl)) h2
    intro n3 q3 h3
    obtain ⟨e, rfl⟩ := step_u32 (.inr (.inr rfl)) h3
    exact wp_withPreopens hJ hs hk i o e q3

/-- **Drops** reach their continuation. -/
theorem wp_dropDesc {d : Desc} {k : SProg ASt imports}
    {Q : ASt × Option (List Val) → Unit × Option (BitVec 64) → Prop}
    (hk : ∀ qT, Wp p2Th k Q qT) (qT : Unit × Option (BitVec 64)) :
    Wp p2Th (dropDesc d k) Q qT := by
  unfold dropDesc
  split
  · exact hk qT
  · exact fun _ q _ => hk q
  · exact fun _ q _ => hk q
  · exact fun _ q _ => hk q
  · rename_i inp out
    cases inp <;> cases out <;> (repeat intro) <;> exact hk _

end Silmaril.Wasi.Versions.Adapter
