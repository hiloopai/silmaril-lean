module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Core

/-!
# Proofs: the read theories on the component's calls and answers

How `fsReadTh3w F` steps on the component's `stream.read` answers (`rd3_completed`,
`rd3_dropped`, `rd3_blocked`, `rd3_none`), and how the 0.2 theory `fsRead2 F` steps on the
component's 0.2 calls (`rd2_nr`: non-read calls leave it; `rd2_rvs`; `rd2_bread`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy blocked CopyResult)
open Silmaril.Wasi.Versions.P3

variable (F : BitVec 32 → List (BitVec 8))

/-- `rest` after `setRest` at the same key. -/
theorem rest_setRest_eq (q : RdSt) (k : Nat) (bs : List (BitVec 8)) :
    rest (setRest q k bs) k = some bs := by
  simp [rest, setRest]

/-- `rest` after `setRest` at another key. -/
theorem rest_setRest_ne (q : RdSt) {k k' : Nat} (bs : List (BitVec 8)) (h : k' ≠ k) :
    rest (setRest q k bs) k' = rest q k' := by
  simp [rest, setRest, Ne.symm h]

theorem rd3_step_of {q : RdSt} {e : WEv} (h : rdShaped e = true) :
    (fsReadTh3w F).step q e = rdStepZ F q e := by
  simp [fsReadTh3w, h]

theorem rdShaped_read {rv nv : Val} (r : Option (List Val)) (hn : (natOf nv).isSome) :
    rdShaped (.imp cStreamRead [rv, nv] r) = true := by
  unfold rdShaped
  simp (config := { decide := true }) only [↓reduceIte, hn]

theorem bytesOf_u8 (l : List (BitVec 8)) : bytesOf (.record (l.map .u8)) = l := by
  simp [bytesOf, List.filterMap_map]

theorem rd3_completed (q : RdSt) {rv nv : Val} {r n k : Nat} {bs l : List (BitVec 8)}
    (hr : natOf rv = some r) (hn : natOf nv = some n) (hq : rest q r = some bs)
    (hk : 0 < k) (hkn : k ≤ n) (hkc : k ≤ cap) (hl : l = bs.take k) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv]
      (some [natV (packCopy .completed k), .record (l.map .u8)])) = some (setRest q r (bs.drop k)) := by
  rw [rd3_step_of F (rdShaped_read _ (by simp [hn]))]
  unfold rdStepZ
  simp (config := { decide := true }) only [↓reduceIte, hr, hn, Option.bind_eq_bind, Option.bind_some, hq,
    natOf_natV (pack_lt hkc), copyOf_completed hkc]
  rw [bytesOf_u8]
  simp [hl, hk, hkn]

theorem rd3_dropped (q : RdSt) {rv nv : Val} {r n : Nat} (xs : Val)
    (hr : natOf rv = some r) (hn : natOf nv = some n) (hq : rest q r = some []) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv]
      (some [natV (packCopy .dropped 0), xs])) = some q := by
  rw [rd3_step_of F (rdShaped_read _ (by simp [hn]))]
  unfold rdStepZ
  simp (config := { decide := true }) only [↓reduceIte, hr, hn, Option.bind_eq_bind, Option.bind_some, hq,
    natOf_natV (by decide : packCopy .dropped 0 < 2 ^ 32), copyOf_dropped]

theorem rd3_blocked (q : RdSt) (a : List Val) (xs : Val) :
    (fsReadTh3w F).step q (.imp cStreamRead a (some [natV blocked, xs])) = some q := by
  rcases a with _ | ⟨rv, _ | ⟨nv, _ | ⟨w, rest⟩⟩⟩
  · rfl
  · rfl
  · cases hn : natOf nv with
    | none =>
      have hs : rdShaped (.imp cStreamRead [rv, nv] (some [natV blocked, xs])) = false := by
        unfold rdShaped
        simp (config := { decide := true }) only [↓reduceIte, hn, Option.isSome_none]
      simp [fsReadTh3w, hs]
    | some n =>
      rw [rd3_step_of F (rdShaped_read _ (by simp [hn]))]
      unfold rdStepZ
      have hb : natOf (natV blocked) >>= copyOf = some none := by
        rw [natOf_natV (by decide : blocked < 2 ^ 32)]; exact copyOf_blocked
      simp (config := { decide := true }) only [↓reduceIte, hn, hb]
      cases natOf rv >>= rest q <;> rfl
  · rfl

theorem rd3_none (q : RdSt) {rv nv : Val} {r : Nat} (pv xs : Val)
    (hr : natOf rv = some r) (hq : rest q r = none) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] (some [pv, xs])) = some q := by
  by_cases hs : rdShaped (.imp cStreamRead [rv, nv] (some [pv, xs])) = true
  · rw [rd3_step_of F hs]
    unfold rdStepZ
    simp (config := { decide := true }) only [↓reduceIte, hr, Option.bind_eq_bind,
      Option.bind_some, hq]
  · simp [fsReadTh3w, hs]

/-- 0.3 `read-via-stream` with its arguments: the theory records the file rest. -/
theorem rd3_rv (q : RdSt) (d : BitVec 32) (off : BitVec 64) {r fr : Nat} (hr : r < 2 ^ 32) :
    (fsReadTh3w F).step q (.imp readVia3 [.u32 d, .u64 off] (some [.record [natV r, natV fr]])) =
      some (setRest q r ((F d).drop off.toNat)) := by
  rw [rd3_step_of F rfl]
  unfold rdStepZ
  simp (config := { decide := true }) only [↓reduceIte, natOf_natV hr]

/-- 0.3 `read-via-stream` with other arguments is not constrained. -/
theorem rd3_rv_bad (q : RdSt) {a : List Val} (ha : rvArgs a = none) (ans : Option (List Val)) :
    (fsReadTh3w F).step q (.imp readVia3 a ans) = some q := by
  have hs : rdShaped (.imp readVia3 a ans) = false := by
    unfold rdShaped
    simp (config := { decide := true }) only [↓reduceIte]
    split
    · simp [rvArgs] at ha
    · rfl
  simp [fsReadTh3w, hs]

/-- Non-read 0.2 calls leave the 0.2 read theory. -/
theorem rd2_nr (q : RdSt) {f : FnName} (hf : f ∈ nrFns) (a : List Val) (n : Option (List Val)) :
    (fsRead2 F).step q (.imp f a n) = some q := by
  simp only [nrFns, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- 0.2 `read-via-stream` records the contents behind the new input stream. -/
theorem rd2_rvs (q : RdSt) (d : BitVec 32) (off : BitVec 64) (ans : Option (List Val)) :
    (fsRead2 F).step q (.imp P2.fdReadStream [.u32 d, .u64 off] ans) =
      some (match isOf ans with
        | some is => setRest q is.toNat ((F d).drop off.toNat)
        | none => q) := by
  simp only [fsRead2]
  unfold rd2Step
  simp (config := { decide := true }) only [↓reduceIte]
  unfold isOf
  split <;> split <;> simp_all

/-- What a `blocking-read` of `is` answered `ans` does to the 0.2 read state. -/
def BreadPost (q q' : RdSt) (is : BitVec 32) (ans : Option (List Val)) : Prop :=
  (∀ k, k ≠ is.toNat → rest q' k = rest q k) ∧
  (∀ bs v, rest q is.toNat = some bs → ans = some [.variant 0 (some v)] →
    bytesOf v = bs.take (bytesOf v).length ∧ rest q' is.toNat = some (bs.drop (bytesOf v).length)) ∧
  (∀ bs e, rest q is.toNat = some bs → ans = some [.variant 1 e] → bs = [] ∧ q' = q) ∧
  ((∀ v, ans ≠ some [.variant 0 (some v)]) → (∀ e, ans ≠ some [.variant 1 e]) → q' = q)

/-- Bytes: a prefix of the rest, consumed. -/
theorem bread_ok {q : RdSt} {is : BitVec 32} {bs : List (BitVec 8)} {v : Val}
    (hq : rest q is.toNat = some bs) (hb : bytesOf v = bs.take (bytesOf v).length) :
    BreadPost q (setRest q is.toNat (bs.drop (bytesOf v).length)) is (some [.variant 0 (some v)]) := by
  refine ⟨fun k hk => rest_setRest_ne q _ hk, fun bs' v' hq' hans' => ?_,
    fun bs' e hq' hans' => by simp at hans', fun h1 _ => absurd rfl (h1 v)⟩
  rw [hq] at hq'
  simp only [Option.some.injEq, List.cons.injEq, Val.variant.injEq, and_true, true_and] at hq' hans'
  subst hq' hans'
  exact ⟨hb, rest_setRest_eq _ _ _⟩

/-- An error: the end of the stream. -/
theorem bread_err {q : RdSt} {is : BitVec 32} {bs : List (BitVec 8)} {e : Option Val}
    (hq : rest q is.toNat = some bs) (hb : bs = []) : BreadPost q q is (some [.variant 1 e]) := by
  refine ⟨fun _ _ => rfl, fun bs' v hq' hans' => by simp at hans', fun bs' e' hq' _ => ?_,
    fun _ _ => rfl⟩
  rw [hq] at hq'
  simp only [Option.some.injEq] at hq'
  exact ⟨hq' ▸ hb, rfl⟩

/-- **0.2 `blocking-read` on an input stream**: the other streams keep their contents; on this
one, bytes are a prefix of the contents and consume them, an error means the end. -/
theorem rd2_bread {q q' : RdSt} {is : BitVec 32} {len : Val} {ans : Option (List Val)}
    (h : (fsRead2 F).step q (.imp P2.isBread [.u32 is, len] ans) = some q') :
    BreadPost q q' is ans := by
  simp only [fsRead2] at h
  unfold rd2Step at h
  simp (config := { decide := true }) only [↓reduceIte] at h
  split at h
  · rename_i _ _ bs v hq
    split_ifs at h with hb
    rw [← Option.some.inj h]
    exact bread_ok hq hb
  · rename_i _ _ bs e hq
    split_ifs at h with hb
    rw [← Option.some.inj h]
    exact bread_err hq hb
  · rename_i _ _ _ hno1 hno2
    rw [← Option.some.inj h]
    exact ⟨fun _ _ => rfl, fun bs v hq hans => (hno1 bs v hq hans).elim,
      fun bs e hq hans => (hno2 bs e hq hans).elim, fun _ _ => rfl⟩

end Silmaril.Wasi.Versions.P3OverP2
