module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Host3Clock
public import Silmaril.Proofs.Wasi.Versions.P3OverP2.ReadStep

/-!
# Proofs: every bounded run of `host3` satisfies the corrected read theory

`host3_fsReadTh3w`: for contents `F` whose files are shorter than `2^28` bytes, every answer
sequence of `host3 F` of fewer than `2^31` answers is accepted by `fsReadTh3w F`. Both bounds
are needed by `host3` as written: its handles are `2 |p| + 1` as `u32` (they repeat after `2^31`
answers), and a copy result `COMPLETED k` is packed as `16 k` in a `u32` (it wraps for
`k ≥ 2^28`). The original `fsReadTh3 F` fails for `host3` (`host3_zero_read`,
`host3_not_fsReadTh3`).

Invariant `H3RdI`: the theory's rest of a readable end is the host's remaining bytes (`srcOf`,
`deliveredOn`); a readable end the host never created has nothing delivered; created ends are
below `2 |p| + 1`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3

/-- An answer that is not a `read-via-stream` answer is no source. -/
theorem srcOf_single_none (r : Nat) {e : WEv}
    (hne : ∀ f d off rv x, e = .imp f [.u32 d, .u64 off] (some [.record [rv, x]]) → False) :
    srcOf r [e] = none := by
  unfold srcOf
  split
  · rename_i heq; cases heq
  · rename_i _ f d off rv x p heq
    simp only [List.cons.injEq] at heq
    exact absurd heq.1 (hne f d off rv x)
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rfl

/-- The source of a readable end, one answer at a time. -/
theorem srcOf_cons (r : Nat) (e : WEv) (l : List WEv) :
    srcOf r (e :: l) = (srcOf r [e]).or (srcOf r l) := by
  conv_lhs => unfold srcOf
  split
  · rename_i heq; cases heq
  · rename_i _ f d off rv x p heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hs : srcOf r [WEv.imp f [.u32 d, .u64 off] (some [.record [rv, x]])] =
        if f = readVia3 ∧ natOf rv = some r then some (d, off.toNat) else none := rfl
    rw [hs]
    split <;> simp
  · rename_i _ e' p hne heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [srcOf_single_none r hne]
    simp

/-- An answer that is not a read answer delivers nothing. -/
theorem deliveredOn_single_zero (r : Nat) {e : WEv}
    (hne : ∀ f rv x y items, e = .imp f (rv :: x) (some [y, items]) → False) :
    deliveredOn r [e] = 0 := by
  unfold deliveredOn
  split
  · rename_i heq; cases heq
  · rename_i _ f rv x y items p heq
    simp only [List.cons.injEq] at heq
    exact absurd heq.1 (hne f rv x y items)
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rfl

/-- The bytes delivered, one answer at a time. -/
theorem deliveredOn_cons (r : Nat) (e : WEv) (l : List WEv) :
    deliveredOn r (e :: l) = deliveredOn r [e] + deliveredOn r l := by
  conv_lhs => unfold deliveredOn
  split
  · rename_i heq; cases heq
  · rename_i _ f rv x y items p heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  · rename_i _ e' p hne heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [deliveredOn_single_zero r hne]
    simp

/-- The source of a readable end after one more answer. -/
theorem srcOf_append (r : Nat) (p : List WEv) (e : WEv) :
    srcOf r (p ++ [e]) = (srcOf r p).or (srcOf r [e]) := by
  induction p with
  | nil => simp [srcOf]
  | cons e' p ih => rw [List.cons_append, srcOf_cons, ih, srcOf_cons r e' p, Option.or_assoc]

/-- The bytes delivered after one more answer. -/
theorem deliveredOn_append (r : Nat) (p : List WEv) (e : WEv) :
    deliveredOn r (p ++ [e]) = deliveredOn r p + deliveredOn r [e] := by
  induction p with
  | nil => simp [deliveredOn]
  | cons e' p ih => rw [List.cons_append, deliveredOn_cons, ih, deliveredOn_cons r e' p]; omega

/-- Only `read-via-stream` creates sources. -/
theorem srcOf_single_ne (r : Nat) {f : FnName} (hf : f ≠ readVia3) (a : List Val)
    (ans : Option (List Val)) : srcOf r [.imp f a ans] = none := by
  unfold srcOf
  split
  · rename_i heq; cases heq
  · rename_i _ f' d off rv x p heq
    simp only [List.cons.injEq, WEv.imp.injEq] at heq
    obtain ⟨⟨rfl, -, -⟩, rfl⟩ := heq
    simp [hf, srcOf]
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rfl

/-- Only `stream.read` delivers. -/
theorem deliveredOn_single_ne (r : Nat) {f : FnName} (hf : f ≠ cStreamRead) (a : List Val)
    (ans : Option (List Val)) : deliveredOn r [.imp f a ans] = 0 := by
  unfold deliveredOn
  split
  · rename_i heq; cases heq
  · rename_i _ f' rv x y items p heq
    simp only [List.cons.injEq, WEv.imp.injEq] at heq
    obtain ⟨⟨rfl, -, -⟩, rfl⟩ := heq
    simp [hf, deliveredOn]
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rfl

/-- The source created by a `read-via-stream` answer. -/
theorem srcOf_single_rv (r r0 r1 : Nat) (hr0 : r0 < 2 ^ 32) (d : BitVec 32) (off : BitVec 64) :
    srcOf r [.imp readVia3 [.u32 d, .u64 off] (some [.record [natV r0, natV r1]])] =
      if r0 = r then some (d, off.toNat) else none := by
  show (if readVia3 = readVia3 ∧ natOf (natV r0) = some r then some (d, off.toNat) else srcOf r []) = _
  rw [natOf_natV hr0]
  by_cases h : r0 = r <;> simp [h, srcOf]

/-- An ill-shaped `read-via-stream` creates no source. -/
theorem srcOf_single_bad (r : Nat) {a : List Val} (ha : rvArgs a = none) (ans : Option (List Val)) :
    srcOf r [.imp readVia3 a ans] = none := by
  unfold srcOf
  split
  · rename_i heq; cases heq
  · rename_i _ f' d off rv x p heq
    simp only [List.cons.injEq, WEv.imp.injEq] at heq
    obtain ⟨⟨-, rfl, -⟩, -⟩ := heq
    simp [rvArgs] at ha
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    rfl

/-- The bytes delivered by one `stream.read` answer. -/
theorem deliveredOn_single_sr (r : Nat) (rv : Val) (tl : List Val) (x items : Val) :
    deliveredOn r [.imp cStreamRead (rv :: tl) (some [x, items])] =
      if natOf rv = some r then (bytesOf items).length else 0 := by
  show (if cStreamRead = cStreamRead ∧ natOf rv = some r then (bytesOf items).length else 0) +
    deliveredOn r [] = _
  simp [deliveredOn]

/-- A `stream.read` without arguments delivers nothing. -/
theorem deliveredOn_single_nil (r : Nat) (ans : Option (List Val)) :
    deliveredOn r [.imp cStreamRead [] ans] = 0 := by
  unfold deliveredOn
  rfl

variable (F : BitVec 32 → List (BitVec 8))

/-- A completed copy of fewer than `2^28` items decodes. -/
theorem copyOf_completed' {k : Nat} (hk : k < 2 ^ 28) :
    copyOf (packCopy .completed k) = some (some (.completed, k)) := by
  have hb : packCopy .completed k ≠ blocked := by
    simp only [packCopy, CopyResult.toNat, blocked]; omega
  have _ := hk
  have h1 : packCopy .completed k % 16 = 0 := by simp only [packCopy, CopyResult.toNat]; omega
  have h2 : packCopy .completed k / 16 = k := by simp only [packCopy, CopyResult.toNat]; omega
  simp only [copyOf, hb, h1, h2, ↓reduceIte]

/-- `stream.read` completing with `k` items, `k < 2^28` (zero only for a zero-length read). -/
theorem rd3_completedZ (q : RdSt) {rv nv : Val} {r n k : Nat} {bs l : List (BitVec 8)}
    (hr : natOf rv = some r) (hn : natOf nv = some n) (hq : rest q r = some bs)
    (hk : 0 < k ∨ n = 0) (hkn : k ≤ n) (hk28 : k < 2 ^ 28) (hl : l = bs.take k) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv]
      (some [natV (packCopy .completed k), .record (l.map .u8)])) = some (setRest q r (bs.drop k)) := by
  have hlt : packCopy .completed k < 2 ^ 32 := by simp only [packCopy, CopyResult.toNat]; omega
  rw [rd3_step_of F (rdShaped_read _ (by simp [hn]))]
  unfold rdStepZ
  simp (config := { decide := true }) only [↓reduceIte, hr, hn, Option.bind_eq_bind, Option.bind_some,
    hq, natOf_natV hlt, copyOf_completed' hk28]
  rw [bytesOf_u8]
  simp [hl, hk, hkn]

/-- `stream.read` of a non-handle is not constrained. -/
theorem rd3_rvnone (q : RdSt) {rv nv : Val} (hr : natOf rv = none) (ans : Option (List Val)) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] ans) = some q := by
  show (if rdShaped _ then rdStepZ F q _ else some q) = some q
  split
  · unfold rdStepZ
    simp (config := { decide := true }) only [↓reduceIte, Option.bind_eq_bind]
    split <;> simp_all
  · rfl

/-- `stream.read` of a non-`u32` count is not constrained. -/
theorem rd3_nvnone (q : RdSt) {rv nv : Val} (hn : natOf nv = none) (ans : Option (List Val)) :
    (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] ans) = some q := by
  have hs : rdShaped (.imp cStreamRead [rv, nv] ans) = false := by
    unfold rdShaped
    simp (config := { decide := true }) only [↓reduceIte, hn, Option.isSome_none]
  simp [fsReadTh3w, hs]

/-- `stream.read` with other than two arguments is not constrained. -/
theorem rd3_not2 (q : RdSt) {a : List Val} (ha : ∀ x y, a ≠ [x, y]) (ans : Option (List Val)) :
    (fsReadTh3w F).step q (.imp cStreamRead a ans) = some q := by
  show (if rdShaped _ then rdStepZ F q _ else some q) = some q
  split
  · unfold rdStepZ
    simp (config := { decide := true }) only [↓reduceIte]
    split
    · rename_i x y _ _ _; exact absurd rfl (ha x y)
    · rfl
  · rfl

/-- Other functions are not constrained by the read theory. -/
theorem rd3_other (q : RdSt) {f : FnName} (h1 : f ≠ readVia3) (h2 : f ≠ cStreamRead) (a : List Val)
    (ans : Option (List Val)) : (fsReadTh3w F).step q (.imp f a ans) = some q := by
  show (if rdShaped _ then rdStepZ F q _ else some q) = some q
  split
  · unfold rdStepZ; simp [h1, h2]
  · rfl

/-- The read invariant of `host3`. -/
def H3RdI (p : List WEv) (q : RdSt) : Prop :=
  (∀ r, rest q r = (srcOf r p).map fun _ => remaining F p r) ∧
  (∀ r, srcOf r p = none → deliveredOn r p = 0) ∧
  (∀ r x, srcOf r p = some x → r < 2 * p.length + 1)

/-- Taking as many as `take n` took. -/
theorem take_length_take (l : List (BitVec 8)) (n : Nat) : l.take (l.take n).length = l.take n := by
  rw [List.length_take]
  by_cases h : n ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-- An answer that changes neither the sources nor the deliveries keeps the invariant. -/
theorem H3RdI.keep {p : List WEv} {q : RdSt} (h : H3RdI F p q) (e : WEv)
    (hs : ∀ r, srcOf r [e] = none) (hd : ∀ r, deliveredOn r [e] = 0) : H3RdI F (p ++ [e]) q := by
  have hsrc : ∀ r, srcOf r (p ++ [e]) = srcOf r p := fun r => by
    rw [srcOf_append, hs]; cases srcOf r p <;> rfl
  have hdel : ∀ r, deliveredOn r (p ++ [e]) = deliveredOn r p := fun r => by
    rw [deliveredOn_append, hd]; rfl
  refine ⟨fun r => ?_, fun r hr => ?_, fun r x hr => ?_⟩
  · rw [h.1 r, hsrc]; simp only [remaining, hsrc, hdel]
  · rw [hdel]; exact h.2.1 r ((hsrc r) ▸ hr)
  · have := h.2.2 r x ((hsrc r) ▸ hr); simp; omega

/-- Sources stay below the bound after a new source `r0` below it. -/
theorem rv_bound {p : List WEv} {q : RdSt} (h : H3RdI F p q) {e : WEv} {r0 r : Nat}
    {d : BitVec 32} {off : Nat} {x : BitVec 32 × Nat} (hr0 : r0 < 2 * (p ++ [e]).length + 1)
    (hr : (srcOf r p).or (if r0 = r then some (d, off) else none) = some x) :
    r < 2 * (p ++ [e]).length + 1 := by
  cases hs : srcOf r p with
  | none =>
    rw [hs, Option.none_or] at hr
    split at hr
    · omega
    · cases hr
  | some y =>
    have hlt : r < 2 * p.length + 1 := h.2.2 r y hs
    simp only [List.length_append, List.length_singleton]
    omega

/-- A new source `r0` (fresh, delivering nothing) keeps the invariant with the whole rest. -/
theorem H3RdI.rv {p : List WEv} {q : RdSt} (h : H3RdI F p q) {e : WEv} {r0 : Nat} {d : BitVec 32}
    {off : Nat} (hs0 : srcOf r0 p = none) (hr0 : r0 < 2 * (p ++ [e]).length + 1)
    (hsrc1 : ∀ r, srcOf r [e] = if r0 = r then some (d, off) else none)
    (hd0 : ∀ r, deliveredOn r [e] = 0) :
    H3RdI F (p ++ [e]) (setRest q r0 ((F d).drop off)) := by
  have hsrc : ∀ r, srcOf r (p ++ [e]) = (srcOf r p).or (if r0 = r then some (d, off) else none) :=
    fun r => by rw [srcOf_append, hsrc1]
  have hdel : ∀ r, deliveredOn r (p ++ [e]) = deliveredOn r p := fun r => by
    rw [deliveredOn_append, hd0]; rfl
  refine ⟨fun r => ?_, fun r hr => ?_, fun r x hr => ?_⟩
  · by_cases he : r = r0
    · subst he
      rw [rest_setRest_eq]
      simp only [remaining, hsrc, hs0, hdel, ite_true, Option.none_or, Option.map_some,
        h.2.1 _ hs0, List.drop_zero]
    · rw [rest_setRest_ne _ _ he, h.1 r]
      simp only [remaining, hsrc, hdel, Ne.symm he, ite_false, Option.or_none]
  · rw [hdel]
    rw [hsrc] at hr
    exact h.2.1 r (Option.or_eq_none_iff.1 hr).1
  · rw [hsrc] at hr
    exact rv_bound F h hr0 hr

/-- The next handle of `host3` is not a source yet. -/
theorem H3RdI.fresh {p : List WEv} {q : RdSt} (hI : H3RdI F p q) :
    srcOf (2 * p.length + 1) p = none := by
  cases hs : srcOf (2 * p.length + 1) p with
  | none => rfl
  | some x => exact absurd (hI.2.2 _ x hs) (by omega)

/-- `read-via-stream` of `host3`. -/
theorem host3_rd_rv {p : List WEv} {q : RdSt} (hI : H3RdI F p q) (hp : 2 * p.length + 3 < 2 ^ 32)
    (a : List Val) :
    ∃ q', (fsReadTh3w F).step q (.imp readVia3 a (host3 F p readVia3 a)) = some q' ∧
      H3RdI F (p ++ [.imp readVia3 a (host3 F p readVia3 a)]) q' := by
  have hh : host3 F p readVia3 a =
      some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]] := rfl
  rw [hh]
  have hd0 : ∀ r, deliveredOn r [.imp readVia3 a
      (some [.record [natV (2 * p.length + 1), natV (2 * p.length + 2)]])] = 0 :=
    fun r => deliveredOn_single_ne r (by decide) _ _
  cases hra : rvArgs a with
  | none => exact ⟨q, rd3_rv_bad F q hra _, hI.keep F _ (fun r => srcOf_single_bad r hra _) hd0⟩
  | some x =>
    obtain ⟨d, off⟩ := x
    have ha : a = [.u32 d, .u64 off] := by
      match a, hra with
      | [.u32 _, .u64 _], h => simp only [rvArgs, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]
    subst ha
    exact ⟨_, rd3_rv F q d off (by omega), hI.rv F (hI.fresh F) (by simp)
      (fun r => srcOf_single_rv r _ _ (by omega) d off) hd0⟩

/-- A `stream.read` of `r1` delivering `k` bytes advances `r1` by `k`. -/
theorem H3RdI.sr {p : List WEv} {q : RdSt} (h : H3RdI F p q) {e : WEv} {r1 k : Nat}
    {x : BitVec 32 × Nat} (hs : srcOf r1 p = some x) (hs1 : ∀ r, srcOf r [e] = none)
    (hd1 : ∀ r, deliveredOn r [e] = if r1 = r then k else 0) :
    H3RdI F (p ++ [e]) (setRest q r1 ((remaining F p r1).drop k)) := by
  have hsrc : ∀ r, srcOf r (p ++ [e]) = srcOf r p := fun r => by
    rw [srcOf_append, hs1]; cases srcOf r p <;> rfl
  have hdel : ∀ r, deliveredOn r (p ++ [e]) = deliveredOn r p + if r1 = r then k else 0 :=
    fun r => by rw [deliveredOn_append, hd1]
  refine ⟨fun r => ?_, fun r hr' => ?_, fun r y hr' => ?_⟩
  · by_cases he : r = r1
    · subst he
      rw [rest_setRest_eq]
      simp only [remaining, hsrc, hs, Option.map_some, hdel, ite_true, List.drop_drop,
        Nat.add_assoc]
    · rw [rest_setRest_ne _ _ he, h.1 r]
      simp only [remaining, hsrc, hdel, Ne.symm he, ite_false, Nat.add_zero]
  · rw [hsrc] at hr'
    have hne : ¬ r1 = r := fun he => by subst he; rw [hs] at hr'; cases hr'
    rw [hdel, h.2.1 r hr']
    simp [hne]
  · rw [hsrc] at hr'
    have hlt : r < 2 * p.length + 1 := h.2.2 r y hr'
    simp only [List.length_append, List.length_singleton]
    omega

/-- `stream.read r1 n` of `host3` on a stream with bytes left: `COMPLETED k`. -/
theorem host3_rd_completed (hF : ∀ d, (F d).length < 2 ^ 28) {p : List WEv} {q : RdSt}
    (hI : H3RdI F p q) {rv nv : Val} {r1 n : Nat} (hr : natOf rv = some r1)
    (hn : natOf nv = some n) {x : BitVec 32 × Nat} (hs : srcOf r1 p = some x)
    (hq : rest q r1 = some (remaining F p r1)) (hrem : remaining F p r1 ≠ [])
    (hra : readArgs [rv, nv] = (r1, n)) (hs0 : ∀ r ans, srcOf r [.imp cStreamRead [rv, nv] ans] = none) :
    ∃ q', (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] (some [natV (readCode F p [rv, nv]),
      bytesV ((remaining F p r1).take n)])) = some q' ∧ H3RdI F (p ++ [.imp cStreamRead [rv, nv]
      (some [natV (readCode F p [rv, nv]), bytesV ((remaining F p r1).take n)])]) q' := by
  obtain ⟨d, off⟩ := x
  have hcode : readCode F p [rv, nv] = packCopy .completed ((remaining F p r1).take n).length := by
    simp [readCode, hra, hrem, readItems]
  have hremlen : (remaining F p r1).length ≤ (F d).length := by
    simp only [remaining, hs, List.length_drop]; omega
  have hk28 : ((remaining F p r1).take n).length < 2 ^ 28 := by
    have := hF d; simp only [List.length_take]; omega
  have hk0 : 0 < ((remaining F p r1).take n).length ∨ n = 0 := by
    have : 0 < (remaining F p r1).length := List.length_pos_iff.2 hrem
    simp only [List.length_take]; omega
  have hkn : ((remaining F p r1).take n).length ≤ n := by simp only [List.length_take]; omega
  rw [hcode]
  refine ⟨_, rd3_completedZ F q hr hn hq hk0 hkn hk28 (take_length_take _ n).symm,
    hI.sr F hs (hs0 · _) (fun r => ?_)⟩
  rw [deliveredOn_single_sr, hr, bytesV, bytesOf_u8]
  by_cases he : r1 = r <;> simp [he]

/-- `stream.read r1 n` of `host3` on a stream with a source. -/
theorem host3_rd_src (hF : ∀ d, (F d).length < 2 ^ 28) {p : List WEv} {q : RdSt} (hI : H3RdI F p q)
    {rv nv : Val} {r1 n : Nat} (hr : natOf rv = some r1) (hn : natOf nv = some n)
    {x : BitVec 32 × Nat} (hs : srcOf r1 p = some x)
    (hs0 : ∀ r ans, srcOf r [.imp cStreamRead [rv, nv] ans] = none) :
    ∃ q', (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] (host3 F p cStreamRead [rv, nv])) =
      some q' ∧ H3RdI F (p ++ [.imp cStreamRead [rv, nv] (host3 F p cStreamRead [rv, nv])]) q' := by
  obtain ⟨d, off⟩ := x
  have hra : readArgs [rv, nv] = (r1, n) := by simp [readArgs, hr, hn]
  have hh : host3 F p cStreamRead [rv, nv] =
      some [natV (readCode F p [rv, nv]), bytesV (readItems F p [rv, nv])] := rfl
  have hq : rest q r1 = some (remaining F p r1) := by rw [hI.1 r1, hs]; rfl
  have hitems : readItems F p [rv, nv] = (remaining F p r1).take n := by simp [readItems, hra]
  rw [hh, hitems]
  by_cases hrem : remaining F p r1 = []
  · have hcode : readCode F p [rv, nv] = packCopy .dropped 0 := by simp [readCode, hra, hrem]
    rw [hcode]
    refine ⟨q, rd3_dropped F q _ hr hn (hrem ▸ hq), hI.keep F _ (hs0 · _) (fun r => ?_)⟩
    rw [deliveredOn_single_sr, hrem]
    simp [bytesV, bytesOf]
  · exact host3_rd_completed F hF hI hr hn hs hq hrem hra hs0

/-- A `stream.read` that delivers nothing keeps the invariant. -/
theorem H3RdI.sr0 {p : List WEv} {q : RdSt} (hI : H3RdI F p q) {rv : Val} {tl : List Val}
    (hi : readItems F p (rv :: tl) = []) :
    H3RdI F (p ++ [.imp cStreamRead (rv :: tl) (host3 F p cStreamRead (rv :: tl))]) q := by
  refine hI.keep F _ (fun r => srcOf_single_ne r (by decide) _ _) (fun r => ?_)
  show deliveredOn r [.imp cStreamRead (rv :: tl)
    (some [natV (readCode F p (rv :: tl)), bytesV (readItems F p (rv :: tl))])] = 0
  rw [deliveredOn_single_sr, hi]
  simp [bytesV, bytesOf]

/-- `stream.read rv nv` of `host3`. -/
theorem host3_rd_sr2 (hF : ∀ d, (F d).length < 2 ^ 28) {p : List WEv} {q : RdSt}
    (hI : H3RdI F p q) (rv nv : Val) :
    ∃ q', (fsReadTh3w F).step q (.imp cStreamRead [rv, nv] (host3 F p cStreamRead [rv, nv])) =
      some q' ∧ H3RdI F (p ++ [.imp cStreamRead [rv, nv] (host3 F p cStreamRead [rv, nv])]) q' := by
  have hs0 : ∀ r ans, srcOf r [.imp cStreamRead [rv, nv] ans] = none :=
    fun r ans => srcOf_single_ne r (by decide) _ ans
  cases hr : natOf rv with
  | none =>
    refine ⟨q, rd3_rvnone F q hr _, hI.keep F _ (hs0 · _) (fun r => ?_)⟩
    show deliveredOn r [.imp cStreamRead [rv, nv] (some [_, _])] = 0
    rw [deliveredOn_single_sr, hr]
    simp
  | some r1 =>
    cases hn : natOf nv with
    | none => exact ⟨q, rd3_nvnone F q hn _, hI.sr0 F (by simp [readItems, readArgs, hn])⟩
    | some n =>
      cases hs : srcOf r1 p with
      | some x => exact host3_rd_src F hF hI hr hn hs hs0
      | none =>
        have hq : rest q r1 = none := by rw [hI.1 r1, hs]; rfl
        have hrem : remaining F p r1 = [] := by simp [remaining, hs]
        exact ⟨q, rd3_none F q _ _ hr hq,
          hI.sr0 F (by simp [readItems, readArgs, hr, hn, hrem])⟩

/-- `stream.read` of `host3`. -/
theorem host3_rd_sr (hF : ∀ d, (F d).length < 2 ^ 28) {p : List WEv} {q : RdSt}
    (hI : H3RdI F p q) (a : List Val) :
    ∃ q', (fsReadTh3w F).step q (.imp cStreamRead a (host3 F p cStreamRead a)) = some q' ∧
      H3RdI F (p ++ [.imp cStreamRead a (host3 F p cStreamRead a)]) q' := by
  have hs0 : ∀ r ans, srcOf r [.imp cStreamRead a ans] = none :=
    fun r ans => srcOf_single_ne r (by decide) a ans
  rcases a with _ | ⟨rv, _ | ⟨nv, _ | ⟨w, tl⟩⟩⟩
  · exact ⟨q, rd3_not2 F q (fun _ _ h => by cases h) _,
      hI.keep F _ (hs0 · _) (fun r => deliveredOn_single_nil r _)⟩
  · exact ⟨q, rd3_not2 F q (fun _ _ h => by cases h) _, hI.sr0 F rfl⟩
  · exact host3_rd_sr2 F hF hI rv nv
  · exact ⟨q, rd3_not2 F q (fun _ _ h => by cases h) _, hI.sr0 F rfl⟩

/-- One answer of `host3` keeps the invariant. -/
theorem host3_rd_step (hF : ∀ d, (F d).length < 2 ^ 28) {p : List WEv} {q : RdSt}
    (hI : H3RdI F p q) (hp : 2 * p.length + 3 < 2 ^ 32) (f : FnName) (a : List Val) :
    ∃ q', (fsReadTh3w F).step q (.imp f a (host3 F p f a)) = some q' ∧
      H3RdI F (p ++ [.imp f a (host3 F p f a)]) q' := by
  by_cases h1 : f = readVia3
  · subst h1; exact host3_rd_rv F hI hp a
  · by_cases h2 : f = cStreamRead
    · subst h2; exact host3_rd_sr F hF hI a
    · exact ⟨q, rd3_other F q h1 h2 _ _, hI.keep F _ (fun r => srcOf_single_ne r h1 a _)
        (fun r => deliveredOn_single_ne r h2 _ _)⟩

/-- **Every run of `host3 F` with fewer than `2^31` answers, on files shorter than `2^28` bytes,
is accepted by the corrected read theory.** -/
theorem host3_fsReadTh3w_run (hF : ∀ d, (F d).length < 2 ^ 28) :
    ∀ t, Follows (host3 F) t → t.length < 2 ^ 31 →
      ∃ q, (fsReadTh3w F).run (fsReadTh3w F).init t = some q ∧ H3RdI F t q := by
  intro t
  induction t using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨[], rfl, fun r => ?_, fun r _ => rfl, fun r x h => by cases h⟩
    rfl
  | append_singleton p e ih =>
    intro ht hlen
    simp only [List.length_append, List.length_singleton] at hlen
    obtain ⟨q, hq, hI⟩ := ih (follows_init ht) (by omega)
    rw [Protocol.run_concat, hq, Option.bind_some]
    cases e with
    | imp f a r =>
      have hr := follows_last ht
      subst hr
      exact host3_rd_step F hF hI (by omega) f a
    | req f a => exact ⟨q, rfl, hI.keep F _ (fun _ => rfl) (fun _ => rfl)⟩
    | call f a => exact ⟨q, rfl, hI.keep F _ (fun _ => rfl) (fun _ => rfl)⟩
    | ret f a r => exact ⟨q, rfl, hI.keep F _ (fun _ => rfl) (fun _ => rfl)⟩

/-- **`host3 F` satisfies the corrected read theory on runs of fewer than `2^31` answers**, for
files shorter than `2^28` bytes. -/
theorem host3_fsReadTh3w {Y : Sig.{0}} {I : Set FnName} (hF : ∀ d, (F d).length < 2 ^ 28) :
    (hostSat fun t => t.length < 2 ^ 31 → (fsReadTh3w F).Accepts t).holds
      (concrete (Y := Y) (I := I) (host3 F)) :=
  concrete_sat _ fun t ht hlen => by
    obtain ⟨q, hq, -⟩ := host3_fsReadTh3w_run F hF t ht hlen
    unfold Protocol.Accepts
    rw [hq]
    rfl

end Silmaril.Wasi.Versions.P3OverP2
