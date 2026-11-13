module

public import Silmaril.Wasi.Versions.Random.Over.Defs
public import Silmaril.Wasi.Versions.Random.Thms
public import Silmaril.Wasi.Versions.Stateful.Thms

@[expose] public section

/-!
# `wasi:random` across versions: theorems

PROVED (standard axioms):

* **(b) 0.3 over 0.2**: `p3OverP2R_sat : (agP randTh2 (retG randTh3)).holds (ofSBody p3OverP2R ())`
  and **`p3OverP2R_model`**: for every host `η` of the 0.2 theory, `link η (ofSBody p3OverP2R ())`
  is a model of the 0.3 theory. The key fact is `ok3_of_ok2`: an exact answer is a short read.
* **0.2 over 0.3**: `p2OverP3R_sat`, **`p2OverP3R_model`**: for every host of the 0.3 theory,
  the accumulating component is a model of the 0.2 theory (exact lengths). `wp_fill`: under
  `randTh3`, `fill` with fuel at least the missing count returns exactly the missing bytes after
  `acc`; the fuel suffices because 0.3 answers at least one byte to a positive request.
* The OS image of (b) is in `Silmaril.Wasi.Versions.Random.Os`.
-/

namespace Silmaril.Wasi.Versions.Random

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Answers -/

/-- A stronger length check gives a stronger byte answer. -/
theorem bytesAns_mono {P Q : Nat → Bool} (h : ∀ k, P k = true → Q k = true)
    {r : Option (List Val)} (hr : bytesAns P r = true) : bytesAns Q r = true := by
  cases r with
  | none => simp [bytesAns] at hr
  | some l =>
    match l, hr with
    | [v], hr =>
      simp only [bytesAns, Bool.and_eq_true] at hr ⊢
      exact ⟨hr.1, h _ hr.2⟩
    | [], hr => simp [bytesAns] at hr
    | _ :: _ :: _, hr => simp [bytesAns] at hr

/-- The same for byte calls. -/
theorem bytesM_mono {P Q : Nat → Nat → Bool} (h : ∀ n k, P n k = true → Q n k = true)
    (a : List Val) (r : Option (List Val)) (ha : bytesM P a r = true) : bytesM Q a r = true := by
  unfold bytesM at ha ⊢
  split
  · next n => exact bytesAns_mono (h n.toNat) (by simpa using ha)
  · rfl

/-- A byte call with other arguments is unconstrained. -/
theorem bytesM_of_ne {P : Nat → Nat → Bool} {a : List Val} (h : ∀ n, a ≠ [.u64 n])
    (r : Option (List Val)) : bytesM P a r = true := by
  unfold bytesM
  split
  · next n => exact absurd rfl (h n)
  · rfl

/-- **An exact 0.2 answer is an admissible 0.3 answer** of the corresponding function. -/
theorem ok3_of_ok2 {f : FnName} (hf : f ∈ rand3Fns) {a : List Val} {r : Option (List Val)}
    (h : ok2 (.imp (to2 f) a r) = true) : ok3 (.imp f a r) = true := by
  simp only [rand3Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [to2, ok2_eq_hand, ok2H, ok3_eq_hand, ok3H, randBytes2, randBytes3, insBytes2, insBytes3, randU64_2, randU64_3,
      insU64_2, insU64_3, insSeed2, insSeed3] at h ⊢
  all_goals first
    | exact h
    | exact bytesM_mono (fun _ _ hk => shortOk_of_exactOk hk) a r h

/-- A forwarded 0.2 call: a 0.3 answer of the corresponding function is a 0.2 answer, for
calls that are not well-typed byte calls. -/
theorem ok2_of_ok3 {f : FnName} (hf : f ∈ rand2Fns) {a : List Val} {r : Option (List Val)}
    (hb : bytesCall f a = none) (h : ok3 (.imp (to3 f) a r) = true) : ok2 (.imp f a r) = true := by
  have hne : f = randBytes2 ∨ f = insBytes2 → ∀ n, a ≠ [.u64 n] := by
    rintro hf' n rfl
    simp [bytesCall, hf'] at hb
  simp only [rand2Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [to3, ok2_eq_hand, ok2H, ok3_eq_hand, ok3H, randBytes2, randBytes3, insBytes2, insBytes3, randU64_2, randU64_3,
      insU64_2, insU64_3, insSeed2, insSeed3] at h ⊢
  all_goals first
    | exact h
    | exact bytesM_of_ne (hne (Or.inl rfl)) r
    | exact bytesM_of_ne (hne (Or.inr rfl)) r

/-- A pointwise step succeeds exactly on accepted events. -/
theorem pointwise_step {ok : WEv → Bool} {q q' : Unit} {e : WEv}
    (h : (pointwise ok).step q e = some q') : ok e = true := by
  by_contra hn
  simp [pointwise, hn] at h

/-- A pointwise step on an accepted event. -/
theorem pointwise_step_of {ok : WEv → Bool} {q : Unit} {e : WEv} (h : ok e = true) :
    (pointwise ok).step q e = some () := by
  simp [pointwise, h]

/-! ## (b) 0.3 over 0.2 -/

/-- The invariant of `p3OverP2R` (none needed). -/
theorem p3OverP2R_inv : WpInv p3OverP2R () randTh2 randTh3 (fun _ _ _ => True) where
  init := trivial
  call := fun _ _ _ q _ _ _ h =>
    ⟨(), pointwise_step_of (ok3_of_ok2 q.1.2 (pointwise_step h)), trivial⟩

/-- **The component guarantee of (b) for `wasi:random`.** -/
theorem p3OverP2R_sat : (agP randTh2 (retG randTh3)).holds (ofSBody p3OverP2R ()) :=
  ag_of_wpInv p3OverP2R_inv

/-- **`wasi:random` 0.3 over 0.2**: over every host of the 0.2 theory, the composite is a model
of the 0.3 theory. -/
theorem p3OverP2R_model {Y : Sig.{0}} {η : Host Y rand2Fns} (hη : (hostSat randTh2.Accepts).holds η) :
    (hostSat randTh3.Accepts).holds (link η (ofSBody p3OverP2R ())) :=
  link_model p3OverP2R_sat hη

/-! ## 0.2 over 0.3 -/

/-- The postcondition of `fill`: the result is a byte list of `acc.length + need` bytes. -/
def FillPost (len : Nat) (a : Unit × Option (List Val)) (_ : Unit) : Prop :=
  ∃ bs : List (BitVec 8), a.2 = some [bytesV bs] ∧ bs.length = len

/-- The byte function of a 0.2 byte call. -/
theorem to3_bytes {f : FnName} (hf : f = randBytes2 ∨ f = insBytes2) :
    to3 f = randBytes3 ∨ to3 f = insBytes3 := by
  rcases hf with rfl | rfl <;> simp [to3, randBytes2, insBytes2]

/-- An accepted answer of the 0.3 byte function to a request for `m` bytes. -/
theorem ok3_bytes {g : FnName} (hg : g = randBytes3 ∨ g = insBytes3) {m : Nat}
    (hm : m < 2 ^ 64) {r : Option (List Val)}
    (h : ok3 (.imp g [.u64 (BitVec.ofNat 64 m)] r) = true) : bytesAns (shortOk m) r = true := by
  have hmod : m % 18446744073709551616 = m := Nat.mod_eq_of_lt (by simpa using hm)
  rcases hg with rfl | rfl <;>
    simpa [ok3_eq_hand, ok3H, bytesM, hmod, randBytes3, insBytes3] using h

/-- The bytes of an accepted 0.3 answer to a positive request. -/
theorem chunk_of_short {need : Nat} (hn : need ≠ 0) {r : Option (List Val)}
    (h : bytesAns (shortOk need) r = true) :
    ∃ v, r = some [v] ∧ chunkOk need v = true ∧ 0 < (bytesOf v).length := by
  cases r with
  | none => simp [bytesAns] at h
  | some l =>
    match l, h with
    | [v], h =>
      simp only [bytesAns, Bool.and_eq_true] at h
      have hk : (bytesOf v).length ≤ need ∧ 0 < (bytesOf v).length := by
        simpa [shortOk, hn] using h.2
      exact ⟨v, rfl, by simp [chunkOk, h.1, hk.1, hk.2], hk.2⟩
    | [], h => simp [bytesAns] at h
    | _ :: _ :: _, h => simp [bytesAns] at h

/-- One round of `fill`, given the claim for the remaining fuel. -/
theorem wp_fill_succ (g : {g // g ∈ rand3Fns}) (hg : g.1 = randBytes3 ∨ g.1 = insBytes3)
    (fuel : Nat) (ih : ∀ (need : Nat) (acc : List (BitVec 8)) (qT : Unit), need ≤ fuel →
      need < 2 ^ 64 → Wp randTh3 (fill g fuel need acc) (FillPost (acc.length + need)) qT)
    (need : Nat) (acc : List (BitVec 8)) (qT : Unit) (h : need ≤ fuel + 1) (hlt : need < 2 ^ 64) :
    Wp randTh3 (fill g (fuel + 1) need acc) (FillPost (acc.length + need)) qT := by
    by_cases h0 : need = 0
    · rw [h0]
      simp only [fill, ↓reduceIte]
      exact ⟨acc, rfl, rfl⟩
    simp only [fill, h0, ↓reduceIte]
    intro r qT' hstep
    obtain ⟨v, hv, hc, hpos⟩ : ∃ v, r = some [v] ∧ chunkOk need v = true ∧
        0 < (bytesOf v).length :=
      chunk_of_short h0 (ok3_bytes hg hlt (pointwise_step hstep))
    have hc' : (allU8 v = true ∧ 0 < (bytesOf v).length) ∧ (bytesOf v).length ≤ need := by
      simpa only [chunkOk, Bool.and_eq_true, decide_eq_true_eq] using hc
    have hle : (bytesOf v).length ≤ need := hc'.2
    have ih : Wp randTh3 (fill g fuel (need - (bytesOf v).length) (acc ++ bytesOf v))
        (FillPost ((acc ++ bytesOf v).length + (need - (bytesOf v).length))) qT' :=
      ih (need - (bytesOf v).length) (acc ++ bytesOf v) qT' (by omega) (by omega)
    have hlen : (acc ++ bytesOf v).length + (need - (bytesOf v).length) = acc.length + need := by
      simp only [List.length_append]
      omega
    rw [hv]
    simp only [hc, ↓reduceIte]
    rw [← hlen]
    exact ih

/-- **`fill` returns exactly the missing bytes** under `randTh3`, given enough fuel. -/
theorem wp_fill (g : {g // g ∈ rand3Fns}) (hg : g.1 = randBytes3 ∨ g.1 = insBytes3) :
    ∀ (fuel need : Nat) (acc : List (BitVec 8)) (qT : Unit), need ≤ fuel → need < 2 ^ 64 →
      Wp randTh3 (fill g fuel need acc) (FillPost (acc.length + need)) qT
  | 0, need, acc, _, h, _ => by
    have h0 : need = 0 := by omega
    rw [h0]
    simp only [fill, ↓reduceIte]
    exact ⟨acc, rfl, rfl⟩
  | fuel + 1, need, acc, qT, h, hlt => wp_fill_succ g hg fuel (wp_fill g hg fuel) need acc qT h hlt

/-- A byte call with its length. -/
theorem bytesCall_some {f : FnName} {a : List Val} {n : Nat} (h : bytesCall f a = some n) :
    (f = randBytes2 ∨ f = insBytes2) ∧ ∃ x : BitVec 64, a = [.u64 x] ∧ x.toNat = n := by
  unfold bytesCall at h
  split_ifs at h with hf
  refine ⟨hf, ?_⟩
  split at h
  · next x => exact ⟨x, rfl, Option.some.inj h⟩
  · exact absurd h (by simp)

/-- An exact byte answer of a 0.2 byte call. -/
theorem ok2_bytes {f : FnName} (hf : f = randBytes2 ∨ f = insBytes2) (x : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = x.toNat) :
    ok2 (.imp f [.u64 x] (some [bytesV bs])) = true := by
  rcases hf with rfl | rfl <;> simp [ok2_eq_hand, ok2H, bytesM, bytesAns_bytesV, exactOk, hbs, insBytes2, randBytes2]

/-- The invariant of `p2OverP3R` (none needed). -/
theorem p2OverP3R_inv : WpInv p2OverP3R () randTh3 randTh2 (fun _ _ _ => True) where
  init := trivial
  call := by
    intro s qT qG q _
    show Wp randTh3 (match bytesCall q.1.1 q.2 with
      | some n => fill (fn3 q.1.1) n n []
      | none => .call (fn3 q.1.1, q.2) fun r => .pure ((), r)) _ qT
    cases hb : bytesCall q.1.1 q.2 with
    | some n =>
      obtain ⟨hf, x, hx, rfl⟩ := bytesCall_some hb
      have hw := wp_fill (fn3 q.1.1) (to3_bytes hf) x.toNat x.toNat [] qT (le_refl _) x.isLt
      refine Wp.mono (fun a _ hp => ?_) hw
      obtain ⟨bs, ha, hbs⟩ := hp
      refine ⟨(), ?_, trivial⟩
      rw [ha, hx]
      exact pointwise_step_of (ok2_bytes hf x bs (by simpa using hbs))
    | none =>
      exact fun n _ h => ⟨(), pointwise_step_of (ok2_of_ok3 q.1.2 hb (pointwise_step h)), trivial⟩

/-- **The component guarantee of 0.2 over 0.3 for `wasi:random`.** -/
theorem p2OverP3R_sat : (agP randTh3 (retG randTh2)).holds (ofSBody p2OverP3R ()) :=
  ag_of_wpInv p2OverP3R_inv

/-- **`wasi:random` 0.2 over 0.3**: over every host of the 0.3 theory (short reads), the
accumulating composite is a model of the 0.2 theory (exact lengths). -/
theorem p2OverP3R_model {Y : Sig.{0}} {η : Host Y rand3Fns} (hη : (hostSat randTh3.Accepts).holds η) :
    (hostSat randTh2.Accepts).holds (link η (ofSBody p2OverP3R ())) :=
  link_model p2OverP3R_sat hη

end Silmaril.Wasi.Versions.Random
