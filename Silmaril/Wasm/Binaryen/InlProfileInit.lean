module

public import Silmaril.Wasm.Binaryen.InlSeg
public import Silmaril.Wasm.Binaryen.GrowWrapperRun
public import Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion

@[expose] public section

/-! # Forced initialization of an inlined activation

Parameter stores and local zeroing form a uniquely forced finite prefix, even
when the following body has nondeterministic numerical or allocation behaviour.
These are the same endpoints and local-layout facts as `InlSim.sets_run` and
`zeros_run`, with uniqueness at every intermediate reduction. No deterministic
numerical profile is required; execution uses the optimizer's closed host.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile}

/-- A finite initialization prefix made entirely of pending local writes.
Unlike a generic forced path, this retains enough structure to lift every step
through values, suffixes and runtime labels, handlers and frames. -/
inductive Initialization {H : Type} : Config H → Config H → Prop where
  | done (c : Config H) : Initialization c c
  | step {c d e : Config H} (write : CoalesceLocalsLite.Completion c d)
      (tail : Initialization d e) : Initialization c e

namespace Initialization

/-- Every pending local write is uniquely forced at an arbitrary profile. -/
theorem forced {c d : Config H} (init : Initialization c d) :
    GrowWrapper.Forced (P := P) c d := by
  induction init with
  | done c => exact .done c
  | step write _ ih => exact .step write.step write.unique ih

theorem trans {a b c : Config H} (first : Initialization a b)
    (second : Initialization b c) : Initialization a c := by
  induction first with
  | done => exact second
  | step write _ ih => exact .step write (ih second)

/-- Preserve each actual initialization write under an outer value prefix and
arbitrary following code. The endpoint remains executable. -/
theorem context {c d : Config H} (init : Initialization c d)
    (vs : List Val) (rest : List Admin) :
    Initialization ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ d.code ++ rest⟩ := by
  induction init with
  | done => exact .done _
  | step write _ ih => exact .step (write.context vs rest) ih

theorem label {c d : Config H} (init : Initialization c d) (n : Nat) (cont : List Instr) :
    Initialization ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨d.store, d.frame, [.label n cont d.code]⟩ := by
  induction init with
  | done => exact .done _
  | @step c d e write _ ih =>
    have sameStore := write.store
    cases c
    cases d
    subst sameStore
    exact .step (CoalesceLocalsLite.Completion.label write [] n cont []) ih

theorem handler {c d : Config H} (init : Initialization c d) (n : Nat) (cs : List Catch) :
    Initialization ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨d.store, d.frame, [.handler n cs d.code]⟩ := by
  induction init with
  | done => exact .done _
  | @step c d e write _ ih =>
    have sameStore := write.store
    cases c
    cases d
    subst sameStore
    exact .step (CoalesceLocalsLite.Completion.handler write [] n cs []) ih

theorem frame {c d : Config H} (init : Initialization c d) (n : Nat) (f : Frame) :
    Initialization ⟨c.store, f, [.frame n c.frame c.code]⟩
      ⟨d.store, f, [.frame n d.frame d.code]⟩ := by
  induction init with
  | done => exact .done _
  | @step c d e write _ ih =>
    have sameStore := write.store
    cases c
    cases d
    subst sameStore
    exact .step (CoalesceLocalsLite.Completion.frame write f [] n []) ih

end Initialization

/-- The stores of the arguments are a forced prefix under any numeric profile. -/
theorem sets_initializes {s : Store H} {M : ModuleInst} {k base : Nat} {R : List Admin} :
    ∀ (V : List Val) (xs : List LocalIdx) (fl : List (Option Val)),
    V.length = xs.length → (∀ j x, xs[j]? = some x → x.toNat = base + j) →
    (∀ j < xs.length, base + j < fl.length) →
    ∃ fl', Initialization
        ⟨s, ⟨fl, M⟩, [.label k [] (vals V ++ expression (xs.reverse.map .localSet) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < V.length, fl'[base + j]? = some V[j]?) ∧
      (∀ i, (i < base ∨ base + V.length ≤ i) → fl'[i]? = fl[i]?)
  | V, xs, fl, hl, hx, hb => by
    induction V using List.reverseRecOn generalizing xs fl with
    | nil =>
      have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst this
      exact ⟨fl, by simpa [expression] using
        (Initialization.done ⟨s, ⟨fl, M⟩, [.label k [] R]⟩),
        rfl, fun j hj => by simp at hj,
        fun _ _ => rfl⟩
    | append_singleton V v ih =>
      obtain ⟨xs', x, rfl⟩ : ∃ xs' x, xs = xs' ++ [x] := by
        have hne : xs ≠ [] := by
          rintro rfl
          simp at hl
        exact ⟨xs.dropLast, xs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
      have hxv : x.toNat = base + V.length := by
        have := hx xs'.length x (by simp)
        rw [this, hl]
      have hx' : ∀ j y, xs'[j]? = some y → y.toNat = base + j := fun j y hj =>
        hx j y (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj)
      have hxlt : x.toNat < fl.length := by
        have := hb xs'.length (by simp)
        omega
      have completion : CoalesceLocalsLite.Completion
          ⟨s, ⟨fl, M⟩, [.label k [] (vals (V ++ [v]) ++
            expression ((xs' ++ [x]).reverse.map .localSet) ++ R)]⟩
          ⟨s, ⟨fl.set x.toNat (some v), M⟩, [.label k [] (vals V ++
            expression (xs'.reverse.map .localSet) ++ R)]⟩ := by
        simpa [vals, expression, List.append_assoc, Frame.setLocal] using
          CoalesceLocalsLite.Completion.label
            (CoalesceLocalsLite.Completion.set s ⟨fl, M⟩ V v x
              (expression (xs'.reverse.map .localSet) ++ R) hxlt) [] k [] []
      obtain ⟨fl', hsteps, hlen, hmid, hout⟩ := ih xs' (fl.set x.toNat (some v)) hl hx'
        (fun j hj => by
          have := hb j (by simp; omega)
          rw [List.length_set]; exact this)
      refine ⟨fl', Initialization.step completion hsteps,
        by rw [hlen, List.length_set], fun j hj => ?_, fun i hi => ?_⟩
      · simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_ge j V.length with hj' | hj'
        · rw [hmid j hj', List.getElem?_append_left hj']
        · have : j = V.length := by omega
          subst this
          rw [hout _ (.inr (by omega)), ← hxv, List.getElem?_set_self hxlt]
          simp
      · simp only [List.length_append, List.length_singleton] at hi
        rw [hout i (by omega), List.getElem?_set_ne (by omega)]

/-- Reinitializing the callee locals is a forced prefix under any numeric profile. -/
theorem zeros_initializes {s : Store H} {M : ModuleInst} {k : Nat} {R : List Admin} :
    ∀ (zs : List Instr) (vs : List Val) (xs : List LocalIdx) (fl : List (Option Val)) (b : Nat),
    zs.length = xs.length → List.Forall₂ (fun z v => (Admin.plain z).val? = some v) zs vs →
    (∀ j x, xs[j]? = some x → x.toNat = b + j) → (∀ j < xs.length, b + j < fl.length) →
    ∃ fl', Initialization ⟨s, ⟨fl, M⟩, [.label k [] (expression (zerosI zs xs) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < vs.length, fl'[b + j]? = some vs[j]?) ∧
      (∀ i, (i < b ∨ b + vs.length ≤ i) → fl'[i]? = fl[i]?)
  | [], [], xs, fl, b, _, .nil, _, _ =>
    ⟨fl, by simpa [zerosI, expression] using
      (Initialization.done ⟨s, ⟨fl, M⟩, [.label k [] R]⟩),
      rfl, fun j hj => by simp at hj, fun _ _ => rfl⟩
  | z :: zs, v :: vs, x :: xs, fl, b, hl, .cons hz hzs, hx, hb => by
    have hx0 : x.toNat = b := by simpa using hx 0 x rfl
    have hxlt : x.toNat < fl.length := by have := hb 0 (by simp); omega
    have hz' : Admin.plain z = v.toAdmin := Admin.eq_of_val? hz
    have completion : CoalesceLocalsLite.Completion
        ⟨s, ⟨fl, M⟩, [.label k [] (expression (zerosI (z :: zs) (x :: xs)) ++ R)]⟩
        ⟨s, ⟨fl.set x.toNat (some v), M⟩, [.label k [] (expression (zerosI zs xs) ++ R)]⟩ := by
      simpa [zerosI, expression, hz', vals, Frame.setLocal] using
        CoalesceLocalsLite.Completion.label
          (CoalesceLocalsLite.Completion.set s ⟨fl, M⟩ [] v x
            (expression (zerosI zs xs) ++ R) hxlt) [] k [] []
    obtain ⟨fl', hsteps, hlen, hmid, hout⟩ := zeros_initializes zs vs xs (fl.set x.toNat (some v)) (b + 1)
      (by simpa using hl) hzs
      (fun j y hy => by have := hx (j + 1) y (by simpa using hy); omega)
      (fun j hj => by have := hb (j + 1) (by simp; omega); simp; omega)
    refine ⟨fl', Initialization.step completion hsteps,
      by rw [hlen, List.length_set], ?_, ?_⟩
    · intro j hj
      rcases j with _ | j
      · rw [Nat.add_zero, hout b (.inl (by omega)), ← hx0, List.getElem?_set_self hxlt]; rfl
      · have := hmid j (by simp at hj; omega)
        rw [show b + (j + 1) = b + 1 + j by omega, this]
        rfl
    · intro i hi
      have hi' : i < b ∨ b + vs.length + 1 ≤ i := by
        rcases hi with hi | hi
        · exact .inl hi
        · right; simp only [List.length_cons] at hi; omega
      rw [hout i (by omega), List.getElem?_set_ne (by omega)]
  | [], _ :: _, _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _, _ => by cases h
  | _ :: _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-- Existing forced-prefix API, projected from the stronger initialization path. -/
theorem sets_forced {s : Store H} {M : ModuleInst} {k base : Nat} {R : List Admin} :
    ∀ (V : List Val) (xs : List LocalIdx) (fl : List (Option Val)),
    V.length = xs.length → (∀ j x, xs[j]? = some x → x.toNat = base + j) →
    (∀ j < xs.length, base + j < fl.length) →
    ∃ fl', GrowWrapper.Forced (P := P)
        ⟨s, ⟨fl, M⟩, [.label k [] (vals V ++ expression (xs.reverse.map .localSet) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < V.length, fl'[base + j]? = some V[j]?) ∧
      (∀ i, (i < base ∨ base + V.length ≤ i) → fl'[i]? = fl[i]?) := by
  intro V xs fl hl hx hb
  obtain ⟨fl', initializes, hlen, hmid, hout⟩ := sets_initializes V xs fl hl hx hb
  exact ⟨fl', initializes.forced, hlen, hmid, hout⟩

/-- Existing forced-zeroing API, projected from the stronger initialization path. -/
theorem zeros_forced {s : Store H} {M : ModuleInst} {k : Nat} {R : List Admin} :
    ∀ (zs : List Instr) (vs : List Val) (xs : List LocalIdx) (fl : List (Option Val)) (b : Nat),
    zs.length = xs.length → List.Forall₂ (fun z v => (Admin.plain z).val? = some v) zs vs →
    (∀ j x, xs[j]? = some x → x.toNat = b + j) → (∀ j < xs.length, b + j < fl.length) →
    ∃ fl', GrowWrapper.Forced (P := P) ⟨s, ⟨fl, M⟩, [.label k [] (expression (zerosI zs xs) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < vs.length, fl'[b + j]? = some vs[j]?) ∧
      (∀ i, (i < b ∨ b + vs.length ≤ i) → fl'[i]? = fl[i]?) := by
  intro zs vs xs fl b hl hv hx hb
  obtain ⟨fl', initializes, hlen, hmid, hout⟩ := zeros_initializes zs vs xs fl b hl hv hx hb
  exact ⟨fl', initializes.forced, hlen, hmid, hout⟩

end Silmaril.Wasm.Binaryen.InlR
