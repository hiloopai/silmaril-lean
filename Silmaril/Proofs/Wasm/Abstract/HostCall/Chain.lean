module

public import Silmaril.Proofs.Wasm.Abstract.HostCall.LoggedInf

/-!
# Building labelled runs and productive runs (proofs)

The constructive counterparts of the splits of `Logged` and `LoggedInf`, for the forward
simulation of logged native runs:

* `evRun_of_free`: a host-free Core run is a labelled run with no event;
* `evRun_wrap`, `coreInf_wrap`: a context that lifts every labelled step with its label lifts
  labelled runs and productive runs; `evRun_ctx`, `evRun_label`, `evRun_frame`,
  `coreInf_ctx`, `coreInf_label`, `coreInf_frame`: its instances for a sequence context, a
  label and a call frame;
* `hEvStep_host_call`: an answered host call is one event;
* `evRun_cons_split`: a labelled run whose log starts with `e` is silent steps, the event `e`,
  and a run with the rest of the log;
* `coreInf_of_inv`: a productive run from an invariant that always reaches the next event;
* `coreInf_of_segments`: **a chain of labelled runs** `K n ⟶ K (n + 1)` with logs `q n` whose
  concatenation is the stream `ω` (`Shape.StreamConcat`, of unbounded length) is a productive
  run with the events `ω`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostCall

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.SingleThreaded
open Shape (streamAppend StreamConcat)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Host-free runs and contexts -/

/-- **A host-free run is silent.** -/
theorem evRun_of_free {c c' : Config H} (h : Steps P (fun _ _ _ _ => False) c c') :
    EvRun P host c [] c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head hs _ ih => exact .silent (.inl hs) ih

/-- A context lifting every labelled step lifts labelled runs. -/
theorem evRun_wrap (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    {c c' : Config H} {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') :
    EvRun P host (W c) cs (W c') := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih => exact .silent (hW _ _ _ hs) ih
  | event hs _ ih => exact .event (hW _ _ _ hs) ih

/-- A context lifting every labelled step lifts productive runs. -/
theorem coreInf_wrap (W : Config H → Config H)
    (hW : ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c'))
    {c : Config H} {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host c ω) :
    CoreInf P host (W c) ω := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨fun n => W (g n), congrArg W hg0, fun n => ?_⟩
  obtain ⟨c₁, hr, he⟩ := hg n
  refine ⟨W c₁, ?_, hW _ _ _ he⟩
  clear he
  induction hr with
  | refl => exact .refl
  | tail _ hs ih => exact .tail ih (hW _ _ _ hs)

theorem hWrap_ctx (ws : List Val) (rest : List Admin) (c : Config H)
    (l : Option (Call (wasmHostSig H))) (c' : Config H) (h : HEvStep P host c l c') :
    HEvStep P host ⟨c.store, c.frame, vals ws ++ c.code ++ rest⟩ l
      ⟨c'.store, c'.frame, vals ws ++ c'.code ++ rest⟩ := by
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_ctx ws rest h

theorem hWrap_label (n : Nat) (cont : List Instr) (c : Config H)
    (l : Option (Call (wasmHostSig H))) (c' : Config H) (h : HEvStep P host c l c') :
    HEvStep P host ⟨c.store, c.frame, [.label n cont c.code]⟩ l
      ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ := by
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_label n cont h

theorem hWrap_frame (n : Nat) (f : Frame) (c : Config H)
    (l : Option (Call (wasmHostSig H))) (c' : Config H) (h : HEvStep P host c l c') :
    HEvStep P host ⟨c.store, f, [.frame n c.frame c.code]⟩ l
      ⟨c'.store, f, [.frame n c'.frame c'.code]⟩ := by
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_frame n h

/-- A labelled run under values and before a continuation. -/
theorem evRun_ctx {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (ws : List Val) (rest : List Admin)
    (h : EvRun P host ⟨s, f, es⟩ cs ⟨s', f', es'⟩) :
    EvRun P host ⟨s, f, vals ws ++ es ++ rest⟩ cs ⟨s', f', vals ws ++ es' ++ rest⟩ :=
  evRun_wrap (fun c => ⟨c.store, c.frame, vals ws ++ c.code ++ rest⟩) (hWrap_ctx ws rest) h

/-- A labelled run inside a label. -/
theorem evRun_label {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (n : Nat) (cont : List Instr)
    (h : EvRun P host ⟨s, f, es⟩ cs ⟨s', f', es'⟩) :
    EvRun P host ⟨s, f, [.label n cont es]⟩ cs ⟨s', f', [.label n cont es']⟩ :=
  evRun_wrap (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩) (hWrap_label n cont) h

/-- A labelled run inside a call frame; the outer frame is untouched. -/
theorem evRun_frame {s s' : Store H} {f F F' : Frame} {es es' : List Admin}
    {cs : List (Call (wasmHostSig H))} (n : Nat)
    (h : EvRun P host ⟨s, F, es⟩ cs ⟨s', F', es'⟩) :
    EvRun P host ⟨s, f, [.frame n F es]⟩ cs ⟨s', f, [.frame n F' es']⟩ :=
  evRun_wrap (fun c => ⟨c.store, f, [.frame n c.frame c.code]⟩) (hWrap_frame n f) h

/-- A productive run under values and before a continuation. -/
theorem coreInf_ctx {s : Store H} {f : Frame} {es : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (ws : List Val) (rest : List Admin) (h : CoreInf P host ⟨s, f, es⟩ ω) :
    CoreInf P host ⟨s, f, vals ws ++ es ++ rest⟩ ω :=
  coreInf_wrap (fun c => ⟨c.store, c.frame, vals ws ++ c.code ++ rest⟩) (hWrap_ctx ws rest) h

/-- A productive run inside a label. -/
theorem coreInf_label {s : Store H} {f : Frame} {es : List Admin} {ω : Nat → Call (wasmHostSig H)}
    (n : Nat) (cont : List Instr) (h : CoreInf P host ⟨s, f, es⟩ ω) :
    CoreInf P host ⟨s, f, [.label n cont es]⟩ ω :=
  coreInf_wrap (fun c => ⟨c.store, c.frame, [.label n cont c.code]⟩) (hWrap_label n cont) h

/-- A productive run inside a call frame. -/
theorem coreInf_frame {s : Store H} {f F : Frame} {es : List Admin}
    {ω : Nat → Call (wasmHostSig H)} (n : Nat) (h : CoreInf P host ⟨s, F, es⟩ ω) :
    CoreInf P host ⟨s, f, [.frame n F es]⟩ ω :=
  coreInf_wrap (fun c => ⟨c.store, f, [.frame n c.frame c.code]⟩) (hWrap_frame n f) h

/-- **An answered host call is its one event**, any frame. -/
theorem hEvStep_host_call {s s' : Store H} {f : Frame} {a : Nat} {fi : FuncInst H} {hh : H}
    {ps rs : Validation.Ty (.list .val)} {us : List Val} {r : Result}
    (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : us.length = ps.length) (hcode : fi.code = .host hh)
    (hans : host hh s us (.returned s' r)) :
    HEvStep P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
      (some ⟨(hh, s, us), (s', r)⟩) ⟨s', f, r.toAdmin⟩ :=
  ⟨.top [] [], a, decompose?_redex (c := .callRefType fi.type) trivial hf he hn hcode, rfl, hans,
    by simp [Ctx.fill, vals]⟩

/-! ## Productive runs from finite segments -/

/-- A labelled run whose log starts with `e`: silent steps, the event `e`, the rest. -/
theorem evRun_cons_split {c d : Config H} {e : Call (wasmHostSig H)}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c (e :: cs) d) :
    ∃ c₁ c₂, Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c₁ ∧
      HEvStep P host c₁ (some e) c₂ ∧ EvRun P host c₂ cs d := by
  generalize hl : e :: cs = l at h
  induction h with
  | refl => cases hl
  | silent hs _ ih =>
    obtain ⟨c₁, c₂, hr, he, hk⟩ := ih hl
    exact ⟨c₁, c₂, .head hs hr, he, hk⟩
  | event hs hk _ =>
    cases hl
    exact ⟨_, _, .refl, hs, hk⟩

/-- **A productive run from an invariant** that always reaches the next event. -/
theorem coreInf_of_inv (Inv : Config H → (Nat → Call (wasmHostSig H)) → Prop)
    (hstep : ∀ c ω, Inv c ω → ∃ c₁ c₂,
      Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c₁ ∧
        HEvStep P host c₁ (some (ω 0)) c₂ ∧ Inv c₂ (fun k => ω (k + 1)))
    {c : Config H} {ω : Nat → Call (wasmHostSig H)} (h : Inv c ω) : CoreInf P host c ω := by
  classical
  choose c₁ c₂ hr he hinv using hstep
  have shift : ∀ n, (fun k => (fun k => ω (n + k)) (k + 1)) = fun k => ω (n + 1 + k) := by
    intro n; funext k; show ω (n + (k + 1)) = ω (n + 1 + k); rw [Nat.add_right_comm, Nat.add_assoc]
  let seq : (n : Nat) → {x : Config H // Inv x (fun k => ω (n + k))} := fun n =>
    Nat.rec ⟨c, by simpa using h⟩
      (fun n x => ⟨c₂ x.1 _ x.2, by rw [← shift n]; exact hinv x.1 _ x.2⟩) n
  refine ⟨fun n => (seq n).1, rfl, fun n => ⟨c₁ (seq n).1 _ (seq n).2, hr _ _ _, ?_⟩⟩
  have := he (seq n).1 _ (seq n).2
  simpa using this

/-- The offset of segment `n`. -/
private abbrev off (q : Nat → List (Call (wasmHostSig H))) (n : Nat) : Nat :=
  ((List.range n).flatMap q).length

private theorem off_succ (q : Nat → List (Call (wasmHostSig H))) (n : Nat) :
    off q (n + 1) = off q n + (q n).length := by
  simp [off, List.range_succ, List.flatMap_append]

private theorem off_mono (q : Nat → List (Call (wasmHostSig H))) {n m : Nat} (h : n ≤ m) :
    off q n ≤ off q m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [off_succ]; omega

/-- The stream after the first `n` segments. -/
private theorem tail_eq {q : Nat → List (Call (wasmHostSig H))} {ω : Nat → Call (wasmHostSig H)}
    (hq : StreamConcat q ω) (n : Nat) :
    (fun i => ω (off q n + i)) = q n ++ω fun i => ω (off q (n + 1) + i) := by
  funext i
  by_cases hi : i < (q n).length
  · rw [Shape.streamAppend_lt hi]
    have hp := hq.1 (n + 1) (off q n + i) (by rw [← off, off_succ]; omega)
    rw [hp]
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [List.getElem_append_right (by simp [off])]
    simp [off]
  · rw [Shape.streamAppend_ge (by omega), off_succ]
    congr 1
    omega

/-- **A chain of labelled runs is a productive run**: segments `K n ⟶ K (n + 1)` with logs
`q n`, whose concatenation is the stream `ω` of unbounded length. -/
theorem coreInf_of_segments (K : Nat → Config H) (q : Nat → List (Call (wasmHostSig H)))
    (h : ∀ n, EvRun P host (K n) (q n) (K (n + 1))) {ω : Nat → Call (wasmHostSig H)}
    (hq : StreamConcat q ω) : CoreInf P host (K 0) ω := by
  classical
  let Inv : Config H → (Nat → Call (wasmHostSig H)) → Prop := fun c ω' =>
    ∃ n r, EvRun P host c r (K n) ∧ ω' = r ++ω fun i => ω (off q n + i)
  -- a nonempty segment at or after every `n`
  have hne : ∀ n, ∃ k, q (n + k) ≠ [] := by
    intro n
    by_contra hno
    simp only [not_exists, not_not] at hno
    obtain ⟨m, hm⟩ := hq.2 (off q n + 1)
    have hc : ∀ k, off q (n + k) = off q n := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [← Nat.add_assoc, off_succ, ih, hno k]; simp
    rcases le_total m n with hmn | hmn
    · have := off_mono q hmn
      change off q (n + 0) + 1 ≤ off q m at hm
      rw [hc] at hm
      omega
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      change _ ≤ off q (n + k) at hm
      rw [hc] at hm
      omega
  -- every state reaches a state whose log is nonempty
  have hnorm : ∀ c ω', Inv c ω' → ∃ n e r, EvRun P host c (e :: r) (K n) ∧
      ω' = (e :: r) ++ω fun i => ω (off q n + i) := by
    rintro c ω' ⟨n, r, hr, rfl⟩
    rcases r with _ | ⟨e, r⟩
    · let k := Nat.find (hne n)
      have hk : q (n + k) ≠ [] := Nat.find_spec (hne n)
      have hlt : ∀ j < k, q (n + j) = [] := fun j hj => by
        have := Nat.find_min (hne n) hj
        simpa using this
      have hrun : ∀ j ≤ k, EvRun P host c [] (K (n + j)) ∧
          off q (n + j) = off q n := by
        intro j hj
        induction j with
        | zero => exact ⟨hr, rfl⟩
        | succ j ih =>
          obtain ⟨h₁, h₂⟩ := ih (by omega)
          have hq0 := hlt j (by omega)
          have := h (n + j)
          rw [hq0] at this
          refine ⟨by simpa [← Nat.add_assoc] using evRun_trans h₁ this, ?_⟩
          rw [← Nat.add_assoc, off_succ, hq0, h₂]
          simp
      obtain ⟨h₁, h₂⟩ := hrun k le_rfl
      obtain ⟨e, r, hqe⟩ := List.exists_cons_of_ne_nil hk
      refine ⟨n + k + 1, e, r, ?_, ?_⟩
      · have := evRun_trans h₁ (h (n + k))
        rwa [hqe] at this
      · rw [Shape.streamAppend_nil, ← hqe]
        rw [← tail_eq hq (n + k), h₂]
    · exact ⟨n, e, r, hr, rfl⟩
  refine coreInf_of_inv Inv (fun c ω' hinv => ?_) ⟨0, [], by simpa using .refl _, ?_⟩
  · obtain ⟨n, e, r, hr, rfl⟩ := hnorm c ω' hinv
    obtain ⟨c₁, c₂, hs, he, hk⟩ := evRun_cons_split hr
    refine ⟨c₁, c₂, hs, ?_, n, r, hk, ?_⟩
    · rw [Shape.streamAppend_lt (by simp)]
      simpa using he
    · funext k
      by_cases hkr : k < r.length
      · rw [Shape.streamAppend_lt (by simp; omega), Shape.streamAppend_lt hkr]
        simp
      · rw [Shape.streamAppend_ge (by simp; omega), Shape.streamAppend_ge (by omega)]
        simp only [List.length_cons]
        congr 2
        omega
  · rw [Shape.streamAppend_nil]
    funext i
    simp [off]

end Silmaril.Proofs.Wasm.Abstract.HostCall
