module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.OsInv

/-!
# Proofs: the OS image of WASI 0.3 over 0.2

The invariant method of `Silmaril.Wasi.Versions.Stateful` with two image protocols: the theory
`osImg2 ch` on the 0.2 answers (its state is the 0.2 image) and the guarantee `osG3 ch` on the
0.3 answers (its state is the state of `osStep3`, the 0.3 image, the number of answers and
whether the run left `PollDone`). `os_wpInv`: after every call, unless the run left
`PollDone`, the invariant `OsInv` holds and the two images are equal.

A play of the component is an idle play followed by the moves of the running call
(`reach_idle_prefix`): these moves add 0.2 events but no 0.3 answer, so the 0.3 image is a
prefix of the 0.2 image, equal when no call runs (`play_os`). Through the zip of a linked play
(`htrace_zip`, `xtrace_zip`) this is `p3OverP2_os` for the composite over any 0.2 host whose
answers `p2Ok` accepts.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Process.LPS (Word Event)

/-! ## Runs of the two image protocols -/

/-- The 0.2 image along a run that `p2Ok` accepts. -/
theorem run_osImg2 (ch : Word) : ∀ (t : List WEv) (q : List Event),
    (∀ e ∈ t, P2.p2Ok e = true) → (osImg2 ch).run q t = some (q ++ P2.osTrace2 ch t)
  | [], q, _ => by simp [P2.osTrace2]
  | e :: t, q, h => by
    have he := h e List.mem_cons_self
    have hstep : (osImg2 ch).step q e = some (q ++ P2.osEv2 ch e) := by
      show (if P2.p2Ok e then _ else none) = _
      rw [he]
      rfl
    rw [Protocol.run_cons, hstep, Option.bind_some,
      run_osImg2 ch t _ fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    simp [P2.osTrace2]

/-- The 0.3 image along any run. -/
theorem run_osG3 (ch : Word) : ∀ (t : List WEv) (q : Os3St), ∃ qG,
    (osG3 ch).run q t = some qG ∧ qG.img = q.img ++ osRun3 ch q.os t ∧
      (qG.bad = false ↔ q.bad = false ∧ (∀ e ∈ t, blockedW e = false) ∧
        (t = [] ∨ q.n + t.length < osBound))
  | [], q => ⟨q, rfl, by simp [osRun3], by simp⟩
  | e :: t, q => by
    obtain ⟨qG, hrun, himg, hbad⟩ := run_osG3 ch t
      ⟨(osStep3 ch q.os e).1, q.img ++ (osStep3 ch q.os e).2, q.n + 1,
        q.bad || blockedW e || decide (osBound ≤ q.n + 1)⟩
    refine ⟨qG, by rw [Protocol.run_cons]; exact hrun, ?_, ?_⟩
    · rw [himg]
      simp [osRun3]
    · rw [hbad]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, List.mem_cons,
        forall_eq_or_imp, List.cons_ne_nil, false_or, List.length_cons]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
        refine ⟨h1, ⟨h2, h4⟩, ?_⟩
        rcases h5 with rfl | h5
        · simpa using h3
        · omega
      · rintro ⟨h1, ⟨h2, h4⟩, h5⟩
        refine ⟨⟨⟨h1, h2⟩, by omega⟩, h4, ?_⟩
        rcases t with _ | ⟨e', t⟩
        · exact Or.inl rfl
        · exact Or.inr (by simp at h5 ⊢; omega)

/-- **The 0.3 image from the start**: the state of `osG3` holds `osTrace3`, and it is not
marked exactly in the runs where the poll loop finishes. -/
theorem run_osG3_init (ch : Word) (t : List WEv) : ∃ qG,
    (osG3 ch).run (osG3 ch).init t = some qG ∧ qG.img = osTrace3 ch t ∧
      (qG.bad = false ↔ PollDone t) := by
  obtain ⟨qG, hrun, himg, hbad⟩ := run_osG3 ch t {}
  refine ⟨qG, hrun, by simpa [osTrace3] using himg, ?_⟩
  rw [hbad]
  unfold PollDone
  have hpos : 0 < osBound := by decide
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨?_, h2⟩
    rcases h3 with rfl | h3
    · simpa using hpos
    · simpa using h3
  · rintro ⟨h1, h2⟩
    exact ⟨rfl, h2, Or.inr (by simpa using h1)⟩


/-! ## The invariant method -/

/-- The invariant of the OS image: unless the run has left `PollDone`, the store invariant
holds and the two images agree. -/
def OsJ (s : St) (qT : List Event) (qG : Os3St) : Prop :=
  qG.bad = false → OsInv s.core qG.os qG.n ∧ qG.img = qT

/-- **The OS images agree after every call.** -/
theorem os_wpInv (ch : Word) : WpInv body init (osImg2 ch) (osG3 ch) OsJ := by
  refine ⟨fun _ => ⟨OsInv.init, rfl⟩, fun s qT qG q hJ => ?_⟩
  cases hb : qG.bad
  · obtain ⟨hinv, himg⟩ := hJ hb
    refine Wp.mono (fun a qT' hpost => ⟨_, rfl, fun hbad => ?_⟩)
      (wp_os ch s q qG.os qG.n qT hinv)
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hbad
    obtain ⟨hinv', hq⟩ := hpost hbad.1.2 hbad.2
    exact ⟨hinv', by rw [himg, hq]⟩
  · refine Wp.stable (R := fun _ => True) (fun _ _ _ _ _ => trivial)
      (fun a q _ => ⟨_, rfl, fun hbad => ?_⟩) (body s q) trivial
    simp [hb] at hbad


/-! ## Plays of a stateful component -/

section Plays

variable {S : Type} {I X : Set FnName} {h : SBody S I X} {s₀ : S}

/-- Whether a control state is idle. -/
def idleB : SCSt S I X → Bool
  | .idle _ => true
  | _ => false

/-- An import move adds no return. -/
theorem retAsImp_snoc_inl (v : List (Move (nsig I) (nsig X))) (m : Ev (nsig I)) :
    retAsImp (wtrace (v ++ [.inl m])) = retAsImp (wtrace v) := by
  cases m <;> simp [wtrace, retAsImp, List.filterMap_append, wev, retImp]

/-- **A play is an idle play followed by the moves of one running call**, which contain no
export return. -/
theorem reach_idle_prefix {t : List (Move (nsig I) (nsig X))} {c : SCSt S I X}
    (ht : SReach h s₀ t c) : ∃ t0 v s, t = t0 ++ v ∧ SReach h s₀ t0 (.idle s) ∧
      retAsImp (wtrace v) = [] ∧ (idleB c = true → v = []) := by
  induction ht with
  | nil => exact ⟨[], [], s₀, rfl, .nil, rfl, fun _ => rfl⟩
  | @snoc t c c' o ht hc ih =>
    obtain ⟨t0, v, s, rfl, h0, hv, hidle⟩ := ih
    cases hc with
    | ask s' q =>
      have hv0 := hidle rfl
      subst hv0
      exact ⟨t0, [.inr (.ask q)], s', by simp, by simpa using ht, rfl, fun h' => by cases h'⟩
    | call q m k =>
      exact ⟨t0, v ++ [.inl (.ask m)], s, by simp, h0, by rw [retAsImp_snoc_inl, hv],
        fun h' => by cases h'⟩
    | reply q m k n =>
      exact ⟨t0, v ++ [.inl (.ans m n)], s, by simp, h0, by rw [retAsImp_snoc_inl, hv],
        fun h' => by cases h'⟩
    | ret q s' r =>
      exact ⟨t0 ++ v ++ [.inr (.ans q r)], [], s', by simp, ht.snoc (.ret q s' r), rfl,
        fun _ => rfl⟩

/-- Whether the last export event of a play is not a call. -/
theorem reach_settled_iff {t : List (Move (nsig I) (nsig X))} {c : SCSt S I X}
    (ht : SReach h s₀ t c) : settled (expView (wtrace t)) = idleB c := by
  induction ht with
  | nil => rfl
  | @snoc t c c' o ht hc ih =>
    cases hc with
    | ask s' q => simp [wtrace, expView, settled, wev, WEv.isExp, idleB]
    | call q m k =>
      simp only [wtrace, List.map_append, List.map_cons, List.map_nil, expView,
        List.filter_append, wev, WEv.isExp, List.filter_cons, List.filter_nil] at ih ⊢
      simpa [idleB] using ih
    | reply q m k n =>
      simp only [wtrace, List.map_append, List.map_cons, List.map_nil, expView,
        List.filter_append, wev, WEv.isExp, List.filter_cons, List.filter_nil] at ih ⊢
      simpa [idleB] using ih
    | ret q s' r => simp [wtrace, expView, settled, wev, WEv.isExp, idleB]

end Plays


/-! ## The OS images of the component and of the composite -/

/-- **The OS images along a play of the component.** If the 0.2 answers are accepted by
`p2Ok` and the 0.3 answers are `PollDone`, the 0.3 image is a prefix of the 0.2 image, and they
are equal when no call is running. -/
theorem play_os (ch : Word) {t : List (Move (nsig P2.p2Command.imports) (nsig p3World.imports))}
    {c : SCSt St P2.p2Command.imports p3World.imports} (ht : SReach body init t c)
    (hT : ∀ e ∈ hostView (wtrace t), P2.p2Ok e = true) (hpd : PollDone (retAsImp (wtrace t))) :
    osTrace3 ch (retAsImp (wtrace t)) <+: P2.osTrace2 ch (hostView (wtrace t)) ∧
      (idleB c = true → osTrace3 ch (retAsImp (wtrace t)) = P2.osTrace2 ch (hostView (wtrace t))) := by
  obtain ⟨t0, v, s, rfl, h0, hv, hidle⟩ := reach_idle_prefix ht
  have hw : wtrace (t0 ++ v) = wtrace t0 ++ wtrace v := List.map_append
  have hr : retAsImp (wtrace (t0 ++ v)) = retAsImp (wtrace t0) := by
    rw [hw, retAsImp, List.filterMap_append]
    rw [retAsImp] at hv
    rw [hv, List.append_nil]
    rfl
  have hhv : hostView (wtrace (t0 ++ v)) = hostView (wtrace t0) ++ hostView (wtrace v) := by
    rw [hw, hostView_append]
  rw [hr] at hpd ⊢
  have hT0 : ∀ e ∈ hostView (wtrace t0), P2.p2Ok e = true := fun e he =>
    hT e (by rw [hhv]; exact List.mem_append_left _ he)
  have hrun2 : (osImg2 ch).run (osImg2 ch).init (hostView (wtrace t0)) =
      some ([] ++ P2.osTrace2 ch (hostView (wtrace t0))) := run_osImg2 ch (hostView (wtrace t0)) [] hT0
  obtain ⟨qG, hqG, hJ⟩ := (os_wpInv ch).reach h0 _ hrun2
  rw [run_retG] at hqG
  obtain ⟨qG', hrun3, himg, hbad⟩ := run_osG3_init ch (retAsImp (wtrace t0))
  rw [hrun3] at hqG
  cases hqG
  have heq0 : osTrace3 ch (retAsImp (wtrace t0)) = P2.osTrace2 ch (hostView (wtrace t0)) := by
    rw [← himg, (hJ (hbad.2 hpd)).2, List.nil_append]
  rw [heq0, hhv]
  refine ⟨by simp [P2.osTrace2], fun hc => ?_⟩
  rw [hidle hc]
  simp [P2.osTrace2, wtrace, hostView]

/-- **The OS image of WASI 0.3 over 0.2.** Over every 0.2 host whose answers `p2Ok` accepts, for
every play `p` of the composite in which the poll loop finishes (`PollDone`), the bytes the
composite accepted on its 0.3 stdout streams (`osTrace3`) are a prefix of the bytes its 0.2 host
wrote (`osTrace2` of the host's part `s` of the play), and the same bytes when no 0.3 call is
running (`settled`). -/
theorem p3OverP2_os (ch : Word) {Y : Sig.{0}} {η : Host Y P2.p2Command.imports}
    (hη : (hostSat (pointwise P2.p2Ok).Accepts).holds η) :
    ∀ p ∈ link η p3OverP2, PollDone (htrace p) → ∃ s ∈ η,
      osTrace3 ch (htrace p) <+: P2.osTrace2 ch (htrace s) ∧
        (settled (xtrace p) = true → osTrace3 ch (htrace p) = P2.osTrace2 ch (htrace s)) := by
  rintro p ⟨s, hs, t, ⟨c, ht⟩, hz⟩ hpd
  have h1 : htrace s = hostView (wtrace t) := htrace_zip hz
  have h2 : xtrace p = expView (wtrace t) := xtrace_zip hz
  have h3 : htrace p = retAsImp (wtrace t) := by
    rw [htrace_eq_retAsImp, h2, retAsImp_expView]
  have hT := (pointwise_accepts_iff _ _).1 (hη s hs)
  rw [h1] at hT
  rw [h3] at hpd ⊢
  refine ⟨s, hs, ?_⟩
  rw [h1]
  obtain ⟨hpre, heq⟩ := play_os ch ht hT hpd
  refine ⟨hpre, fun hset => heq ?_⟩
  rw [h2, reach_settled_iff ht] at hset
  exact hset

/-- The same over every host of the 0.2 theory `P2.p2Th r` (strict or loose). -/
theorem p3OverP2_os_p2Th (ch : Word) (r : P2.Reading) {Y : Sig.{0}} {η : Host Y P2.p2Command.imports}
    (hη : (hostSat (P2.p2Th r).Accepts).holds η) :
    ∀ p ∈ link η p3OverP2, PollDone (htrace p) → ∃ s ∈ η,
      osTrace3 ch (htrace p) <+: P2.osTrace2 ch (htrace s) ∧
        (settled (xtrace p) = true → osTrace3 ch (htrace p) = P2.osTrace2 ch (htrace s)) :=
  p3OverP2_os ch fun s hs => by
    have h := hη s hs
    simp only [P2.p2Th, Protocol.accepts_prod_iff] at h
    exact h.2.2.1

/-- The same over every host of `p2ThF F`, the 0.2 theory of `p3OverP2_model`. -/
theorem p3OverP2_os_F (ch : Word) (F : BitVec 32 → List (BitVec 8)) {Y : Sig.{0}}
    {η : Host Y P2.p2Command.imports} (hη : (hostSat (p2ThF F).Accepts).holds η) :
    ∀ p ∈ link η p3OverP2, PollDone (htrace p) → ∃ s ∈ η,
      osTrace3 ch (htrace p) <+: P2.osTrace2 ch (htrace s) ∧
        (settled (xtrace p) = true → osTrace3 ch (htrace p) = P2.osTrace2 ch (htrace s)) :=
  p3OverP2_os_p2Th ch .loose fun s hs => by
    have h := hη s hs
    simp only [p2ThF, Protocol.accepts_prod_iff] at h
    exact h.1

end Silmaril.Wasi.Versions.P3OverP2
