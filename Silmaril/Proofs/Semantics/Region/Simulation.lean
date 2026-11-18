module

public import Silmaril.Semantics.Region.Simulation.Defs

public section

namespace Silmaril.Semantics.Region.SimulationProofs

variable {Small Full Lab Event SmallStop FullStop : Type*}
variable {small : TransitionSystem Small Lab Event SmallStop}
variable {full : TransitionSystem Full Lab Event FullStop} {support : Lab → Prop}

theorem liftExit (map : Realizes small full) {s out : Small} {trace : List Event}
    (run : FirstExit small support s trace out) : ∀ {initial}, map.relates s initial →
    ∃ final, FirstExit full support initial trace final ∧ map.relates out final := by
  induction run with
  | leave inside edge outside =>
    intro _ related
    obtain ⟨_, step, related'⟩ := map.step related edge
    exact ⟨_, .leave (map.pc related ▸ inside) step (map.pc related' ▸ outside), related'⟩
  | step inside edge _ ih =>
    intro _ related
    obtain ⟨_, step, related'⟩ := map.step related edge
    obtain ⟨_, tail, final⟩ := ih related'
    exact ⟨_, .step (map.pc related ▸ inside) step tail, final⟩

private theorem startsInside {s t : Full} {es : List Event} (run : FirstExit full support s es t) :
    support (full.pc s) := by cases run <;> assumption

private theorem insideStarts {s t : Full} {es : List Event} (run : Inside full support s es t) :
    support (full.pc s) := by cases run <;> assumption

private theorem uniqueExit (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ∀ es next,
    FirstExit full support s es next → es = trace ∧ next = out := by
  induction run with
  | leave _ edge outside =>
    intro _ _ other
    cases other with
    | leave _ edge' _ => exact det.step_unique edge' edge
    | step _ edge' tail =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      exact False.elim (outside (startsInside tail))
  | step _ edge tail ih =>
    intro _ _ other
    cases other with
    | leave _ edge' outside =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      exact False.elim (outside (startsInside tail))
    | step _ edge' tail' =>
      obtain ⟨rfl, rfl⟩ := det.step_unique edge' edge
      obtain ⟨rfl, rfl⟩ := ih _ _ tail'
      exact ⟨rfl, rfl⟩

private theorem accessible (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) :
    Acc (fun t s => support (full.pc s) ∧ support (full.pc t) ∧ ∃ es, full.step s es t) s := by
  induction run with
  | leave _ edge outside =>
    refine Acc.intro _ ?_
    rintro _ ⟨_, inside, _, other⟩
    obtain ⟨_, rfl⟩ := det.step_unique other edge
    exact False.elim (outside inside)
  | step _ edge _ ih =>
    refine Acc.intro _ ?_
    rintro _ ⟨_, _, _, other⟩
    obtain ⟨_, rfl⟩ := det.step_unique other edge
    exact ih

private theorem progress (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ∀ es mid,
    Inside full support s es mid → ∃ tail next, full.step mid tail next := by
  induction run with
  | leave _ edge outside =>
    intro _ _ insideRun
    cases insideRun with
    | refl => exact ⟨_, _, edge⟩
    | step _ other rest =>
      obtain ⟨_, rfl⟩ := det.step_unique other edge
      exact False.elim (outside (insideStarts rest))
  | step _ edge _ ih =>
    intro _ _ insideRun
    cases insideRun with
    | refl => exact ⟨_, _, edge⟩
    | step _ other rest =>
      obtain ⟨_, rfl⟩ := det.step_unique other edge
      exact ih _ _ rest

theorem completes (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) : ExitsNormally full support s trace out :=
  ⟨run, uniqueExit det run, ⟨accessible det run, fun es mid insideRun => .inr (progress det run es mid insideRun)⟩,
    fun es mid insideRun _ => let ⟨_, _, step⟩ := progress det run es mid insideRun; det.step_no_halt step⟩

theorem liftProperty (map : Realizes small full) (det : Determinate full) {s : Small} {initial : Full}
    (related : map.relates s initial) (settled : ∃ trace out, FirstExit small support s trace out)
    (P : List Event → Small → Prop) (proved : ∀ trace out, FirstExit small support s trace out → P trace out) :
    (∃ trace final, ExitsNormally full support initial trace final) ∧
    ∀ trace final, FirstExit full support initial trace final → ∃ out, map.relates out final ∧ P trace out := by
  obtain ⟨trace, out, run⟩ := settled
  obtain ⟨final, lifted, finalRelated⟩ := liftExit map run related
  have normal := completes det lifted
  refine ⟨⟨trace, final, normal⟩, ?_⟩
  intro es next other
  obtain ⟨rfl, rfl⟩ := normal.unique es next other
  exact ⟨out, finalRelated, proved _ _ run⟩

private theorem exitOfAcc {s : Small}
    (acc : Acc (fun t s => support (small.pc s) ∧ support (small.pc t) ∧ ∃ es, small.step s es t) s)
    (inside : support (small.pc s))
    (progress : ∀ es mid, Inside small support s es mid →
      (∃ stop, small.halt mid stop) ∨ ∃ tail next, small.step mid tail next)
    (noHalt : ∀ es mid stop, Inside small support s es mid → ¬ small.halt mid stop) :
    ∃ trace out, FirstExit small support s trace out := by
  induction acc with
  | intro s _ ih =>
    rcases progress [] s (.refl inside) with ⟨stop, halt⟩ | ⟨events, next, edge⟩
    · exact False.elim (noHalt [] s stop (.refl inside) halt)
    by_cases nextInside : support (small.pc next)
    · obtain ⟨trace, out, run⟩ := ih next ⟨inside, nextInside, events, edge⟩ nextInside
        (fun _ _ tail => progress _ _ (.step inside edge tail))
        (fun _ _ _ tail => noHalt _ _ _ (.step inside edge tail))
      exact ⟨events ++ trace, out, .step inside edge run⟩
    · exact ⟨events, next, .leave inside edge nextInside⟩

theorem contractExit {admit : Small → Prop} {s : Small} (admitted : admit s)
    (entry : support (small.pc s)) {ubEvent : Event → Prop} {ubStop : SmallStop → Prop}
    (safe : NoUB small admit support ubEvent ubStop) {Q : Lab → List Event → Small → Prop}
    (contract : TotalHoare small admit support Q (fun stop _ _ => ubStop stop)) :
    ∃ trace out, FirstExit small support s trace out := by
  obtain ⟨acc, progress⟩ := contract.2 _ admitted
  exact exitOfAcc acc entry progress fun es mid stop run halt =>
    safe.2 s es mid stop admitted run halt (contract.1.2 s es mid stop admitted run halt)

private theorem mayEffectOfExit {s out : Small} {trace : List Event}
    (run : FirstExit small support s trace out) {event : Event} (mem : event ∈ trace) :
    MayEffect small (· = s) support event := by
  induction run with
  | leave inside edge _ => exact ⟨_, [], _, _, _, rfl, .refl inside, edge, by simpa using mem⟩
  | step inside edge _ ih =>
    rcases List.mem_append.mp mem with first | rest
    · exact ⟨_, [], _, _, _, rfl, .refl inside, edge, by simpa using first⟩
    · obtain ⟨_, _, _, _, _, rfl, prior, last, seen⟩ := ih rest
      exact ⟨_, _, _, _, _, rfl, .step inside edge prior, last,
        by rw [List.append_assoc]; exact List.mem_append_right _ seen⟩

private theorem effectOnExit (det : Determinate full) {s out : Full} {trace : List Event}
    (run : FirstExit full support s trace out) {event : Event} : ∀ es mid tail next,
    Inside full support s es mid → full.step mid tail next → event ∈ es ++ tail → event ∈ trace := by
  induction run with
  | leave _ edge outside =>
    intro _ _ _ _ prior last seen
    cases prior with
    | refl =>
      obtain ⟨rfl, _⟩ := det.step_unique last edge
      simpa using seen
    | step _ other rest =>
      obtain ⟨_, rfl⟩ := det.step_unique other edge
      exact False.elim (outside (insideStarts rest))
  | step _ edge _ ih =>
    intro _ _ _ _ prior last seen
    cases prior with
    | refl =>
      obtain ⟨rfl, _⟩ := det.step_unique last edge
      exact List.mem_append_left _ (by simpa using seen)
    | step _ other rest =>
      obtain ⟨rfl, rfl⟩ := det.step_unique other edge
      rw [List.append_assoc] at seen
      exact (List.mem_append.mp seen).elim (List.mem_append_left _) (List.mem_append_right _ ∘ ih _ _ _ _ rest last)

theorem transferContract (map : Realizes small full) (det : Determinate full)
    {admit : Small → Prop} {admitFull : Full → Prop} {ubEvent : Event → Prop}
    {ubStop : SmallStop → Prop} {ubFullStop : FullStop → Prop} {Q : Lab → List Event → Small → Prop}
    (safe : NoUB small admit support ubEvent ubStop)
    (contract : TotalHoare small admit support Q (fun stop _ _ => ubStop stop))
    (entry : ∀ s, admit s → support (small.pc s))
    (initial : ∀ t, admitFull t → ∃ s, admit s ∧ map.relates s t) :
    NoUB full admitFull support ubEvent ubFullStop ∧
    TotalHoare full admitFull support (fun label es t => ∃ s, map.relates s t ∧ Q label es s)
      (fun stop _ _ => ubFullStop stop) ∧ map.RefinesExits admit admitFull support := by
  have matched : ∀ t, admitFull t → ∃ s trace out final,
      admit s ∧ map.relates s t ∧ FirstExit small support s trace out ∧
      ExitsNormally full support t trace final ∧ map.relates out final := by
    intro t admitted
    obtain ⟨s, hs, relates⟩ := initial t admitted
    obtain ⟨trace, out, run⟩ := contractExit hs (entry s hs) safe contract
    obtain ⟨final, lifted, output⟩ := liftExit map run relates
    exact ⟨s, trace, out, final, hs, relates, run, completes det lifted, output⟩
  refine ⟨⟨?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro event ub ⟨t, es, mid, tail, next, admitted, prior, edge, seen⟩
    obtain ⟨s, _, _, _, hs, _, run, normal, _⟩ := matched t admitted
    obtain ⟨s', es', mid', tail', next', eq, prior', edge', seen'⟩ :=
      mayEffectOfExit run (effectOnExit det normal.witness es mid tail next prior edge seen)
    subst s'
    exact safe.1 event ub ⟨s, es', mid', tail', next', hs, prior', edge', seen'⟩
  · intro t es mid stop admitted prior halt _
    obtain ⟨_, _, _, _, _, _, _, normal, _⟩ := matched t admitted
    exact normal.noHalt es mid prior stop halt
  · intro t es next admitted run
    obtain ⟨s, _, out, _, hs, _, smallRun, normal, output⟩ := matched t admitted
    obtain ⟨rfl, rfl⟩ := normal.unique es next run
    exact ⟨out, output, map.pc output ▸ contract.1.1 s _ out hs smallRun⟩
  · intro t es mid stop admitted prior halt
    obtain ⟨_, _, _, _, _, _, _, normal, _⟩ := matched t admitted
    exact False.elim (normal.noHalt es mid prior stop halt)
  · intro t admitted
    obtain ⟨_, _, _, _, _, _, _, normal, _⟩ := matched t admitted
    exact normal.finishes
  · intro t es next admitted run
    obtain ⟨s, _, out, _, hs, related, smallRun, normal, output⟩ := matched t admitted
    obtain ⟨rfl, rfl⟩ := normal.unique es next run
    exact ⟨s, out, hs, related, smallRun, output⟩

end Silmaril.Semantics.Region.SimulationProofs
