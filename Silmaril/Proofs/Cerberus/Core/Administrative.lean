module

public import Silmaril.Cerberus.Core.Administrative.Defs

@[expose] public section
set_option maxHeartbeats 4000000
namespace Silmaril.Cerberus.Core.Administrative
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

theorem Plain.not_halted {state : Dynamics.State} (plain : Plain state) :
    ∀ outcome, state.control ≠ .halt outcome := by
  intro outcome impossible
  have live := plain.unwrapped
  rw [impossible] at live
  cases live

theorem Edge.source_plain {file : Program} {labels : Labels} {source target : Dynamics.State}
    (edge : Edge file labels source target) : Plain source := by
  cases edge with
  | next plain _ _ _ | choose plain _ _ _ | update plain _ _ _ => exact plain

theorem Edge.target_plain {file : Program} {labels : Labels} {source target : Dynamics.State}
    (edge : Edge file labels source target) : Plain target := by
  cases edge with
  | next _ _ plain _ | choose _ _ plain _ | update _ _ plain _ => exact plain

theorem Path.source_plain {file : Program} {labels : Labels} {source target : Dynamics.State}
    (path : Path file labels source target) : Plain source := by
  cases path with
  | refl plain => exact plain
  | cons edge _ => exact edge.source_plain

theorem Path.target_plain {file : Program} {labels : Labels} {source target : Dynamics.State}
    (path : Path file labels source target) : Plain target := by
  induction path with
  | refl plain => exact plain
  | cons _ _ ih => exact ih

theorem Path.trans {file : Program} {labels : Labels} {source middle target : Dynamics.State}
    (first : Path file labels source middle) (second : Path file labels middle target) :
    Path file labels source target := by
  induction first with
  | refl _ => exact second
  | cons edge _ ih => exact .cons edge (ih second)

theorem Edge.forced {file : Program} {labels : Labels} {source target : Dynamics.State}
    (edge : Edge file labels source target) (outer : List Frame) :
    Forced.Reaches file labels (extend source outer) (extend target outer) := by
  cases edge with
  | @next control frames sourcePlain _ targetPlain requested =>
    show Forced.Reaches file labels (extend source outer) (extend ⟨control, frames, source.memory⟩ outer)
    apply Forced.next (by intro outcome halted; exact sourcePlain.not_halted outcome halted)
    unfold request
    change (match requestAux file labels source.memory source.control (source.stack ++ outer) false with
      | .next (.jumping symbol values environment) frames => jump labels symbol values environment frames
      | response => response) = .next control (frames ++ outer)
    rw [requested outer]
    have live : unwrapped control = true := targetPlain.unwrapped
    cases control <;> simp_all [Silmaril.Cerberus.Core.Administrative.unwrapped]
  | choose sourcePlain _ _ requested =>
    apply Forced.choose (by intro outcome halted; exact sourcePlain.not_halted outcome halted)
    change (match requestAux file labels source.memory source.control (source.stack ++ outer) false with
      | .next (.jumping symbol values environment) frames => jump labels symbol values environment frames
      | response => response) = .choose _
    rw [requested outer]
  | update sourcePlain _ _ requested =>
    apply Forced.update (by intro outcome halted; exact sourcePlain.not_halted outcome halted)
    change (match requestAux file labels source.memory source.control (source.stack ++ outer) false with
      | .next (.jumping symbol values environment) frames => jump labels symbol values environment frames
      | response => response) = .update _ _ _
    rw [requested outer]

theorem Path.forced {file : Program} {labels : Labels} {source target : Dynamics.State}
    (path : Path file labels source target) (outer : List Frame) :
    Forced.Reaches file labels (extend source outer) (extend target outer) := by
  induction path with
  | refl _ => exact .refl
  | cons edge _ ih => exact (edge.forced outer).trans ih

theorem Edge.source_running {file : Program} {labels : Labels} {source target : Dynamics.State}
    (edge : Edge file labels source target) : NotDone source := by
  cases edge with
  | next _ running _ _ | choose _ running _ _ | update _ running _ _ => exact running

theorem Plain.pair {left right : Dynamics.State} (first : Plain left) (second : Plain right) :
    Plain (pair left.control left.stack right) := by
  constructor
  · rfl
  · change controlHasCCall (.interleave [] [(0, left.control, left.stack), (1, right.control, right.stack)]) [] = false
    rw [controlHasCCall]
    simp [first.callfree, second.callfree]
  · change activeCall (.interleave [] [(0, left.control, left.stack), (1, right.control, right.stack)]) [] = false
    rw [activeCall]
    simp [first.inactive, second.inactive]

theorem Plain.single (done : List (Nat × Val × List Access)) {child : Dynamics.State} (plain : Plain child) :
    Plain (single done child) := by
  constructor
  · rfl
  · change controlHasCCall (.interleave done [(0, child.control, child.stack)]) [] = false
    rw [controlHasCCall]
    simp [plain.callfree]
  · change activeCall (.interleave done [(0, child.control, child.stack)]) [] = false
    rw [activeCall]
    simp [plain.inactive]

private def pairWrap (labels : Labels) (left : Dynamics.State) (outer : List Frame)
    (control : Control) (frames : List Frame) : Control × List Frame :=
  match control with
  | .raise outcome => (.raise outcome, [])
  | .jumping symbol values environment => arenaJump labels symbol values environment outer
  | _ => (.interleave [] [(0, left.control, left.stack), (1, control, frames)], outer)

private def leftWrap (labels : Labels) (right : Dynamics.State) (outer : List Frame)
    (control : Control) (frames : List Frame) : Control × List Frame :=
  match control with
  | .raise outcome => (.raise outcome, [])
  | .jumping symbol values environment => arenaJump labels symbol values environment outer
  | _ => (.interleave [] [(0, control, frames), (1, right.control, right.stack)], outer)

private def pairRightGroup (file : Program) (labels : Labels) (left source : Dynamics.State) (outer : List Frame) :
    Bool × List (Control × List Frame) :=
  match source.control, annotationsOnly source.stack with
  | .value value, some accesses =>
      (true, [(.interleave [(1, value, accesses)] [(0, left.control, left.stack)], outer)])
  | _, _ =>
    match requestAux file labels source.memory source.control source.stack false with
    | .scheduled choices => (false, choices.map fun (control, frames) => pairWrap labels left outer control frames)
    | .memory name memory control frames =>
        (true, [(.commitMemory name memory (.interleave [] [(0, left.control, left.stack), (1, control, frames)]), outer)])
    | .next (.jumping symbol values environment) _ =>
        (true, [arenaJump labels symbol values environment outer])
    | .update memory control frames =>
        (true, [(.commitUpdate memory (.interleave [] [(0, left.control, left.stack), (1, control, frames)]), outer)])
    | .pull action control frames =>
        (true, match liftAction source.memory action
          (.interleave [] [(0, left.control, left.stack), (1, control, frames)]) outer with
        | .update memory next frames => [(.commitUpdate memory next, frames)]
        | .pull action next frames => [(.pulling action next frames, [])]
        | _ => [])
    | .next control frames => (true, [pairWrap labels left outer control frames])
    | .choose choices => (true, choices.map fun (control, frames) => pairWrap labels left outer control frames)
    | .end_ outcome => (true, [(.raise outcome, [])])

private def pairLeftGroup (file : Program) (labels : Labels) (left right : Dynamics.State) (outer : List Frame) :
    Bool × List (Control × List Frame) :=
  match left.control, annotationsOnly left.stack with
  | .value value, some accesses =>
      (true, [(.interleave [(0, value, accesses)] [(1, right.control, right.stack)], outer)])
  | _, _ =>
    match requestAux file labels right.memory left.control left.stack false with
    | .scheduled choices => (false, choices.map fun (control, frames) => leftWrap labels right outer control frames)
    | .memory name memory control frames =>
        (true, [(.commitMemory name memory (.interleave [] [(0, control, frames), (1, right.control, right.stack)]), outer)])
    | .next (.jumping symbol values environment) _ =>
        (true, [arenaJump labels symbol values environment outer])
    | .update memory control frames =>
        (true, [(.commitUpdate memory (.interleave [] [(0, control, frames), (1, right.control, right.stack)]), outer)])
    | .pull action control frames =>
        (true, match liftAction right.memory action
          (.interleave [] [(0, control, frames), (1, right.control, right.stack)]) outer with
        | .update memory next frames => [(.commitUpdate memory next, frames)]
        | .pull action next frames => [(.pulling action next frames, [])]
        | _ => [])
    | .next control frames => (true, [leftWrap labels right outer control frames])
    | .choose choices => (true, choices.map fun (control, frames) => leftWrap labels right outer control frames)
    | .end_ outcome => (true, [(.raise outcome, [])])

private def chooseGroups (groups : List (Bool × List (Control × List Frame))) : Request :=
  match groups.find? (·.1) with
  | some (_, choices) => .choose choices
  | none => .scheduled (groups.flatMap (·.2))

/-- An equation of the actual scheduler, not a replacement scheduler. -/
private theorem pair_request {file : Program} {labels : Labels} {left source : Dynamics.State}
    (leftPlain : Plain left) (sourcePlain : Plain source) (outer : List Frame) :
    requestAux file labels source.memory (pair left.control left.stack source).control outer false =
      chooseGroups [pairRightGroup file labels left source outer, pairLeftGroup file labels left source outer] := by
  change requestAux file labels source.memory
    (.interleave [] [(0, left.control, left.stack), (1, source.control, source.stack)]) outer false = _
  rw [requestAux]
  · simp [leftPlain.inactive, sourcePlain.inactive, leftPlain.callfree, sourcePlain.callfree,
      awaitsScheduling, pairRightGroup, pairLeftGroup, pairWrap, leftWrap, chooseGroups, List.filter]
    rfl
  · intro impossible
    cases impossible

private theorem pairRightGroup_next {file : Program} {labels : Labels} {left source : Dynamics.State}
    (running : NotDone source) (control : Control) (frames : List Frame) (valid : unwrapped control = true)
    (requested : requestAux file labels source.memory source.control source.stack false = .next control frames)
    (outer : List Frame) :
    pairRightGroup file labels left source outer =
      (true, [((pair left.control left.stack ⟨control, frames, source.memory⟩).control, outer)]) := by
  unfold pairRightGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    cases control <;> simp_all [Silmaril.Cerberus.Core.Administrative.unwrapped, pairWrap, pair]

private theorem pair_request_next {file : Program} {labels : Labels} {left source : Dynamics.State}
    (leftPlain : Plain left) (sourcePlain : Plain source) (running : NotDone source)
    (control : Control) (frames : List Frame) (valid : unwrapped control = true)
    (requested : requestAux file labels source.memory source.control source.stack false = .next control frames)
    (outer : List Frame) :
    requestAux file labels source.memory (pair left.control left.stack source).control outer false =
      .choose [((pair left.control left.stack ⟨control, frames, source.memory⟩).control, outer)] := by
  rw [pair_request leftPlain sourcePlain, pairRightGroup_next running control frames valid requested]
  rfl

private theorem pairRightGroup_choose {file : Program} {labels : Labels} {left source : Dynamics.State}
    (running : NotDone source) (control : Control) (frames : List Frame) (valid : unwrapped control = true)
    (requested : requestAux file labels source.memory source.control source.stack false = .choose [(control, frames)])
    (outer : List Frame) :
    pairRightGroup file labels left source outer =
      (true, [((pair left.control left.stack ⟨control, frames, source.memory⟩).control, outer)]) := by
  unfold pairRightGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    cases control <;> simp_all [Silmaril.Cerberus.Core.Administrative.unwrapped, pairWrap, pair]

private theorem pairRightGroup_update {file : Program} {labels : Labels} {left source : Dynamics.State}
    (running : NotDone source) (control : Control) (frames : List Frame) (memory : Mem.Concrete.State)
    (requested : requestAux file labels source.memory source.control source.stack false = .update memory control frames)
    (outer : List Frame) :
    pairRightGroup file labels left source outer =
      (true, [(.commitUpdate memory (pair left.control left.stack ⟨control, frames, memory⟩).control, outer)]) := by
  unfold pairRightGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    rfl

theorem NotDone.pair (left : Control) (frames : List Frame) (right : Dynamics.State) :
    NotDone (pair left frames right) := by
  intro value accesses impossible
  cases impossible

theorem Plain.withMemory {state : Dynamics.State} (plain : Plain state) (memory : Mem.Concrete.State) :
    Plain ⟨state.control, state.stack, memory⟩ :=
  ⟨plain.unwrapped, plain.callfree, plain.inactive⟩

theorem Plain.commitUpdate {control : Control} {sourceMemory : Mem.Concrete.State}
    (plain : Plain ⟨control, [], sourceMemory⟩) (memory : Mem.Concrete.State) :
    Plain ⟨.commitUpdate memory control, [], sourceMemory⟩ := by
  constructor
  · rfl
  · change controlHasCCall (.commitUpdate memory control) [] = false
    rw [controlHasCCall]
    simpa only [List.any_nil, Bool.or_false] using plain.callfree
  · change activeCall (.commitUpdate memory control) [] = false
    rw [activeCall]
    simpa only [List.any_nil, Bool.false_or] using plain.inactive

theorem NotDone.commitUpdate (memory sourceMemory : Mem.Concrete.State) (control : Control) :
    NotDone ⟨.commitUpdate memory control, [], sourceMemory⟩ := by
  intro value accesses impossible
  cases impossible

/-- Lift one real child edge into the scheduler's right operand. An actual
update is selected as a commitUpdate control and then actually committed. -/
theorem Edge.pairRight {file : Program} {labels : Labels} {left source target : Dynamics.State}
    (leftPlain : Plain left) (edge : Edge file labels source target) :
    Path file labels (pair left.control left.stack source) (pair left.control left.stack target) := by
  cases edge with
  | @next control frames sourcePlain running targetPlain requested =>
    show Path file labels (pair left.control left.stack source)
      (pair left.control left.stack ⟨control, frames, source.memory⟩)
    apply Path.cons (Edge.choose (source := pair left.control left.stack source)
      (control := (pair left.control left.stack ⟨control, frames, source.memory⟩).control) (frames := [])
      (leftPlain.pair sourcePlain) (NotDone.pair _ _ _)
      (leftPlain.pair targetPlain) ?_) (.refl (leftPlain.pair targetPlain))
    intro outer
    simpa only [pair, List.nil_append, List.append_nil] using
      pair_request_next leftPlain sourcePlain running control frames targetPlain.unwrapped (by simpa using requested []) outer
  | @choose control frames sourcePlain running targetPlain requested =>
    show Path file labels (pair left.control left.stack source)
      (pair left.control left.stack ⟨control, frames, source.memory⟩)
    apply Path.cons (Edge.choose (source := pair left.control left.stack source)
      (control := (pair left.control left.stack ⟨control, frames, source.memory⟩).control) (frames := [])
      (leftPlain.pair sourcePlain) (NotDone.pair _ _ _)
      (leftPlain.pair targetPlain) ?_) (.refl (leftPlain.pair targetPlain))
    intro outer
    change requestAux file labels source.memory (pair left.control left.stack source).control outer false = _
    rw [pair_request leftPlain sourcePlain,
      pairRightGroup_choose running control frames targetPlain.unwrapped (by simpa using requested [])]
    rfl
  | @update control frames memory sourcePlain running targetPlain requested =>
    show Path file labels (pair left.control left.stack source)
      (pair left.control left.stack ⟨control, frames, memory⟩)
    let next := pair left.control left.stack ⟨control, frames, memory⟩
    have nextPlain : Plain next := leftPlain.pair targetPlain
    have commitPlain : Plain ⟨.commitUpdate memory next.control, [], source.memory⟩ :=
      (nextPlain.withMemory source.memory).commitUpdate memory
    apply Path.cons (Edge.choose (leftPlain.pair sourcePlain) (NotDone.pair _ _ _) commitPlain ?_)
    · apply Path.cons (Edge.update commitPlain (NotDone.commitUpdate _ _ _) nextPlain ?_) (.refl nextPlain)
      intro outer
      simp [requestAux, awaitsScheduling, next, pair]
    · intro outer
      change requestAux file labels source.memory (pair left.control left.stack source).control outer false = _
      rw [pair_request leftPlain sourcePlain,
        pairRightGroup_update running control frames memory (by simpa using requested [])]
      rfl

theorem Path.pairRight {file : Program} {labels : Labels} {left source target : Dynamics.State}
    (leftPlain : Plain left) (path : Path file labels source target) :
    Path file labels (pair left.control left.stack source) (pair left.control left.stack target) := by
  induction path with
  | refl plain => exact .refl (leftPlain.pair plain)
  | cons edge _ ih => exact (edge.pairRight leftPlain).trans ih

/-- The scheduler removes the actually finished right operand and retains its
real annotation list. The left operand resumes in the current shared memory. -/
theorem pair_completeRight {file : Program} {labels : Labels} {left right : Dynamics.State}
    (leftPlain : Plain left) (rightPlain : Plain right) (value : Val) (accesses : List Access)
    (valueEq : right.control = .value value) (annotationsEq : annotationsOnly right.stack = some accesses) :
    Path file labels (pair left.control left.stack right)
      (single [(1, value, accesses)] ⟨left.control, left.stack, right.memory⟩) := by
  have targetPlain := (leftPlain.withMemory right.memory).single [(1, value, accesses)]
  apply Path.cons (Edge.choose (source := pair left.control left.stack right)
    (control := (single [(1, value, accesses)] ⟨left.control, left.stack, right.memory⟩).control) (frames := [])
    (leftPlain.pair rightPlain) (NotDone.pair _ _ _) targetPlain ?_) (.refl targetPlain)
  intro outer
  change requestAux file labels right.memory (pair left.control left.stack right).control outer false = _
  rw [pair_request leftPlain rightPlain]
  unfold pairRightGroup
  rw [valueEq, annotationsEq]
  rfl

private def singleWrap (labels : Labels) (done : List (Nat × Val × List Access)) (outer : List Frame)
    (control : Control) (frames : List Frame) : Control × List Frame :=
  match control with
  | .raise outcome => (.raise outcome, [])
  | .jumping symbol values environment => arenaJump labels symbol values environment outer
  | _ => (.interleave done [(0, control, frames)], outer)

private def singleGroup (file : Program) (labels : Labels) (done : List (Nat × Val × List Access))
    (source : Dynamics.State) (outer : List Frame) : Bool × List (Control × List Frame) :=
  match source.control, annotationsOnly source.stack with
  | .value value, some accesses => (true, [(.interleave ((0, value, accesses) :: done) [], outer)])
  | _, _ =>
    match requestAux file labels source.memory source.control source.stack false with
    | .scheduled choices => (false, choices.map fun (control, frames) => singleWrap labels done outer control frames)
    | .memory name memory control frames =>
        (true, [(.commitMemory name memory (.interleave done [(0, control, frames)]), outer)])
    | .next (.jumping symbol values environment) _ =>
        (true, [arenaJump labels symbol values environment outer])
    | .update memory control frames =>
        (true, [(.commitUpdate memory (.interleave done [(0, control, frames)]), outer)])
    | .pull action control frames =>
        (true, match liftAction source.memory action (.interleave done [(0, control, frames)]) outer with
        | .update memory next frames => [(.commitUpdate memory next, frames)]
        | .pull action next frames => [(.pulling action next frames, [])]
        | _ => [])
    | .next control frames => (true, [singleWrap labels done outer control frames])
    | .choose choices => (true, choices.map fun (control, frames) => singleWrap labels done outer control frames)
    | .end_ outcome => (true, [(.raise outcome, [])])

private theorem single_request {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source : Dynamics.State} (plain : Plain source) (outer : List Frame) :
    requestAux file labels source.memory (single done source).control outer false =
      chooseGroups [singleGroup file labels done source outer] := by
  change requestAux file labels source.memory (.interleave done [(0, source.control, source.stack)]) outer false = _
  rw [requestAux]
  · simp [plain.inactive, awaitsScheduling, singleGroup, singleWrap, chooseGroups, List.filter]
    rfl
  · intro impossible
    cases impossible

private theorem singleGroup_next {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source : Dynamics.State} (running : NotDone source) (control : Control) (frames : List Frame)
    (valid : unwrapped control = true)
    (requested : requestAux file labels source.memory source.control source.stack false = .next control frames)
    (outer : List Frame) :
    singleGroup file labels done source outer =
      (true, [((single done ⟨control, frames, source.memory⟩).control, outer)]) := by
  unfold singleGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    cases control <;> simp_all [Silmaril.Cerberus.Core.Administrative.unwrapped, singleWrap, single]

private theorem singleGroup_choose {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source : Dynamics.State} (running : NotDone source) (control : Control) (frames : List Frame)
    (valid : unwrapped control = true)
    (requested : requestAux file labels source.memory source.control source.stack false = .choose [(control, frames)])
    (outer : List Frame) :
    singleGroup file labels done source outer =
      (true, [((single done ⟨control, frames, source.memory⟩).control, outer)]) := by
  unfold singleGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    cases control <;> simp_all [Silmaril.Cerberus.Core.Administrative.unwrapped, singleWrap, single]

private theorem singleGroup_update {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source : Dynamics.State} (running : NotDone source) (control : Control) (frames : List Frame)
    (memory : Mem.Concrete.State)
    (requested : requestAux file labels source.memory source.control source.stack false = .update memory control frames)
    (outer : List Frame) :
    singleGroup file labels done source outer =
      (true, [(.commitUpdate memory (single done ⟨control, frames, memory⟩).control, outer)]) := by
  unfold singleGroup
  split
  · rename_i value accesses controlEq annotationsEq
    exact (running value accesses controlEq annotationsEq).elim
  · rw [requested]
    rfl

theorem NotDone.single (done : List (Nat × Val × List Access)) (child : Dynamics.State) :
    NotDone (single done child) := by
  intro value accesses impossible
  cases impossible

/-- Lift into the last active operand, retaining genuine commit updates. -/
theorem Edge.inSingle {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source target : Dynamics.State} (edge : Edge file labels source target) :
    Path file labels (single done source) (single done target) := by
  cases edge with
  | @next control frames sourcePlain running targetPlain requested =>
    show Path file labels (single done source) (single done ⟨control, frames, source.memory⟩)
    apply Path.cons (Edge.choose (source := single done source)
      (control := (single done ⟨control, frames, source.memory⟩).control) (frames := [])
      (sourcePlain.single done) (NotDone.single _ _) (targetPlain.single done) ?_)
      (.refl (targetPlain.single done))
    intro outer
    change requestAux file labels source.memory (single done source).control outer false = _
    rw [single_request done sourcePlain,
      singleGroup_next done running control frames targetPlain.unwrapped (by simpa using requested [])]
    rfl
  | @choose control frames sourcePlain running targetPlain requested =>
    show Path file labels (single done source) (single done ⟨control, frames, source.memory⟩)
    apply Path.cons (Edge.choose (source := single done source)
      (control := (single done ⟨control, frames, source.memory⟩).control) (frames := [])
      (sourcePlain.single done) (NotDone.single _ _) (targetPlain.single done) ?_)
      (.refl (targetPlain.single done))
    intro outer
    change requestAux file labels source.memory (single done source).control outer false = _
    rw [single_request done sourcePlain,
      singleGroup_choose done running control frames targetPlain.unwrapped (by simpa using requested [])]
    rfl
  | @update control frames memory sourcePlain running targetPlain requested =>
    show Path file labels (single done source) (single done ⟨control, frames, memory⟩)
    let next := single done ⟨control, frames, memory⟩
    have nextPlain : Plain next := targetPlain.single done
    have commitPlain : Plain ⟨.commitUpdate memory next.control, [], source.memory⟩ :=
      (nextPlain.withMemory source.memory).commitUpdate memory
    apply Path.cons (Edge.choose (source := single done source)
      (sourcePlain.single done) (NotDone.single _ _) commitPlain ?_)
    · apply Path.cons (Edge.update commitPlain (NotDone.commitUpdate _ _ _) nextPlain ?_) (.refl nextPlain)
      intro outer
      simp [requestAux, awaitsScheduling, next, single]
    · intro outer
      change requestAux file labels source.memory (single done source).control outer false = _
      rw [single_request done sourcePlain,
        singleGroup_update done running control frames memory (by simpa using requested [])]
      rfl

theorem Path.inSingle {file : Program} {labels : Labels} (done : List (Nat × Val × List Access))
    {source target : Dynamics.State} (path : Path file labels source target) :
    Path file labels (single done source) (single done target) := by
  induction path with
  | refl plain => exact .refl (plain.single done)
  | cons edge _ ih => exact (edge.inSingle done).trans ih

theorem Plain.emptyInterleave (done : List (Nat × Val × List Access)) (memory : Mem.Concrete.State) :
    Plain ⟨.interleave done [], [], memory⟩ := by
  constructor
  · rfl
  · simp [controlHasCCall]
  · simp [activeCall]

/-- After both real operands finish without accesses, the actual scheduler
sorts their source positions and produces the source-ordered tuple. -/
theorem single_finishPair {file : Program} {labels : Labels} (leftValue rightValue : Val)
    (frames : List Frame) (memory : Mem.Concrete.State)
    (annotations : annotationsOnly frames = some [])
    (plain : Plain ⟨.value leftValue, frames, memory⟩) :
    Path file labels (single [(1, rightValue, [])] ⟨.value leftValue, frames, memory⟩)
      ⟨.value (.tuple [leftValue, rightValue]), [.annotations []], memory⟩ := by
  let done : List (Nat × Val × List Access) := [(0, leftValue, []), (1, rightValue, [])]
  have emptyPlain := Plain.emptyInterleave done memory
  have valuePlain : Plain ⟨.value (.tuple [leftValue, rightValue]), [.annotations []], memory⟩ := by
    constructor
    · rfl
    · simp [controlHasCCall]
    · simp [activeCall]
  apply Path.cons (Edge.choose (source := single [(1, rightValue, [])] ⟨.value leftValue, frames, memory⟩)
    (control := .interleave done []) (frames := []) (plain.single _)
    (NotDone.single _ _) emptyPlain ?_)
  · apply Path.cons (Edge.next emptyPlain (by intro value accesses impossible; cases impossible) valuePlain ?_)
      (.refl valuePlain)
    intro outer
    simp [requestAux, awaitsScheduling, done]
  · intro outer
    change requestAux file labels memory (single [(1, rightValue, [])] ⟨.value leftValue, frames, memory⟩).control outer false = _
    rw [single_request _ plain]
    unfold singleGroup
    rw [annotations]
    rfl

private theorem unseq_start {file : Program} {labels : Labels} (left right : EE) (environment : Env)
    (memory : Mem.Concrete.State) (leftPlain : Plain ⟨.effectExpr left environment, [], memory⟩)
    (rightPlain : Plain ⟨.effectExpr right environment, [], memory⟩) :
    Path file labels ⟨.effectExpr (.mk [] (.unseq [left, right])) environment, [], memory⟩
      (pair (.effectExpr left environment) [] ⟨.effectExpr right environment, [], memory⟩) := by
  have leftFree : hasCCall left = false := by simpa [controlHasCCall] using leftPlain.callfree
  have rightFree : hasCCall right = false := by simpa [controlHasCCall] using rightPlain.callfree
  have plain : Plain ⟨.effectExpr (.mk [] (.unseq [left, right])) environment, [], memory⟩ := by
    constructor
    · rfl
    · simp [controlHasCCall, hasCCall, leftFree, rightFree]
    · simp [activeCall]
  have paired := leftPlain.pair rightPlain
  apply Path.cons (Edge.next plain (by intro value accesses impossible; cases impossible) paired ?_)
    (.refl paired)
  intro outer
  simp [requestAux, awaitsScheduling]

/-- Compose two independently derived child traces through actual unseq
scheduling. Right is evaluated first; values retain left-to-right source order.
The final source theorem supplies these traces by induction on its source. -/
theorem unseq_pair {file : Program} {labels : Labels} (left right : EE) (environment : Env)
    (leftValue rightValue : Val) (leftFrames rightFrames : List Frame)
    (memory rightMemory finalMemory : Mem.Concrete.State)
    (rightPath : Path file labels ⟨.effectExpr right environment, [], memory⟩
      ⟨.value rightValue, rightFrames, rightMemory⟩)
    (rightAnnotations : annotationsOnly rightFrames = some [])
    (leftPath : Path file labels ⟨.effectExpr left environment, [], rightMemory⟩
      ⟨.value leftValue, leftFrames, finalMemory⟩)
    (leftAnnotations : annotationsOnly leftFrames = some []) :
    Path file labels ⟨.effectExpr (.mk [] (.unseq [left, right])) environment, [], memory⟩
      ⟨.value (.tuple [leftValue, rightValue]), [.annotations []], finalMemory⟩ := by
  have leftPlain := leftPath.source_plain
  exact (unseq_start left right environment memory (leftPlain.withMemory memory) rightPath.source_plain).trans
    ((rightPath.pairRight leftPlain).trans
      ((pair_completeRight leftPlain rightPath.target_plain rightValue [] rfl rightAnnotations).trans
        ((leftPath.inSingle [(1, rightValue, [])]).trans
          (single_finishPair leftValue rightValue leftFrames finalMemory leftAnnotations leftPath.target_plain))))

end Silmaril.Cerberus.Core.Administrative
