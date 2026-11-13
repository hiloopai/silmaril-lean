module

public import Silmaril.Cerberus.Core.Interleave.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false

/-! # Procedure-local label transfers in operand arenas

A deferred label transfer carries no procedure boundary. This is the boundary
fact needed when lifting a procedure's execution into an unsequenced operand.
-/

@[expose] public section

namespace Silmaril.Cerberus.Core.ArenaLift

open Silmaril.Cerberus.Core.Dynamics

/-- A request that does not expose a deferred label transfer. -/
def NoJump (r : Request) : Prop :=
  ∀ s vs env k, r ≠ .next (.jumping s vs env) k

@[simp] theorem noJump_memory (name : String) (m : Mem.Concrete.State) (c : Control)
    (k : List Frame) : NoJump (.memory name m c k) := by simp [NoJump]
@[simp] theorem noJump_update (m : Mem.Concrete.State) (c : Control) (k : List Frame) :
    NoJump (.update m c k) := by simp [NoJump]
@[simp] theorem noJump_pull (a c : Control) (k : List Frame) : NoJump (.pull a c k) := by
  simp [NoJump]
@[simp] theorem noJump_choose (cs : List (Control × List Frame)) : NoJump (.choose cs) := by
  simp [NoJump]
@[simp] theorem noJump_scheduled (cs : List (Control × List Frame)) : NoJump (.scheduled cs) := by
  simp [NoJump]
@[simp] theorem noJump_end (o : Outcome) : NoJump (.end_ o) := by simp [NoJump]

private theorem jump_noJump (labels : Labels) (s : Sym) (vs : List Val) (env : Env)
    (k : List Frame) : NoJump (jump labels s vs env k) := by
  unfold jump jumpDestination
  cases hc : procedureContext labels k with
  | mk ls retained =>
    dsimp only
    cases hl : ls.lookup s with
    | none => simp
    | some entry =>
      obtain ⟨ps, body⟩ := entry
      dsimp only
      by_cases ha : ps.length == vs.length <;> simp [ha, NoJump]

private theorem requestJump_noJump (labels : Labels) (s : Sym) (vs : List Val) (env : Env)
    (k : List Frame) (hb : hasBoundary k = true) :
    NoJump (requestJump labels s vs env k) := by
  simpa [requestJump, hb] using jump_noJump labels s vs env k

@[simp] theorem arguments_noJump (op : Prim) (ps : List PE) (env : Env) (k : List Frame) :
    NoJump (arguments op ps env k) := by cases ps <;> simp [arguments, NoJump]

@[simp] theorem memoryRequest_noJump (m : Mem.Concrete.State) (op : MemoryOp)
    (vs : List Val) (k : List Frame) (tags : Mem.Concrete.Tags) :
    NoJump (memoryRequest m op vs k tags) := by
  unfold memoryRequest
  extract_lets result
  cases hr : result with
  | ok pair =>
    obtain ⟨v, m'⟩ := pair
    exact noJump_memory _ _ _ _
  | error e => cases e <;> exact noJump_end _

@[simp] theorem liftAction_noJump (m : Mem.Concrete.State) (a c : Control) (k : List Frame) :
    NoJump (liftAction m a c k) := by
  unfold liftAction
  dsimp only
  split
  · exact noJump_pull _ _ _
  · exact noJump_update _ _ _

@[simp] theorem scheduledRequest_noJump (r : Request) : NoJump (scheduledRequest r) := by
  cases r <;> simp [scheduledRequest]

/-- Location bookkeeping cannot introduce a deferred jump. -/
theorem location_noJump (r : Request) (loc prior : Loc) :
    NoJump r → NoJump (if loc == prior then r else match r with
      | .next c frames => .next (.setLocation loc c) frames
      | .choose cs => .choose (cs.map fun (c, frames) => (.setLocation loc c, frames))
      | .scheduled cs => .scheduled (cs.map fun (c, frames) => (.setLocation loc c, frames))
      | r => r) := by
  intro h
  split
  · exact h
  · cases r <;> simp_all [NoJump]

/-- A sole operand may take its scheduled call step after its siblings have
finished. The arena retains the operand's own procedure frames. -/
theorem requestAux_sole_scheduled (file : Program) (labels : Labels)
    (m : Mem.Concrete.State) (done : List (Nat × (Val × List Access)))
    (i : Nat) (c c' : Control) (fr fr' k : List Frame)
    (hunf : Interleave.Unfinished ⟨c, fr, m⟩)
    (hr : requestAux file labels m c fr false = .scheduled [(c', fr')])
    (hp : Interleave.Plain c') :
    requestAux file labels m (.interleave done [(i, c, fr)]) k false =
      .scheduled [(.interleave done [(i, c', fr')], k)] := by
  have wrap : (match c' with
      | .raise o => (Control.raise o, ([] : List Frame))
      | .jumping s vs env => arenaJump labels s vs env k
      | _ => (Control.interleave done [(i, c', fr')], k)) =
      (.interleave done [(i, c', fr')], k) := by
    cases c' <;> simp_all [Interleave.Plain]
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_and, Bool.false_or, Bool.or_false,
    List.any_cons, List.any_nil, List.attach_cons, List.attach_nil,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.filter_cons, List.filter_nil, beq_self_eq_true, bne_self_eq_false,
    Bool.and_not_self, Bool.false_eq_true, ite_false, ite_true,
    List.nil_append, List.find?_cons, List.find?_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases c
  case value v =>
    simp only [hunf v rfl, hr, List.map_cons, List.map_nil]
    exact congrArg (fun p => Request.scheduled [p]) wrap
  all_goals
    simp only [hr, List.map_cons, List.map_nil]
    exact congrArg (fun p => Request.scheduled [p]) wrap

/-- Annotation propagation preserves the absence of a deferred transfer. -/
theorem annotations_noJump (r : Request) (xs : List Access) :
    NoJump r → NoJump (match r with
      | .next c fr => .next c (.annotations xs :: fr)
      | .memory name m c fr => .memory name m c (.annotations xs :: fr)
      | .update m c fr => .update m c (.annotations xs :: fr)
      | .pull a c fr => .pull a c (.annotations xs :: fr)
      | .choose cs => .choose (cs.map fun (c, fr) => (c, .annotations xs :: fr))
      | .scheduled cs => .scheduled (cs.map fun (c, fr) => (c, .annotations xs :: fr))
      | .end_ o => .end_ o) := by
  intro h
  cases r with
  | next c fr =>
    intro s vs env k he
    exact h s vs env fr (congrArg (fun c => Request.next c fr) (Request.next.inj he).1)
  | memory name m c fr => exact noJump_memory _ _ _ _
  | update m c fr => exact noJump_update _ _ _
  | pull a c fr => exact noJump_pull _ _ _
  | choose cs => exact noJump_choose _
  | scheduled cs => exact noJump_scheduled _
  | end_ o => exact noJump_end _

/-- Values resolve a label transfer using their own procedure frames. -/
theorem requestAux_value_noJump (file : Program) (labels : Labels)
    (v : Val) (m : Mem.Concrete.State) (k : List Frame) (wc : Bool)
    (hb : hasBoundary k = true) : NoJump (requestAux file labels m (.value v) k wc) := by
  induction k generalizing m wc with
  | nil => simp [hasBoundary] at hb
  | cons f rest ih =>
    cases f <;> rw [requestAux.eq_def] <;>
      simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
    case annotations xs =>
      have hrest : hasBoundary rest = true := by simpa [hasBoundary] using hb
      have hi := ih m (wc && !(List.any (.annotations xs :: rest) Interleave.isBound)) hrest
      cases rest with
      | nil => simp [hasBoundary] at hrest
      | cons f rest =>
        cases f <;> dsimp only
        all_goals first
          | solve | simp [NoJump]
          | apply annotations_noJump; exact hi
    all_goals repeat' first
      | solve
          | exact memoryRequest_noJump _ _ _ _ _
          | exact requestJump_noJump _ _ _ _ _ (by simpa [hasBoundary] using hb)
          | simp_all [NoJump]
      | split

/-- Pure expression decomposition never emits a label transfer. -/
theorem requestAux_pure_noJump (file : Program) (labels : Labels)
    (p : PE) (env : Env) (m : Mem.Concrete.State) (k : List Frame) (wc : Bool) :
    NoJump (requestAux file labels m (.pureExpr p env) k wc) := by
  obtain ⟨ann, ty, p⟩ := p
  cases p <;> rw [requestAux.eq_def] <;>
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  all_goals repeat' first
    | solve
        | exact arguments_noJump _ _ _ _
        | simp_all [NoJump]
    | split

private theorem next_noJump (c : Control) (k : List Frame)
    (hp : ∀ s vs env, c ≠ .jumping s vs env) : NoJump (.next c k) := by
  intro s vs env fr he
  exact hp s vs env (Request.next.inj he).1

private theorem ite_noJump (p : Prop) [Decidable p] (a b : Request) :
    NoJump a → NoJump b → NoJump (if p then a else b) := by
  intro ha hb
  split
  · exact ha
  · exact hb

/-- A primitive application returns values, expressions, or scheduled requests. -/
theorem requestAux_apply_noJump (file : Program) (labels : Labels)
    (op : Prim) (vs : List Val) (m : Mem.Concrete.State) (k : List Frame) (wc : Bool) :
    NoJump (requestAux file labels m (.apply op vs) k wc) := by
  cases op <;> rw [requestAux.eq_def] <;>
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  all_goals repeat' first
    | solve
        | contradiction
        | with_reducible exact scheduledRequest_noJump _
        | with_reducible exact memoryRequest_noJump _ _ _ _ _
        | with_reducible exact noJump_memory _ _ _ _
        | with_reducible exact noJump_end _
        | apply next_noJump; intro s vs env h; cases h
    | refine ite_noJump _ _ _ ?_ ?_
    | split

/-- An effect expression resolves its run using the visible procedure boundary. -/
theorem requestAux_effect_noJump (file : Program) (labels : Labels)
    (e : EE) (env : Env) (m : Mem.Concrete.State) (k : List Frame) (wc : Bool)
    (hb : hasBoundary k = true) :
    NoJump (requestAux file labels m (.effectExpr e env) k wc) := by
  obtain ⟨ann, e⟩ := e
  cases e <;> rw [requestAux.eq_def] <;>
    simp only [awaitsScheduling, Bool.false_eq_true, ite_false]
  all_goals try apply location_noJump
  all_goals repeat' first
    | solve
        | contradiction
        | with_reducible exact arguments_noJump _ _ _ _
        | with_reducible exact liftAction_noJump _ _ _ _
        | with_reducible exact requestJump_noJump _ _ _ _ _ hb
        | with_reducible exact noJump_choose _
        | with_reducible exact noJump_end _
        | apply next_noJump; intro s vs env h; cases h
    | split

private theorem select_noJump (groups : List (Bool × List (Control × List Frame))) :
    NoJump (match groups.find? (·.1) with
      | some (_, cs) => .choose cs
      | none => .scheduled (groups.flatMap (·.2))) := by
  cases hg : groups.find? (·.1) with
  | none => exact noJump_scheduled _
  | some pair => obtain ⟨_, cs⟩ := pair; exact noJump_choose _

/-- An arena answers by choosing or scheduling, never with a deferred jump. -/
theorem requestAux_interleave_noJump (file : Program) (labels : Labels)
    (done : List (Nat × (Val × List Access))) (ts : List (Nat × (Control × List Frame)))
    (m : Mem.Concrete.State) (k : List Frame) (wc : Bool) :
    NoJump (requestAux file labels m (.interleave done ts) k wc) := by
  rw [requestAux.eq_def]
  simp only [awaitsScheduling, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  cases ts with
  | nil =>
    repeat' first
      | solve
          | contradiction
          | with_reducible exact noJump_end _
          | with_reducible exact noJump_choose _
          | with_reducible exact noJump_scheduled _
          | apply next_noJump; intro s vs env h; cases h
      | split
  | cons t ts => exact select_noJump _

/-- A visible procedure boundary resolves transfers before an operand can
expose a jumping control (lemma J). -/
theorem requestAux_noJump (file : Program) (labels : Labels) (m : Mem.Concrete.State)
    (c : Control) (k : List Frame) (wc : Bool) (hb : hasBoundary k = true) :
    NoJump (requestAux file labels m c k wc) := by
  cases c
  case value v => exact requestAux_value_noJump file labels v m k wc hb
  case pureExpr p env => exact requestAux_pure_noJump file labels p env m k wc
  case apply op vs => exact requestAux_apply_noJump file labels op vs m k wc
  case effectExpr e env => exact requestAux_effect_noJump file labels e env m k wc hb
  case interleave done ts => exact requestAux_interleave_noJump file labels done ts m k wc
  all_goals rw [requestAux.eq_def]
  all_goals simp only [awaitsScheduling, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  all_goals repeat' first
    | solve
        | contradiction
        | with_reducible exact memoryRequest_noJump _ _ _ _ _
        | with_reducible exact liftAction_noJump _ _ _ _
        | with_reducible exact requestJump_noJump _ _ _ _ _ hb
        | with_reducible exact noJump_memory _ _ _ _
        | with_reducible exact noJump_update _ _ _
        | with_reducible exact noJump_end _
        | apply next_noJump; intro s vs env h; cases h
    | split

/-- With a visible boundary, the top-level normalizer has no extra work. -/
theorem request_eq_aux (file : Program) (labels : Labels) (s : State)
    (hb : hasBoundary s.stack = true) :
    request file labels s = requestAux file labels s.memory s.control s.stack false := by
  unfold request
  have hj := requestAux_noJump file labels s.memory s.control s.stack false hb
  generalize he : requestAux file labels s.memory s.control s.stack false = r at *
  cases r
  case next c k =>
    cases c
    case jumping sym vs env => exact (hj sym vs env k rfl).elim
    all_goals rfl
  all_goals rfl

end Silmaril.Cerberus.Core.ArenaLift
