module

public import Silmaril.Cerberus.Spec.Allowed.Defs
public import Silmaril.Cerberus.Core.Explore.Defs

/-! # A bounded decision procedure for `Spec.allowed`

`check` explores the Core LTS depth-first from the program's initial state, over every
successor that `Core.Dynamics.successors` enumerates (proved complete and sound for the
transition relation by `successors_correct`). It keeps no visited set: a path is a stack entry,
so memory is proportional to the number of open choice points, not to the length of a run.

Several observations of one program are decided in one exploration. An observation is
`admitted` as soon as a halted state admits it, and every pending observation is admitted when
an undefined behaviour is reached. When the exploration ends:

* `admitted`: proved to imply `Spec.allowed` (`check_sound`);
* `rejected`: the exploration was exhaustive (no budget or depth limit was hit) and reached no
  `error` or `unsupported` ending, and no halted state admits the observation;
* `unknown`: otherwise (a bound was exhausted, or the program left the supported fragment).

Both directions are proved: `check_sound` (admitted → allowed) and `check_complete`
(rejected → not allowed: an exhaustive exploration visits every reachable halted state). An
`error` or `unsupported` ending makes the result `unknown` although `Spec.allowed` admits nothing
there: such a program is outside the fragment where the specification is meant to be C. -/

@[expose] public section
namespace Silmaril.Cerberus.Spec

open Core.Dynamics

inductive Verdict where
  | admitted
  | rejected
  | unknown
  deriving DecidableEq, Repr

/-- Exploration bounds: `depth` transitions on one path, `budget` stack pops in all. -/
structure Bounds where
  depth : Nat := 3000000
  budget : Nat := 20000000

/-- The state of an exploration. `outcomes` keeps up to `keep` distinct oracle observations of
the halted states, for diagnostics only. -/
structure Search where
  admitted : List Obs
  pending : List Obs
  steps : Nat := 0
  leaves : Nat := 0
  limited : Bool := false
  gap : Bool := false
  ub : Bool := false
  /-- Every query was admitted before the exploration was exhaustive. -/
  stopped : Bool := false
  outcomes : List Observation := []

def keep : Nat := 32

def Search.leaf (impl : Impl) (acc : Search) (o : Outcome) (out : String) : Search :=
  let obs := {observation (some o) with stdout := out}
  let outcomes := if acc.outcomes.length < keep && !acc.outcomes.contains obs then
      acc.outcomes ++ [obs] else acc.outcomes
  let gap := match o with
    | .error _ | .unsupported _ => true
    | _ => acc.gap
  let ub := match o with
    | .ub _ _ => true
    | _ => acc.ub
  { acc with
    admitted := acc.admitted ++ acc.pending.filter fun x => decide (admits impl o out x)
    pending := acc.pending.filter fun x => !decide (admits impl o out x)
    leaves := acc.leaves + 1, gap, ub, outcomes }

/-- Depth-first exploration. Stack entries carry the remaining per-path depth. -/
def search (impl : Impl) (file : Program) (labels : Labels) :
    Nat → List (Nat × State) → Search → Search
  | 0, stack, acc => if stack.isEmpty then acc else { acc with limited := true }
  | _ + 1, [], acc => acc
  | budget + 1, (depth, s) :: rest, acc =>
      if acc.pending.isEmpty then { acc with stopped := true } else
      match s.control with
      | .halt o => search impl file labels budget rest (acc.leaf impl o s.memory.stdout)
      | _ => match depth with
        | 0 => search impl file labels budget rest { acc with limited := true }
        | d + 1 =>
            search impl file labels budget
              ((successors file labels s).map (fun p => (d, p.2)) ++ rest)
              { acc with steps := acc.steps + 1 }

structure Result where
  search : Search
  /-- The exploration was exhaustive and stayed inside the supported fragment. -/
  decided : Bool

def Result.verdict (r : Result) (obs : Obs) : Verdict :=
  if r.search.admitted.contains obs then .admitted
  else if r.decided && r.search.pending.contains obs then .rejected
  else .unknown

/-- Explore the program once and decide every observation of `queries`. -/
def check (impl : Impl) (file : Program) (enums : Map Sym IntegerType) (args : List String)
    (queries : List Obs) (bounds : Bounds := {}) : Result :=
  match initial file enums (Core.Startup.execArguments args) with
  | .error o =>
      let acc := Search.leaf impl { admitted := [], pending := queries } o ""
      ⟨acc, !acc.gap⟩
  | .ok (start, labels) =>
      let acc := search impl file labels bounds.budget [(bounds.depth, start)]
        { admitted := [], pending := queries }
      ⟨acc, !acc.limited && !acc.gap && !acc.stopped⟩

/-! ## Soundness -/

theorem Search.leaf_admitted (impl : Impl) (acc : Search) (o : Outcome) (out : String) (x : Obs)
    (h : x ∈ (acc.leaf impl o out).admitted) : x ∈ acc.admitted ∨ admits impl o out x := by
  simp only [Search.leaf, List.mem_append, List.mem_filter, decide_eq_true_eq] at h
  rcases h with h | ⟨_, h⟩
  · exact .inl h
  · exact .inr h

theorem Search.leaf_admitted_eq (impl : Impl) (acc : Search) (o : Outcome) (out : String) :
    (acc.leaf impl o out).pending = acc.pending.filter fun x => !decide (admits impl o out x) := rfl

/-- Every admitted observation is admitted by a reachable halted state. -/
theorem search_sound (impl : Impl) (file : Program) (labels : Labels) (start : State)
    (budget : Nat) (stack : List (Nat × State)) (acc : Search)
    (hstack : ∀ p ∈ stack, Reaches file labels start p.2)
    (hacc : ∀ x ∈ acc.admitted, ∃ s o, Reaches file labels start s ∧ s.control = .halt o ∧
      admits impl o s.memory.stdout x) :
    ∀ x ∈ (search impl file labels budget stack acc).admitted,
      ∃ s o, Reaches file labels start s ∧ s.control = .halt o ∧ admits impl o s.memory.stdout x := by
  induction budget generalizing stack acc with
  | zero =>
      intro x hx
      simp only [search] at hx
      split at hx
      · exact hacc x hx
      · exact hacc x hx
  | succ budget ih =>
      intro x hx
      match stack with
      | [] => exact hacc x (by simpa [search] using hx)
      | (depth, s) :: rest =>
          have hs : Reaches file labels start s := hstack (depth, s) (by simp)
          have hrest : ∀ p ∈ rest, Reaches file labels start p.2 :=
            fun p hp => hstack p (by simp [hp])
          simp only [search] at hx
          split at hx
          · exact hacc x hx
          · split at hx
            · rename_i o hcontrol
              refine ih rest _ hrest ?_ x hx
              intro y hy
              rcases Search.leaf_admitted impl acc o s.memory.stdout y hy with hy | hy
              · exact hacc y hy
              · exact ⟨s, o, hs, hcontrol, hy⟩
            · split at hx
              · exact ih rest { acc with limited := true } hrest hacc x hx
              · refine ih _ { acc with steps := acc.steps + 1 } ?_ hacc x hx
                intro p hp
                rcases List.mem_append.mp hp with hp | hp
                · obtain ⟨⟨a, t⟩, hmem, rfl⟩ := List.mem_map.mp hp
                  have htr := (successors_correct file labels s a t).mp hmem
                  exact Relation.ReflTransGen.tail hs ⟨a, htr⟩
                · exact hrest p hp

/-- **Soundness of the decision procedure**: an admitted observation is allowed. -/
theorem check_sound (impl : Impl) (file : Program) (enums : Map Sym IntegerType)
    (args : List String) (queries : List Obs) (bounds : Bounds) (x : Obs)
    (h : (check impl file enums args queries bounds).verdict x = .admitted) :
    allowed impl file enums args x := by
  have hmem : x ∈ (check impl file enums args queries bounds).search.admitted := by
    unfold Result.verdict at h
    split at h
    · rename_i hc
      exact List.contains_iff_mem.mp hc
    · split at h <;> cases h
  unfold allowed
  unfold check at hmem
  split at hmem
  · rename_i o _
    rcases Search.leaf_admitted impl _ o "" x hmem with hx | hx
    · simp at hx
    · simp [*]
  · rename_i start labels heq
    simp only [heq]
    exact search_sound impl file labels start bounds.budget _ _
      (by intro p hp; simp at hp; rw [hp]; exact .refl)
      (by intro y hy; simp at hy) x hmem

/-! ## Completeness -/

theorem search_limited (impl : Impl) (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Search), acc.limited = true →
      (search impl file labels budget stack acc).limited = true := by
  intro budget
  induction budget with
  | zero => intro stack acc h; simp only [search]; split <;> simp [h]
  | succ budget ih =>
      intro stack acc h
      match stack with
      | [] => simpa [search] using h
      | (depth, s) :: rest =>
          simp only [search]
          split
          · simpa using h
          · split
            · exact ih _ _ (by simpa [Search.leaf] using h)
            · split
              · exact ih _ _ rfl
              · exact ih _ _ h

theorem search_pending (impl : Impl) (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Search) (x : Obs),
      x ∈ (search impl file labels budget stack acc).pending → x ∈ acc.pending := by
  intro budget
  induction budget with
  | zero => intro stack acc x h; simp only [search] at h; split at h <;> exact h
  | succ budget ih =>
      intro stack acc x h
      match stack with
      | [] => simpa [search] using h
      | (depth, s) :: rest =>
          simp only [search] at h
          split at h
          · exact h
          · split at h
            · have := ih _ _ x h
              simp only [Search.leaf, List.mem_filter] at this
              exact this.1
            · split at h
              · exact ih _ { acc with limited := true } x h
              · exact ih _ { acc with steps := acc.steps + 1 } x h

theorem reaches_halt {file : Program} {labels : Labels} {s t : State} {o : Outcome}
    (hs : s.control = .halt o) (h : Reaches file labels s t) : t = s := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ _ =>
      obtain ⟨a, hstep⟩ := step
      cases hstep with
      | respond live _ => exact absurd hs (live o)

/-- One step of `search` on a nonempty stack. -/
theorem search_step (impl : Impl) (file : Program) (labels : Labels) (budget depth : Nat) (s : State)
    (rest : List (Nat × State)) (acc : Search) :
    let r := search impl file labels (budget + 1) ((depth, s) :: rest) acc
    (acc.pending.isEmpty = true ∧ r = { acc with stopped := true }) ∨
    (∃ o, s.control = .halt o ∧ r = search impl file labels budget rest (acc.leaf impl o s.memory.stdout)) ∨
    ((∀ o, s.control ≠ .halt o) ∧ depth = 0 ∧
      r = search impl file labels budget rest { acc with limited := true }) ∨
    ((∀ o, s.control ≠ .halt o) ∧ ∃ d, depth = d + 1 ∧
      r = search impl file labels budget ((successors file labels s).map (fun p => (d, p.2)) ++ rest)
        { acc with steps := acc.steps + 1 }) := by
  intro r
  simp only [r, search]
  split
  · exact .inl ⟨by assumption, rfl⟩
  · split
    · rename_i o hc
      exact .inr (.inl ⟨o, hc, rfl⟩)
    · rename_i hlive
      split
      · exact .inr (.inr (.inl ⟨hlive, rfl, rfl⟩))
      · rename_i d
        exact .inr (.inr (.inr ⟨hlive, d, rfl, rfl⟩))

/-- When the exploration ends without hitting a bound and without stopping early, an observation
still pending is admitted by no halted state reachable from any stack entry. -/
theorem search_complete (impl : Impl) (file : Program) (labels : Labels) :
    ∀ (budget : Nat) (stack : List (Nat × State)) (acc : Search) (x : Obs),
      (search impl file labels budget stack acc).limited = false →
      (search impl file labels budget stack acc).stopped = false →
      x ∈ (search impl file labels budget stack acc).pending →
      ∀ p ∈ stack, ∀ t o, Reaches file labels p.2 t → t.control = .halt o →
        ¬ admits impl o t.memory.stdout x := by
  intro budget
  induction budget with
  | zero =>
      intro stack acc x hl _ _ p hp
      simp only [search] at hl
      split at hl
      · rename_i hempty
        simp only [List.isEmpty_iff] at hempty
        simp [hempty] at hp
      · simp at hl
  | succ budget ih =>
      intro stack acc x hl hst hx p hp
      match stack with
      | [] => simp at hp
      | (depth, s) :: rest =>
          rcases search_step impl file labels budget depth s rest acc with
            ⟨_, hr⟩ | ⟨o, hc, hr⟩ | ⟨_, _, hr⟩ | ⟨hlive, d, _, hr⟩ <;> rw [hr] at hl hst hx
          · simp at hst
          · have hall := ih rest _ x hl hst hx
            rcases List.mem_cons.mp hp with rfl | hp
            · intro t o' hreach ht
              have := reaches_halt hc hreach
              subst this
              rw [hc] at ht
              cases ht
              have hpend := search_pending impl file labels budget rest _ x hx
              simp only [Search.leaf, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hpend
              exact hpend.2
            · exact hall p hp
          · rw [search_limited impl file labels budget rest _ rfl] at hl
            cases hl
          · have hall := ih _ _ x hl hst hx
            rcases List.mem_cons.mp hp with rfl | hp
            · intro t o hreach ht
              rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨u, ⟨a, hstep⟩, hrest⟩
              · subst heq
                exact absurd ht (hlive o)
              · have hmem : (a, u) ∈ successors file labels s :=
                  (successors_correct file labels s a u).mpr hstep
                exact hall (d, u) (List.mem_append_left _
                  (List.mem_map.mpr ⟨(a, u), hmem, rfl⟩)) t o hrest ht
            · exact hall p (List.mem_append_right _ hp)

/-- **Completeness of a rejection**: a rejected observation is not allowed. -/
theorem check_complete (impl : Impl) (file : Program) (enums : Map Sym IntegerType)
    (args : List String) (queries : List Obs) (bounds : Bounds) (x : Obs)
    (h : (check impl file enums args queries bounds).verdict x = .rejected) :
    ¬ allowed impl file enums args x := by
  unfold Result.verdict at h
  split at h
  · cases h
  · split at h
    · rename_i hdec
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hdec
      obtain ⟨hdecided, hpend⟩ := hdec
      unfold allowed
      unfold check at hdecided hpend
      rcases hinit : initial file enums (Core.Startup.execArguments args) with o | ⟨start, labels⟩
      · simp only [hinit] at hpend ⊢
        simp only [Search.leaf, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hpend
        exact hpend.2
      · simp only [hinit] at hdecided hpend ⊢
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdecided
        obtain ⟨⟨hl, _⟩, hs⟩ := hdecided
        rintro ⟨t, o, hreach, ht, hadm⟩
        exact search_complete impl file labels bounds.budget _ _ x hl hs hpend
          (bounds.depth, start) (by simp) t o hreach ht hadm
    · cases h

/-! ## Conventions

Other Silmaril semantics (csem's `Core.beh`) observe `abort()` as termination by signal 6
with the exact output. In `Spec.Obs` that is `Termination.abort` (SIGABRT) and the stdout prefix that
`admits` allows contains the exact output, so their observation of an abort is admitted here. -/

/-- The exact-output abort observation (signal 6 with all of the output) is admitted. -/
theorem admits_abort_exact (impl : Impl) (out : String) :
    admits impl .aborted out ⟨.abort, bytes out⟩ :=
  ⟨rfl, List.prefix_refl _, fun _ => rfl⟩

end Silmaril.Cerberus.Spec
