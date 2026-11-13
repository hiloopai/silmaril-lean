module

public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! # Jump threading

`JumpThread.run` retargets every jump and branch of a function past the blocks that only
jump: a block with no instruction whose terminator is `jump l'` is skipped, and the chain is
followed as far as the function has blocks (`dest`), so an empty cycle stops somewhere on
the cycle and stays one. Nothing else changes: the instructions, the number of blocks (the
skipped ones stay, possibly unreachable), the data. After constant propagation turns
branches into jumps, such blocks are common.

Correctness (`JumpThread.correct : Contract.mirPass run`, through `FuncPass.Shape`):

* the instructions are unchanged, so the pass keeps the interface of every function and
  its symbol references (`FuncPass.Shape`): the names in force, `MirSem.taken`, the valid
  placements, the data and the initial memory are the input's;
* the output state `lift s` is the input state `s` with every function threaded (the
  current one and each suspended caller's). From `lift s`, the output steps to `lift s₂`
  where the input steps from `s` to `s₁` and then, through the skipped blocks, to `s₂`
  (`step_match`; the skipped blocks are empty, so the input only jumps through them,
  `thread_steps`). Every other result (return, trap, stuck) is the input's. This is a
  lock-step simulation **from the output to the input** (`lockstep`), so no measure is
  needed: every behaviour of the output, divergence and stuck included, is one of the
  input (`behaves`), which is the backward clause of the contract itself. -/

@[expose] public section

namespace Silmaril.Compile.Mir.JumpThread

open Silmaril.Machine Relation
open Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem
open Silmaril.Compile.Mir.FuncPass

/-! ## The pass -/

/-- The target of block `l` when it has no instruction and jumps. -/
def next (f : Func) (l : Nat) : Option Nat :=
  match f.blocks[l]? with
  | some b =>
    if b.instrs.size = 0 then
      match b.term with
      | .jump l' => some l'
      | _ => none
    else none
  | none => none

/-- Follow the blocks that only jump from `l`, `k` of them at most. -/
def thread (f : Func) : Nat → Nat → Nat
  | 0, l => l
  | k + 1, l =>
    match next f l with
    | some l' => thread f k l'
    | none => l

/-- Where the output goes instead of `l`: past the blocks that only jump, as many as `f`
has blocks (enough for every chain without a cycle). -/
def dest (f : Func) (l : Nat) : Nat := thread f f.blocks.size l

/-- A terminator with its targets threaded. -/
def threadTerm (f : Func) : Lir.Term Nat → Lir.Term Nat
  | .jump l => .jump (dest f l)
  | .branch c l₁ l₂ => .branch c (dest f l₁) (dest f l₂)
  | t => t

/-- Thread the jumps and branches of `f`. -/
def jtFunc (f : Func) : Func :=
  { f with blocks := f.blocks.map fun b => { b with term := threadTerm f b.term } }

/-- The pass on units. -/
def run : Array Mir.Unit → Array Mir.Unit := mapFuncs jtFunc

/-! ## Correctness -/

theorem shape : Shape jtFunc where
  name _ := rfl
  params _ := rfl
  results _ := rfl
  weak _ := rfl
  size _ := by simp [jtFunc]
  refs _ := by simp [funcRefs, jtFunc, List.flatMap_map]

theorem blocks_get (f : Func) (l : Nat) :
    (jtFunc f).blocks[l]? = f.blocks[l]?.map fun b => { b with term := threadTerm f b.term } := by
  simp [jtFunc]

/-- The input runs through the blocks that only jump. -/
theorem thread_steps (us : Array Mir.Unit) (P : Placement) (f : Func) (fr : Lir.Frame Nat)
    (st : List Act) (m : Lir.Memory) :
    ∀ k l, ReflTransGen (Step us P) ⟨f, l, 0, fr, st, m⟩ ⟨f, thread f k l, 0, fr, st, m⟩
  | 0, _ => .refl
  | k + 1, l => by
    simp only [thread]
    cases hn : next f l with
    | none => exact .refl
    | some l' =>
      refine .head ?_ (thread_steps us P f fr st m k l')
      simp only [next] at hn
      cases hb : f.blocks[l]? with
      | none => simp [hb] at hn
      | some b =>
        simp only [hb] at hn
        split at hn
        · rename_i h0
          cases ht : b.term <;> simp only [ht, reduceCtorEq, Option.some.injEq] at hn
          subst hn
          simp [Step, step, hb, h0, ht]
        · cases hn

/-- A suspended caller in the output. -/
def liftAct (a : Act) : Act := { a with func := jtFunc a.func }

/-- The output state of an input state: every function threaded. -/
def lift (s : State) : State := { s with func := jtFunc s.func, stack := s.stack.map liftAct }

/-- What the output's step from `lift s` gives when the input's from `s` gives `r`. -/
inductive Match (us : Array Mir.Unit) (P : Placement) : Result → Result → Prop
  | running {s₁ s₂ : State} : ReflTransGen (Step us P) s₁ s₂ →
      Match us P (.running s₁) (.running (lift s₂))
  | returned {vs m} : Match us P (.returned vs m) (.returned vs m)
  | trapped {m} : Match us P (.trapped m) (.trapped m)
  | stuck : Match us P .stuck .stuck

theorem match_call (us : Array Mir.Unit) (P : Placement) (s : State) (fn : Func)
    (vals : List Lir.Word) (res : List Nat) :
    Match us P (call s fn vals res) (call (lift s) (jtFunc fn) vals res) := by
  simp only [call, enter_eq shape.iface]
  cases enter fn vals with
  | none => exact .stuck
  | some fr => exact .running (s₂ := ⟨fn, 0, 0, fr, ⟨s.func, s.label, s.index, s.frame, res⟩ :: s.stack, s.mem⟩) .refl

/-- **One step**: the output steps from `lift s` as the input from `s`, past the blocks
that only jump. -/
theorem step_match (us : Array Mir.Unit) (P : Placement) (s : State) :
    Match us P (step us P s) (step (run us) P (lift s)) := by
  obtain ⟨f, l, i, fr, st, m⟩ := s
  have hb' := blocks_get f l
  cases hb : f.blocks[l]? with
  | none =>
    simp only [hb, Option.map_none] at hb'
    simp only [step, lift, hb, hb']
    exact .stuck
  | some b =>
  simp only [hb, Option.map_some] at hb'
  cases hx : b.instrs[i]? with
  | some x =>
    cases x with
    | op o =>
      cases he : o.exec fr m with
      | none =>
        simp only [step, lift, hb, hb', hx, he]
        exact .stuck
      | some p =>
        simp only [step, lift, hb, hb', hx, he]
        exact .running (s₂ := ⟨f, l, i + 1, p.1, st, p.2⟩) .refl
    | fop op d a c =>
      cases he : Lir.FOp.exec op d a c fr with
      | none =>
        simp only [step, lift, hb, hb', hx, he]
        exact .stuck
      | some fr₁ =>
        simp only [step, lift, hb, hb', hx, he]
        exact .running (s₂ := ⟨f, l, i + 1, fr₁, st, m⟩) .refl
    | addr d sym off =>
      cases hv : symValue us P sym with
      | none =>
        simp only [step, lift, hb, hb', hx, run, symValue_eq shape.iface, hv]
        exact .stuck
      | some v =>
        simp only [step, lift, hb, hb', hx, run, symValue_eq shape.iface, hv]
        exact .running (s₂ := ⟨f, l, i + 1, fr.set d (BitVec.ofNat 64 (v + off)), st, m⟩) .refl
    | call c args res =>
      cases hfn : funcOf us c with
      | none =>
        simp only [step, lift, hb, hb', hx, run, funcOf_eq shape.iface, hfn, Option.map_none]
        exact .stuck
      | some fn =>
        cases hv : fr.readAll (args.map .reg) with
        | none =>
          simp only [step, lift, hb, hb', hx, run, funcOf_eq shape.iface, hfn, Option.map_some, hv]
          exact .stuck
        | some vals =>
          simp only [step, lift, hb, hb', hx, run, funcOf_eq shape.iface, hfn, Option.map_some, hv]
          exact match_call us P ⟨f, l, i, fr, st, m⟩ fn vals res
    | callIndirect t args res =>
      cases htv : fr.get t with
      | none =>
        simp only [step, lift, hb, hb', hx, htv]
        exact .stuck
      | some v =>
        cases hv : fr.readAll (args.map .reg) with
        | none =>
          simp only [step, lift, hb, hb', hx, htv, hv]
          exact .stuck
        | some vals =>
          cases hfn : target us P v args.length res.length with
          | none =>
            simp only [step, lift, hb, hb', hx, htv, hv, run, target_eq shape.iface, hfn,
              Option.map_none]
            exact .stuck
          | some fn =>
            simp only [step, lift, hb, hb', hx, htv, hv, run, target_eq shape.iface, hfn,
              Option.map_some]
            exact match_call us P ⟨f, l, i, fr, st, m⟩ fn vals res
  | none =>
    by_cases hi : i = b.instrs.size
    swap
    · simp only [step, lift, hb, hb', hx, hi, ne_eq, not_false_eq_true, ↓reduceIte]
      exact .stuck
    subst hi
    cases ht : b.term with
    | jump l' =>
      simp only [step, lift, hb, hb', hx, ht, threadTerm, ne_eq, not_true_eq_false, ↓reduceIte]
      exact .running (thread_steps us P f fr st m _ l')
    | branch c l₁ l₂ =>
      cases hc : fr.get c with
      | none =>
        simp only [step, lift, hb, hb', hx, ht, threadTerm, hc, ne_eq, not_true_eq_false,
          ↓reduceIte]
        exact .stuck
      | some x =>
        by_cases hx0 : x = 0
        · simp only [step, lift, hb, hb', hx, ht, threadTerm, hc, hx0, ne_eq, not_true_eq_false,
            ↓reduceIte]
          exact .running (thread_steps us P f fr st m _ l₂)
        · simp only [step, lift, hb, hb', hx, ht, threadTerm, hc, hx0, ne_eq, not_true_eq_false,
            ↓reduceIte]
          exact .running (thread_steps us P f fr st m _ l₁)
    | ret locs =>
      cases hv : fr.readAll locs with
      | none =>
        simp only [step, lift, hb, hb', hx, ht, threadTerm, hv, ne_eq, not_true_eq_false,
          ↓reduceIte]
        exact .stuck
      | some vals =>
        cases st with
        | nil =>
          simp only [step, lift, hb, hb', hx, ht, threadTerm, hv, ne_eq, not_true_eq_false,
            ↓reduceIte, List.map_nil]
          exact .returned
        | cons a rest =>
          cases hw : a.frame.writeAll (a.results.map .reg) vals with
          | none =>
            simp only [step, lift, hb, hb', hx, ht, threadTerm, hv, ne_eq, not_true_eq_false,
              ↓reduceIte, List.map_cons, liftAct, hw]
            exact .stuck
          | some fr₁ =>
            simp only [step, lift, hb, hb', hx, ht, threadTerm, hv, ne_eq, not_true_eq_false,
              ↓reduceIte, List.map_cons, liftAct, hw]
            exact .running (s₂ := ⟨a.func, a.label, a.index + 1, fr₁, rest, m⟩) .refl
    | trap =>
      simp only [step, lift, hb, hb', hx, ht, threadTerm, ne_eq, not_true_eq_false, ↓reduceIte]
      exact .trapped

/-- The output, run from `lift s`, is matched by the input from `s`, step for nonempty
run. -/
theorem lockstep (us : Array Mir.Unit) (P : Placement) :
    LockstepSim (Step (run us) P) (Step us P) fun t s => t = lift s where
  step := by
    rintro t t₁ s ht rfl
    have ht : step (run us) P (lift s) = .running t₁ := ht
    have hm := step_match us P s
    rw [ht] at hm
    generalize hr : step us P s = r at hm
    cases hm with
    | running h => exact ⟨_, TransGen.head' hr h, rfl⟩

/-- Every output run from `lift s` ends in a lift of an input state reached from `s`. -/
theorem reach_lift {us : Array Mir.Unit} {P : Placement} {s : State} {t : State}
    (h : ReflTransGen (Step (run us) P) (lift s) t) :
    ∃ s', ReflTransGen (Step us P) s s' ∧ t = lift s' :=
  (lockstep us P).steps h rfl

/-- **Every behaviour of the output from `lift s` is one of the input from `s`.** -/
theorem behaves {us : Array Mir.Unit} {P : Placement} {s : State} {b : Lir.Behavior}
    (h : Behaves (run us) P (lift s) b) : Behaves us P s b := by
  cases b with
  | diverges => exact (lockstep us P).diverges h rfl
  | returned vs m =>
    obtain ⟨t, ht, hf⟩ := h
    obtain ⟨s', hs', rfl⟩ := reach_lift ht
    have hm := step_match us P s'
    rw [hf] at hm
    generalize hr : step us P s' = r at hm
    cases hm
    exact ⟨s', hs', hr⟩
  | trapped m =>
    obtain ⟨t, ht, hf⟩ := h
    obtain ⟨s', hs', rfl⟩ := reach_lift ht
    have hm := step_match us P s'
    rw [hf] at hm
    generalize hr : step us P s' = r at hm
    cases hm
    exact ⟨s', hs', hr⟩
  | stuck =>
    obtain ⟨t, ht, hf⟩ := h
    obtain ⟨s', hs', rfl⟩ := reach_lift ht
    have hm := step_match us P s'
    rw [hf] at hm
    generalize hr : step us P s' = r at hm
    cases hm
    exact ⟨s', hs', hr⟩

/-- **Jump threading refines the input** (`Contract.mirPass`). -/
theorem correct : Contract.mirPass run := by
  intro us
  refine ⟨fun base => (need_eq us base).le, fun memSize _ P hP => ?_⟩
  refine ⟨P, (valid_iff shape us memSize P).mp hP, fun s hs₀ => ?_⟩
  have hstart : start (run us) P memSize = some (lift s) := by
    simp only [start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs₀
    obtain ⟨fn, hfn, fr, hfr, rfl⟩ := hs₀
    simp [start, run, funcDefs_eq shape.iface, List.head?_map, hfn, enter_eq shape.iface, hfr,
      initMem_eq shape.iface, lift]
  refine ⟨⟨_, hstart⟩, fun t ht b hb => ?_⟩
  rw [hstart] at ht
  obtain rfl := Option.some.inj ht
  exact ⟨b, behaves hb, .inr rfl⟩

end Silmaril.Compile.Mir.JumpThread
