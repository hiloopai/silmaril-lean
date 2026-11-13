module

public import Silmaril.Compiler.Mir.FuncPass.Defs
/-! # Memory-aware function-local Mir simulations

This sibling of `FuncPass` adds the shared memory to the point relation. Memory
facts survive straight-line operations, but a suspended caller's return obligation
must hold for every returned memory. Function shape, placement and linking lemmas
are reused unchanged. The simulation is forward, including stuttering, and Mir
semantics determinism yields the frozen backward `Contract.mirPass`.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.MemoryFuncPass

open Silmaril.Machine Relation
open Silmaril.Compile.Contract
open Silmaril.Compile.Contract.MirSem
open Silmaril.Compile.Mir.FuncPass (Shape Iface mapFuncs need_eq valid_iff funcDefs_eq
  enter_eq initMem_eq symValue_eq funcOf_eq target_eq termOut TermOut step_term writeAll_some_of)

/-- A point relation: `PR f l i fr i' fr' m` relates the point `(l, i)` of `f` with frame
`fr` to the point `(l, i')` of the transformed function with frame `fr'`. -/
abbrev PointRel := Func → Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Lir.Memory → Prop

/-- After a call at `i` (input) and `i'` (output): the frames that receive the same results
are related at the next points for every returned memory. -/
def RetSim (Q : Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Lir.Memory → Prop) (i : Nat) (fr : Lir.Frame Nat)
    (i' : Nat) (fr' : Lir.Frame Nat) (res : List Nat) : Prop :=
  ∀ vals fr₁ fr₁' m, fr.writeAll (res.map .reg) vals = some fr₁ →
    fr'.writeAll (res.map .reg) vals = some fr₁' → Q (i + 1) fr₁ (i' + 1) fr₁' m

/-- One input instruction `x` at `i` (frame `fr`, memory `m`) and the output's instruction
`y` at `i'` (frame `fr'`, same memory): an operation is deleted (`y` unused, memory
unchanged) or matched by an operation, any other instruction by one of the same kind. -/
def InstrSim (Q : Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Lir.Memory → Prop) (i : Nat) (fr : Lir.Frame Nat)
    (i' : Nat) (fr' : Lir.Frame Nat) (m : Lir.Memory) : Instr → Option Instr → Prop
  | .op o, y => ∀ fr₁ m₁, o.exec fr m = some (fr₁, m₁) →
      (m₁ = m ∧ Q (i + 1) fr₁ i' fr' m₁) ∨
      ∃ o', y = some (.op o') ∧ ∃ fr₁', o'.exec fr' m = some (fr₁', m₁) ∧ Q (i + 1) fr₁ (i' + 1) fr₁' m₁
  | .fop op d a b, y => ∀ fr₁, Lir.FOp.exec op d a b fr = some fr₁ →
      ∃ op' d' a' b', y = some (.fop op' d' a' b') ∧
        ∃ fr₁', Lir.FOp.exec op' d' a' b' fr' = some fr₁' ∧ Q (i + 1) fr₁ (i' + 1) fr₁' m
  | .addr d sym off, y => y = some (.addr d sym off) ∧ ∀ w, Q (i + 1) (fr.set d w) (i' + 1) (fr'.set d w) m
  | .call c args res, y => ∀ vals, fr.readAll (args.map .reg) = some vals →
      ∃ args', y = some (.call c args' res) ∧ fr'.readAll (args'.map .reg) = some vals ∧
        RetSim Q i fr i' fr' res
  | .callIndirect t args res, y => ∀ v vals, fr.get t = some v → fr.readAll (args.map .reg) = some vals →
      ∃ t' args', y = some (.callIndirect t' args' res) ∧ fr'.get t' = some v ∧
        fr'.readAll (args'.map .reg) = some vals ∧ RetSim Q i fr i' fr' res

/-- A terminator and its output: the same outcome, and related entry points after a jump
(`Q l fr fr' m` relates the starts of block `l`). -/
def TermSim (Q : Nat → Lir.Frame Nat → Lir.Frame Nat → Lir.Memory → Prop) (fr fr' : Lir.Frame Nat)
    (t t' : Lir.Term Nat) (m : Lir.Memory) : Prop :=
  termOut fr t ≠ .stuck → termOut fr' t' = termOut fr t ∧ ∀ l, termOut fr t = .goto l → Q l fr fr' m

/-- The obligations of a function `f` and its output `f'`, with the point relation
`Q l i fr i' fr' m`. -/
structure FSim (f f' : Func) (Q : Nat → Nat → Lir.Frame Nat → Nat → Lir.Frame Nat → Lir.Memory → Prop) : Prop where
  /-- Function entry: a fresh frame is related to itself. -/
  entry : ∀ fr m, Q 0 0 fr 0 fr m
  /-- At an input instruction. -/
  instr : ∀ l b b' i fr i' fr' m x, f.blocks[l]? = some b → f'.blocks[l]? = some b' →
    Q l i fr i' fr' m → b.instrs[i]? = some x →
    InstrSim (Q l) i fr i' fr' m x b'.instrs[i']?
  /-- At an input terminator. -/
  term : ∀ l b b' i fr i' fr' m, f.blocks[l]? = some b → f'.blocks[l]? = some b' →
    Q l i fr i' fr' m → i = b.instrs.size →
    i' = b'.instrs.size ∧ TermSim (fun l fr fr' m => Q l 0 fr 0 fr' m) fr fr' b.term b'.term m

/-- The obligations of a function-local pass `g` with point relation `PR`. -/
def Sim (g : Func → Func) (PR : PointRel) : Prop := ∀ f, FSim f (g f) (PR f)

/-! ## The simulation -/

section Simulation

variable {g : Func → Func} {PR : PointRel}

/-- A suspended input caller and its output. -/
def ActRel (g : Func → Func) (PR : PointRel) (a a' : Act) : Prop :=
  a'.func = g a.func ∧ a'.label = a.label ∧ a'.results = a.results ∧
    RetSim (PR a.func a.label) a.index a.frame a'.index a'.frame a.results

/-- An input state and its output. -/
def Rel (g : Func → Func) (PR : PointRel) (s t : State) : Prop :=
  t.func = g s.func ∧ t.label = s.label ∧ t.mem = s.mem ∧
    PR s.func s.label s.index s.frame t.index t.frame s.mem ∧ List.Forall₂ (ActRel g PR) s.stack t.stack

/-- The instructions left in the current block. -/
def measure (s : State) : Nat :=
  match s.func.blocks[s.label]? with
  | some b => b.instrs.size - s.index
  | none => 0

/-- What the output does from `t` when the input's step from `s` gives `r`. -/
inductive Match (us us' : Array Mir.Unit) (P : Placement) (g : Func → Func) (PR : PointRel)
    (s t : State) : Result → Prop
  | run {s₁ t₁ : State} : step us' P t = .running t₁ → Rel g PR s₁ t₁ → Match us us' P g PR s t (.running s₁)
  | stutter {s₁ : State} : Rel g PR s₁ t → measure s₁ < measure s → Match us us' P g PR s t (.running s₁)
  | returned {vs m} : step us' P t = .returned vs m → Match us us' P g PR s t (.returned vs m)
  | trapped {m} : step us' P t = .trapped m → Match us us' P g PR s t (.trapped m)

variable (hg : Iface g) (hs : Sim g PR) (us : Array Mir.Unit) (P : Placement)
include hg hs

/-- The one-step simulation, and the equal final results. -/
theorem step_match {s t : State} (hr : Rel g PR s t) (hstuck : step us P s ≠ .stuck) :
    Match us (mapFuncs g us) P g PR s t (step us P s) := by
  obtain ⟨hf, hl, hm, hp, hst⟩ := hr
  obtain ⟨func, label, index, frame, stack, mem⟩ := s
  obtain ⟨tfunc, tlabel, tindex, tframe, tstack, tmem⟩ := t
  simp only at hf hl hm hp hst
  subst hf; subst tlabel; subst tmem
  cases hb : func.blocks[label]? with
  | none => exact absurd (by simp [step, hb]) hstuck
  | some b =>
  obtain ⟨b', hb'⟩ : ∃ b', (g func).blocks[label]? = some b' := by
    have hlt : label < func.blocks.size := (Array.getElem?_eq_some_iff.mp hb).1
    exact ⟨_, Array.getElem?_eq_getElem (by rw [hg.size]; exact hlt)⟩
  cases hx : b.instrs[index]? with
  | some x =>
    have hlt : index < b.instrs.size := (Array.getElem?_eq_some_iff.mp hx).1
    have hsim := (hs func).instr label b b' index frame tindex tframe mem x hb hb' hp hx
    cases x with
    | op o =>
      cases he : o.exec frame mem with
      | none => exact absurd (by simp [step, hb, hx, he]) hstuck
      | some p =>
        obtain ⟨fr₁, m₁⟩ := p
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, fr₁, stack, m₁⟩ := by simp [step, hb, hx, he]
        rw [hstep]
        rcases hsim fr₁ m₁ he with ⟨rfl, hq⟩ | ⟨o', hy, fr₁', he', hq⟩
        · refine .stutter ⟨rfl, rfl, rfl, hq, hst⟩ ?_
          simp only [measure, hb]; omega
        · refine .run (t₁ := ⟨g func, label, tindex + 1, fr₁', tstack, m₁⟩) ?_ ⟨rfl, rfl, rfl, hq, hst⟩
          simp [step, hb', hy, he']
    | fop op d a c =>
      cases he : Lir.FOp.exec op d a c frame with
      | none => exact absurd (by simp [step, hb, hx, he]) hstuck
      | some fr₁ =>
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, fr₁, stack, mem⟩ := by simp [step, hb, hx, he]
        rw [hstep]
        obtain ⟨op', d', a', c', hy, fr₁', he', hq⟩ := hsim fr₁ he
        refine .run (t₁ := ⟨g func, label, tindex + 1, fr₁', tstack, mem⟩) ?_ ⟨rfl, rfl, rfl, hq, hst⟩
        simp [step, hb', hy, he']
    | addr d sym off =>
      obtain ⟨hy, hq⟩ := hsim
      cases hv : symValue us P sym with
      | none => exact absurd (by simp [step, hb, hx, hv]) hstuck
      | some v =>
        have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
            .running ⟨func, label, index + 1, frame.set d (BitVec.ofNat 64 (v + off)), stack, mem⟩ := by
          simp [step, hb, hx, hv]
        rw [hstep]
        refine .run (t₁ := ⟨g func, label, tindex + 1, tframe.set d (BitVec.ofNat 64 (v + off)), tstack, mem⟩)
          ?_ ⟨rfl, rfl, rfl, hq _, hst⟩
        simp [step, hb', hy, symValue_eq hg, hv]
    | call c args res =>
      cases hfn : funcOf us c with
      | none => exact absurd (by simp [step, hb, hx, hfn]) hstuck
      | some fn =>
      cases hv : frame.readAll (args.map .reg) with
      | none => exact absurd (by simp [step, hb, hx, hfn, hv]) hstuck
      | some vals =>
      cases hen : enter fn vals with
      | none => exact absurd (by simp [step, hb, hx, hfn, hv, call, hen]) hstuck
      | some fr₀ =>
      have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
          .running ⟨fn, 0, 0, fr₀, ⟨func, label, index, frame, res⟩ :: stack, mem⟩ := by
        simp [step, hb, hx, hfn, hv, call, hen]
      rw [hstep]
      obtain ⟨args', hy, hv', hret⟩ := hsim vals hv
      refine .run (t₁ := ⟨g fn, 0, 0, fr₀, ⟨g func, label, tindex, tframe, res⟩ :: tstack, mem⟩) ?_
        ⟨rfl, rfl, rfl, (hs fn).entry fr₀ mem, .cons ⟨rfl, rfl, rfl, hret⟩ hst⟩
      simp [step, hb', hy, funcOf_eq hg, hfn, hv', call, enter_eq hg, hen]
    | callIndirect tr args res =>
      cases htr : frame.get tr with
      | none => exact absurd (by simp [step, hb, hx, htr]) hstuck
      | some v =>
      cases hv : frame.readAll (args.map .reg) with
      | none => exact absurd (by simp [step, hb, hx, htr, hv]) hstuck
      | some vals =>
      cases hfn : target us P v args.length res.length with
      | none => exact absurd (by simp [step, hb, hx, htr, hv, hfn]) hstuck
      | some fn =>
      cases hen : enter fn vals with
      | none => exact absurd (by simp [step, hb, hx, htr, hv, hfn, call, hen]) hstuck
      | some fr₀ =>
      have hstep : step us P ⟨func, label, index, frame, stack, mem⟩ =
          .running ⟨fn, 0, 0, fr₀, ⟨func, label, index, frame, res⟩ :: stack, mem⟩ := by
        simp [step, hb, hx, htr, hv, hfn, call, hen]
      rw [hstep]
      obtain ⟨tr', args', hy, htr', hv', hret⟩ := hsim v vals htr hv
      have hlen : args'.length = args.length := by
        have h1 := LinkCorrect.readAll_length hv
        have h2 := LinkCorrect.readAll_length hv'
        simp only [List.length_map] at h1 h2
        omega
      refine .run (t₁ := ⟨g fn, 0, 0, fr₀, ⟨g func, label, tindex, tframe, res⟩ :: tstack, mem⟩) ?_
        ⟨rfl, rfl, rfl, (hs fn).entry fr₀ mem, .cons ⟨rfl, rfl, rfl, hret⟩ hst⟩
      simp [step, hb', hy, htr', hv', hlen, target_eq hg, hfn, call, enter_eq hg, hen]
  | none =>
    by_cases hi : index = b.instrs.size
    swap
    · exact absurd (by simp [step, hb, hx, hi]) hstuck
    obtain ⟨hi', hterm⟩ := (hs func).term label b b' index frame tindex tframe mem hb hb' hp hi
    have hstep' := step_term (mapFuncs g us) P ⟨g func, label, tindex, tframe, tstack, mem⟩ b' hb' hi'
    rw [step_term us P ⟨func, label, index, frame, stack, mem⟩ b hb hi] at hstuck ⊢
    cases hout : termOut frame b.term with
    | stuck => simp [hout] at hstuck
    | goto l =>
      obtain ⟨hout', hq⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      exact .run hstep' ⟨rfl, rfl, rfl, hq l hout, hst⟩
    | trap =>
      obtain ⟨hout', -⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      exact .trapped hstep'
    | ret vals =>
      obtain ⟨hout', -⟩ := hterm (by simp [hout])
      rw [hout', hout] at hstep'
      rw [hout] at hstuck
      cases hst with
      | nil => exact .returned hstep'
      | @cons a a' rest rest' ha hrest =>
        obtain ⟨haf, hal, har, hret⟩ := ha
        simp only at hstep' hstuck ⊢
        cases hw : a.frame.writeAll (a.results.map .reg) vals with
        | none => simp [hw] at hstuck
        | some fr₁ =>
        obtain ⟨fr₁', hw'⟩ := writeAll_some_of (fr₂ := a'.frame) hw
        rw [har, hw'] at hstep'
        exact .run hstep' ⟨haf, hal, rfl, hret vals fr₁ fr₁' mem hw hw', hrest⟩

/-- `Rel` is a forward simulation of `MirSem.Step`. -/
def forwardSim : ForwardSim (Step us P) (Step (mapFuncs g us) P) (Rel g PR) where
  measure := measure
  step := by
    intro s s₁ t hstep hr
    have hm := step_match hg hs us P hr (by rw [hstep]; simp)
    rw [hstep] at hm
    cases hm with
    | run ht hr₁ => exact ⟨_, .inl (.single ht), hr₁⟩
    | stutter hr₁ hlt => exact ⟨t, .inr ⟨rfl, hlt⟩, hr₁⟩

/-- The output of a related state has the input's behaviour, unless the input is stuck. -/
theorem behaves {s t : State} (hr : Rel g PR s t) {b : Lir.Behavior} (hb : Behaves us P s b)
    (hns : b ≠ .stuck) : Behaves (mapFuncs g us) P t b := by
  have sim := forwardSim hg hs us P
  cases b with
  | stuck => exact absurd rfl hns
  | diverges => exact sim.diverges hb hr
  | returned vs m =>
    obtain ⟨s₁, hs₁, hf⟩ := hb
    obtain ⟨t₁, ht₁, hr₁⟩ := sim.steps hs₁ hr
    have hm := step_match hg hs us P hr₁ (by rw [hf]; simp)
    rw [hf] at hm
    cases hm with
    | returned h => exact ⟨t₁, ht₁, h⟩
  | trapped m =>
    obtain ⟨s₁, hs₁, hf⟩ := hb
    obtain ⟨t₁, ht₁, hr₁⟩ := sim.steps hs₁ hr
    have hm := step_match hg hs us P hr₁ (by rw [hf]; simp)
    rw [hf] at hm
    cases hm with
    | trapped h => exact ⟨t₁, ht₁, h⟩

end Simulation

/-- **A function-local pass with a forward simulation refines its input.** -/
theorem mirPass {g : Func → Func} {PR : PointRel} (hg : Shape g) (hs : Sim g PR) :
    Contract.mirPass (mapFuncs g) := by
  intro us
  refine ⟨fun base => (need_eq us base).le, fun memSize _ P hP => ?_⟩
  refine ⟨P, (valid_iff hg us memSize P).mp hP, fun s hs₀ => ?_⟩
  have hstart : start (mapFuncs g us) P memSize =
      some { s with func := g s.func, stack := [] } := by
    simp only [start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs₀
    obtain ⟨fn, hfn, fr, hfr, rfl⟩ := hs₀
    simp [start, funcDefs_eq hg.iface, List.head?_map, hfn, enter_eq hg.iface, hfr,
      initMem_eq hg.iface]
  have hr : Rel g PR s { s with func := g s.func, stack := [] } := by
    simp only [start, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs₀
    obtain ⟨fn, -, fr, -, rfl⟩ := hs₀
    exact ⟨rfl, rfl, rfl, (hs fn).entry fr _, .nil⟩
  refine ⟨⟨_, hstart⟩, fun t ht b hb => ?_⟩
  rw [hstart] at ht
  obtain rfl := Option.some.inj ht
  obtain ⟨b', hb'⟩ := Behaves.exists us P s
  refine ⟨b', hb', ?_⟩
  by_cases hns : b' = .stuck
  · exact .inl hns
  · exact .inr (Behaves.unique (behaves hg.iface hs us P hr hb' hns) hb)

end Silmaril.Compile.Mir.MemoryFuncPass
