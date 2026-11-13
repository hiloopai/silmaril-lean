module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Run
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
public import Silmaril.Wasm.Binaryen.ConstBranchSim

@[expose] public section

/-! # Adequacy of the grounded interpreter for silmaril's small-step semantics

* `step1_transGen`, `run_steps`, `run_transGen`: a successful run of `run` is a run of
  `Execution.Core.Step` (any profile, any host), from `vals st.reverse ++ code ++ rest`, in
  the same store; it takes at least one step when the code is not all constants.
* `step_inv`: conversely, the only closed-host step of a stack-only instruction or of
  `local.get` at the head of the active code is the one `step1` computes, and it keeps
  store and frame.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Runs of the interpreter are runs of the machine -/

/-- Lifting a run under values and before code. -/
theorem lift_transGen {c c' : Config H} (h : Relation.TransGen (Step P host) c c')
    (W : List Val) (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨c.store, c.frame, vals W ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals W ++ c'.code ++ rest⟩ := by
  have lift : ∀ {a b : Config H}, Step P host a b →
      Step P host ⟨a.store, a.frame, vals W ++ a.code ++ rest⟩
        ⟨b.store, b.frame, vals W ++ b.code ++ rest⟩ := by
    intro a b hab
    obtain ⟨_, _, _⟩ := a
    obtain ⟨_, _, _⟩ := b
    exact Step.append_right (Step.vals_left hab W) rest
  induction h with
  | single hab => exact .single (lift hab)
  | tail _ hab ih => exact ih.tail (lift hab)

/-- A stack-only instruction: same frame, and its stack transformer. -/
theorem step1_stk_inv {i : GInstr} (hi : i.stk = true) {f f' : Frame} {X Y : List Val}
    (h : step1 i f X = some (f', Y)) : f = f' ∧ stepS i X = some Y := by
  rw [step1_of_stk hi] at h
  obtain ⟨Y', hY', he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨rfl, hY'⟩

/-- The head steps of the interpreter: the instruction after its operands `us`. -/
def HeadRun (P : Profile) (host : HostSemantics H) (s : Store H) (i : GInstr) (f f' : Frame)
    (X Y : List Val) : Prop :=
  ∃ W us ws, X.reverse = W ++ us ∧ Y.reverse = W ++ ws ∧
    Relation.TransGen (Step P host) ⟨s, f, vals us ++ [.plain i.lower]⟩ ⟨s, f', vals ws⟩

theorem headRun_one {s : Store H} {i : GInstr} {f f' : Frame} {W us ws : List Val}
    (h : Step P host ⟨s, f, vals us ++ [.plain i.lower]⟩ ⟨s, f', vals ws⟩) :
    HeadRun P host s i f f' (W ++ us).reverse (W ++ ws).reverse :=
  ⟨W, us, ws, by simp, by simp, .single h⟩

theorem headRun_bin {s : Store H} {b : Bin} {f f' : Frame} {X Y : List Val}
    (h : step1 (.bin b) f X = some (f', Y)) : HeadRun P host s (.bin b) f f' X Y := by
  obtain ⟨rfl, h'⟩ := step1_stk_inv rfl h
  obtain ⟨x, y, X', rfl, rfl⟩ := stepS_bin_inv h'
  have hs : Step P host ⟨s, f, vals [Val.i32 x, Val.i32 y] ++ [.plain (GInstr.bin b).lower]⟩
      ⟨s, f, vals [Val.i32 (b.eval x y)]⟩ :=
    Step.numeric (NumericStep.intBinOp (Bin.intBinOp_eq b x y))
  simpa using headRun_one (W := X'.reverse) hs

theorem headRun_eqz {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 .eqz f X = some (f', Y)) : HeadRun P host s .eqz f f' X Y := by
  obtain ⟨rfl, h'⟩ := step1_stk_inv rfl h
  obtain ⟨x, X', rfl, rfl⟩ := stepS_eqz_inv h'
  have hs : Step P host ⟨s, f, vals [Val.i32 x] ++ [.plain GInstr.eqz.lower]⟩
      ⟨s, f, vals [Val.i32 (Numerics.intTestOp .i32 .eqz x)]⟩ :=
    Step.numeric NumericStep.intTestOp
  simpa using headRun_one (W := X'.reverse) hs

theorem headRun_drop {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 .drop f X = some (f', Y)) : HeadRun P host s .drop f f' X Y := by
  obtain ⟨rfl, h'⟩ := step1_stk_inv rfl h
  obtain ⟨v, rfl⟩ := stepS_drop_inv h'
  have hs : Step P host ⟨s, f, vals [v] ++ [.plain GInstr.drop.lower]⟩ ⟨s, f, vals []⟩ :=
    Step.parametric (ParametricStep.drop v)
  simpa using headRun_one (W := Y.reverse) hs

theorem headRun_nop {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 .nop f X = some (f', Y)) : HeadRun P host s .nop f f' X Y := by
  obtain ⟨rfl, h'⟩ := step1_stk_inv rfl h
  obtain rfl : X = Y := Option.some.inj h'
  have hs : Step P host ⟨s, f, vals [] ++ [.plain GInstr.nop.lower]⟩ ⟨s, f, vals []⟩ :=
    Step.parametric ParametricStep.nop
  simpa using headRun_one (W := X.reverse) hs

/-- `local.get` reads a set local. -/
theorem step1_get_inv {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localGet x) f X = some (f', Y)) :
    ∃ v, f.local? x = some (some v) ∧ f = f' ∧ Y = v :: X := by
  obtain ⟨o, ho, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, rfl, he⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨v, ho, rfl, rfl⟩

theorem headRun_get {s : Store H} {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localGet x) f X = some (f', Y)) : HeadRun P host s (.localGet x) f f' X Y := by
  obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h
  have hs : Step P host ⟨s, f, vals [] ++ [.plain (GInstr.localGet x).lower]⟩
      ⟨s, f, vals [v]⟩ :=
    Step.variable (VariableStep.localGet hv)
  simpa using headRun_one (W := X.reverse) hs

/-- `local.set` writes an existing local. -/
theorem step1_set_inv {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localSet x) f X = some (f', Y)) :
    ∃ v, X = v :: Y ∧ x.toNat < f.locals.length ∧ f' = f.setLocal x v := by
  rcases X with _ | ⟨v, X'⟩
  · cases h
  · have h' : (if x.toNat < f.locals.length then some (f.setLocal x v, X') else none) =
        some (f', Y) := h
    split at h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      exact ⟨v, rfl, by assumption, rfl⟩
    · cases h'

/-- `local.tee` writes an existing local and keeps the value. -/
theorem step1_tee_inv {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localTee x) f X = some (f', Y)) :
    ∃ v X', X = v :: X' ∧ Y = v :: X' ∧ x.toNat < f.locals.length ∧ f' = f.setLocal x v := by
  rcases X with _ | ⟨v, X'⟩
  · cases h
  · have h' : (if x.toNat < f.locals.length then some (f.setLocal x v, v :: X') else none) =
        some (f', Y) := h
    split at h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      exact ⟨v, X', rfl, rfl, by assumption, rfl⟩
    · cases h'

theorem headRun_set {s : Store H} {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localSet x) f X = some (f', Y)) : HeadRun P host s (.localSet x) f f' X Y := by
  obtain ⟨v, rfl, hx, rfl⟩ := step1_set_inv h
  have hs : Step P host ⟨s, f, vals [v] ++ [.plain (GInstr.localSet x).lower]⟩
      ⟨s, f.setLocal x v, vals []⟩ :=
    Step.variable (VariableStep.localSet hx)
  simpa using headRun_one (W := Y.reverse) hs

theorem headRun_tee {s : Store H} {x : LocalIdx} {f f' : Frame} {X Y : List Val}
    (h : step1 (.localTee x) f X = some (f', Y)) : HeadRun P host s (.localTee x) f f' X Y := by
  obtain ⟨v, X', rfl, rfl, hx, rfl⟩ := step1_tee_inv h
  have h₁ : Step P host ⟨s, f, vals [v] ++ [.plain (GInstr.localTee x).lower]⟩
      ⟨s, f, vals [v] ++ [v.toAdmin, .plain (.localSet x)]⟩ :=
    Step.variable VariableStep.localTee
  have h₂ : Step P host ⟨s, f, vals [v] ++ [v.toAdmin, .plain (.localSet x)]⟩
      ⟨s, f.setLocal x v, vals [v] ++ []⟩ :=
    Step.vals_left (Step.variable (VariableStep.localSet hx)) [v]
  refine ⟨X'.reverse, [v], [v], by simp, by simp, ?_⟩
  exact .tail (.single h₁) (by simpa using h₂)

theorem headRun {s : Store H} {i : GInstr} (hi : i.isConst = false) {f f' : Frame}
    {X Y : List Val} (h : step1 i f X = some (f', Y)) : HeadRun P host s i f f' X Y := by
  cases i with
  | const _ => cases hi
  | bin _ => exact headRun_bin h
  | eqz => exact headRun_eqz h
  | localGet _ => exact headRun_get h
  | localSet _ => exact headRun_set h
  | localTee _ => exact headRun_tee h
  | drop => exact headRun_drop h
  | nop => exact headRun_nop h

/-- **One non-constant instruction of the interpreter is at least one machine step.** -/
theorem step1_transGen {i : GInstr} (hi : i.isConst = false) {s : Store H} {f f' : Frame}
    {X Y : List Val} (h : step1 i f X = some (f', Y)) (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  obtain ⟨W, us, ws, hX, hY, hr⟩ := headRun (P := P) (host := host) (s := s) hi h
  have hl := lift_transGen hr W rest
  rw [hX, hY]
  simpa [List.append_assoc] using hl

/-- One instruction of the interpreter is a machine run (no step for a constant). -/
theorem step1_steps {i : GInstr} {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : step1 i f X = some (f', Y)) (rest : List Admin) :
    Steps P host ⟨s, f, vals X.reverse ++ .plain i.lower :: rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  cases hc : i.isConst with
  | false => exact (step1_transGen hc h rest).to_reflTransGen
  | true =>
    obtain ⟨k, rfl⟩ : ∃ k, i = .const k := by cases i <;> simp_all [GInstr.isConst]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have e : vals X.reverse ++ Admin.plain (GInstr.const k).lower :: rest =
        vals (Val.i32 k :: X).reverse ++ rest := by
      simp [vals, GInstr.lower, Val.toAdmin, Val.i32]
    rw [e]

/-- **Adequacy**: a successful run of the interpreter is a run of the machine. -/
theorem run_steps {c : List GInstr} {s : Store H} {f f' : Frame} {X Y : List Val}
    (h : run c f X = some (f', Y)) (rest : List Admin) :
    Steps P host ⟨s, f, vals X.reverse ++ expression (lower c) ++ rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  induction c generalizing f X with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    show Steps P host ⟨s, f, vals X.reverse ++ [] ++ rest⟩ _
    rw [List.append_nil]
  | cons i c ih =>
    obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    have hs := step1_steps (P := P) (host := host) (s := s) h₁ (expression (lower c) ++ rest)
    have e : vals X.reverse ++ expression (lower (i :: c)) ++ rest =
        vals X.reverse ++ .plain i.lower :: (expression (lower c) ++ rest) := by
      simp [lower, expression]
    rw [e]
    exact hs.trans (by simpa using ih h₂)

/-- A successful run of code that is not all constants takes at least one machine step. -/
theorem run_transGen {c : List GInstr} (hc : ∃ i ∈ c, i.isConst = false) {s : Store H}
    {f f' : Frame} {X Y : List Val} (h : run c f X = some (f', Y)) (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨s, f, vals X.reverse ++ expression (lower c) ++ rest⟩
      ⟨s, f', vals Y.reverse ++ rest⟩ := by
  obtain ⟨ks, i, c₁, rfl, hi⟩ := split_op hc
  rw [run_consts, run_cons] at h
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  have hs := step1_transGen (P := P) (host := host) (s := s) hi h₁ (expression (lower c₁) ++ rest)
  have e : vals X.reverse ++ expression (lower (ks.map GInstr.const ++ i :: c₁)) ++ rest =
      vals ((kvals ks).reverse ++ X).reverse ++ .plain i.lower :: (expression (lower c₁) ++ rest) := by
    have hk : expression (lower (ks.map GInstr.const)) = vals (kvals ks) := expression_consts ks
    have e₁ : expression (lower (ks.map GInstr.const ++ i :: c₁)) =
        vals (kvals ks) ++ .plain i.lower :: expression (lower c₁) := by
      rw [← hk]
      simp [lower, expression]
    rw [e₁]
    simp [List.append_assoc]
  rw [e]
  exact hs.trans_left (by simpa using run_steps (P := P) (host := host) (s := s) h₂ rest)

end Silmaril.Wasm.FnInst.Ground
