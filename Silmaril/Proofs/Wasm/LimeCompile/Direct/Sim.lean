module

public import Silmaril.Wasm.LimeCompile.Direct.Defs
public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.ConstSelectSim
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.SingleThreaded.InertHead

/-!
# The direct rewrite of a typed `select`: the code simulation

Base pairs relate a `select` with one annotation to a `select` with another (`selBI`, symmetric).
In Core 3.0 the `select` rules ignore the annotation, so the simulation is lockstep, at every
numerical profile and under every host (a `select` never calls one).

* `select_step_inv`, `select_step`: the inversion and the construction of a `select` step;
* `selBaseSim`: the `BaseSim` obligations, for every function relation;
* `lowerL_rel`, `lowerModule_rel`: the rewrite relates every body to its image
  (`InstrsRel selBI`), so a module and its lowering are `ModuleBodiesRel selBI`-related.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Direct

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.LimeCompile.Direct

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Source base pairs: two `select`s with any annotations. -/
inductive selBI : List Instr → List Instr → Prop where
  | mk (ts ts' : Option (List ValType)) : selBI [.select ts] [.select ts']

/-- Runtime base pairs: the same, as administrative code. -/
inductive selB : List Admin → List Admin → Prop where
  | mk (ts ts' : Option (List ValType)) : selB [.plain (.select ts)] [.plain (.select ts')]

theorem selBI_flip : (fun a b => selBI b a) = selBI := by
  funext a b
  apply propext
  constructor
  · rintro ⟨ts, ts'⟩; exact .mk _ _
  · rintro ⟨ts, ts'⟩; exact .mk _ _

/-- Inverting a `select` step: it pops two values and an `i32`. -/
theorem select_step_inv {s s' : Store H} {f f' : Frame} {vs : List Val} {rest es' : List Admin}
    {ts : Option (List ValType)}
    (h : Step P host ⟨s, f, vals vs ++ .plain (.select ts) :: rest⟩ ⟨s', f', es'⟩) :
    ∃ (pre : List Val) (a b : Val) (c : BitVec 32), vs = pre ++ [a, b, .num ⟨.int .i32, c⟩] ∧
      s' = s ∧ f' = f ∧ es' = vals pre ++ [(if c = 0 then b else a).toAdmin] ++ rest := by
  obtain ⟨pre, args, c₀, hW, hh, he⟩ :=
    SingleThreaded.inert_head_inv (by simp [Admin.val?]) (by simp) (by simp [Admin.isCallRef]) h
  obtain ⟨a, b, c, hargs, hc₀⟩ := ConstSelect.head_select hh
  subst hargs hc₀
  simp only [Config.mk.injEq] at he
  exact ⟨pre, a, b, c, hW, he.1, he.2.1, he.2.2⟩

/-- A `select` step, with any annotation, in a value prefix and a suffix. -/
theorem select_step (u : Store H) (f : Frame) (pre : List Val) (a b : Val) (c : BitVec 32)
    (rest : List Admin) (ts : Option (List ValType)) :
    Step P host ⟨u, f, vals (pre ++ [a, b, .num ⟨.int .i32, c⟩]) ++ .plain (.select ts) :: rest⟩
      ⟨u, f, vals pre ++ [(if c = 0 then b else a).toAdmin] ++ rest⟩ := by
  have hbase : Step P host
      ⟨u, f, [a.toAdmin, b.toAdmin, constI32 c, .plain (.select ts)]⟩
      ⟨u, f, [(if c = 0 then b else a).toAdmin]⟩ := by
    by_cases hc : c = 0
    · subst hc
      simpa using Step.parametric (P := P) (host := host) (s := u) (f := f)
        (ParametricStep.selectFalse a b ts)
    · simp only [hc, ↓reduceIte]
      simpa using Step.parametric (P := P) (host := host) (s := u) (f := f)
        (ParametricStep.selectTrue (v₁ := a) (v₂ := b) (ts := ts) hc)
  have h := Step.append_right (Step.vals_left hbase pre) rest
  simpa [vals, constI32, Val.i32, List.append_assoc] using h

/-- The step obligation at a `select` pair: lockstep. -/
theorem select_matched {F : FuncInst H → FuncInst H → Prop} {s u s' : Store H} {f f' : Frame}
    {vs : List Val} {rest rest' es' : List Admin} {ts ts' : Option (List ValType)}
    (hst : StoreRel F s u) (hrest : AdminsRel selBI selB rest rest')
    (hstep : Step P host ⟨s, f, vals vs ++ [.plain (.select ts)] ++ rest⟩ ⟨s', f', es'⟩) :
    ∃ (t' : Store H) (es'' : List Admin),
      (Relation.TransGen (Step P host) ⟨u, f, vals vs ++ [.plain (.select ts')] ++ rest'⟩
          ⟨t', f', es''⟩ ∨
        (t' = u ∧ f' = f ∧ es'' = vals vs ++ [.plain (.select ts')] ++ rest' ∧
          codeSize es' < codeSize (vals vs ++ [.plain (.select ts)] ++ rest))) ∧
      StoreRel F s' t' ∧ AdminsRel selBI selB es' es'' := by
  have hs : Step P host ⟨s, f, vals vs ++ .plain (.select ts) :: rest⟩ ⟨s', f', es'⟩ := by
    simpa using hstep
  obtain ⟨pre, a, b, c, hvs, hs₁, hf₁, he₁⟩ := select_step_inv hs
  subst hvs hs₁ hf₁ he₁
  have hR : Step P host
      ⟨u, f', vals (pre ++ [a, b, .num ⟨.int .i32, c⟩]) ++ [.plain (.select ts')] ++ rest'⟩
      ⟨u, f', vals pre ++ [(if c = 0 then b else a).toAdmin] ++ rest'⟩ := by
    simpa using select_step (P := P) (host := host) u f' pre a b c rest' ts'
  exact ⟨u, vals pre ++ [(if c = 0 then b else a).toAdmin] ++ rest', Or.inl (.single hR),
    hst, (AdminsRel.refl _).append hrest⟩

/-- **The lockstep simulation of `select` annotations**, for every function relation. -/
theorem selBaseSim {F : FuncInst H → FuncInst H → Prop} : BaseSim P host F selBI selB where
  src := by
    intro x y h
    cases h with
    | mk ts ts' => exact .mk ts ts'
  step := by
    intro s u s' f f' vs x y rest rest' es' hst hxy hrest hstep
    cases hxy with
    | mk ts ts' => exact select_matched hst hrest hstep
  exit := by
    intro s u f vs us x y kk j hst hxy hk he
    exfalso
    cases hxy with
    | mk ts ts' =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain (.select ts)) (x' := [])
        (by simp [Admin.val?]) (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp)
        (by simp) hk (by simpa using he)
  values := by
    intro s u f vs us x y hst hxy hx
    exfalso
    cases hxy with
    | mk ts ts' =>
      have hmem : Admin.plain (.select ts) ∈ vals us := by rw [← hx]; simp
      exact SingleThreaded.Det.mem_vals hmem (by simp [Admin.val?])

set_option linter.unusedTactic false in
mutual
/-- The rewrite relates an instruction to its image. -/
theorem lowerI_rel (i : Instr) : InstrRel selBI i (lowerI i) ∨ selBI [i] [lowerI i] := by
  cases i with
  | select ts =>
    cases ts with
    | none => rw [lowerI]; exact Or.inl (.refl _); all_goals simp
    | some ts =>
      rw [lowerI]
      split
      · exact Or.inr (.mk _ _)
      · exact Or.inl (.refl _)
  | block bt b => rw [lowerI]; exact Or.inl (.block bt (lowerL_rel b))
  | loop bt b => rw [lowerI]; exact Or.inl (.loop bt (lowerL_rel b))
  | if_ bt b₁ b₂ => rw [lowerI]; exact Or.inl (.if_ bt (lowerL_rel b₁) (lowerL_rel b₂))
  | tryTable bt cs b => rw [lowerI]; exact Or.inl (.tryTable bt cs (lowerL_rel b))
  | _ => rw [lowerI]; exact Or.inl (.refl _); all_goals simp
termination_by sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The rewrite relates an instruction sequence to its image. -/
theorem lowerL_rel : ∀ is : List Instr, InstrsRel selBI is (lowerL is)
  | [] => by rw [lowerL]; exact .nil
  | i :: is => by
    rw [lowerL]
    rcases lowerI_rel i with h | h
    · exact .cons h (lowerL_rel is)
    · exact InstrsRel.append (x := [i]) (y := [lowerI i]) (.base h) (lowerL_rel is)
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- **A module and its lowering have related bodies.** -/
theorem lowerModule_rel (m : Module) : ModuleBodiesRel selBI m (lowerModule m) where
  other := rfl
  funcs := by
    simp only [lowerModule, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun f _ => ⟨rfl, rfl, lowerL_rel f.body⟩

end Silmaril.Proofs.Wasm.LimeCompile.Direct
