module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Top

/-!
# The machine steps of the top frame against Core

From `Top` with a normalized top frame: falling off the end of the body (`end_case`), `return`
(`return_case`), `if` (`if_case`), a call of a defined function (`call_case`), and a
straight-line instruction that steps (`seg_next`) or traps (`seg_trapped`, `oob_trapped`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {mi : ModuleInst} {c : Cfg} {s : Store H} {fr : Silmaril.Wasm.FX.Asyncify.Tool.Frame}
  {frs : List Silmaril.Wasm.FX.Asyncify.Tool.Frame} {fs : CFr} {rest : List CFr}

local notation "Steps" => Execution.Core.Steps Pf host

theorem stackA_split (n : Nat) (ops : List W) :
    stackA ops = vals ((ops.drop n).reverse.map Val.i32 ++ (ops.take n).reverse.map Val.i32) := by
  conv_lhs => rw [← List.take_append_drop n ops]
  simp only [stackA, List.reverse_append, List.map_append]

theorem stackA_trap (ops : List W) (R : List Admin) :
    stackA ops ++ .trap :: R = vals (ops.reverse.map Val.i32) ++ [.trap] ++ R := by
  simp only [stackA, List.append_assoc, List.singleton_append]

theorem absOk_cons_inv {b : Bool} {a : List Bool} {ops : List W} (h : AbsOk (b :: a) ops) :
    ∃ w ops', ops = w :: ops' ∧ (b = true → w.toNat % 4 = 0) ∧ AbsOk a ops' := by
  obtain ⟨w, ops', hw, ha, he⟩ := List.forall₂_cons_left_iff.1 h
  exact ⟨w, ops', he, hw, ha⟩

theorem top_sinv (hT : Top cap E mi c s fr frs fs rest) : SInv cap E mi s c.globals c.mem :=
  hT.2.2.2.2.2.1

/-! ## Leaving the frame -/

theorem end_case (hT : Top cap E mi c s fr frs fs rest) (h0 : fs.l0.code = [])
    (hls : fs.ls = []) : CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hcode : fr.code = [] := by rw [hT.2.1.2.2.2, CFr.code, h0, hls]; rfl
  have hops : fr.ops = fs.l0.ops := by rw [fr_ops hT.2.1, hls, List.flatMap_nil, List.append_nil]
  have hlen : fs.l0.ops.length = fs.nres := by
    have hq := ck_nil_inv (h0 ▸ hT.2.2.2.1.2.1)
    rw [hls] at hq
    exact (absOk_length hT.2.2.2.1.1).symm.trans hq
  have hoob : ¬ OOB cap c := fun ⟨_, h, _⟩ => by simp [access, hT.1, hcode] at h
  have hstep : stepB cap E c = ret c fr.ops frs := by
    rw [stepB, ite_eq_right_iff.2 (fun h => absurd h hoob)]; simp [step, hT.1, hcode]
  have hcore : ∀ f, Steps ⟨s, f, [fs.admin mi []]⟩ ⟨s, f, stackA fs.l0.ops⟩ := fun f => by
    rw [admin_nil, h0, hls, show expression ([] : List Instr) = [] from rfl, List.append_nil]
    exact end_frameA (Pf := Pf) (host := host) (s := s) f mi fs.locals
        (fs.l0.ops.reverse.map Val.i32) (by rw [List.length_map, List.length_reverse, hlen])
  rw [hstep, hops]
  exact ret_case hT _ hlen hcore

theorem return_case (hT : Top cap E mi c s fr frs fs rest) {code : List Instr}
    (h0 : fs.l0.code = .return_ :: code) (hn : fs.nres ≤ fs.l0.abs.length) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hcode := fr_code hT.2.1 h0
  have hn' : fs.nres ≤ fs.l0.ops.length := by rw [← absOk_length hT.2.2.2.1.1]; exact hn
  have hstep : stepB cap E c = ret c (fs.l0.ops.take fs.nres) frs := by
    rw [stepB_top hT.1 hcode (not_oob hT.1 hcode (by simp [accessAt]))]
    simp only [exec, ctlOf, hT.2.1.2.1, fr_ops hT.2.1, List.take_append_of_le_length hn']
  have hcore : ∀ f, Steps ⟨s, f, [fs.admin mi []]⟩ ⟨s, f, stackA (fs.l0.ops.take fs.nres)⟩ :=
    fun f => by
      rw [admin_nil, h0, stackA_split fs.nres fs.l0.ops,
        show expression (.return_ :: code) = [.plain .return_] ++ expression code from rfl,
        ← List.append_assoc]
      exact ret_frameA (Pf := Pf) (host := host) (s := s) f mi fs.locals fs.ls _
          ((fs.l0.ops.take fs.nres).reverse.map Val.i32) (expression code)
          (by simp only [List.length_map, List.length_reverse, List.length_take]; omega)
  rw [hstep]
  exact ret_case hT _ (by rw [List.length_take]; omega) hcore

/-! ## `if` -/

theorem if_core {F : Silmaril.Wasm.Execution.Core.Frame} (x : W) (ops : List W)
    (t e : List Instr) (R : List Admin) :
    Steps ⟨s, F, stackA (x :: ops) ++ .plain (.if_ .empty t e) :: R⟩
      ⟨s, F, stackA ops ++ .label 0 [] (expression (if x = 0 then e else t)) :: R⟩ := by
  have h1 : Step Pf host ⟨s, F, [constI32 x, .plain (.if_ .empty t e)]⟩
      ⟨s, F, [.plain (.block .empty (if x = 0 then e else t))]⟩ := by
    by_cases hx : x = 0
    · rw [ite_eq_left_iff.2 (fun h => absurd hx h), hx]; exact .ifFalse
    · rw [ite_eq_right_iff.2 (fun h => absurd h hx)]; exact .ifTrue hx
  have h2 : Step Pf host ⟨s, F, [.plain (.block .empty (if x = 0 then e else t))]⟩
      ⟨s, F, [.label 0 [] (expression (if x = 0 then e else t))]⟩ :=
    Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  have h3 := steps_instrs (ops.reverse.map Val.i32) R ((Relation.ReflTransGen.single h1).tail h2)
  rw [stackA_cons]
  simpa only [stackA, constI32, List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append] using h3

theorem if_case (hT : Top cap E mi c s fr frs fs rest) {t e code : List Instr} {b : Bool}
    {a : List Bool} (h0 : fs.l0.code = .if_ .empty t e :: code) (habs : fs.l0.abs = b :: a)
    (ht : Ck (fs.ctx E) (· = []) t []) (he : Ck (fs.ctx E) (· = []) e [])
    (hck : Ck (fs.ctx E) (qOf fs.nres fs.ls) code a) :
    CMatch Pf host cap E mi s (stackC mi (fs :: rest) []) (stepB cap E c) := by
  have hcode := fr_code hT.2.1 h0
  obtain ⟨x, ops', hops, -, ha⟩ := absOk_cons_inv (habs ▸ hT.2.2.2.1.1)
  have hstep : stepB cap E c = .next (c.setTop
      { fr with
        ops := ops' ++ fs.ls.flatMap Lvl.ops
        code := (if x = 0 then e else t) ++ (code ++ fs.ls.flatMap Lvl.code) } frs) := by
    rw [stepB_top hT.1 hcode (not_oob hT.1 hcode (by simp [accessAt]))]
    simp only [exec, ctlOf, fr_ops hT.2.1, hops, List.cons_append]
  have harm : Ck (fs.ctx E) (· = []) (if x = 0 then e else t) [] := by
    by_cases hx : x = 0
    · rw [ite_eq_left_iff.2 (fun h => absurd hx h)]; exact he
    · rw [ite_eq_right_iff.2 (fun h => absurd h hx)]; exact ht
  have hcore : Steps ⟨s, ⟨[], mi⟩, stackC mi (fs :: rest) []⟩ ⟨s, ⟨[], mi⟩,
      stackC mi (⟨fs.locals, fs.nres, ⟨[], [], if x = 0 then e else t⟩,
        ⟨ops', a, code⟩ :: fs.ls⟩ :: rest) []⟩ := by
    rw [stackC_cons, stackC_cons, admin_nil, admin_nil, h0, hops]
    exact steps_top rest fs.ls (if_core x ops' t e (expression code)) _
  rw [hstep]
  refine ⟨s, _, hcore, top_crel ⟨rfl, ⟨hT.2.1.1, hT.2.1.2.1, ?_, ?_⟩, hT.2.2.1,
    ⟨.nil, harm, ha, hck, hT.2.2.2.1.2.2⟩, hT.2.2.2.2.1, hT.2.2.2.2.2.1, hT.2.2.2.2.2.2⟩⟩
  · simp only [CFr.ops, List.nil_append, List.flatMap_cons]
  · simp only [CFr.code, List.flatMap_cons]

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
