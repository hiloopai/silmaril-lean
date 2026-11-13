module

public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Core head steps of `nop` and `ref.func`, at every profile

`Det.Head` inversions for the two plain instructions the WasmFX generator examples need beyond
those of `Silmaril.Proofs.Wasm.Logic.Hoare.Instr` (`head_call`, `head_intBinOp`). The local
macros `fnv_simp`, `fam_cfg`, `fam_code` and `head_absurd` are copied from
`Silmaril/Proofs/Wasm/Logic/Hoare/Instr.lean` (they are local there).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape)
open Silmaril.Wasm.Logic.Hoare (cfg_split fnv_eq_split fnv_intConst_cons)

variable {H : Type} {P : Profile}

local macro "fnv_simp " h:ident : tactic => `(tactic| (
  try simp only [SingleThreaded.Det.fnv_toAdmin_cons, SingleThreaded.Det.fnv_ref_cons, constI32,
    SingleThreaded.Det.fnv_vals_append, aconst, fnv_intConst_cons] at $h:ident
  simp [SingleThreaded.Det.fnv, Admin.val?] at $h:ident))

local macro "fam_cfg " h:ident : tactic => `(tactic| (
  obtain ⟨rfl, rfl, h₁⟩ := cfg_split $h rfl
  fnv_simp h₁))

local macro "fam_code " h:ident : tactic => `(tactic| (
  have h₁ := fnv_eq_split $h rfl
  fnv_simp h₁))

local macro "head_absurd" : tactic => `(tactic| (exfalso; first
  | exact absurd (famOf_of_shape (SingleThreaded.Det.ParametricStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.NumericStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VectorStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.VariableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.TableStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.MemoryStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.RefStep.shape ‹_›)).2 (by simp [famOf])
  | exact absurd (famOf_of_shape (SingleThreaded.Det.AggregateStep.shape ‹_›)).2 (by simp [famOf])
  | (simp only [Admin.IsCallRef, Admin.IsReturnCallRef] at *; done)))

theorem par_nop {args : List Val} {is' : List Admin}
    (h : ParametricStep (vals args ++ [.plain .nop]) is') : args = [] ∧ is' = [] := by
  generalize hc : vals args ++ [.plain .nop] = c at h
  cases h with
  | nop =>
    have h₁ := fnv_eq_split hc rfl
    fnv_simp h₁
    exact ⟨h₁, rfl⟩
  | _ => fam_code hc

theorem head_nop {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Head P s f args (.plain .nop) c₀) : args = [] ∧ c₀ = ⟨s, f, []⟩ := by
  cases h with
  | parametric h =>
    obtain ⟨rfl, rfl⟩ := par_nop h
    exact ⟨rfl, rfl⟩
  | _ => head_absurd

theorem ref_refFunc {s : Store H} {f : Frame} {args : List Val} {x : FuncIdx} {c₀ : Config H}
    (h : RefStep ⟨s, f, vals args ++ [.plain (.refFunc x)]⟩ c₀) :
    args = [] ∧ ∃ a, f.module.funcs[x.toNat]? = some a ∧ c₀ = ⟨s, f, [.ref (.func a)]⟩ := by
  generalize hc : (⟨s, f, vals args ++ [.plain (.refFunc x)]⟩ : Config H) = c at h
  cases h with
  | refFunc hx =>
    obtain ⟨rfl, rfl, h₁⟩ := cfg_split hc rfl
    fnv_simp h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨rfl, _, hx, rfl⟩
  | _ => fam_cfg hc

theorem head_refFunc {s : Store H} {f : Frame} {args : List Val} {x : FuncIdx} {c₀ : Config H}
    (h : Head P s f args (.plain (.refFunc x)) c₀) :
    args = [] ∧ ∃ a, f.module.funcs[x.toNat]? = some a ∧ c₀ = ⟨s, f, [.ref (.func a)]⟩ := by
  cases h with
  | reference h => exact ref_refFunc h
  | _ => head_absurd

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
