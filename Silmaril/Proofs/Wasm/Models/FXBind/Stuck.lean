module

public import Silmaril.Proofs.Wasm.Models.FXBind.Behaviours
public import Silmaril.Wasm.SingleThreaded.HeadInversion
public import Silmaril.Wasm.SingleThreaded.Determinism

/-!
# Partial application: calls with too few arguments are stuck

* `call_short_stuck`: without host calls, `V; ref.func a; call_ref` does not step when `a` has
  more parameters than `V` has values (the only `call_ref` rules need the full argument list);
* `underHW_short_empty`: such a call under a handler frame, after any values, has no CoreFX
  behaviours (the handler frame does not let the call reach the values outside it).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXLower (tgtCall onHandler)
open Silmaril.Proofs.Wasm.Models.FXLower (underH underHW UnderHStep Escapes step_underH
  step_prefixHandler behavioursFX_sub_of_succ underHW_not_result)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head famOf famOf_of_shape IsCallRef.famOf
  splitVals_vals_cons splitVals_vals)
open Silmaril.Wasm.SingleThreaded (splitVals)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- The call instruction is not a value. -/
theorem callRefType_val (d : DefType) : (Admin.callRefType d).val? = none := rfl

theorem tgtCall_eq (a : Nat) (d : DefType) (V : List Val) :
    tgtCall a d V = vals (V ++ [.ref (.func a)]) ++ Admin.callRefType d :: [] := by
  simp [tgtCall, vals_append]
  rfl

/-- The first non-value of the call. -/
theorem splitVals_tgtCall (a : Nat) (d : DefType) (V : List Val) :
    splitVals (tgtCall a d V) = (V ++ [.ref (.func a)], [Admin.callRefType d]) := by
  rw [tgtCall_eq, splitVals_vals_cons (callRefType_val d)]

/-- A head step at `call_ref` with a function reference is a call on its parameters. -/
theorem head_callRef_args {s : Store H} {f : Frame} {args : List Val} {d : DefType}
    {c₀ : Config H} (h : Head P s f args (.callRefType d) c₀) :
    (∃ vs a fi ps rs, args = vs ++ [.ref (.func a)] ∧ s.funcs[a]? = some fi ∧
      Expand fi.type (.func ps rs) ∧ vs.length = ps.length) ∨ args = [.ref .null] := by
  have hk : famOf (Admin.callRefType d) = .control := IsCallRef.famOf (by simp [Admin.IsCallRef])
  cases h with
  | parametric h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape h')).2.symm.trans hk) (by simp)
  | numeric h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape h')).2.symm.trans hk) (by simp)
  | vector h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape h')).2.symm.trans hk) (by simp)
  | «variable» h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape h')).2.symm.trans hk) (by simp)
  | table h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.TableStep.shape h')).2.symm.trans hk) (by simp)
  | memory h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape h')).2.symm.trans hk) (by simp)
  | reference h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.RefStep.shape h')).2.symm.trans hk) (by simp)
  | aggregate h' => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape h')).2.symm.trans hk) (by simp)
  | callRefNull _ => exact Or.inr rfl
  | callRefFunc ha _ hf he hn _ => exact Or.inl ⟨_, _, _, _, _, ha, hf, he, hn⟩

/-- **A call with too few arguments does not step** (no host calls). -/
theorem call_short_stuck {s : Store H} {f : Frame} {V : List Val} {a : Nat} {fi : FuncInst H}
    {d : DefType} {ps rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hV : V.length < ps.length) {c' : Config H}
    (h : Step P noHost ⟨s, f, tgtCall a d V⟩ c') : False := by
  rw [tgtCall_eq] at h
  obtain ⟨vs, args, c₀, hW, hh, -⟩ :=
    Silmaril.Wasm.SingleThreaded.hostFree_head_inv (callRefType_val d) (by simp) (by simp) h
  rcases head_callRef_args hh with ⟨us, a', fi', ps', rs', rfl, hf', he', hn⟩ | rfl
  · rw [← List.append_assoc] at hW
    obtain ⟨hVu, ha⟩ := List.append_inj' hW rfl
    have ha' : a' = a := by simpa using ha.symm
    subst ha'
    have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hf)
    subst hfi
    have hps : ps' = ps := by
      have := Silmaril.Wasm.SingleThreaded.Det.Expand.det he he'
      cases this
      rfl
    subst hps
    have hl : us.length ≤ V.length := by rw [hVu]; simp
    omega
  · obtain ⟨-, ha⟩ := List.append_inj' hW rfl
    simp at ha

/-- The short call is not a result and does not start with an escaping branch. -/
theorem tgtCall_not_escape {a : Nat} {d : DefType} {V vs : List Val} {X : Admin}
    {rest : List Admin} (hX : Escapes X) (h : tgtCall a d V = vals vs ++ [X] ++ rest) : False := by
  have h1 := congrArg splitVals h
  have hXv : X.val? = none := by
    rcases hX with ⟨l, rfl⟩ | rfl <;> rfl
  rw [splitVals_tgtCall, List.append_assoc, List.singleton_append,
    splitVals_vals_cons hXv] at h1
  simp only [Prod.mk.injEq, List.cons.injEq] at h1
  rcases hX with ⟨l, rfl⟩ | rfl <;> simp at h1

theorem tgtCall_not_result {a : Nat} {d : DefType} {V : List Val} (r : Result)
    (h : tgtCall a d V = r.toAdmin) : False := by
  have h1 := congrArg splitVals h
  rw [splitVals_tgtCall] at h1
  cases r with
  | values vs => rw [Result.toAdmin, splitVals_vals] at h1; simp at h1
  | throw b =>
    rw [show (Result.throw b).toAdmin = vals [.ref (.exn b)] ++ Admin.plain .throwRef :: [] from rfl,
      splitVals_vals_cons rfl] at h1
    simp at h1
  | trap =>
    rw [show (Result.trap).toAdmin = vals [] ++ Admin.trap :: [] from rfl,
      splitVals_vals_cons rfl] at h1
    simp at h1

/-- No step of the short call under a handler frame. -/
theorem underH_short_noStep {K : List (Option ContFX)} {hs : List HClause} {s : Store H}
    {f : Frame} {V : List Val} {a : Nat} {fi : FuncInst H} {d : DefType}
    {ps rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hV : V.length < ps.length) {y : ConfigFX H}
    (h : UnderHStep (P := P) K hs ⟨s, f, tgtCall a d V⟩ y) : False := by
  rcases h with ⟨c', hst, -⟩ | ⟨r, hr, -⟩ | ⟨vs, X, rest, hX, hc, -⟩
  · exact call_short_stuck hf he hV hst
  · exact tgtCall_not_result r hr
  · exact tgtCall_not_escape hX hc

/-- **A short call under a handler frame has no behaviours.** -/
theorem underHW_short_empty {K : List (Option ContFX)} {hs : List HClause} {W : List Val}
    {s : Store H} {f : Frame} {V : List Val} {a : Nat} {fi : FuncInst H} {d : DefType}
    {ps rs : Ty (.list .val)} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hV : V.length < ps.length) :
    behavioursFX P noHost noFX (underHW K hs W ⟨s, f, tgtCall a d V⟩) = ∅ := by
  refine Set.eq_empty_of_subset_empty (behavioursFX_sub_of_succ underHW_not_result ?_)
  intro y hy
  exfalso
  by_cases hW : W = []
  · subst hW
    exact underH_short_noStep hf he hV (step_underH (c := ⟨s, f, tgtCall a d V⟩) hy)
  · obtain ⟨y', hy', -⟩ := step_prefixHandler hy W hs ((tgtCall a d V).map .core) hW rfl
    exact underH_short_noStep hf he hV (step_underH (c := ⟨s, f, tgtCall a d V⟩) hy')

end Silmaril.Proofs.Wasm.Models.FXBind
