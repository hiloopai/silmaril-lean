module

public import Silmaril.Wasm.Models.V2Core.Defs

/-!
# Inversion of a 2.0 step at `val* (CALL_ADDR a)`, and host monotonicity

* `step_callAddr_inv`: a 2.0 step from code `val* (CALL_ADDR a)` calls the function at `a`. The
  address is allocated. A suffix `args` of the values has the arity of its parameters. Then
  either the function is Wasm code, or it is a host function `hh` and the step is a host
  outcome on `args`: a return to `val* result` on the returned store, or a divergence, which
  leaves the configuration unchanged;
* `not_step_unalloc`: at an unallocated address, the code `val* (CALL_ADDR a)` does not step;
* `behaviours_unalloc`: the 2.0 behaviours of invoking an unallocated address are empty;
* `step_of_closed`, `steps_of_closed`, `diverges_of_closed`, `behaviours_of_closed`: a step
  (run, divergence, behaviour) under the closed 2.0 host `closedV`, which has no outcome, is
  one under every host.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution (Admin Config Step Steps Diverges vals Result)

variable {H : Type}

/-- An administrative instruction that is neither a value nor a `CALL_ADDR`. -/
def nonCall : Admin → Bool
  | .plain (.intConst _ _) | .plain (.floatConst _ _) | .plain (.vecConst _)
  | .plain (.refNull _) | .refFuncAddr _ | .refHostAddr _ | .callAddr _ => false
  | _ => true

@[simp] theorem nonCall_toAdmin (v : VVal) :
    nonCall (Silmaril.Wasm.V2.Execution.Val.toAdmin v) = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

@[simp] theorem any_nonCall_vals (vs : List VVal) : (vals vs).any nonCall = false := by
  simp [vals]

@[simp] theorem any_nonCall_callAddr (vs : List VVal) (a : Nat) :
    (vals vs ++ [Admin.callAddr a]).any nonCall = false := by
  simp [nonCall]

theorem toAdmin_injective : Function.Injective Silmaril.Wasm.V2.Execution.Val.toAdmin :=
  fun x y h => by simpa using congrArg Admin.val? h

theorem vals_injective {vs ws : List VVal} (h : vals vs = vals ws) : vs = ws :=
  (List.map_injective_iff.mpr toAdmin_injective) h

theorem vals_callAddr_inj {vs ws : List VVal} {a b : Nat}
    (h : vals vs ++ [Admin.callAddr a] = vals ws ++ [Admin.callAddr b]) : vs = ws ∧ a = b := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨vals_injective h1, by simpa using h2⟩

/-- Every element of a sequence of values is a value. -/
theorem all_isVal_of_append {l r : List Admin} {vs : List VVal} (h : l ++ r = vals vs) :
    l.all Admin.isVal = true := by
  have hv : (l ++ r).all Admin.isVal = true := by
    rw [h]; exact Silmaril.Wasm.V2.Execution.all_isVal_vals vs
  simp only [List.all_append, Bool.and_eq_true] at hv
  exact hv.1

/-- **The context split of `val* x`** for a non-value `x`: a non-value code `is` under a value
prefix `vs₀` and a suffix `rest` is `val* x` itself. -/
theorem split_last {vs₀ vs : List VVal} {is rest : List Admin} {x : Admin}
    (his : is.all Admin.isVal = false) (h : vals vs₀ ++ is ++ rest = vals vs ++ [x]) :
    rest = [] ∧ ∃ vs₁, is = vals vs₁ ++ [x] ∧ vs = vs₀ ++ vs₁ := by
  rcases List.eq_nil_or_concat rest with rfl | ⟨r', y, rfl⟩
  · rcases List.eq_nil_or_concat is with rfl | ⟨is', z, rfl⟩
    · simp at his
    · have h' : (vals vs₀ ++ is') ++ [z] = vals vs ++ [x] := by simpa using h
      obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
      obtain ⟨l₁, l₂, rfl, e1, e2⟩ := List.map_eq_append_iff.mp (show vals vs = _ from h1.symm)
      have hl₁ : l₁ = vs₀ := vals_injective e1
      subst hl₁
      refine ⟨rfl, l₂, ?_, rfl⟩
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      rw [← e2]
      simp [vals]
  · have h' : (vals vs₀ ++ is ++ r') ++ [y] = vals vs ++ [x] := by simpa using h
    obtain ⟨h1, -⟩ := List.append_inj' h' rfl
    have hall := all_isVal_of_append (l := vals vs₀ ++ is) (r := r') (by simpa using h1)
    simp [his] at hall

/-- The conclusion of `step_callAddr_inv`. -/
def CallInv (host : VHost H) (c c' : Config H) (vs : List VVal) (a : Nat) : Prop :=
  ∃ fi, c.store.funcInst? a = some fi ∧ ∃ pre args, vs = pre ++ args ∧
    args.length = fi.type.params.length ∧
    ((∃ fn, fi.code = .wasm fn) ∨ ∃ hh, fi.code = .host hh ∧
      ((∃ s' r, host hh c.store args (.returned s' r) ∧
          c' = ⟨s', c.frame, vals pre ++ Result.toAdmin r⟩) ∨
        (host hh c.store args .diverged ∧ c' = c)))

theorem any_of_eq {l : List Admin} {vs : List VVal} {a : Nat}
    (hc : l = vals vs ++ [.callAddr a]) : l.any nonCall = false := by
  rw [hc]
  exact any_nonCall_callAddr vs a

/-- No `Step_pure` rule applies to `val* (CALL_ADDR a)`. -/
theorem pure_not_call {P : Profile} {is is' : List Admin}
    (hp : Silmaril.Wasm.V2.Execution.PureStep P is is') (hb : is.any nonCall = false) : False := by
  cases hp <;> simp [nonCall, Silmaril.Wasm.V2.Execution.constI32] at hb

/-- The only `Step_read` rule at `val* (CALL_ADDR a)` is `call_addr`. -/
theorem read_callInv {host : VHost H} {s : VStore H} {f : Silmaril.Wasm.V2.Execution.Frame}
    {is is' : List Admin} (hr : Silmaril.Wasm.V2.Execution.ReadStep s f is is')
    {vs : List VVal} {a : Nat} (hc : is = vals vs ++ [.callAddr a]) :
    CallInv host ⟨s, f, is⟩ ⟨s, f, is'⟩ vs a := by
  cases hr with
  | @callAddr a' vs' fi fn hf hcode hk =>
    obtain ⟨rfl, rfl⟩ := vals_callAddr_inj hc
    exact ⟨fi, hf, [], vs', rfl, hk, .inl ⟨fn, hcode⟩⟩
  | _ => exact absurd (any_of_eq hc) (by simp [nonCall, Silmaril.Wasm.V2.Execution.constI32])

/-- `CallInv` under a value prefix. -/
theorem callInv_ctxt {host : VHost H} {s s' : VStore H}
    {f f' : Silmaril.Wasm.V2.Execution.Frame} {vs₀ vs₁ : List VVal} {is' : List Admin} {a : Nat}
    (ih : CallInv host ⟨s, f, vals vs₁ ++ [.callAddr a]⟩ ⟨s', f', is'⟩ vs₁ a) :
    CallInv host ⟨s, f, vals vs₀ ++ (vals vs₁ ++ [.callAddr a]) ++ []⟩
      ⟨s', f', vals vs₀ ++ is' ++ []⟩ (vs₀ ++ vs₁) a := by
  obtain ⟨fi, hf, pre, args, rfl, hk, hcase⟩ := ih
  refine ⟨fi, hf, vs₀ ++ pre, args, by simp, hk, ?_⟩
  rcases hcase with hw | ⟨hh, hcode, ⟨s'', r, hr, heq⟩ | ⟨hdiv, heq⟩⟩
  · exact .inl hw
  · have hst : s' = s'' ∧ f' = f ∧ is' = vals pre ++ Result.toAdmin r := by
      simpa only [Config.mk.injEq] using heq
    obtain ⟨rfl, rfl, rfl⟩ := hst
    exact .inr ⟨hh, hcode, .inl ⟨_, r, hr, by simp [vals]⟩⟩
  · have hst : s' = s ∧ f' = f ∧ is' = vals (pre ++ args) ++ [.callAddr a] := by
      simpa only [Config.mk.injEq] using heq
    obtain ⟨rfl, rfl, rfl⟩ := hst
    exact .inr ⟨hh, hcode, .inr ⟨hdiv, rfl⟩⟩

/-- **Inversion at `val* (CALL_ADDR a)`.** -/
theorem step_callAddr_inv {P : Profile} {host : VHost H} {c c' : Config H}
    (h : Step P host c c') :
    ∀ {vs : List VVal} {a : Nat}, c.code = vals vs ++ [.callAddr a] → CallInv host c c' vs a := by
  induction h with
  | pure hp => exact fun hc => (pure_not_call hp (any_of_eq hc)).elim
  | read hr => exact fun hc => read_callInv hr hc
  | ctxtInstrs hstep _ ih =>
    intro vs a hc
    obtain ⟨rfl, vs₁, rfl, rfl⟩ := split_last hstep.not_allVals hc
    exact callInv_ctxt (ih rfl)
  | ctxtLabel _ _ => exact fun hc => absurd (any_of_eq hc) (by simp [nonCall])
  | ctxtFrame _ _ => exact fun hc => absurd (any_of_eq hc) (by simp [nonCall])
  | @callAddrHost s s' f a' vs' fi hh r hf hcode hk hhost =>
    intro vs a hc
    obtain ⟨rfl, rfl⟩ := vals_callAddr_inj hc
    exact ⟨fi, hf, [], vs', rfl, hk, .inr ⟨hh, hcode, .inl ⟨s', r, hhost, by simp [vals]⟩⟩⟩
  | @callAddrHostDiv s f a' vs' fi hh hf hcode hk hhost =>
    intro vs a hc
    obtain ⟨rfl, rfl⟩ := vals_callAddr_inj hc
    exact ⟨fi, hf, [], vs', rfl, hk, .inr ⟨hh, hcode, .inr ⟨hhost, rfl⟩⟩⟩
  | _ =>
    exact fun hc => absurd (any_of_eq hc) (by simp [nonCall, Silmaril.Wasm.V2.Execution.constI32])

/-- At an unallocated address, `val* (CALL_ADDR a)` does not step. -/
theorem not_step_unalloc {P : Profile} {host : VHost H} {s : VStore H}
    {f : Silmaril.Wasm.V2.Execution.Frame} {vs : List VVal} {a : Nat} {c' : Config H}
    (ha : s.funcs.length ≤ a) : ¬ Step P host ⟨s, f, vals vs ++ [.callAddr a]⟩ c' := by
  intro h
  obtain ⟨fi, hf, -⟩ := step_callAddr_inv h rfl
  simp [Silmaril.Wasm.V2.Execution.Store.funcInst?, List.getElem?_eq_none ha] at hf

/-- A configuration with no step has no further run. -/
theorem steps_of_stuck {P : Profile} {host : VHost H} {c c' : Config H}
    (hn : ∀ c'', ¬ Step P host c c'') (h : Steps P host c c') : c' = c := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hs _ _ => exact absurd hs (hn _)

/-- `val* (CALL_ADDR a)` is not a result. -/
theorem callAddr_not_result {vs : List VVal} {a : Nat} (r : Result) :
    vals vs ++ [Admin.callAddr a] ≠ r.toAdmin := by
  intro h
  cases r with
  | values ws =>
    have hb := congrArg (fun l => List.all l Admin.isVal) h
    simp [Result.toAdmin, Admin.isVal, Admin.val?] at hb
  | trap =>
    have hb := congrArg List.getLast? h
    simp [Result.toAdmin] at hb

/-- **The 2.0 behaviours of invoking an unallocated address are empty.** -/
theorem behaviours_unalloc (P : Profile) (src : VHost H) (s : VStore H) {a : Nat}
    (ha : s.funcs.length ≤ a) (vs : List VVal) :
    Silmaril.Wasm.V2.Execution.behaviours P src s a vs = ∅ := by
  have hn : ∀ c'', ¬ Step P src (Silmaril.Wasm.V2.Execution.invoke s a vs) c'' :=
    fun _ => not_step_unalloc ha
  ext b
  simp only [Silmaril.Wasm.V2.Execution.behaviours_eq,
    Silmaril.Wasm.V2.Execution.behavioursOf, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨c', r, hrun, hcode, -⟩
    obtain rfl := steps_of_stuck hn hrun
    exact callAddr_not_result r hcode
  · rintro ⟨-, hdiv⟩
    obtain ⟨c', hs, -⟩ := Silmaril.InfiniteTrace.unfold hdiv
    exact hn _ hs

/-! ## Host monotonicity from the closed host -/

/-- Rebuild a store-level 2.0 step (one that is neither a context nor a host rule) from its
premises, for another host. -/
macro "restep" : tactic =>
  `(tactic| first
    | (apply Step.localSet; all_goals assumption)
    | (apply Step.globalSet; all_goals assumption)
    | (apply Step.tableSetTrap; all_goals assumption)
    | (apply Step.tableSetVal; all_goals assumption)
    | (apply Step.tableGrowSucceed; all_goals assumption)
    | (apply Step.tableGrowFail; all_goals assumption)
    | (apply Step.elemDrop; all_goals assumption)
    | (apply Step.storeIntTrap; all_goals assumption)
    | (apply Step.storeIntVal; all_goals assumption)
    | (apply Step.storeFloatTrap; all_goals assumption)
    | (apply Step.storeFloatVal; all_goals assumption)
    | (apply Step.storePackTrap; all_goals assumption)
    | (apply Step.storePackVal; all_goals assumption)
    | (apply Step.vecStoreOob; all_goals assumption)
    | (apply Step.vecStoreVal; all_goals assumption)
    | (apply Step.vecStoreLaneOob; all_goals assumption)
    | (apply Step.vecStoreLaneVal; all_goals assumption)
    | (apply Step.memoryGrowSucceed; all_goals assumption)
    | (apply Step.memoryGrowFail; all_goals assumption)
    | (apply Step.dataDrop; all_goals assumption))

/-- A step under the closed host is a step under every host. -/
theorem step_of_closed {P : Profile} {src : VHost H} {c c' : Config H}
    (h : Step P closedV c c') : Step P src c c' := by
  induction h with
  | pure hp => exact .pure hp
  | read hr => exact .read hr
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | callAddrHost _ _ _ hhost => exact hhost.elim
  | callAddrHostDiv _ _ _ hhost => exact hhost.elim
  | _ => restep

theorem steps_of_closed {P : Profile} {src : VHost H} {c c' : Config H}
    (h : Steps P closedV c c') : Steps P src c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_of_closed hs)

theorem diverges_of_closed {P : Profile} {src : VHost H} {c : Config H}
    (h : Diverges P closedV c) : Diverges P src c :=
  Silmaril.InfiniteTrace.map id (fun _ _ hs => step_of_closed hs) h

/-- A behaviour under the closed host is a behaviour under every host. -/
theorem behaviours_of_closed {P : Profile} {src : VHost H} {s : VStore H} {a : Nat}
    {vs : List VVal} :
    Silmaril.Wasm.V2.Execution.behaviours P closedV s a vs ⊆
      Silmaril.Wasm.V2.Execution.behaviours P src s a vs := by
  rintro b (⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨c', r, steps_of_closed hrun, hcode, rfl⟩
  · exact Or.inr ⟨rfl, diverges_of_closed hdiv⟩

end Silmaril.Proofs.Wasm.Models.V2Core
