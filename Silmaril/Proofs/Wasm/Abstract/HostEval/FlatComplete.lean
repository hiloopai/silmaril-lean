module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Backward

/-!
# Completeness of checked flat instructions (proofs)

`flat_complete` (deterministic profile, any host): a Core run of a checked, typed flat
instruction `vals stk.reverse ++ [plain i]` to a stuck end `c` with final form `oc` is the
native `evalFlat` result: `evalFlat s f stk i = some (c.store, c.frame, fl)` with
`FlowMatch fl oc`. From typed progress (`Interp.evalFlat_progressH`) and `back_flat`.

`ends_split`, `outcome_ends_unique`: a code has at most one final form (`Outcome.Ends`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)

variable {H : Type} {host : HostSemantics H}

/-- The non-normal final forms, as a value prefix and a non-value head. -/
theorem ends_split {o : Outcome} {c : List Admin} (h : o.Ends c) (hn : ∀ vs, o ≠ .normal vs) :
    ∃ ws d rest, d.val? = none ∧ c = vals ws ++ d :: rest ∧
      ((∃ x : LabelIdx, d = .plain (.br x) ∧ o = .br x.toNat ws) ∨
        (d = .plain .return_ ∧ o = .ret ws) ∨ (d = .trap ∧ o = .trap) ∨
        (∃ a, d = .plain .throwRef ∧ ws = [.ref (.exn a)] ∧ o = .throw a) ∨
        (∃ vs a, d.IsReturnCallRef ∧ ws = vs ++ [.ref (.func a)] ∧ o = .tail vs a d) ∨
        (∃ vs, d.IsReturnCallRef ∧ ws = vs ++ [.ref .null] ∧ o = .tailNull vs d)) := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩ | ⟨vs, r⟩
  · exact (hn vs rfl).elim
  · obtain ⟨x, rest, rfl, h⟩ := h
    exact ⟨vs, _, rest, rfl, h, .inl ⟨x, rfl, rfl⟩⟩
  · obtain ⟨rest, h⟩ := h
    exact ⟨vs, _, rest, rfl, h, .inr (.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨[], _, [], rfl, h, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨[.ref (.exn a)], _, [], rfl, h, .inr (.inr (.inr (.inl ⟨a, rfl, rfl, rfl⟩)))⟩
  · obtain ⟨hr, rest, h⟩ := h
    exact ⟨vs ++ [.ref (.func a)], r, rest, Admin.val?_of_isReturnCallRef hr,
      by simpa [Val.toAdmin] using h,
      .inr (.inr (.inr (.inr (.inl ⟨vs, a, hr, rfl, rfl⟩))))⟩
  · obtain ⟨hr, rest, h⟩ := h
    exact ⟨vs ++ [.ref .null], r, rest, Admin.val?_of_isReturnCallRef hr,
      by simpa [Val.toAdmin] using h,
      .inr (.inr (.inr (.inr (.inr ⟨vs, hr, rfl, rfl⟩))))⟩

/-- A code has at most one final form. -/
theorem outcome_ends_unique {o o' : Outcome} {c : List Admin} (h : o.Ends c) (h' : o'.Ends c) :
    o = o' := by
  by_cases hn : ∃ vs, o = .normal vs
  · obtain ⟨vs, rfl⟩ := hn
    exact (ends_vals (show o'.Ends (vals vs) from h ▸ h')).symm
  by_cases hn' : ∃ vs, o' = .normal vs
  · obtain ⟨vs, rfl⟩ := hn'
    exact ends_vals (show o.Ends (vals vs) from h' ▸ h)
  simp only [not_exists] at hn hn'
  obtain ⟨ws, d, rest, hd, rfl, k⟩ := ends_split h hn
  obtain ⟨ws', d', rest', hd', he, k'⟩ := ends_split h' hn'
  obtain ⟨rfl, rfl, -⟩ := SingleThreaded.vals_append_cons_inj hd hd' he
  rcases k with ⟨x, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, rfl, rfl, rfl⟩ |
      ⟨vs, a, hr, rfl, rfl⟩ | ⟨vs, hr, rfl, rfl⟩ <;>
    rcases k' with ⟨x', hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩ | ⟨a', hx, hw, rfl⟩ |
      ⟨vs', a', hr', hw, rfl⟩ | ⟨vs', hr', hw, rfl⟩ <;>
    simp_all [Admin.IsReturnCallRef]

theorem flat_complete {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame} {stk : List Val}
    {i : Instr} {c : Config H} {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat}
    {labels : List Nat} {o₁ : Option Nat} {oc : Outcome} (hi : ∀ x, i ≠ .call x)
    (hc : Interp.flatChk F mi f.locals.length ret labels stk.length i = some o₁)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ [.plain i]⟩)
    (h : Steps (SingleThreaded.profile o) host ⟨s, f, vals stk.reverse ++ [.plain i]⟩ c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') (he : oc.Ends c.code) :
    ∃ fl, Binaryen.evalFlat s f stk i = some (c.store, c.frame, fl) ∧ Interp.FlowMatch fl oc := by
  obtain ⟨⟨s₂, f₂, fl⟩, hflat⟩ := Interp.evalFlat_progressH (rest := []) hc hi ht
  obtain ⟨n, hn⟩ := stepsN_of_steps h
  obtain ⟨hnorm, habr⟩ := back_flat (rest := []) hi hc hflat hn hend
  by_cases hN : fl.IsNormal
  · rcases fl with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hN
    obtain ⟨m, -, hm⟩ := hnorm stk₂ rfl
    have hstuck : ∀ c', ¬ Step (SingleThreaded.profile o) host ⟨s₂, f₂, vals stk₂.reverse⟩ c' :=
      fun _ => Sim.Step.not_vals
    have hc' := stepsN_of_stuck hstuck (by simpa using hm)
    subst hc'
    obtain rfl := ends_vals he
    exact ⟨_, hflat, rfl⟩
  · obtain ⟨oc', he', hst, hfr, hm⟩ := habr hN
    dsimp only at hst hfr
    obtain rfl := outcome_ends_unique he he'
    rcases c with ⟨cs, cf, cc⟩
    dsimp only at hst hfr
    subst hst hfr
    exact ⟨fl, hflat, hm⟩

end Silmaril.Proofs.Wasm.Abstract.HostEval
