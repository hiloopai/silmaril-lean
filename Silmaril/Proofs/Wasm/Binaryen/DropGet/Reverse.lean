module

public import Silmaril.Proofs.Wasm.Binaryen.DropGet.Sound
public import Silmaril.Wasm.Binaryen.Deferred.Thms
public import Silmaril.Wasm.Binaryen.CodeSimTyped
public import Silmaril.Wasm.Binaryen.ConstBranchSim
public import Silmaril.Wasm.Execution.Core.Sim.TypedLocalBounds

@[expose] public section

/-! # Dropped local reads: the typed reverse simulation and soundness at every profile

The result `nop` is on the **left**. Its step is matched by the original
`local.get x; drop`, which needs the local `x` to hold a value. That is not a
property of the code alone (an untyped frame may lack `x`, or hold an unset
non-defaultable local), so this direction is a silmaril `TypedBaseSim`: the right
(original) configuration is typed in its active context, and `CtxOk.set` turns the
typing of `local.get x` into a value of `x` in the actual frame
(`readable_of_contextTyped`). Silmaril's `exportRefines_of_typedBodiesRel` supplies
the guard from invocation typing at the same arbitrary numerical profile. With the
original-on-the-left `dgBaseSim` (`Sound.lean`, already profile-generic) this gives
exact export equivalence at every numerical profile, with no determinism argument.
-/

namespace Silmaril.Proofs.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.DropGet

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Runtime base pairs of the reverse simulation: the result on the left. -/
inductive dgRB : List Admin → List Admin → Prop where
  | mk (x : LocalIdx) : dgRB [.plain .nop] [.plain (.localGet x), .plain .drop]

/-- A typed active `local.get x` reads a value from the actual frame. -/
theorem readable_of_contextTyped {t : Store H} {f : Frame} {vs : List Val} {x : LocalIdx}
    {rest : List Admin} (h : ContextTyped ⟨t, f, vals vs ++ .plain (.localGet x) :: rest⟩) :
    ∃ v, f.local? x = some (some v) := by
  obtain ⟨C, it, _, _, hc, ha⟩ := h.active_admin_typed
  obtain ⟨ty, hx, _⟩ := ha.plain_inv_ne.localGet_invVar
  exact hc.set _ _ hx

/-- The original's `local.get x; drop` runs to its continuation. -/
theorem get_drop_steps {host : HostSemantics H} {t : Store H} {f : Frame} {vs : List Val}
    {v : Val} {x : LocalIdx} {rest' : List Admin} (hv : f.local? x = some (some v)) :
    Relation.TransGen (Step P host)
      ⟨t, f, vals vs ++ [.plain (.localGet x), .plain .drop] ++ rest'⟩ ⟨t, f, vals vs ++ rest'⟩ := by
  have h₁ : Step P host ⟨t, f, vals vs ++ [.plain (.localGet x)] ++ (.plain .drop :: rest')⟩
      ⟨t, f, vals vs ++ [v.toAdmin] ++ (.plain .drop :: rest')⟩ :=
    (Deferred.Forced.get t f vs x v (.plain .drop :: rest') hv).step
  have h₂ : Step P host ⟨t, f, vals vs ++ [v.toAdmin, .plain .drop] ++ rest'⟩
      ⟨t, f, vals vs ++ [] ++ rest'⟩ :=
    Step.append_right (Step.vals_left
      (Step.parametric (P := P) (host := host) (s := t) (f := f) (ParametricStep.drop v)) vs)
      rest'
  exact .tail (.single (by simpa using h₁)) (by simpa using h₂)

/-- A `nop` after values is removed, leaving store and frame unchanged. -/
theorem nop_step_inv {host : HostSemantics H} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {rest es' : List Admin}
    (h : Step P host ⟨s, f, vals vs ++ .plain .nop :: rest⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs ++ rest := by
  obtain ⟨pre, args, c₀, hV, hh, he⟩ := SimplifyLocalsLite.inert_head_inv rfl (by simp) rfl h
  obtain ⟨hargs, hc₀⟩ : args = [] ∧ c₀ = ⟨s, f, []⟩ := ConstBranch.head_nop hh
  have hpre : vs = pre := by rw [hV, hargs, List.append_nil]
  have hparts : s' = s ∧ f' = f ∧ es' = vals pre ++ rest := by
    simpa only [hc₀, Config.mk.injEq, List.append_nil] using he
  rw [hpre]
  exact hparts

theorem dgReverseFacts {F : FuncInst H → FuncInst H → Prop} :
    BaseFacts P closedHost F (fun a b => dgBI b a) dgRB where
  src := by
    intro x y h
    cases h with
    | mk x => exact .mk x
  exit := by
    intro s t f vs us x y k j hst hxy hk he
    exfalso
    cases hxy with
    | mk x =>
      exact GuardSim.not_exit (W := vs) (e₀ := .plain .nop) (x' := []) rfl (by simp) (by simp)
        (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) hk (by simpa using he)
  values := by
    intro s t f vs us x y hst hxy hx
    exfalso
    have hall : ∀ a ∈ x, a.val? ≠ none := by
      rw [hx]; intro a ha; exact SingleThreaded.Det.mem_vals ha
    cases hxy with
    | mk x => exact hall (.plain .nop) (by simp) rfl

/-- **The typed reverse simulation**: the original simulates the result whenever the
original is typed, at every numerical profile. -/
theorem dgReverseTypedSim {F : FuncInst H → FuncInst H → Prop} :
    TypedBaseSim P F (fun a b => dgBI b a) dgRB where
  facts := dgReverseFacts
  step := by
    intro s t s' f f' vs x y rest rest' es' hst hxy hrest htyped hstep
    cases hxy with
    | mk x =>
      have hs : Step P (fun _ _ _ _ => False) ⟨s, f, vals vs ++ .plain .nop :: rest⟩
          ⟨s', f', es'⟩ := by
        simpa using hstep
      have ht : ContextTyped ⟨t, f, vals vs ++ .plain (.localGet x) :: (.plain .drop :: rest')⟩ := by
        simpa using htyped
      obtain ⟨v, hv⟩ : ∃ v, f.local? x = some (some v) := readable_of_contextTyped ht
      obtain ⟨hs₁, hf₁, he₁⟩ : s' = s ∧ f' = f ∧ es' = vals vs ++ rest := nop_step_inv hs
      rw [hs₁, hf₁, he₁]
      exact ⟨t, vals vs ++ rest', Or.inl (get_drop_steps hv), hst,
        (AdminsRel.refl _).append hrest⟩

/-- The raw rewrite is exactly export-equivalent at every numerical profile. -/
theorem dropGet_sound_any {m : BModule} (hm : m.Ok) (hm' : (dropGet m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (dropGet m).lower m.lower :=
  ⟨exportRefines_of_typedBodiesRel dgReverseTypedSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (dropGet_bodiesRel m).flip hm' hm,
    (exportRefines_of_bodiesRel dgBaseSim
      (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
      (dropGet_bodiesRel m) hm hm').mono fun _ _ h => h.symm⟩

/-- The checked stage keeps validity and is exactly export-equivalent at every
numerical profile; its validator fallback is the identity. -/
theorem dropGetChecked_sound_any {m : BModule} (hm : m.Ok) :
    (dropGetChecked m).Ok ∧ ExportEquiv (· = ·) P (closedHost (H := H))
      (dropGetChecked m).lower m.lower := by
  unfold dropGetChecked
  dsimp only
  split
  · next h => exact ⟨Exe.validOk_sound h, dropGet_sound_any hm (Exe.validOk_sound h)⟩
  · exact ⟨hm, ExportRefines.refl (R := fun b b' => b = b') (fun _ => rfl) _,
      ExportRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) _⟩

end Silmaril.Proofs.Wasm.Binaryen.DropGet
