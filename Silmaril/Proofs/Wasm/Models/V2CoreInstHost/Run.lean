module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstHost.Setup

/-!
# The 2.0 instantiation runs of `mI`

* `step_call_inv`: the only step at `call x` is `Step_read/call`;
* `inst_cases`: an instantiation run of `mI` at a store `s` is `call 0` under the allocated module
  instance, on a store `s'` with `s'.funcs = s.funcs` and `s'.tables = s.tables`;
* `behaviours_st`: at `st`, every behaviour of such a run is `diverges`: the start function is
  the host function, and `src` only diverges on a store without `ref.null extern`;
* `returns_stX`: at the ill-typed store `stX`, which has the same Core image, a run returns `[]`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstHost

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Proofs.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Execution (Admin Config Step Steps vals Result)

/-- An administrative instruction other than a value or `call`. -/
def nonValCall : Admin → Bool
  | .plain (.intConst _ _) | .plain (.floatConst _ _) | .plain (.vecConst _)
  | .plain (.refNull _) | .refFuncAddr _ | .refHostAddr _ | .plain (.call _) => false
  | _ => true

@[simp] theorem nonValCall_toAdmin (v : VVal) :
    nonValCall (Silmaril.Wasm.V2.Execution.Val.toAdmin v) = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

@[simp] theorem any_nonValCall_vals (vs : List VVal) : (vals vs).any nonValCall = false := by
  simp [vals]

theorem pure_not_call {P : Profile} {is is' : List Admin}
    (hp : Silmaril.Wasm.V2.Execution.PureStep P is is') (hb : is.any nonValCall = false) : False := by
  cases hp <;> simp [nonValCall, Silmaril.Wasm.V2.Execution.constI32] at hb

/-- What a step at `call x` must be. -/
def CallStep (c c' : Config Nat) (x : FuncIdx) : Prop :=
  ∃ a, c.frame.module.funcAddr? x = some a ∧ c' = ⟨c.store, c.frame, [.callAddr a]⟩

/-- A code whose instructions other than values and `call` exist cannot be `call x`. -/
theorem not_call_of_any {l : List Admin} {x : FuncIdx}
    (hc : l = [.plain (.call x)]) (hl : l.any nonValCall = true) : False := by
  rw [hc] at hl
  simp [nonValCall] at hl

/-- The only `Step_read` rule at `call x` is `call`. -/
theorem read_call_inv {s : VStore Nat} {f : Silmaril.Wasm.V2.Execution.Frame}
    {is is' : List Admin} (hr : Silmaril.Wasm.V2.Execution.ReadStep s f is is')
    {x : FuncIdx} (hc : is = [.plain (.call x)]) :
    CallStep ⟨s, f, is⟩ ⟨s, f, is'⟩ x := by
  cases hr with
  | @call y a hx =>
    have hx' : y = x := by simpa using hc
    exact ⟨a, hx' ▸ hx, rfl⟩
  | _ => exact (not_call_of_any hc (by simp [vals, nonValCall, Silmaril.Wasm.V2.Execution.constI32])).elim

/-- No step under a value prefix or before a suffix is at `call x`. -/
theorem ctxt_not_call {s s' : VStore Nat} {f f' : Silmaril.Wasm.V2.Execution.Frame}
    {P : Profile} {host : VHost Nat} {vs : List VVal} {is is' rest : List Admin}
    (hstep : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs ≠ [] ∨ rest ≠ [])
    {x : FuncIdx} (hc : vals vs ++ is ++ rest = [.plain (.call x)]) : False := by
  have hc' : vals vs ++ is ++ rest = vals [] ++ [.plain (.call x)] := by simpa [vals] using hc
  obtain ⟨hrest, vs₁, -, hvs⟩ := split_last hstep.not_allVals hc'
  have h0 : vs = [] := (List.append_eq_nil_iff.mp hvs.symm).1
  exact hne.elim (fun h => h h0) (fun h => h hrest)

/-- **Inversion at `call x`.** -/
theorem step_call_inv {P : Profile} {host : VHost Nat} {c c' : Config Nat}
    (h : Step P host c c') : ∀ {x}, c.code = [.plain (.call x)] → CallStep c c' x := by
  induction h with
  | pure hp =>
    intro x hc
    exact (pure_not_call hp (by simp only at hc; rw [hc]; rfl)).elim
  | read hr => exact fun hc => read_call_inv hr hc
  | ctxtInstrs hstep hne _ => exact fun hc => (ctxt_not_call hstep hne hc).elim
  | ctxtLabel _ _ => intro x hc; simp at hc
  | ctxtFrame _ _ => intro x hc; simp at hc
  | _ =>
    intro x hc
    exact (not_call_of_any hc (by simp [vals, nonValCall, Silmaril.Wasm.V2.Execution.constI32])).elim

/-- The imports: the host function at address `0`. -/
abbrev xasI : List Silmaril.Wasm.V2.Execution.ExternAddr := [.func 0]

/-- The module instance of `mI`. -/
def miI : Silmaril.Wasm.V2.Execution.ModuleInst := { types := [⟨[], []⟩], funcs := [0] }

theorem alloc_st : Silmaril.Wasm.V2.Execution.allocModule? st mI xasI [] [] = some (st, miI) := rfl

theorem alloc_stX : Silmaril.Wasm.V2.Execution.allocModule? stX mI xasI [] [] = some (stX, miI) :=
  rfl

/-- The instantiation configuration of `mI` at `s`. -/
def cI (s : VStore Nat) : Config Nat := ⟨s, { module := miI }, [.plain (.call ⟨0⟩)]⟩

/-- **The instantiation runs of `mI`** at a store whose allocation is `alloc_st`'s. -/
theorem inst_eq {P : Profile} {host : VHost Nat} {s : VStore Nat} {c : Config Nat}
    (ha : Silmaril.Wasm.V2.Execution.allocModule? s mI xasI [] [] = some (s, miI))
    (h : Silmaril.Wasm.V2.Execution.Instantiate P host s mI xasI c) : c = cI s := by
  obtain ⟨valsG, refsE, s', mi, hG, hE, hA, hc⟩ := h.run
  have hG' : valsG = [] := List.forall₂_nil_left_iff.mp hG
  have hE' : refsE = [] := List.forall₂_nil_left_iff.mp hE
  subst hG' hE'
  rw [ha] at hA
  cases hA
  rw [hc]
  rfl

/-- The configuration after `call 0`: the host function's `CALL_ADDR`. -/
def cA (s : VStore Nat) : Config Nat := ⟨s, { module := miI }, [.callAddr 0]⟩

/-! ## The ill-typed store: the run returns -/

/-- At `stX`, `mI` instantiates to `cI stX`. -/
theorem inst_stX (P : Profile) :
    Silmaril.Wasm.V2.Execution.Instantiate P src stX mI xasI (cI stX) where
  valid := ⟨_, _, mI_ok, .cons (.func (fi := fiH) rfl) .nil⟩
  bounded := by simp [mI]
  run := ⟨[], [], stX, miI, .nil, .nil, alloc_stX, rfl⟩

/-- **At `stX` the run returns `[]`**: the host finds `ref.null extern` in the table. -/
theorem returns_stX (P : Profile) :
    Behaviour.returns [] ∈ Silmaril.Wasm.V2.Execution.behavioursOf P src (cI stX) := by
  have h₁ : Step P src (cI stX) (cA stX) := .read (.call (a := 0) rfl)
  have h₂ : Step P src (cA stX) ⟨stX, { module := miI }, Result.toAdmin (.values [])⟩ :=
    .callAddrHost (vs := []) (fi := fiH) (h := 0) rfl rfl rfl (Or.inr ⟨stX_ext, rfl⟩)
  exact Silmaril.Wasm.V2.Execution.returns_mem_behavioursOf
    (Relation.ReflTransGen.tail (.single h₁) h₂) rfl

/-! ## The point's store: the run only diverges -/

theorem call_not_result (r : Result) : [Admin.plain (.call ⟨0⟩)] ≠ r.toAdmin := by
  intro h
  cases r with
  | values ws =>
    have hb := congrArg (fun l => List.all l Admin.isVal) h
    simp [Result.toAdmin, Admin.isVal, Admin.val?] at hb
  | trap => simp [Result.toAdmin] at h

/-- From `cI st`, the only step is `call 0`. -/
theorem step_cI {P : Profile} {c' : Config Nat} (h : Step P src (cI st) c') : c' = cA st := by
  obtain ⟨a, ha, rfl⟩ := step_call_inv h rfl
  have : a = 0 := by
    change some 0 = some a at ha
    exact (Option.some.inj ha).symm
  subst this
  rfl

/-- From `cA st`, the host only diverges: `st` has no `ref.null extern`. -/
theorem step_cA {P : Profile} {c' : Config Nat} (h : Step P src (cA st) c') : c' = cA st := by
  obtain ⟨fi, hf, pre, args, hvs, -, hcase⟩ := step_callAddr_inv (vs := []) h rfl
  change some fiH = some fi at hf
  cases hf
  rcases hcase with ⟨fn, hcode⟩ | ⟨hh, -, ⟨s', r, hr, -⟩ | ⟨-, heq⟩⟩
  · simp [fiH] at hcode
  · rcases hr with hr | ⟨hx, -⟩
    · cases hr
    · exact absurd hx st_noExt
  · exact heq

/-- Every run from `cI st` stays at `cI st` or `cA st`. -/
theorem steps_cI {P : Profile} {c' : Config Nat} (h : Steps P src (cI st) c') :
    c' = cI st ∨ c' = cA st := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | rfl
    · exact Or.inr (step_cI hs)
    · exact Or.inr (step_cA hs)

/-- **At `st` every behaviour of the run is `diverges`.** -/
theorem behaviours_st (P : Profile) {b : Behaviour VVal}
    (hb : b ∈ Silmaril.Wasm.V2.Execution.behavioursOf P src (cI st)) : b = .diverges := by
  rcases hb with ⟨c', r, hrun, hcode, -⟩ | ⟨rfl, -⟩
  · rcases steps_cI hrun with rfl | rfl
    · exact absurd hcode (call_not_result r)
    · have hn := callAddr_not_result (vs := []) (a := 0) r
      exact absurd hcode hn
  · rfl
