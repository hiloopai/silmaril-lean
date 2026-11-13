module

public import Silmaril.Wasm.Component.Reference.Start.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusRef
public import Silmaril.Proofs.Wasm.Component.Reference.StartIR

/-!
# A litmus component with a start function

`startS` exports `get() -> u32` over `startCore3`, whose start function stores `42` in a mutable
global that `get` reads.

* `startS_instS` (`Simple.InstS`, by kernel evaluation of a summary of validation and
  instantiation: the start function is at address `0`, `get` at address `1`);
* `startS_valid` (the validator accepts `startS.toRef`) and `start_ref`: over `core3 neverFail`
  the reference machine instantiates `startS.toRef`, running the start function, and `get()`
  returns `42` (closed run of the copied drivers);
* `start_sound`: the instance of `simple_sound_start`: every reference behaviour of `get()` is
  matched by the IR over `modSemS P`, for every profile and component choice profile.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Reference.Litmus
open Silmaril.Wasm.Component.Reference.Core3Adder (emb first)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game

/-- The function type of `get`. -/
abbrev getFn : FnType := ⟨[], [.num (.int .i32)]⟩

/-- The checks on the instantiation of `startCore3`. -/
def startBody : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx) → Bool
  | some (s, f, some x) => exportFuncAddrs f.module == [1] && f.module.funcs[x.toNat]? == some 0 &&
      (s.funcs[1]?.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == some (some getFn)
  | _ => false

/-- The Boolean summary of the validation and instantiation of `startCore3`. -/
def startSummary : Bool :=
  ((Silmaril.Wasm.Validation.validate? startCore3).map (·.imports.length) == some 0) &&
    startBody (instantiateOnce? (importStore []) startCore3 [])

theorem startSummary_ok : startSummary = true := by decide +kernel

/-- The store of the instance of `startCore3` before its start function. -/
def startStore : Store Nat :=
  match instantiateOnce? (importStore []) startCore3 [] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `startCore3` before its start function. -/
def startInst : ScalarInstance where
  imports := []
  exports := [getFn]
  addrs := [1]
  store := startStore

theorem startBody_eq {o : Option (Store Nat × Frame × Option Silmaril.Wasm.FuncIdx)}
    (h : startBody o = true) :
    ∃ s f x, o = some (s, f, some x) ∧ exportFuncAddrs f.module = [1] ∧
      f.module.funcs[x.toNat]? = some 0 ∧
      (s.funcs[1]?.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = some (some getFn) := by
  match o, h with
  | some (s, f, some x), h =>
    have h' : (exportFuncAddrs f.module = [1] ∧ f.module.funcs[x.toNat]? = some 0) ∧
        (s.funcs[1]?.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
          some (some getFn) := by
      simpa only [startBody, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨s, f, x, rfl, h'.1.1, h'.1.2, h'.2⟩

/-- **`startInst` is the instance of `startMod` before its start function, at address `0`.** -/
theorem startMod_isInstS : startMod.IsInstS startInst (some 0) := by
  have h' : (Silmaril.Wasm.Validation.validate? startCore3).map (·.imports.length) = some 0 ∧
      startBody (instantiateOnce? (importStore []) startCore3 []) = true := by
    simpa only [startSummary, Bool.and_eq_true, beq_iff_eq] using startSummary_ok
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  have himp : mt.imports = [] := List.length_eq_zero_iff.mp hlen
  obtain ⟨s, f, x, hrun, hfa, hx, hty⟩ := startBody_eq h'.2
  have hs : startStore = s := by simp only [startStore, hrun]
  obtain ⟨fi, hfi, hfty⟩ : ∃ fi, s.funcs[1]? = some fi ∧ FnType.ofDefType? fi.type = some getFn := by
    cases hf : s.funcs[1]? with
    | none => rw [hf] at hty; cases hty
    | some fi =>
      rw [hf] at hty
      exact ⟨fi, rfl, Option.some.inj hty⟩
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, some x, ?_, hfa, .some hx⟩
    rw [himp]
    show instantiateOnce? (importStore []) startCore3 [] = some (startStore, f, some x)
    rw [hs]
    exact hrun
  · refine .cons ⟨fi, ?_, hfty⟩ .nil
    show startStore.funcs[1]? = some fi
    rw [hs]
    exact hfi

theorem startS_instS : startS.InstS := ⟨⟨startInst, some 0, startMod_isInstS⟩, rfl⟩

theorem startS_good : startS.Good :=
  ⟨by decide, by intro x hx; simp only [startS, List.mem_singleton] at hx; subst hx; exact ⟨"get", rfl⟩⟩

theorem startS_floatFree : startS.FloatFree := by
  intro x hx
  simp only [startS, List.mem_singleton] at hx
  subst hx
  exact ⟨rfl, rfl⟩

theorem startS_arity : startS.Arity := by
  intro x hx
  simp only [startS, List.mem_singleton] at hx
  subst hx
  decide

theorem startS_valid : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 startS.toRef = .ok ct :=
  exists_of_accepts (by decide +kernel)

/-- **The reference machine runs the start function**: over `core3 neverFail`, `get()` after
instantiation returns `42`. -/
theorem start_ref : Outcome.returns (some [toRefVal (.u32 42)]) ∈
    exportBehaviours first.prof (Silmaril.Wasm.Component.Reference.Host.ofEmbedder emb) ()
      startS.toRef [] "get" [] :=
  returns_of_summary (by decide +kernel)

/-- **Soundness for the start litmus**: every reference behaviour of `get()` is matched by the
IR over `modSemS P`. -/
theorem start_sound (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) :
    ∀ b ∈ exportBehaviours prof (refHost P) () startS.toRef [] "get" [],
      IRObs (startS.toComp.den (modSemS P)) ⟨0, by decide⟩ [] b :=
  simple_sound_start P prof startS startS_good startS_floatFree startS_instS startS_arity
    ⟨0, by decide⟩ [] rfl

end Silmaril.Proofs.Wasm.Component.Reference.Litmus
