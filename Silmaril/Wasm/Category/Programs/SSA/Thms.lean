module

public import Silmaril.Wasm.Category.Programs.SSA.Defs
public import Silmaril.Compile.Category.Valid

@[expose] public section

/-!
# The lambda-SSA dialect as a Wasm language: soundness

* `ssaToCore_beh`: a successful translation `ssaToCoreRun f = some p` has **exactly** the
  observations of `f` through the convention: every Core 3.0 behaviour of a typed invocation
  of `p` (every profile, divergence included) realises an SSA observation of `f`, and every SSA
  observation of `f` is realised (`Silmaril.Wasm.SSA.compileCore_spec`);
* `ssaToCore P`: the translation as a sound compiler (`Valid`);
* `ssaOptimize`: the lambda-SSA optimiser `optimizeSSA` as an optimisation of `ssaLang` (it keeps
  the signature and the outcomes, `optimizeSSA_iff`).

New.
-/

namespace Silmaril.Wasm.Category

open Silmaril.Compile.Category Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA

/-- Every Core observation of a compiled function realises an SSA observation. -/
theorem ssaToCore_sound_obs (P : Numerics.Profile) {f : SFunc} {s : Store Empty}
    (hs : compileCore? f = some s) {vs : List Val} {b : Behaviour Val}
    (hok : InvokeOk s 0 vs) (hb : b ∈ behaviours P Binaryen.closedHost s 0 vs) :
    ∃ o ∈ ssaLang.beh f, (ssaCoreConv P).R o (vs, b) := by
  obtain ⟨args, rfl, hargs, hbeh⟩ := compileCore_spec hs P hok
  have hb' : (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o) := by
    rw [hbeh] at hb
    exact hb
  rcases hb' with ⟨o, ho, rfl⟩ | ⟨rfl, hnone⟩
  · exact ⟨(args, some o), ⟨hargs, fun o' h' => Option.some.inj h' ▸ ho, nofun⟩, rfl, rfl⟩
  · exact ⟨(args, none), ⟨hargs, nofun, fun _ => hnone⟩, rfl, rfl⟩

/-- Every SSA observation of a function is realised by its compilation. -/
theorem ssaToCore_complete_obs (P : Numerics.Profile) {f : SFunc} {s : Store Empty}
    (hs : compileCore? f = some s) {args : List WVal} {ob : Option FOut}
    (ho : (args, ob) ∈ ssaLang.beh f) :
    InvokeOk s 0 (args.map WVal.toVal) ∧
      outBeh ob ∈ behaviours P Binaryen.closedHost s 0 (args.map WVal.toVal) := by
  obtain ⟨hargs, hsome, hnone⟩ := ho
  have hok : InvokeOk s 0 (args.map WVal.toVal) := compileCore_invokeOk hs hargs
  obtain ⟨args', hargs', -, hbeh⟩ := compileCore_spec hs P hok
  have he : args' = args := WVal.map_toVal_inj hargs'.symm
  refine ⟨hok, ?_⟩
  rw [hbeh, he]
  rcases ob with _ | o
  · exact .inr ⟨rfl, hnone rfl⟩
  · exact .inl ⟨o, hsome o rfl, rfl⟩

/-- **The translation to Core is exact through the convention**: the Core 3.0 observations of
the compiled function are exactly the realisations of the SSA observations. -/
theorem ssaToCore_beh (P : Numerics.Profile) {f : SFunc} {p : CoreFn}
    (h : ssaToCoreRun f = some p) :
    (coreFnLang P).beh p = {o' | ∃ o ∈ ssaLang.beh f, (ssaCoreConv P).R o o'} := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  ext ⟨vs, b⟩
  constructor
  · rintro ⟨hok, hb⟩
    exact ssaToCore_sound_obs P hs hok hb
  · rintro ⟨⟨args, ob⟩, ho, h₁, h₂⟩
    have hvs : vs = args.map WVal.toVal := h₁
    have hb : b = outBeh ob := h₂
    rw [hvs, hb]
    exact ssaToCore_complete_obs P hs ho

/-- **The translation of lambda-SSA functions to Core 3.0 as a sound compiler.** -/
noncomputable def ssaToCore (P : Numerics.Profile) : Compiler ssaLang (coreFnLang P) where
  conv := ssaCoreConv P
  run := ssaToCoreRun
  sound f p h := by
    refine (valid_iff_beh _ _ _).2 ⟨?_, ?_⟩
    · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
    · rw [ssaToCore_beh P h]
      exact fun _ ho => ho

/-- The lambda-SSA optimiser keeps the observations. -/
theorem optimizeSSA_beh (f : SFunc) : ssaLang.beh (optimizeSSA f) = ssaLang.beh f := by
  ext ⟨args, ob⟩
  have hrun : ∀ o, (optimizeSSA f).Run args o ↔ f.Run args o := fun o => optimizeSSA_iff
  show (args.map WVal.type = (optimizeSSA f).params ∧
      (∀ o, ob = some o → (optimizeSSA f).Run args o) ∧
      (ob = none → ∀ o, ¬ (optimizeSSA f).Run args o)) ↔
    (args.map WVal.type = f.params ∧ (∀ o, ob = some o → f.Run args o) ∧
      (ob = none → ∀ o, ¬ f.Run args o))
  simp only [hrun]
  rfl

/-- **The lambda-SSA optimiser as an optimisation of the dialect.** -/
def ssaOptimize : EndoPass ssaLang :=
  ⟨optimizeSSA, fun f => ⟨rfl, (optimizeSSA_beh f).le⟩⟩

end Silmaril.Wasm.Category
