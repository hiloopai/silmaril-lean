module

public import Silmaril.Wasm.Component.Lime1RT.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Prepare

/-!
# The instance store of a Lime1 module is of Lime1

* `evalGlobals?_funcs`, `evalExprs?_funcs`, `evalExprss?_funcs`: constant evaluation (a run of
  host-free Core steps, `Steps.funcs_eq`) keeps the function instances;
* `allocModule?_funcs`, `prepare?_funcs`, **`prepareE?_funcs`**: allocation and instantiation
  append to the function instances only Wasm functions of the module (`NewOf`);
* `storeIn_append`, `body_of_inFeat`, **`prepareE?_storeIn`**: instantiating a module of `S`
  keeps a store of `S` (`Rt.StoreIn S`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1RT.Inst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models

variable {H : Type}

/-- Constant evaluation of the global initialisers keeps the function instances. -/
theorem evalGlobals?_funcs :
    ∀ {s : Store H} {f : Frame} {gs : List Validation.CGlobalType} {es : List Expr}
      {s' : Store H} {f' : Frame} {vs : List Val},
      evalGlobals? evalConst? s f gs es = some (s', f', vs) → s'.funcs = s.funcs := by
  intro s f gs es s' f' vs h
  have hE := evalGlobals?_sound (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.Det.noHost) evalConst?_evalSound h
  clear h
  induction hE with
  | nil => rfl
  | cons he _ ih =>
    exact ih.trans (Silmaril.Wasm.Component.Engine.Core3.Typed.Steps.funcs_eq he)

/-- A run of constant reference initialisers keeps the function instances. -/
theorem evalExprs_funcs {P : Numerics.Profile} {s : Store H} {f : Frame} {es : List Expr}
    {s' : Store H} {f' : Frame} {rs : List Ref}
    (hE : EvalExprs P SingleThreaded.Det.noHost s f es s' f' rs) : s'.funcs = s.funcs := by
  induction hE with
  | nil => rfl
  | cons he _ ih => exact ih.trans (Silmaril.Wasm.Component.Engine.Core3.Typed.Steps.funcs_eq he)

/-- Constant evaluation of reference initialisers keeps the function instances. -/
theorem evalExprs?_funcs {s : Store H} {f : Frame} {es : List Expr} {s' : Store H} {f' : Frame}
    {rs : List Ref} (h : evalExprs? evalConst? s f es = some (s', f', rs)) :
    s'.funcs = s.funcs :=
  evalExprs_funcs (evalExprs?_sound (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.Det.noHost) evalConst?_evalSound h)

/-- Constant evaluation of element segments keeps the function instances. -/
theorem evalExprss?_funcs {s : Store H} {f : Frame} {ess : List (List Expr)} {s' : Store H}
    {f' : Frame} {rss : List (List Ref)}
    (h : evalExprss? evalConst? s f ess = some (s', f', rss)) : s'.funcs = s.funcs := by
  have hE := evalExprss?_sound (P := SingleThreaded.profile SingleThreaded.neverFail)
    (host := SingleThreaded.Det.noHost) evalConst?_evalSound h
  clear h
  induction hE with
  | nil => rfl
  | cons he _ ih => exact ih.trans (evalExprs_funcs he)

/-- The new function instances of a store, each a Wasm function of `m` or a host function. -/
def NewOf (m : Module) (new : List (FuncInst H)) : Prop :=
  ∀ fi ∈ new, ∀ fn : Func, fi.code = .wasm fn → fn ∈ m.funcs

/-- `$allocmodule` appends one Wasm function instance per module function. -/
theorem allocModule?_funcs {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s', mi)) :
    ∃ new, s'.funcs = s.funcs ++ new ∧ NewOf m new := by
  obtain ⟨_, funcTypes, _, -, -, -, -, rfl⟩ := allocModule?_inv h
  refine ⟨(funcTypes.zip m.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩, rfl, ?_⟩
  intro fi hfi fn hfn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfi
  cases hfn
  exact (List.of_mem_zip hp).2

set_option linter.unusedTactic false in
/-- **Allocation appends the module's functions**: after `prepare?`, the function instances are
those of the input store followed by Wasm functions of the module. -/
theorem prepare?_funcs {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    {st : Option FuncIdx} (h : prepare? evalConst? s m xas = some (c, st)) :
    ∃ new, c.store.funcs = s.funcs ++ new ∧ NewOf m new := by
  unfold prepare? at h
  split at h <;> try cases h
  split at h <;> try cases h
  rename_i s₁ f₁ valsG hG
  split at h <;> try cases h
  rename_i s₂ f₂ refsT hT
  split at h <;> try cases h
  rename_i s₃ f₃ refsE hE
  split at h <;> try cases h
  rename_i s₄ mi hM
  obtain ⟨new, hnew, hm⟩ : ∃ new, s₄.funcs = s₃.funcs ++ new ∧ NewOf m new :=
    allocModule?_funcs hM
  have h₃ : s₃.funcs = s.funcs := by
    rw [evalExprss?_funcs hE, evalExprs?_funcs hT, evalGlobals?_funcs hG]
  exact ⟨new, h₃ ▸ hnew, hm⟩

/-- **Instantiation appends the module's functions**: after `prepareE?`, the function instances
are those of the input store followed by Wasm functions of the module. -/
theorem prepareE?_funcs {s s' : Store H} {m : Module} {xas : List ExternAddr} {i : ModuleInst}
    {st : Option Nat}
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', i, st)) :
    ∃ new, s'.funcs = s.funcs ++ new ∧ NewOf m new := by
  obtain ⟨-, f', st₀, -, -, hi, -, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_inv h
  obtain ⟨s₁, f₁, vs, c, hg, hp, hS⟩ := instantiateOnce?_steps
    (P := SingleThreaded.profile SingleThreaded.neverFail) (host := fun _ _ _ _ => False) hi
  obtain ⟨new, hnew, hm⟩ := prepare?_funcs hp
  refine ⟨new, ?_, hm⟩
  rw [show s'.funcs = c.store.funcs from
    Silmaril.Wasm.Component.Engine.Core3.Typed.Steps.funcs_eq hS, hnew, evalGlobals?_funcs hg]


/-! ## The runtime invariant of the instance store -/

/-- Appending functions whose Wasm bodies are of `S` keeps a store of `S`. -/
theorem storeIn_append {S : FeatureSet} {s s' : Store H} {new : List (FuncInst H)}
    (hs : Rt.StoreIn S s) (he : s'.funcs = s.funcs ++ new)
    (hn : ∀ fi ∈ new, ∀ fn : Func, fi.code = .wasm fn → Instr.insInFeatB S fn.body = true) :
    Rt.StoreIn S s' := by
  intro a fi fn ha hc
  rw [he] at ha
  rcases Nat.lt_or_ge a s.funcs.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at ha
    exact hs a fi fn ha hc
  · rw [List.getElem?_append_right hge] at ha
    exact hn fi (List.mem_of_getElem? ha) fn hc

/-- The bodies of the functions of a module of `S` are of `S`. -/
theorem body_of_inFeat {S : FeatureSet} {m : Module} (hm : Module.InFeat S m) {fn : Func}
    (hfn : fn ∈ m.funcs) : Instr.insInFeatB S fn.body = true := by
  have h : Module.inFeatB S m = true := hm
  simp only [Module.inFeatB, Bool.and_eq_true, List.all_eq_true] at h
  have hf := h.1.1.1.1.2 fn hfn
  simp only [Func.inFeatB, Bool.and_eq_true] at hf
  exact hf.2

/-- **Instantiating a module of `S` keeps a store of `S`.** -/
theorem prepareE?_storeIn {S : FeatureSet} {s s' : Store H} {m : Module}
    {xas : List ExternAddr} {i : ModuleInst} {st : Option Nat} (hm : Module.InFeat S m)
    (hs : Rt.StoreIn S s)
    (h : Silmaril.Wasm.Component.Engine.Core3.prepareE? s m xas = some (s', i, st)) :
    Rt.StoreIn S s' := by
  obtain ⟨new, he, hn⟩ := prepareE?_funcs h
  exact storeIn_append hs he fun fi hfi fn hc => body_of_inFeat hm (hn fi hfi fn hc)

end Silmaril.Proofs.Wasm.Component.Lime1RT.Inst
