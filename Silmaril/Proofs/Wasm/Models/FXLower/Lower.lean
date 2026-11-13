module

public import Silmaril.Proofs.Wasm.Models.FXLower.Handler

/-!
# Lowering `resume (cont.new (ref.func a))` to `call_ref`: soundness

* `behavioursFX_of_steps`: FX behaviours are closed under prefixing a run;
* `src_steps`: the source takes two FX steps (`cont.new` under `ctxt-instrs`, then `resume`) to
  the target code under a handler frame, with the continuation consumed;
* **`lower_sound`**: every Core behaviour of the target is an FX behaviour of the source.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **FX behaviours are closed under prefixing a run.** -/
theorem behavioursFX_of_steps {x y : ConfigFX H} (h : StepsFX P host fx x y) :
    behavioursFX P host fx y ⊆ behavioursFX P host fx x := by
  rintro b (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, h.trans hrun, hcode, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.of_steps h hdiv⟩

/-- The continuation `cont.new` allocates for function address `a`. -/
def contOf (a : Nat) (d : Silmaril.Wasm.Validation.DefType) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType d)]⟩

/-- The continuation store after the source consumed its continuation. -/
def kAfter (K : List (Option ContFX)) (a : Nat) (d : Silmaril.Wasm.Validation.DefType) :
    List (Option ContFX) :=
  (K ++ [some (contOf a d)]).set K.length none

/-- The plugged continuation is the target code. -/
theorem plug_contOf (a : Nat) (d : Silmaril.Wasm.Validation.DefType) (vs : List Val) :
    (contOf a d).plug (cvals vs) = (tgtCall a d vs).map .core := by
  simp [contOf, tgtCall, cvals]

/-- **The source runs to the target under a handler frame.** -/
theorem src_steps {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    StepsFX P host fx ⟨s, K, f, srcResume a ct hs vs⟩
      (underH (kAfter K a fi.type) hs' ⟨s, f, tgtCall a fi.type vs⟩) := by
  have h1 : StepFX P host fx ⟨s, K, f, srcResume a ct hs vs⟩
      ⟨s, K ++ [some (contOf a fi.type)], f,
        cvals vs ++ [.contRef K.length] ++ [.fx (.resume ct hs)]⟩ := by
    have h := StepFX.seq (vs := vs) (rest := [.fx (.resume ct hs)])
      (StepFX.contNew (P := P) (host := host) (fx := fx) (K := K) (f := f) (ct := ct) hf)
      (Or.inr (by simp))
    simpa [srcResume, contOf] using h
  have hk : (K ++ [some (contOf a fi.type)])[K.length]? = some (some (contOf a fi.type)) := by
    simp
  have h2 := StepFX.resume (P := P) (host := host) (fx := fx) (s := s) (f := f) (vs := vs)
    (ct := ct) hk hr
  have h2' : StepFX P host fx
      ⟨s, K ++ [some (contOf a fi.type)], f,
        cvals vs ++ [.contRef K.length] ++ [.fx (.resume ct hs)]⟩
      (underH (kAfter K a fi.type) hs' ⟨s, f, tgtCall a fi.type vs⟩) := by
    rw [List.append_assoc]
    unfold underH onHandler kAfter
    rw [← plug_contOf]
    exact h2
  exact (Relation.ReflTransGen.single h1).tail h2'

/-- **Soundness of the lowering**: every Core behaviour of `vs; ref.func a; call_ref` is an FX
behaviour of `vs; ref.func a; cont.new; resume`. -/
theorem lower_sound {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type vs⟩ ⊆
      behavioursFX P host fx ⟨s, K, f, srcResume a ct hs vs⟩ :=
  (behaviours_handler_sub _ hs' _).trans (behavioursFX_of_steps (src_steps hf hr))

end Silmaril.Proofs.Wasm.Models.FXLower
