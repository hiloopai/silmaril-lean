module

public import Silmaril.Wasm.SSA.Native.Defs
public import Silmaril.Wasm.SSA.Pipeline.Thms
public import Silmaril.Wasm.SSA.Checked.Thms
import Silmaril.Proofs.Wasm.SSA.Native.FwdRun
import Silmaril.Proofs.Wasm.SSA.Native.BwdRun
import Silmaril.Proofs.Wasm.SSA.Native.Outcome

/-!
# Native adequacy and the optimiser at the Binaryen level

* `native_adequate`: for an arity-checked fragment function (`FragFunc.native`)
  recognised from a folded body `bs`, and arguments of the parameter types,
  the terminating outcomes of the fragment semantics are exactly those of
  silmaril's native Binaryen interpreter (`Binaryen.Eval`) on `bs`, from the
  frame of the arguments and zero-initialised locals, in any store and module
  instance (the store is never changed). This is the adequacy
  statement for the checked sub-fragment, with the arity check in place of
  Core validation; it excludes the conversion operators, which the native
  interpreter does not implement.
* `optimizeFuncCertified_spec`: the validator-guarded, arity-guarded
  replacement is valid in its module and equivalent at both levels.
* `native_outcome`: every native result of an arity-checked body has a call outcome
  (`flowOut`) that the function reaches; the interpreter never ends such a body with an
  unobservable flow.
* `optimizeFuncNative?_spec`: the guarded optimiser's source and result are both recognised
  and arity-checked, with the same parameters and result and equivalent runs.
* `optimizeFuncNative?_equiv`: when the arity-guarded optimiser returns `bf'`
  for `bf`, both bodies have the same `Binaryen.Eval` outcomes (`nativeOut`),
  each from its own declared locals.

Silmaril does not prove its native interpreter adequate for Core small-step execution (its
`FwdSim`/`BwdSim` obligations in `Binaryen/AdequacyReduce` are open upstream); Silmaril proves it
for arity-checked native stores (`Silmaril.Wasm.Interp.native_adequacy`), and
`Silmaril.Wasm.SSA.CoreCert` combines the two for invocations of the optimised function. No
`ExportEquiv` statement follows here.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

/-- Terminating outcomes of a function body under silmaril's native interpreter. -/
def nativeOut {H : Type} (s : Store H) (mi : ModuleInst) (f : FragFunc) (bs : List BExpr)
    (args : List WVal) (o : FOut) : Prop :=
  ∃ (s' : Store H) (fr : Frame) (fl : Flow),
    Binaryen.Eval s (frameOf mi (f.initLocals args)) [] bs (s', fr, fl) ∧ flowOut f.result fl = some o

/-- **Native adequacy** for arity-checked functions. -/
theorem native_adequate {H : Type} (s : Store H) (mi : ModuleInst) {f : FragFunc}
    {bs : List BExpr} (hb : ofBExprs? bs = some f.body) (hn : f.native = true)
    {args : List WVal} (hty : args.map WVal.type = f.params) (o : FOut) :
    f.Run args o ↔ nativeOut s mi f bs args o := by
  constructor
  · intro h
    obtain ⟨fr, fl, he, ho⟩ := Silmaril.Proofs.Wasm.SSA.Native.native_forward s mi hb hn h
    exact ⟨s, fr, fl, he, ho⟩
  · rintro ⟨s', fr, fl, he, ho⟩
    exact Silmaril.Proofs.Wasm.SSA.Native.Bwd.native_backward hb hn hty he ho

theorem ofBFunc?_body {ft : FuncType} {bf : BFunc} {f : FragFunc} (h : ofBFunc? ft bf = some f) :
    ofBExprs? bf.body = some f.body := by
  obtain ⟨params, results⟩ := ft
  rcases results with _ | ⟨t, _ | ⟨t₂, rest⟩⟩ <;>
    simp only [ofBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
  · obtain ⟨_, _, _, _, _, _, b, hb, rfl⟩ := h; exact hb
  · obtain ⟨_, _, _, _, _, _, b, hb, rfl⟩ := h; exact hb
  · simp at h

theorem toBFunc?_body {ty : TypeIdx} {g : FragFunc} {bf : BFunc} (h : toBFunc? ty g = some bf) :
    ofBExprs? bf.body = some g.body := by
  simp only [toBFunc?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact ofBExprs?_toBExprs? hb

/-- The guarded optimiser succeeds exactly through its four steps: recognise,
check nativeness, optimise, check nativeness again and lower. -/
private theorem optimizeFuncNative?_inv {ft : FuncType} {bf bf' : BFunc}
    (ho : optimizeFuncNative? ft bf = some bf') :
    ∃ f g, ofBFunc? ft bf = some f ∧ f.native = true ∧ optimize? f = some g ∧
      g.native = true ∧ toBFunc? bf.type g = some bf' := by
  have ho' : ∃ f, ofBFunc? ft bf = some f ∧ ∃ u, guard (f.native = true) = some u ∧
      ∃ g, optimize? f = some g ∧ ∃ v, guard (g.native = true) = some v ∧
        toBFunc? bf.type g = some bf' := by
    simpa only [optimizeFuncNative?, Option.bind_eq_bind, Option.bind_eq_some_iff] using ho
  obtain ⟨f, hf, u, hu, g, hg, v, hv, hb⟩ := ho'
  have hfn : f.native = true := by
    by_contra hc; simp [guard, hc] at hu
  have hgn : g.native = true := by
    by_contra hc; simp [guard, hc] at hv
  exact ⟨f, g, hf, hfn, hg, hgn, hb⟩

/-- **Every native result of an arity-checked body is observable**, and the function runs to
its outcome. -/
theorem native_outcome {H : Type} {s : Store H} {mi : ModuleInst} {f : FragFunc}
    {bs : List BExpr} (hb : ofBExprs? bs = some f.body) (hn : f.native = true)
    {args : List WVal} (hty : args.map WVal.type = f.params) {s' : Store H} {fr : Frame}
    {fl : Flow} (h : Binaryen.Eval s (frameOf mi (f.initLocals args)) [] bs (s', fr, fl)) :
    ∃ o, flowOut f.result fl = some o ∧ f.Run args o :=
  Silmaril.Proofs.Wasm.SSA.Native.Bwd.native_outcome hb hn hty h

/-- The arity-guarded optimiser: both functions are recognised at the source's type and pass the
arity check, with the same parameters and result, and they are equivalent in the fragment
semantics. -/
theorem optimizeFuncNative?_spec {ft : FuncType} {bf bf' : BFunc}
    (ho : optimizeFuncNative? ft bf = some bf') :
    ∃ f g, ofBFunc? ft bf = some f ∧ f.native = true ∧ ofBFunc? ft bf' = some g ∧
      g.native = true ∧ g.params = f.params ∧ g.result = f.result ∧
      ∀ args o, f.Run args o ↔ g.Run args o := by
  obtain ⟨f, g, hf, hnf, hg, hng, hb⟩ := optimizeFuncNative?_inv ho
  obtain ⟨hp, hr⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  obtain ⟨gp, gr⟩ : g.params = f.params ∧ g.result = f.result := optimize?_params hg
  have hg' : ofBFunc? ft bf' = some g :=
    ofBFunc?_toBFunc? hb (by rw [hp, gp]) (by rw [hr, gr])
  exact ⟨f, g, hf, hnf, hg', hng, gp, gr, optimize?_equiv hg⟩

/-- **The arity-guarded optimiser preserves native Binaryen semantics.** The
source and the optimised function are recognised at the same type, are
equivalent in the fragment semantics, and, for arguments of the parameter
types, their bodies have the same terminating outcomes under silmaril's
native interpreter (each run from its own declared locals). -/
theorem optimizeFuncNative?_equiv {ft : FuncType} {bf bf' : BFunc}
    (ho : optimizeFuncNative? ft bf = some bf') :
    ∃ f g, ofBFunc? ft bf = some f ∧ ofBFunc? ft bf' = some g ∧ g.params = f.params ∧
      g.result = f.result ∧ (∀ args o, f.Run args o ↔ g.Run args o) ∧
      ∀ {H : Type} (s : Store H) (mi : ModuleInst) (args : List WVal),
        args.map WVal.type = f.params → ∀ o,
          nativeOut s mi f bf.body args o ↔ nativeOut s mi g bf'.body args o := by
  obtain ⟨f, g, hf, hnf, hg, hng, hb⟩ := optimizeFuncNative?_inv ho
  obtain ⟨hp, hr⟩ : ft.params = f.params.map (fun t => .num (.int t)) ∧
      ft.results = resultTypes f.result := ofBFunc?_types hf
  obtain ⟨gp, gr⟩ : g.params = f.params ∧ g.result = f.result := optimize?_params hg
  have hfg : ∀ args o, f.Run args o ↔ g.Run args o := optimize?_equiv hg
  have hg' : ofBFunc? ft bf' = some g :=
    ofBFunc?_toBFunc? hb (by rw [hp, gp]) (by rw [hr, gr])
  refine ⟨f, g, hf, hg', gp, gr, hfg, ?_⟩
  intro H s mi args hty o
  show nativeOut s mi f bf.body args o ↔ nativeOut s mi g bf'.body args o
  rw [← native_adequate s mi (ofBFunc?_body hf) hnf hty,
    ← native_adequate s mi (toBFunc?_body hb) hng (gp ▸ hty)]
  exact hfg args o

/-- **Certified replacement**: the module with the replacement validates, and the
replacement is equivalent to the original function both in the fragment
semantics and under silmaril's native interpreter. -/
theorem optimizeFuncCertified_spec {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCertified m g = some bf') :
    (m.setFunc g bf').Ok ∧ ∃ bf ft f f', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      ofBFunc? ft bf = some f ∧ ofBFunc? ft bf' = some f' ∧
      (∀ args o, f.Run args o ↔ f'.Run args o) ∧
      ∀ {H : Type} (s : Store H) (mi : ModuleInst) (args : List WVal),
        args.map WVal.type = f.params → ∀ o,
          nativeOut s mi f bf.body args o ↔ nativeOut s mi f' bf'.body args o := by
  unfold optimizeFuncCertified at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, hbf, ft, hft, bf'', ho, hv⟩ := h
  split at hv
  · cases hv
    obtain ⟨f, f', hf, hf', -, -, heq, hn⟩ := optimizeFuncNative?_equiv ho
    exact ⟨validates_ok ‹_›, bf, ft, f, f', hbf, hft, hf, hf', heq, hn⟩
  · cases hv

end Silmaril.Wasm.SSA
