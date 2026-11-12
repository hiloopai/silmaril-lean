module

public import Silmaril.Wasm.FnInst.IR.Bodies.Defs
public import Silmaril.Wasm.FnInst.IR.Lang.Thms

/-!
# The IR and SSA body variants: preservation and reflection of equivalence

Every translation of `Bodies.Defs` has the identity as environment map, so each comorphism is
model-expansive and borrows validity both ways (`valid_toSSA_iff`, `valid_ofSSA_iff`,
`valid_ofBir_iff`, `valid_nativeIncl_iff`).

Equivalence, concretely (`Beh.Equiv` of terminating outcomes):

* `equiv_compile_iff`: two fragment functions are equivalent iff their SSA translations are;
* `equiv_decompile_iff`: two decompilable SSA functions are equivalent iff their
  out-of-SSA results are;
* `compile_decompile_equiv`: the round trip `frag → SSA → frag`, where out-of-SSA succeeds, is
  equivalent to the source;
* `equiv_bir_iff`: two Binaryen bodies are equivalent (in any store and module instance) iff
  their recognised fragment functions are;
* `lower_body`, `equiv_lower_iff`: where the partial lowering `toBFunc?` succeeds on
  native-checked functions, Binaryen equivalence of the lowered bodies is fragment equivalence.

So the variants are equivalent where the translations are exact: on all fragment functions for
SSA, on decompilable SSA functions for out-of-SSA, on native-checked recognised bodies for
Binaryen IR.

Applications (equations of the optimiser as valid sentences):

* `optimize_valid`: `optimize? f = some g` makes `f ≐ g` valid in the fragment institution;
* `optimizeSSA_valid`: `optimizeSSA s ≐ s` is valid in the SSA institution;
* `optimizeFuncNative_valid`: `optimizeFuncNative? h.funcType bf = some bf'` makes `bf ≐ bf'`
  valid in the Binaryen institution, by borrowing along `ofBir ≫ nativeIncl` from the fragment
  equation (no native-interpreter reasoning in the proof).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.Institution (Formula)
open Silmaril.Wasm.SSA
open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

variable {Sig : Type} [Category.{0} Sig] (F : Frame Sig)

/-! ## Borrowing along the translations -/

theorem valid_toSSA_iff (E : Type) {S : Sig} (φ : ((frag E).inst F).Sen S) :
    ((frag E).inst F).Valid φ ↔ ((ssa E).inst F).Valid (((toSSA E).comorphism F).sen S φ) :=
  (toSSA E).valid_iff F (fun e => ⟨e, rfl⟩) φ

theorem valid_ofSSA_iff (E : Type) {S : Sig} (φ : ((ssaDec E).inst F).Sen S) :
    ((ssaDec E).inst F).Valid φ ↔ ((frag E).inst F).Valid (((ofSSA E).comorphism F).sen S φ) :=
  (ofSSA E).valid_iff F (fun e => ⟨e, rfl⟩) φ

theorem valid_ofBir_iff (H : Type) {S : Sig} (φ : ((bir H).inst F).Sen S) :
    ((bir H).inst F).Valid φ ↔
      ((fragNative (Store H × ModuleInst)).inst F).Valid (((ofBir H).comorphism F).sen S φ) :=
  (ofBir H).valid_iff F (fun e => ⟨e, rfl⟩) φ

theorem valid_nativeIncl_iff (E : Type) {S : Sig} (φ : ((fragNative E).inst F).Sen S) :
    ((fragNative E).inst F).Valid φ ↔
      ((frag E).inst F).Valid (((nativeIncl E).comorphism F).sen S φ) :=
  (nativeIncl E).valid_iff F (fun e => ⟨e, rfl⟩) φ

/-! ## Equivalence, concretely -/

/-- **SSA reflects and preserves equivalence.** -/
theorem equiv_compile_iff (f f' : FragFunc) :
    Beh.Equiv (compileFunc f).Run (compileFunc f').Run ↔ Beh.Equiv f.Run f'.Run := by
  simp only [Beh.Equiv, compileFunc_iff]

/-- **Out-of-SSA reflects and preserves equivalence.** -/
theorem equiv_decompile_iff {s s' : SFunc} {g g' : FragFunc} (hg : decompileFunc s = some g)
    (hg' : decompileFunc s' = some g') : Beh.Equiv g.Run g'.Run ↔ Beh.Equiv s.Run s'.Run := by
  simp only [Beh.Equiv, decompileFunc_iff hg, decompileFunc_iff hg']

/-- The round trip through SSA, where out-of-SSA succeeds, is equivalent to the source. -/
theorem compile_decompile_equiv {f g : FragFunc} (hg : decompileFunc (compileFunc f) = some g) :
    Beh.Equiv g.Run f.Run := fun _ _ => (decompileFunc_iff hg).trans compileFunc_iff

/-- **Binaryen IR reflects and preserves equivalence**: two Binaryen bodies are equivalent in
an environment iff their recognised fragment functions are. -/
theorem equiv_bir_iff (H : Type) (e : Store H × ModuleInst) {h : Hole} (b b' : BirBody h) :
    Beh.Equiv ((bir H).den e h b) ((bir H).den e h b') ↔ Beh.Equiv b.recog.Run b'.recog.Run :=
  (ofBir H).equiv_iff e h b b' |>.symm

/-- A native-checked fragment function that lowers is a Binaryen body recognising back to it. -/
theorem lower_body {h : Hole} (f : (fragNative Unit).Body h) {ty : TypeIdx} {bf : BFunc}
    (hl : toBFunc? ty f.1 = some bf) : ∃ b : BirBody h, b.1 = bf ∧ b.recog = f.1 := by
  have hr : ofBFunc? h.funcType bf = some f.1 :=
    ofBFunc?_toBFunc? hl (by rw [f.2.1.1]; rfl) (by rw [f.2.1.2]; rfl)
  refine ⟨⟨bf, f.1, hr, f.2.2⟩, rfl, ?_⟩
  exact Option.some.inj ((BirBody.recog_spec _).symm.trans hr)

/-- **Lowering is exact on equivalence**: lowered native-checked functions are Binaryen-equivalent
(in any environment) iff they are equivalent in the fragment. -/
theorem equiv_lower_iff (H : Type) (e : Store H × ModuleInst) {h : Hole}
    (f f' : (fragNative Unit).Body h) {ty ty' : TypeIdx} {bf bf' : BFunc}
    (hl : toBFunc? ty f.1 = some bf) (hl' : toBFunc? ty' f'.1 = some bf') :
    ∃ b b' : BirBody h, b.1 = bf ∧ b'.1 = bf' ∧
      (Beh.Equiv ((bir H).den e h b) ((bir H).den e h b') ↔ Beh.Equiv f.1.Run f'.1.Run) := by
  obtain ⟨b, hb, hbr⟩ := lower_body f hl
  obtain ⟨b', hb', hbr'⟩ := lower_body f' hl'
  refine ⟨b, b', hb, hb', ?_⟩
  rw [equiv_bir_iff, hbr, hbr']

/-! ## The optimiser's equations as valid sentences -/

/-- `optimize? f = some g` makes `f ≐ g` valid in the fragment institution. -/
theorem optimize_valid (E : Type) {S : Sig} [Nonempty (F.Ctx S)]
    (f : (frag E).Body (F.hole S)) {g : FragFunc} (hg : optimize? f.1 = some g) :
    ∃ g' : (frag E).Body (F.hole S), g'.1 = g ∧
      ((frag E).inst F).Valid (Formula.eq f g' : ((frag E).inst F).Sen S) := by
  obtain ⟨gp, gr⟩ := optimize?_params hg
  refine ⟨⟨g, gp.trans f.2.1, gr.trans f.2.2⟩, rfl, ?_⟩
  exact ((frag E).valid_eq_iff F f _).2 fun _ args o => optimize?_equiv hg args o

/-- `optimizeSSA s ≐ s` is valid in the SSA institution. -/
theorem optimizeSSA_valid (E : Type) {S : Sig} (s : (ssa E).Body (F.hole S))
    (hs : (optimizeSSA s.1).params = s.1.params ∧ (optimizeSSA s.1).result = s.1.result) :
    ((ssa E).inst F).Valid
      (Formula.eq ⟨optimizeSSA s.1, hs.1.trans s.2.1, hs.2.trans s.2.2⟩ s :
        ((ssa E).inst F).Sen S) := by
  intro M
  exact ((ssa E).sat_eq_iff F M _ s).2 fun _ _ => optimizeSSA_iff

/-- The optimised Binaryen function of `optimizeFuncNative?` is a Binaryen body at the same
hole, recognising to the optimiser's fragment output. -/
theorem optimizeFuncNative_bodies {h : Hole} {bf bf' : BFunc}
    (ho : optimizeFuncNative? h.funcType bf = some bf') :
    ∃ (b b' : BirBody h), b.1 = bf ∧ b'.1 = bf' ∧ optimize? b.recog = some b'.recog := by
  obtain ⟨f, hf, u, hu, g, hg, v, hv, hb⟩ : ∃ f, ofBFunc? h.funcType bf = some f ∧ ∃ u,
      guard (f.native = true) = some u ∧ ∃ g, optimize? f = some g ∧ ∃ v,
        guard (g.native = true) = some v ∧ toBFunc? bf.type g = some bf' := by
    simpa only [optimizeFuncNative?, Option.bind_eq_bind, Option.bind_eq_some_iff] using ho
  have hfn : f.native = true := by
    by_contra hc; simp [guard, hc] at hu
  have hgn : g.native = true := by
    by_contra hc; simp [guard, hc] at hv
  obtain ⟨gp, gr⟩ := optimize?_params hg
  have hft : HasType f h := hasType_of_ofBFunc? hf
  obtain ⟨b', hb', hbr'⟩ := lower_body (h := h) ⟨g, ⟨gp.trans hft.1, gr.trans hft.2⟩, hgn⟩ hb
  let b : BirBody h := ⟨bf, f, hf, hfn⟩
  have hrec : BirBody.recog b = f := Option.some.inj ((BirBody.recog_spec b).symm.trans hf)
  exact ⟨b, b', rfl, hb', by rw [hrec, hbr']; exact hg⟩

/-- **The arity-guarded optimiser as a valid Binaryen sentence**: `bf ≐ bf'` is valid in the
Binaryen institution, borrowed along `ofBir` and `nativeIncl` from the fragment equation
`optimize?_equiv`. -/
theorem optimizeFuncNative_valid (H : Type) {S : Sig} {bf bf' : BFunc}
    (ho : optimizeFuncNative? (F.hole S).funcType bf = some bf') :
    ∃ (b b' : BirBody (F.hole S)), b.1 = bf ∧ b'.1 = bf' ∧
      ((bir H).inst F).Valid (Formula.eq b b' : ((bir H).inst F).Sen S) := by
  obtain ⟨b, b', hb, hb', hopt⟩ := optimizeFuncNative_bodies ho
  refine ⟨b, b', hb, hb', ?_⟩
  refine (valid_ofBir_iff F H _).2 ((valid_nativeIncl_iff F _ _).2 fun M => ?_)
  exact ((frag _).sat_eq_iff F M _ _).2 fun args o => optimize?_equiv hopt args o

end Silmaril.Wasm.FnInst.IR
