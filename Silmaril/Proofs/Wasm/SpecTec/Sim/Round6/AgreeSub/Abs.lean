module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeSub.RulesBot
public import Silmaril.Wasm.SpecTec.Sim.Round6.RefOkB.Thms

/-!
# Round 6: the abstract heap-type order, under `DDerivesB`

Rule lemmas for `Heaptype_sub` that need no defined type, in any typed context `c`:

* `dderivesB_refl`, `dderivesB_trans`: `refl` and `trans` (whose middle needs `Heaptype_ok`);
* `dderivesB_axiom`: `eq-any`, `i31-eq`, `struct-eq`, `array-eq`;
* `dderivesB_botRule`: `none`, `nofunc`, `noexn`, `noextern`;
* `dderivesB_absSub`: **Silmaril's abstract order `absSub` is derivable**, through abstract
  middle types only (`EQ` for `I31`/`STRUCT`/`ARRAY <: ANY`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV absV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.Reading

variable {B : Builtins}

/-- `C ⊢ a <: b` under `DDerivesB`, in `simEnv B`. -/
abbrev HSub (B : Builtins) (O : ElseI) (c a b : Value) : Prop :=
  DDerivesB (simEnv B) O "Heaptype_sub" "%|-%<:%" [] (.tuple [c, a, b])

/-- A typed context. -/
abbrev CtxT (B : Builtins) (c : Value) : Prop := TypedV (simEnv B) (.varT "context" []) c

/-- A typed heap type. -/
abbrev HeapT (B : Builtins) (h : Value) : Prop := TypedV (simEnv B) (.varT "heaptype" []) h

/-- A nullary case evaluates to itself. -/
theorem evalExp_atomE {env : Env} {ρ : VarEnv} (op : MixopS) :
    EvalExp env ρ (atomE op) (.case op (.tuple [])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- An abstract heap type is a typed heap type. -/
theorem heapT_abs (a : AbsHeapType) : HeapT B (absV a) := typedV_heaptype (h := .abs a) rfl

/-- **`Heaptype_sub/refl`.** -/
theorem dderivesB_refl (O : ElseI) {c h : Value} (hc : CtxT B c) (hh : HeapT B h) :
    HSub B O c h h :=
  dderivesB_of_ruleAt ruleAt_refl (self_mem_conclAlts _) [("C", c), ("heaptype", h)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) premsB_nil

/-- **`Heaptype_sub/trans`**, through a middle type `m` with `C ⊢ m : OK`. -/
theorem dderivesB_trans (O : ElseI) {c a m b : Value} (hc : CtxT B c) (ha : HeapT B a)
    (hb : HeapT B b) (hm : HeapT B m)
    (hok : DDerivesB (simEnv B) O "Heaptype_ok" "%|-%:OK" [] (.tuple [c, m]))
    (h₁ : HSub B O c a m) (h₂ : HSub B O c m b) : HSub B O c a b :=
  dderivesB_of_ruleAt ruleAt_trans (self_mem_conclAlts _)
    [("C", c), ("heaptype_1", a), ("heaptype_2", b), ("heaptype'", m)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (ha _ (valsOnly_bind _))
      (QuantsOk.cons rfl (hb _ (valsOnly_bind _)) (QuantsOk.cons rfl (hm _ (valsOnly_bind _))
        QuantsOk.nil))))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
    (RefOkB.premsB_cons
      (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) hok)
      (premsB_two
        (.rulePr (evalArgs_nil _ _)
          (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) h₁)
        (.rulePr (evalArgs_nil _ _)
          (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl)) h₂)))

/-- **`Heaptype_sub/trans` through an abstract middle type**, which is valid in every typed
context (`Heaptype_ok/abs`). -/
theorem dderivesB_transAbs (O : ElseI) {c a b : Value} (m : AbsHeapType) (hc : CtxT B c)
    (ha : HeapT B a) (hb : HeapT B b) (h₁ : HSub B O c a (absV m)) (h₂ : HSub B O c (absV m) b) :
    HSub B O c a b :=
  dderivesB_trans O hc ha hb (heapT_abs m) (dderivesB_heaptypeOk_abs O hc m) h₁ h₂

/-- **The four abstract axioms** `eq-any`, `i31-eq`, `struct-eq`, `array-eq`. -/
theorem dderivesB_axiom (O : ElseI) {c : Value} (hc : CtxT B c) {k : Nat} {nm : IL.Id}
    {a b : MixopS}
    (hr : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" k
      (.ruleD nm [ctxP] "%|-%<:%" (.tupE [.varE "C", atomE a, atomE b]) [])) :
    HSub B O c (.case a (.tuple [])) (.case b (.tuple [])) :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (evalExp_var rfl) (evalExp_atomE a) (evalExp_atomE b)) premsB_nil

/-- **`Heaptype_sub/none` and its siblings**: an abstract bottom is below every non-`BOT` heap
type below its top. -/
theorem dderivesB_botRule (O : ElseI) {c h : Value} (hc : CtxT B c) (hh : HeapT B h)
    {k : Nat} {nm : IL.Id} {bot top : MixopS}
    (hr : HasRuleAt (simEnv B) "Heaptype_sub" "%|-%<:%" k (botRule nm bot top))
    (hne : h ≠ .case "BOT" (.tuple [])) (hs : HSub B O c h (.case top (.tuple []))) :
    HSub B O c (.case bot (.tuple [])) h :=
  dderivesB_of_ruleAt hr (self_mem_conclAlts _) [("C", c), ("heaptype", h)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hh _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (evalExp_var rfl) (evalExp_atomE bot) (evalExp_var rfl))
    (premsB_two
      (.rulePr (evalArgs_nil _ _) (evalExp_tup3 (evalExp_var rfl) (evalExp_var rfl)
        (evalExp_atomE top)) hs)
      (.ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_atomE "BOT",
        by simp [cmpValues, hne]⟩)))

/-- An abstract heap type is not `BOT`. -/
theorem absV_ne_bot (a : AbsHeapType) : absV a ≠ .case "BOT" (.tuple []) := by
  cases a <;> simp [absV]

/-- `X <: ANY` for the four abstract types below `EQ` or equal to it. -/
theorem dderivesB_toAny (O : ElseI) {c : Value} (hc : CtxT B c) :
    ∀ b : AbsHeapType, absSub b .any = true → HSub B O c (absV b) (absV .any) := by
  intro b hb
  have eqAny : HSub B O c (absV .eq) (absV .any) := dderivesB_axiom O hc ruleAt_eqAny
  cases b <;> simp [absSub] at hb
  · exact dderivesB_refl O hc (heapT_abs _)
  · exact eqAny
  · exact dderivesB_transAbs O .eq hc (heapT_abs _) (heapT_abs _)
      (dderivesB_axiom O hc ruleAt_i31Eq) eqAny
  · exact dderivesB_transAbs O .eq hc (heapT_abs _) (heapT_abs _)
      (dderivesB_axiom O hc ruleAt_structEq) eqAny
  · exact dderivesB_transAbs O .eq hc (heapT_abs _) (heapT_abs _)
      (dderivesB_axiom O hc ruleAt_arrayEq) eqAny
  · exact dderivesB_botRule O hc (heapT_abs _) ruleAt_none (absV_ne_bot _)
      (dderivesB_refl O hc (heapT_abs .any))

/-- **Silmaril's abstract order is derivable**: `absSub a b` gives `C ⊢ a <: b`. -/
theorem dderivesB_absSub (O : ElseI) {c : Value} (hc : CtxT B c) :
    ∀ a b : AbsHeapType, absSub a b = true → HSub B O c (absV a) (absV b) := by
  intro a b hab
  have refl : ∀ x : AbsHeapType, HSub B O c (absV x) (absV x) := fun x =>
    dderivesB_refl O hc (heapT_abs x)
  have toAny := dderivesB_toAny (B := B) O hc
  have none : ∀ x, absSub x .any = true → HSub B O c (absV .none) (absV x) := fun x hx =>
    dderivesB_botRule O hc (heapT_abs x) ruleAt_none (absV_ne_bot x) (toAny x hx)
  cases a <;> cases b <;> simp [absSub] at hab <;>
    first
    | exact refl _
    | exact toAny _ rfl
    | exact none _ rfl
    | exact dderivesB_axiom O hc ruleAt_i31Eq
    | exact dderivesB_axiom O hc ruleAt_structEq
    | exact dderivesB_axiom O hc ruleAt_arrayEq
    | exact dderivesB_botRule O hc (heapT_abs _) ruleAt_nofunc (absV_ne_bot _) (refl .func)
    | exact dderivesB_botRule O hc (heapT_abs _) ruleAt_noexn (absV_ne_bot _) (refl .exn)
    | exact dderivesB_botRule O hc (heapT_abs _) ruleAt_noextern (absV_ne_bot _) (refl .extern)

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub
