module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLift
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumEnv

/-!
# The 1.0 script forward through any nesting of contexts, labels and frames

2.0's forward half stops at one evaluation context (`Sim20.Whole.wholeStepCtxS20`): nesting under
`LABEL_`/`FRAME_` needed typing inversions that were not proved, and 2.0 needs an erratum for
`ctxt-instrs`. 1.0 needs no erratum, and this module proves the inversions for the 1.0 IL:

* `typedV_state_of_typed10`, `typedV_code_of_typed10`: a typed configuration image has a typed
  state and typed code;
* `typedV_stV_iff10`: `state = store; frame` is typed exactly when both halves are;
* `label_inv10`, `frame_inv10`: a typed `LABEL_ n {instr*} admininstr*` (`FRAME_ n {f}
  admininstr*`) has typed components;
* `typedV_val_of_admin10`: a `CONST` typed as `admininstr` is typed as `val` (the IL inlines
  `instr` into `admininstr`, and the two `CONST` cases have one payload type);
* `Nest10 L`: the closure of a relation `L` on V1 configurations under V1's `context`, `label`
  and `frame` (`Nest10.step`: it is a V1 step when `L` is);
* `FwdAt10 B hn c c'`: the image of `c` steps to the image of `c'` in the 1.0 script whenever the
  states and codes of both are typed;
* **`fwd10_nest`**: `FwdAt10` passes from the leaves `L` to all of `Nest10 L`, at every builtins.

So the forward 1.0 half reduces to its leaves, with no hypothesis about the context: the
inversions read every typing the structural rules need off the typing of the outer
configurations.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV stV TypedV ValsOnly stateT storeT frameT nT instrsT
  typedV_list_iff typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase hasTyp_of_hasTypCase matchArgs_nil_scope
  hasTyp_varT_nil_congr)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Generic shapes -/

/-- The empty scope binds term variables only. -/
theorem valsOnly_empty : ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

/-- A closed type name, typed in one scope binding term variables only, is typed in all. -/
theorem typedV_of_scope {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id} {v : Value}
    (h : HasTyp env ρ (.varT x []) v) : TypedV env (.varT x []) v :=
  fun _ hρ' => hasTyp_varT_nil_congr hρ hρ' h

/-- The same, for a list of a closed type name. -/
theorem typedV_list_of_scope {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id}
    {vs : List Value} (h : HasTyp env ρ (.iterT (.varT x []) .list) (.list vs)) :
    TypedV env (.iterT (.varT x []) .list) (.list vs) := by
  obtain ⟨us, hus, hl⟩ := hasTyp_iterT_list_iff.1 h
  obtain rfl := (Value.list.inj hus).symm
  exact typedV_list_iff.2 fun u hu => typedV_of_scope hρ (hasTypList_iff.1 hl u hu)

/-- **Inversion of a closed variant**: a typed injection carries a payload of its case's type, in
the empty scope. -/
theorem hasTyp_closedVariant_inv {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x : IL.Id}
    {cs : List TypCase} (htd : env.findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    {op : MixopS} {w : Value} {t : Typ} {prems : List Prem}
    (h : HasTyp env ρ (.varT x []) (.case op w)) (hf : findCase cs op = some (t, prems)) :
    HasTyp env VarEnv.empty t w := by
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd', -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [htd] at htd'
  obtain rfl := (Option.some.inj htd').symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hi'
  · obtain rfl := matchArgs_nil_scope hm
    obtain ⟨op', w', he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    exact hasTyp_of_hasTypCase hc hf
  · exact absurd hi' not_hasTypInsts_nil

/-- A closed alias, as `TypedV` (as `Sim20.Whole.typedV_aliasG`). -/
theorem typedV_aliasG10 {env : Env} {x : IL.Id} {t : Typ}
    (htd : env.findTyp? x = some ([], [.instD [] [] (.aliasT t)]))
    {v : Value} (h : HasTyp env VarEnv.empty t v) : TypedV env (.varT x []) v :=
  fun ρ hρ =>
    hasTyp_varT_of_insts (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) htd Equiv.evalArgs_nil
      (hasTypInsts_head matchArgs_nil (hasTypDef_aliasT_iff.2 h))

/-- A pair of typed components (as `Sim20.Whole.hasTyp_tup2G`). -/
theorem hasTyp_tup2G10 {env : Env} {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h₁ : TypedV env τ₁ u) (h₂ : TypedV env τ₂ v) :
    HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩

/-- The components of a typed triple with closed component types. -/
theorem hasTyp_tup3_inv {env : Env} {a b c x z : IL.Id} {τ : Typ} {u v : Value}
    {w : List Value}
    (h : HasTyp env VarEnv.empty (.tupT [.mk a (.varT x []), .mk b τ,
      .mk c (.iterT (.varT z []) .list)]) (.tuple [u, v, .list w]))
    (hτ : ∀ {ρ : VarEnv}, ValsOnly ρ → HasTyp env ρ τ v → TypedV env τ v) :
    TypedV env (.varT x []) u ∧ TypedV env τ v ∧ TypedV env (.iterT (.varT z []) .list) (.list w) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨u', us, hus, hu, htup₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hus
  obtain ⟨v', vs', hvs', hv, htup₂⟩ := hasTypTup_cons_iff.1 htup₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj hvs'
  obtain ⟨w', ws', hws', hw, -⟩ := hasTypTup_cons_iff.1 htup₂
  obtain ⟨rfl, -⟩ := List.cons.inj hws'
  exact ⟨typedV_of_scope valsOnly_empty hu, hτ ⟨rfl, rfl, rfl⟩ hv,
    typedV_list_of_scope ⟨rfl, rfl, rfl⟩ hw⟩

/-! ## The 1.0 type definitions -/

theorem findTyp_config10 : (simEnv10 B).findTyp? "config" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]) [] []])]) := rfl

theorem findTyp_state10 : (simEnv10 B).findTyp? "state" = some ([], [.instD [] []
    (.variantT [.mk "%;%" (.tupT [.mk "store" (.varT "store" []), .mk "frame" (.varT "frame" [])])
      [] []])]) := rfl

theorem findTyp_n10 : (simEnv10 B).findTyp? "n" =
    some ([], [.instD [] [] (.aliasT (.numT .natT))]) := rfl

/-- The payload type of `CONST`, in `val` and in `admininstr`. -/
abbrev constT10 : Typ :=
  .tupT [.mk "valtype" (.varT "valtype" []), .mk "_" (.varT "val_" [.expA (.varE "valtype")])]

/-- The payload type of `LABEL_`. -/
abbrev labelT10 : Typ :=
  .tupT [.mk "n" (.varT "n" []), .mk "instr*" (.iterT (.varT "instr" []) .list),
    .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]

/-- The payload type of `FRAME_`. -/
abbrev frameCaseT10 : Typ :=
  .tupT [.mk "n" (.varT "n" []), .mk "frame" (.varT "frame" []),
    .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)]

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- 1.0's `admininstr`, with its `CONST`, `LABEL_` and `FRAME_` cases. -/
theorem findTyp_admininstr10F : ∃ cs, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "CONST" = some (constT10, []) ∧
    findCase cs "LABEL_%{%}%" = some (labelT10, []) ∧
    findCase cs "FRAME_%{%}%" = some (frameCaseT10, []) :=
  ⟨_, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8000000 in
/-- 1.0's `val`, with its single `CONST` case. -/
theorem findTyp_val10F : ∃ cs, (simEnv10 B).findTyp? "val" =
      some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "CONST" = some (constT10, []) :=
  ⟨_, rfl, rfl⟩

/-! ## Configurations and states -/

/-- The payload of a typed configuration image is a typed `state admininstr*` pair. -/
theorem hasTyp_cfgTup_of_typed10 {c : Config H}
    (h : Typed10 (simEnv10 B) hn c) :
    HasTyp (simEnv10 B) VarEnv.empty (.tupT [.mk "state" (.varT "state" []),
      .mk "admininstr*" (.iterT (.varT "admininstr" []) .list)])
      (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)]) :=
  hasTyp_closedVariant_inv valsOnly_empty findTyp_config10 h rfl

/-- **The state of a typed configuration image is typed.** -/
theorem typedV_state_of_typed10 {c : Config H}
    (h : Typed10 (simEnv10 B) hn c) : TypedV (simEnv10 B) stateT (stateV hn c.store c.frame) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (hasTyp_cfgTup_of_typed10 h)
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, hy, -⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, -⟩ := List.cons.inj hys
  exact typedV_of_scope valsOnly_empty hy

/-- **The code of a typed configuration image is a typed `admininstr*`.** -/
theorem typedV_code_of_typed10 {c : Config H}
    (h : Typed10 (simEnv10 B) hn c) : TypedV (simEnv10 B) adminsT (.list (adminsToV c.code)) := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 (hasTyp_cfgTup_of_typed10 h)
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨-, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  exact typedV_list_of_scope ⟨rfl, rfl, rfl⟩ hy'

/-- **`state = store; frame` is typed exactly when both halves are.** -/
theorem typedV_stV_iff10 {s f : Value} :
    TypedV (simEnv10 B) stateT (stV s f) ↔
      TypedV (simEnv10 B) storeT s ∧ TypedV (simEnv10 B) frameT f := by
  constructor
  · intro h
    have hp := hasTyp_closedVariant_inv valsOnly_empty findTyp_state10 (h _ valsOnly_empty) rfl
    obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
    obtain rfl := (Value.tuple.inj hvs).symm
    obtain ⟨y, ys, hys, hy, htup'⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨rfl, rfl⟩ := List.cons.inj hys
    obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
    obtain ⟨rfl, -⟩ := List.cons.inj hys'
    exact ⟨typedV_of_scope valsOnly_empty hy, typedV_of_scope ⟨rfl, rfl, rfl⟩ hy'⟩
  · rintro ⟨hs, hf⟩
    exact Sim20.Pure.typedV_closedCase20 findTyp_state10 rfl
      (hasTyp_tup2G10 hs hf)

/-- `n` holds every natural. -/
theorem typedV_n10 (k : Nat) : TypedV (simEnv10 B) nT (.num (.natN k)) :=
  typedV_aliasG10 findTyp_n10 (hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩)

/-! ## Administrative instructions -/

/-- `admininstr`. -/
abbrev adminT10 : Typ := .varT "admininstr" []

/-- **Inversion of `LABEL_`**: a typed label has a typed arity, continuation and body. -/
theorem label_inv10 {n : Value} {cont is : List Value}
    (h : TypedV (simEnv10 B) adminT10 (.case "LABEL_%{%}%" (.tuple [n, .list cont, .list is]))) :
    TypedV (simEnv10 B) nT n ∧ TypedV (simEnv10 B) instrsT (.list cont) ∧
      TypedV (simEnv10 B) adminsT (.list is) := by
  obtain ⟨cs, htd, -, hl, -⟩ := findTyp_admininstr10F (B := B)
  exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hl)
    (fun hρ hv => typedV_list_of_scope hρ hv)

/-- **Inversion of `FRAME_`**: a typed frame has a typed arity, frame and body. -/
theorem frame_inv10 {n fr : Value} {is : List Value}
    (h : TypedV (simEnv10 B) adminT10 (.case "FRAME_%{%}%" (.tuple [n, fr, .list is]))) :
    TypedV (simEnv10 B) nT n ∧ TypedV (simEnv10 B) frameT fr ∧
      TypedV (simEnv10 B) adminsT (.list is) := by
  obtain ⟨cs, htd, -, -, hf⟩ := findTyp_admininstr10F (B := B)
  exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hf)
    (fun hρ hv => typedV_of_scope hρ hv)

/-- **A `CONST` typed as `admininstr` is typed as `val`.** -/
theorem typedV_val_of_admin10 {w : Value}
    (h : TypedV (simEnv10 B) adminT10 (.case "CONST" w)) :
    TypedV (simEnv10 B) (.varT "val" []) (.case "CONST" w) := by
  obtain ⟨cs, htd, hc, -, -⟩ := findTyp_admininstr10F (B := B)
  obtain ⟨cs', htd', hc'⟩ := findTyp_val10F (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd' hc'
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hc)

/-- **The images of V1 values typed as `admininstr*` are a typed `val*`.** -/
theorem typedV_vals_of_admins10 {us : List Execution.Runtime.Value}
    (h : TypedV (simEnv10 B) adminsT (.list (us.map valV))) :
    TypedV (simEnv10 B) valsTy10 (.list (us.map valV)) :=
  typedV_list_iff.2 fun u hu => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
    exact typedV_val_of_admin10 (w := .tuple [valTypeV v.type, numV v]) (typedV_list_iff.1 h _ hu)

/-- The image of code split in three. -/
theorem adminsToV_append3 (l₁ l₂ l₃ : List Admin) :
    adminsToV (l₁ ++ l₂ ++ l₃) = adminsToV l₁ ++ adminsToV l₂ ++ adminsToV l₃ := by
  simp only [adminsToV_map10, List.map_append]

/-! ## The structural rules on V1 images -/

/-- The image of a configuration, as `cfgV` of `stV`. -/
theorem configV_eq_cfgV10 (s : Store H) (f : Frame) (code : List Admin) :
    configV hn ⟨s, f, code⟩ = cfgV (stateV hn s f) (adminsToV code) := rfl

/-- **`Step/ctxt-instrs` forward on V1 images**: V1's `context`, with every typing read off the
codes and states. -/
theorem fwd10_context {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (vs : List Execution.Runtime.Value) (tail : List Admin)
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f))
    (hz' : TypedV (simEnv10 B) stateT (stateV hn s' f'))
    (hc : TypedV (simEnv10 B) adminsT (.list (adminsToV (values vs ++ before ++ tail))))
    (hc' : TypedV (simEnv10 B) adminsT (.list (adminsToV (values vs ++ after ++ tail))))
    (h : SStepB (simEnv10 B) (configV hn ⟨s, f, before⟩) (configV hn ⟨s', f', after⟩)) :
    SStepB (simEnv10 B) (configV hn ⟨s, f, values vs ++ before ++ tail⟩)
      (configV hn ⟨s', f', values vs ++ after ++ tail⟩) := by
  rw [adminsToV_append3, adminsToV_values] at hc hc'
  obtain ⟨hcv, hct⟩ := typedV_list_append.1 hc
  obtain ⟨hvs, hb⟩ := typedV_list_append.1 hcv
  obtain ⟨hcv', -⟩ := typedV_list_append.1 hc'
  obtain ⟨-, ha⟩ := typedV_list_append.1 hcv'
  by_cases hne : vs.map valV ≠ [] ∨ adminsToV tail ≠ []
  · have hs := sstep10_ctxtInstrs hz hz' (typedV_vals_of_admins10 hvs) hb ha hct hne
      ((sstepB10_iff B).1 h)
    refine (sstepB10_iff B).2 ?_
    simpa only [configV_eq_cfgV10, adminsToV_append3, adminsToV_values] using hs
  · obtain ⟨h₁, h₂⟩ : vs.map valV = [] ∧ adminsToV tail = [] := by simpa [not_or] using hne
    obtain rfl : vs = [] := List.map_eq_nil_iff.1 h₁
    obtain rfl : tail = [] := by
      rw [adminsToV_map10] at h₂
      exact List.map_eq_nil_iff.1 h₂
    simpa [values] using h

/-- **`Step/ctxt-label` forward on V1 images**: V1's `label`. -/
theorem fwd10_label {s s' : Store H} {f f' : Frame} {before after : List Admin} (n : Nat)
    (cont : V1.Expr) (hz : TypedV (simEnv10 B) stateT (stateV hn s f))
    (hz' : TypedV (simEnv10 B) stateT (stateV hn s' f'))
    (hc : TypedV (simEnv10 B) adminsT (.list (adminsToV [.label n cont before])))
    (hc' : TypedV (simEnv10 B) adminsT (.list (adminsToV [.label n cont after])))
    (h : SStepB (simEnv10 B) (configV hn ⟨s, f, before⟩) (configV hn ⟨s', f', after⟩)) :
    SStepB (simEnv10 B) (configV hn ⟨s, f, [.label n cont before]⟩)
      (configV hn ⟨s', f', [.label n cont after]⟩) := by
  obtain ⟨hn', hcont, hb⟩ := label_inv10 (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, -, ha⟩ := label_inv10 (typedV_list_iff.1 hc' _ (.head _))
  exact (sstepB10_iff B).2 (sstep10_ctxtLabel hz hz' hn' hcont hb ha ((sstepB10_iff B).1 h))

/-- **`Step/ctxt-frame` forward on V1 images**: V1's `frame`, the inner frame changing. -/
theorem fwd10_frame {s s' : Store H} {inner inner' outer : Frame} {before after : List Admin}
    (n : Nat) (hz : TypedV (simEnv10 B) stateT (stateV hn s outer))
    (hz' : TypedV (simEnv10 B) stateT (stateV hn s' outer))
    (hc : TypedV (simEnv10 B) adminsT (.list (adminsToV [.frame n inner before])))
    (hc' : TypedV (simEnv10 B) adminsT (.list (adminsToV [.frame n inner' after])))
    (h : SStepB (simEnv10 B) (configV hn ⟨s, inner, before⟩) (configV hn ⟨s', inner', after⟩)) :
    SStepB (simEnv10 B) (configV hn ⟨s, outer, [.frame n inner before]⟩)
      (configV hn ⟨s', outer, [.frame n inner' after]⟩) := by
  obtain ⟨hs, ho⟩ := typedV_stV_iff10.1 hz
  obtain ⟨hs', -⟩ := typedV_stV_iff10.1 hz'
  obtain ⟨hn', hi, hb⟩ := frame_inv10 (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, hi', ha⟩ := frame_inv10 (typedV_list_iff.1 hc' _ (.head _))
  exact (sstepB10_iff B).2 (sstep10_ctxtFrame hs hs' ho hi hi' hn' hb ha ((sstepB10_iff B).1 h))

/-! ## Nesting -/

/-- **The closure of `L` under V1's `context`, `label` and `frame`.** -/
inductive Nest10 (L : Config H → Config H → Prop) : Config H → Config H → Prop where
  | leaf {c c' : Config H} (h : L c c') : Nest10 L c c'
  | context {s s' : Store H} {f f' : Frame} {before after : List Admin}
      (h : Nest10 L ⟨s, f, before⟩ ⟨s', f', after⟩) (vs : List Execution.Runtime.Value)
      (tail : List Admin) :
      Nest10 L ⟨s, f, values vs ++ before ++ tail⟩ ⟨s', f', values vs ++ after ++ tail⟩
  | label {s s' : Store H} {f f' : Frame} {before after : List Admin}
      (h : Nest10 L ⟨s, f, before⟩ ⟨s', f', after⟩) (n : Nat) (cont : V1.Expr) :
      Nest10 L ⟨s, f, [.label n cont before]⟩ ⟨s', f', [.label n cont after]⟩
  | frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
      (h : Nest10 L ⟨s, inner, before⟩ ⟨s', inner', after⟩) (n : Nat) (outer : Frame) :
      Nest10 L ⟨s, outer, [.frame n inner before]⟩ ⟨s', outer, [.frame n inner' after]⟩

/-- `Nest10 L` steps are V1 steps when the leaves are. -/
theorem Nest10.step {L : Config H → Config H → Prop} {host : HostSemantics H}
    (hL : ∀ c c', L c c' → Step host c c') {c c' : Config H} (h : Nest10 L c c') :
    Step host c c' := by
  induction h with
  | leaf h => exact hL _ _ h
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer

/-- **The forward obligation at a pair of configurations**: whenever the states and codes of both
are typed, the image of `c` steps to the image of `c'` in the 1.0 script. -/
def FwdAt10 (B : Builtins) (hn : H → String) (c c' : Config H) : Prop :=
  TypedV (simEnv10 B) stateT (stateV hn c.store c.frame) →
    TypedV (simEnv10 B) stateT (stateV hn c'.store c'.frame) →
    TypedV (simEnv10 B) adminsT (.list (adminsToV c.code)) →
    TypedV (simEnv10 B) adminsT (.list (adminsToV c'.code)) →
    SStepB (simEnv10 B) (configV hn c) (configV hn c')

/-- `FwdAt10` lifts through V1's `context`. -/
theorem fwdAt10_context {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : FwdAt10 B hn ⟨s, f, before⟩ ⟨s', f', after⟩) (vs : List Execution.Runtime.Value)
    (tail : List Admin) :
    FwdAt10 B hn ⟨s, f, values vs ++ before ++ tail⟩ ⟨s', f', values vs ++ after ++ tail⟩ := by
  intro hz hz' hc hc'
  have hb : TypedV (simEnv10 B) adminsT (.list (adminsToV before)) := by
    rw [adminsToV_append3] at hc
    exact (typedV_list_append.1 (typedV_list_append.1 hc).1).2
  have ha : TypedV (simEnv10 B) adminsT (.list (adminsToV after)) := by
    rw [adminsToV_append3] at hc'
    exact (typedV_list_append.1 (typedV_list_append.1 hc').1).2
  exact fwd10_context vs tail hz hz' hc hc' (ih hz hz' hb ha)

/-- `FwdAt10` lifts through V1's `label`. -/
theorem fwdAt10_label {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (ih : FwdAt10 B hn ⟨s, f, before⟩ ⟨s', f', after⟩) (n : Nat) (cont : V1.Expr) :
    FwdAt10 B hn ⟨s, f, [.label n cont before]⟩ ⟨s', f', [.label n cont after]⟩ :=
  fun hz hz' hc hc' => fwd10_label n cont hz hz' hc hc'
    (ih hz hz' (label_inv10 (typedV_list_iff.1 hc _ (.head _))).2.2
      (label_inv10 (typedV_list_iff.1 hc' _ (.head _))).2.2)

/-- `FwdAt10` lifts through V1's `frame`. -/
theorem fwdAt10_frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin}
    (ih : FwdAt10 B hn ⟨s, inner, before⟩ ⟨s', inner', after⟩) (n : Nat) (outer : Frame) :
    FwdAt10 B hn ⟨s, outer, [.frame n inner before]⟩ ⟨s', outer, [.frame n inner' after]⟩ := by
  intro hz hz' hc hc'
  obtain ⟨-, hi, hb⟩ := frame_inv10 (typedV_list_iff.1 hc _ (.head _))
  obtain ⟨-, hi', ha⟩ := frame_inv10 (typedV_list_iff.1 hc' _ (.head _))
  have hzi : TypedV (simEnv10 B) stateT (stateV hn s inner) :=
    typedV_stV_iff10.2 ⟨(typedV_stV_iff10.1 hz).1, hi⟩
  have hzi' : TypedV (simEnv10 B) stateT (stateV hn s' inner') :=
    typedV_stV_iff10.2 ⟨(typedV_stV_iff10.1 hz').1, hi'⟩
  exact fwd10_frame n hz hz' hc hc' (ih hzi hzi' hb ha)

/-- **The forward 1.0 half passes from the leaves to every nesting**, at every builtins. -/
theorem fwd10_nest {L : Config H → Config H → Prop} (hL : ∀ c c', L c c' → FwdAt10 B hn c c')
    {c c' : Config H} (h : Nest10 L c c') : FwdAt10 B hn c c' := by
  induction h with
  | leaf h => exact hL _ _ h
  | context _ vs tail ih => exact fwdAt10_context ih vs tail
  | label _ n cont ih => exact fwdAt10_label ih n cont
  | frame _ n outer ih => exact fwdAt10_frame ih n outer

/-- `fwd10_nest` from typed configuration images. -/
theorem fwd10_nest_typed {L : Config H → Config H → Prop}
    (hL : ∀ c c', L c c' → FwdAt10 B hn c c') {c c' : Config H}
    (hc : Typed10 (simEnv10 B) hn c) (hc' : Typed10 (simEnv10 B) hn c') (h : Nest10 L c c') :
    SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  fwd10_nest hL h (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc')
    (typedV_code_of_typed10 hc) (typedV_code_of_typed10 hc')

end Silmaril.Wasm.SpecTec.Sim10.Whole
