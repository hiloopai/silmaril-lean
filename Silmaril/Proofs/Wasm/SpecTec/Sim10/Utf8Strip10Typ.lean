module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Inv

/-!
# Leg 2 for 1.0: a configuration typed in `utf8Env10T`, stripped, is typed in `simEnv10T`

`utf8Env10T B` and `simEnv10T B` have the same type table (`Utf8Fix.findTyp?_utf8Env10T`), and
they type alike every type off the twelve types that reach `name` (`Utf8Fix.hasTyp_u10T_iff`).
At a module instance the one field whose type reaches `name` is `EXPORTS`, and stripping leaves
`[]` there, which every environment types. So:

* `typedV_u10`: off `badU20`, `utf8Env10T B` typing gives `simEnv10T B` typing;
* `typed10_iffE`, `typedV_stV_iffE`, `typedV_frame_iffE`, `typedV_funcInst_iffE`,
  `typedV_store_iffE`: the 1.0 configuration, state, frame, function instance and store are
  typed field by field, in any environment with the type table of `simEnv10T B`;
* `typedV_admin_u10`: an `admininstr` of `utf8Env10T B` other than a label or frame is one of
  `simEnv10T B` (the kernel checks the cases of 1.0's `admininstr`, `adminCasesOk10`);
* **`typedV_moduleInst_strip10`**, `typedV_store_strip10`, `typedV_frame_strip10`,
  `typedV_admins_strip10` and **`typed10_strip`**: typing in `utf8Env10T B`, with the exports
  removed, is typing in `simEnv10T B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT nT instrsT)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Else (badU20 evFreeB goodEvs_of_all)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T hasTyp_u10T_iff findTyp?_utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (adminsT adminT10 labelT10 frameCaseT10 hasTyp_tup2G10
  hasTyp_tup3G10 hasTyp_tup3_inv hasTyp_closedVariant_inv typedV_of_scope typedV_list_of_scope
  valsOnly_empty)
open Silmaril.Wasm.SpecTec.Sim20.Whole (hasTypFields_of_closed hasTypFields_cons_nil_iff
  typedV_of_empty20 typedV_list_of_empty20 typedV_structG hasTypFields_consG hasTypFields_oneG)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## Moving types off `badU20` -/

/-- **Off `badU20`, a type of `utf8Env10T B` is one of `simEnv10T B`.** -/
theorem typedV_u10 (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (ht : (evTyp t).all (tyEvB badU20) = true) (hte : (evTyp t).all (evFreeB "utf8") = true)
    (h : TypedV (utf8Env10T B) t v) : TypedV (simEnv10T B) t v := fun ρ hρ =>
  (hasTyp_u10T_iff hB hρ.1 (fun p hp => by simp [hρ.2.1] at hp) (goodT_of_all ht)
    (goodEvs_of_all hte)).1 (h ρ hρ)

/-- `typedV_u10` in the empty scope. -/
theorem hasTyp_u10 (hB : ∀ ws, B.call "utf8" ws = none) {t : Typ} {v : Value}
    (ht : (evTyp t).all (tyEvB badU20) = true) (hte : (evTyp t).all (evFreeB "utf8") = true)
    (h : HasTyp (utf8Env10T B) VarEnv.empty t v) : HasTyp (simEnv10T B) VarEnv.empty t v :=
  (hasTyp_u10T_iff hB rfl (fun p hp => by simp [VarEnv.empty, Map.empty] at hp) (goodT_of_all ht)
    (goodEvs_of_all hte)).1 h

/-- The empty list is typed at every list type. -/
theorem typedV_listNil10 {e : Env} {t : Typ} : TypedV e (.iterT t .list) (.list []) :=
  Sim.typedV_list_iff.2 fun _ hu => nomatch hu

/-! ## The 1.0 runtime types -/

set_option maxRecDepth 8000000 in
theorem findTyp_moduleinst10T : (simEnv10T B).findTyp? "moduleinst" = some ([], [.instD [] []
    (.structT [.mk "TYPES" (.iterT (.varT "functype" []) .list) [] [],
      .mk "FUNCS" (.iterT (.varT "funcaddr" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globaladdr" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableaddr" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "memaddr" []) .list) [] [],
      .mk "EXPORTS" (.iterT (.varT "exportinst" []) .list) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_funcinst10T : (simEnv10T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_store10T : (simEnv10T B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" (.iterT (.varT "funcinst" []) .list) [] [],
      .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" (.iterT (.varT "tableinst" []) .list) [] [],
      .mk "MEMS" (.iterT (.varT "meminst" []) .list) [] []])]) := rfl

/-- An environment with the type table of `simEnv10T B`. -/
def SameTyps (B : Builtins) (E : Env) : Prop := ∀ x, E.findTyp? x = (simEnv10T B).findTyp? x

theorem sameTyps_sim (B : Builtins) : SameTyps B (simEnv10T B) := fun _ => rfl

theorem sameTyps_utf8 (B : Builtins) : SameTyps B (utf8Env10T B) := fun x => findTyp?_utf8Env10T B x

variable {E : Env}

/-- **A configuration image is typed exactly when its state and code are.** -/
theorem typed10_iffE (hE : SameTyps B E) {c : Config H} :
    Typed10 E hn c ↔ TypedV E stateT (stateV hn c.store c.frame) ∧
      TypedV E adminsT (.list (adminsToV c.code)) := by
  have htd := (hE "config").trans StoreAgree.findTyp_config10T
  constructor
  · intro h
    have hp := hasTyp_closedVariant_inv valsOnly_empty htd h rfl
    obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
    obtain rfl := (Value.tuple.inj hvs).symm
    obtain ⟨y, ys, hys, hy, htup'⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨rfl, rfl⟩ := List.cons.inj hys
    obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
    obtain ⟨rfl, -⟩ := List.cons.inj hys'
    exact ⟨typedV_of_scope valsOnly_empty hy, typedV_list_of_scope ⟨rfl, rfl, rfl⟩ hy'⟩
  · rintro ⟨hz, hc⟩
    exact Sim20.Pure.typedV_closedCase20 htd rfl (hasTyp_tup2G10 hz hc) _ valsOnly_empty

/-- **`state = store; frame` is typed exactly when both halves are.** -/
theorem typedV_stV_iffE (hE : SameTyps B E) {s : Store H} {f : Frame} :
    TypedV E stateT (stateV hn s f) ↔ TypedV E storeT (storeV hn s) ∧ TypedV E frameT (frameV f) := by
  have htd := (hE "state").trans StoreAgree.findTyp_state10T
  constructor
  · intro h
    have hp := hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) rfl
    obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
    obtain rfl := (Value.tuple.inj hvs).symm
    obtain ⟨y, ys, hys, hy, htup'⟩ := hasTypTup_cons_iff.1 htup
    obtain ⟨rfl, rfl⟩ := List.cons.inj hys
    obtain ⟨y', ys', hys', hy', -⟩ := hasTypTup_cons_iff.1 htup'
    obtain ⟨rfl, -⟩ := List.cons.inj hys'
    exact ⟨typedV_of_scope valsOnly_empty hy, typedV_of_scope ⟨rfl, rfl, rfl⟩ hy'⟩
  · rintro ⟨hs, hf⟩
    exact Sim20.Pure.typedV_closedCase20 htd rfl (hasTyp_tup2G10 hs hf)

/-- **A frame, field by field.** -/
theorem typedV_frame_iffE (hE : SameTyps B E) {f : Frame} :
    TypedV E frameT (frameV f) ↔
      TypedV E (.iterT (.varT "val" []) .list) (.list (f.locals.map valV)) ∧
        TypedV E (.varT "moduleinst" []) (moduleInstV f.module) := by
  have htd := (hE "frame").trans Whole.findTyp_frame10T
  constructor
  · intro h
    obtain ⟨hL, hf₁⟩ := hasTypFields_cons_nil_iff.1 (hasTypFields_of_closed htd h)
    obtain ⟨hM, -⟩ := hasTypFields_cons_nil_iff.1 hf₁
    exact ⟨typedV_list_of_empty20 hL, typedV_of_empty20 hM⟩
  · rintro ⟨hL, hM⟩
    exact typedV_structG htd (hasTypFields_consG hL (hasTypFields_oneG hM))

/-- The fields of a function instance's image. -/
theorem funcInstV_fields (fi : FuncInst V1.Func H) : ∃ t m c, funcInstV hn fi =
    .struct [("TYPE", t), ("MODULE", moduleInstV m), ("CODE", c)] ∧
    funcInstV hn (stripFI10 fi) =
      .struct [("TYPE", t), ("MODULE", moduleInstV (stripModule10 m)), ("CODE", c)] := by
  cases fi with
  | wasm t m fn => exact ⟨_, m, _, rfl, rfl⟩
  | host t h => exact ⟨_, {}, _, rfl, rfl⟩

/-- **A function instance image with a given module image, field by field.** -/
theorem typedV_funcInst_iffE (hE : SameTyps B E) {t c : Value} {m : ModuleInst} :
    TypedV E (.varT "funcinst" []) (.struct [("TYPE", t), ("MODULE", moduleInstV m), ("CODE", c)]) ↔
      TypedV E (.varT "functype" []) t ∧ TypedV E (.varT "moduleinst" []) (moduleInstV m) ∧
        TypedV E (.varT "func" []) c := by
  have htd := (hE "funcinst").trans findTyp_funcinst10T
  constructor
  · intro h
    obtain ⟨hT, hf₁⟩ := hasTypFields_cons_nil_iff.1 (hasTypFields_of_closed htd h)
    obtain ⟨hM, hf₂⟩ := hasTypFields_cons_nil_iff.1 hf₁
    obtain ⟨hC, -⟩ := hasTypFields_cons_nil_iff.1 hf₂
    exact ⟨typedV_of_empty20 hT, typedV_of_empty20 hM, typedV_of_empty20 hC⟩
  · rintro ⟨hT, hM, hC⟩
    exact typedV_structG htd (hasTypFields_consG hT (hasTypFields_consG hM (hasTypFields_oneG hC)))

/-- **A store, field by field.** -/
theorem typedV_store_iffE (hE : SameTyps B E) {s : Store H} :
    TypedV E storeT (storeV hn s) ↔
      TypedV E (.iterT (.varT "funcinst" []) .list) (.list (s.funcs.map (funcInstV hn))) ∧
      TypedV E (.iterT (.varT "globalinst" []) .list) (.list (s.globals.map globalInstV)) ∧
      TypedV E (.iterT (.varT "tableinst" []) .list) (.list (s.tables.map tableInstV)) ∧
      TypedV E (.iterT (.varT "meminst" []) .list) (.list (s.memories.map memInstV)) := by
  have htd := (hE "store").trans findTyp_store10T
  constructor
  · intro h
    obtain ⟨hF, hf₁⟩ := hasTypFields_cons_nil_iff.1 (hasTypFields_of_closed htd h)
    obtain ⟨hG, hf₂⟩ := hasTypFields_cons_nil_iff.1 hf₁
    obtain ⟨hT, hf₃⟩ := hasTypFields_cons_nil_iff.1 hf₂
    obtain ⟨hM, -⟩ := hasTypFields_cons_nil_iff.1 hf₃
    exact ⟨typedV_list_of_empty20 hF, typedV_list_of_empty20 hG, typedV_list_of_empty20 hT,
      typedV_list_of_empty20 hM⟩
  · rintro ⟨hF, hG, hT, hM⟩
    exact typedV_structG htd (hasTypFields_consG hF (hasTypFields_consG hG
      (hasTypFields_consG hT (hasTypFields_oneG hM))))

/-! ## Stripping, structure by structure -/

/-- **A `moduleinst` of `utf8Env10T B` without its exports is a `moduleinst` of
`simEnv10T B`.** -/
theorem typedV_moduleInst_strip10 (hB : ∀ ws, B.call "utf8" ws = none) {m : ModuleInst}
    (h : TypedV (utf8Env10T B) (.varT "moduleinst" []) (moduleInstV m)) :
    TypedV (simEnv10T B) (.varT "moduleinst" []) (moduleInstV (stripModule10 m)) := by
  have hf := hasTypFields_of_closed ((sameTyps_utf8 B "moduleinst").trans findTyp_moduleinst10T) h
  obtain ⟨hT, hf₁⟩ := hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hF, hf₂⟩ := hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hG, hf₃⟩ := hasTypFields_cons_nil_iff.1 hf₂
  obtain ⟨hTa, hf₄⟩ := hasTypFields_cons_nil_iff.1 hf₃
  obtain ⟨hM, -⟩ := hasTypFields_cons_nil_iff.1 hf₄
  exact typedV_structG findTyp_moduleinst10T
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hT))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hF))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hG))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hTa))
    (hasTypFields_consG (typedV_u10 hB (by decide) (by decide) (typedV_list_of_empty20 hM))
      (hasTypFields_oneG typedV_listNil10))))))

/-- **A function instance of `utf8Env10T B` without its module's exports is one of
`simEnv10T B`.** -/
theorem typedV_funcInst_strip10 (hB : ∀ ws, B.call "utf8" ws = none) {fi : FuncInst V1.Func H}
    (h : TypedV (utf8Env10T B) (.varT "funcinst" []) (funcInstV hn fi)) :
    TypedV (simEnv10T B) (.varT "funcinst" []) (funcInstV hn (stripFI10 fi)) := by
  obtain ⟨t, m, c, he, he'⟩ := funcInstV_fields (hn := hn) fi
  rw [he] at h
  rw [he']
  obtain ⟨hT, hM, hC⟩ := (typedV_funcInst_iffE (sameTyps_utf8 B)).1 h
  exact (typedV_funcInst_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) hT,
    typedV_moduleInst_strip10 hB hM, typedV_u10 hB (by decide) (by decide) hC⟩

/-- **A store of `utf8Env10T B` without exports is a store of `simEnv10T B`.** -/
theorem typedV_store_strip10 (hB : ∀ ws, B.call "utf8" ws = none) {s : Store H}
    (h : TypedV (utf8Env10T B) storeT (storeV hn s)) :
    TypedV (simEnv10T B) storeT (storeV hn (stripStore10 s)) := by
  obtain ⟨hF, hG, hT, hM⟩ := (typedV_store_iffE (sameTyps_utf8 B)).1 h
  refine (typedV_store_iffE (sameTyps_sim B)).2 ⟨?_, typedV_u10 hB (by decide) (by decide) hG,
    typedV_u10 hB (by decide) (by decide) hT, typedV_u10 hB (by decide) (by decide) hM⟩
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨fi, hfi, rfl⟩ : ∃ fi ∈ s.funcs, funcInstV hn (stripFI10 fi) = u := by
    simpa only [stripStore10, List.map_map, List.mem_map, Function.comp_apply] using hu
  exact typedV_funcInst_strip10 hB (Sim.typedV_list_iff.1 hF _ (List.mem_map_of_mem hfi))

/-- **A frame of `utf8Env10T B` without its module's exports is a frame of `simEnv10T B`.** -/
theorem typedV_frame_strip10 (hB : ∀ ws, B.call "utf8" ws = none) {f : Frame}
    (h : TypedV (utf8Env10T B) frameT (frameV f)) :
    TypedV (simEnv10T B) frameT (frameV (stripFrame10 f)) := by
  obtain ⟨hL, hM⟩ := (typedV_frame_iffE (sameTyps_utf8 B)).1 h
  exact (typedV_frame_iffE (sameTyps_sim B)).2
    ⟨typedV_u10 hB (by decide) (by decide) hL, typedV_moduleInst_strip10 hB hM⟩

/-- **A state of `utf8Env10T B` without exports is a state of `simEnv10T B`.** -/
theorem typedV_state_strip10 (hB : ∀ ws, B.call "utf8" ws = none) {s : Store H} {f : Frame}
    (h : TypedV (utf8Env10T B) stateT (stateV hn s f)) :
    TypedV (simEnv10T B) stateT (stateV hn (stripStore10 s) (stripFrame10 f)) := by
  obtain ⟨hs, hf⟩ := (typedV_stV_iffE (sameTyps_utf8 B)).1 h
  exact (typedV_stV_iffE (sameTyps_sim B)).2 ⟨typedV_store_strip10 hB hs, typedV_frame_strip10 hB hf⟩

/-! ## Code -/

/-- **An instruction typed as `admininstr` is typed as `instr`**, in any environment with 1.0's
type table. -/
theorem typedV_instr_of_adminE (hE : SameTyps B E) {i : V1.Instr}
    (h : TypedV E adminT10 (instrToV i)) : TypedV E (.varT "instr" []) (instrToV i) := by
  obtain ⟨ci, ex, hi, ha, hex⟩ := Whole.findTyp_instrAdmin10T (B := B)
  have hi' := (hE "instr").trans hi
  have ha' := (hE "admininstr").trans ha
  obtain ⟨u, hu⟩ := Whole.instrToV_case10 i
  rw [hu] at h ⊢
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed ha' (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  rcases Whole.hasTypCase_append_inv hc with hc' | hm
  · exact fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) hi'
      Equiv.evalArgs_nil matchArgs_nil hc'
  · exact absurd (hex ▸ hm) (Whole.instrHead10_not_admin i)

/-- **A label's arity, continuation and body**, in any environment with 1.0's type table. -/
theorem typedV_label_iffE (hE : SameTyps B E) {n : Nat} {cont : V1.Expr} {body : List Admin} :
    TypedV E adminT10 (adminToV (.label n cont body)) ↔
      TypedV E nT (.num (.natN n)) ∧ TypedV E instrsT (.list (instrsToV cont)) ∧
        TypedV E adminsT (.list (adminsToV body)) := by
  obtain ⟨cs, htd, -, hl, -⟩ := StoreAgree.findTyp_admininstr10TF (B := B)
  have htdE := (hE "admininstr").trans htd
  constructor
  · intro h
    exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htdE (h _ valsOnly_empty) hl)
      (fun hρ hv => typedV_list_of_scope hρ hv)
  · rintro ⟨h₁, h₂, h₃⟩
    exact Sim20.Pure.typedV_closedCase20 htdE hl (hasTyp_tup3G10 h₁ h₂ h₃)

/-- **A frame instruction's arity, frame and body**, in any environment with 1.0's type
table. -/
theorem typedV_frameA_iffE (hE : SameTyps B E) {n : Nat} {f : Frame} {body : List Admin} :
    TypedV E adminT10 (adminToV (.frame n f body)) ↔
      TypedV E nT (.num (.natN n)) ∧ TypedV E frameT (frameV f) ∧
        TypedV E adminsT (.list (adminsToV body)) := by
  obtain ⟨cs, htd, -, -, hf⟩ := StoreAgree.findTyp_admininstr10TF (B := B)
  have htdE := (hE "admininstr").trans htd
  constructor
  · intro h
    exact hasTyp_tup3_inv (hasTyp_closedVariant_inv valsOnly_empty htdE (h _ valsOnly_empty) hf)
      (fun hρ hv => typedV_of_scope hρ hv)
  · rintro ⟨h₁, h₂, h₃⟩
    exact Sim20.Pure.typedV_closedCase20 htdE hf (hasTyp_tup3G10 h₁ h₂ h₃)

mutual
/-- **An `admininstr` of `utf8Env10T B` with the exports of its frames removed is an
`admininstr` of `simEnv10T B`.** -/
theorem typedV_admin_strip10 (hB : ∀ ws, B.call "utf8" ws = none) : ∀ a : Admin,
    TypedV (utf8Env10T B) adminT10 (adminToV a) →
      TypedV (simEnv10T B) adminT10 (adminToV (stripAdmin10 a))
  | .source i, h => Whole.typedV_admin_of_instr10T
      (typedV_u10 hB (by decide) (by decide) (typedV_instr_of_adminE (sameTyps_utf8 B) h))
  | .invoke a, _ => Whole.typedV_invoke10T a
  | .trap, _ => Whole.typedV_trap10T
  | .label n cont body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_label_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_label_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) h₁,
      typedV_u10 hB (by decide) (by decide) h₂, typedV_admins_strip10 hB body h₃⟩
  | .frame n f body, h => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_frameA_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_frameA_iffE (sameTyps_sim B)).2 ⟨typedV_u10 hB (by decide) (by decide) h₁,
      typedV_frame_strip10 hB h₂, typedV_admins_strip10 hB body h₃⟩

/-- `typedV_admin_strip10` on a sequence. -/
theorem typedV_admins_strip10 (hB : ∀ ws, B.call "utf8" ws = none) : ∀ l : List Admin,
    TypedV (utf8Env10T B) adminsT (.list (adminsToV l)) →
      TypedV (simEnv10T B) adminsT (.list (adminsToV (stripAdmins10 l)))
  | [], _ => typedV_listNil10
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2 ⟨typedV_admin_strip10 hB a ha, typedV_admins_strip10 hB l hl⟩
end

/-- **Leg 2 for 1.0: a configuration typed in `utf8Env10T B`, with its exports removed, is typed
in `simEnv10T B`.** -/
theorem typed10_strip (hB : ∀ ws, B.call "utf8" ws = none) {c : Config H}
    (h : Typed10 (utf8Env10T B) hn c) : Typed10 (simEnv10T B) hn (stripConfig10 c) := by
  obtain ⟨hz, hc⟩ := (typed10_iffE (sameTyps_utf8 B)).1 h
  exact (typed10_iffE (sameTyps_sim B)).2
    ⟨typedV_state_strip10 hB hz, typedV_admins_strip10 hB c.code hc⟩

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
