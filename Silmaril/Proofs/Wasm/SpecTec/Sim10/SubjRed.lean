module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdRestP
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.CallIndirectTrap

/-!
# Subject reduction for the image of the 1.0 fragment

`Task.wholeStepNest10` (pass 1) assumes the successor configuration's image is typed. This
module proves it is: every `Nest10 Leaf10F` step from a configuration whose image is IL-typed
leads to one whose image is IL-typed (`typed10_of_nest`), at every builtins. So the stronger
**`wholeStepNest10'`** (no successor hypothesis) holds.

The image typing is taken apart and put back together along the 1.0 type definitions:

* `typed10_iff`: `config = state; admininstr*`;
* `frame = {LOCALS val*, MODULE moduleinst}`, `globalinst = {TYPE globaltype, VALUE val}` and the
  `GLOBALS` field of `store` (`findTyp_frame10`, …, kernel `rfl`); a frame with a local replaced
  by a typed value stays typed (`typedV_frameV_setLocal10`);
* the new code: `[]`, `[TRAP]`, a value (`typedV_admin_of_val10`, the converse of pass 1's
  `typedV_val_of_admin10`), `CALL_ADDR a`, `LOCAL.SET x`, `BR l`, and a label or frame around
  typed pieces (`typedV_label10`, `typedV_frame10`);
* the closure under V1's `context`, `label` and `frame` (`subjRed10_nest`).

The generic record and list lemmas are 2.0's (`Sim20.Whole.typedV_struct2`, …).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT storeT frameT nT instrsT typedV_list_iff
  typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (typedV_struct2 hasTyp_struct2_fst hasTyp_struct2_snd
  typedV_list_set20 typedV_list_of_empty20 typedV_of_getElem?)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The 1.0 type definitions used -/

set_option maxRecDepth 8000000 in
theorem findTyp_frame10 : (simEnv10 B).findTyp? "frame" = some ([], [.instD [] []
    (.structT [.mk "LOCALS" (.iterT (.varT "val" []) .list) [] [],
      .mk "MODULE" (.varT "moduleinst" []) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_globalinst10 : (simEnv10 B).findTyp? "globalinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "globaltype" []) [] [], .mk "VALUE" (.varT "val" []) [] []])]) :=
  rfl

set_option maxRecDepth 8000000 in
theorem findTyp_storeG10 : ∃ t₁ t₃ t₄, (simEnv10 B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" t₁ [] [], .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" t₃ [] [], .mk "MEMS" t₄ [] []])]) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
theorem findTyp_admininstr10_sr : ∃ cs, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "TRAP" = some (.tupT [], []) ∧
    findCase cs "CALL_ADDR" = some (.varT "funcaddr" [], []) ∧
    findCase cs "LOCAL.SET" = some (.varT "localidx" [], []) ∧
    findCase cs "BR" = some (.varT "labelidx" [], []) ∧
    findCase cs "CONST" = some (constT10, []) ∧
    findCase cs "LABEL_%{%}%" = some (labelT10, []) ∧
    findCase cs "FRAME_%{%}%" = some (frameCaseT10, []) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8000000 in
theorem findTyp_funcaddr10 : (simEnv10 B).findTyp? "funcaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl

/-! ## `config` and the state -/

/-- **A configuration image is typed exactly when its state and code are.** -/
theorem typed10_iff {c : Config H} :
    Typed10 (simEnv10 B) hn c ↔ TypedV (simEnv10 B) stateT (stateV hn c.store c.frame) ∧
      TypedV (simEnv10 B) adminsT (.list (adminsToV c.code)) := by
  refine ⟨fun h => ⟨typedV_state_of_typed10 h, typedV_code_of_typed10 h⟩, fun ⟨hz, hc⟩ => ?_⟩
  exact Sim20.Pure.typedV_closedCase20 findTyp_config10 rfl (hasTyp_tup2G10 hz hc) _
    valsOnly_empty

/-- The frame of a typed state. -/
theorem typedV_frame_of_state10 {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10 B) stateT (stateV hn s f)) : TypedV (simEnv10 B) frameT (frameV f) :=
  (typedV_stV_iff10.1 hz).2

/-- The locals of a typed frame are typed values. -/
theorem typedV_locals10 {f : Frame} (hf : TypedV (simEnv10 B) frameT (frameV f)) :
    TypedV (simEnv10 B) (.iterT (.varT "val" []) .list) (.list (f.locals.map valV)) :=
  typedV_list_of_empty20 (hasTyp_struct2_fst findTyp_frame10 hf)

/-- **A frame with a local replaced by a typed value.** -/
theorem typedV_frameV_setLocal10 {f : Frame} (hf : TypedV (simEnv10 B) frameT (frameV f))
    (i : Nat) {v : Execution.Runtime.Value} (hv : TypedV (simEnv10 B) (.varT "val" []) (valV v)) :
    TypedV (simEnv10 B) frameT (frameV { f with locals := f.locals.set i v }) := by
  have hl : TypedV (simEnv10 B) (.iterT (.varT "val" []) .list)
      (.list ((f.locals.set i v).map valV)) := typedV_list_set20 (typedV_locals10 hf) hv
  exact typedV_struct2 findTyp_frame10 (hl _ valsOnly_empty)
    (hasTyp_struct2_snd findTyp_frame10 hf)

/-- The globals of a typed store are typed global instances. -/
theorem typedV_globals10 {s : Store H} (hs : TypedV (simEnv10 B) storeT (storeV hn s)) :
    TypedV (simEnv10 B) (.iterT (.varT "globalinst" []) .list)
      (.list (s.globals.map globalInstV)) := by
  obtain ⟨t₁, t₃, t₄, htd⟩ := findTyp_storeG10 (B := B)
  have hfs := Sim20.Whole.hasTypFields_of_closed htd hs
  obtain ⟨w₁, gs₁, he₁, -, -, hfs₁⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨-, rfl⟩ := List.cons.inj he₁
  obtain ⟨w, gs₂, he₂, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs₁
  obtain ⟨he₂', -⟩ := List.cons.inj he₂
  obtain rfl := (Prod.mk.inj he₂').2
  exact typedV_list_of_empty20 hw

/-- The value of a typed global instance is a typed value. -/
theorem typedV_globalValue10 {g : GlobalInst}
    (hg : TypedV (simEnv10 B) (.varT "globalinst" []) (globalInstV g)) :
    TypedV (simEnv10 B) (.varT "val" []) (valV g.value) :=
  Sim20.Whole.typedV_of_empty20 (hasTyp_struct2_snd findTyp_globalinst10 hg)

/-! ## The new code -/

/-- **A typed value is a typed `admininstr`.** -/
theorem typedV_admin_of_val10 {v : Execution.Runtime.Value}
    (h : TypedV (simEnv10 B) (.varT "val" []) (valV v)) :
    TypedV (simEnv10 B) adminT10 (adminToV (value v)) := by
  obtain ⟨cs, htd, -, -, -, -, hc, -, -⟩ := findTyp_admininstr10_sr (B := B)
  obtain ⟨cs', htd', hc'⟩ := findTyp_val10F (B := B)
  rw [adminToV_value]
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (hasTyp_closedVariant_inv valsOnly_empty htd' (h _ valsOnly_empty) hc')

/-- Code from typed pieces. -/
theorem typedV_admins_of10 {l : List Admin}
    (h : ∀ a ∈ l, TypedV (simEnv10 B) adminT10 (adminToV a)) :
    TypedV (simEnv10 B) adminsT (.list (adminsToV l)) := by
  rw [adminsToV_map10]
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  exact h a ha

/-- The elements of typed code are typed. -/
theorem typedV_admin_of_mem10 {l : List Admin} (h : TypedV (simEnv10 B) adminsT
    (.list (adminsToV l))) {a : Admin} (ha : a ∈ l) : TypedV (simEnv10 B) adminT10 (adminToV a) := by
  rw [adminsToV_map10] at h
  exact typedV_list_iff.1 h _ (List.mem_map_of_mem ha)

theorem typedV_trap10 : TypedV (simEnv10 B) adminT10 (adminToV .trap) := by
  obtain ⟨cs, htd, ht, -⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd ht hasTyp_tupT_nil

theorem typedV_invoke10 (a : Execution.Runtime.FuncAddr) :
    TypedV (simEnv10 B) adminT10 (adminToV (.invoke a)) := by
  obtain ⟨cs, htd, -, hc, -⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (typedV_aliasG10 findTyp_funcaddr10 (typedV_addr10 a.value _ valsOnly_empty) _ valsOnly_empty)

theorem typedV_localSet10 (x : LocalIdx) :
    TypedV (simEnv10 B) adminT10 (adminToV (.source (.localSet x))) := by
  obtain ⟨cs, htd, -, -, hc, -⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (typedV_aliasG10 findTyp_localidx10 (typedV_idxAll10 x _ valsOnly_empty) _ valsOnly_empty)

theorem typedV_br10 (l : LabelIdx) :
    TypedV (simEnv10 B) adminT10 (adminToV (.source (.br l))) := by
  obtain ⟨cs, htd, -, -, -, hc, -⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc (typedV_labelidx10 l _ valsOnly_empty)

/-- A triple of typed components, for `LABEL_` and `FRAME_`. -/
theorem hasTyp_tup3G10 {env : Env} {a b c : IL.Id} {τ₁ τ₂ τ₃ : Typ} {u v w : Value}
    (h₁ : TypedV env τ₁ u) (h₂ : TypedV env τ₂ v) (h₃ : TypedV env τ₃ w) :
    HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂, .mk c τ₃]) (.tuple [u, v, w]) :=
  hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩

/-- **A label around typed pieces.** -/
theorem typedV_label10 {n : Nat} {cont : V1.Expr} {body : List Admin}
    (hc : TypedV (simEnv10 B) instrsT (.list (instrsToV cont)))
    (hb : TypedV (simEnv10 B) adminsT (.list (adminsToV body))) :
    TypedV (simEnv10 B) adminT10 (adminToV (.label n cont body)) := by
  obtain ⟨cs, htd, -, -, -, -, -, hl, -⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hl (hasTyp_tup3G10 (typedV_n10 n) hc hb)

/-- **A frame around typed pieces.** -/
theorem typedV_frame10 {n : Nat} {fr : Frame} {body : List Admin}
    (hf : TypedV (simEnv10 B) frameT (frameV fr))
    (hb : TypedV (simEnv10 B) adminsT (.list (adminsToV body))) :
    TypedV (simEnv10 B) adminT10 (adminToV (.frame n fr body)) := by
  obtain ⟨cs, htd, -, -, -, -, -, -, hfr⟩ := findTyp_admininstr10_sr (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hfr (hasTyp_tup3G10 (typedV_n10 n) hf hb)

/-! ## The leaves -/

/-- The state and code of a configuration image are typed. -/
def TS10 (B : Builtins) (hn : H → String) (c : Config H) : Prop :=
  TypedV (simEnv10 B) stateT (stateV hn c.store c.frame) ∧
    TypedV (simEnv10 B) adminsT (.list (adminsToV c.code))

/-- The new code of a leaf that keeps the state, from typed elements. -/
theorem ts10_keep {s : Store H} {f : Frame} {code code' : List Admin}
    (h : TS10 B hn ⟨s, f, code⟩)
    (h' : ∀ a ∈ code', TypedV (simEnv10 B) adminT10 (adminToV a)) : TS10 B hn ⟨s, f, code'⟩ :=
  ⟨h.1, typedV_admins_of10 h'⟩

/-- **Subject reduction at the sixteen leaves.** -/
theorem subjRed10_leaf {c c' : Config H} (hl : Leaf10F c c') (h : TS10 B hn c) :
    TS10 B hn c' := by
  have hm : ∀ {a : Admin}, a ∈ c.code → TypedV (simEnv10 B) adminT10 (adminToV a) :=
    fun ha => typedV_admin_of_mem10 h.2 ha
  cases hl with
  | unreachable s f => exact ts10_keep h (by simpa using typedV_trap10)
  | nop s f => exact ts10_keep h (by simp)
  | drop s f v => exact ts10_keep h (by simp)
  | localGet s f x v hv =>
    have hv' : TypedV (simEnv10 B) (.varT "val" []) (valV v) :=
      typedV_of_getElem? (typedV_locals10 (typedV_frame_of_state10 h.1)) hv
    exact ts10_keep h (by simpa using typedV_admin_of_val10 hv')
  | globalGet s f x a g ha hg =>
    have hg' : TypedV (simEnv10 B) (.varT "globalinst" []) (globalInstV g) :=
      typedV_of_getElem? (typedV_globals10 (typedV_stV_iff10.1 h.1).1) hg
    exact ts10_keep h (by simpa using typedV_admin_of_val10 (typedV_globalValue10 hg'))
  | call s f x a ha => exact ts10_keep h (by simpa using typedV_invoke10 a)
  | localSet s f x v old hold =>
    have hv : TypedV (simEnv10 B) (.varT "val" []) (valV v) := typedV_val_of_head10 h.2
    obtain ⟨hs, hf⟩ := typedV_stV_iff10.1 h.1
    exact ⟨typedV_stV_iff10.2 ⟨hs, typedV_frameV_setLocal10 hf x.toNat hv⟩,
      typedV_admins_of10 (by simp)⟩
  | labelDone s f n cont vs =>
    exact ⟨h.1, (label_inv10 (hm (List.mem_singleton_self _))).2.2⟩
  | frameDone s f fr vs =>
    exact ⟨h.1, (frame_inv10 (hm (List.mem_singleton_self _))).2.2⟩
  | labelTrap s f n cont => exact ts10_keep h (by simpa using typedV_trap10)
  | frameTrap s f fr n => exact ts10_keep h (by simpa using typedV_trap10)
  | localTee s f x v =>
    have hv := hm (List.mem_cons_self ..)
    exact ts10_keep h (by simpa using ⟨hv, typedV_localSet10 x⟩)
  | brIfZero s f l => exact ts10_keep h (by simp)
  | brIfNonzero s f l c hc => exact ts10_keep h (by simpa using typedV_br10 l)
  | selectZero s f a b _ =>
    exact ts10_keep h (by simpa using hm (by simp : value b ∈ [value a, value b,
      value (.int .i32 0), .source .select]))
  | selectNonzero s f a b _ c _ =>
    exact ts10_keep h (by simpa using hm (by simp : value a ∈ [value a, value b,
      value (.int .i32 c), .source .select]))

/-! ## Nesting -/

/-- Subject reduction through V1's `context`. -/
theorem ts10_context {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (vs : List Execution.Runtime.Value) (tail : List Admin)
    (hc : TS10 B hn ⟨s, f, values vs ++ before ++ tail⟩)
    (ih : TS10 B hn ⟨s, f, before⟩ → TS10 B hn ⟨s', f', after⟩) :
    TS10 B hn ⟨s', f', values vs ++ after ++ tail⟩ := by
  have hw : TypedV (simEnv10 B) adminsT
      (.list (adminsToV (values vs) ++ adminsToV before ++ adminsToV tail)) := by
    rw [← adminsToV_append3]
    exact hc.2
  obtain ⟨hvb, ht⟩ := typedV_list_append.1 hw
  obtain ⟨hv, hb⟩ := typedV_list_append.1 hvb
  obtain ⟨hz', ha⟩ := ih ⟨hc.1, hb⟩
  refine ⟨hz', ?_⟩
  rw [adminsToV_append3]
  exact typedV_list_append.2 ⟨typedV_list_append.2 ⟨hv, ha⟩, ht⟩

/-- Subject reduction through V1's `label`. -/
theorem ts10_label {s s' : Store H} {f f' : Frame} {before after : List Admin} (n : Nat)
    (cont : V1.Expr) (hc : TS10 B hn ⟨s, f, [.label n cont before]⟩)
    (ih : TS10 B hn ⟨s, f, before⟩ → TS10 B hn ⟨s', f', after⟩) :
    TS10 B hn ⟨s', f', [.label n cont after]⟩ := by
  obtain ⟨-, hcont, hb⟩ := label_inv10 (typedV_admin_of_mem10 hc.2 (List.mem_singleton_self _))
  obtain ⟨hz', ha⟩ := ih ⟨hc.1, hb⟩
  exact ⟨hz', typedV_admins_of10 (by simpa using typedV_label10 hcont ha)⟩

/-- Subject reduction through V1's `frame`. -/
theorem ts10_frame {s s' : Store H} {inner inner' : Frame} {before after : List Admin} (n : Nat)
    (outer : Frame) (hc : TS10 B hn ⟨s, outer, [.frame n inner before]⟩)
    (ih : TS10 B hn ⟨s, inner, before⟩ → TS10 B hn ⟨s', inner', after⟩) :
    TS10 B hn ⟨s', outer, [.frame n inner' after]⟩ := by
  obtain ⟨-, hi, hb⟩ := frame_inv10 (typedV_admin_of_mem10 hc.2 (List.mem_singleton_self _))
  obtain ⟨hs, ho⟩ := typedV_stV_iff10.1 hc.1
  obtain ⟨hz', ha⟩ := ih ⟨typedV_stV_iff10.2 ⟨hs, hi⟩, hb⟩
  obtain ⟨hs', hi'⟩ := typedV_stV_iff10.1 hz'
  exact ⟨typedV_stV_iff10.2 ⟨hs', ho⟩, typedV_admins_of10 (by simpa using typedV_frame10 hi' ha)⟩

/-- **Subject reduction passes from the leaves to every nesting.** -/
theorem subjRed10_nest {L : Config H → Config H → Prop}
    (hL : ∀ c c', L c c' → TS10 B hn c → TS10 B hn c') {c c' : Config H} (h : Nest10 L c c')
    (hc : TS10 B hn c) : TS10 B hn c' := by
  induction h with
  | leaf h => exact hL _ _ h hc
  | context _ vs tail ih => exact ts10_context vs tail hc ih
  | label _ n cont ih => exact ts10_label n cont hc ih
  | frame _ n outer ih => exact ts10_frame n outer hc ih

/-- **Subject reduction for the fragment**: a `Nest10 Leaf10F` step from a typed image leads to
a typed image. -/
theorem typed10_of_nest {c c' : Config H} (h : Nest10 Leaf10F c c')
    (hc : Typed10 (simEnv10 B) hn c) : Typed10 (simEnv10 B) hn c' :=
  typed10_iff.2 (subjRed10_nest (fun _ _ hl => subjRed10_leaf hl) h (typed10_iff.1 hc))

/-- **`Task.wholeStepNest10` without the successor hypothesis**: at every builtins, every
`Nest10 Leaf10F` step from a configuration whose image is typed is a step of the wasm-1.0 script
between the images. -/
theorem wholeStepNest10' (H : Type) (hn : H → String) (B : Builtins) (c c' : Config H)
    (hc : Typed10 (simEnv10 B) hn c) (h : Nest10 Leaf10F c c') :
    SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  wholeStepNest10 H hn B c c' hc (typed10_of_nest h hc) h

end Silmaril.Wasm.SpecTec.Sim10.Whole
