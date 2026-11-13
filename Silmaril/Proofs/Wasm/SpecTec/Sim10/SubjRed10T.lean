module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdWhole10T

/-! -/

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
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly instrsT typedV_list_iff typedV_list_append)
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression frameMemory setGlobal setMemory)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst MemInst ModuleInst FuncInst)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly stateT storeT frameT instrsT typedV_list_iff)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim20.Whole (typedV_struct2 hasTyp_struct2_fst hasTyp_struct2_snd
  typedV_list_set20 typedV_list_of_empty20 typedV_of_empty20 typedV_of_getElem?
  hasTypFields_cons_nil_iff hasTypFields_of_closed)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.V1.Execution (frameMemory setMemory setGlobal storeInt storeFloat)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

set_option maxRecDepth 8000000 in
theorem findTyp_globalinst10T : (simEnv10T B).findTyp? "globalinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "globaltype" []) [] [], .mk "VALUE" (.varT "val" []) [] []])]) :=
  rfl

set_option maxRecDepth 8000000 in
theorem findTyp_storeG10T : ∃ t₁ t₃ t₄, (simEnv10T B).findTyp? "store" = some ([], [.instD [] []
    (.structT [.mk "FUNCS" t₁ [] [], .mk "GLOBALS" (.iterT (.varT "globalinst" []) .list) [] [],
      .mk "TABLES" t₃ [] [], .mk "MEMS" t₄ [] []])]) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
theorem findTyp_admininstr10_srT : ∃ cs, (simEnv10T B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧ findCase cs "TRAP" = some (.tupT [], []) ∧
    findCase cs "CALL_ADDR" = some (.varT "funcaddr" [], []) ∧
    findCase cs "LOCAL.SET" = some (.varT "localidx" [], []) ∧
    findCase cs "BR" = some (.varT "labelidx" [], []) ∧
    findCase cs "CONST" = some (constT10, []) ∧
    findCase cs "LABEL_%{%}%" = some (labelT10, []) ∧
    findCase cs "FRAME_%{%}%" = some (frameCaseT10, []) :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8000000 in
theorem findTyp_funcaddr10T : (simEnv10T B).findTyp? "funcaddr" =
    some ([], [.instD [] [] (.aliasT (.varT "addr" []))]) := rfl

/-- **A configuration image is typed exactly when its state and code are.** -/
theorem typed10_iffT {c : Config H} :
    Typed10 (simEnv10T B) hn c ↔ TypedV (simEnv10T B) stateT (stateV hn c.store c.frame) ∧
      TypedV (simEnv10T B) adminsT (.list (adminsToV c.code)) := by
  refine ⟨fun h => ⟨typedV_state_of_typed10T h, typedV_code_of_typed10T h⟩, fun ⟨hz, hc⟩ => ?_⟩
  exact Sim20.Pure.typedV_closedCase20 StoreAgree.findTyp_config10T rfl (hasTyp_tup2G10 hz hc) _
    valsOnly_empty

/-- The frame of a typed state. -/
theorem typedV_frame_of_state10T {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) : TypedV (simEnv10T B) frameT (frameV f) :=
  (typedV_stV_iff10T.1 hz).2

/-- The locals of a typed frame are typed values. -/
theorem typedV_locals10T {f : Frame} (hf : TypedV (simEnv10T B) frameT (frameV f)) :
    TypedV (simEnv10T B) (.iterT (.varT "val" []) .list) (.list (f.locals.map valV)) :=
  typedV_list_of_empty20 (hasTyp_struct2_fst findTyp_frame10T hf)

/-- **A frame with a local replaced by a typed value.** -/
theorem typedV_frameV_setLocal10T {f : Frame} (hf : TypedV (simEnv10T B) frameT (frameV f))
    (i : Nat) {v : Execution.Runtime.Value} (hv : TypedV (simEnv10T B) (.varT "val" []) (valV v)) :
    TypedV (simEnv10T B) frameT (frameV { f with locals := f.locals.set i v }) := by
  have hl : TypedV (simEnv10T B) (.iterT (.varT "val" []) .list)
      (.list ((f.locals.set i v).map valV)) := typedV_list_set20 (typedV_locals10T hf) hv
  exact typedV_struct2 findTyp_frame10T (hl _ valsOnly_empty)
    (hasTyp_struct2_snd findTyp_frame10T hf)

/-- The globals of a typed store are typed global instances. -/
theorem typedV_globals10T {s : Store H} (hs : TypedV (simEnv10T B) storeT (storeV hn s)) :
    TypedV (simEnv10T B) (.iterT (.varT "globalinst" []) .list)
      (.list (s.globals.map globalInstV)) := by
  obtain ⟨t₁, t₃, t₄, htd⟩ := findTyp_storeG10T (B := B)
  have hfs := Sim20.Whole.hasTypFields_of_closed htd hs
  obtain ⟨w₁, gs₁, he₁, -, -, hfs₁⟩ := hasTypFields_cons_iff.1 hfs
  obtain ⟨-, rfl⟩ := List.cons.inj he₁
  obtain ⟨w, gs₂, he₂, hw, -, -⟩ := hasTypFields_cons_iff.1 hfs₁
  obtain ⟨he₂', -⟩ := List.cons.inj he₂
  obtain rfl := (Prod.mk.inj he₂').2
  exact typedV_list_of_empty20 hw

/-- The value of a typed global instance is a typed value. -/
theorem typedV_globalValue10T {g : GlobalInst}
    (hg : TypedV (simEnv10T B) (.varT "globalinst" []) (globalInstV g)) :
    TypedV (simEnv10T B) (.varT "val" []) (valV g.value) :=
  Sim20.Whole.typedV_of_empty20 (hasTyp_struct2_snd findTyp_globalinst10T hg)

/-- **A typed value is a typed `admininstr`.** -/
theorem typedV_admin_of_val10T {v : Execution.Runtime.Value}
    (h : TypedV (simEnv10T B) (.varT "val" []) (valV v)) :
    TypedV (simEnv10T B) adminT10 (adminToV (value v)) := by
  obtain ⟨cs, htd, -, -, -, -, hc, -, -⟩ := findTyp_admininstr10_srT (B := B)
  obtain ⟨cs', htd', hc'⟩ := StoreAgree.findTyp_val10TF (B := B)
  rw [adminToV_value]
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (hasTyp_closedVariant_inv valsOnly_empty htd' (h _ valsOnly_empty) hc')

/-- Code from typed pieces. -/
theorem typedV_admins_of10T {l : List Admin}
    (h : ∀ a ∈ l, TypedV (simEnv10T B) adminT10 (adminToV a)) :
    TypedV (simEnv10T B) adminsT (.list (adminsToV l)) := by
  rw [adminsToV_map10]
  refine typedV_list_iff.2 fun u hu => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  exact h a ha

theorem typedV_trap10T : TypedV (simEnv10T B) adminT10 (adminToV .trap) := by
  obtain ⟨cs, htd, ht, -⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd ht hasTyp_tupT_nil

theorem typedV_invoke10T (a : Execution.Runtime.FuncAddr) :
    TypedV (simEnv10T B) adminT10 (adminToV (.invoke a)) := by
  obtain ⟨cs, htd, -, hc, -⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (typedV_aliasG10 findTyp_funcaddr10T (typedV_addr10T a.value _ valsOnly_empty) _ valsOnly_empty)

theorem typedV_localSet10T (x : LocalIdx) :
    TypedV (simEnv10T B) adminT10 (adminToV (.source (.localSet x))) := by
  obtain ⟨cs, htd, -, -, hc, -⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc
    (typedV_aliasG10 findTyp_localidx10T (typedV_idxAll10T x _ valsOnly_empty) _ valsOnly_empty)

theorem typedV_br10T (l : LabelIdx) :
    TypedV (simEnv10T B) adminT10 (adminToV (.source (.br l))) := by
  obtain ⟨cs, htd, -, -, -, hc, -⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hc (typedV_labelidx10T l _ valsOnly_empty)

/-- **A label around typed pieces.** -/
theorem typedV_label10T {n : Nat} {cont : V1.Expr} {body : List Admin}
    (hc : TypedV (simEnv10T B) instrsT (.list (instrsToV cont)))
    (hb : TypedV (simEnv10T B) adminsT (.list (adminsToV body))) :
    TypedV (simEnv10T B) adminT10 (adminToV (.label n cont body)) := by
  obtain ⟨cs, htd, -, -, -, -, -, hl, -⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hl (hasTyp_tup3G10 (typedV_n10T n) hc hb)

/-- **A frame around typed pieces.** -/
theorem typedV_frame10T {n : Nat} {fr : Frame} {body : List Admin}
    (hf : TypedV (simEnv10T B) frameT (frameV fr))
    (hb : TypedV (simEnv10T B) adminsT (.list (adminsToV body))) :
    TypedV (simEnv10T B) adminT10 (adminToV (.frame n fr body)) := by
  obtain ⟨cs, htd, -, -, -, -, -, -, hfr⟩ := findTyp_admininstr10_srT (B := B)
  exact Sim20.Pure.typedV_closedCase20 htd hfr (hasTyp_tup3G10 (typedV_n10T n) hf hb)

/-- The state and code of a configuration image are typed. -/
def TS10T (B : Builtins) (hn : H → String) (c : Config H) : Prop :=
  TypedV (simEnv10T B) stateT (stateV hn c.store c.frame) ∧
    TypedV (simEnv10T B) adminsT (.list (adminsToV c.code))

/-- The new code of a leaf that keeps the state, from typed elements. -/
theorem ts10_keepT {s : Store H} {f : Frame} {code code' : List Admin}
    (h : TS10T B hn ⟨s, f, code⟩)
    (h' : ∀ a ∈ code', TypedV (simEnv10T B) adminT10 (adminToV a)) : TS10T B hn ⟨s, f, code'⟩ :=
  ⟨h.1, typedV_admins_of10T h'⟩

/-- **Subject reduction at the sixteen leaves.** -/
theorem subjRed10_leafT {c c' : Config H} (hl : Leaf10F c c') (h : TS10T B hn c) :
    TS10T B hn c' := by
  have hm : ∀ {a : Admin}, a ∈ c.code → TypedV (simEnv10T B) adminT10 (adminToV a) :=
    fun ha => typedV_admin_of_mem10T h.2 ha
  cases hl with
  | unreachable s f => exact ts10_keepT h (by simpa using typedV_trap10T)
  | nop s f => exact ts10_keepT h (by simp)
  | drop s f v => exact ts10_keepT h (by simp)
  | localGet s f x v hv =>
    have hv' : TypedV (simEnv10T B) (.varT "val" []) (valV v) :=
      typedV_of_getElem? (typedV_locals10T (typedV_frame_of_state10T h.1)) hv
    exact ts10_keepT h (by simpa using typedV_admin_of_val10T hv')
  | globalGet s f x a g ha hg =>
    have hg' : TypedV (simEnv10T B) (.varT "globalinst" []) (globalInstV g) :=
      typedV_of_getElem? (typedV_globals10T (typedV_stV_iff10T.1 h.1).1) hg
    exact ts10_keepT h (by simpa using typedV_admin_of_val10T (typedV_globalValue10T hg'))
  | call s f x a ha => exact ts10_keepT h (by simpa using typedV_invoke10T a)
  | localSet s f x v old hold =>
    have hv : TypedV (simEnv10T B) (.varT "val" []) (valV v) := typedV_val_of_head10T h.2
    obtain ⟨hs, hf⟩ := typedV_stV_iff10T.1 h.1
    exact ⟨typedV_stV_iff10T.2 ⟨hs, typedV_frameV_setLocal10T hf x.toNat hv⟩,
      typedV_admins_of10T (by simp)⟩
  | labelDone s f n cont vs =>
    exact ⟨h.1, (label_inv10T (hm (List.mem_singleton_self _))).2.2⟩
  | frameDone s f fr vs =>
    exact ⟨h.1, (frame_inv10T (hm (List.mem_singleton_self _))).2.2⟩
  | labelTrap s f n cont => exact ts10_keepT h (by simpa using typedV_trap10T)
  | frameTrap s f fr n => exact ts10_keepT h (by simpa using typedV_trap10T)
  | localTee s f x v =>
    have hv := hm (List.mem_cons_self ..)
    exact ts10_keepT h (by simpa using ⟨hv, typedV_localSet10T x⟩)
  | brIfZero s f l => exact ts10_keepT h (by simp)
  | brIfNonzero s f l c hc => exact ts10_keepT h (by simpa using typedV_br10T l)
  | selectZero s f a b _ =>
    exact ts10_keepT h (by simpa using hm (by simp : value b ∈ [value a, value b,
      value (.int .i32 0), .source .select]))
  | selectNonzero s f a b _ c _ =>
    exact ts10_keepT h (by simpa using hm (by simp : value a ∈ [value a, value b,
      value (.int .i32 c), .source .select]))

/-- Subject reduction through V1's `context`. -/
theorem ts10_contextT {s s' : Store H} {f f' : Frame} {before after : List Admin}
    (vs : List Execution.Runtime.Value) (tail : List Admin)
    (hc : TS10T B hn ⟨s, f, values vs ++ before ++ tail⟩)
    (ih : TS10T B hn ⟨s, f, before⟩ → TS10T B hn ⟨s', f', after⟩) :
    TS10T B hn ⟨s', f', values vs ++ after ++ tail⟩ := by
  have hw : TypedV (simEnv10T B) adminsT
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
theorem ts10_labelT {s s' : Store H} {f f' : Frame} {before after : List Admin} (n : Nat)
    (cont : V1.Expr) (hc : TS10T B hn ⟨s, f, [.label n cont before]⟩)
    (ih : TS10T B hn ⟨s, f, before⟩ → TS10T B hn ⟨s', f', after⟩) :
    TS10T B hn ⟨s', f', [.label n cont after]⟩ := by
  obtain ⟨-, hcont, hb⟩ := label_inv10T (typedV_admin_of_mem10T hc.2 (List.mem_singleton_self _))
  obtain ⟨hz', ha⟩ := ih ⟨hc.1, hb⟩
  exact ⟨hz', typedV_admins_of10T (by simpa using typedV_label10T hcont ha)⟩

/-- Subject reduction through V1's `frame`. -/
theorem ts10_frameT {s s' : Store H} {inner inner' : Frame} {before after : List Admin} (n : Nat)
    (outer : Frame) (hc : TS10T B hn ⟨s, outer, [.frame n inner before]⟩)
    (ih : TS10T B hn ⟨s, inner, before⟩ → TS10T B hn ⟨s', inner', after⟩) :
    TS10T B hn ⟨s', outer, [.frame n inner' after]⟩ := by
  obtain ⟨-, hi, hb⟩ := frame_inv10T (typedV_admin_of_mem10T hc.2 (List.mem_singleton_self _))
  obtain ⟨hs, ho⟩ := typedV_stV_iff10T.1 hc.1
  obtain ⟨hz', ha⟩ := ih ⟨typedV_stV_iff10T.2 ⟨hs, hi⟩, hb⟩
  obtain ⟨hs', hi'⟩ := typedV_stV_iff10T.1 hz'
  exact ⟨typedV_stV_iff10T.2 ⟨hs', ho⟩, typedV_admins_of10T (by simpa using typedV_frame10T hi' ha)⟩

/-- **Subject reduction passes from the leaves to every nesting.** -/
theorem subjRed10_nestT {L : Config H → Config H → Prop}
    (hL : ∀ c c', L c c' → TS10T B hn c → TS10T B hn c') {c c' : Config H} (h : Nest10 L c c')
    (hc : TS10T B hn c) : TS10T B hn c' := by
  induction h with
  | leaf h => exact hL _ _ h hc
  | context _ vs tail ih => exact ts10_contextT vs tail hc ih
  | label _ n cont ih => exact ts10_labelT n cont hc ih
  | frame _ n outer ih => exact ts10_frameT n outer hc ih

/-- **Every V1 value is a typed `val`** of the 1.0 script (a hypothesis here; integers are
always typed, floats need 1.0's `fN`). -/
def ValTyped10T (B : Builtins) : Prop :=
  ∀ v : Execution.Runtime.Value, TypedV (simEnv10T B) (.varT "val" []) (valV v)

/-- Code typed as `admininstr*`. -/
abbrev CodeTy10T (B : Builtins) (l : List Admin) : Prop :=
  TypedV (simEnv10T B) adminsT (.list (adminsToV l))

/-- Code all of whose elements are pieces of typed code is typed. -/
theorem codeTy10_subT {l l' : List Admin} (h : CodeTy10T B l) (hs : ∀ a ∈ l', a ∈ l) :
    CodeTy10T B l' :=
  typedV_admins_of10T fun _ ha => typedV_admin_of_mem10T h (hs _ ha)

/-- Code built from typed pieces. -/
theorem codeTy10_appendT {l l' : List Admin} (h : CodeTy10T B l) (h' : CodeTy10T B l') :
    CodeTy10T B (l ++ l') :=
  typedV_admins_of10T fun _ ha => (List.mem_append.1 ha).elim (typedV_admin_of_mem10T h)
    (typedV_admin_of_mem10T h')

/-- A value is typed code. -/
theorem codeTy10_valueT (V : ValTyped10T B) (v : Execution.Runtime.Value) :
    CodeTy10T B [value v] :=
  typedV_admins_of10T fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_admin_of_val10T (V v)

/-- One typed instruction is typed code. -/
theorem codeTy10_singleT {a : Admin} (h : TypedV (simEnv10T B) adminT10 (adminToV a)) :
    CodeTy10T B [a] :=
  typedV_admins_of10T fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact h

theorem codeTy10_trapT : CodeTy10T B [.trap] :=
  typedV_admins_of10T fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_trap10T

theorem codeTy10_brT (l : LabelIdx) : CodeTy10T B [.source (.br l)] :=
  typedV_admins_of10T fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_br10T l

theorem codeTy10_nilT : CodeTy10T B [] := typedV_admins_of10T fun _ ha => nomatch ha

/-- **An instruction typed as `instr` is typed as `admininstr`.** -/
theorem typedV_admin_of_instr10T {i : V1.Instr}
    (h : TypedV (simEnv10T B) (.varT "instr" []) (instrToV i)) :
    TypedV (simEnv10T B) adminT10 (instrToV i) := by
  obtain ⟨ci, ex, hi, ha, -⟩ := findTyp_instrAdmin10T (B := B)
  obtain ⟨u, hu⟩ := instrToV_case10 i
  rw [hu] at h ⊢
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed hi (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  exact fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) ha
    Equiv.evalArgs_nil matchArgs_nil (hasTypCase_append_left hc)

/-- **A typed `instr*` is typed code** through `expression`. -/
theorem codeTy10_expressionT {is : List V1.Instr}
    (h : TypedV (simEnv10T B) instrsT (.list (instrsToV is))) : CodeTy10T B (expression is) := by
  refine typedV_admins_of10T fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [instrsToV_map10] at h
  exact typedV_admin_of_instr10T (typedV_list_iff.1 h _ (List.mem_map_of_mem hi))

/-- One typed `instr` is a typed `instr*`. -/
theorem typedV_instrs_one10T {i : V1.Instr}
    (h : TypedV (simEnv10T B) (.varT "instr" []) (instrToV i)) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV [i])) :=
  typedV_list_iff.2 fun _ hu => by
    obtain rfl := List.mem_singleton.1 hu
    exact h

theorem typedV_instrs_nil10T : TypedV (simEnv10T B) instrsT (.list (instrsToV [])) :=
  typedV_list_iff.2 fun _ hu => nomatch hu

/-- **The `BLOCK` an `IF` reduces to is typed.** -/
theorem typedV_blockOfIf10T {bt : V1.BlockType} {b₁ b₂ : V1.Expr}
    (h : TypedV (simEnv10T B) adminT10 (instrToV (.if_ bt b₁ b₂))) :
    TypedV (simEnv10T B) adminT10 (instrToV (.block bt b₁)) ∧
      TypedV (simEnv10T B) adminT10 (instrToV (.block bt b₂)) := by
  obtain ⟨cs, htd, hb, -, hi⟩ := findTyp_admininstr10_ctrlT (B := B)
  obtain ⟨hbt, h₁, h₂⟩ := hasTyp_tup3_inv
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hi)
    (fun hρ hv => typedV_list_of_scope hρ hv)
  have mk : ∀ {b : V1.Expr}, TypedV (simEnv10T B) instrsT (.list (instrsToV b)) →
      TypedV (simEnv10T B) adminT10 (instrToV (.block bt b)) := fun hb' =>
    Sim20.Pure.typedV_closedCase20 htd hb (Sim20.Whole.hasTyp_tup2G hbt hb')
  exact ⟨mk h₁, mk h₂⟩

/-- A typed label's continuation and body. -/
theorem label_parts10T {n : Nat} {cont : V1.Expr} {body : List Admin}
    (h : CodeTy10T B [.label n cont body]) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV cont)) ∧ CodeTy10T B body := by
  have h' := typedV_admin_of_mem10T h (List.mem_singleton_self _)
  exact ⟨(label_inv10T h').2.1, (label_inv10T h').2.2⟩

/-- A typed frame's body. -/
theorem frame_body10T {n : Nat} {fr : Frame} {body : List Admin}
    (h : CodeTy10T B [.frame n fr body]) : CodeTy10T B body :=
  (frame_inv10T (typedV_admin_of_mem10T h (List.mem_singleton_self _))).2.2

/-- Subject reduction at `block`. -/
theorem codeTy10_blockT {bt : V1.BlockType} {b : V1.Expr} (hc : CodeTy10T B [.source (.block bt b)]) :
    CodeTy10T B [.label bt.toList.length [] (expression b)] := by
  have hl := typedV_label10T (n := bt.toList.length) typedV_instrs_nil10T
    (codeTy10_expressionT (block_body10T (typedV_head10T hc)))
  exact typedV_admins_of10T (by simpa using hl)

/-- Subject reduction at `loop`. -/
theorem codeTy10_loopT {bt : V1.BlockType} {b : V1.Expr} (hc : CodeTy10T B [.source (.loop bt b)]) :
    CodeTy10T B [.label 0 [.loop bt b] (expression b)] := by
  have hl := typedV_head10T hc
  have hl' := typedV_label10T (n := 0) (typedV_instrs_one10T (typedV_instr_of_admin10T hl))
    (codeTy10_expressionT (loop_body10T hl))
  exact typedV_admins_of10T (by simpa using hl')

/-- Subject reduction at `if`: both blocks are typed. -/
theorem codeTy10_ifT {bt : V1.BlockType} {b₁ b₂ : V1.Expr} {c : BitVec 32}
    (hc : CodeTy10T B [value (.int .i32 c), .source (.if_ bt b₁ b₂)]) :
    CodeTy10T B [.source (.block bt b₁)] ∧ CodeTy10T B [.source (.block bt b₂)] := by
  obtain ⟨h₁, h₂⟩ := typedV_blockOfIf10T (typedV_second10T hc)
  exact ⟨codeTy10_singleT h₁, codeTy10_singleT h₂⟩

/-- **Subject reduction for every pure step of V1**, given that V1 values are typed. -/
theorem codeTy10_pureT (V : ValTyped10T B) {before after : List Admin}
    (hp : PureStep before after) (hc : CodeTy10T B before) : CodeTy10T B after := by
  cases hp with
  | nop => exact codeTy10_nilT
  | unreachable => exact codeTy10_trapT
  | drop v => exact codeTy10_nilT
  | selectZero a b _ => exact codeTy10_subT hc (by simp)
  | selectNonzero a b _ c _ => exact codeTy10_subT hc (by simp)
  | block bt body => exact codeTy10_blockT hc
  | loop bt body => exact codeTy10_loopT hc
  | ifZero bt l r => exact (codeTy10_ifT hc).2
  | ifNonzero bt l r c _ => exact (codeTy10_ifT hc).1
  | brIfZero l => exact codeTy10_nilT
  | brIfNonzero l c _ => exact codeTy10_brT l
  | brTable ls d c => exact codeTy10_brT _
  | labelDone n cont vs => exact (label_parts10T hc).2
  | labelBranch n cont extra vs tail _ =>
    obtain ⟨hk, hb⟩ := label_parts10T hc
    exact codeTy10_appendT (codeTy10_subT hb (by simp_all)) (codeTy10_expressionT hk)
  | labelBranchOuter n cont vs tail l _ =>
    exact codeTy10_appendT (codeTy10_subT (label_parts10T hc).2 (by simp_all)) (codeTy10_brT _)
  | labelReturn n cont vs tail =>
    exact codeTy10_subT (label_parts10T hc).2 fun _ ha => List.mem_append_left _ ha
  | frameDone n fr vs _ => exact frame_body10T hc
  | frameReturn n fr extra vs tail _ => exact codeTy10_subT (frame_body10T hc) (by simp_all)
  | trapValues v vs tail => exact codeTy10_trapT
  | trapTail i tail => exact codeTy10_trapT
  | labelTrap n cont => exact codeTy10_trapT
  | frameTrap n fr => exact codeTy10_trapT
  | localTee i v =>
    exact codeTy10_appendT (l := [value v, value v]) (codeTy10_subT hc (by simp))
      (codeTy10_singleT (typedV_localSet10T i))
  | intUnary t op x => exact codeTy10_valueT V _
  | intBinary t op x y z _ => exact codeTy10_valueT V _
  | intBinaryTrap t op x y e _ => exact codeTy10_trapT
  | intTest t op x => exact codeTy10_valueT V _
  | intRel t op x y => exact codeTy10_valueT V _
  | floatUnary t op x y _ => exact codeTy10_valueT V _
  | floatBinary t op x y z _ => exact codeTy10_valueT V _
  | floatRel t op x y => exact codeTy10_valueT V _
  | convert op x y _ => exact codeTy10_valueT V _
  | convertTrap op x e _ => exact codeTy10_trapT

/-- A typed state with its store replaced by another typed store. -/
theorem typedV_state_store10T {s s' : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) (hs : StoreTy10T B hn s') :
    TypedV (simEnv10T B) stateT (stateV hn s' f) :=
  typedV_stV_iff10T.2 ⟨typedV_storeV_iff10T.2 hs, (typedV_stV_iff10T.1 hz).2⟩

/-- The store of a typed state, field by field. -/
theorem storeTy10_of_stateT {s : Store H} {f : Frame}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) : StoreTy10T B hn s :=
  typedV_storeV_iff10T.1 (typedV_stV_iff10T.1 hz).1

/-- **A global instance with a value of its type is typed.** -/
theorem typedV_globalInst_set10T {g : GlobalInst} {v : Execution.Runtime.Value}
    (hg : TypedV (simEnv10T B) (.varT "globalinst" []) (globalInstV g))
    (hv : TypedV (simEnv10T B) (.varT "val" []) (valV v)) (ht : v.type = g.value.type) :
    TypedV (simEnv10T B) (.varT "globalinst" []) (globalInstV {g with value := v}) := by
  have hT := hasTyp_struct2_fst findTyp_globalinst10T hg
  have e : globalTypeV g.mutability v.type = globalTypeV g.mutability g.value.type := by rw [ht]
  exact typedV_struct2 findTyp_globalinst10T (by simpa [globalInstV, e] using hT)
    (hv _ valsOnly_empty)

set_option maxRecDepth 8000000 in
theorem findTyp_meminst10T : (simEnv10T B).findTyp? "meminst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "memtype" []) [] [],
      .mk "BYTES" (.iterT (.varT "byte" []) .list) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_memtype10T : (simEnv10T B).findTyp? "memtype" =
    some ([], [.instD [] [] (.aliasT (.varT "limits" []))]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_limits10T : (simEnv10T B).findTyp? "limits" = some ([], [.instD [] []
    (.variantT [.mk "[%..%]" (.tupT [.mk "u32" (.varT "u32" []),
      .mk "u32?" (.iterT (.varT "u32" []) .opt)]) [] []])]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_byte10T : (simEnv10T B).findTyp? "byte" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "i" (.numT .natT)]) []
      [.ifPr (.binE .andOp .boolT (.cmpE .geOp (.numT .natT) (.varE "i") (.numE (.natN 0)))
        (.cmpE .leOp (.numT .natT) (.varE "i") (.numE (.natN 255))))]])]) := rfl

/-- `byte` holds every natural below `256` (2.0's `hasTyp_byte20`, ported). -/
theorem typedV_byte10T {n : Nat} (hn : n < 256) : TypedV (simEnv10T B) (.varT "byte" []) (pctV n) := by
  have htup : HasTyp (simEnv10T B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN n)]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, Sim20.Whole.hasTyp_nat _ _ n,
      hasTypTup_nil_iff.2 rfl⟩⟩
  refine fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1])
    findTyp_byte10T Equiv.evalArgs_nil matchArgs_nil (Sim.IntNumeric.hasTypCase_of_findCase rfl htup
      (Sim.IntNumeric.premsOk_if (Sim.IntNumeric.evalExp_and ?_ ?_)))
  · exact evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num (by simp [Num.cmp])
  · refine evalExp_cmpNum (evalExp_var (v := .num (.natN n)) rfl) evalExp_num ?_
    simp only [Num.cmp, Option.some.injEq, decide_eq_true_eq]
    omega

/-- An encoded byte string is a `byte*`. -/
theorem typedV_bytes10T (b : ByteArray) :
    TypedV (simEnv10T B) (.iterT (.varT "byte" []) .list) (bytesV b) :=
  typedV_list_iff.2 fun w hw => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hw
    exact typedV_byte10T c.toNat_lt

/-- The maximum of a typed memory instance is a typed `u32?`. -/
theorem typedV_memMax10T {m : MemInst}
    (h : TypedV (simEnv10T B) (.varT "meminst" []) (memInstV m)) :
    TypedV (simEnv10T B) (.iterT (.varT "u32" []) .opt) (.opt (m.max.map pctV)) := by
  have hT : HasTyp (simEnv10T B) VarEnv.empty (.varT "memtype" [])
      (limitsV (Execution.Memory.size m.data) m.max) := hasTyp_struct2_fst findTyp_meminst10T h
  have hL : HasTyp (simEnv10T B) VarEnv.empty (.varT "limits" [])
      (limitsV (Execution.Memory.size m.data) m.max) :=
    hasTypDef_aliasT_iff.1 (Sim20.Whole.hasTypDef_of_closed findTyp_memtype10T hT)
  have hP := hasTyp_closedVariant_inv valsOnly_empty findTyp_limits10T hL (op := "[%..%]") rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hP
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', hmax, -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, -⟩ := List.cons.inj hys'
  intro ρ hρ
  rcases hasTyp_iterT_opt_iff.1 hmax with he | ⟨w, he, hw⟩
  · exact hasTyp_iterT_opt_iff.2 (.inl he)
  · exact hasTyp_iterT_opt_iff.2 (.inr ⟨w, he, Sim.IntNumeric.hasTyp_varT_nil_congr
      ⟨rfl, rfl, rfl⟩ hρ hw⟩)

/-- **A grown memory instance is typed**: the old maximum, and at most `65536` pages. -/
theorem typedV_memInst_grow10T {m : MemInst} {n : Nat} {d : Execution.Memory.Bytes}
    (h : TypedV (simEnv10T B) (.varT "meminst" []) (memInstV m))
    (hg : Execution.Memory.grow? m.data m.max n = some d) :
    TypedV (simEnv10T B) (.varT "meminst" []) (memInstV {m with data := d}) := by
  have hle : Execution.Memory.size d < 2 ^ 32 := by
    unfold Execution.Memory.grow? at hg
    split at hg
    · rename_i hc
      obtain rfl := (Option.some.inj hg).symm
      have hr : ({ data := Array.replicate (n * 65536) 0 } : ByteArray).size = n * 65536 := by
        simp [ByteArray.size]
      simp only [Execution.Memory.size, Execution.Memory.pageSize, Execution.Memory.maxPages,
        ByteArray.size_append, hr] at hc ⊢
      omega
    · cases hg
  have hL : TypedV (simEnv10T B) (.varT "limits" []) (limitsV (Execution.Memory.size d) m.max) :=
    Sim20.Pure.typedV_closedCase20 findTyp_limits10T rfl
      (Sim20.Whole.hasTyp_tup2G (typedV10T (typedV_u32_10 hle)) (typedV_memMax10T h))
  exact typedV_struct2 findTyp_meminst10T
    (typedV_aliasG10 findTyp_memtype10T (hL _ valsOnly_empty) _ valsOnly_empty)
    (typedV_bytes10T d _ valsOnly_empty)

set_option maxRecDepth 8000000 in
theorem findTyp_funcF10T : (simEnv10T B).findTyp? "func" = some ([], [.instD [] []
    (.variantT [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] []])]) :=
  rfl

set_option maxRecDepth 8000000 in
theorem findTyp_expr10T : (simEnv10T B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) := rfl

set_option maxRecDepth 8000000 in
theorem findTyp_funcinstF10T : (simEnv10T B).findTyp? "funcinst" = some ([], [.instD [] []
    (.structT [.mk "TYPE" (.varT "functype" []) [] [], .mk "MODULE" (.varT "moduleinst" []) [] [],
      .mk "CODE" (.varT "func" []) [] []])]) := rfl

/-- **The module of a typed Wasm `funcinst` is a typed `moduleinst`.** -/
theorem typedV_moduleOfInst10T {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hi : HasTyp (simEnv10T B) VarEnv.empty (.varT "funcinst" []) (funcInstV hn (.wasm ft m fn))) :
    TypedV (simEnv10T B) (.varT "moduleinst" []) (moduleInstV m) := by
  have h₀ : HasTypFields (simEnv10T B) VarEnv.empty _
      [("TYPE", funcTypeV ft), ("MODULE", moduleInstV m), ("CODE", funcV fn)] :=
    hasTypFields_of_closed findTyp_funcinstF10T (typedV_of_empty20 hi)
  exact typedV_of_empty20 (hasTypFields_cons_nil_iff.1 (hasTypFields_cons_nil_iff.1 h₀).2).1

/-- **The body of a typed `func` is a typed `instr*`.** -/
theorem typedV_bodyOfFunc10T {fn : V1.Func}
    (h : TypedV (simEnv10T B) (.varT "func" []) (funcV fn)) :
    TypedV (simEnv10T B) instrsT (.list (instrsToV fn.body)) := by
  have hp := hasTyp_closedVariant_inv valsOnly_empty findTyp_funcF10T (h _ valsOnly_empty)
    (op := "FUNC") rfl
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hp
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y, ys, hys, -, htup₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys
  obtain ⟨y', ys', hys', -, htup₂⟩ := hasTypTup_cons_iff.1 htup₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj hys'
  obtain ⟨y'', ys'', hys'', he, -⟩ := hasTypTup_cons_iff.1 htup₂
  obtain ⟨rfl, -⟩ := List.cons.inj hys''
  have he' : HasTyp (simEnv10T B) VarEnv.empty (.varT "expr" []) (.list (instrsToV fn.body)) :=
    Sim.IntNumeric.hasTyp_varT_nil_congr ⟨rfl, rfl, rfl⟩ valsOnly_empty he
  exact typedV_list_of_scope valsOnly_empty
    (hasTypDef_aliasT_iff.1 (Sim20.Whole.hasTypDef_of_closed findTyp_expr10T he'))

/-- **The code `call_addr` opens is typed**: the new frame and its body's label. -/
theorem typed_invokeFrame10T (V : ValTyped10T B) {s : Store H} (hst : StoreTy10T B hn s)
    {a : Execution.Runtime.FuncAddr} {ft : V1.FuncType} {m : ModuleInst} {fn : V1.Func}
    (hfi : s.funcs[a.value]? = some (.wasm ft m fn)) (args : List Execution.Runtime.Value)
    (n : Nat) : CodeTy10T B [.frame n ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
      [.label n [] (expression fn.body)]] := by
  have hstore : TypedV (simEnv10T B) storeT (storeV hn s) := typedV_storeV_iff10T.2 hst
  have hi := hasTyp_funcinst_of_store10T hstore hfi
  have hbody := typedV_bodyOfFunc10T (typedV_funcV_of_inst10T hi)
  have hlocals : TypedV (simEnv10T B) (.iterT (.varT "val" []) .list)
      (.list ((args ++ fn.locals.map Execution.Runtime.Value.zero).map valV)) :=
    typedV_list_iff.2 fun u hu => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hu
      exact V v
  have hF : TypedV (simEnv10T B) frameT
      (frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩) :=
    typedV_struct2 findTyp_frame10T (hlocals _ valsOnly_empty)
      (typedV_moduleOfInst10T hi _ valsOnly_empty)
  have hl : CodeTy10T B [.label n [] (expression fn.body)] :=
    codeTy10_singleT (typedV_label10T typedV_instrs_nil10T (codeTy10_expressionT hbody))
  exact codeTy10_singleT (typedV_frame10T hF hl)

/-- Subject reduction at `global.set`. -/
theorem ts10_globalSetT (s : Store H) (f : Frame) (x : GlobalIdx) (a : Execution.Runtime.GlobalAddr)
    (g : GlobalInst) (v : Execution.Runtime.Value) (ha : f.module.globals[x.toNat]? = some a)
    (hg : s.globals[a.value]? = some g) (hts : TS10T B hn ⟨s, f, [value v, .source (.globalSet x)]⟩)
    (hok : GSetOk s f [value v, .source (.globalSet x)]) :
    TS10T B hn ⟨setGlobal s a { g with value := v }, f, []⟩ := by
  have hst := storeTy10_of_stateT hts.1
  have hgi := typedV_globalInst_set10T (typedV_of_getElem? hst.globals hg)
    (typedV_val_of_head10T hts.2) (gsetOk_redex hok ha hg)
  have hgs : TypedV (simEnv10T B) (.iterT (.varT "globalinst" []) .list)
      (.list ((s.globals.set a.value { g with value := v }).map globalInstV)) :=
    typedV_list_set20 hst.globals hgi
  exact ⟨typedV_state_store10T (s' := setGlobal s a { g with value := v }) hts.1
    ⟨hst.funcs, hgs, hst.tables, hst.mems⟩, codeTy10_nilT⟩

/-- Subject reduction at `memory.grow`. -/
theorem ts10_memoryGrowT (V : ValTyped10T B) (s : Store H) (f : Frame)
    (a : Execution.Runtime.MemAddr) (m : MemInst) (c r : BitVec 32) (b : Execution.Memory.Bytes)
    (hm : frameMemory s f = some (a, m)) (hgr : Execution.Memory.Grow m.data m.max c.toNat b r)
    (hts : TS10T B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩) :
    TS10T B hn ⟨setMemory s a {m with data := b}, f, [value (.int .i32 r)]⟩ := by
  refine ⟨?_, codeTy10_valueT V _⟩
  have hsm := (frameMemory_some hm).2
  cases hgr with
  | success _ hgrow =>
    have hst := storeTy10_of_stateT hts.1
    have hms : TypedV (simEnv10T B) (.iterT (.varT "meminst" []) .list)
        (.list ((s.memories.set a.value {m with data := b}).map memInstV)) :=
      typedV_list_set20 hst.mems (typedV_memInst_grow10T (typedV_of_getElem? hst.mems hsm) hgrow)
    exact typedV_state_store10T (s' := setMemory s a {m with data := b}) hts.1
      ⟨hst.funcs, hst.globals, hst.tables, hms⟩
  | failure =>
    rw [setMemory_self hsm]
    exact hts.1

/-! ## Stores: a write keeps the memory's size -/

/-- **A memory instance with its bytes replaced by as many bytes is typed** (in `simEnv10`). -/
theorem typedV_memInst_write10 {m : MemInst} {d : Execution.Memory.Bytes}
    (h : TypedV (simEnv10 B) (.varT "meminst" []) (memInstV m)) (hsz : d.size = m.data.size) :
    TypedV (simEnv10 B) (.varT "meminst" []) (memInstV {m with data := d}) := by
  have hT : HasTyp (simEnv10 B) VarEnv.empty (.varT "memtype" [])
      (limitsV (Execution.Memory.size m.data) m.max) := hasTyp_struct2_fst findTyp_meminst10 h
  have e : Execution.Memory.size d = Execution.Memory.size m.data := by
    simp only [Execution.Memory.size, hsz]
  exact typedV_struct2 findTyp_meminst10 (by rw [e]; exact hT) (typedV_bytes10 d _ valsOnly_empty)

/-- **A store write keeps the state typed in `simEnv10T`.** -/
theorem typedV_state_write10T {s : Store H} {f : Frame} {a : Execution.Runtime.MemAddr}
    {m : MemInst} {d : Execution.Memory.Bytes}
    (hz : TypedV (simEnv10T B) stateT (stateV hn s f)) (hm : frameMemory s f = some (a, m))
    (hsz : d.size = m.data.size) :
    TypedV (simEnv10T B) stateT (stateV hn (setMemory s a {m with data := d}) f) := by
  have hst := storeTy10_of_stateT hz
  have hms := mems10_of_state10T hz
  have hsm := (frameMemory_some hm).2
  have hms' : TypedV (simEnv10 B) (.iterT (.varT "meminst" []) .list)
      (.list ((s.memories.set a.value {m with data := d}).map memInstV)) :=
    typedV_list_set20 hms (typedV_memInst_write10 (typedV_of_getElem? hms hsm) hsz)
  exact typedV_state_store10T (s' := setMemory s a {m with data := d}) hz
    ⟨hst.funcs, hst.globals, hst.tables, typedV10T hms'⟩

/-- **Subject reduction for every V1 step**, given that V1 values are typed: from a configuration
whose images are typed and which satisfies `GSetOk`, every V1 step leads to typed images. -/
theorem ts10_stepT (V : ValTyped10T B) {host : HostSemantics H} {c c' : Config H}
    (h : Step host c c') (hts : TS10T B hn c) (hg : GSetOk c.store c.frame c.code) :
    TS10T B hn c' := by
  induction h with
  | pure s f hp => exact ⟨hts.1, codeTy10_pureT V hp hts.2⟩
  | context hs vs tail ih => exact ts10_contextT vs tail hts fun h' => ih h' (gsetOk_mid hg)
  | label _ n cont ih => exact ts10_labelT n cont hts fun h' => ih h' (gsetOk_label hg)
  | frame _ n outer ih => exact ts10_frameT n outer hts fun h' => ih h' (gsetOk_frame hg)
  | localGet s f i v hv => exact subjRed10_leafT (.localGet s f i v hv) hts
  | localSet s f i v old hv => exact subjRed10_leafT (.localSet s f i v old hv) hts
  | globalGet s f i a g h₁ h₂ => exact subjRed10_leafT (.globalGet s f i a g h₁ h₂) hts
  | globalSet s f i a g v h₁ h₂ _ => exact ts10_globalSetT s f i a g v h₁ h₂ hts hg
  | call s f i a h₁ => exact subjRed10_leafT (.call s f i a h₁) hts
  | callIndirect s f i c t a fn ft _ _ _ _ _ => exact ⟨hts.1, codeTy10_singleT (typedV_invoke10T a)⟩
  | callIndirectBounds s f i c t _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | callIndirectNull s f i c t _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | callIndirectType s f i c t a fn ft _ _ _ _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | invokeWasm s f a ft m fn args h₁ _ _ =>
    exact ⟨hts.1, typed_invokeFrame10T V (storeTy10_of_stateT hts.1) h₁ args _⟩
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact (not_typed_host10T hts.1 h₁).elim
  | invokeHostDiverges s f a ft fn args h₁ _ _ => exact (not_typed_host10T hts.1 h₁).elim
  | intLoad s f t p arg c a m v _ _ => exact ⟨hts.1, codeTy10_valueT V v⟩
  | intLoadTrap s f t p arg c a m _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | floatLoad s f t arg c a m v _ _ => exact ⟨hts.1, codeTy10_valueT V v⟩
  | floatLoadTrap s f t arg c a m _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | intStore s f t p arg c x a m b h₁ h₂ =>
    exact ⟨typedV_state_write10T hts.1 h₁ (storeInt_size10 h₂), codeTy10_nilT⟩
  | intStoreTrap s f t p arg c x a m _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | floatStore s f t arg c x a m b h₁ h₂ =>
    exact ⟨typedV_state_write10T hts.1 h₁ (storeFloat_size10 h₂), codeTy10_nilT⟩
  | floatStoreTrap s f t arg c x a m _ _ => exact ⟨hts.1, codeTy10_trapT⟩
  | memorySize s f a m _ => exact ⟨hts.1, codeTy10_valueT V _⟩
  | memoryGrow s f a m c r b h₁ h₂ => exact ts10_memoryGrowT V s f a m c r b h₁ h₂ hts

/-- **Subject reduction on configuration images.** -/
theorem typed10_stepT (V : ValTyped10T B) {host : HostSemantics H} {c c' : Config H}
    (h : Step host c c') (hc : Typed10 (simEnv10T B) hn c) (hg : GSetOk c.store c.frame c.code) :
    Typed10 (simEnv10T B) hn c' :=
  typed10_iffT.2 (ts10_stepT V h (typed10_iffT.1 hc) hg)

end Silmaril.Wasm.SpecTec.Sim10.Whole
