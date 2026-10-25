module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Memory
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadCtl

@[expose] public section

/-! # Simulation under address maps: head steps

`head_sim`: a head step (`SingleThreaded.Det.Head`) of side `A` at a related
first non-value has a matching step of side `B` with related results. The
context rules are discharged by an induction hypothesis on smaller code.
`head_sim_pair` is the call of a related function address.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

/-! ## Instruction classes -/

/-- The instructions `IRel` relates non-trivially. -/
def ourI : Instr → Bool
  | .call _ | .globalGet _ | .globalSet _ | .block .. | .loop .. | .if_ .. => true
  | _ => false

-- FLAG(statement-change): simple vector arithmetic is now related in module code.
theorem simpleI_fam {i : Instr} (h : simpleI i = true) :
    famOf (.plain i) = .parametric ∨ famOf (.plain i) = .numeric ∨
      famOf (.plain i) = .variable ∨ famOf (.plain i) = .control ∨
      famOf (.plain i) = .memory ∨ famOf (.plain i) = .vector := by
  cases i <;> simp [simpleI, famOf] at h ⊢

-- FLAG(statement-change): IRel now includes unchanged vector arithmetic.
theorem IRel.fam {X : SimCtx} {i j : Instr} (h : IRel X i j) :
    famOf (.plain i) = .parametric ∨ famOf (.plain i) = .numeric ∨
      famOf (.plain i) = .variable ∨ famOf (.plain i) = .control ∨
      famOf (.plain i) = .memory ∨ famOf (.plain i) = .vector := by
  cases h with
  | call => exact .inr (.inr (.inr (.inl rfl)))
  | globalGet => exact .inr (.inr (.inl rfl))
  | globalSet => exact .inr (.inr (.inl rfl))
  | block => exact .inr (.inr (.inr (.inl rfl)))
  | loop => exact .inr (.inr (.inr (.inl rfl)))
  | if_ => exact .inr (.inr (.inr (.inl rfl)))
  | simple h => exact simpleI_fam h

/-- Table, reference and aggregate families occur only in foreign code. -/
-- FLAG(statement-change): vectors use fam_pure in either mode; excluded here.
theorem ARel.fam_same {X : SimCtx} {m : Mode} {e e' : Admin} (he : ARel X m e e')
    (hk : famOf e = .table ∨ famOf e = .reference ∨ famOf e = .aggregate) : m = .same ∧ e' = e := by
  cases he with
  | plainS => exact ⟨rfl, rfl⟩
  | plainO h =>
    exfalso
    rcases IRel.fam h with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hk <;> simp at hk
  | ref => simp [famOf] at hk
  | callRefType => simp [famOf] at hk
  | returnCallRefType => simp [famOf] at hk
  | trap => simp [famOf] at hk
  | labelS => simp [famOf] at hk
  | labelO => simp [famOf] at hk
  | handler => simp [famOf] at hk
  | frameS => simp [famOf] at hk
  | frameO => simp [famOf] at hk

/-- These families have identical instruction syntax on both sides. -/
theorem ARel.fam_pure {X : SimCtx} {m : Mode} {e e' : Admin} (he : ARel X m e e')
    (hk : famOf e = .parametric ∨ famOf e = .numeric ∨ famOf e = .vector ∨ famOf e = .memory) : e' = e := by
  cases he with
  | plainS => rfl
  | plainO h =>
    cases h with
    | simple => rfl
    | _ => simp [famOf] at hk
  | ref => simp [famOf] at hk
  | callRefType => simp [famOf] at hk
  | returnCallRefType => simp [famOf] at hk
  | trap => simp [famOf] at hk
  | labelS => simp [famOf] at hk
  | labelO => simp [famOf] at hk
  | handler => simp [famOf] at hk
  | frameS => simp [famOf] at hk
  | frameO => simp [famOf] at hk

/-- A simple instruction is related only to itself. -/
theorem ARel.plain_simple {X : SimCtx} {m : Mode} {i : Instr} {e' : Admin}
    (hi : simpleI i = true) (he : ARel X m (.plain i) e') : e' = .plain i := by
  cases he with
  | plainS => rfl
  | plainO h =>
    cases h with
    | simple => rfl
    | _ => simp [simpleI] at hi

/-- An instruction outside the module's repertoire occurs only in foreign code. -/
theorem ARel.plain_other {X : SimCtx} {m : Mode} {i : Instr} {e' : Admin}
    (hi : simpleI i = false) (ho : ourI i = false) (he : ARel X m (.plain i) e') :
    m = .same ∧ e' = .plain i := by
  cases he with
  | plainS => exact ⟨rfl, rfl⟩
  | plainO h =>
    cases h with
    | simple h => simp [h] at hi
    | _ => simp [ourI] at ho

/-! ## Values and traps -/

/-- A foreign value or a trap. -/
def ValTrap (n0 : Nat) (a : Admin) : Prop := a = .trap ∨ ∃ v, a = v.toAdmin ∧ valF n0 v

theorem CodeR.of_valTrap {X : SimCtx} {m : Mode} : ∀ {l : List Admin},
    (∀ a ∈ l, ValTrap X.n0 a) → CodeR X m l l
  | [], _ => .nil
  | x :: l, h => by
    have ht := CodeR.of_valTrap (m := m) (l := l) (fun a ha => h a (by simp [ha]))
    rcases h x (by simp) with rfl | ⟨v, rfl, hv⟩
    · exact .cons .trap ht
    · exact .cons (ARel.val hv) ht

theorem valTrap_val {n0 : Nat} {v : Val} (h : valF n0 v) : ValTrap n0 v.toAdmin := .inr ⟨v, rfl, h⟩

theorem valTrap_intConst (n0 : Nat) (t : IntType) (b : BitVec t.width) :
    ValTrap n0 (.plain (.intConst t b)) := .inr ⟨.num ⟨.int t, b⟩, rfl, trivial⟩

theorem valTrap_floatConst (n0 : Nat) (t : FloatType) (b : BitVec t.width) :
    ValTrap n0 (.plain (.floatConst t b)) := .inr ⟨.num ⟨.float t, b⟩, rfl, trivial⟩

theorem valTrap_vecConst (n0 : Nat) (b : BitVec 128) : ValTrap n0 (.plain (.vecConst b)) :=
  .inr ⟨.vec b, rfl, trivial⟩

theorem valTrap_constI32 (n0 : Nat) (b : BitVec 32) : ValTrap n0 (constI32 b) :=
  .inr ⟨.i32 b, rfl, trivial⟩

theorem valTrap_trap (n0 : Nat) : ValTrap n0 .trap := .inl rfl

theorem parametric_out {n0 : Nat} {l l' : List Admin} (h : ParametricStep l l')
    (hl : ∀ a ∈ l, flatF n0 a) : ∀ a ∈ l', ValTrap n0 a := by
  cases h with
  | unreachable => simp [valTrap_trap]
  | nop => simp
  | drop v => simp
  | selectTrue hc =>
    simp only [List.mem_singleton, forall_eq]
    exact valTrap_val (by simpa using hl _ List.mem_cons_self)
  | selectFalse v₁ v₂ ts =>
    simp only [List.mem_singleton, forall_eq]
    exact valTrap_val (by simpa using hl _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem numeric_out {n0 : Nat} {l l' : List Admin} (h : NumericStep P l l') :
    ∀ a ∈ l', ValTrap n0 a := by
  cases h <;> simp only [List.mem_singleton, forall_eq] <;>
    first
    | exact valTrap_trap n0
    | exact valTrap_intConst n0 _ _
    | exact valTrap_floatConst n0 _ _
    | exact valTrap_constI32 n0 _
    | exact valTrap_val trivial

theorem vector_out {n0 : Nat} {l l' : List Admin} (h : VectorStep P l l') :
    ∀ a ∈ l', ValTrap n0 a := by
  cases h <;> simp only [List.mem_singleton, forall_eq] <;>
    first
    | exact valTrap_trap n0
    | exact valTrap_vecConst n0 _
    | exact valTrap_constI32 n0 _
    | exact valTrap_val trivial

/-! ## Frames -/

theorem FrameRel.locals {X : SimCtx} {m : Mode} {f f' : Frame} (h : FrameRel X m f f') :
    f.locals = f'.locals := by
  cases m
  · rw [h.1]
  · exact h.2.2.1

theorem FrameRel.locF {X : SimCtx} {m : Mode} {f f' : Frame} (h : FrameRel X m f f') :
    localsF X.n0 f.locals := by
  cases m
  · exact h.2.2
  · exact h.2.2.2

theorem FrameRel.types {X : SimCtx} (hX : X.WF) {m : Mode} {f f' : Frame} (h : FrameRel X m f f') :
    f.module.types = f'.module.types := by
  cases m
  · rw [h.1]
  · rw [h.1, h.2.1]; exact hX.types

theorem blockType?_congr {m₁ m₂ : ModuleInst} (h : m₁.types = m₂.types) (bt : BlockType) :
    m₁.blockType? bt = m₂.blockType? bt := by
  cases bt <;> simp [ModuleInst.blockType?, ModuleInst.instVal, h]

theorem FrameRel.setLocal {X : SimCtx} {m : Mode} {f f' : Frame} (h : FrameRel X m f f')
    (x : LocalIdx) {v : Val} (hv : valF X.n0 v) : FrameRel X m (f.setLocal x v) (f'.setLocal x v) := by
  have hl : localsF X.n0 (f.setLocal x v).locals := by
    intro o ho w hw
    rcases mem_set_or ho with ho | rfl
    · exact h.locF o ho w hw
    · cases hw; exact hv
  cases m
  · obtain ⟨rfl, hm, -⟩ := h
    exact ⟨rfl, hm, hl⟩
  · obtain ⟨h1, h2, h3, -⟩ := h
    exact ⟨h1, h2, by simp [Frame.setLocal, h3], hl⟩

theorem local?_val {X : SimCtx} {m : Mode} {f f' : Frame} (h : FrameRel X m f f') {x : LocalIdx}
    {v : Val} (hx : f.local? x = some (some v)) : f'.local? x = some (some v) ∧ valF X.n0 v := by
  refine ⟨by simpa [Frame.local?, h.locals] using hx, ?_⟩
  exact h.locF _ (List.mem_of_getElem? hx) v rfl

theorem localsF_forCall {n0 : Nat} {mi : ModuleInst} {vs : List Val} {ls : List ValType}
    (hvs : ∀ v ∈ vs, valF n0 v) : localsF n0 (Frame.forCall mi vs ls).locals := by
  intro o ho w hw
  simp only [Frame.forCall, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨v, hv, rfl⟩ | ⟨t, -, rfl⟩
  · exact (Option.some.inj hw) ▸ hvs v hv
  · exact valF_defaultVal hw

/-- The frame of a foreign Wasm function. -/
theorem frameS_forCall {X : SimCtx} {mi : ModuleInst} {vs : List Val} {ls : List ValType}
    (hm : modF X.n0 X.g0 mi) (hvs : ∀ v ∈ vs, valF X.n0 v) : FrameS X (Frame.forCall mi vs ls) :=
  ⟨hm, localsF_forCall hvs⟩

theorem tag?_congr {S T : Store H} (h : S.tags = T.tags) (f : Frame) (x : TagIdx) :
    S.tag? f x = T.tag? f x := by
  unfold Store.tag?; rw [h]

theorem catchMatches_congr {S T : Store H} (h : S.exns = T.exns) {f : Frame} {a : Nat}
    {c : Catch} : CatchMatches S f a c ↔ CatchMatches T f a c := by
  cases c <;> simp only [CatchMatches, h]

theorem vals_snoc_append (vs : List Val) (v : Val) (x : Admin) :
    vals (vs ++ [v]) ++ [x] = vals vs ++ [v.toAdmin, x] := by
  simp [vals]

/-! ## Stores -/

theorem StoreRel.tags_eq {X : SimCtx} {S T : Store H} (h : StoreRel X S T) : S.tags = T.tags :=
  by have := congrArg Store.tags h.rest; exact this
theorem StoreRel.exns_eq {X : SimCtx} {S T : Store H} (h : StoreRel X S T) : S.exns = T.exns :=
  by have := congrArg Store.exns h.rest; exact this
theorem StoreRel.structs_eq {X : SimCtx} {S T : Store H} (h : StoreRel X S T) :
    S.structs = T.structs := by have := congrArg Store.structs h.rest; exact this
theorem StoreRel.arrays_eq {X : SimCtx} {S T : Store H} (h : StoreRel X S T) :
    S.arrays = T.arrays := by have := congrArg Store.arrays h.rest; exact this

theorem StoreRel.T_eq {X : SimCtx} {S T : Store H} (h : StoreRel X S T) :
    T = S.withFG T.funcs T.globals := Store.withFG_eq h.rest

theorem StoreRel.withFG_of {X : SimCtx} {S T S' : Store H} (hS : StoreRel X S T)
    (hf : S'.funcs = S.funcs) (hg : S'.globals = S.globals) (hF : StoreF X.n0 X.g0 S') :
    StoreRel X S' (S'.withFG T.funcs T.globals) where
  rest := by cases S'; rfl
  funcs a ha := by rw [hf]; exact hS.funcs a ha
  globals a ha := by rw [hg]; exact hS.globals a ha
  fpair a b h := by
    have := hS.fpair a b h
    unfold FuncPair at this ⊢
    rw [hf]
    exact this
  gpair a b h := by rw [hg]; exact hS.gpair a b h
  fgn := hF
  intp a b h := by rw [hf]; exact hS.intp a b h

theorem StoreRel.setGlobal_lo {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a : Nat}
    (ha : a < X.g0) {v : Val} (hv : valF X.n0 v) :
    StoreRel X (S.setGlobal a v) (T.setGlobal a v) where
  rest := hS.rest
  funcs := hS.funcs
  globals a' ha' := by
    simp only [Store.setGlobal, List.getElem?_modify]
    rw [hS.globals a' ha']
  fpair := hS.fpair
  gpair a' b' h := by
    obtain ⟨h1, h2, g, h3, h4⟩ := hS.gpair a' b' h
    refine ⟨h1, h2, g, ?_, ?_⟩
    · simp only [Store.setGlobal]
      rw [List.getElem?_modify_ne _ _ (by omega)]
      exact h3
    · simp only [Store.setGlobal]
      rw [List.getElem?_modify_ne _ _ (by omega)]
      exact h4
  fgn := hS.fgn.setGlobal a v hv
  intp := hS.intp

theorem StoreRel.setGlobal_pair {X : SimCtx} (hX : X.WF) {S T : Store H} (hS : StoreRel X S T)
    {a b : Nat} (hab : X.G a b) {v : Val} (hv : valF X.n0 v) :
    StoreRel X (S.setGlobal a v) (T.setGlobal b v) where
  rest := hS.rest
  funcs := hS.funcs
  globals a' ha' := by
    obtain ⟨h1, h2, -⟩ := hS.gpair a b hab
    simp only [Store.setGlobal]
    rw [List.getElem?_modify_ne _ _ (by omega), List.getElem?_modify_ne _ _ (by omega)]
    exact hS.globals a' ha'
  fpair := hS.fpair
  gpair a' b' h := by
    obtain ⟨h1, h2, g, h3, h4⟩ := hS.gpair a' b' h
    refine ⟨h1, h2, ?_⟩
    by_cases ha : a = a'
    · subst ha
      have hb := hX.gfun _ _ _ hab h
      subst hb
      exact ⟨{ g with value := v }, by simp [Store.setGlobal, h3], by simp [Store.setGlobal, h4]⟩
    · have hb : b ≠ b' := fun hb => ha (hX.ginj _ _ _ hab (hb ▸ h))
      refine ⟨g, ?_, ?_⟩
      · simp only [Store.setGlobal]
        rw [List.getElem?_modify_ne _ _ ha]
        exact h3
      · simp only [Store.setGlobal]
        rw [List.getElem?_modify_ne _ _ hb]
        exact h4
  fgn := hS.fgn.setGlobal a v hv
  intp := hS.intp

theorem StoreRel.addExn {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) (e : ExnInst)
    (he : ∀ v ∈ e.fields, valF X.n0 v) : StoreRel X (S.addExn e) (T.addExn e) where
  rest := congrArg (fun s : Store H => { s with exns := s.exns ++ [e] }) hS.rest
  funcs := hS.funcs
  globals := hS.globals
  fpair := hS.fpair
  gpair := hS.gpair
  fgn := hS.fgn.addExn e he
  intp := hS.intp

/-- A foreign function is the same function on both sides. -/
theorem StoreRel.func_lo {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a : Nat}
    (ha : a < X.n0) {fi : FuncInst H} (h : S.funcs[a]? = some fi) : T.funcs[a]? = some fi := by
  rw [← hS.funcs a ha]; exact h

theorem StoreRel.refOk_iff {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {r : Ref}
    (hr : refF X.n0 r) {t : CRefType} : RefOk S r t ↔ RefOk T r t := by
  rw [hS.T_eq]
  exact refOk_withFG_iff (fun a ha => hS.funcs a ha) hr

theorem StoreRel.global_lo {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {f : Frame}
    (hm : modF X.n0 X.g0 f.module) {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : S.global? f x = some (a, g)) : a < X.g0 ∧ T.global? f x = some (a, g) := by
  obtain ⟨h1, h2⟩ := global?_some h
  have ha : a < X.g0 := hm.2 a (List.mem_of_getElem? h1)
  exact ⟨ha, global?_of h1 (by rw [← hS.globals a ha]; exact h2)⟩

/-! ## Code -/

theorem snoc_inv {A B : List Val} {e x : Admin} (h : vals A ++ [e] = vals B ++ [x])
    (he : e.val? = none) (hx : x.val? = none) : A = B ∧ e = x := by
  obtain ⟨h1, h2, -⟩ := Silmaril.Wasm.SingleThreaded.Det.vals_append_cons_inj h he hx
  exact ⟨h1, h2⟩

theorem flat_args {n0 : Nat} {args : List Val} {e : Admin} (hargs : ∀ v ∈ args, valF n0 v)
    (he : flatF n0 e) : ∀ a ∈ vals args ++ [e], flatF n0 a := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · exact flatF_vals.2 hargs a ha
  · simp at ha; subst ha; exact he

/-- Splitting at a non-value that is not a `CALL_REF`. -/
theorem CodeR.split_nc {X : SimCtx} {m : Mode} {V : List Val} {x : Admin} {rest ys : List Admin}
    (h : CodeR X m (vals V ++ x :: rest) ys) (hx : x.val? = none) (hc : ∀ d, x ≠ .callRefType d) :
    ∃ x' rest', ys = vals V ++ x' :: rest' ∧ (∀ v ∈ V, valF X.n0 v) ∧ ARel X m x x' ∧
      CodeR X m rest rest' := by
  rcases CodeR.split_fnv hx h with h' | ⟨_, _, _, d, _, -, rfl, -⟩
  · exact h'
  · exact absurd rfl (hc d)

theorem CodeR.split1 {X : SimCtx} {m : Mode} {A : List Val} {x : Admin} {R ys : List Admin}
    (h : CodeR X m (vals A ++ [x] ++ R) ys) (hx : x.val? = none) (hc : ∀ d, x ≠ .callRefType d) :
    ∃ x' R', ys = vals A ++ [x'] ++ R' ∧ (∀ v ∈ A, valF X.n0 v) ∧ ARel X m x x' ∧
      CodeR X m R R' := by
  have h' : CodeR X m (vals A ++ x :: R) ys := by simpa using h
  obtain ⟨x', R', rfl, hA, hx', hR⟩ := CodeR.split_nc h' hx hc
  exact ⟨x', R', by simp, hA, hx', hR⟩

theorem CodeR.split2 {X : SimCtx} {m : Mode} {A B : List Val} {x : Admin} {R ys : List Admin}
    (h : CodeR X m (vals A ++ vals B ++ [x] ++ R) ys) (hx : x.val? = none)
    (hc : ∀ d, x ≠ .callRefType d) :
    ∃ x' R', ys = vals A ++ vals B ++ [x'] ++ R' ∧ (∀ v ∈ A, valF X.n0 v) ∧
      (∀ v ∈ B, valF X.n0 v) ∧ ARel X m x x' ∧ CodeR X m R R' := by
  have h' : CodeR X m (vals (A ++ B) ++ x :: R) ys := by simpa using h
  obtain ⟨x', R', rfl, hAB, hx', hR⟩ := CodeR.split_nc h' hx hc
  exact ⟨x', R', by simp, fun v hv => hAB v (by simp [hv]), fun v hv => hAB v (by simp [hv]),
    hx', hR⟩

theorem CodeR.split3 {X : SimCtx} {m : Mode} {A : List Val} {v : Val} {x : Admin}
    {R ys : List Admin} (h : CodeR X m (vals A ++ [v.toAdmin, x] ++ R) ys) (hx : x.val? = none)
    (hc : ∀ d, x ≠ .callRefType d) :
    ∃ x' R', ys = vals A ++ [v.toAdmin, x'] ++ R' ∧ (∀ w ∈ A, valF X.n0 w) ∧ valF X.n0 v ∧
      ARel X m x x' ∧ CodeR X m R R' := by
  have h' : CodeR X m (vals (A ++ [v]) ++ x :: R) ys := by simpa using h
  obtain ⟨x', R', rfl, hAv, hx', hR⟩ := CodeR.split_nc h' hx hc
  exact ⟨x', R', by simp, fun w hw => hAv w (by simp [hw]), hAv v (by simp), hx', hR⟩

theorem CodeR.split4 {X : SimCtx} {m : Mode} {A B : List Val} {v : Val} {x : Admin}
    {R ys : List Admin} (h : CodeR X m (vals A ++ vals B ++ [v.toAdmin, x] ++ R) ys)
    (hx : x.val? = none) (hc : ∀ d, x ≠ .callRefType d) :
    ∃ x' R', ys = vals A ++ vals B ++ [v.toAdmin, x'] ++ R' ∧ (∀ w ∈ B, valF X.n0 w) ∧
      valF X.n0 v ∧ ARel X m x x' ∧ CodeR X m R R' := by
  have h' : CodeR X m (vals (A ++ B ++ [v]) ++ x :: R) ys := by simpa using h
  obtain ⟨x', R', rfl, hAv, hx', hR⟩ := CodeR.split_nc h' hx hc
  exact ⟨x', R', by simp, fun w hw => hAv w (by simp [hw]), hAv v (by simp), hx', hR⟩

theorem CodeR.throwing_inv {X : SimCtx} {m : Mode} {a : Nat} {ys : List Admin}
    (h : CodeR X m (throwing a) ys) : ys = throwing a := by
  have h' : CodeR X m (vals [.ref (.exn a)] ++ .plain .throwRef :: []) ys := h
  obtain ⟨x', rest', rfl, -, hx, hr⟩ := CodeR.split_nc h' rfl (by simp)
  rw [ARel.plain_simple rfl hx]
  cases hr
  rfl

theorem CodeR.throwing {X : SimCtx} {m : Mode} (a : Nat) : CodeR X m (throwing a) (throwing a) := by
  cases m
  · exact .cons (.ref trivial) (.cons .plainS .nil)
  · exact .cons (.ref trivial) (.cons (.plainO (.simple rfl)) .nil)

theorem CodeR.trap {X : SimCtx} {m : Mode} : CodeR X m [.trap] [.trap] := .cons .trap .nil

theorem CodeR.plain_simple {X : SimCtx} {m : Mode} {i : Instr} (hi : simpleI i = true) :
    CodeR X m [.plain i] [.plain i] := by
  cases m
  · exact .cons .plainS .nil
  · exact .cons (.plainO (.simple hi)) .nil

theorem ARel.frame_of {X : SimCtx} {m m' : Mode} {n : Nat} {fr fr' : Frame} {b b' : List Admin}
    (hf : FrameRel X m' fr fr') (hb : CodeR X m' b b') : ARel X m (.frame n fr b) (.frame n fr' b') := by
  cases m'
  · obtain ⟨rfl, hs⟩ := hf
    exact .frameS hs hb
  · exact .frameO hf hb

theorem ARel.label_of {X : SimCtx} {m : Mode} {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (hc : ContRel X m c c') (hb : CodeR X m b b') : ARel X m (.label n c b) (.label n c' b') := by
  cases m
  · cases hc; exact .labelS hb
  · exact .labelO hc hb

theorem ContRel.nil {X : SimCtx} {m : Mode} : ContRel X m [] [] := by
  cases m
  · rfl
  · exact IRels.nil

/-- The `CALL_REF` a returning tail call leaves behind is related to itself. -/
theorem ARel.retToCallIn {X : SimCtx} {m : Mode} {c : Admin} (hc : c.IsReturnCallRef)
    (mi : ModuleInst) : ARel X m (c.retToCallIn mi) (c.retToCallIn mi) := by
  rcases IsReturnCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · simp only [Admin.retToCallIn]
    split
    · exact .callRefType
    · cases m
      · exact .plainS
      · exact .plainO (.simple rfl)
  · exact .callRefType

theorem IsReturnCallRef.ne_callRefType {c : Admin} (hc : c.IsReturnCallRef) (d : DefType) :
    c ≠ .callRefType d := by
  rintro rfl; exact hc

/-- A return call is not code of the module. -/
theorem ARel.returnCall_same {X : SimCtx} {m : Mode} {c c' : Admin} (hc : c.IsReturnCallRef)
    (h : ARel X m c c') : m = .same ∧ c' = c := by
  rcases IsReturnCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact ARel.plain_other rfl rfl h
  · exact ARel.returnCallRefType_inv h

theorem ARel.callRef_eq {X : SimCtx} {m : Mode} {c c' : Admin} (hc : c.IsCallRef)
    (h : ARel X m c c') : c' = c := by
  rcases IsCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact ARel.plain_simple rfl h
  · exact ARel.callRefType_inv h

theorem sizeOf_label_lt (n : Nat) (c : List Instr) (b : List Admin) :
    sizeOf b < sizeOf (Admin.label n c b) := by
  simp only [Admin.label.sizeOf_spec]; omega

theorem sizeOf_handler_lt (n : Nat) (c : List Catch) (b : List Admin) :
    sizeOf b < sizeOf (Admin.handler n c b) := by
  simp only [Admin.handler.sizeOf_spec]; omega

theorem sizeOf_frame_lt (n : Nat) (f : Frame) (b : List Admin) :
    sizeOf b < sizeOf (Admin.frame n f b) := by
  simp only [Admin.frame.sizeOf_spec]; omega

end Silmaril.Wasm.Binaryen.RUMESim
