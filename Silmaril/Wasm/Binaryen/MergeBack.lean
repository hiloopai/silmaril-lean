module

public import Silmaril.Wasm.Binaryen.MergeScope

@[expose] public section

/-! # A linked step implies a source step

The linker's simulation (`WholeSimulation.step`) maps every source step to a
linked step. For behaviour sets without typing we also need the converse for
progress: when the linked configuration steps, so does the source configuration
related to it (`back`). The source may be ill-typed (an invocation with wrong
arguments), so this is not progress: it compares the premises of the rule taken
by the linked code with those of the source code. Lookups through relocated
indices are pulled back with the source's index scoping (`XI`); type tests are
decided either way; other premises read store fields the relation keeps equal.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type}

/-! ## Relocation preimages -/

/-- What a source instruction relocated to `j` looks like. -/
def Preimage (r : Relocation) (j i : Instr) : Prop :=
  match j with
  | .block bt' _ => ∃ bt body, i = .block bt body ∧ blockType? r.types bt = some bt'
  | .loop bt' _ => ∃ bt body, i = .loop bt body ∧ blockType? r.types bt = some bt'
  | .if_ bt' _ _ => ∃ bt yes no, i = .if_ bt yes no ∧ blockType? r.types bt = some bt'
  | .select (some _) => ∃ ts, i = .select (some ts)
  | .call y => ∃ x, i = .call x ∧ function? r x = some y
  | .returnCall y => ∃ x, i = .returnCall x ∧ function? r x = some y
  | .refFunc y => ∃ x, i = .refFunc x ∧ function? r x = some y
  | .callRef _ => ∃ x, i = .callRef x
  | .returnCallRef _ => ∃ x, i = .returnCallRef x
  | .globalGet y => ∃ x, i = .globalGet x ∧ shiftIdx? r.globals x = some y
  | .globalSet y => ∃ x, i = .globalSet x ∧ shiftIdx? r.globals x = some y
  | .refNull _ => ∃ h, i = .refNull h
  | .refTest _ => ∃ rt, i = .refTest rt
  | .refCast _ => ∃ rt, i = .refCast rt
  | .brOnCast l _ _ => ∃ a b, i = .brOnCast l a b
  | .brOnCastFail l _ _ => ∃ a b, i = .brOnCastFail l a b
  | .structNew y => ∃ x, i = .structNew x ∧ shiftIdx? r.types x = some y
  | .structNewDefault y => ∃ x, i = .structNewDefault x ∧ shiftIdx? r.types x = some y
  | .structGet sx y k => ∃ x, i = .structGet sx x k ∧ shiftIdx? r.types x = some y
  | .structSet y k => ∃ x, i = .structSet x k ∧ shiftIdx? r.types x = some y
  | .arrayNew y => ∃ x, i = .arrayNew x ∧ shiftIdx? r.types x = some y
  | .arrayNewDefault y => ∃ x, i = .arrayNewDefault x ∧ shiftIdx? r.types x = some y
  | .arrayNewFixed y n => ∃ x, i = .arrayNewFixed x n ∧ shiftIdx? r.types x = some y
  | .arrayGet sx y => ∃ x, i = .arrayGet sx x ∧ shiftIdx? r.types x = some y
  | .arraySet y => ∃ x, i = .arraySet x ∧ shiftIdx? r.types x = some y
  | .arrayFill y => ∃ x, i = .arrayFill x ∧ shiftIdx? r.types x = some y
  | .arrayCopy y₁ y₂ => ∃ x₁ x₂, i = .arrayCopy x₁ x₂ ∧ shiftIdx? r.types x₁ = some y₁ ∧
      shiftIdx? r.types x₂ = some y₂
  | j => i = j

theorem preimage {r : Relocation} {i j : Instr} (h : instruction? r i = some j) :
    Preimage r j i := by
  cases i
  case select ts =>
    cases ts with
    | none =>
      simp only [instruction?, Option.some.injEq] at h
      subst h
      exact rfl
    | some ts =>
      simp only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ts', -, rfl⟩ := h
      exact ⟨_, rfl⟩
  all_goals simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    reduceCtorEq] at h
  all_goals first
    | (subst h; exact rfl)
    | (obtain ⟨y, hy, rfl⟩ := h; first | exact ⟨_, rfl, hy⟩ | exact ⟨_, rfl⟩)
    | (obtain ⟨a, ha, b, hb, rfl⟩ := h
       first | exact ⟨_, _, rfl, ha, hb⟩ | exact ⟨_, _, rfl, ha⟩ | exact ⟨_, _, rfl⟩)
    | (obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h; exact ⟨_, _, _, rfl, ha⟩)

theorem inv_fixed {mode : Mode} {i j : Instr} (hr : Instruction mode i j)
    (hfix : ∀ r, Preimage r j i → i = j) : i = j := by
  cases mode with
  | same => exact hr
  | relocated r => exact hfix r (preimage hr)

theorem inv_none {r : Relocation} {i j : Instr} (hr : Instruction (.relocated r) i j)
    (hfix : Preimage r j i → i = j) (hnone : instruction? r j = none) : False := by
  have hi := hfix (preimage hr)
  subst hi
  change instruction? r i = some i at hr
  rw [hnone] at hr
  cases hr

theorem value_source {mode : Mode} {i j : Instr} {v : Val} (hr : Instruction mode i j)
    (hb : Admin.plain j = v.toAdmin) : Admin.plain i = v.toAdmin := by
  have hv : (Admin.plain j).val? = some v := by rw [hb]; exact Admin.val?_toAdmin v
  cases mode with
  | same =>
    change i = j at hr
    subst hr
    exact hb
  | relocated r =>
    have hp := preimage (r := r) hr
    cases j <;> simp only [Admin.val?, reduceCtorEq] at hv
    all_goals (change i = _ at hp; subst hp; exact hb)

theorem toAdmin_ne {v : Val} {b : Admin} (hb : v.toAdmin = b) (hn : b.val? = none) : False := by
  rw [← hb, Admin.val?_toAdmin] at hn
  cases hn

/-! ## Inverting the code relation from the linked side -/

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.nil_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin}
    (h : Control mode m m' xs []) : xs = [] := by
  cases h
  rfl

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.value_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {v : Val}
    (h : Control mode m m' xs (v.toAdmin :: ys)) :
    ∃ rest, xs = v.toAdmin :: rest ∧ Control mode m m' rest ys := by
  generalize hb : v.toAdmin = b at h
  cases h
  case plain hr rest =>
    refine ⟨_, ?_, rest⟩
    rw [value_source hr hb.symm, hb]
  case val rest => exact ⟨_, rfl, rest⟩
  case ref rest => exact ⟨_, rfl, rest⟩
  all_goals exact (toAdmin_ne hb rfl).elim

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.vals_right {mode : Mode}
    {m m' : ModuleInst} {vs : List Val} {xs ys : List Admin}
    (h : Control mode m m' xs (vals vs ++ ys)) :
    ∃ rest, xs = vals vs ++ rest ∧ Control mode m m' rest ys := by
  induction vs generalizing xs with
  | nil => exact ⟨_, rfl, h⟩
  | cons v vs ih =>
    obtain ⟨rest, rfl, hr⟩ := Control.value_right (v := v) h
    obtain ⟨rest', rfl, hr'⟩ := ih hr
    exact ⟨rest', rfl, hr'⟩

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.plain_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {j : Instr}
    (h : Control mode m m' xs (.plain j :: ys)) (nonvalue : (Admin.plain j).val? = none)
    (nonthrow : j ≠ .throwRef := by intro h; cases h) :
    ∃ i rest, xs = .plain i :: rest ∧ Instruction mode i j ∧ Control mode m m' rest ys := by
  generalize ha : Admin.plain j = b at h
  cases h
  case plain rewrite tail => cases ha; exact ⟨_, _, rfl, rewrite, tail⟩
  case val tail => exact (toAdmin_ne ha.symm nonvalue).elim
  case throwRef rest => cases ha; exact (nonthrow rfl).elim
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.throwRef_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin}
    (h : Control mode m m' xs (.plain .throwRef :: ys)) :
    ∃ rest, xs = .plain .throwRef :: rest ∧ Control mode m m' rest ys := by
  generalize ha : Admin.plain .throwRef = b at h
  cases h
  case plain rewrite tail =>
    cases ha
    refine ⟨_, ?_, tail⟩
    rw [inv_fixed rewrite (fun _ h => h)]
  case val tail => exact (toAdmin_ne ha.symm rfl).elim
  case throwRef rest => exact ⟨_, rfl, rest⟩
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.label_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {n : Nat}
    {cont : List Instr} {body : List Admin}
    (h : Control mode m m' xs (.label n cont body :: ys)) :
    ∃ cont₀ body₀ rest, xs = .label n cont₀ body₀ :: rest ∧ Instructions mode cont₀ cont ∧
      Control mode m m' body₀ body ∧ Control mode m m' rest ys := by
  generalize ha : Admin.label n cont body = b at h
  cases h
  case label continuation inner rest => cases ha; exact ⟨_, _, _, rfl, continuation, inner, rest⟩
  case val tail => exact (toAdmin_ne ha.symm rfl).elim
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.frame_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {n : Nat}
    {f : Frame} {body : List Admin} (h : Control mode m m' xs (.frame n f body :: ys)) :
    ∃ (innerMode : Mode) (f₀ : Frame) (body₀ rest : List Admin), xs = .frame n f₀ body₀ :: rest ∧
      Frames innerMode f₀ f ∧ Control innerMode f₀.module f.module body₀ body ∧
      Control mode m m' rest ys := by
  generalize ha : Admin.frame n f body = b at h
  cases h
  case frame frames inner rest => cases ha; exact ⟨_, _, _, _, rfl, frames, inner, rest⟩
  case val tail => exact (toAdmin_ne ha.symm rfl).elim
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.handler_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {n : Nat}
    {cs : List Catch} {body : List Admin} (h : Control mode m m' xs (.handler n cs body :: ys)) :
    ∃ body₀ rest, xs = .handler n cs body₀ :: rest ∧ mode = .same ∧ m = m' ∧
      Control mode m m' body₀ body ∧ Control mode m m' rest ys := by
  generalize ha : Admin.handler n cs body = b at h
  cases h
  case handler inner rest => cases ha; exact ⟨_, _, rfl, rfl, rfl, inner, rest⟩
  case val tail => exact (toAdmin_ne ha.symm rfl).elim
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.trap_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin}
    (h : Control mode m m' xs (.trap :: ys)) :
    ∃ rest, xs = .trap :: rest ∧ Control mode m m' rest ys := by
  generalize ha : Admin.trap = b at h
  cases h
  case trap rest => exact ⟨_, rfl, rest⟩
  case val tail => exact (toAdmin_ne ha.symm rfl).elim
  all_goals cases ha

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.ref_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {r : Ref}
    (h : Control mode m m' xs (.ref r :: ys)) :
    ∃ rest, xs = .ref r :: rest ∧ Control mode m m' rest ys :=
  Control.value_right (v := .ref r) h

/-- A call-reference administrative instruction is related only to another one. -/
theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.callRef_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin} {c : Admin}
    (h : Control mode m m' xs (c :: ys)) (hc : c.IsCallRef) :
    ∃ c₀ rest, xs = c₀ :: rest ∧ c₀.IsCallRef ∧ Control mode m m' rest ys := by
  cases c with
  | plain j =>
    cases j <;> try exact (hc : False).elim
    obtain ⟨i, rest, rfl, hr, tail⟩ := h.plain_right rfl
    refine ⟨_, _, rfl, ?_, tail⟩
    cases mode with
    | same =>
      change i = _ at hr
      subst hr
      trivial
    | relocated r =>
      obtain ⟨x, rfl⟩ := preimage (r := r) hr
      trivial
  | callRefType d =>
    generalize ha : Admin.callRefType d = b at h
    cases h
    case callRefType rest => exact ⟨_, _, rfl, trivial, rest⟩
    case val tail => exact (toAdmin_ne ha.symm rfl).elim
    all_goals cases ha
  | _ => exact (hc : False).elim

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.returnCallRef_right {mode : Mode} {m m' : ModuleInst} {xs ys : List Admin}
    {c : Admin} (h : Control mode m m' xs (c :: ys)) (hc : c.IsReturnCallRef) :
    ∃ c₀ rest, xs = c₀ :: rest ∧ c₀.IsReturnCallRef ∧ Control mode m m' rest ys := by
  cases c with
  | plain j =>
    cases j <;> try exact (hc : False).elim
    obtain ⟨i, rest, rfl, hr, tail⟩ := h.plain_right rfl
    refine ⟨_, _, rfl, ?_, tail⟩
    cases mode with
    | same =>
      change i = _ at hr
      subst hr
      trivial
    | relocated r =>
      obtain ⟨x, rfl⟩ := preimage (r := r) hr
      trivial
  | returnCallRefType d =>
    generalize ha : Admin.returnCallRefType d = b at h
    cases h
    case returnCallRefType rest => exact ⟨_, _, rfl, trivial, rest⟩
    case val tail => exact (toAdmin_ne ha.symm rfl).elim
    all_goals cases ha
  | _ => exact (hc : False).elim

/-- A value sequence followed by one fixed, non-value instruction. -/
theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.vals_plain_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin}
    {vs : List Val} {j : Instr} (h : Control mode m m' xs (vals vs ++ [.plain j]))
    (nonvalue : (Admin.plain j).val? = none) (nonthrow : j ≠ .throwRef := by intro h; cases h) :
    ∃ i, xs = vals vs ++ [.plain i] ∧ Instruction mode i j := by
  obtain ⟨rest, rfl, hr⟩ := h.vals_right
  obtain ⟨i, rest', rfl, hi, hn⟩ := hr.plain_right nonvalue nonthrow
  rw [hn.nil_right]
  exact ⟨i, rfl, hi⟩

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.vals_right_exact {mode : Mode} {m m' : ModuleInst} {xs : List Admin}
    {vs : List Val} (h : Control mode m m' xs (vals vs)) : xs = vals vs := by
  have h' : Control mode m m' xs (vals vs ++ []) := by simpa using h
  obtain ⟨rest, rfl, hr⟩ := h'.vals_right
  rw [hr.nil_right, List.append_nil]

/-! ## Frames and lookups -/

theorem frames_same {f₀ f : Frame} (h : Frames .same f₀ f) : f₀ = f := by
  obtain ⟨view, locals⟩ := h
  obtain ⟨l₀, m₀⟩ := f₀
  obtain ⟨l, m⟩ := f
  cases view
  simp only at locals
  subst locals
  rfl

theorem frames_view {mode : Mode} {f₀ f : Frame} (h : Frames mode f₀ f) :
    View mode f₀.module f.module := h.view

theorem inv_call {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y : FuncIdx}
    (view : View mode m₀ m) (hr : Instruction mode i (.call y)) (hsc : XI m₀ i) {a : Nat}
    (ha : m.funcs[y.toNat]? = some a) : ∃ x, i = .call x ∧ m₀.funcs[x.toNat]? = some a := by
  cases view with
  | same _ => exact ⟨y, hr, ha⟩
  | relocated views =>
    obtain ⟨x, rfl, hx⟩ := preimage hr
    have hlt : x.toNat < m₀.funcs.length := by simp only [XI, XE] at hsc; exact hsc.2
    refine ⟨x, rfl, ?_⟩
    have h0 := List.getElem?_eq_getElem hlt
    have h1 := views.functions hx h0
    rw [ha] at h1
    cases h1
    exact h0

theorem inv_returnCall {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y : FuncIdx}
    (view : View mode m₀ m) (hr : Instruction mode i (.returnCall y)) (hsc : XI m₀ i) {a : Nat}
    (ha : m.funcs[y.toNat]? = some a) :
    ∃ x, i = .returnCall x ∧ m₀.funcs[x.toNat]? = some a := by
  cases view with
  | same _ => exact ⟨y, hr, ha⟩
  | relocated views =>
    obtain ⟨x, rfl, hx⟩ := preimage hr
    have hlt : x.toNat < m₀.funcs.length := by simp only [XI, XE] at hsc; exact hsc.2
    refine ⟨x, rfl, ?_⟩
    have h0 := List.getElem?_eq_getElem hlt
    have h1 := views.functions hx h0
    rw [ha] at h1
    cases h1
    exact h0

theorem inv_refFunc {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y : FuncIdx}
    (view : View mode m₀ m) (hr : Instruction mode i (.refFunc y)) (hsc : XI m₀ i) {a : Nat}
    (ha : m.funcs[y.toNat]? = some a) :
    ∃ x, i = .refFunc x ∧ m₀.funcs[x.toNat]? = some a := by
  cases view with
  | same _ => exact ⟨y, hr, ha⟩
  | relocated views =>
    obtain ⟨x, rfl, hx⟩ := preimage hr
    have hlt : x.toNat < m₀.funcs.length := by simp only [XI, XE] at hsc; exact hsc.2
    refine ⟨x, rfl, ?_⟩
    have h0 := List.getElem?_eq_getElem hlt
    have h1 := views.functions hx h0
    rw [ha] at h1
    cases h1
    exact h0

/-- A global lookup through a relocated index pulls back. -/
theorem inv_global {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y : GlobalIdx}
    (C : GlobalIdx → Instr) (view : View mode m₀ m) (hr : Instruction mode i (C y))
    (hpre : ∀ r, Preimage r (C y) i → ∃ x, i = C x ∧ shiftIdx? r.globals x = some y)
    (hsc : ∀ x, XI m₀ (C x) → x.toNat < m₀.globals.length) (hi : XI m₀ i) :
    ∃ x, i = C x ∧ ∀ a, m.globals[y.toNat]? = some a → m₀.globals[x.toNat]? = some a := by
  cases view with
  | same _ => exact ⟨y, hr, fun _ h => h⟩
  | relocated views =>
    obtain ⟨x, rfl, hx⟩ := hpre _ (preimage hr)
    refine ⟨x, rfl, fun a ha => ?_⟩
    have h0 := List.getElem?_eq_getElem (hsc x hi)
    have h1 := views.globals hx h0
    rw [ha] at h1
    cases h1
    exact h0

/-- A type lookup through a relocated index pulls back. -/
theorem inv_type {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y : TypeIdx}
    (C : TypeIdx → Instr) (view : View mode m₀ m) (hr : Instruction mode i (C y))
    (hpre : ∀ r, Preimage r (C y) i → ∃ x, i = C x ∧ shiftIdx? r.types x = some y)
    (hsc : ∀ x, XI m₀ (C x) → x.toNat < m₀.types.length) (hi : XI m₀ i) :
    ∃ x, i = C x ∧ ∀ d, m.types[y.toNat]? = some d → m₀.types[x.toNat]? = some d := by
  cases view with
  | same _ => exact ⟨y, hr, fun _ h => h⟩
  | relocated views =>
    obtain ⟨x, rfl, hx⟩ := hpre _ (preimage hr)
    refine ⟨x, rfl, fun d hd => ?_⟩
    have h0 := List.getElem?_eq_getElem (hsc x hi)
    have h1 := views.types hx h0
    rw [hd] at h1
    cases h1
    exact h0

/-- Block types pull back with their source scoping. -/
theorem block_back {r : Relocation} {m₀ m : ModuleInst} {bt₀ bt : BlockType}
    {p : List CValType × List CValType} (views : Views.Successful r m₀ m)
    (hr : blockType? r.types bt₀ = some bt) (hsc : ControlViews.BlockScoped m₀.types.length bt₀)
    (hp : m.blockType? bt = some p) : m₀.blockType? bt₀ = some p := by
  have hsome : ∃ q, m₀.blockType? bt₀ = some q := by
    cases bt₀ with
    | empty => exact ⟨_, rfl⟩
    | value v => exact ⟨_, rfl⟩
    | typeIdx x =>
      have hx : x.toNat < m₀.types.length := hsc
      have h0 := List.getElem?_eq_getElem hx
      simp only [Link.GC.blockType?, Option.map_eq_map, Option.map_eq_some_iff] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      have h1 := views.types hy h0
      simp only [ModuleInst.blockType?, h1, Option.bind_eq_bind, Option.bind_some] at hp
      exact ⟨p, by simp only [ModuleInst.blockType?, h0, Option.bind_eq_bind, Option.bind_some, hp]⟩
  obtain ⟨q, hq⟩ := hsome
  have := ControlViews.block_lookup views hr hsc hq
  rw [hp] at this
  cases this
  exact hq

theorem inv_blockType {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {bt : BlockType}
    {p : List CValType × List CValType} (C : BlockType → Instr) (view : View mode m₀ m)
    (hr : Instruction mode i (C bt))
    (hpre : ∀ r, Preimage r (C bt) i → ∃ bt₀, i = C bt₀ ∧ blockType? r.types bt₀ = some bt)
    (hsc : ∀ bt₀, XI m₀ (C bt₀) → ControlViews.BlockScoped m₀.types.length bt₀) (hi : XI m₀ i)
    (hp : m.blockType? bt = some p) : ∃ bt₀, i = C bt₀ ∧ m₀.blockType? bt₀ = some p := by
  cases view with
  | same _ => exact ⟨bt, hr, hp⟩
  | relocated views =>
    obtain ⟨bt₀, rfl, hb⟩ := hpre _ (preimage hr)
    exact ⟨bt₀, rfl, block_back views hb (hsc bt₀ hi) hp⟩

/-! ## Store transport for unchanged code -/

theorem store_eta {s t : Store H} (h : StoreRelation.State s t) : s = { t with funcs := s.funcs } := by
  obtain ⟨tags, globals, mems, tables, funcs, datas, elems, structs, arrays, exns⟩ := s
  obtain ⟨⟩ := t
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

theorem variable_funcs {t t' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : VariableStep ⟨t, f, is⟩ ⟨t', f', is'⟩) (F : List (FuncInst H)) :
    VariableStep ⟨{ t with funcs := F }, f, is⟩ ⟨{ t' with funcs := F }, f', is'⟩ := by
  cases h <;> constructor <;> assumption

theorem table_funcs {P : Profile} {t t' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : TableStep P ⟨t, f, is⟩ ⟨t', f', is'⟩) (F : List (FuncInst H)) :
    TableStep P ⟨{ t with funcs := F }, f, is⟩ ⟨{ t' with funcs := F }, f', is'⟩ := by
  cases h <;> constructor <;> assumption

theorem memory_funcs {P : Profile} {t t' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : MemoryStep P ⟨t, f, is⟩ ⟨t', f', is'⟩) (F : List (FuncInst H)) :
    MemoryStep P ⟨{ t with funcs := F }, f, is⟩ ⟨{ t' with funcs := F }, f', is'⟩ := by
  cases h <;> constructor <;> assumption

theorem aggregate_funcs {t t' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : AggregateStep ⟨t, f, is⟩ ⟨t', f', is'⟩) (F : List (FuncInst H)) :
    AggregateStep ⟨{ t with funcs := F }, f, is⟩ ⟨{ t' with funcs := F }, f', is'⟩ := by
  cases h
  case arrayCopyOob₂ => apply AggregateStep.arrayCopyOob₂ <;> assumption
  case arrayInitElemOob₂ => apply AggregateStep.arrayInitElemOob₂ <;> assumption
  case arrayInitDataOob₂ => apply AggregateStep.arrayInitDataOob₂ <;> assumption
  all_goals (constructor! <;> assumption)


/-! ## More inversions -/

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.cons_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {b : Admin}
    {ys : List Admin} (h : Control mode m m' xs (b :: ys)) :
    ∃ a xs', xs = a :: xs' ∧ Control mode m m' [a] [b] ∧ Control mode m m' xs' ys := by
  generalize hy : b :: ys = zs at h
  cases h with
  | nil => cases hy
  | plain hr rest => cases hy; exact ⟨_, _, rfl, .plain hr .nil, rest⟩
  | val rest => cases hy; exact ⟨_, _, rfl, .val .nil, rest⟩
  | ref rest => cases hy; exact ⟨_, _, rfl, .ref .nil, rest⟩
  | callRefType rest => cases hy; exact ⟨_, _, rfl, .callRefType .nil, rest⟩
  | returnCallRefType rest => cases hy; exact ⟨_, _, rfl, .returnCallRefType .nil, rest⟩
  | throwRef rest => cases hy; exact ⟨_, _, rfl, .throwRef .nil, rest⟩
  | label hc hb rest => cases hy; exact ⟨_, _, rfl, .label hc hb .nil, rest⟩
  | handler hb rest => cases hy; exact ⟨_, _, rfl, .handler hb .nil, rest⟩
  | frame hf hb rest => cases hy; exact ⟨_, _, rfl, .frame hf hb .nil, rest⟩
  | trap rest => cases hy; exact ⟨_, _, rfl, .trap .nil, rest⟩

theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.append_right {mode : Mode}
    {m m' : ModuleInst} {xs ys zs : List Admin} (h : Control mode m m' zs (xs ++ ys)) :
    ∃ xs' ys', zs = xs' ++ ys' ∧ Control mode m m' xs' xs ∧ Control mode m m' ys' ys := by
  induction xs generalizing zs with
  | nil => exact ⟨[], zs, rfl, .nil, h⟩
  | cons b xs ih =>
    obtain ⟨a, zs', rfl, hab, hrest⟩ := Control.cons_right h
    obtain ⟨xs', ys', rfl, hx, hy⟩ := ih hrest
    exact ⟨a :: xs', ys', rfl, hab.append hx, hy⟩

/-- Values, one fixed non-value instruction, then a suffix. -/
theorem _root_.Silmaril.Wasm.Link.GC.AdminRelation.Control.vals_plain_rest_right {mode : Mode} {m m' : ModuleInst} {xs rest : List Admin}
    {vs : List Val} {j : Instr} (h : Control mode m m' xs (vals vs ++ [.plain j] ++ rest))
    (nonvalue : (Admin.plain j).val? = none) (nonthrow : j ≠ .throwRef := by intro h; cases h) :
    ∃ i rest₀, xs = vals vs ++ [.plain i] ++ rest₀ ∧ Instruction mode i j ∧
      Control mode m m' rest₀ rest := by
  rw [List.append_assoc] at h
  obtain ⟨R, rfl, hR⟩ := h.vals_right
  obtain ⟨i, rest₀, rfl, hi, hr⟩ := hR.plain_right nonvalue nonthrow
  exact ⟨i, rest₀, by simp, hi, hr⟩

theorem xi_of_vals_plain {m : ModuleInst} {vs : List Val} {i : Instr} {rest : List Admin}
    (h : XAs m (vals vs ++ [.plain i] ++ rest)) : XI m i := by
  simp only [xas_append_iff, xas_cons_iff, xa_plain] at h
  exact h.1.2.1

theorem xi_of_vals_plain' {m : ModuleInst} {vs : List Val} {i : Instr}
    (h : XAs m (vals vs ++ [.plain i])) : XI m i :=
  xi_of_vals_plain (vs := vs) (rest := []) (by simpa using h)

theorem inv_select {mode : Mode} {i : Instr} {ts : Option (List ValType)}
    (hr : Instruction mode i (.select ts)) : ∃ ts₀, i = .select ts₀ := by
  cases mode with
  | same => exact ⟨ts, hr⟩
  | relocated r =>
    have hp := preimage (r := r) hr
    cases ts with
    | none => exact ⟨none, hp⟩
    | some ts => obtain ⟨ts₀, rfl⟩ := hp; exact ⟨_, rfl⟩

theorem inv_refNull {mode : Mode} {i : Instr} {ht : HeapType}
    (hr : Instruction mode i (.refNull ht)) : ∃ h₀, i = .refNull h₀ := by
  cases mode with
  | same => exact ⟨ht, hr⟩
  | relocated r => exact preimage (r := r) hr

theorem inv_refTest {mode : Mode} {i : Instr} {rt : RefType}
    (hr : Instruction mode i (.refTest rt)) : ∃ rt₀, i = .refTest rt₀ := by
  cases mode with
  | same => exact ⟨rt, hr⟩
  | relocated r => exact preimage (r := r) hr

theorem inv_refCast {mode : Mode} {i : Instr} {rt : RefType}
    (hr : Instruction mode i (.refCast rt)) : ∃ rt₀, i = .refCast rt₀ := by
  cases mode with
  | same => exact ⟨rt, hr⟩
  | relocated r => exact preimage (r := r) hr

theorem inv_brOnCast {mode : Mode} {i : Instr} {l : LabelIdx} {a b : RefType}
    (hr : Instruction mode i (.brOnCast l a b)) : ∃ a₀ b₀, i = .brOnCast l a₀ b₀ := by
  cases mode with
  | same => exact ⟨a, b, hr⟩
  | relocated r => exact preimage (r := r) hr

theorem inv_brOnCastFail {mode : Mode} {i : Instr} {l : LabelIdx} {a b : RefType}
    (hr : Instruction mode i (.brOnCastFail l a b)) : ∃ a₀ b₀, i = .brOnCastFail l a₀ b₀ := by
  cases mode with
  | same => exact ⟨a, b, hr⟩
  | relocated r => exact preimage (r := r) hr

theorem inv_if {mode : Mode} {i : Instr} {bt : BlockType} {y n : List Instr}
    (hr : Instruction mode i (.if_ bt y n)) : ∃ bt₀ y₀ n₀, i = .if_ bt₀ y₀ n₀ := by
  cases mode with
  | same => exact ⟨bt, y, n, hr⟩
  | relocated r =>
    obtain ⟨bt₀, y₀, n₀, rfl, -⟩ := preimage (r := r) hr
    exact ⟨bt₀, y₀, n₀, rfl⟩

theorem inv_block {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {bt : BlockType}
    {body : List Instr} {p : List CValType × List CValType} (view : View mode m₀ m)
    (hr : Instruction mode i (.block bt body)) (hi : XI m₀ i) (hp : m.blockType? bt = some p) :
    ∃ bt₀ body₀, i = .block bt₀ body₀ ∧ m₀.blockType? bt₀ = some p := by
  cases view with
  | same _ => exact ⟨bt, body, hr, hp⟩
  | relocated views =>
    obtain ⟨bt₀, body₀, rfl, hb⟩ := preimage hr
    exact ⟨bt₀, body₀, rfl, block_back views hb (xi_block.mp hi).1 hp⟩

theorem inv_loop {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {bt : BlockType}
    {body : List Instr} {p : List CValType × List CValType} (view : View mode m₀ m)
    (hr : Instruction mode i (.loop bt body)) (hi : XI m₀ i) (hp : m.blockType? bt = some p) :
    ∃ bt₀ body₀, i = .loop bt₀ body₀ ∧ m₀.blockType? bt₀ = some p := by
  cases view with
  | same _ => exact ⟨bt, body, hr, hp⟩
  | relocated views =>
    obtain ⟨bt₀, body₀, rfl, hb⟩ := preimage hr
    exact ⟨bt₀, body₀, rfl, block_back views hb (xi_loop.mp hi).1 hp⟩

theorem inv_arrayCopy {mode : Mode} {m₀ m : ModuleInst} {i : Instr} {y₁ y₂ : TypeIdx}
    (view : View mode m₀ m) (hr : Instruction mode i (.arrayCopy y₁ y₂)) (hi : XI m₀ i) :
    ∃ x₁ x₂, i = .arrayCopy x₁ x₂ ∧
      ∀ d, m.types[y₂.toNat]? = some d → m₀.types[x₂.toNat]? = some d := by
  cases view with
  | same _ => exact ⟨y₁, y₂, hr, fun _ h => h⟩
  | relocated views =>
    obtain ⟨x₁, x₂, rfl, -, h₂⟩ := preimage hr
    refine ⟨x₁, x₂, rfl, fun d hd => ?_⟩
    have hlt : x₂.toNat < m₀.types.length := by simp only [XI, XE] at hi; exact hi.2.2
    have h0 := List.getElem?_eq_getElem hlt
    have h1 := views.types h₂ h0
    rw [hd] at h1
    cases h1
    exact h0

theorem plain_of_fam {e : Admin} {k : SingleThreaded.Det.Fam} (hk : famOf e = k)
    (hc : k ≠ .control) : ∃ j, e = .plain j := by
  cases e with
  | plain j => exact ⟨j, rfl⟩
  | _ => exact absurd hk.symm hc

theorem ne_throwRef_of_fam {j : Instr} {k : SingleThreaded.Det.Fam}
    (hk : famOf (.plain j) = k) (hc : k ≠ .control) : j ≠ .throwRef := by
  rintro rfl
  exact hc hk.symm

theorem fixed_numeric {j : Instr} (hk : famOf (.plain j) = .numeric) :
    ∀ r i, Preimage r j i → i = j := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> exact fun _ _ hp => hp

theorem fixed_vector {j : Instr} (hk : famOf (.plain j) = .vector) :
    ∀ r i, Preimage r j i → i = j := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> exact fun _ _ hp => hp

theorem fixed_table {j : Instr} (hk : famOf (.plain j) = .table) :
    ∀ r i, Preimage r j i → i = j := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> exact fun _ _ hp => hp

theorem fixed_memory {j : Instr} (hk : famOf (.plain j) = .memory) :
    ∀ r i, Preimage r j i → i = j := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> exact fun _ _ hp => hp

theorem none_table {j : Instr} (hk : famOf (.plain j) = .table) (r : Relocation) :
    instruction? r j = none := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> simp [instruction?]

theorem none_memory {j : Instr} (hk : famOf (.plain j) = .memory) (r : Relocation) :
    instruction? r j = none := by
  cases j <;> (try simp only [famOf, reduceCtorEq] at hk) <;> simp [instruction?]

theorem Function.wasm_back {fi₀ fi : FuncInst H} {code : Func} (h : StoreRelation.Function fi₀ fi)
    (hc : fi.code = .wasm code) : ∃ code₀, fi₀.code = .wasm code₀ := by
  cases h with
  | same => exact ⟨code, hc⟩
  | relocated _ _ _ => exact ⟨_, rfl⟩

theorem global_back {s₀ s : Store H} {f₀ f : Frame} {x y : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hg : s.global? f y = some (a, g))
    (hglob : ∀ a, f.module.globals[y.toNat]? = some a → f₀.module.globals[x.toNat]? = some a)
    (heq : s₀.globals = s.globals) : s₀.global? f₀ x = some (a, g) := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨a', ha, g', hg', rfl, rfl⟩ := hg
  simp only [Store.global?, hglob a' ha, Option.bind_eq_bind, Option.bind_some, heq, hg',
    Option.pure_def]

theorem catchMatches_iff {s₀ s : Store H} {f : Frame} {a : Nat} {c : Catch}
    (h : s₀.exns = s.exns) : CatchMatches s₀ f a c ↔ CatchMatches s f a c := by
  cases c <;> simp only [CatchMatches, h]

theorem xi_of_mem {m : ModuleInst} {X : List Admin} {i : Instr} (h : XAs m X)
    (hi : Admin.plain i ∈ X) : XI m i :=
  xa_plain.mp (h _ hi)

set_option hygiene false in
/-- Peel the value operands off a literal linked code and invert its final
instruction: `hco : Control mode m m' X [v₁, …, vₙ, .plain j]` becomes
`X = [v₁, …, vₙ, .plain i]` with `hr : Instruction mode i j`. -/
macro "inv_head " hco:ident i:ident hr:ident : tactic => `(tactic| (
  repeat (first
    | (obtain ⟨_, hX_, hco_⟩ := Control.ref_right $hco
       subst hX_
       clear $hco
       have $hco := hco_
       clear hco_)
    | (obtain ⟨_, hX_, hco_⟩ := Control.value_right $hco
       subst hX_
       clear $hco
       have $hco := hco_
       clear hco_))
  obtain ⟨$i, _, hX_, $hr, hn_⟩ := Control.plain_right $hco rfl
  subst hX_
  obtain rfl := Control.nil_right hn_))

/-! ## Backward progress -/

/-- Backward progress for aggregate rules retains the actual leaf family.
This extracts the existing branch of `back` without changing its witnesses. -/
theorem aggregate_back_progress {ct ct' : Config H} (h : AggregateStep ct ct') :
    ∀ {mode : Mode} {s₀ : Store H} {f₀ : Frame} {X : List Admin},
      StoreRelation.Related s₀ ct.store → Frames mode f₀ ct.frame →
      Control mode f₀.module ct.frame.module X ct.code → XAs f₀.module X →
      ∃ c, AggregateStep ⟨s₀, f₀, X⟩ c := by
  obtain ⟨s, f, Y⟩ := ct
  obtain ⟨s', f', Y'⟩ := ct'
  intro mode s₀ f₀ X hst hfr hco hsc
  dsimp only at hst hfr hco
  cases mode with
  | same =>
    obtain rfl := frames_same hfr
    obtain ⟨args, e, rfl, hev, hfam⟩ := AggregateStep.shape h
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    change i = j at hr
    subst hr
    rw [store_eta hst.toState]
    exact ⟨_, (aggregate_funcs h _)⟩
  | relocated r =>
    have view := frames_view hfr
    have tyS : ∀ {C : TypeIdx → Instr},
        (∀ x, XE f₀.module (C x) → x.toNat < f₀.module.types.length) →
        ∀ x, XI f₀.module (C x) → x.toNat < f₀.module.types.length :=
      fun hC x h => hC x h.2
    cases h with
    | structNew hd he hn hp =>
      obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .structNew y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.structNew (hx _ hd) he hn hp)⟩
    | structNewDefault hd he hdef =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .structNewDefault y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.structNewDefault (hx _ hd) he hdef)⟩
    | structGetNull =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .structGet _ y _) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, .structGetNull⟩
    | structGetStruct hs hf hd he hi hu =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .structGet _ y _) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.structGetStruct (by rw [hst.structs]; exact hs) hf (hx _ hd) he hi hu)⟩
    | structSetNull =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .structSet y _) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, .structSetNull⟩
    | structSetStruct hd he hi hs hf hp =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .structSet y _) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.structSetStruct (hx _ hd) he hi (by rw [hst.structs]; exact hs) hf hp)⟩
    | arrayNew v n =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayNew y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayNew v n)⟩
    | arrayNewDefault hd he hv =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .arrayNewDefault y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayNewDefault (hx _ hd) he hv)⟩
    | arrayNewFixed hd he hn hp =>
      obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .arrayNewFixed y _) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayNewFixed (hx _ hd) he hn hp)⟩
    | arrayNewElemOob _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayNewElemAlloc _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayNewDataOob _ _ _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayNewDataNum _ _ _ _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayGetNull =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayGet _ y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, .arrayGetNull⟩
    | arrayGetOob ha h =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayGet _ y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayGetOob (by rw [hst.arrays]; exact ha) h)⟩
    | arrayGetArray ha h hd he hu =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .arrayGet _ y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayGetArray (by rw [hst.arrays]; exact ha) h (hx _ hd) he hu)⟩
    | arraySetNull =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arraySet y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, .arraySetNull⟩
    | arraySetOob ha h =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arraySet y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arraySetOob (by rw [hst.arrays]; exact ha) h)⟩
    | arraySetArray ha h hd he hp =>
      inv_head hco i hr
      obtain ⟨x, rfl, hx⟩ := inv_type (fun y => .arraySet y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arraySetArray (by rw [hst.arrays]; exact ha) h (hx _ hd) he hp)⟩
    | arrayLenNull =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .arrayLenNull⟩
    | arrayLenArray ha =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, (.arrayLenArray (by rw [hst.arrays]; exact ha))⟩
    | arrayFillNull =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayFill y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, .arrayFillNull⟩
    | arrayFillOob ha h =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayFill y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayFillOob (by rw [hst.arrays]; exact ha) h)⟩
    | arrayFillZero ha h =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayFill y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayFillZero (by rw [hst.arrays]; exact ha) h)⟩
    | arrayFillSucc ha h hn =>
      inv_head hco i hr
      obtain ⟨x, rfl, -⟩ := inv_type (fun y => .arrayFill y) view hr (fun _ h => h)
        (tyS fun x h => by simpa only [XE] using h) (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayFillSucc (by rw [hst.arrays]; exact ha) h hn)⟩
    | arrayCopyNull₁ =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, -⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, .arrayCopyNull₁⟩
    | arrayCopyNull₂ =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, -⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, .arrayCopyNull₂⟩
    | arrayCopyOob₁ ha h =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, -⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayCopyOob₁ (by rw [hst.arrays]; exact ha) h)⟩
    | arrayCopyOob₂ ha h =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, -⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayCopyOob₂ (by rw [hst.arrays]; exact ha) h)⟩
    | arrayCopyZero ha₁ ha₂ h =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, -⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayCopyZero (by rw [hst.arrays]; exact ha₁)
        (by rw [hst.arrays]; exact ha₂) h)⟩
    | arrayCopyLe ha₁ ha₂ h hn hd he hle =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, hx⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayCopyLe (by rw [hst.arrays]; exact ha₁)
        (by rw [hst.arrays]; exact ha₂) h hn (hx _ hd) he hle)⟩
    | arrayCopyGt ha₁ ha₂ h hn hd he hgt =>
      inv_head hco i hr
      obtain ⟨x₁, x₂, rfl, hx⟩ := inv_arrayCopy view hr (xi_of_mem hsc (by simp))
      exact ⟨_, (.arrayCopyGt (by rw [hst.arrays]; exact ha₁)
        (by rw [hst.arrays]; exact ha₂) h hn (hx _ hd) he hgt)⟩
    | arrayInitElemNull =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitElemOob₁ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitElemOob₂ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitElemZero _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitElemSucc _ _ _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitDataNull =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitDataOob₁ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitDataOob₂ _ _ _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitDataZero _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
    | arrayInitDataNum _ _ _ _ _ _ _ =>
      inv_head hco i hr
      exact (inv_none hr (fun h => h) (by simp [instruction?])).elim

/-- **A linked step implies a source step**, for related, scoped configurations. -/
theorem back {P : Profile} {ct ct' : Config H} (step : Step P Simulation.noHost ct ct') :
    ∀ {mode : Mode} {s₀ : Store H} {f₀ : Frame} {X : List Admin},
      StoreRelation.Related s₀ ct.store → Frames mode f₀ ct.frame →
      Control mode f₀.module ct.frame.module X ct.code → XAs f₀.module X →
      ∃ c, Step P Simulation.noHost ⟨s₀, f₀, X⟩ c := by
  induction step with
  | @parametric s f is is' h =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    cases h with
    | unreachable =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .parametric .unreachable⟩
    | nop =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .parametric .nop⟩
    | drop v =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .parametric (.drop v)⟩
    | selectTrue hc =>
      inv_head hco i hr
      obtain ⟨ts₀, rfl⟩ := inv_select hr
      exact ⟨_, .parametric (.selectTrue (ts := ts₀) hc)⟩
    | selectFalse v₁ v₂ ts =>
      inv_head hco i hr
      obtain ⟨ts₀, rfl⟩ := inv_select hr
      exact ⟨_, .parametric (.selectFalse v₁ v₂ ts₀)⟩
  | @numeric s f is is' h =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨args, e, rfl, hev, hfam⟩ := NumericStep.shape h
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    obtain rfl := inv_fixed hr (fun r => fixed_numeric hfam r _)
    exact ⟨_, .numeric h⟩
  | @vector s f is is' h =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨args, e, rfl, hev, hfam⟩ := VectorStep.shape h
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    obtain rfl := inv_fixed hr (fun r => fixed_vector hfam r _)
    exact ⟨_, .vector h⟩
  | @«variable» c c' h =>
    obtain ⟨s, f, Y⟩ := c
    obtain ⟨s', f', Y'⟩ := c'
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    cases mode with
    | same =>
      obtain rfl := frames_same hfr
      obtain ⟨args, e, rfl, hev, hfam⟩ := VariableStep.shape h
      obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
      obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
      change i = j at hr
      subst hr
      rw [store_eta hst.toState]
      exact ⟨_, .variable (variable_funcs h _)⟩
    | relocated r =>
      have view := frames_view hfr
      cases h with
      | @localGet _ _ x v hloc =>
        obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
        obtain rfl := inv_fixed hr (fun _ h => h)
        have hloc' : f₀.local? x = some (some v) := by
          simpa only [Frame.local?, hfr.locals] using hloc
        exact ⟨_, .variable (.localGet hloc')⟩
      | localSet hx =>
        inv_head hco i hr
        obtain rfl := inv_fixed hr (fun _ h => h)
        refine ⟨_, .variable (.localSet ?_)⟩
        simpa only [hfr.locals] using hx
      | localTee =>
        inv_head hco i hr
        obtain rfl := inv_fixed hr (fun _ h => h)
        exact ⟨_, .variable .localTee⟩
      | globalGet hg =>
        obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
        obtain ⟨x, rfl, hx⟩ := inv_global (fun y => .globalGet y) view hr (fun _ h => h)
          (fun x h => by simp only [XI, XE] at h; exact h.2) (xi_of_mem hsc (by simp))
        exact ⟨_, .variable (.globalGet (global_back hg hx hst.globals))⟩
      | globalSet hg =>
        inv_head hco i hr
        obtain ⟨x₀, rfl, hx⟩ := inv_global (fun y => .globalSet y) view hr (fun _ h => h)
          (fun x h => by simp only [XI, XE] at h; exact h.2) (xi_of_mem hsc (by simp))
        exact ⟨_, .variable (.globalSet (global_back hg hx hst.globals))⟩
  | @table c c' h =>
    obtain ⟨s, f, Y⟩ := c
    obtain ⟨s', f', Y'⟩ := c'
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨args, e, rfl, hev, hfam⟩ := TableStep.shape h
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    cases mode with
    | same =>
      obtain rfl := frames_same hfr
      change i = j at hr
      subst hr
      rw [store_eta hst.toState]
      exact ⟨_, .table (table_funcs h _)⟩
    | relocated r => exact (inv_none hr (fixed_table hfam r i) (none_table hfam r)).elim
  | @memory c c' h =>
    obtain ⟨s, f, Y⟩ := c
    obtain ⟨s', f', Y'⟩ := c'
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨args, e, rfl, hev, hfam⟩ := MemoryStep.shape h
    obtain ⟨j, rfl⟩ := plain_of_fam hfam (by decide)
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right hev (ne_throwRef_of_fam hfam (by decide))
    cases mode with
    | same =>
      obtain rfl := frames_same hfr
      change i = j at hr
      subst hr
      rw [store_eta hst.toState]
      exact ⟨_, .memory (memory_funcs h _)⟩
    | relocated r => exact (inv_none hr (fixed_memory hfam r i) (none_memory hfam r)).elim
  | @reference c c' h =>
    obtain ⟨s, f, Y⟩ := c
    obtain ⟨s', f', Y'⟩ := c'
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    have view := frames_view hfr
    cases h with
    | refNull ht =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain ⟨h₀, rfl⟩ := inv_refNull hr
      exact ⟨_, .reference (.refNull h₀)⟩
    | refFunc ha =>
      obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
      obtain ⟨x, rfl, hx⟩ := inv_refFunc view hr (xi_of_mem hsc (by simp)) ha
      exact ⟨_, .reference (.refFunc hx)⟩
    | refI31 n =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.refI31 n)⟩
    | isNullTrue =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference .isNullTrue⟩
    | isNullFalse hn =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.isNullFalse hn)⟩
    | asNonNullNull =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference .asNonNullNull⟩
    | asNonNullAddr hn =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.asNonNullAddr hn)⟩
    | eqNull =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference .eqNull⟩
    | eqTrue hn =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.eqTrue hn)⟩
    | eqFalse hn =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.eqFalse hn)⟩
    | @testTrue _ _ r rt _ =>
      inv_head hco i hr
      obtain ⟨rt₀, rfl⟩ := inv_refTest hr
      by_cases hok : RefOk s₀ r (f₀.module.instRef rt₀)
      · exact ⟨_, .reference (.testTrue hok)⟩
      · exact ⟨_, .reference (.testFalse hok)⟩
    | @testFalse _ _ r rt _ =>
      inv_head hco i hr
      obtain ⟨rt₀, rfl⟩ := inv_refTest hr
      by_cases hok : RefOk s₀ r (f₀.module.instRef rt₀)
      · exact ⟨_, .reference (.testTrue hok)⟩
      · exact ⟨_, .reference (.testFalse hok)⟩
    | @castSucceed _ _ r rt _ =>
      inv_head hco i hr
      obtain ⟨rt₀, rfl⟩ := inv_refCast hr
      by_cases hok : RefOk s₀ r (f₀.module.instRef rt₀)
      · exact ⟨_, .reference (.castSucceed hok)⟩
      · exact ⟨_, .reference (.castFail hok)⟩
    | @castFail _ _ r rt _ =>
      inv_head hco i hr
      obtain ⟨rt₀, rfl⟩ := inv_refCast hr
      by_cases hok : RefOk s₀ r (f₀.module.instRef rt₀)
      · exact ⟨_, .reference (.castSucceed hok)⟩
      · exact ⟨_, .reference (.castFail hok)⟩
    | i31GetNull sx =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.i31GetNull sx)⟩
    | i31GetNum sx n =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.i31GetNum sx n)⟩
    | externConvertNull =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference .externConvertNull⟩
    | externConvertAddr hn =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.externConvertAddr hn)⟩
    | anyConvertNull =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference .anyConvertNull⟩
    | anyConvertAddr r =>
      inv_head hco i hr
      obtain rfl := inv_fixed hr (fun _ h => h)
      exact ⟨_, .reference (.anyConvertAddr r)⟩
  | @aggregate c c' h =>
    intro mode s₀ f₀ X hst hfr hco hsc
    obtain ⟨result, actual⟩ := aggregate_back_progress h hst hfr hco hsc
    exact ⟨result, .aggregate actual⟩
  | @ctxtInstrs s s' f f' vs is is' rest h hne ih =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    rw [List.append_assoc] at hco
    obtain ⟨R, rfl, hR⟩ := hco.vals_right
    obtain ⟨A, B, rfl, hA, hB⟩ := hR.append_right
    simp only [xas_append_iff] at hsc
    obtain ⟨⟨s₁, f₁, A'⟩, hA'⟩ := ih hst hfr hA hsc.2.1
    have hne' : vs ≠ [] ∨ B ≠ [] := by
      rcases hne with h | h
      · exact .inl h
      · right
        intro hb
        subst hb
        exact h hB.nil_left
    have hstep := Step.ctxtInstrs (P := P) (host := Simulation.noHost) (vs := vs) (rest := B) hA' hne'
    simp only [List.append_assoc] at hstep
    exact ⟨_, hstep⟩
  | @ctxtLabel s s' f f' n cont is is' h ih =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest, rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    simp only [xas_cons_iff, xa_label, xas_nil, and_true] at hsc
    obtain ⟨⟨s₁, f₁, b'⟩, hb'⟩ := ih hst hfr hb hsc.2
    exact ⟨_, .ctxtLabel hb'⟩
  | @ctxtHandler s s' f f' n cs is is' h ih =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest, rfl, rfl, hm, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    simp only [xas_cons_iff, xa_handler, xas_nil, and_true] at hsc
    obtain ⟨⟨s₁, f₁, b'⟩, hb'⟩ := ih hst hfr hb hsc
    exact ⟨_, .ctxtHandler hb'⟩
  | @ctxtFrame s s' f fi fi' n is is' h ih =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest, rfl, hfi, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    simp only [xas_cons_iff, xa_frame, xas_nil, and_true] at hsc
    obtain ⟨⟨s₁, f₁, b'⟩, hb'⟩ := ih hst hfi hb hsc
    exact ⟨_, .ctxtFrame hb'⟩
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
    obtain ⟨bt₀, body₀, rfl, hb⟩ := inv_block (frames_view hfr) hr (xi_of_mem hsc (by simp)) hbt
    exact ⟨_, .block hb hm⟩
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
    obtain ⟨bt₀, body₀, rfl, hb⟩ := inv_loop (frames_view hfr) hr (xi_of_mem hsc (by simp)) hbt
    exact ⟨_, .loop hb hm⟩
  | @ifTrue s f c bt b₁ b₂ hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨bt₀, y₀, n₀, rfl⟩ := inv_if hr
    exact ⟨_, .ifTrue hc⟩
  | @ifFalse s f bt b₁ b₂ =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨bt₀, y₀, n₀, rfl⟩ := inv_if hr
    exact ⟨_, .ifFalse⟩
  | @labelVals s f n cont vs =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest, rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    obtain rfl := hb.vals_right_exact
    exact ⟨_, .labelVals⟩
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    rw [← vals_append] at hb
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.label n cont₀ (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest₀)]⟩ _ :=
      .brLabelZero hl hn
    rw [← vals_append] at hstep
    exact ⟨_, hstep⟩
  | @brLabelSucc s f n cont vs l rest hl =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    exact ⟨_, .brLabelSucc hl⟩
  | @brHandler s f n cs vs l rest =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    exact ⟨_, .brHandler⟩
  | @brIfTrue s f c l hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brIfTrue hc⟩
  | @brIfFalse s f l =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brIfFalse⟩
  | @brTableLt s f c ls l' l hi =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brTableLt hi⟩
  | @brTableGe s f c ls l' hi =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brTableGe hi⟩
  | @brOnNullNull s f l =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brOnNullNull⟩
  | @brOnNullAddr s f v l hv =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brOnNullAddr hv⟩
  | @brOnNonNullNull s f l =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brOnNonNullNull⟩
  | @brOnNonNullAddr s f v l hv =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .brOnNonNullAddr hv⟩
  | @brOnCastSucceed s f r l rt₁ rt₂ _ =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCast hr
    by_cases hok : RefOk s₀ r (f₀.module.instRef b₀)
    · exact ⟨_, .brOnCastSucceed hok⟩
    · exact ⟨_, .brOnCastFail hok⟩
  | @brOnCastFail s f r l rt₁ rt₂ _ =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCast hr
    by_cases hok : RefOk s₀ r (f₀.module.instRef b₀)
    · exact ⟨_, .brOnCastSucceed hok⟩
    · exact ⟨_, .brOnCastFail hok⟩
  | @brOnCastFailSucceed s f r l rt₁ rt₂ _ =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCastFail hr
    by_cases hok : RefOk s₀ r (f₀.module.instRef b₀)
    · exact ⟨_, .brOnCastFailSucceed hok⟩
    · exact ⟨_, .brOnCastFailFail hok⟩
  | @brOnCastFailFail s f r l rt₁ rt₂ _ =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    inv_head hco i hr
    obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCastFail hr
    by_cases hok : RefOk s₀ r (f₀.module.instRef b₀)
    · exact ⟨_, .brOnCastFailSucceed hok⟩
    · exact ⟨_, .brOnCastFailFail hok⟩
  | @call s f y a fi hx hf =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain ⟨x, rfl, hx₀⟩ := inv_call (frames_view hfr) hr (xi_of_mem hsc (by simp)) hx
    obtain ⟨fi₀, hf₀, -⟩ := hst.function_lookup_reverse hf
    exact ⟨_, .call hx₀ hf₀⟩
  | @callRefNull s f c hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨rest, rfl, hr⟩ := hco.ref_right
    obtain ⟨c₀, rest', rfl, hc₀, hn⟩ := hr.callRef_right hc
    obtain rfl := hn.nil_right
    exact ⟨_, .callRefNull hc₀⟩
  | @callRefFunc s f c vs a fi ps rs code hc hf he hn hcode =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨R, rfl, hR⟩ := hco.vals_right
    obtain ⟨rest, rfl, hr⟩ := hR.ref_right
    obtain ⟨c₀, rest', rfl, hc₀, hn'⟩ := hr.callRef_right hc
    obtain rfl := hn'.nil_right
    obtain ⟨fi₀, hf₀, hF⟩ := hst.function_lookup_reverse hf
    obtain ⟨code₀, hcode₀⟩ := Function.wasm_back hF hcode
    exact ⟨_, .callRefFunc hc₀ hf₀ (hF.type_eq ▸ he) hn hcode₀⟩
  | @callRefHost s s' f c vs a fi ps rs hh r hc hf he hn hcode hhost => exact hhost.elim
  | @callRefHostDiv s f c vs a fi ps rs hh hc hf he hn hcode hhost => exact hhost.elim
  | @returnCall s f y a fi hx hf =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain ⟨x, rfl, hx₀⟩ := inv_returnCall (frames_view hfr) hr (xi_of_mem hsc (by simp)) hx
    obtain ⟨fi₀, hf₀, -⟩ := hst.function_lookup_reverse hf
    exact ⟨_, .returnCall hx₀ hf₀⟩
  | @returnCallRefLabel s f k cont vs c rest hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    rw [List.append_assoc] at hb
    obtain ⟨R, rfl, hR⟩ := hb.vals_right
    obtain ⟨c₀, rest₀, rfl, hc₀, -⟩ := hR.returnCallRef_right hc
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.label k cont₀ (vals vs ++ [c₀] ++ rest₀)]⟩ _ := .returnCallRefLabel hc₀
    simp only [List.append_assoc, List.singleton_append] at hstep
    exact ⟨_, hstep⟩
  | @returnCallRefHandler s f k cs vs c rest hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    rw [List.append_assoc] at hb
    obtain ⟨R, rfl, hR⟩ := hb.vals_right
    obtain ⟨c₀, rest₀, rfl, hc₀, -⟩ := hR.returnCallRef_right hc
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.handler k cs (vals vs ++ [c₀] ++ rest₀)]⟩ _ := .returnCallRefHandler hc₀
    simp only [List.append_assoc, List.singleton_append] at hstep
    exact ⟨_, hstep⟩
  | @returnCallRefFrameNull s f fi k vs c rest hc =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest', rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    rw [List.append_assoc] at hb
    obtain ⟨R, rfl, hR⟩ := hb.vals_right
    obtain ⟨R', rfl, hR'⟩ := hR.ref_right
    obtain ⟨c₀, rest₀, rfl, hc₀, -⟩ := hR'.returnCallRef_right hc
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.frame k fi₀ (vals vs ++ [.ref .null, c₀] ++ rest₀)]⟩ _ :=
      .returnCallRefFrameNull hc₀
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hstep
    exact ⟨_, hstep⟩
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hc hf he hn =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest', rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    rw [← vals_append, List.append_assoc] at hb
    obtain ⟨R, rfl, hR⟩ := hb.vals_right
    obtain ⟨R', rfl, hR'⟩ := hR.ref_right
    obtain ⟨c₀, rest₀, rfl, hc₀, -⟩ := hR'.returnCallRef_right hc
    obtain ⟨fn₀, hf₀, hF⟩ := hst.function_lookup_reverse hf
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.frame k fi₀ (vals vs' ++ vals vs ++ [.ref (.func a), c₀] ++ rest₀)]⟩ _ :=
      .returnCallRefFrameAddr hc₀ hf₀ (hF.type_eq ▸ he) hn
    rw [← vals_append] at hstep
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hstep
    exact ⟨_, hstep⟩
  | @callIndirect s f x y =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .callIndirect⟩
  | @returnCallIndirect s f x y =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := Control.vals_plain_right (vs := []) hco rfl
    obtain rfl := inv_fixed hr (fun _ h => h)
    exact ⟨_, .returnCallIndirect⟩
  | @frameVals s f fi n vs hn =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest, rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    obtain rfl := hb.vals_right_exact
    exact ⟨_, .frameVals hn⟩
  | @returnFrame s f fi n vs' vs rest hn =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest', rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    rw [← vals_append] at hb
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    have hstep : Step P Simulation.noHost
        ⟨s₀, f₀, [.frame n fi₀ (vals vs' ++ vals vs ++ [.plain .return_] ++ rest₀)]⟩ _ :=
      .returnFrame hn
    rw [← vals_append] at hstep
    exact ⟨_, hstep⟩
  | @returnLabel s f n cont vs rest =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    exact ⟨_, .returnLabel⟩
  | @returnHandler s f n cs vs rest =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨i, rest₀, rfl, hi, -⟩ := hb.vals_plain_rest_right rfl
    obtain rfl := inv_fixed hi (fun _ h => h)
    exact ⟨_, .returnHandler⟩
  | @throw s f x vs ta ti ts ht he hn =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
    cases mode with
    | same =>
      obtain rfl := frames_same hfr
      change i = _ at hr
      subst hr
      refine ⟨_, .throw (ta := ta) (ti := ti) ?_ he hn⟩
      simpa only [Store.tag?, hst.tags] using ht
    | relocated r => exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
  | @throwRefNull s f =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨rest, rfl, hr⟩ := hco.ref_right
    obtain ⟨rest', rfl, hn⟩ := hr.throwRef_right
    obtain rfl := hn.nil_right
    exact ⟨_, .throwRefNull⟩
  | @throwRefInstrs s f vs a rest hne =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    rw [List.append_assoc] at hco
    obtain ⟨R, rfl, hR⟩ := hco.vals_right
    obtain ⟨R', rfl, hR'⟩ := hR.ref_right
    obtain ⟨rest₀, rfl, hrest⟩ := hR'.throwRef_right
    have hne' : vs ≠ [] ∨ rest₀ ≠ [] := by
      rcases hne with h | h
      · exact .inl h
      · right
        intro hb
        subst hb
        exact h hrest.nil_left
    have hstep : Step P Simulation.noHost ⟨s₀, f₀, vals vs ++ throwing a ++ rest₀⟩ _ :=
      .throwRefInstrs hne'
    simp only [throwing, List.append_assoc, List.cons_append, List.nil_append] at hstep
    exact ⟨_, hstep⟩
  | @throwRefLabel s f n cont a =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefLabel⟩
  | @throwRefFrame s f fi n a =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest', rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefFrame⟩
  | @throwRefHandlerEmpty s f n a =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerEmpty⟩
  | @throwRefHandlerCatch s f n x l cs a e he ht =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, rfl, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain rfl := frames_same hfr
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatch (by rw [hst.exns]; exact he) ht⟩
  | @throwRefHandlerCatchRef s f n x l cs a e he ht =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, rfl, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain rfl := frames_same hfr
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatchRef (by rw [hst.exns]; exact he) ht⟩
  | @throwRefHandlerCatchAll s f n l cs a =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatchAll⟩
  | @throwRefHandlerCatchAllRef s f n l cs a =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerCatchAllRef⟩
  | @throwRefHandlerNext s f n c cs a h =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, rfl, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain rfl := frames_same hfr
    obtain ⟨R, rfl, hR⟩ := hb.ref_right
    obtain ⟨R', rfl, hR'⟩ := hR.throwRef_right
    obtain rfl := hR'.nil_right
    exact ⟨_, .throwRefHandlerNext (by rwa [catchMatches_iff hst.exns])⟩
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨i, rfl, hr⟩ := hco.vals_plain_right rfl
    cases mode with
    | same =>
      obtain rfl := frames_same hfr
      change i = _ at hr
      subst hr
      exact ⟨_, .tryTable hbt hm⟩
    | relocated r => exact (inv_none hr (fun h => h) (by simp [instruction?])).elim
  | @handlerVals s f n cs vs =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain rfl := hb.vals_right_exact
    exact ⟨_, .handlerVals⟩
  | @trapInstrs s f vs rest hne =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    rw [List.append_assoc] at hco
    obtain ⟨R, rfl, hR⟩ := hco.vals_right
    obtain ⟨rest₀, rfl, hrest⟩ := hR.trap_right
    have hne' : vs ≠ [] ∨ rest₀ ≠ [] := by
      rcases hne with h | h
      · exact .inl h
      · right
        intro hb
        subst hb
        exact h hrest.nil_left
    have hstep : Step P Simulation.noHost ⟨s₀, f₀, vals vs ++ [.trap] ++ rest₀⟩ _ :=
      .trapInstrs hne'
    simp only [List.append_assoc, List.singleton_append] at hstep
    exact ⟨_, hstep⟩
  | @trapLabel s f n cont =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨cont₀, body₀, rest', rfl, -, hb, hr⟩ := hco.label_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.trap_right
    obtain rfl := hR.nil_right
    exact ⟨_, .trapLabel⟩
  | @trapHandler s f n cs =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨body₀, rest', rfl, -, -, hb, hr⟩ := hco.handler_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.trap_right
    obtain rfl := hR.nil_right
    exact ⟨_, .trapHandler⟩
  | @trapFrame s f fi n =>
    intro mode s₀ f₀ X hst hfr hco hsc
    dsimp only at hst hfr hco
    obtain ⟨innerMode, fi₀, body₀, rest', rfl, -, hb, hr⟩ := hco.frame_right
    obtain rfl := hr.nil_right
    obtain ⟨R, rfl, hR⟩ := hb.trap_right
    obtain rfl := hR.nil_right
    exact ⟨_, .trapFrame⟩

end Silmaril.Wasm.Binaryen.MergeUntyped
