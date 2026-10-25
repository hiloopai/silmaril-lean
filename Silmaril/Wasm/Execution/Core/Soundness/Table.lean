module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

@[expose] public section

/-! # Soundness, table family

Preservation of `TableStep` (the frame is unchanged; the store is extended and
stays valid) and progress for `TableInstrOk`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Inversion of table-instruction typing -/

/-- The table-family instructions. -/
def _root_.Silmaril.Wasm.Instr.IsTableI : Instr → Prop
  | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _ | .tableCopy _ _
  | .tableInit _ _ | .elemDrop _ => True
  | _ => False

/-- The number of operands of a table-family instruction. -/
def _root_.Silmaril.Wasm.Instr.tableArity : Instr → Nat
  | .tableGet _ => 1 | .tableSet _ => 2 | .tableGrow _ => 2 | .tableFill _ => 3
  | .tableCopy _ _ => 3 | .tableInit _ _ => 3 | _ => 0

theorem _root_.Silmaril.Wasm.Validation.InstrOk.table_inv {C : Context} {i : Instr}
    {it : InstrType} (h : InstrOk C i it) (hi : i.IsTableI) : TableInstrOk C i it := by
  cases h <;> first
    | assumption
    | (rename_i h'; cases h' <;> simp [Instr.IsTableI] at hi)
    | simp [Instr.IsTableI] at hi

theorem StateOk.table_ctx {s : Store H} {f : Frame} {C : Context} {x : TableIdx}
    {a : AddrType} {l : Limits} {rt : CRefType} {ta : Nat} {ti : TableInst}
    (hst : StateOk s f C) (hx : C.tables[x.toNat]? = some ⟨a, l, rt⟩)
    (ht : s.table? f x = some (ta, ti)) :
    ti.type.address = a ∧ (∀ r, RefOk s r ti.type.element ↔ RefOk s r rt) ∧ TyOk {} rt ∧
      TyOk C.toTypeCtx rt ∧ TableInstOk s ti ∧ s.tables[ta]? = some ti := by
  obtain ⟨ta', ti', ht', h₁, h₂, h₃, h₄⟩ := hst.table hx
  rw [ht] at ht'
  cases ht'
  exact ⟨h₁, h₂, h₃, TyOk.of_empty _ h₃, h₄, (Store.table?_spec ht).2⟩

theorem Store.elem?_spec {s : Store H} {f : Frame} {y : ElemIdx} {a : Nat} {ei : ElemInst}
    (h : s.elem? f y = some (a, ei)) : s.elems[a]? = some ei := by
  simp only [Store.elem?] at h
  cases h₁ : f.module.elems[y.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.elems[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact h₂

theorem StateOk.elem_ctx {s : Store H} {f : Frame} {C : Context} {y : ElemIdx}
    {rt : CRefType} {ea : Nat} {ei : ElemInst}
    (hst : StateOk s f C) (hy : C.elems[y.toNat]? = some rt)
    (he : s.elem? f y = some (ea, ei)) :
    ei.type = rt ∧ ElemInstOk s ei ∧ TyOk {} rt ∧ TyOk C.toTypeCtx rt := by
  obtain ⟨ea', ei', he', h₁, h₂⟩ := hst.elem hy
  rw [he] at he'
  cases he'
  exact ⟨h₁, h₂, h₁ ▸ h₂.1, TyOk.of_empty _ (h₁ ▸ h₂.1)⟩

theorem _root_.Silmaril.Wasm.Validation.TableInstrOk.hi {s : Store H} {f : Frame} {C : Context} {i : Instr} {it : InstrType}
    (hst : StateOk s f C) (h : TableInstrOk C i it) :
    it.inits = [] ∧ it.params.length = i.tableArity ∧ ResultOk {} it.params := by
  cases h with
  | tableSet h =>
    have := (hst.table h).choose_spec.choose_spec.2.2.2.1
    exact ⟨rfl, rfl, by rok⟩
  | tableGrow h =>
    have := (hst.table h).choose_spec.choose_spec.2.2.2.1
    exact ⟨rfl, rfl, by rok⟩
  | tableFill h =>
    have := (hst.table h).choose_spec.choose_spec.2.2.2.1
    exact ⟨rfl, rfl, by rok⟩
  | _ => exact ⟨rfl, rfl, by rok⟩

theorem tableHi {s : Store H} {f : Frame} {C : Context} {i : Instr} (hst : StateOk s f C)
    (hti : i.IsTableI) {vs : List Val} (hlen : vs.length = i.tableArity) :
    ∀ it₀, InstrOk C i it₀ →
      it₀.inits = [] ∧ it₀.params.length = vs.length ∧ ResultOk {} it₀.params := by
  intro it₀ h
  obtain ⟨h₁, h₂, h₃⟩ := (h.table_inv hti).hi hst
  exact ⟨h₁, h₂.trans hlen.symm, h₃⟩

/-- **Preservation (table).** -/
theorem TableStep.preservation {P : Profile} {c c' : Config H} {C : Context} {it : InstrType}
    (hst : StateOk c.store c.frame C) (hty : AdminsOk c.store C c.code it)
    (h : TableStep P c c') :
    c'.frame = c.frame ∧ StoreOk c'.store ∧ Extend c.store c'.store ∧
      AdminsOk c'.store C c'.code it := by
  have hs := hst.1
  cases h with
  | @getOob s f x a i ta ti ht hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableGet hx =>
      obtain ⟨-, -, -, hrt, -⟩ := hst.table_ctx hx ht
      exact SeqOk.trap (by rok)
  | @getVal s f x a i ta ti r ht hr =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableGet hx =>
      obtain ⟨-, hiff, -, hrt, htok, -⟩ := hst.table_ctx hx ht
      have hrok : RefOk s r _ := (hiff r).1 (htok.2.2 r (List.mem_of_getElem? hr))
      exact SeqOk.ref SeqOk.nil resultOk_nil hrok hrt
  | @setOob s f x a i r ta ti ht hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, .ref r]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableSet hx => exact SeqOk.trap resultOk_nil
  | @setVal s f x a i r ta ti ht hlt =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv (vs := [.num ⟨.int a.intType, i⟩, .ref r])
      hst (tableHi hst (by trivial) (by rfl)) hty
    cases hi.table_inv trivial with
    | tableSet hx =>
      obtain ⟨-, hiff, -, hrt, htok, hget⟩ := hst.table_ctx hx ht
      rcases hvs with _ | ⟨-, _ | ⟨hv, -⟩⟩
      have hr : RefOk s r ti.type.element := (hiff r).2 (ValOk.ref_eq hv)
      have htok' : TableInstOk s { ti with refs := ti.refs.set i.toNat r } := by
        refine ⟨htok.1, by simpa using htok.2.1, fun r' hr' => ?_⟩
        rcases List.mem_or_eq_of_mem_set hr' with hr' | rfl
        · exact htok.2.2 r' hr'
        · exact hr
      obtain ⟨hs', he⟩ := StoreOk.setTable (ti' := { ti with refs := ti.refs.set i.toNat r }) hs hget
        ⟨rfl, rfl, rfl, Nat.le_refl _, by simp⟩ htok'
      exact ⟨rfl, hs', he, hk _ _ SeqOk.nil⟩
  | @size s f x ta ti ht =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := []) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableSize hx =>
      obtain ⟨haddr, -⟩ := hst.table_ctx hx ht
      subst haddr
      exact SeqOk.addr SeqOk.nil _ _
  | @growSucceed s f x a n r ta ti ti' ht hg hp =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv (vs := [.ref r, .num ⟨.int a.intType, n⟩])
      hst (tableHi hst (by trivial) (by rfl)) hty
    cases hi.table_inv trivial with
    | tableGrow hx =>
      obtain ⟨-, hiff, -, hrt, htok, hget⟩ := hst.table_ctx hx ht
      rcases hvs with _ | ⟨hv, _ | ⟨hn, -⟩⟩
      obtain rfl := ValOk.addr_eq hn
      have hr : RefOk s r ti.type.element := (hiff r).2 (ValOk.ref_eq hv)
      obtain ⟨htok', hx'⟩ := TableInst.grow?_ok htok hr hg
      obtain ⟨hs', he⟩ := StoreOk.setTable hs hget hx' htok'
      exact ⟨rfl, hs', he, hk _ _ (SeqOk.addr SeqOk.nil _ _)⟩
  | @growFail s f x a n r ta ti ht hp =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.ref r, .num ⟨.int a.intType, n⟩]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableGrow hx =>
      rcases hvs with _ | ⟨-, _ | ⟨hn, -⟩⟩
      obtain rfl := ValOk.addr_eq hn
      exact SeqOk.addr SeqOk.nil _ _
  | @fillOob s f x a i n v ta ti ht hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, n⟩])
      hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableFill hx => exact SeqOk.trap resultOk_nil
  | @fillZero s f x a i v ta ti ht hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, 0⟩])
      hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableFill hx => exact SeqOk.nil
  | @fillSucc s f x a i n v ta ti ht hle hn =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, v, .num ⟨.int a.intType, n⟩])
      hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableFill hx =>
      obtain ⟨-, -, -, hrt, -⟩ := hst.table_ctx hx ht
      rcases hvs with _ | ⟨ha, _ | ⟨hv, _ | ⟨-, -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a i
      have e2 := SeqOk.v e1 hv (.refv hrt)
      have e3 := SeqOk.ins [] [a.valType, .refv _] e2 (.table (.tableSet hx))
      have e4 := SeqOk.addr e3 a (i + 1)
      have e5 := SeqOk.v e4 hv (.refv hrt)
      have e6 := SeqOk.addr e5 a (n - 1)
      exact SeqOk.ins [] [a.valType, .refv _, a.valType] e6 (.table (.tableFill hx))
  | @copyOob s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableCopy hx₁ hx₂ hsub => exact SeqOk.trap resultOk_nil
  | @copyZero s f x₁ x₂ a₁ a₂ a' i₁ i₂ ta₁ ta₂ ti₁ ti₂ h₁ h₂ hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, 0⟩]) hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableCopy hx₁ hx₂ hsub => exact SeqOk.nil
  | @copyLe s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ hle' hn hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableCopy hx₁ hx₂ hsub =>
      obtain ⟨-, -, -, hrt₁, -⟩ := hst.table_ctx hx₁ h₁
      obtain ⟨-, -, -, hrt₂, -⟩ := hst.table_ctx hx₂ h₂
      rcases hvs with _ | ⟨ha₁, _ | ⟨ha₂, _ | ⟨ha', -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha₁
      obtain rfl := ValOk.addr_eq ha₂
      obtain rfl := ValOk.addr_eq ha'
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a₁ i₁
      have e2 := SeqOk.addr e1 a₂ i₂
      have e3 := SeqOk.ins [a₁.valType] [a₂.valType] e2 (.table (.tableGet hx₂))
      have e3' := SeqOk.sub (ts' := [a₁.valType, .refv _]) e3
        (.cons .num (.cons (.refv hsub) .nil)) (by rok)
      have e4 := SeqOk.ins [] [a₁.valType, .refv _] e3' (.table (.tableSet hx₁))
      have e5 := SeqOk.addr e4 a₁ (i₁ + 1)
      have e6 := SeqOk.addr e5 a₂ (i₂ + 1)
      have e7 := SeqOk.addr e6 _ (n - 1)
      exact SeqOk.ins [] [a₁.valType, a₂.valType, _] e7 (.table (.tableCopy hx₁ hx₂ hsub))
  | @copyGt s f x₁ x₂ a₁ a₂ a' i₁ i₂ n ta₁ ta₂ ti₁ ti₂ h₁ h₂ hle' hn hgt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a₁.intType, i₁⟩, .num ⟨.int a₂.intType, i₂⟩,
      .num ⟨.int a'.intType, n⟩]) hst (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableCopy hx₁ hx₂ hsub =>
      obtain ⟨-, -, -, hrt₁, -⟩ := hst.table_ctx hx₁ h₁
      obtain ⟨-, -, -, hrt₂, -⟩ := hst.table_ctx hx₂ h₂
      rcases hvs with _ | ⟨ha₁, _ | ⟨ha₂, _ | ⟨ha', -⟩⟩⟩
      obtain rfl := ValOk.addr_eq ha₁
      obtain rfl := ValOk.addr_eq ha₂
      obtain rfl := ValOk.addr_eq ha'
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a₁ (i₁ + BitVec.ofNat _ n.toNat - 1)
      have e2 := SeqOk.addr e1 a₂ (i₂ + BitVec.ofNat _ n.toNat - 1)
      have e3 := SeqOk.ins [a₁.valType] [a₂.valType] e2 (.table (.tableGet hx₂))
      have e3' := SeqOk.sub (ts' := [a₁.valType, .refv _]) e3
        (.cons .num (.cons (.refv hsub) .nil)) (by rok)
      have e4 := SeqOk.ins [] [a₁.valType, .refv _] e3' (.table (.tableSet hx₁))
      have e5 := SeqOk.addr e4 a₁ i₁
      have e6 := SeqOk.addr e5 a₂ i₂
      have e7 := SeqOk.addr e6 _ (n - 1)
      exact SeqOk.ins [] [a₁.valType, a₂.valType, _] e7 (.table (.tableCopy hx₁ hx₂ hsub))
  | @initOob s f x y a i j n ta ea ti ei ht he hlt =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 n]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableInit hx hy hsub => exact SeqOk.trap resultOk_nil
  | @initZero s f x y a i j ta ea ti ei ht he hle =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 0]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableInit hx hy hsub => exact SeqOk.nil
  | @initSucc s f x y a i j n ta ea ti ei r ht he hle hn hr =>
    refine ⟨rfl, hs, Extend.refl hs, ?_⟩
    refine AdminsOk.redex_replace (vs := [.num ⟨.int a.intType, i⟩, Val.i32 j, Val.i32 n]) hst
      (tableHi hst (by trivial) (by rfl)) hty fun P R hi hvs => ?_
    cases hi.table_inv trivial with
    | tableInit hx hy hsub =>
      obtain ⟨-, -, -, hrt₁, -⟩ := hst.table_ctx hx ht
      obtain ⟨hety, heok, -, hrt₂⟩ := hst.elem_ctx hy he
      rcases hvs with _ | ⟨ha, -⟩
      obtain rfl := ValOk.addr_eq ha
      have hr' : RefOk s r _ := hety ▸ heok.2 r (List.mem_of_getElem? hr)
      have e1 := SeqOk.addr (s := s) (C := C) SeqOk.nil a i
      have e2 := SeqOk.ref e1 (by rok) hr' hrt₂
      have e2' := SeqOk.sub (ts' := [a.valType, .refv _]) e2
        (.cons .num (.cons (.refv hsub) .nil)) (by rok)
      have e3 := SeqOk.ins [] [a.valType, .refv _] e2' (.table (.tableSet hx))
      have e4 := SeqOk.addr e3 a (i + 1)
      have e5 := SeqOk.i32 e4 (j + 1)
      have e6 := SeqOk.i32 e5 (n - 1)
      exact SeqOk.ins [] [a.valType, Ty.i32, Ty.i32] e6 (.table (.tableInit hx hy hsub))
  | @elemDrop s f y ea ei he =>
    obtain ⟨P, R, hi, hvs, hk⟩ := AdminsOk.redex_inv (vs := []) hst
      (tableHi hst (by trivial) (by rfl)) hty
    cases hi.table_inv trivial with
    | elemDrop hy =>
      obtain ⟨hs', he'⟩ := StoreOk.setElem_nil (a := ea) hs
      exact ⟨rfl, hs', he', hk _ _ SeqOk.nil⟩

/-- **Progress (table).** -/
theorem TableInstrOk.progress {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    {vs : List Val} (hst : StateOk s f C) (hi : TableInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : List.Forall₂ (ValOk s) vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | tableGet h =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hlt : b.toNat < ti.refs.length
    · exact ⟨_, .table (.getVal ht (List.getElem?_eq_getElem hlt))⟩
    · exact ⟨_, .table (.getOob ht (by omega))⟩
  | tableSet h =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨r, rfl, -⟩ := ValOk.ref_inv hv₂
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hlt : b.toNat < ti.refs.length
    · exact ⟨_, .table (.setVal ht hlt)⟩
    · exact ⟨_, .table (.setOob ht (by omega))⟩
  | tableSize h =>
    obtain ⟨⟩ := hvs
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    exact ⟨_, .table (.size ht)⟩
  | tableGrow h =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨r, rfl, -⟩ := ValOk.ref_inv hv₁
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₂
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hf : P.growMayFail .table ta ti.refs.length b.toNat
    · exact ⟨_, .table (.growFail ht (.inl hf))⟩
    · cases hg : ti.grow? b.toNat r with
      | none => exact ⟨_, .table (.growFail ht (.inr hg))⟩
      | some ti' =>
        exact ⟨_, .table (.growSucceed ht hg (Profile.growMaySucceed_of_not_fail hf))⟩
  | tableFill h =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨n, hn⟩ := ValOk.addr_inv hv₃
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hn]
    by_cases hoob : ti.refs.length < b.toNat + n.toNat
    · exact ⟨_, .table (.fillOob ht hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.fillZero ht (by simp at hoob; omega))⟩
      · exact ⟨_, .table (.fillSucc ht (by omega) hz)⟩
  | tableCopy h₁ h₂ hs =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b₁, hb₁⟩ := ValOk.addr_inv hv₁
    obtain ⟨b₂, hb₂⟩ := ValOk.addr_inv hv₂
    obtain ⟨n, hn⟩ := ValOk.addr_inv hv₃
    obtain ⟨ta₁, ti₁, ht₁, -⟩ := hst.table h₁
    obtain ⟨ta₂, ti₂, ht₂, -⟩ := hst.table h₂
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb₁, hb₂,
      hn]
    by_cases hoob : ti₁.refs.length < b₁.toNat + n.toNat ∨ ti₂.refs.length < b₂.toNat + n.toNat
    · exact ⟨_, .table (.copyOob ht₁ ht₂ hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.copyZero ht₁ ht₂ (by simp at hoob; omega))⟩
      · by_cases hle : b₁.toNat ≤ b₂.toNat
        · exact ⟨_, .table (.copyLe ht₁ ht₂ (by omega) hz hle)⟩
        · exact ⟨_, .table (.copyGt ht₁ ht₂ (by omega) hz (by omega))⟩
  | tableInit h he hs =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValOk.addr_inv hv₁
    obtain ⟨j, hj⟩ := ValOk.i32_inv hv₂
    obtain ⟨n, hn⟩ := ValOk.i32_inv hv₃
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    obtain ⟨ea, ei, hei, -⟩ := hst.elem he
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hj, hn]
    by_cases hoob : ti.refs.length < b.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat
    · exact ⟨_, .table (.initOob ht hei hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.initZero ht hei (by simp at hoob; omega))⟩
      · have hn0 := BitVec.toNat_ne_zero hz
        exact ⟨_, .table (.initSucc ht hei (by omega) hz
          (List.getElem?_eq_getElem (by omega)))⟩
  | elemDrop he =>
    obtain ⟨⟩ := hvs
    obtain ⟨ea, ei, hei, -⟩ := hst.elem he
    exact ⟨_, .table (.elemDrop hei)⟩

end Silmaril.Wasm.Execution.Core
