module

public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalStep
public import Silmaril.Wasm.Execution.Core.Soundness.InstantiationTypes

@[expose] public section

/-! # Typing helpers for constant evaluation

Value typing up to context subtyping, the principal inversion of a typed
instruction sequence with a valid frame prefix, the inversion of the typing of
each constant instruction, and heap-address bookkeeping (`Ref.In`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Heap addresses of values -/

/-- The structure, array and exception addresses of a reference exist in `s`. -/
def Ref.In (s : Store H) : Ref → Prop
  | .struct a => a < s.structs.length
  | .array a => a < s.arrays.length
  | .exn a => a < s.exns.length
  | .extern r => Ref.In s r
  | _ => True

def Val.In (s : Store H) : Val → Prop
  | .ref r => r.In s
  | _ => True

def FieldVal.In (s : Store H) : FieldVal → Prop
  | .val v => v.In s
  | .pack _ _ => True

theorem Ref.In.mono {s s' : Store H} (hs : s.structs.length ≤ s'.structs.length)
    (ha : s.arrays.length ≤ s'.arrays.length) (he : s.exns.length ≤ s'.exns.length) :
    ∀ {r : Ref}, r.In s → r.In s'
  | .struct _, h => by simp only [Ref.In] at *; omega
  | .array _, h => by simp only [Ref.In] at *; omega
  | .exn _, h => by simp only [Ref.In] at *; omega
  | .extern r, h => Ref.In.mono hs ha he (r := r) h
  | .i31 _, _ => trivial
  | .null, _ => trivial
  | .func _, _ => trivial
  | .host _, _ => trivial

theorem Val.In.mono {s s' : Store H} (hs : s.structs.length ≤ s'.structs.length)
    (ha : s.arrays.length ≤ s'.arrays.length) (he : s.exns.length ≤ s'.exns.length)
    {v : Val} (h : v.In s) : v.In s' := by
  cases v with
  | ref r => exact Ref.In.mono hs ha he (r := r) h
  | _ => trivial

theorem FieldVal.In.mono {s s' : Store H} (hs : s.structs.length ≤ s'.structs.length)
    (ha : s.arrays.length ≤ s'.arrays.length) (he : s.exns.length ≤ s'.exns.length)
    {v : FieldVal} (h : v.In s) : v.In s' := by
  cases v with
  | val v => exact Val.In.mono hs ha he (v := v) h
  | pack => trivial

theorem RefOk.in {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) : r.In s := by
  induction h with
  | struct h => exact (List.getElem?_eq_some_iff.mp h).1
  | array h => exact (List.getElem?_eq_some_iff.mp h).1
  | exn h => exact (List.getElem?_eq_some_iff.mp h).1
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

theorem ValOk.in {s : Store H} {v : Val} {t : CValType} (h : ValOk s v t) : v.In s := by
  cases h with
  | ref h => exact h.in
  | _ => trivial

theorem FieldValOk.in {s : Store H} {v : FieldVal} {t : CStorageType} (h : FieldValOk s v t) :
    v.In s := by
  cases h with
  | val h => exact h.in
  | pack => trivial

/-! ## Values and subtyping -/

theorem Sub.ref_nullable {Δ : TypeCtx} {h h' : CHeapType} {n : Bool}
    (hs : Sub Δ (Ty.ref true h : CRefType) (.ref n h')) : n = true := by
  cases hs; rfl

theorem Sub.ref_heap {Δ : TypeCtx} {h h' : CHeapType} {n n' : Bool}
    (hs : Sub Δ (Ty.ref n h : CRefType) (.ref n' h')) : Sub Δ h h' := by
  cases hs <;> assumption

theorem RefOk.null_nullable {s : Store H} {rt : CRefType} (h : RefOk s .null rt) :
    ∃ h', rt = .ref true h' := by
  obtain ⟨rt₀, e, hrt, -⟩ := h.principal
  simp only [Ref.type?, Option.some.injEq] at e
  subst e
  rcases hrt with rfl | ⟨-, hs⟩
  · exact ⟨_, rfl⟩
  · match rt, hs with
    | .ref n h', hs => exact ⟨h', by rw [Sub.ref_nullable hs]⟩

theorem Ref.type?_nonnull {s : Store H} {r : Ref} {rt₀ : CRefType} (e : Ref.type? s r = some rt₀)
    (hn : r ≠ .null) : ∃ h₀, rt₀ = .ref false h₀ := by
  cases r <;> simp_all [Ref.type?] <;> (try obtain ⟨_, _, rfl⟩ := e) <;>
    exact ⟨_, rfl⟩

/-- A non-null reference has the non-null version of any of its types. -/
theorem RefOk.nonnull {s : Store H} {r : Ref} {n : Bool} {h : CHeapType}
    (hr : RefOk s r (.ref n h)) (hn : r ≠ .null) : RefOk s r (.ref false h) := by
  obtain ⟨rt₀, e, hrt, hx⟩ := hr.principal
  obtain ⟨h₀, rfl⟩ := Ref.type?_nonnull e hn
  rcases hrt with e' | ⟨hok, hs⟩
  · cases e'; exact RefOk.of_type? e hx
  · have hok' : TyOk {} (Ty.ref false h : CRefType) := by
      cases hok with | ref hh => exact .ref hh
    exact .sub (RefOk.of_type? e hx) hok' (.refNonNull (Sub.ref_heap hs))

theorem ValOk.sub_empty_ce {s : Store H} {v : Val} {a b : CValType} (h : ValOk s v a)
    (hs : Sub {} a b) (hb : TyOk {} b) : ValOk s v b := by
  cases h with
  | num w => cases hs; exact .num w
  | vec w => cases hs; exact .vec w
  | ref hr =>
    cases hs with
    | refv hs' =>
      cases hb with
      | refv hb' => exact .ref (.sub hr hb' hs')

/-- Value typing along a context subtyping between types valid in `{}`. -/
theorem ValOk.sub_ctx_ce {s : Store H} {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {v : Val}
    {a b : CValType} (h : ValOk s v a) (ha : TyOk {} a) (hb : TyOk {} b) (hs : Sub Δ a b) :
    ValOk s v b :=
  h.sub_empty_ce (Sub.empty_of_closed hΔ hr ha hb hs) hb

theorem ValOk.not_botv' {s : Store H} {v : Val} (h : ValOk s v .botv) : False := by
  cases h

/-- A value below `i32` is an `i32`. -/
theorem ValOk.i32_of_sub {s : Store H} {Δ : TypeCtx} {v : Val} {a : CValType}
    (h : ValOk s v a) (hs : Sub Δ a Ty.i32) : ∃ b, v = Val.i32 b := by
  cases h with
  | num w =>
    rcases w with ⟨t, b⟩
    cases hs
    exact ⟨b, rfl⟩
  | vec => cases hs
  | ref => cases hs

theorem defaultVal?_ok {s : Store H} {t : CValType} {v : Val} (h : defaultVal? t = some v)
    (ht : TyOk {} t) : ValOk s v t := by
  unfold defaultVal? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact .num ⟨.int _, 0⟩
  · exact .num ⟨.float _, 0⟩
  · rename_i vt; cases vt; exact .vec 0
  · cases ht with
    | refv hr => exact .ref (.sub .null hr (.refNull .bot))

theorem packField_ok {s : Store H} {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) {z : CStorageType}
    {v : Val} {a : CValType} (h : ValOk s v a) (ha : TyOk {} a) (hz : TyOk {} z)
    (hs : Sub Δ a z.unpack) : FieldValOk s (packField z v) z := by
  cases z with
  | pack p =>
    obtain ⟨b, rfl⟩ := h.i32_of_sub hs
    exact .pack p _
  | val t =>
    have ht : TyOk {} t := by cases hz with | val h => exact h
    exact .val (h.sub_ctx_ce hΔ hr ha ht hs)

/-! ## Principal inversion with a valid frame prefix -/

theorem InstrsOk.single_inv_pre_aux {C : Context} {is : List Instr} {i : Instr} {it : InstrType}
    (hC : C.Wf) (h : InstrsOk C is it) (his : is = [i]) :
    ∃ ts it₀, InstrOk C i it₀ ∧ ResultOk C.toTypeCtx ts ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  induction h using InstrsOk.ind with
  | nil => cases his
  | @instr C i' it₀ h =>
      cases his
      exact ⟨[], it₀, h, (fun _ h => by cases h), by simpa using InstrTypeSub.refl C it₀⟩
  | @cons C i' is t₁ t₂ t₃ xs₁ xs₂ hi _ hs _ =>
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp his
      obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) hs
      simp only [Context.initLocals_toTypeCtx] at s
      exact ⟨[], ⟨t₁, xs₁, t₂⟩, hi, (fun _ h => by cases h),
        by simpa using InstrTypeSub.seq_nil s i₂⟩
  | @seq C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ =>
      rcases List.append_eq_singleton_iff.mp his with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨s₁, i₁⟩ := InstrsOk.nil_inv hC h₁
        have hC₁ : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
        obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih₂ (hC.initLocals _) rfl
        rw [hC₁] at hi hsub h₂ hts
        refine ⟨ts, it₀, hi, hts, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₂) hsub ?_⟩
        refine ⟨s₁, ResultSub.refl _ _, ?_⟩
        intro x hx hn
        rcases List.mem_append.mp hx with hx | hx
        · exact i₁ x hx
        · exact absurd hx hn
      · obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih₁ hC rfl
        obtain ⟨s, i₂⟩ := InstrsOk.nil_inv (hC.initLocals _) h₂
        simp only [Context.initLocals_toTypeCtx] at s
        exact ⟨ts, it₀, hi, hts, InstrTypeSub.trans hC.types (InstrsOk.regular hC h₁) hsub
          (InstrTypeSub.seq_nil s i₂)⟩
  | sub h hs hok ih =>
      obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih hC his
      exact ⟨ts, it₀, hi, hts, InstrTypeSub.trans hC.types (InstrsOk.regular hC h) hsub hs⟩
  | @frame C is ts' t₁ t₂ xs h hok ih =>
      obtain ⟨ts, it₀, hi, hts, hsub⟩ := ih hC his
      refine ⟨ts' ++ ts, it₀, hi, ResultOk.append hok hts, ?_⟩
      simpa using InstrTypeSub.frame hsub ts'

theorem Context.initLocals_of_locals_nil {C : Context} (hL : C.locals = []) {xs : List Nat}
    (hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    obtain ⟨lt, h⟩ := hx x (by simp)
    rw [hL] at h; cases h

/-- Inversion of `i :: is` in a context without locals: the instruction is typed
on top of a valid prefix of the stack, and the rest continues from there. -/
theorem InstrsOk.cons_inv' {C : Context} (hC : C.Wf) (hL : C.locals = []) {i : Instr}
    {is : List Instr} {ts rs : List CValType} {xs : List Nat}
    (h : InstrsOk C (i :: is) ⟨ts, xs, rs⟩) :
    ∃ pre p r, InstrOk C i ⟨p, [], r⟩ ∧ ResultOk C.toTypeCtx pre ∧
      ResultSub C.toTypeCtx ts (pre ++ p) ∧ InstrsOk C is ⟨pre ++ r, [], rs⟩ := by
  obtain ⟨tm, xs₁, xs₂, h₁, h₂⟩ := InstrsOk.append_inv (is₁ := [i]) hC h
  have hr₁ := InstrsOk.regular hC h₁
  have e₁ : xs₁ = [] := Context.initLocals_of_locals_nil hL hr₁.2.2
  subst e₁
  simp only [Context.initLocals_nil] at h₂
  have hr₂ := InstrsOk.regular hC h₂
  have e₂ : xs₂ = [] := Context.initLocals_of_locals_nil hL hr₂.2.2
  subst e₂
  obtain ⟨pre, ⟨p, xs₀, r⟩, hi, hpre, hsub⟩ := InstrsOk.single_inv_pre_aux hC h₁ rfl
  have hri := hi.regular hC
  have e₀ : xs₀ = [] := Context.initLocals_of_locals_nil hL hri.2.2
  subst e₀
  refine ⟨pre, p, r, hi, hpre, hsub.1, ?_⟩
  refine InstrsOk.sub h₂ ⟨hsub.2.1, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
    ⟨ResultOk.append hpre hri.2.1, hr₂.2.1, by simp⟩

/-! ## Acyclicity of the heap under allocation -/

/-- The acyclicity conditions of `Store_ok`. -/
def HeapAcyclic (s : Store H) : Prop :=
  (∀ a < s.structs.length,
    ¬ ImmutReachable s (.val (.ref (.struct a))) (.val (.ref (.struct a)))) ∧
  (∀ a < s.arrays.length,
    ¬ ImmutReachable s (.val (.ref (.array a))) (.val (.ref (.array a)))) ∧
  (∀ a < s.exns.length,
    ¬ ImmutReachable s (.val (.ref (.exn a))) (.val (.ref (.exn a))))

/-- Every heap object only refers to existing heap objects. -/
def HeapIn (s : Store H) : Prop :=
  (∀ si ∈ s.structs, ∀ fv ∈ si.fields, fv.In s) ∧
  (∀ ai ∈ s.arrays, ∀ fv ∈ ai.fields, fv.In s) ∧
  (∀ e ∈ s.exns, ∀ v ∈ e.fields, v.In s)

/-- Reachability in an extended heap from an old value stays in the old heap. -/
theorem ImmutReachable.old {s s' : Store H} (hin : HeapIn s)
    (hs : ∀ a si, a < s.structs.length → s'.structs[a]? = some si → s.structs[a]? = some si)
    (ha : ∀ a ai, a < s.arrays.length → s'.arrays[a]? = some ai → s.arrays[a]? = some ai)
    (he : s'.exns = s.exns) {x y : FieldVal} (h : ImmutReachable s' x y) (hx : x.In s) :
    ImmutReachable s x y ∧ y.In s := by
  induction h with
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨h₁, hb⟩ := ih₁ hx
    obtain ⟨h₂, hc⟩ := ih₂ hb
    exact ⟨.trans h₁ h₂, hc⟩
  | refStruct hsi hexp hi hfv =>
    have hsi' := hs _ _ hx hsi
    exact ⟨.refStruct hsi' hexp hi hfv,
      hin.1 _ (List.mem_of_getElem? hsi') _ (List.mem_of_getElem? hfv)⟩
  | refArray hai hexp hfv =>
    have hai' := ha _ _ hx hai
    exact ⟨.refArray hai' hexp hfv,
      hin.2.1 _ (List.mem_of_getElem? hai') _ (List.mem_of_getElem? hfv)⟩
  | refExn hex hv =>
    rw [he] at hex
    exact ⟨.refExn hex hv, hin.2.2 _ (List.mem_of_getElem? hex) _ (List.mem_of_getElem? hv)⟩
  | refExtern r => exact ⟨.refExtern r, hx⟩

theorem HeapAcyclic.addStruct {s : Store H} (hac : HeapAcyclic s) (hin : HeapIn s)
    {si : StructInst} (hsi : ∀ fv ∈ si.fields, fv.In s) : HeapAcyclic (s.addStruct si) := by
  have hs : ∀ a si', a < s.structs.length → (s.addStruct si).structs[a]? = some si' →
      s.structs[a]? = some si' := by
    intro a si' ha h
    simpa [Store.addStruct, List.getElem?_append_left ha] using h
  have hold := fun {x y : FieldVal} (h : ImmutReachable (s.addStruct si) x y) (hx : x.In s) =>
    ImmutReachable.old hin hs (fun _ _ _ h => h) rfl h hx
  -- from the new structure, reachability only reaches old values
  have hnew : ∀ {x y : FieldVal}, ImmutReachable (s.addStruct si) x y →
      x = .val (.ref (.struct s.structs.length)) → y.In s := by
    intro x y h
    induction h with
    | trans h₁ h₂ ih₁ _ => intro e; exact (hold h₂ (ih₁ e)).2
    | refStruct hsi' _ _ hfv =>
      intro e
      cases e
      simp [Store.addStruct] at hsi'
      subst hsi'
      exact hsi _ (List.mem_of_getElem? hfv)
    | refArray => intro e; cases e
    | refExn => intro e; cases e
    | refExtern => intro e; cases e
  refine ⟨fun a ha hr => ?_, fun a ha hr => ?_, fun a ha hr => ?_⟩
  · simp only [Store.addStruct, List.length_append, List.length_singleton] at ha
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
    · exact hac.1 a ha (hold hr (by simpa [Store.addStruct, FieldVal.In, Val.In, Ref.In] using ha)).1
    · have := hnew hr rfl
      simp [FieldVal.In, Val.In, Ref.In] at this
  · exact hac.2.1 a ha (hold hr (by simpa [Store.addStruct, FieldVal.In, Val.In, Ref.In] using ha)).1
  · exact hac.2.2 a ha (hold hr (by simpa [Store.addStruct, FieldVal.In, Val.In, Ref.In] using ha)).1

theorem HeapAcyclic.addArray {s : Store H} (hac : HeapAcyclic s) (hin : HeapIn s)
    {ai : ArrayInst} (hai : ∀ fv ∈ ai.fields, fv.In s) : HeapAcyclic (s.addArray ai) := by
  have ha : ∀ a ai', a < s.arrays.length → (s.addArray ai).arrays[a]? = some ai' →
      s.arrays[a]? = some ai' := by
    intro a ai' ha h
    simpa [Store.addArray, List.getElem?_append_left ha] using h
  have hold := fun {x y : FieldVal} (h : ImmutReachable (s.addArray ai) x y) (hx : x.In s) =>
    ImmutReachable.old (s' := s.addArray ai) hin (fun _ _ _ h => by simpa [Store.addArray] using h) ha rfl h hx
  have hnew : ∀ {x y : FieldVal}, ImmutReachable (s.addArray ai) x y →
      x = .val (.ref (.array s.arrays.length)) → y.In s := by
    intro x y h
    induction h with
    | trans h₁ h₂ ih₁ _ => intro e; exact (hold h₂ (ih₁ e)).2
    | refArray hai' _ hfv =>
      intro e
      cases e
      simp [Store.addArray] at hai'
      subst hai'
      exact hai _ (List.mem_of_getElem? hfv)
    | refStruct => intro e; cases e
    | refExn => intro e; cases e
    | refExtern => intro e; cases e
  refine ⟨fun a ha' hr => ?_, fun a ha' hr => ?_, fun a ha' hr => ?_⟩
  · exact hac.1 a ha' (hold hr (by simpa [Store.addArray, FieldVal.In, Val.In, Ref.In] using ha')).1
  · simp only [Store.addArray, List.length_append, List.length_singleton] at ha'
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha' with ha' | rfl
    · exact hac.2.1 a ha' (hold hr (by simpa [Store.addArray, FieldVal.In, Val.In, Ref.In] using ha')).1
    · have := hnew hr rfl
      simp [FieldVal.In, Val.In, Ref.In] at this
  · exact hac.2.2 a ha' (hold hr (by simpa [Store.addArray, FieldVal.In, Val.In, Ref.In] using ha')).1

/-! ## Typing of the constant instructions -/

section Inversion

variable {C : Context} {it : InstrType}

theorem _root_.Silmaril.Wasm.Validation.InstrOk.intConst_inv {t : IntType} {b : BitVec t.width} (h : InstrOk C (.intConst t b) it) :
    it = .plain [] [.num (.int t)] := by
  cases h with
  | numeric h => cases h; rfl
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.floatConst_inv {t : FloatType} {b : BitVec t.width}
    (h : InstrOk C (.floatConst t b) it) : it = .plain [] [.num (.float t)] := by
  cases h with
  | numeric h => cases h; rfl
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.vecConst_inv {b : BitVec 128} (h : InstrOk C (.vecConst b) it) :
    it = .plain [] [.vec .v128] := by
  cases h with
  | vector h => cases h; rfl
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.refNull_inv {ht : HeapType} (h : InstrOk C (.refNull ht) it) :
    it = .plain [] [.refT true (C.closeHeap ht)] ∧ TyOk C.toTypeCtx (C.closeHeap ht) := by
  cases h with
  | reference h => cases h with | refNull h => exact ⟨rfl, h⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.refFunc_inv {x : FuncIdx} (h : InstrOk C (.refFunc x) it) :
    ∃ d, C.funcs[x.toNat]? = some d ∧ it = .plain [] [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | refFunc h _ => exact ⟨_, h, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.refI31_inv (h : InstrOk C .refI31 it) :
    it = .plain [.i32] [.refT false (.abs .i31)] := by
  cases h with
  | reference h => cases h; rfl
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.structNew_inv {x : TypeIdx} (h : InstrOk C (.structNew x) it) :
    ∃ d fs, C.type? x = some d ∧ Expand d (.struct fs) ∧
      it = .plain (fs.toList.map fieldUnpack) [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | structNew hd he => exact ⟨_, _, hd, he, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.structNewDefault_inv {x : TypeIdx} (h : InstrOk C (.structNewDefault x) it) :
    ∃ d fs, C.type? x = some d ∧ Expand d (.struct fs) ∧
      it = .plain [] [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | structNewDefault hd he _ => exact ⟨_, _, hd, he, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.arrayNew_inv {x : TypeIdx} (h : InstrOk C (.arrayNew x) it) :
    ∃ d m z, C.type? x = some d ∧ Expand d (.array (.field m z)) ∧
      it = .plain [z.unpack, .i32] [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | arrayNew hd he => exact ⟨_, _, _, hd, he, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.arrayNewDefault_inv {x : TypeIdx} (h : InstrOk C (.arrayNewDefault x) it) :
    ∃ d m z, C.type? x = some d ∧ Expand d (.array (.field m z)) ∧
      it = .plain [.i32] [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | arrayNewDefault hd he _ => exact ⟨_, _, _, hd, he, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.arrayNewFixed_inv {x : TypeIdx} {n : Fin (2 ^ 32)}
    (h : InstrOk C (.arrayNewFixed x n) it) :
    ∃ d m z, C.type? x = some d ∧ Expand d (.array (.field m z)) ∧
      it = .plain (List.replicate n.val z.unpack) [.refT false (.defHeap d)] := by
  cases h with
  | reference h => cases h with | arrayNewFixed hd he => exact ⟨_, _, _, hd, he, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.externConvertAny_inv (h : InstrOk C .externConvertAny it) :
    ∃ n, it = .plain [.refT n (.abs .any)] [.refT n (.abs .extern)] := by
  cases h with
  | reference h => cases h with | externConvertAny n => exact ⟨n, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.anyConvertExtern_inv (h : InstrOk C .anyConvertExtern it) :
    ∃ n, it = .plain [.refT n (.abs .extern)] [.refT n (.abs .any)] := by
  cases h with
  | reference h => cases h with | anyConvertExtern n => exact ⟨n, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.globalGet_inv {x : GlobalIdx} (h : InstrOk C (.globalGet x) it) :
    ∃ m t, C.globals[x.toNat]? = some ⟨m, t⟩ ∧ it = .plain [] [t] := by
  cases h with
  | «variable» h => cases h with | globalGet h => exact ⟨_, _, h, rfl⟩
  | _ => rename_i h; cases h

theorem _root_.Silmaril.Wasm.Validation.InstrOk.intBinOp_inv {t : IntType} {op : IntBinOp} (h : InstrOk C (.intBinOp t op) it) :
    it = .plain [.num (.int t), .num (.int t)] [.num (.int t)] := by
  cases h with
  | numeric h => cases h; rfl
  | _ => rename_i h; cases h

end Inversion

/-! ## Invariants of constant evaluation -/

/-- A locals-free, well-formed, closed validation context. -/
structure ConstCtxOk (C : Context) : Prop where
  wf : C.Wf
  locals : C.locals = []
  recs : C.recs = []
  types : ∀ d ∈ C.types, TyOk {} d

/-- The frame agrees with the typing context: referenced functions and constant
globals are typed in the final store `S`; the globals are read from the
current store `s`. -/
structure FrameAgree (S s : Store H) (C : Context) (f : Frame) : Prop where
  types : f.module.types = C.types
  funcs : ∀ (x : Nat) (d : DefType), C.funcs[x]? = some d →
    TyOk {} d ∧ ∃ a, f.module.funcs[x]? = some a ∧ RefOk S (.func a) (.ref false (.defHeap d))
  globals : ∀ (x : Nat) (gt : CGlobalType), C.globals[x]? = some gt → gt.mutability = .const →
    TyOk {} gt.type ∧ ∃ a gi, f.module.globals[x]? = some a ∧ s.globals[a]? = some gi ∧
      ValOk S gi.value gt.type ∧ gi.value.In s

/-- The heap of the current store is typed in the final store and acyclic. -/
structure HeapOk (S s : Store H) : Prop where
  structs : ∀ si ∈ s.structs, StructInstOk S si
  arrays : ∀ ai ∈ s.arrays, ArrayInstOk S ai
  inn : HeapIn s
  acyclic : HeapAcyclic s
  structsClosed : ∀ si ∈ s.structs, TyOk {} si.type
  arraysClosed : ∀ ai ∈ s.arrays, TyOk {} ai.type

theorem forall₂_of_mapM' {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM' hbs)

theorem Store.global?_spec_ce {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) :
    f.module.globals[x.toNat]? = some a ∧ s.globals[a]? = some g := by
  simp only [Store.global?] at h
  cases h₁ : f.module.globals[x.toNat]? with
  | none => simp [h₁] at h
  | some b =>
    cases h₂ : s.globals[b]? with
    | none => simp [h₁, h₂] at h
    | some t =>
      simp [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h₂⟩

theorem fieldUnpack_eq (ft : CFieldType) : fieldUnpack ft = (fieldStorage ft).unpack := by
  cases ft; rfl

theorem TyOk.fieldStorage {Δ : TypeCtx} {ft : CFieldType} (h : TyOk Δ ft) :
    TyOk Δ (fieldStorage ft) := by
  cases h with | field h => exact h

/-- Packing the operands of `struct.new` into the fields. -/
theorem packFields_ok {S : Store H} {Δ : TypeCtx} (hΔ : Δ.Ok) (hr : Δ.recs = []) :
    ∀ {fs : List CFieldType} {vs : List Val} {tw : List CValType},
      List.Forall₂ (ValOk S) vs tw → (∀ t ∈ tw, TyOk {} t) → (∀ ft ∈ fs, TyOk {} ft) →
      List.Forall₂ (Sub Δ) tw (fs.map fieldUnpack) →
      List.Forall₂ (FieldValOk S) ((fs.zip vs).map fun (ft, v) => packField (fieldStorage ft) v)
        (fs.map fieldStorage) := by
  intro fs
  induction fs with
  | nil => intro vs tw hv _ _ hs; cases hs; cases hv; exact .nil
  | cons ft fs ih =>
    intro vs tw hv htw hfs hs
    cases hs with
    | cons hs hss =>
      cases hv with
      | cons hv hvs =>
        refine .cons ?_ (ih hvs (fun t ht => htw t (by simp [ht]))
          (fun ft ht => hfs ft (by simp [ht])) hss)
        rw [fieldUnpack_eq] at hs
        exact packField_ok hΔ hr hv (htw _ (by simp)) (TyOk.fieldStorage (hfs ft (by simp))) hs

theorem ResultSub.replicate {Δ : TypeCtx} {a b : CValType} (h : Sub Δ a b) (n : Nat) :
    ResultSub Δ (List.replicate n a) (List.replicate n b) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons h ih

theorem ResultOk.replicate {Δ : TypeCtx} {a : CValType} (h : TyOk Δ a) (n : Nat) :
    ResultOk Δ (List.replicate n a) := by
  intro t ht
  rw [(List.mem_replicate.mp ht).2]; exact h

theorem TyOk.refT_def {d : DefType} (hd : TyOk {} d) (n : Bool) :
    TyOk {} (Ty.refT n (.defHeap d)) := .refv (.ref (.use (.dt hd)))

theorem Sub.refT_null_le {Δ : TypeCtx} (h : CHeapType) (n : Bool) :
    Sub Δ (Ty.refT false h) (Ty.refT n h) := by
  cases n
  · exact .refv (.refNonNull .heapRefl)
  · exact .refv (.refNull .heapRefl)

/-- The values produced by a store extension that only appends structures and arrays. -/
theorem HeapIn.addStruct {s : Store H} (h : HeapIn s) {si : StructInst}
    (hsi : ∀ fv ∈ si.fields, fv.In s) : HeapIn (s.addStruct si) := by
  have m1 : s.structs.length ≤ (s.addStruct si).structs.length := by simp [Store.addStruct]
  refine ⟨fun si' hsi' fv hfv => ?_, fun ai hai fv hfv => ?_, fun e he v hv => ?_⟩
  · simp only [Store.addStruct, List.mem_append, List.mem_singleton] at hsi'
    rcases hsi' with hsi' | rfl
    · exact FieldVal.In.mono m1 (Nat.le_refl _) (Nat.le_refl _) (h.1 si' hsi' fv hfv)
    · exact FieldVal.In.mono m1 (Nat.le_refl _) (Nat.le_refl _) (hsi fv hfv)
  · exact FieldVal.In.mono m1 (Nat.le_refl _) (Nat.le_refl _) (h.2.1 ai hai fv hfv)
  · exact Val.In.mono m1 (Nat.le_refl _) (Nat.le_refl _) (h.2.2 e he v hv)

theorem HeapIn.addArray {s : Store H} (h : HeapIn s) {ai : ArrayInst}
    (hai : ∀ fv ∈ ai.fields, fv.In s) : HeapIn (s.addArray ai) := by
  have m1 : s.arrays.length ≤ (s.addArray ai).arrays.length := by simp [Store.addArray]
  refine ⟨fun si hsi fv hfv => ?_, fun ai' hai' fv hfv => ?_, fun e he v hv => ?_⟩
  · exact FieldVal.In.mono (s := s) (s' := s.addArray ai) (Nat.le_refl _) m1 (Nat.le_refl _) (h.1 si hsi fv hfv)
  · simp only [Store.addArray, List.mem_append, List.mem_singleton] at hai'
    rcases hai' with hai' | rfl
    · exact FieldVal.In.mono (s := s) (s' := s.addArray ai) (Nat.le_refl _) m1 (Nat.le_refl _) (h.2.1 ai' hai' fv hfv)
    · exact FieldVal.In.mono (s := s) (s' := s.addArray ai') (Nat.le_refl _) m1 (Nat.le_refl _) (hai fv hfv)
  · exact Val.In.mono (s := s) (s' := s.addArray ai) (Nat.le_refl _) m1 (Nat.le_refl _) (h.2.2 e he v hv)

theorem packField_in {s : Store H} {z : CStorageType} {v : Val} (h : v.In s) :
    (packField z v).In s := by
  unfold packField
  split <;> trivial

/-! ## Typing of a constant redex -/

/-- The reduct of a constant redex: values of runtime types followed by
constant instructions that consume them and produce a subtype of `r`. -/
def RedexOut (S s' : Store H) (C : Context) (out : List Admin) (r : List CValType) : Prop :=
  ∃ ws js two r₀, out = vals ws ++ expression js ∧ List.Forall₂ (ValOk S) ws two ∧
    (∀ t ∈ two, TyOk {} t) ∧ (∀ v ∈ ws, v.In s') ∧ InstrsOk C js ⟨two, [], r₀⟩ ∧
    ResultSub C.toTypeCtx r₀ r ∧ (∀ j ∈ js, InstrConst C j)

theorem RedexOut.single {S s' : Store H} {C : Context} {v : Val} {t : CValType}
    (hv : ValOk S v t) (ht : TyOk {} t) (hin : v.In s') {r : List CValType}
    (hr : ResultSub C.toTypeCtx [t] r) : RedexOut S s' C [v.toAdmin] r := by
  refine ⟨[v], [], [t], [t], by simp [vals, expression], .cons hv .nil, by simpa using ht,
    by simpa using hin, InstrsOk.id ?_, hr, by simp⟩
  intro t' ht'; simp at ht'; subst ht'; exact TyOk.of_empty _ ht

theorem ConstRedex.store_shape {s s' : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s' out) :
    s' = s ∨ (∃ si, s' = s.addStruct si) ∨ (∃ ai, s' = s.addArray ai) := by
  cases h <;> first | exact .inl rfl | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr ⟨_, rfl⟩)

theorem Frame.type?_eq {f : Frame} {C : Context} (h : f.module.types = C.types) {x : TypeIdx}
    {d d' : DefType} (hd : f.type? x = some d) (hd' : C.type? x = some d') : d = d' := by
  unfold Frame.type? at hd
  unfold Context.type? at hd'
  rw [h] at hd
  exact Option.some.inj (hd.symm.trans hd')

theorem ConstRedex.arity {s s' : Store H} {f : Frame} {C : Context} {w : List Val} {i : Instr}
    {out : List Admin} (hfa : f.module.types = C.types) (h : ConstRedex s f w i s' out)
    {p r : List CValType} {xs : List Nat} (hi : InstrOk C i ⟨p, xs, r⟩) :
    w.length = p.length := by
  cases h with
  | refNull => obtain ⟨hit, -⟩ := hi.refNull_inv; cases hit; rfl
  | refFunc => obtain ⟨_, _, hit⟩ := hi.refFunc_inv; cases hit; rfl
  | refI31 => have hit := hi.refI31_inv; cases hit; rfl
  | structNew hd he hn =>
    obtain ⟨d', fs', hd', he', hit⟩ := hi.structNew_inv
    cases hit
    obtain rfl := Frame.type?_eq hfa hd hd'
    have := Expand.func_eq he he'
    cases this
    simpa [Ty.length] using hn
  | structNewDefault => obtain ⟨_, _, _, _, hit⟩ := hi.structNewDefault_inv; cases hit; rfl
  | arrayNew => obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNew_inv; cases hit; rfl
  | arrayNewDefault => obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNewDefault_inv; cases hit; rfl
  | arrayNewFixed hd he hn =>
    obtain ⟨_, _, _, _, _, hit⟩ := hi.arrayNewFixed_inv; cases hit; simpa using hn
  | externConvertNull => obtain ⟨_, hit⟩ := hi.externConvertAny_inv; cases hit; rfl
  | externConvertAddr => obtain ⟨_, hit⟩ := hi.externConvertAny_inv; cases hit; rfl
  | anyConvertNull => obtain ⟨_, hit⟩ := hi.anyConvertExtern_inv; cases hit; rfl
  | anyConvertAddr => obtain ⟨_, hit⟩ := hi.anyConvertExtern_inv; cases hit; rfl
  | globalGet => obtain ⟨_, _, _, hit⟩ := hi.globalGet_inv; cases hit; rfl
  | binop => have hit := hi.intBinOp_inv; cases hit; rfl

theorem defaultVal?_in {s : Store H} {t : CValType} {v : Val} (h : defaultVal? t = some v) :
    v.In s := by
  unfold defaultVal? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> trivial

theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) (n : Nat) :
    List.Forall₂ R (List.replicate n a) (List.replicate n b) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons h ih

theorem forall₂_mem_left' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_mem_left' hs a h
      exact ⟨b, by simp [hb], hr⟩

theorem forall₂_mem_right' {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab hs, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right' hs b h
      exact ⟨a, by simp [ha], hr⟩

theorem forall₂_replicate_right {α β : Type} {R : α → β → Prop} {b : β} :
    ∀ {l : List α} {n : Nat}, List.Forall₂ R l (List.replicate n b) → ∀ a ∈ l, R a b
  | _, 0, h, a, ha => by cases h; cases ha
  | _, n + 1, .cons h hs, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h
    · exact forall₂_replicate_right hs a ha

theorem prefix_getElem_last {α : Type} {l l' : List α} {x : α} (h : l ++ [x] <+: l') :
    l'[l.length]? = some x := by
  obtain ⟨t, rfl⟩ := h
  simp

/-- **Typing of a constant redex** (against the final store `S`). -/
theorem ConstRedex.typed {S s s' : Store H} {f : Frame} {C : Context} {w : List Val} {i : Instr}
    {out : List Admin} (hC : ConstCtxOk C) (hfa : FrameAgree S s C f) (hheap : HeapOk S s)
    (hps : s'.structs <+: S.structs) (hpa : s'.arrays <+: S.arrays)
    (hr : ConstRedex s f w i s' out) (hic : InstrConst C i) {p r : List CValType}
    (hi : InstrOk C i ⟨p, [], r⟩) {tw : List CValType} (hw : List.Forall₂ (ValOk S) w tw)
    (htw : ∀ t ∈ tw, TyOk {} t) (hwin : ∀ v ∈ w, v.In s)
    (hsub : ResultSub C.toTypeCtx tw p) :
    RedexOut S s' C out r ∧ HeapOk S s' := by
  have hΔ : C.toTypeCtx.Ok := hC.wf.types
  have hrec : C.toTypeCtx.recs = [] := hC.recs
  cases hr with
  | refNull ht =>
    obtain ⟨hit, hok⟩ := hi.refNull_inv
    cases hit
    have hty : TyOk {} (C.closeHeap ht) := TyOk.closeHeap_empty hC.types rfl hok
    exact ⟨RedexOut.single (v := .ref .null) (.ref (.sub .null (.ref hty) (.refNull .bot)))
      (.refv (.ref hty)) trivial (ResultSub.refl _ _), hheap⟩
  | refFunc hfx =>
    obtain ⟨d, hd, hit⟩ := hi.refFunc_inv
    cases hit
    obtain ⟨hdok, a', ha', hra⟩ := hfa.funcs _ _ hd
    rw [hfx] at ha'
    cases ha'
    exact ⟨RedexOut.single (v := .ref (.func _)) (.ref hra) (TyOk.refT_def hdok false) trivial
      (ResultSub.refl _ _), hheap⟩
  | refI31 i =>
    have hit := hi.refI31_inv
    cases hit
    exact ⟨RedexOut.single (v := .ref (.i31 _)) (.ref (.i31 _)) (TyOk.refT_abs false .i31)
      trivial (ResultSub.refl _ _), hheap⟩
  | structNew hd he hn =>
    obtain ⟨d', fs', hd', he', hit⟩ := hi.structNew_inv
    cases hit
    have e1 : d' = _ := (Frame.type?_eq hfa.types hd hd').symm
    subst e1
    have e2 : fs' = _ := (Ty.struct.inj (Expand.func_eq he he')).symm
    subst e2
    have hdok : TyOk {} d' := hC.types d' (List.mem_of_getElem? hd')
    have hfsok : ∀ ft ∈ fs'.toList, TyOk {} ft := Expand.struct_ok hdok he'
    have hfields := packFields_ok hΔ hrec hw htw hfsok hsub
    have hin : ∀ fv ∈ ((fs'.toList.zip w).map fun (ft, v) => packField (fieldStorage ft) v),
        fv.In s := by
      intro fv hfv
      obtain ⟨⟨ft, v⟩, hmem, rfl⟩ := List.mem_map.mp hfv
      exact packField_in (hwin v (List.of_mem_zip hmem).2)
    have hS := prefix_getElem_last hps
    refine ⟨RedexOut.single (v := .ref (.struct s.structs.length)) (.ref (.struct hS))
      (TyOk.refT_def hdok false) (by simp [Val.In, Ref.In, Store.addStruct])
      (ResultSub.refl _ _), ?_⟩
    refine ⟨fun si hsi => ?_, hheap.arrays, hheap.inn.addStruct hin,
      hheap.acyclic.addStruct hheap.inn hin, fun si hsi => ?_, hheap.arraysClosed⟩
    · simp only [Store.addStruct, List.mem_append, List.mem_singleton] at hsi
      rcases hsi with hsi | rfl
      · exact hheap.structs si hsi
      · exact ⟨fs', he', hfields⟩
    · simp only [Store.addStruct, List.mem_append, List.mem_singleton] at hsi
      rcases hsi with hsi | rfl
      · exact hheap.structsClosed si hsi
      · exact hdok
  | @structNewDefault x d fs vs hd he hdef =>
    obtain ⟨d', fs', hd', he', hit⟩ := hi.structNewDefault_inv
    cases hit
    obtain rfl := Frame.type?_eq hfa.types hd hd'
    have hfs := Expand.func_eq he he'
    cases hfs
    have hdok : TyOk {} d := hC.types d (List.mem_of_getElem? hd')
    have hfsok : ∀ ft ∈ fs.toList, TyOk {} ft := Expand.struct_ok hdok he
    have hvs := forall₂_of_mapM' hdef
    have hvals : List.Forall₂ (ValOk S) vs (fs.toList.map fieldUnpack) := by
      clear hdef
      revert hfsok
      generalize fs.toList = L at hvs ⊢
      intro hfsok
      induction hvs with
      | nil => exact .nil
      | @cons ft v fts vs' h _ ih =>
        refine .cons ?_ (ih fun ft' h' => hfsok ft' (by simp [h']))
        rw [fieldUnpack_eq]
        exact defaultVal?_ok h (TyOk.unpack (TyOk.fieldStorage (hfsok ft (by simp))))
    have hvin : ∀ v ∈ vs, v.In s := by
      intro v hv
      obtain ⟨ft, -, h⟩ := forall₂_mem_right' hvs v hv
      exact defaultVal?_in h
    refine ⟨⟨vs, [.structNew x], fs.toList.map fieldUnpack, _, by simp [expression], hvals,
      ?_, hvin, .instr (.reference (.structNew hd' he)), ResultSub.refl _ _, ?_⟩, hheap⟩
    · intro t ht
      obtain ⟨ft, hft, rfl⟩ := List.mem_map.mp ht
      exact TyOk.fieldUnpack (hfsok ft hft)
    · intro j hj; simp at hj; subst hj; exact .structNew x
  | @arrayNew x v n =>
    obtain ⟨d, m, z, hd, he, hit⟩ := hi.arrayNew_inv
    cases hit
    match tw, hw, hsub, htw with
    | [t1, t2], .cons hv1 (.cons _ .nil), .cons hs1 (.cons _ .nil), htw =>
    have ht1 : TyOk {} t1 := htw t1 (by simp)
    have hdok : TyOk {} d := hC.types d (List.mem_of_getElem? hd)
    refine ⟨⟨List.replicate n.toNat v, [.arrayNewFixed x ⟨n.toNat, n.isLt⟩],
      List.replicate n.toNat t1, _, by simp [expression], forall₂_replicate hv1 _, ?_, ?_, ?_,
      ResultSub.refl _ _, ?_⟩, hheap⟩
    · intro t ht; rw [(List.mem_replicate.mp ht).2]; exact ht1
    · intro v' hv'; rw [(List.mem_replicate.mp hv').2]; exact hwin v (by simp)
    · refine .sub (.instr (.reference (.arrayNewFixed hd he)))
        ⟨ResultSub.replicate hs1 _, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
        ⟨ResultOk.replicate (TyOk.of_empty _ ht1) _, ?_, by simp⟩
      intro t ht; simp at ht; subst ht; exact TyOk.of_empty _ (TyOk.refT_def hdok false)
    · intro j hj; simp at hj; subst hj; exact .arrayNewFixed x _
  | @arrayNewDefault x n d ft dv hd he hv =>
    obtain ⟨d', m, z, hd', he', hit⟩ := hi.arrayNewDefault_inv
    cases hit
    obtain rfl := Frame.type?_eq hfa.types hd hd'
    have hft := Expand.func_eq he he'
    cases hft
    have hdok : TyOk {} d := hC.types d (List.mem_of_getElem? hd')
    have hz : TyOk {} z.unpack := TyOk.unpack (Expand.array_ok hdok he)
    have hdv : ValOk S dv z.unpack := defaultVal?_ok hv hz
    refine ⟨⟨List.replicate n.toNat dv, [.arrayNewFixed x ⟨n.toNat, n.isLt⟩],
      List.replicate n.toNat z.unpack, _, by simp [expression], forall₂_replicate hdv _, ?_, ?_,
      .instr (.reference (.arrayNewFixed hd' he)), ResultSub.refl _ _, ?_⟩, hheap⟩
    · intro t ht; rw [(List.mem_replicate.mp ht).2]; exact hz
    · intro v' hv'; rw [(List.mem_replicate.mp hv').2]; exact defaultVal?_in hv
    · intro j hj; simp at hj; subst hj; exact .arrayNewFixed x _
  | arrayNewFixed hd he hn =>
    obtain ⟨d', m, z, hd', he', hit⟩ := hi.arrayNewFixed_inv
    cases hit
    have e1 : d' = _ := (Frame.type?_eq hfa.types hd hd').symm
    subst e1
    have e2 : Ty.field m z = _ := (Ty.array.inj (Expand.func_eq he he')).symm
    rw [← e2] at he ⊢
    have hdok : TyOk {} d' := hC.types d' (List.mem_of_getElem? hd')
    have hz : TyOk {} z := Expand.array_ok hdok he'
    have hin : ∀ fv ∈ w.map (packField (fieldStorage (.field m z))), fv.In s := by
      intro fv hfv
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hfv
      exact packField_in (hwin v hv)
    have hS := prefix_getElem_last hpa
    refine ⟨RedexOut.single (v := .ref (.array s.arrays.length)) (.ref (.array hS))
      (TyOk.refT_def hdok false) (by simp [Val.In, Ref.In, Store.addArray])
      (ResultSub.refl _ _), ?_⟩
    refine ⟨hheap.structs, fun ai hai => ?_, hheap.inn.addArray hin,
      hheap.acyclic.addArray hheap.inn hin, hheap.structsClosed, fun ai hai => ?_⟩
    rotate_left
    · simp only [Store.addArray, List.mem_append, List.mem_singleton] at hai
      rcases hai with hai | rfl
      · exact hheap.arraysClosed ai hai
      · exact hdok
    simp only [Store.addArray, List.mem_append, List.mem_singleton] at hai
    rcases hai with hai | rfl
    · exact hheap.arrays ai hai
    · refine ⟨.field m z, he', fun fv hfv => ?_⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hfv
      obtain ⟨t, ht, hvt⟩ := forall₂_mem_left' hw v hv
      exact packField_ok hΔ hrec hvt (htw t ht) hz (forall₂_replicate_right hsub t ht)
  | externConvertNull =>
    obtain ⟨n, hit⟩ := hi.externConvertAny_inv
    cases hit
    match tw, hw, hsub with
    | [t1], .cons hv1 .nil, .cons hs1 .nil =>
    cases hv1 with
    | ref hr1 =>
    obtain ⟨h', rfl⟩ := hr1.null_nullable
    cases hs1 with
    | refv hs1 =>
    obtain rfl := Sub.ref_nullable hs1
    exact ⟨RedexOut.single (v := .ref .null)
      (.ref (.sub .null (.ref (.abs _)) (.refNull .bot))) (TyOk.refT_abs true .extern) trivial
      (ResultSub.refl _ _), hheap⟩
  | @externConvertAddr r hrn =>
    obtain ⟨n, hit⟩ := hi.externConvertAny_inv
    cases hit
    match tw, hw, hsub, htw with
    | [t1], .cons hv1 .nil, .cons hs1 .nil, htw =>
    have hv' := hv1.sub_ctx_ce hΔ hrec (htw t1 (by simp)) (TyOk.refT_abs n .any) hs1
    cases hv' with
    | ref hr' =>
    have hin : (Val.ref (.extern r)).In s := hwin (.ref r) (by simp)
    exact ⟨RedexOut.single (v := .ref (.extern r)) (.ref (.extern (hr'.nonnull hrn) hrn))
      (TyOk.refT_abs false .extern) hin (.cons (Sub.refT_null_le _ n) .nil), hheap⟩
  | anyConvertNull =>
    obtain ⟨n, hit⟩ := hi.anyConvertExtern_inv
    cases hit
    match tw, hw, hsub with
    | [t1], .cons hv1 .nil, .cons hs1 .nil =>
    cases hv1 with
    | ref hr1 =>
    obtain ⟨h', rfl⟩ := hr1.null_nullable
    cases hs1 with
    | refv hs1 =>
    obtain rfl := Sub.ref_nullable hs1
    exact ⟨RedexOut.single (v := .ref .null)
      (.ref (.sub .null (.ref (.abs _)) (.refNull .bot))) (TyOk.refT_abs true .any) trivial
      (ResultSub.refl _ _), hheap⟩
  | anyConvertAddr r =>
    obtain ⟨n, hit⟩ := hi.anyConvertExtern_inv
    cases hit
    match tw, hw with
    | [t1], .cons hv1 .nil =>
    cases hv1 with
    | ref hr1 =>
    obtain ⟨_, _, _, hx⟩ := hr1.principal
    obtain ⟨hr', -⟩ := hx r rfl
    have hin : (Val.ref r).In s := hwin (.ref (.extern r)) (by simp)
    exact ⟨RedexOut.single (v := .ref r) (.ref hr') (TyOk.refT_abs false .any)
      hin (.cons (Sub.refT_null_le _ n) .nil), hheap⟩
  | globalGet hg =>
    obtain ⟨m, t, hgx, hit⟩ := hi.globalGet_inv
    cases hit
    have hm : m = .const := by
      cases hic with
      | globalGet hc => rw [hgx] at hc; cases hc; rfl
    obtain ⟨htok, a', gi, ha', hgi, hval, hin⟩ := hfa.globals _ _ hgx hm
    obtain ⟨ha, hga⟩ := Store.global?_spec_ce hg
    rw [ha] at ha'
    cases ha'
    rw [hga] at hgi
    cases hgi
    exact ⟨RedexOut.single hval htok hin (ResultSub.refl _ _), hheap⟩
  | @binop t op x y z h =>
    have hit := hi.intBinOp_inv
    cases hit
    exact ⟨RedexOut.single (v := .num ⟨.int t, z⟩) (.num _) (.num _) trivial
      (ResultSub.refl _ _), hheap⟩

/-! ## Running constant code -/

/-- Constant evaluation leaves the store unchanged except for appended globals,
structures and arrays. -/
structure EvalShape (s s' : Store H) : Prop where
  tags : s'.tags = s.tags
  mems : s'.mems = s.mems
  tables : s'.tables = s.tables
  funcs : s'.funcs = s.funcs
  datas : s'.datas = s.datas
  elems : s'.elems = s.elems
  exns : s'.exns = s.exns
  globals : s.globals <+: s'.globals
  structs : s.structs <+: s'.structs
  arrays : s.arrays <+: s'.arrays

theorem EvalShape.refl (s : Store H) : EvalShape s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem EvalShape.trans {s₁ s₂ s₃ : Store H} (h₁ : EvalShape s₁ s₂) (h₂ : EvalShape s₂ s₃) :
    EvalShape s₁ s₃ :=
  ⟨h₂.tags.trans h₁.tags, h₂.mems.trans h₁.mems, h₂.tables.trans h₁.tables,
    h₂.funcs.trans h₁.funcs, h₂.datas.trans h₁.datas, h₂.elems.trans h₁.elems,
    h₂.exns.trans h₁.exns, h₁.globals.trans h₂.globals, h₁.structs.trans h₂.structs,
    h₁.arrays.trans h₂.arrays⟩

theorem EvalShape.of_redex {s s' : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s' out) : EvalShape s s' := by
  rcases h.store_shape with rfl | ⟨si, rfl⟩ | ⟨ai, rfl⟩
  · exact EvalShape.refl _
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_append _ _,
      List.prefix_refl _⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, List.prefix_refl _,
      List.prefix_append _ _⟩

theorem EvalShape.lengths {s s' : Store H} (h : EvalShape s s') :
    s.structs.length ≤ s'.structs.length ∧ s.arrays.length ≤ s'.arrays.length ∧
      s.exns.length ≤ s'.exns.length :=
  ⟨h.structs.length_le, h.arrays.length_le, by rw [h.exns]⟩

theorem ConstRedex.out_constOk {s s' : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s' out) : ∀ a ∈ out, a.ConstOk := by
  cases h <;> intro a ha <;>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    first
    | (subst ha; exact Admin.constOk_toAdmin _)
    | (subst ha; simp [Admin.ConstOk, Instr.IsConstI])
    | (rcases ha with ha | rfl
       · exact Admin.constOk_vals _ a ha
       · simp [Admin.ConstOk, Instr.IsConstI])

theorem ConstRedex.globals_eq {s s' : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s' out) : s'.globals = s.globals := by
  rcases h.store_shape with rfl | ⟨si, rfl⟩ | ⟨ai, rfl⟩ <;> rfl

/-- Constant code steps to constant code, only appending to the heap. -/
theorem Steps.const_shape {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hc : ∀ a ∈ c.code, a.ConstOk) :
    EvalShape c.store c'.store ∧ c'.frame = c.frame ∧ (∀ a ∈ c'.code, a.ConstOk) ∧
      c'.store.globals = c.store.globals := by
  induction h with
  | refl => exact ⟨EvalShape.refl _, rfl, hc, rfl⟩
  | tail _ hst ih =>
    obtain ⟨hsh, hf, hc', hg⟩ := ih
    obtain ⟨hf', pre, w, i, post, out, e₁, e₂, hr⟩ := hst.const_redex hc'
    refine ⟨hsh.trans (EvalShape.of_redex hr), hf'.trans hf, ?_, hr.globals_eq.trans hg⟩
    rw [e₂]
    have hpost : ∀ a ∈ post, a.ConstOk := fun a ha => hc' a (by rw [e₁]; simp [ha])
    intro a ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · exact Admin.constOk_vals _ a ha
    · exact hr.out_constOk a ha
    · exact hpost a ha

/-- A typed state: values of runtime types followed by constant instructions. -/
def CodeOk (S s : Store H) (C : Context) (vs : List Val) (is : List Instr) (t : CValType) :
    Prop :=
  ∃ ts, List.Forall₂ (ValOk S) vs ts ∧ (∀ t ∈ ts, TyOk {} t) ∧ (∀ v ∈ vs, v.In s) ∧
    InstrsOk C is ⟨ts, [], [t]⟩ ∧ ∀ i ∈ is, InstrConst C i

/-- The instructions start with a non-value. -/
def Canon (is : List Instr) : Prop := ∀ i is', is = i :: is' → Admin.val? (.plain i) = none

theorem vals_nonval_eq {i i' : Instr} (hi : Admin.val? (.plain i) = none)
    (hi' : Admin.val? (.plain i') = none) :
    ∀ {A A' : List Val} {B B' : List Admin},
      vals A ++ .plain i :: B = vals A' ++ .plain i' :: B' → A = A' ∧ i = i' ∧ B = B'
  | [], [], B, B', h => by simp [vals] at h; exact ⟨rfl, h⟩
  | [], v :: A', B, B', h => by
    simp only [vals, List.map_nil, List.nil_append, List.map_cons, List.cons_append,
      List.cons.injEq] at h
    have := congrArg Admin.val? h.1
    rw [Admin.val?_toAdmin, hi] at this; cases this
  | v :: A, [], B, B', h => by
    simp only [vals, List.map_nil, List.nil_append, List.map_cons, List.cons_append,
      List.cons.injEq] at h
    have := congrArg Admin.val? h.1
    rw [Admin.val?_toAdmin, hi'] at this; cases this
  | v :: A, v' :: A', B, B', h => by
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    have hv : v = v' := by
      have := congrArg Admin.val? h.1
      simpa using this
    subst hv
    obtain ⟨rfl, rfl, rfl⟩ := vals_nonval_eq hi hi' (A := A) (A' := A') h.2
    exact ⟨rfl, rfl, rfl⟩

theorem vals_ne_nonval {i : Instr} (hi : Admin.val? (.plain i) = none) :
    ∀ {A ws : List Val} {B : List Admin}, vals A ++ .plain i :: B ≠ vals ws
  | [], [], B, h => by simp [vals] at h
  | [], w :: ws, B, h => by
    simp only [vals, List.map_nil, List.nil_append, List.map_cons, List.cons.injEq] at h
    have := congrArg Admin.val? h.1
    rw [Admin.val?_toAdmin, hi] at this; cases this
  | v :: A, [], B, h => by simp [vals] at h
  | v :: A, w :: ws, B, h => by
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    exact vals_ne_nonval hi h.2

theorem vals_injective' : ∀ {A B : List Val}, vals A = vals B → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals] at h
  | _ :: _, [], h => by simp [vals] at h
  | a :: A, b :: B, h => by
    simp only [vals, List.map_cons, List.cons.injEq] at h
    have hab : a = b := by
      have := congrArg Admin.val? h.1
      simpa using this
    rw [hab, vals_injective' h.2]

theorem ConstRedex.nonval {s s' : Store H} {f : Frame} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s f w i s' out) : Admin.val? (.plain i) = none := by
  cases h <;> rfl

theorem expression_cons' (i : Instr) (is : List Instr) :
    expression (i :: is) = .plain i :: expression is := rfl

theorem expression_append' (is js : List Instr) :
    expression (is ++ js) = expression is ++ expression js := List.map_append ..

theorem expression_eq_nil {is : List Instr} (h : expression is = []) : is = [] :=
  List.map_eq_nil_iff.mp h

theorem Admin.val?_plain_inv {i : Instr} {v : Val} (hv : Admin.val? (.plain i) = some v) :
    ∃ tv, (∀ (C : Context) it, InstrOk C i it → it = .plain [] [tv]) ∧
      (∀ (S : Store H), ValOk S v tv) ∧ TyOk {} tv ∧ ∀ (s : Store H), v.In s := by
  cases i <;> simp only [Admin.val?, Option.some.injEq, reduceCtorEq] at hv <;> subst hv
  · exact ⟨_, fun C it h => h.intConst_inv, fun S => .num _, .num _, fun _ => trivial⟩
  · exact ⟨_, fun C it h => h.floatConst_inv, fun S => .num _, .num _, fun _ => trivial⟩
  · exact ⟨_, fun C it h => h.vecConst_inv, fun S => .vec _, .vec _, fun _ => trivial⟩

/-- Absorb leading value instructions into the value stack. -/
theorem CodeOk.normalize {S s : Store H} {C : Context} (hC : ConstCtxOk C) {t : CValType} :
    ∀ {is : List Instr} {vs : List Val}, CodeOk S s C vs is t →
      ∃ vs' is', vals vs ++ expression is = vals vs' ++ expression is' ∧ CodeOk S s C vs' is' t ∧
        Canon is'
  | [], vs, h => ⟨vs, [], rfl, h, fun _ _ e => by cases e⟩
  | i :: is, vs, h => by
    cases hv : Admin.val? (.plain i) with
    | none =>
      exact ⟨vs, i :: is, rfl, h, fun i' is' e => by cases e; exact hv⟩
    | some v =>
      obtain ⟨ts, hts, htsok, hvin, hty, hcst⟩ := h
      obtain ⟨pre, p, r, hi, hpre, hsub, hrest⟩ := InstrsOk.cons_inv' hC.wf hC.locals hty
      obtain ⟨tv, hinv, hvt', htv, hvin'⟩ := Admin.val?_plain_inv (H := H) hv
      have hvt := hvt' S
      have hit := hinv C _ hi
      simp only [InstrType.plain, InstrType.mk.injEq] at hit
      obtain ⟨rfl, -, rfl⟩ := hit
      simp only [List.append_nil] at hsub
      have h' : CodeOk S s C (vs ++ [v]) is t := by
        refine ⟨ts ++ [tv], List.rel_append hts (.cons hvt .nil), ?_, ?_, ?_,
          fun j hj => hcst j (by simp [hj])⟩
        · intro t' ht'
          rcases List.mem_append.mp ht' with ht' | ht'
          · exact htsok t' ht'
          · simp at ht'; subst ht'; exact htv
        · intro v' hv'
          rcases List.mem_append.mp hv' with hv' | hv'
          · exact hvin v' hv'
          · simp at hv'; subst hv'; exact hvin' s
        · have hr := InstrsOk.regular hC.wf hrest
          refine InstrsOk.sub hrest ⟨ResultSub.append hsub (ResultSub.refl _ _),
            ResultSub.refl _ _, fun _ h hn => absurd h hn⟩ ⟨?_, hr.2.1, by simp⟩
          intro t' ht'
          rcases List.mem_append.mp ht' with ht' | ht'
          · exact TyOk.of_empty _ (htsok t' ht')
          · simp at ht'; subst ht'; exact TyOk.of_empty _ htv
      obtain ⟨vs', is', e, h'', hc⟩ := CodeOk.normalize hC h'
      refine ⟨vs', is', ?_, h'', hc⟩
      rw [← e, expression_cons', Admin.eq_of_val? hv]
      simp [vals]

theorem forall₂_append_split {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List α} {c : List β} {d : List β},
      List.Forall₂ R (a ++ b) (c ++ d) → a.length = c.length →
      List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], _, [], _, h, _ => ⟨.nil, h⟩
  | [], _, _ :: _, _, _, hl => by simp at hl
  | _ :: _, _, [], _, _, hl => by simp at hl
  | x :: a, b, y :: c, d, .cons h hs, hl => by
    obtain ⟨h₁, h₂⟩ := forall₂_append_split hs (by simpa using hl)
    exact ⟨.cons h h₁, h₂⟩

theorem forall₂_append_left_split {α β : Type} {R : α → β → Prop} :
    ∀ {a b : List α} {l : List β}, List.Forall₂ R (a ++ b) l →
      ∃ c d, l = c ++ d ∧ List.Forall₂ R a c ∧ List.Forall₂ R b d
  | [], b, l, h => ⟨[], l, rfl, .nil, h⟩
  | x :: a, b, _ :: l, .cons h hs => by
    obtain ⟨c, d, rfl, h₁, h₂⟩ := forall₂_append_left_split hs
    exact ⟨_ :: c, d, rfl, .cons h h₁, h₂⟩

theorem CodeOk.constOk {S s : Store H} {C : Context} {vs : List Val} {is : List Instr}
    {t : CValType} (h : CodeOk S s C vs is t) : ∀ a ∈ vals vs ++ expression is, a.ConstOk := by
  obtain ⟨_, _, _, _, _, hcst⟩ := h
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact Admin.constOk_vals _ a ha
  · simp only [expression, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact (hcst i hi).isConstI

theorem FrameAgree.of_shape {S s s' : Store H} {C : Context} {f : Frame}
    (h : FrameAgree S s C f) (hsh : EvalShape s s') : FrameAgree S s' C f := by
  refine ⟨h.types, h.funcs, fun x gt hx hc => ?_⟩
  obtain ⟨htok, a, gi, ha, hgi, hv, hin⟩ := h.globals x gt hx hc
  obtain ⟨l, hl⟩ := hsh.globals
  obtain ⟨m1, m2, m3⟩ := hsh.lengths
  refine ⟨htok, a, gi, ha, ?_, hv, Val.In.mono m1 m2 m3 hin⟩
  rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hgi).1]; exact hgi

/-- **One step of typed constant code.** -/
theorem CodeOk.step {P : Profile} {host : HostSemantics H} {S s s' : Store H} {f f' : Frame}
    {C : Context} {vs : List Val} {is : List Instr} {t : CValType} {code' : List Admin}
    (hC : ConstCtxOk C) (hcode : CodeOk S s C vs is t) (hcan : Canon is) (hheap : HeapOk S s)
    (hfa : FrameAgree S s C f)
    (hst : Step P host ⟨s, f, vals vs ++ expression is⟩ ⟨s', f', code'⟩)
    (hps : s'.structs <+: S.structs) (hpa : s'.arrays <+: S.arrays) :
    f' = f ∧ EvalShape s s' ∧ HeapOk S s' ∧ FrameAgree S s' C f ∧
      ∃ vs' is', code' = vals vs' ++ expression is' ∧ CodeOk S s' C vs' is' t := by
  have hc := hcode.constOk
  obtain ⟨ts, hts, htsok, hvin, hty, hcst⟩ := hcode
  obtain ⟨hf, pre, w, i', post, out, e₁, e₂, hr⟩ := hst.const_redex hc
  simp only at hf e₁ e₂ hr
  cases is with
  | nil =>
    exfalso
    simp only [expression, List.map_nil, List.append_nil] at e₁
    exact vals_ne_nonval hr.nonval (A := pre ++ w) (B := post) (by simpa using e₁.symm)
  | cons i is₀ =>
    have hi0 := hcan i is₀ rfl
    obtain ⟨hvs, rfl, hpost⟩ := vals_nonval_eq hi0 hr.nonval (A := vs) (A' := pre ++ w)
      (B := expression is₀) (B' := post) (by simpa [expression_cons'] using e₁)
    subst hvs hpost
    obtain ⟨pre', p, r, hi, hpre', hsub, hrest⟩ := InstrsOk.cons_inv' hC.wf hC.locals hty
    obtain ⟨tpre, tw, rfl, htpre, htw⟩ := forall₂_append_left_split hts
    have hlen : w.length = p.length := hr.arity hfa.types hi
    have l1 := htpre.length_eq
    have l2 := htw.length_eq
    have l3 := hsub.length_eq
    simp only [List.length_append] at l3
    obtain ⟨hsubpre, hsubw⟩ := forall₂_append_split hsub (by omega)
    have hic : InstrConst C i := hcst i (by simp)
    obtain ⟨⟨ws, js, two, r₀, hout, hws, htwo, hwsin, hjs, hr₀, hjsc⟩, hheap'⟩ :=
      hr.typed hC hfa hheap hps hpa hic hi htw (fun t ht => htsok t (by simp [ht]))
        (fun v hv => hvin v (by simp [hv])) hsubw
    have hsh := EvalShape.of_redex hr
    obtain ⟨m1, m2, m3⟩ := hsh.lengths
    refine ⟨hf, hsh, hheap', hfa.of_shape hsh, pre ++ ws, js ++ is₀, ?_, ?_⟩
    · rw [e₂, hout]; simp [expression_append']
    · have htpreok : ResultOk C.toTypeCtx tpre := fun t' ht' =>
        TyOk.of_empty _ (htsok t' (by simp [ht']))
      have hjs' : InstrsOk C js ⟨tpre ++ two, [], tpre ++ r₀⟩ := InstrsOk.frame hjs htpreok
      have hr₀ok := (InstrsOk.regular hC.wf hjs).2.1
      have hrest' : InstrsOk C is₀ ⟨tpre ++ r₀, [], [t]⟩ :=
        InstrsOk.sub hrest ⟨ResultSub.append hsubpre hr₀, ResultSub.refl _ _,
          fun _ h hn => absurd h hn⟩
          ⟨ResultOk.append htpreok hr₀ok, (InstrsOk.regular hC.wf hrest).2.1, by simp⟩
      refine ⟨tpre ++ two, List.rel_append htpre hws, ?_, ?_, ?_, ?_⟩
      · intro t' ht'
        rcases List.mem_append.mp ht' with ht' | ht'
        · exact htsok t' (by simp [ht'])
        · exact htwo t' ht'
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact Val.In.mono m1 m2 m3 (hvin v (by simp [hv]))
        · exact hwsin v hv
      · simpa using InstrsOk.append hjs' (by simp) hrest'
      · intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact hjsc j hj
        · exact hcst j (by simp [hj])

/-- **Running typed constant code to values.** -/
theorem evalCode_ok {P : Profile} {host : HostSemantics H} {S : Store H} {C : Context}
    {t : CValType} (hC : ConstCtxOk C) (ht : TyOk {} t) {c c' : Config H} (h : Steps P host c c') :
    ∀ {vs : List Val} {is : List Instr}, c.code = vals vs ++ expression is →
      CodeOk S c.store C vs is t → HeapOk S c.store → FrameAgree S c.store C c.frame →
      ∀ {ws : List Val}, c'.code = vals ws → c'.store.structs <+: S.structs →
        c'.store.arrays <+: S.arrays →
        c'.frame = c.frame ∧ EvalShape c.store c'.store ∧ HeapOk S c'.store ∧
          FrameAgree S c'.store C c.frame ∧ ∃ v, ws = [v] ∧ ValOk S v t ∧ v.In c'.store := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro vs is hc hcode hheap hfa ws hc' _ _
    obtain ⟨vs', is', e, hcode', hcan⟩ := hcode.normalize hC
    have e' : vals vs' ++ expression is' = vals ws := by rw [← e, ← hc, hc']
    cases is' with
    | cons i is₀ =>
      exfalso
      exact vals_ne_nonval (hcan i is₀ rfl) (A := vs') (B := expression is₀)
        (by simpa [expression_cons'] using e')
    | nil =>
      simp only [expression, List.map_nil, List.append_nil] at e'
      obtain rfl := vals_injective' e'
      obtain ⟨ts, hts, htsok, hvin, hty, -⟩ := hcode'
      obtain ⟨hsub, -⟩ := InstrsOk.nil_inv hC.wf hty
      simp only at hsub
      match ts, hts, hsub with
      | [tv], .cons hv .nil, .cons hs .nil =>
        exact ⟨rfl, EvalShape.refl _, hheap, hfa, _, rfl,
          hv.sub_ctx_ce hC.wf.types hC.recs (htsok tv (by simp)) ht hs, hvin _ (by simp)⟩
  | head hst hrest ih =>
    rename_i c₀ c₁
    intro vs is hc hcode hheap hfa ws hc' hps hpa
    obtain ⟨vs', is', e, hcode', hcan⟩ := hcode.normalize hC
    have hc₀ : c₀.code = vals vs' ++ expression is' := hc.trans e
    have hk₀ : ∀ a ∈ c₀.code, a.ConstOk := by rw [hc₀]; exact hcode'.constOk
    obtain ⟨-, -, hk₁, -⟩ := Steps.const_shape (Relation.ReflTransGen.single hst) hk₀
    obtain ⟨hsh₁, -, -, -⟩ := Steps.const_shape hrest hk₁
    obtain ⟨s₀, f₀, code₀⟩ := c₀
    obtain ⟨s₁, f₁, code₁⟩ := c₁
    simp only at hc₀ hcode' hheap hfa hsh₁ ih ⊢
    subst hc₀
    obtain ⟨hf, hsh, hheap₁, hfa₁, vs₁, is₁, hc₁, hcode₁⟩ :=
      CodeOk.step hC hcode' hcan hheap hfa hst (hsh₁.structs.trans hps) (hsh₁.arrays.trans hpa)
    subst hf
    obtain ⟨hf', hsh', hheap', hfa', hv⟩ := ih hc₁ hcode₁ hheap₁ hfa₁ hc' hps hpa
    exact ⟨hf', hsh.trans hsh', hheap', hfa', hv⟩

/-- **Evaluating a constant expression.** -/
theorem EvalExpr.const_ok {P : Profile} {host : HostSemantics H} {S s s' : Store H}
    {f f' : Frame} {C : Context} {e : Expr} {vs : List Val} {t : CValType}
    (hC : ConstCtxOk C) (ht : TyOk {} t) (h : EvalExpr P host s f e s' f' vs)
    (he : ExprOkConst C e t) (hheap : HeapOk S s) (hfa : FrameAgree S s C f)
    (hps : s'.structs <+: S.structs) (hpa : s'.arrays <+: S.arrays) :
    f' = f ∧ EvalShape s s' ∧ HeapOk S s' ∧ FrameAgree S s' C f ∧
      ∃ v, vs = [v] ∧ ValOk S v t ∧ v.In s' :=
  evalCode_ok (c := ⟨s, f, expression e⟩) (c' := ⟨s', f', vals vs⟩) hC ht h (vs := [])
    (by simp [vals]) ⟨[], .nil, by simp, by simp, he.typed, he.const⟩ hheap hfa rfl hps hpa

/-- The shape of a constant evaluation, without typing. -/
theorem EvalExpr.const_shape {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {e : Expr} {vs : List Val} (h : EvalExpr P host s f e s' f' vs)
    (he : ∀ i ∈ e, i.IsConstI) : EvalShape s s' ∧ f' = f ∧ s'.globals = s.globals := by
  have := Steps.const_shape (c := ⟨s, f, expression e⟩) (c' := ⟨s', f', vals vs⟩) h (by
    intro a ha
    simp only [expression, List.mem_map] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact he i hi)
  exact ⟨this.1, this.2.1, this.2.2.2⟩

end Silmaril.Wasm.Execution.Core
