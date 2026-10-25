module

public import Silmaril.Wasm.Execution.Core.Soundness.ConstEvalTyping

@[expose] public section

/-! # Evaluation of constant initialisers (helpers for `Instantiate.alloc_ok`)

`$instantiate` evaluates the global, table and element initialisers in the
provisional module instance `moduleinst_0`, whose function addresses are only
allocated afterwards by `$allocmodule`. So the intermediate stores are *not*
valid (a `ref.func` may name a function that does not exist yet), and
`Step.preservation` does not apply. Instead the values are typed against the
*final* store `S`, of which every intermediate store is a prefix.

* `EvalShape s s'`: constant evaluation only appends globals (`$evalglobals`),
  structures and arrays;
* `InitTyped S s₃ …`: the heap objects created and the values produced are typed
  in `S`, and the heap stays acyclic.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## List helpers -/

theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM hbs)

theorem mapM_eq_of_forall₂ {α β : Type} {f : α → Option β} {l : List α} {l₁ l₂ : List β}
    (h : l.mapM f = some l₁) (h₂ : List.Forall₂ (fun a b => f a = some b) l l₂) : l₁ = l₂ := by
  have h₁ := forall₂_of_mapM h
  clear h
  induction h₁ generalizing l₂ with
  | nil => cases h₂; rfl
  | cons hb _ ih =>
    cases h₂ with
    | cons hb' hs => rw [hb] at hb'; cases hb'; rw [ih hs]

theorem forall₂_range' {α : Type} {P : Nat → α → Prop} (base : Nat) :
    ∀ {l : List α}, (∀ (i : Nat) (x : α), l[i]? = some x → P (base + i) x) →
      List.Forall₂ P (List.range' base l.length) l
  | [], _ => .nil
  | x :: l, h => by
    simp only [List.length_cons, List.range'_succ]
    refine .cons (by simpa using h 0 x rfl) ?_
    have := forall₂_range' (P := P) (base + 1) (l := l) fun i y hy => by
      have := h (i + 1) y (by simpa using hy)
      rwa [show base + (i + 1) = base + 1 + i by omega] at this
    exact this

theorem ExtendsList.of_prefix {α : Type} {R : α → α → Prop} {l l' : List α} (h : l <+: l')
    (hR : ∀ x ∈ l, R x x) : ExtendsList R l l' := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨by simp, fun i x hx => ⟨x, ?_, hR x (List.mem_of_getElem? hx)⟩⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx

/-! ## Kinds of external addresses -/

def ExternAddr.kind : ExternAddr → Nat
  | .tag _ => 0 | .global _ => 1 | .mem _ => 2 | .table _ => 3 | .func _ => 4

def _root_.Silmaril.Wasm.Validation.CExternType.kind : CExternType → Nat
  | .tag _ => 0 | .global _ => 1 | .mem _ => 2 | .table _ => 3 | .func _ => 4

theorem ExternAddrOk.kind_eq {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : xa.kind = xt.kind := by
  induction h with
  | sub _ _ hs ih => rw [ih]; cases hs <;> rfl
  | _ => rfl

theorem ExternAddrOk.forall₂_tags {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a d => ExternAddrOk s (.tag a) (.tag d))
        (ExternAddr.tags xas) (CExternType.tags xts)
  | [], [], .nil => .nil
  | xa :: xas, xt :: xts, .cons h hs => by
    have hk := h.kind_eq
    have ih := ExternAddrOk.forall₂_tags hs
    cases xa <;> cases xt <;> simp_all [ExternAddr.kind, CExternType.kind, ExternAddr.tags,
      CExternType.tags]

theorem ExternAddrOk.forall₂_globals {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a d => ExternAddrOk s (.global a) (.global d))
        (ExternAddr.globals xas) (CExternType.globals xts)
  | [], [], .nil => .nil
  | xa :: xas, xt :: xts, .cons h hs => by
    have hk := h.kind_eq
    have ih := ExternAddrOk.forall₂_globals hs
    cases xa <;> cases xt <;> simp_all [ExternAddr.kind, CExternType.kind, ExternAddr.globals,
      CExternType.globals]

theorem ExternAddrOk.forall₂_mems {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a d => ExternAddrOk s (.mem a) (.mem d))
        (ExternAddr.mems xas) (CExternType.mems xts)
  | [], [], .nil => .nil
  | xa :: xas, xt :: xts, .cons h hs => by
    have hk := h.kind_eq
    have ih := ExternAddrOk.forall₂_mems hs
    cases xa <;> cases xt <;> simp_all [ExternAddr.kind, CExternType.kind, ExternAddr.mems,
      CExternType.mems]

theorem ExternAddrOk.forall₂_tables {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a d => ExternAddrOk s (.table a) (.table d))
        (ExternAddr.tables xas) (CExternType.tables xts)
  | [], [], .nil => .nil
  | xa :: xas, xt :: xts, .cons h hs => by
    have hk := h.kind_eq
    have ih := ExternAddrOk.forall₂_tables hs
    cases xa <;> cases xt <;> simp_all [ExternAddr.kind, CExternType.kind, ExternAddr.tables,
      CExternType.tables]

theorem ExternAddrOk.forall₂_funcs {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List CExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a d => ExternAddrOk s (.func a) (.func d))
        (ExternAddr.funcs xas) (CExternType.funcs xts)
  | [], [], .nil => .nil
  | xa :: xas, xt :: xts, .cons h hs => by
    have hk := h.kind_eq
    have ih := ExternAddrOk.forall₂_funcs hs
    cases xa <;> cases xt <;> simp_all [ExternAddr.kind, CExternType.kind, ExternAddr.funcs,
      CExternType.funcs]


theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hab⟩
    · exact forall₂_exists_left hs a h

theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab hs, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hab⟩
    · exact forall₂_exists_right hs b h

theorem forall₂_mem_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α} {b : β},
      (b, a) ∈ l₂.zip l₁ → R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons hab hs, a, b, h => by
    rcases List.mem_cons.mp h with e | h
    · cases e; exact hab
    · exact forall₂_mem_zip hs h

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : Nat} {a : α} {b : β},
      l₁[i]? = some a → l₂[i]? = some b → R a b
  | _, _, .nil, _, _, _, h, _ => by cases h
  | _, _, .cons hab hs, 0, a, b, h₁, h₂ => by
    simp at h₁ h₂; subst h₁ h₂; exact hab
  | _, _, .cons _ hs, i + 1, a, b, h₁, h₂ => by
    simp at h₁ h₂; exact forall₂_getElem hs h₁ h₂


/-! ## Validation facts about the allocated types -/

theorem GlobalsOk.types_eq {dts : List DefType} :
    ∀ {C : Context} {gs : List Global} {gts : List CGlobalType}, C.types = dts →
      GlobalsOk C gs gts →
      gs.map (fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll (dts.map .dt)⟩ : CGlobalType)) = gts
  | _, [], [], _, .nil => rfl
  | C, g :: gs, gt :: gts, hT, .cons h hs => by
    have ih := GlobalsOk.types_eq (C := { C with globals := C.globals ++ [gt] }) hT hs
    rw [List.map_cons, ih, h.1]
    simp [Context.closeGlobalType, Context.closeVal, hT]

theorem GlobalsOk.length_eq : ∀ {C : Context} {gs : List Global} {gts : List CGlobalType},
    GlobalsOk C gs gts → gs.length = gts.length
  | _, [], [], .nil => rfl
  | _, _ :: _, _ :: _, .cons _ hs => by simp [GlobalsOk.length_eq hs]

theorem tables_types_eq {C : Context} {dts : List DefType} (hT : C.types = dts)
    {ts : List Table} {tts : List CTableType} (h : List.Forall₂ (TableOk C) ts tts) :
    ts.map (fun t => (⟨t.type.address, t.type.limits,
      (liftRef t.type.element).substAll (dts.map .dt)⟩ : CTableType)) = tts := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    rw [List.map_cons, ih, h.1]
    simp [Context.closeTableType, Context.closeRef, hT]

theorem elems_types_eq {C : Context} {dts : List DefType} (hT : C.types = dts)
    {es : List Elem} {rts : List CRefType} (h : List.Forall₂ (ElemOk C) es rts) :
    es.map (fun e => (liftRef e.type).substAll (dts.map .dt)) = rts := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    rw [List.map_cons, ih, h.1]
    simp [Context.closeRef, hT]

/-- What the allocation proof needs from the evaluation of the initialisers,
against the final store `S`. -/
structure InitTyped (S s₃ : Store H) (gts : List CGlobalType) (tts : List CTableType)
    (rts : List CRefType) (valsG : List Val) (refsT : List Ref) (refsE : List (List Ref)) :
    Prop where
  globals : ∀ gi ∈ s₃.globals, GlobalInstOk S gi
  structs : ∀ si ∈ s₃.structs, StructInstOk S si
  arrays : ∀ ai ∈ s₃.arrays, ArrayInstOk S ai
  acyclic : HeapAcyclic s₃
  valsG : List.Forall₂ (fun v gt => ValOk S v gt.type) valsG gts
  refsT : List.Forall₂ (fun r tt => RefOk S r tt.element) refsT tts
  refsE : List.Forall₂ (fun rs rt => ∀ r ∈ rs, RefOk S r rt) refsE rts
  structsClosed : ∀ si ∈ s₃.structs, TyOk {} si.type
  arraysClosed : ∀ ai ∈ s₃.arrays, TyOk {} ai.type

/-! ## Shapes of the initialiser evaluations -/

theorem EvalShape.of_allocGlobal (s : Store H) (g : CGlobalType) (v : Val) :
    EvalShape s (allocGlobal s g v).1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_append _ _, List.prefix_refl _,
    List.prefix_refl _⟩

theorem EvalGlobals.shape {P : Profile} {host : HostSemantics H} :
    ∀ {s : Store H} {f : Frame} {gts : List CGlobalType} {es : List Expr} {s'' : Store H}
      {f'' : Frame} {vs : List Val}, EvalGlobals P host s f gts es s'' f'' vs →
      (∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      EvalShape s s'' ∧ f''.module.types = f.module.types ∧ f''.module.funcs = f.module.funcs
  | _, _, _, _, _, _, _, .nil, _ => ⟨EvalShape.refl _, rfl, rfl⟩
  | _, _, _, _, _, _, _, .cons he hs, hc => by
    obtain ⟨hsh₁, rfl, -⟩ := EvalExpr.const_shape he (hc _ (by simp))
    obtain ⟨hsh₂, ht, hf⟩ := EvalGlobals.shape hs (fun e he => hc e (by simp [he]))
    exact ⟨(hsh₁.trans (EvalShape.of_allocGlobal _ _ _)).trans hsh₂, ht, hf⟩

theorem EvalExprs.shape {P : Profile} {host : HostSemantics H} :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s'' : Store H} {f'' : Frame} {rs : List Ref},
      EvalExprs P host s f es s'' f'' rs → (∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      EvalShape s s'' ∧ f'' = f ∧ s''.globals = s.globals
  | _, _, _, _, _, _, .nil, _ => ⟨EvalShape.refl _, rfl, rfl⟩
  | _, _, _, _, _, _, .cons he hs, hc => by
    obtain ⟨hsh₁, rfl, hg₁⟩ := EvalExpr.const_shape he (hc _ (by simp))
    obtain ⟨hsh₂, rfl, hg₂⟩ := EvalExprs.shape hs (fun e he => hc e (by simp [he]))
    exact ⟨hsh₁.trans hsh₂, rfl, hg₂.trans hg₁⟩

theorem EvalExprss.shape {P : Profile} {host : HostSemantics H} :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s'' : Store H} {f'' : Frame}
      {rss : List (List Ref)}, EvalExprss P host s f ess s'' f'' rss →
      (∀ es ∈ ess, ∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      EvalShape s s'' ∧ f'' = f ∧ s''.globals = s.globals
  | _, _, _, _, _, _, .nil, _ => ⟨EvalShape.refl _, rfl, rfl⟩
  | _, _, _, _, _, _, .cons he hs, hc => by
    obtain ⟨hsh₁, rfl, hg₁⟩ := EvalExprs.shape he (hc _ (by simp))
    obtain ⟨hsh₂, rfl, hg₂⟩ := EvalExprss.shape hs (fun e he => hc e (by simp [he]))
    exact ⟨hsh₁.trans hsh₂, rfl, hg₂.trans hg₁⟩

/-! ## Invariant maintenance -/

theorem ConstCtxOk.of {C : Context} (hT : ∀ d ∈ C.types, TyOk {} d) (hcl : ∀ d ∈ C.types, d.Closed)
    (hrecs : C.recs = []) (htags : ∀ d ∈ C.tags, TyOk C.toTypeCtx d)
    (hglobals : ∀ g ∈ C.globals, TyOk C.toTypeCtx g.type)
    (htables : ∀ t ∈ C.tables, TyOk C.toTypeCtx t.element)
    (hfuncs : ∀ d ∈ C.funcs, TyOk C.toTypeCtx d) (hlocals : C.locals = [])
    (hlabels : C.labels = []) (hret : C.return_ = none)
    (helems : ∀ rt ∈ C.elems, TyOk C.toTypeCtx rt) : ConstCtxOk C :=
  ⟨⟨fun d hd => ⟨hcl d hd, TyOk.of_empty _ (hT d hd)⟩, htags, hglobals, htables, hfuncs,
    by simp [hlocals], by simp [hlabels], by simp [hret], helems⟩, hlocals, hrecs, hT⟩

theorem ConstCtxOk.addGlobal {C : Context} (hC : ConstCtxOk C) {gt : CGlobalType}
    (hg : TyOk C.toTypeCtx gt.type) : ConstCtxOk { C with globals := C.globals ++ [gt] } := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hl, hr, hT⟩ := hC
  refine ⟨⟨h1, h2, fun g hg' => ?_, h4, h5, h6, h7, h8, h9⟩, hl, hr, hT⟩
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact h3 g hg'
  · simp at hg'; subst hg'; exact hg

theorem HeapOk.of_allocGlobal {S s : Store H} (h : HeapOk S s) (g : CGlobalType) (v : Val) :
    HeapOk S (allocGlobal s g v).1 := by
  obtain ⟨h1, h2, ⟨i1, i2, i3⟩, h4, h5, h6⟩ := h
  have m := Nat.le_refl s.structs.length
  have m' := Nat.le_refl s.arrays.length
  have m'' := Nat.le_refl s.exns.length
  refine ⟨h1, h2, ⟨fun si hsi fv hfv => ?_, fun ai hai fv hfv => ?_, fun e he w hw => ?_⟩,
    ⟨?_, ?_, ?_⟩, h5, h6⟩
  · exact FieldVal.In.mono (s' := (allocGlobal s g v).1) m m' m'' (i1 si hsi fv hfv)
  · exact FieldVal.In.mono (s' := (allocGlobal s g v).1) m m' m'' (i2 ai hai fv hfv)
  · exact Val.In.mono (s' := (allocGlobal s g v).1) m m' m'' (i3 e he w hw)
  · intro a ha hr
    exact h4.1 a ha (TM.immutReachable_transfer (s := s) (s' := (allocGlobal s g v).1) rfl rfl rfl hr)
  · intro a ha hr
    exact h4.2.1 a ha (TM.immutReachable_transfer (s := s) (s' := (allocGlobal s g v).1) rfl rfl rfl hr)
  · intro a ha hr
    exact h4.2.2 a ha (TM.immutReachable_transfer (s := s) (s' := (allocGlobal s g v).1) rfl rfl rfl hr)

theorem FrameAgree.congr {S s : Store H} {C C' : Context} {f : Frame} (h : FrameAgree S s C f)
    (ht : C'.types = C.types) (hf : C'.funcs = C.funcs) (hg : C'.globals <+: C.globals) :
    FrameAgree S s C' f := by
  refine ⟨h.types.trans ht.symm, fun x d hx => h.funcs x d (hf ▸ hx), fun x gt hx hc => ?_⟩
  obtain ⟨l, hl⟩ := hg
  refine h.globals x gt ?_ hc
  rw [← hl, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx

theorem FrameAgree.of_allocGlobal {S s : Store H} {C : Context} {f : Frame} (h : FrameAgree S s C f)
    (hlen : C.globals.length = f.module.globals.length) {gt : CGlobalType} {v : Val}
    (hv : ValOk S v gt.type) (hin : v.In s) (ht : TyOk {} gt.type) :
    FrameAgree S (allocGlobal s gt v).1 { C with globals := C.globals ++ [gt] }
      { f with module := { f.module with globals := f.module.globals ++ [(allocGlobal s gt v).2] } } := by
  refine ⟨h.types, h.funcs, fun x g hx hc => ?_⟩
  simp only at hx ⊢
  by_cases hlt : x < C.globals.length
  · rw [List.getElem?_append_left hlt] at hx
    obtain ⟨htok, a, gi, ha, hgi, hval, hin'⟩ := h.globals x g hx hc
    refine ⟨htok, a, gi, ?_, ?_, hval,
      Val.In.mono (s := s) (s' := (allocGlobal s gt v).1) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) hin'⟩
    · rw [List.getElem?_append_left (by omega)]; exact ha
    · simp only [allocGlobal]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hgi).1]; exact hgi
  · have hx' := hx
    rw [List.getElem?_append_right (by omega)] at hx'
    have hx0 : x - C.globals.length = 0 := by
      have := (List.getElem?_eq_some_iff.mp hx').1; simp at this; omega
    have hxe : x = f.module.globals.length := by omega
    rw [hx0] at hx'
    simp at hx'
    subst hx' hxe
    refine ⟨ht, s.globals.length, ⟨gt, v⟩, ?_, ?_, hv,
      Val.In.mono (s := s) (s' := (allocGlobal s gt v).1) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) hin⟩
    · simp [allocGlobal]
    · simp [allocGlobal]

theorem HeapOk.of_storeOk {S s : Store H} (hs : StoreOk s) (he : Extend s S) : HeapOk S s := by
  refine ⟨fun si hsi => ?_, fun ai hai => ?_, ⟨?_, ?_, ?_⟩, ⟨hs.acyclicStructs, hs.acyclicArrays,
    hs.acyclicExns⟩, hs.structsClosed, hs.arraysClosed⟩
  · obtain ⟨fs, hexp, hf⟩ := hs.structs si hsi
    exact ⟨fs, hexp, hf.imp fun _ _ h => h.extend he⟩
  · obtain ⟨ft, hexp, hf⟩ := hs.arrays ai hai
    exact ⟨ft, hexp, fun fv hfv => (hf fv hfv).extend he⟩
  · intro si hsi fv hfv
    obtain ⟨fs, -, hf⟩ := hs.structs si hsi
    obtain ⟨t, -, ht⟩ := forall₂_mem_left' hf fv hfv
    exact ht.in
  · intro ai hai fv hfv
    obtain ⟨ft, -, hf⟩ := hs.arrays ai hai
    exact (hf fv hfv).in
  · intro e he' v hv
    obtain ⟨ti, ts, -, -, hvs⟩ := hs.exns e he'
    obtain ⟨t, -, ht⟩ := forall₂_mem_left' hvs v hv
    exact ht.in

/-- An imported function address has a function reference of the declared type. -/
theorem ExternAddrOk.func_refOk {S : Store H} {a : Nat} {xt : CExternType}
    (h : ExternAddrOk S (.func a) xt) : ∀ {d : DefType}, xt = .func d →
      RefOk S (.func a) (.ref false (.defHeap d)) := by
  generalize e : ExternAddr.func a = xa at h
  induction h with
  | func hf => intro d hd; cases e; cases hd; exact .func hf
  | sub _ hok hs ih =>
    intro d hd
    subst hd
    cases hs with
    | func hsub =>
      cases hok with
      | func hd _ =>
        exact .sub (ih e rfl) (.ref (.use (.dt hd))) (.refNonNull (.defDef hsub))
  | _ => intro d hd; cases e

/-- An imported constant global holds a value of the declared type. -/
theorem ExternAddrOk.global_val_ce {s : Store H} (hs : StoreOk s) {a : Nat} {xt : CExternType}
    (h : ExternAddrOk s (.global a) xt) : ∀ {gt : CGlobalType},
      xt = .global gt → gt.mutability = .const →
      ∃ gi, s.globals[a]? = some gi ∧ ValOk s gi.value gt.type := by
  generalize e : ExternAddr.global a = xa at h
  induction h with
  | global hg =>
    intro gt hgt _
    cases e; cases hgt
    exact ⟨_, hg, (hs.globals _ (List.mem_of_getElem? hg)).2⟩
  | sub _ hok hs' ih =>
    intro gt hgt hc
    subst hgt
    cases hs' with
    | global hg =>
      cases hg with
      | const hsub =>
        obtain ⟨gi, hgi, hv⟩ := ih e rfl rfl
        cases hok with
        | global hgt => exact ⟨gi, hgi, hv.sub_empty_ce hsub hgt⟩
      | var => cases hc
  | _ => intro gt hgt _; cases e

/-- Facts about the imported external types of a valid module. -/
theorem imports_funcs_mem {dts : List DefType} :
    ∀ {ims : List Import} {xts : List CExternType}, List.Forall₂ (ImportOk { types := dts }) ims xts →
      ∀ d ∈ CExternType.funcs xts, d ∈ dts
  | [], [], .nil, _, h => by cases h
  | im :: ims, xt :: xts, .cons h hs, d, hd => by
    have ih := imports_funcs_mem hs
    obtain ⟨hc, -⟩ := h
    cases xt with
    | func d' =>
      simp only [CExternType.funcs, List.mem_cons] at hd
      rcases hd with rfl | hd
      · cases hi : im.type with
        | func x =>
          rw [hi] at hc
          simp only [Context.closeExtern?, Context.type?, Option.map_eq_some_iff] at hc
          obtain ⟨d'', hd'', e⟩ := hc
          injection e with e
          subst e
          exact List.mem_of_getElem? hd''
        | _ => rw [hi] at hc; simp [Context.closeExtern?] at hc
      · exact ih d hd
    | _ => exact ih d (by simpa [CExternType.funcs] using hd)

theorem imports_globals_ok {dts : List DefType} (hdts : ∀ d ∈ dts, TyOk {} d) :
    ∀ {ims : List Import} {xts : List CExternType}, List.Forall₂ (ImportOk { types := dts }) ims xts →
      ∀ gt ∈ CExternType.globals xts, TyOk {} gt.type
  | [], [], .nil, _, h => by cases h
  | im :: ims, xt :: xts, .cons h hs, gt, hgt => by
    have ih := imports_globals_ok hdts hs
    obtain ⟨hc, hok⟩ := h
    cases xt with
    | global g' =>
      simp only [CExternType.globals, List.mem_cons] at hgt
      rcases hgt with rfl | hgt
      · cases hi : im.type with
        | global g =>
          rw [hi] at hc
          simp only [Context.closeExtern?, Option.some.injEq, CExternType.global.injEq] at hc
          subst hc
          cases hok with
          | global h' =>
            simp only [GlobalTypeOk, Context.closeGlobalType, Context.closeVal] at h' ⊢
            exact TyOk.closeVal_empty hdts rfl h'
        | _ => rw [hi] at hc; simp [Context.closeExtern?] at hc
      · exact ih gt hgt
    | _ => exact ih gt (by simpa [CExternType.globals] using hgt)

theorem imports_tags_ok {Δ : TypeCtx} {Δ' : Context} :
    ∀ {ims : List Import} {xts : List CExternType}, List.Forall₂ (ImportOk Δ') ims xts →
      Δ'.toTypeCtx = Δ → ∀ d ∈ CExternType.tags xts, TyOk Δ d
  | [], [], .nil, _, _, h => by cases h
  | _ :: _, xt :: xts, .cons h hs, e, d, hd => by
    have ih := imports_tags_ok hs e
    cases xt with
    | tag d' =>
      simp only [CExternType.tags, List.mem_cons] at hd
      rcases hd with rfl | hd
      · cases h.2 with | tag h' => rw [← e]; exact h'.1
      · exact ih d hd
    | _ => exact ih d (by simpa [CExternType.tags] using hd)

theorem imports_globals_ty {Δ : TypeCtx} {Δ' : Context} :
    ∀ {ims : List Import} {xts : List CExternType}, List.Forall₂ (ImportOk Δ') ims xts →
      Δ'.toTypeCtx = Δ → ∀ g ∈ CExternType.globals xts, TyOk Δ g.type
  | [], [], .nil, _, _, h => by cases h
  | _ :: _, xt :: xts, .cons h hs, e, g, hg => by
    have ih := imports_globals_ty hs e
    cases xt with
    | global g' =>
      simp only [CExternType.globals, List.mem_cons] at hg
      rcases hg with rfl | hg
      · cases h.2 with | global h' => rw [← e]; exact h'
      · exact ih g hg
    | _ => exact ih g (by simpa [CExternType.globals] using hg)

theorem imports_tables_ty {Δ : TypeCtx} {Δ' : Context} :
    ∀ {ims : List Import} {xts : List CExternType}, List.Forall₂ (ImportOk Δ') ims xts →
      Δ'.toTypeCtx = Δ → ∀ t ∈ CExternType.tables xts, TyOk Δ t.element
  | [], [], .nil, _, _, h => by cases h
  | _ :: _, xt :: xts, .cons h hs, e, t, ht => by
    have ih := imports_tables_ty hs e
    cases xt with
    | table t' =>
      simp only [CExternType.tables, List.mem_cons] at ht
      rcases ht with rfl | ht
      · cases h.2 with | table h' => rw [← e]; exact h'.2
      · exact ih t ht
    | _ => exact ih t (by simpa [CExternType.tables] using ht)


/-! ## Typed evaluation of the initialisers -/

theorem GlobalsOk.const : ∀ {C : Context} {gs : List Global} {gts : List CGlobalType},
    GlobalsOk C gs gts → ∀ e ∈ gs.map Global.init, ∀ i ∈ e, i.IsConstI
  | _, [], [], .nil, _, h => by cases h
  | _, _ :: _, _ :: _, .cons hg hs, e, he => by
    simp only [List.map_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact fun i hi => (hg.2.2.const i hi).isConstI
    · exact GlobalsOk.const hs e he

theorem GlobalsOk.tyOk : ∀ {C : Context} {gs : List Global} {gts : List CGlobalType},
    GlobalsOk C gs gts → ∀ gt ∈ gts, TyOk C.toTypeCtx gt.type
  | _, [], [], .nil, _, h => by cases h
  | C, _ :: _, _ :: _, .cons hg hs, gt, hgt => by
    rcases List.mem_cons.mp hgt with rfl | hgt
    · exact hg.2.1
    · exact GlobalsOk.tyOk (C := { C with globals := C.globals ++ [_] }) hs gt hgt

theorem GlobalsOk.tyOk_empty {dts : List DefType} (hdts : ∀ d ∈ dts, TyOk {} d) :
    ∀ {C : Context} {gs : List Global} {gts : List CGlobalType}, C.types = dts →
      GlobalsOk C gs gts → ∀ gt ∈ gts, TyOk {} gt.type
  | _, [], [], _, .nil, _, h => by cases h
  | C, g :: gs, gt :: gts, hT, .cons hg hs, gt', hgt' => by
    rcases List.mem_cons.mp hgt' with rfl | hgt'
    · have h2 : TyOk C.toTypeCtx gt'.type := hg.2.1
      rw [hg.1] at h2 ⊢
      simp only [Context.closeGlobalType, Context.closeVal, hT] at h2 ⊢
      exact TyOk.closeVal_empty hdts (Δ := C.toTypeCtx) hT h2
    · exact GlobalsOk.tyOk_empty hdts (C := { C with globals := C.globals ++ [gt] }) hT hs gt' hgt'

theorem forall₂_exprOkConst_const {C : Context} :
    ∀ {es : List Expr} {ts : List CRefType},
      List.Forall₂ (fun e rt => ExprOkConst C e (.refv rt)) es ts → ∀ e ∈ es, ∀ i ∈ e, i.IsConstI
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h hs, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact fun i hi => (h.const i hi).isConstI
    · exact forall₂_exprOkConst_const hs e he

theorem evalGlobals_ok {P : Profile} {host : HostSemantics H} {S : Store H} :
    ∀ {s : Store H} {f : Frame} {gts' : List CGlobalType} {es : List Expr} {s'' : Store H}
      {f'' : Frame} {vs : List Val}, EvalGlobals P host s f gts' es s'' f'' vs →
      ∀ {C : Context} {gs : List Global} {gts : List CGlobalType}, GlobalsOk C gs gts →
      gts' = gts → es = gs.map Global.init → ConstCtxOk C →
      C.globals.length = f.module.globals.length → (∀ gt ∈ gts, TyOk {} gt.type) →
      HeapOk S s → FrameAgree S s C f → s''.structs <+: S.structs → s''.arrays <+: S.arrays →
      EvalShape s s'' ∧ f''.module.types = f.module.types ∧ f''.module.funcs = f.module.funcs ∧
      HeapOk S s'' ∧ FrameAgree S s'' { C with globals := C.globals ++ gts } f'' ∧
      List.Forall₂ (fun v gt => ValOk S v gt.type) vs gts ∧
      (∀ gi ∈ s''.globals, gi ∈ s.globals ∨ GlobalInstOk S gi)
  | _, _, _, _, _, _, _, .nil, C, gs, gts, hg, e1, e2, _, _, _, hheap, hfa, _, _ => by
    cases gs with
    | cons => simp at e2
    | nil =>
      cases hg
      exact ⟨EvalShape.refl _, rfl, rfl, hheap, by simpa using hfa, .nil, fun gi h => .inl h⟩
  | _, _, _, _, _, _, _, @EvalGlobals.cons _ _ _ s s' s'' f f' f'' g gs' e es v vs he hs,
      C, gs, gts, hg, e1, e2, hC, hlen, htg, hheap, hfa, hps, hpa => by
    cases gs with
    | nil => simp at e2
    | cons g0 gs₀ =>
      simp only [List.map_cons, List.cons.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      cases hg with
      | @cons _ _ _ gt gts₀ hg0 hgs =>
        simp only [List.cons.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have hconst : ∀ i ∈ g0.init, i.IsConstI := fun i hi => (hg0.2.2.const i hi).isConstI
        obtain ⟨hshR, -, -⟩ := EvalGlobals.shape hs (GlobalsOk.const hgs)
        have hps' : s'.structs <+: S.structs := hshR.structs.trans hps
        have hpa' : s'.arrays <+: S.arrays := hshR.arrays.trans hpa
        have hgt : TyOk {} g.type := htg g (by simp)
        obtain ⟨hf, hsh, hheap', hfa', v', hvv, hval, hin⟩ :=
          EvalExpr.const_ok hC hgt he hg0.2.2 hheap hfa hps' hpa'
        simp only [List.cons.injEq, and_true] at hvv
        subst hvv hf
        obtain ⟨-, -, hglob⟩ := EvalExpr.const_shape he hconst
        have hC₁ := hC.addGlobal (gt := g) hg0.2.1
        have hfa₁ := hfa'.of_allocGlobal hlen hval hin hgt
        have hheap₁ := hheap'.of_allocGlobal g v
        obtain ⟨hsh', ht', hf', hheap'', hfa'', hvs, hgl⟩ :=
          evalGlobals_ok hs hgs rfl rfl hC₁ (by simp [hlen])
            (fun gt h => htg gt (by simp [h])) hheap₁ hfa₁ hps hpa
        refine ⟨hsh.trans ((EvalShape.of_allocGlobal _ _ _).trans hsh'), ht', hf', hheap'', ?_,
          .cons hval hvs, ?_⟩
        · simpa [List.append_assoc] using hfa''
        · intro gi hgi
          rcases hgl gi hgi with h | h
          · simp only [allocGlobal, hglob, List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact .inl h
            · exact .inr ⟨hgt, hval⟩
          · exact .inr h

theorem evalExprs_ok {P : Profile} {host : HostSemantics H} {S : Store H} :
    ∀ {s : Store H} {f : Frame} {es : List Expr} {s'' : Store H} {f'' : Frame} {rs : List Ref},
      EvalExprs P host s f es s'' f'' rs → ∀ {C : Context} {ts : List CRefType},
      List.Forall₂ (fun e rt => ExprOkConst C e (.refv rt)) es ts → ConstCtxOk C →
      (∀ rt ∈ ts, TyOk {} rt) → HeapOk S s → FrameAgree S s C f →
      s''.structs <+: S.structs → s''.arrays <+: S.arrays →
      f'' = f ∧ EvalShape s s'' ∧ HeapOk S s'' ∧ FrameAgree S s'' C f ∧
        List.Forall₂ (RefOk S) rs ts
  | _, _, _, _, _, _, .nil, C, ts, hty, _, _, hheap, hfa, _, _ => by
    cases hty; exact ⟨rfl, EvalShape.refl _, hheap, hfa, .nil⟩
  | _, _, _, _, _, _, .cons he hs, C, ts, hty, hC, hts, hheap, hfa, hps, hpa => by
    cases hty with
    | @cons _ rt _ ts' h1 hrest =>
      obtain ⟨hshR, -, -⟩ := EvalExprs.shape hs (forall₂_exprOkConst_const hrest)
      obtain ⟨hf, hsh, hheap', hfa', v, hvv, hval, -⟩ :=
        EvalExpr.const_ok hC (.refv (hts rt (by simp))) he h1 hheap hfa
          (hshR.structs.trans hps) (hshR.arrays.trans hpa)
      simp only [List.cons.injEq, and_true] at hvv
      subst hvv hf
      cases hval with
      | ref hr =>
      obtain ⟨hf', hsh', hheap'', hfa'', hrs⟩ :=
        evalExprs_ok hs hrest hC (fun rt h => hts rt (by simp [h])) hheap' hfa' hps hpa
      exact ⟨hf', hsh.trans hsh', hheap'', hfa'', .cons hr hrs⟩

theorem forall₂_replicate_of_forall {α β : Type} {R : α → β → Prop} {b : β} :
    ∀ {l : List α}, (∀ a ∈ l, R a b) → List.Forall₂ R l (List.replicate l.length b)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_replicate_of_forall fun x hx => h x (by simp [hx]))

theorem evalExprss_ok {P : Profile} {host : HostSemantics H} {S : Store H} :
    ∀ {s : Store H} {f : Frame} {ess : List (List Expr)} {s'' : Store H} {f'' : Frame}
      {rss : List (List Ref)}, EvalExprss P host s f ess s'' f'' rss →
      ∀ {C : Context} {rts : List CRefType},
      List.Forall₂ (fun es rt => ∀ e ∈ es, ExprOkConst C e (.refv rt)) ess rts → ConstCtxOk C →
      (∀ rt ∈ rts, TyOk {} rt) → HeapOk S s → FrameAgree S s C f →
      s''.structs <+: S.structs → s''.arrays <+: S.arrays →
      f'' = f ∧ EvalShape s s'' ∧ HeapOk S s'' ∧ FrameAgree S s'' C f ∧
        List.Forall₂ (fun rs rt => ∀ r ∈ rs, RefOk S r rt) rss rts
  | _, _, _, _, _, _, .nil, C, ts, hty, _, _, hheap, hfa, _, _ => by
    cases hty; exact ⟨rfl, EvalShape.refl _, hheap, hfa, .nil⟩
  | _, _, _, _, _, _, .cons he hs, C, ts, hty, hC, hts, hheap, hfa, hps, hpa => by
    cases hty with
    | @cons es rt _ ts' h1 hrest =>
      have hrep := forall₂_replicate_of_forall (R := fun e rt => ExprOkConst C e (.refv rt)) h1
      obtain ⟨hshR, -, -⟩ := EvalExprss.shape hs (fun es' hes' e' he' i hi => by
        obtain ⟨rt', -, h'⟩ := forall₂_mem_left' hrest es' hes'
        exact ((h' e' he').const i hi).isConstI)
      obtain ⟨hf, hsh, hheap', hfa', hrs⟩ :=
        evalExprs_ok he hrep hC (fun rt' h => by
          rw [(List.mem_replicate.mp h).2]; exact hts rt (by simp)) hheap hfa
          (hshR.structs.trans hps) (hshR.arrays.trans hpa)
      subst hf
      obtain ⟨hf', hsh', hheap'', hfa'', hrss⟩ :=
        evalExprss_ok hs hrest hC (fun rt h => hts rt (by simp [h])) hheap' hfa' hps hpa
      exact ⟨hf', hsh.trans hsh', hheap'', hfa'',
        .cons (fun r hr => forall₂_replicate_right hrs r hr) hrss⟩


/-- **Evaluation of the initialisers of a valid module.** -/
theorem initEval_ok {P : Profile} {host : HostSemantics H} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s)
    {dts : List DefType} {xtI : List CExternType} {jts : List DefType}
    {gts : List CGlobalType} {tts : List CTableType} {fdts : List DefType}
    {rts : List CRefType} {C' C : Context}
    (htypes : TypesOk {} m.types dts)
    (himports : List.Forall₂ (ImportOk { types := dts }) m.imports xtI)
    (hC' : C' = { types := dts, globals := CExternType.globals xtI,
                  funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m })
    (hC : C = { C' with
                tags := CExternType.tags xtI ++ jts, globals := C'.globals ++ gts,
                mems := CExternType.mems xtI ++ m.memories,
                tables := CExternType.tables xtI ++ tts,
                datas := m.data.map fun _ => (), elems := rts })
    (htags : List.Forall₂ (TagOk C') m.tags jts)
    (hglobals : GlobalsOk C' m.globals gts)
    (htables : List.Forall₂ (TableOk C') m.tables tts)
    (hfuncs : List.Forall₂ (FuncOk C) m.funcs fdts)
    (helems : List.Forall₂ (ElemOk C) m.elems rts)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ s₂ s₃ : Store H} {f₁ f₂ f₃ : Frame} {valsG : List Val} {refsT : List Ref}
    {refsE : List (List Ref)}
    (hg : EvalGlobals P host s ⟨[], ModuleInst.initial s m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
      (m.globals.map Global.init) s₁ f₁ valsG)
    (ht : EvalExprs P host s₁ f₁ (m.tables.map Table.init) s₂ f₂ refsT)
    (he : EvalExprss P host s₂ f₂ (m.elems.map Elem.init) s₃ f₃ refsE) :
    EvalShape s s₃ ∧
      ∀ S : Store H, s₃.globals <+: S.globals → s₃.structs <+: S.structs →
        s₃.arrays <+: S.arrays → Extend s S →
        (∀ i fd, fdts[i]? = some fd →
          ∃ fi, S.funcs[s.funcs.length + i]? = some fi ∧ fi.type = fd) →
        InitTyped S s₃ gts tts rts valsG refsT refsE := by
  have hdts : ∀ d ∈ dts, TyOk {} d := TypesOk.tyOk_empty htypes
  have hcl : ∀ d ∈ dts, d.Closed := TypesOk.closed (by simp) htypes
  have hallocT : allocTypes m.types = dts := allocTypes_eq htypes
  have hC'T : C'.types = dts := by subst hC'; rfl
  have hCT : C.types = dts := by subst hC hC'; rfl
  have hgtypes : (m.globals.map fun g => (⟨g.type.mutability,
      (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)) = gts := by
    rw [hallocT]; exact GlobalsOk.types_eq hC'T hglobals
  -- constness of the initialisers
  have hconstT : ∀ e ∈ m.tables.map Table.init, ∀ i ∈ e, i.IsConstI := by
    intro e he i hi
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    obtain ⟨tt, -, h⟩ := forall₂_mem_left' htables t ht
    exact (h.2.2.const i hi).isConstI
  have hconstE : ∀ es ∈ m.elems.map Elem.init, ∀ e ∈ es, ∀ i ∈ e, i.IsConstI := by
    intro es hes e he i hi
    obtain ⟨el, hel, rfl⟩ := List.mem_map.mp hes
    obtain ⟨rt, -, h⟩ := forall₂_mem_left' helems el hel
    exact ((h.2.2.1 e he).const i hi).isConstI
  obtain ⟨hsh₁, hft₁, hff₁⟩ := EvalGlobals.shape hg (GlobalsOk.const hglobals)
  obtain ⟨hsh₂, hf₂, hg₂⟩ := EvalExprs.shape ht hconstT
  obtain ⟨hsh₃, hf₃, hg₃⟩ := EvalExprss.shape he hconstE
  refine ⟨(hsh₁.trans hsh₂).trans hsh₃, fun S hgS hsS haS hext hfS => ?_⟩
  subst f₂; subst f₃
  -- the typing contexts
  have hfdts : ∀ d ∈ fdts, d ∈ dts := by
    intro d hd
    obtain ⟨fn, -, hfn⟩ := forall₂_mem_right' hfuncs d hd
    cases hfn with
    | mk hd' _ _ _ =>
      have h1 : C.types[fn.type.toNat]? = some d := hd'
      rw [hCT] at h1
      exact List.mem_of_getElem? h1
  have hfuncsTy : ∀ d ∈ CExternType.funcs xtI ++ fdts, d ∈ dts := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact imports_funcs_mem himports d hd
    · exact hfdts d hd
  have hgts : ∀ gt ∈ gts, TyOk {} gt.type := GlobalsOk.tyOk_empty hdts hC'T hglobals
  have htts : ∀ tt ∈ tts, TyOk {} tt.element := by
    intro tt htt
    obtain ⟨t, -, ht'⟩ := forall₂_mem_right' htables tt htt
    have h3 := ht'.2.1.2
    rw [ht'.1] at h3 ⊢
    simp only [Context.closeTableType, Context.closeRef, hC'T] at h3 ⊢
    exact TyOk.closeRef_empty hdts hC'T h3
  have hrts : ∀ rt ∈ rts, TyOk {} rt := by
    intro rt hrt
    obtain ⟨e, -, he'⟩ := forall₂_mem_right' helems rt hrt
    have h2 := he'.2.1
    rw [he'.1] at h2 ⊢
    simp only [Context.closeRef, hCT] at h2 ⊢
    exact TyOk.closeRef_empty hdts hCT h2
  have hC'ok : ConstCtxOk C' := by
    subst hC'
    refine ConstCtxOk.of hdts hcl rfl (by simp) (imports_globals_ty himports rfl) (by simp)
      (fun d hd => TyOk.of_empty _ (hdts d (hfuncsTy d hd))) rfl rfl rfl (by simp)
  have hCok : ConstCtxOk C := by
    subst hC hC'
    refine ConstCtxOk.of hdts hcl rfl ?_ ?_ ?_ (fun d hd => TyOk.of_empty _ (hdts d (hfuncsTy d hd)))
      rfl rfl rfl (fun rt hrt => TyOk.of_empty _ (hrts rt (by simpa using hrt)))
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact imports_tags_ok himports rfl d hd
      · obtain ⟨x, -, hx⟩ := forall₂_mem_right' htags d hd
        exact hx.2.1
    · intro g hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact imports_globals_ty himports rfl g hg'
      · exact GlobalsOk.tyOk hglobals g hg'
    · intro t ht'
      rcases List.mem_append.mp ht' with ht' | ht'
      · exact imports_tables_ty himports rfl t ht'
      · obtain ⟨tb, -, htb⟩ := forall₂_mem_right' htables t ht'
        exact htb.2.1.2
  -- the initial frame
  have hheap₀ : HeapOk S s := HeapOk.of_storeOk hs hext
  have hflen := (ExternAddrOk.forall₂_funcs hxas).length_eq
  have hglen := (ExternAddrOk.forall₂_globals hxas).length_eq
  have hmflen : m.funcs.length = fdts.length := hfuncs.length_eq
  have hfa₀ : FrameAgree S s C' ⟨[], ModuleInst.initial s m xas⟩ := by
    refine ⟨by simp [ModuleInst.initial, hallocT, hC'T], fun x d hx => ?_, fun x gt hx hc => ?_⟩
    · have hC'F : C'.funcs = CExternType.funcs xtI ++ fdts := by subst hC'; rfl
      rw [hC'F] at hx
      refine ⟨hdts d (hfuncsTy d (List.mem_of_getElem? hx)), ?_⟩
      simp only [ModuleInst.initial]
      by_cases hlt : x < (CExternType.funcs xtI).length
      · rw [List.getElem?_append_left hlt] at hx
        obtain ⟨a, ha⟩ : ∃ a, (ExternAddr.funcs xas)[x]? = some a :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        refine ⟨a, by rw [List.getElem?_append_left (by omega)]; exact ha, ?_⟩
        have hxa := forall₂_getElem (ExternAddrOk.forall₂_funcs hxas) ha hx
        exact (hxa.extend hs hext).func_refOk rfl
      · rw [List.getElem?_append_right (by omega)] at hx
        have hj : x - (CExternType.funcs xtI).length < fdts.length :=
          (List.getElem?_eq_some_iff.mp hx).1
        obtain ⟨fi, hfi, hty⟩ := hfS _ d hx
        refine ⟨s.funcs.length + (x - (CExternType.funcs xtI).length), ?_, ?_⟩
        · rw [List.getElem?_append_right (by omega)]
          simp [hflen, hmflen, hj]
        · have := RefOk.func (s := S) hfi
          rwa [hty] at this
    · have hC'G : C'.globals = CExternType.globals xtI := by subst hC'; rfl
      rw [hC'G] at hx
      refine ⟨imports_globals_ok hdts himports gt (List.mem_of_getElem? hx), ?_⟩
      obtain ⟨a, ha⟩ : ∃ a, (ExternAddr.globals xas)[x]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by
          have := (List.getElem?_eq_some_iff.mp hx).1; omega)⟩
      have hxa := forall₂_getElem (ExternAddrOk.forall₂_globals hxas) ha hx
      obtain ⟨gi, hgi, hv⟩ := hxa.global_val_ce hs rfl hc
      exact ⟨a, gi, by simpa [ModuleInst.initial] using ha, hgi, hv.extend hext, hv.in⟩
  -- the globals
  have hps₁ : s₁.structs <+: S.structs := (hsh₂.trans hsh₃).structs.trans hsS
  have hpa₁ : s₁.arrays <+: S.arrays := (hsh₂.trans hsh₃).arrays.trans haS
  obtain ⟨-, hft, hff, hheap₁, hfa₁, hvals, hgl⟩ :=
    evalGlobals_ok (S := S) hg hglobals hgtypes rfl hC'ok
      (by subst hC'; simpa [ModuleInst.initial] using hglen.symm) hgts hheap₀ hfa₀ hps₁ hpa₁
  -- the tables
  have hfaT : FrameAgree S s₁ C' f₁ :=
    hfa₁.congr (C' := C') rfl rfl (List.prefix_append _ _)
  have htyT : List.Forall₂ (fun e rt => ExprOkConst C' e (.refv rt)) (m.tables.map Table.init)
      (tts.map (·.element)) :=
    List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (htables.imp fun _ _ h => h.2.2))
  obtain ⟨-, -, hheap₂, -, hrefsT⟩ :=
    evalExprs_ok (S := S) ht htyT hC'ok (fun rt h => by
      obtain ⟨tt, htt, rfl⟩ := List.mem_map.mp h; exact htts tt htt) hheap₁ hfaT
      (hsh₃.structs.trans hsS) (hsh₃.arrays.trans haS)
  -- the element segments
  have hfaE : FrameAgree S s₂ C f₁ := by
    refine (hfa₁.of_shape hsh₂).congr ?_ ?_ ?_
    · rw [hCT]; subst hC'; rfl
    · subst hC hC'; rfl
    · subst hC; exact List.prefix_refl _
  have htyE : List.Forall₂ (fun es rt => ∀ e ∈ es, ExprOkConst C e (.refv rt))
      (m.elems.map Elem.init) rts :=
    List.forall₂_map_left_iff.mpr (helems.imp fun _ _ h => h.2.2.1)
  obtain ⟨-, -, hheap₃, -, hrefsE⟩ :=
    evalExprss_ok (S := S) he htyE hCok hrts hheap₂ hfaE hsS haS
  refine ⟨fun gi hgi => ?_, hheap₃.structs, hheap₃.arrays, hheap₃.acyclic, hvals, ?_, hrefsE,
    hheap₃.structsClosed, hheap₃.arraysClosed⟩
  · rw [hg₃, hg₂] at hgi
    rcases hgl gi hgi with h | h
    · obtain ⟨h1, h2⟩ := hs.globals gi h
      exact ⟨h1, h2.extend hext⟩
    · exact h
  · exact List.forall₂_map_right_iff.mp hrefsT

end Silmaril.Wasm.Execution.Core
