module

public import Silmaril.Wasm.Execution.Core.Soundness.CallMeta
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

@[expose] public section

/-! # Preservation for the call rules of `Step` (§4.3)

`AdminsOk`-level subject reduction for `call`, `call_ref` (null, Wasm function,
host function with a result, divergent host function), `return_call`,
`return_call_ref` (label, handler, frame-null, frame-addr), `call_indirect` and
`return_call_indirect`.

The general form is `AdminsOk s C lhs it → wf hypotheses → AdminsOk s' C rhs it`,
where the context `C` of the redex is related to the running frame `f` by
`CtxOk s f C` (as in the progress proof), `C.Wf`, and `StoreOk s`.

Additional hypotheses (see the doc of each lemma):

* `StoreTypesOk s`: struct and array instance types are valid in `{}`. `StoreOk`
  (like the spec's `Structinst_ok`) does not require it, but without it a
  value's principal type may be an ill-formed defined type whose declared
  supertypes mention `REC` indices; together with the unconstrained `RECS` of
  `Moduleinst_ok` this makes subtyping in a frame context unsound w.r.t. `{}`
  (and the call rules, which move arguments into a new frame, not preserving).
* `callRefType` annotations valid in `{}` (they are produced by `call` with a
  store function type).
-/

namespace Silmaril.Wasm.Execution.Core.PC

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Store invariants and value transfer -/

/-- Struct and array instance types are valid (in `{}`). -/
def StoreTypesOk (s : Store H) : Prop :=
  (∀ si ∈ s.structs, TyOk {} si.type) ∧ (∀ ai ∈ s.arrays, TyOk {} ai.type)

theorem FuncInstOk.tyOk' {s : Store H} {fi : FuncInst H} (h : FuncInstOk s fi) :
    TyOk {} fi.type := by
  cases h with
  | wasm hdt => exact hdt
  | host hdt => exact hdt

theorem StoreOk.func_tyOk {s : Store H} (hs : StoreOk s) {a : Nat} {fi : FuncInst H}
    (h : s.funcs[a]? = some fi) : TyOk {} fi.type :=
  FuncInstOk.tyOk' (hs.funcs fi (List.mem_of_getElem? h))

theorem refI_principal {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {r : Ref}
    {rt₀ : CRefType} (e : Ref.type? s r = some rt₀) (hr : r ≠ .null) : RefI rt₀ := by
  cases r with
  | null => exact absurd rfl hr
  | i31 b => cases e; simp [RefI, HeapI]
  | struct a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨si, h, rfl⟩ := e
    simpa [RefI, HeapI, Ty.defHeap] using hsT.1 si (List.mem_of_getElem? h)
  | array a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨ai, h, rfl⟩ := e
    simpa [RefI, HeapI, Ty.defHeap] using hsT.2 ai (List.mem_of_getElem? h)
  | func a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨fi, h, rfl⟩ := e
    simpa [RefI, HeapI, Ty.defHeap] using StoreOk.func_tyOk hs h
  | exn a =>
    simp only [Ref.type?, Option.map_eq_some_iff] at e
    obtain ⟨_, _, rfl⟩ := e
    simp [RefI, HeapI]
  | host a => cases e; simp [RefI, HeapI]
  | extern r => cases e; simp [RefI, HeapI]

theorem refOk_null_inv {s : Store H} {rt : CRefType} (h : RefOk s .null rt) :
    ∃ hh, rt = .ref true hh := by
  obtain ⟨rt₀, e, hrt, -⟩ := h.principal
  simp only [Ref.type?, Option.some.injEq] at e
  subst e
  rcases hrt with rfl | ⟨-, hs⟩
  · exact ⟨_, rfl⟩
  · cases hs with | refNull _ => exact ⟨_, rfl⟩

/-- A value typed at `t ≤ t'` in a context with valid types has the runtime type `t'`. -/
theorem valOk_transfer {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {Δ : TypeCtx}
    (hΔ : TypesOk Δ) {v : Val} {t t' : CValType} (hv : ValOk s v t) (h : Sub Δ t t')
    (ht' : TyOk {} t') : ValOk s v t' := by
  cases hv with
  | num v => cases h; exact .num v
  | vec b => cases h; exact .vec b
  | @ref r rt hr =>
    cases h with
    | @refv _ _ rt' h =>
      have hrt' : TyOk {} rt' := ht'.refv_inv
      by_cases hn : r = .null
      · subst hn
        obtain ⟨hh, rfl⟩ := refOk_null_inv hr
        cases h with
        | refNull _ => exact .ref (.sub .null hrt' (.refNull .bot))
      · obtain ⟨rt₀, e, hrt, -⟩ := hr.principal
        have hI₀ := refI_principal hs hsT e hn
        have hI : RefI rt := by
          rcases hrt with rfl | ⟨hok, hs0⟩
          · exact hI₀
          · exact (ref_toEmpty typesOk_empty hs0 hI₀ hok).2
        exact .ref (.sub hr hrt' (ref_toEmpty hΔ h hI hrt').1)

theorem valsOk_transfer {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {Δ : TypeCtx}
    (hΔ : TypesOk Δ) {vs : List Val} {ts : List CValType} (hv : List.Forall₂ (ValOk s) vs ts) :
    ∀ {ts' : List CValType}, ResultSub Δ ts ts' → ResultOk {} ts' →
      List.Forall₂ (ValOk s) vs ts' := by
  induction hv with
  | nil => intro ts' h _; cases h; exact .nil
  | cons hv _ ih =>
    intro ts' h hok
    cases h with
    | cons h hl =>
      exact .cons (valOk_transfer hs hsT hΔ hv h (hok _ (by simp)))
        (ih hl fun t ht => hok t (by simp [ht]))

/-! ## Contexts of frames -/

theorem ModuleInstOk.typesOk' {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : TypesOk C.toTypeCtx := by
  cases h with | mk htypes => exact htypes

theorem FrameOk.typesOk' {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    TypesOk C.toTypeCtx := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  show TypesOk C₀.toTypeCtx
  exact ModuleInstOk.typesOk' hm

theorem CtxOk.typesOk' {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C) :
    TypesOk C.toTypeCtx := by
  obtain ⟨Cf, hf, hv, -⟩ := h.frame
  rw [Context.eq_of_frameView hv]
  show TypesOk Cf.toTypeCtx
  exact FrameOk.typesOk' hf

theorem CtxOk.func' {s : Store H} {f : Frame} {C : Context} (h : CtxOk s f C) {x : FuncIdx}
    {d : DefType} (hx : C.funcs[x.toNat]? = some d) :
    ∃ a, f.module.funcs[x.toNat]? = some a ∧ ExternAddrOk s (.func a) (.func d) := by
  obtain ⟨Cf, hf, hv, -⟩ := h.frame
  rw [Context.eq_of_frameView hv] at hx
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ _ _ hfuncs =>
    obtain ⟨a, ha, hx⟩ := forall₂_getElem?_right hfuncs hx
    exact ⟨a, ha, hx⟩

/-- A function address typed at `d`: `d` is the instance's type or a valid supertype. -/
theorem externAddr_func {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) :
    ∀ {a : Nat} {fi : FuncInst H} {d : DefType}, xa = .func a → s.funcs[a]? = some fi →
      xt = .func d → d = fi.type ∨ (TyOk {} d ∧ Sub {} fi.type d) := by
  induction h with
  | func h =>
    intro a fi d ha hf hd
    cases ha; cases hd
    rw [h] at hf; cases hf
    exact .inl rfl
  | sub _ hok hs ih =>
    intro a fi d ha hf hd
    subst hd
    cases hs with
    | @func d' _ hsub =>
      have hd : TyOk {} d := by cases hok with | func h _ => exact h
      rcases ih ha hf rfl with rfl | ⟨hd', hs'⟩
      · exact .inr ⟨hd, hsub⟩
      · exact .inr ⟨hd, Sub.trans TypeCtx.ok_empty hd' hs' hsub⟩
  | _ => intro a fi d ha; cases ha

/-! ## Typing inversion for administrative sequences -/

theorem subEqR_ok {Δ : TypeCtx} {a b : List CValType} (h : List.Forall₂ (SubEqR Δ) a b)
    (ha : ResultOk Δ a) : ResultOk Δ b := by
  induction h with
  | nil => simp
  | @cons x y _ _ hxy _ ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rcases hxy with rfl | ⟨_, hy⟩
      · exact ha _ (by simp)
      · exact hy
    · exact ih (fun t ht => ha t (by simp [ht])) t ht

/-- `AdminsOk.single_aux` (`Configurations`) that also records that the frame
part is well-formed. -/
theorem single_aux' {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ a, as = [a] →
      C.toTypeCtx.Ok →
      ∃ ts it₀, AdminOk s C a it₀ ∧ ResultOk C.toTypeCtx ts ∧
        List.Forall₂ (SubEqL C.toTypeCtx) it.params (ts ++ it₀.params) ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (ts ++ it₀.results) it.results ∧
        ∀ x ∈ it.inits, x ∉ it₀.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _, e, _ => by cases e
  | _, _, it, .single h, a, e, _ => by
    cases e
    exact ⟨[], it, h, by simp [ResultOk], forall₂_self (fun _ => .inl rfl) _,
      forall₂_self (fun _ => .inl rfl) _, fun _ hx hn => absurd hx hn⟩
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha _ hs, a, e, hΔ => by
    obtain ⟨rfl, e₂⟩ := List.cons_eq_cons.mp e
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux hs e₂ hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂ s₂
    refine ⟨[], ⟨t₁, xs₁, t₂⟩, ha, by simp [ResultOk], forall₂_self (fun _ => .inl rfl) _,
      forall₂_subEqR_of_sub s₂ r₂, ?_⟩
    intro x hx hn
    rcases List.mem_append.mp hx with hx | hx
    · exact absurd hx hn
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact absurd hx' hn
      · exact ⟨t, h'⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, a, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain ⟨p₁, _, s₁, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := single_aux' h₂ a e₂ hΔ'
      rw [hC] at ha hp hr hi hts
      refine ⟨ts, it₀, ha, hts, forall₂_comp s₁ hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (p₁ a ha') hbc, hr, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact i₁ x hx
      · exact hi x hx hn
    · obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := single_aux' h₁ a e₁ hΔ
      obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ e₂ hΔ'
      rw [Context.initLocals_toTypeCtx] at r₂ s₂
      refine ⟨ts, it₀, ha, hts, hp, forall₂_comp hr s₂ fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (r₂ c hc), ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx hn
      · obtain ⟨t, ht⟩ := i₂ x hx
        rcases Context.initLocals_set ht with hx' | h'
        · exact hi x hx' hn
        · exact ⟨t, h'⟩
  | _, _, _, .sub (it := it) h hs hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := single_aux' h a e hΔ
    refine ⟨ts, it₀, ha, hts, forall₂_comp hs.1 hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (hok.1 a ha') hbc,
      forall₂_comp hr hs.2.1 fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc), ?_⟩
    intro x hx hn
    by_cases hx' : x ∈ it.inits
    · exact hi x hx' hn
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame (ts := F) h hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hts, hp, hr, hi⟩ := single_aux' h a e hΔ
    refine ⟨F ++ ts, it₀, ha, ResultOk.append hok hts, ?_, ?_, hi⟩
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hp
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hr

/-- Locals initialised by code whose instructions initialise none are already set. -/
theorem inits_set {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
      (∀ a ∈ as, ∀ C' it', AdminOk s C' a it' → it'.inits = []) →
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _ => by simp
  | _, _, _, .single h, hI => by
    have := hI _ (by simp) _ _ h
    intro x hx; rw [this] at hx; cases hx
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, hI => by
    intro x hx
    have i₁ := inits_set h₁ fun a ha => hI a (List.mem_append_left _ ha)
    have i₂ := inits_set h₂ fun a ha => hI a (List.mem_append_right _ ha)
    rcases List.mem_append.mp hx with hx | hx
    · exact i₁ x hx
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact i₁ x hx'
      · exact ⟨t, h'⟩
  | C, _, _, .cons (xs₁ := xs₁) ha _ hs, hI => by
    have e := hI _ (by simp) _ _ ha
    have ih := inits_set hs (fun a ha' => hI a (List.mem_cons_of_mem _ ha'))
    simp only at e
    intro x hx
    rw [e, List.nil_append] at hx
    rw [e] at ih
    exact ih x hx
  | _, _, _, .sub (it := it) h hs _, hI => by
    intro x hx
    by_cases hx' : x ∈ it.inits
    · exact inits_set h hI x hx'
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame h _, hI => fun x hx => inits_set h hI x hx

theorem val_inits {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : it.inits = [] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      rfl
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      rfl
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      rfl
  · cases h with
    | ref _ => rfl

theorem mem_vals {a : Admin} {vs : List Val} (h : a ∈ vals vs) : ∃ v : Val, a = v.toAdmin := by
  simp only [vals, List.mem_map] at h
  obtain ⟨v, -, rfl⟩ := h
  exact ⟨v, rfl⟩

/-- **Redex inversion and replacement** for `vals vs ++ [c]`, where `c` has only
typings that initialise no local. -/
theorem redex_rep {s : Store H} {C : Context} (hC : C.Wf) {vs : List Val} {c : Admin}
    {it : InstrType} (hc0 : ∀ C' it₀, AdminOk s C' c it₀ → it₀.inits = [])
    (h : AdminsOk s C (vals vs ++ [c]) it) :
    ∃ tvs it₀ M ts, AdminOk s C c it₀ ∧ List.Forall₂ (ValOk s) vs tvs ∧
      ResultSub C.toTypeCtx (it.params ++ tvs) M ∧ ResultOk C.toTypeCtx M ∧
      ResultOk C.toTypeCtx ts ∧ ResultSub C.toTypeCtx M (ts ++ it₀.params) ∧
      ResultOk C.toTypeCtx it.params ∧
      (ResultOk C.toTypeCtx it₀.results → ∀ (s' : Store H) (new : List Admin),
        AdminsOk s' C new ⟨it.params, [], ts ++ it₀.results⟩ → AdminsOk s' C new it) := by
  have hΔ := hC.types
  have hI : ∀ a ∈ vals vs ++ [c], ∀ C' it', AdminOk s C' a it' → it'.inits = [] := by
    intro a ha C' it' h'
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨v, rfl⟩ := mem_vals ha
      exact val_inits h'
    · simp only [List.mem_singleton] at ha
      subst ha
      exact hc0 _ _ h'
  have hxs := inits_set h hI
  have hpo := AdminsOk.params_ok hC h
  obtain ⟨M, xs₁, xs₂, h₁, h₂, -⟩ := AdminsOk.split h hC (vals vs) [c] rfl (by simp)
  have hx₁ := inits_set h₁ fun a ha => hI a (List.mem_append_left _ ha)
  rw [Context.initLocals_of_set hx₁] at h₂
  obtain ⟨tvs, hvs, hsub⟩ := AdminsOk.vals_inv hΔ h₁
  have hM := (AdminsOk.params_ok hC h₂).1
  obtain ⟨ts, it₀, hc, hts, hp, hr, -⟩ := single_aux' h₂ c rfl hΔ
  refine ⟨tvs, it₀, M, ts, hc, hvs, hsub, hM, hts, hp.imp fun _ _ h => h.sub, hpo.1, ?_⟩
  intro hr₀ s' new hnew
  rcases it with ⟨P, xs, R⟩
  refine .sub hnew ⟨ResultSub.refl _ _, hr.imp fun _ _ h => h.sub, fun x hx _ => hxs x hx⟩
    ⟨hpo.1, subEqR_ok hr (ResultOk.append hts hr₀), hpo.2⟩

/-- Principal replacement for a single administrative instruction. -/
theorem single_rep {s : Store H} {C : Context} (hC : C.Wf) {a : Admin} {it : InstrType}
    (ha0 : ∀ C' it₀, AdminOk s C' a it₀ → it₀.inits = []) (h : AdminsOk s C [a] it) :
    ∃ it₀, AdminOk s C a it₀ ∧
      (ResultOk C.toTypeCtx it₀.params → ResultOk C.toTypeCtx it₀.results →
        ∀ (s' : Store H) (new : List Admin), AdminsOk s' C new it₀ → AdminsOk s' C new it) := by
  have h' : AdminsOk s C (vals [] ++ [a]) it := by simpa [vals] using h
  obtain ⟨tvs, it₀, M, ts, hc, hvs, hsub, hM, hts, hp, hP, hrep⟩ := redex_rep hC ha0 h'
  cases hvs
  refine ⟨it₀, hc, fun hp₀ hr₀ s' new hnew => hrep hr₀ s' new ?_⟩
  have hi0 := ha0 _ _ hc
  rcases it₀ with ⟨p₀, i₀, r₀⟩
  simp only at hi0 hp hr₀ hp₀
  subst hi0
  simp only [List.append_nil] at hsub
  refine .sub (.frame hnew hts) ⟨ResultSub.trans hC.types hM hsub hp, ResultSub.refl _ _,
    by simp⟩ ⟨hP, ResultOk.append hts hr₀, by simp⟩

/-! ## Small typing combinators -/

theorem rok1 {Δ : TypeCtx} {t : CValType} (h : TyOk Δ t) : ResultOk Δ [t] := by
  intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact h

theorem refT_def_ok {Δ : TypeCtx} {d : DefType} (h : TyOk Δ d) (n : Bool) :
    TyOk Δ (Ty.refT n (Ty.defHeap d)) := .refv (.ref (.use (.dt h)))

theorem resultSub_weaken {Δ : TypeCtx} {a b : List CValType} (h : ResultSub {} a b) :
    ResultSub Δ a b :=
  h.imp fun _ _ h => Sub.weakenE h Δ rfl fun _ _ h => by simp at h

theorem resultOk_weaken {Δ : TypeCtx} {a : List CValType} (h : ResultOk {} a) : ResultOk Δ a :=
  fun t ht => TyOk.of_empty Δ (h t ht)

theorem seqk {s : Store H} {C : Context} {as₁ as₂ : List Admin} {A B D : List CValType}
    (h₁ : AdminsOk s C as₁ ⟨A, [], B⟩) (h₂ : AdminsOk s C as₂ ⟨B, [], D⟩) :
    AdminsOk s C (as₁ ++ as₂) ⟨A, [], D⟩ := by
  simpa using AdminsOk.seq h₁ (by simp) h₂

theorem subk {s : Store H} {C : Context} {as : List Admin} {A B A' B' : List CValType}
    (h : AdminsOk s C as ⟨A, [], B⟩) (hA : ResultSub C.toTypeCtx A' A)
    (hB : ResultSub C.toTypeCtx B B') (hA' : ResultOk C.toTypeCtx A')
    (hB' : ResultOk C.toTypeCtx B') : AdminsOk s C as ⟨A', [], B'⟩ :=
  .sub h ⟨hA, hB, by simp⟩ ⟨hA', hB', by simp⟩

theorem expand_func_of_sub {d₁ d₂ : DefType} (h1 : TyOk {} d₁) (h2 : TyOk {} d₂)
    (hs : Sub {} d₁ d₂) {p r : Ty (.list .val)} (he : Expand d₂ (.func p r)) :
    ∃ p' r', Expand d₁ (.func p' r') := by
  have hc := Sub.complete TypeCtx.ok_empty rfl hs h1 h2
  simp only [Sub.checkK] at hc
  have hk := TypeCtx.checkDef_kind TypeCtx.ok_empty h1 hc
  obtain ⟨hu⟩ := he
  simp only [Validation.defKind, hu, Option.map_some] at hk
  cases hu1 : unrolldt d₁ with
  | none => simp [hu1] at hk
  | some st =>
    rw [hu1] at hk
    cases st with
    | sub fin sups ct =>
      cases ct with
      | func p' r' => exact ⟨p', r', ⟨hu1⟩⟩
      | struct _ => simp [compAbs, Ty.body] at hk
      | array _ => simp [compAbs, Ty.body] at hk

/-- Function types of a store function below a typed use `d`. -/
theorem func_sub_data {d t : DefType} (hdt : d = t ∨ (TyOk {} d ∧ Sub {} t d)) (ht : TyOk {} t)
    {ps rs : Ty (.list .val)} (he : Expand d (.func ps rs)) :
    ∃ ps' rs', Expand t (.func ps' rs') ∧ ResultSub {} ps.toList ps'.toList ∧
      ResultSub {} rs'.toList rs.toList := by
  rcases hdt with rfl | ⟨hd, hsub⟩
  · exact ⟨ps, rs, he, ResultSub.refl _ _, ResultSub.refl _ _⟩
  · obtain ⟨ps', rs', he'⟩ := expand_func_of_sub ht hd hsub he
    obtain ⟨h1, h2⟩ := ds_func ht hd (.defDef hsub) he' he
    exact ⟨ps', rs', he', h1, h2⟩

theorem closeRef_typeIdx {C : Context} {y : TypeIdx} {d : DefType} (hd : C.type? y = some d) :
    C.closeRef ⟨true, .typeIdx y⟩ = .ref true (.use (.dt d)) := by
  simp only [Context.type?] at hd
  simp [Context.closeRef, liftRef, liftHeap, liftTypeIdx, Ty.substAll, Ty.subst, Subst.all, hd]

/-! ## Inversions of the call instructions -/

theorem inv_call {s : Store H} {C : Context} {x : FuncIdx} {it : InstrType}
    (h : AdminOk s C (.plain (.call x)) it) :
    ∃ d ps rs, C.funcs[x.toNat]? = some d ∧ Expand d (.func ps rs) ∧
      it = .plain ps.toList rs.toList := by
  cases h with
  | plain h =>
    cases h with
    | call hf he => exact ⟨_, _, _, hf, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h

theorem inv_returnCall {s : Store H} {C : Context} {x : FuncIdx} {it : InstrType}
    (h : AdminOk s C (.plain (.returnCall x)) it) :
    ∃ d ps rs rs' t₃ t₄, C.funcs[x.toNat]? = some d ∧ Expand d (.func ps rs) ∧
      C.return_ = some rs' ∧ ResultSub C.toTypeCtx rs.toList rs' ∧
      InstrTypeOk C (.plain t₃ t₄) ∧ it = .plain (t₃ ++ ps.toList) t₄ := by
  cases h with
  | plain h =>
    cases h with
    | returnCall hf he hr hs hok => exact ⟨_, _, _, _, _, _, hf, he, hr, hs, hok, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h

theorem inv_callIndirect {s : Store H} {C : Context} {x : TableIdx} {y : TypeIdx}
    {it : InstrType} (h : AdminOk s C (.plain (.callIndirect x y)) it) :
    ∃ a l rt d ps rs, C.tables[x.toNat]? = some ⟨a, l, rt⟩ ∧ Sub C.toTypeCtx rt Ty.funcref ∧
      C.type? y = some d ∧ Expand d (.func ps rs) ∧
      it = .plain (ps.toList ++ [a.valType]) rs.toList := by
  cases h with
  | plain h =>
    cases h with
    | callIndirect ht hs hd he => exact ⟨_, _, _, _, _, _, ht, hs, hd, he, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h

theorem inv_returnCallIndirect {s : Store H} {C : Context} {x : TableIdx} {y : TypeIdx}
    {it : InstrType} (h : AdminOk s C (.plain (.returnCallIndirect x y)) it) :
    ∃ a l rt d ps rs rs' t₃ t₄, C.tables[x.toNat]? = some ⟨a, l, rt⟩ ∧
      Sub C.toTypeCtx rt Ty.funcref ∧ C.type? y = some d ∧ Expand d (.func ps rs) ∧
      C.return_ = some rs' ∧ ResultSub C.toTypeCtx rs.toList rs' ∧
      InstrTypeOk C (.plain t₃ t₄) ∧ it = .plain (t₃ ++ ps.toList ++ [a.valType]) t₄ := by
  cases h with
  | plain h =>
    cases h with
    | returnCallIndirect ht hs hd he hr hrs hok =>
      exact ⟨_, _, _, _, _, _, _, _, _, ht, hs, hd, he, hr, hrs, hok, rfl⟩
    | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
      cases h

/-- Typings of `CALL_REF` (either representation). -/
theorem inv_callRef {s : Store H} {C : Context} {c : Admin} (hc : c.IsCallRef) {it : InstrType}
    (h : AdminOk s C c it) :
    ∃ d ps rs, Expand d (.func ps rs) ∧
      it = .plain (ps.toList ++ [Ty.refT true (Ty.defHeap d)]) rs.toList ∧
      (∀ y, c = .plain (.callRef y) → C.type? y = some d) ∧
      (∀ d', c = .callRefType d' → d' = d ∧ TyOk {} d) := by
  cases c with
  | plain i =>
    cases i <;> simp [Admin.IsCallRef] at hc
    cases h with
    | plain h =>
      cases h with
      | callRef hd he =>
        exact ⟨_, _, _, he, rfl, (fun y hy => by cases hy; exact hd), (fun _ h => by cases h)⟩
      | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
        cases h
  | callRefType d =>
    cases h with
    | callRefType hok he =>
      exact ⟨_, _, _, he, rfl, (fun _ h => by cases h), (fun _ h => by cases h; exact ⟨rfl, hok⟩)⟩
  | _ => simp [Admin.IsCallRef] at hc

theorem inv_callRef_tyOk {C : Context} (hC : C.Wf) {c : Admin} (hc : c.IsCallRef)
    {d : DefType} (h1 : ∀ y, c = .plain (.callRef y) → C.type? y = some d)
    (h2 : ∀ d', c = .callRefType d' → d' = d ∧ TyOk {} d) : TyOk C.toTypeCtx d := by
  cases c with
  | plain i =>
    cases i <;> simp [Admin.IsCallRef] at hc
    exact hC.type (h1 _ rfl)
  | callRefType d' => exact TyOk.of_empty _ (h2 _ rfl).2
  | _ => simp [Admin.IsCallRef] at hc

/-- Typings of `RETURN_CALL_REF` (either representation). -/
theorem inv_returnCallRef {s : Store H} {C : Context} {c : Admin} (hc : c.IsReturnCallRef)
    {it : InstrType} (h : AdminOk s C c it) :
    ∃ d ps rs rs' t₃ t₄, Expand d (.func ps rs) ∧ C.return_ = some rs' ∧
      ResultSub C.toTypeCtx rs.toList rs' ∧ InstrTypeOk C (.plain t₃ t₄) ∧
      it = .plain (t₃ ++ ps.toList ++ [Ty.refT true (Ty.defHeap d)]) t₄ ∧
      (∀ y, c = .plain (.returnCallRef y) → C.type? y = some d) ∧
      (∀ d', c = .returnCallRefType d' → d' = d ∧ TyOk {} d) := by
  cases c with
  | plain i =>
    cases i <;> simp [Admin.IsReturnCallRef] at hc
    cases h with
    | plain h =>
      cases h with
      | returnCallRef hd he hr hs hok =>
        exact ⟨_, _, _, _, _, _, he, hr, hs, hok, rfl, (fun y hy => by cases hy; exact hd),
          (fun _ h => by cases h)⟩
      | parametric h | numeric h | vector h | «variable» h | memory h | table h | reference h =>
        cases h
  | returnCallRefType d =>
    cases h with
    | returnCallRefType hok he hr hs hit =>
      exact ⟨_, _, _, _, _, _, he, hr, hs, hit, rfl, (fun _ h => by cases h),
        (fun _ h => by cases h; exact ⟨rfl, hok⟩)⟩
  | _ => simp [Admin.IsReturnCallRef] at hc

/-- Rebuild a `RETURN_CALL_REF` typing from its data. -/
theorem returnCallRef_mk {s : Store H} {C : Context} {c : Admin} (hc : c.IsReturnCallRef)
    {d : DefType} {ps rs : Ty (.list .val)} {rs' t₃ t₄ : List CValType}
    (he : Expand d (.func ps rs)) (hr : C.return_ = some rs')
    (hs : ResultSub C.toTypeCtx rs.toList rs') (hok : InstrTypeOk C (.plain t₃ t₄))
    (h1 : ∀ y, c = .plain (.returnCallRef y) → C.type? y = some d)
    (h2 : ∀ d', c = .returnCallRefType d' → d' = d ∧ TyOk {} d) :
    AdminOk s C c (.plain (t₃ ++ ps.toList ++ [Ty.refT true (Ty.defHeap d)]) t₄) := by
  cases c with
  | plain i =>
    cases i <;> simp [Admin.IsReturnCallRef] at hc
    exact .plain (.returnCallRef (h1 _ rfl) he hr hs hok)
  | returnCallRefType d' =>
    obtain ⟨rfl, hd⟩ := h2 _ rfl
    exact .returnCallRefType hd he hr hs hok
  | _ => simp [Admin.IsReturnCallRef] at hc

theorem callRef_inits {s : Store H} {c : Admin} (hc : c.IsCallRef) :
    ∀ C' it₀, AdminOk s C' c it₀ → it₀.inits = [] := by
  intro C' it₀ h
  obtain ⟨_, _, _, _, rfl, -⟩ := inv_callRef hc h
  rfl

theorem returnCallRef_inits {s : Store H} {c : Admin} (hc : c.IsReturnCallRef) :
    ∀ C' it₀, AdminOk s C' c it₀ → it₀.inits = [] := by
  intro C' it₀ h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl, -⟩ := inv_returnCallRef hc h
  rfl

/-! ## `call`, `call_ref` (null, divergent host), `return_call`, trap -/

/-- `Step_read/call`. -/
theorem pres_call {s : Store H} {f : Frame} {C : Context} {it : InstrType} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} (hs : StoreOk s) (hc : CtxOk s f C) (hC : C.Wf)
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : AdminsOk s C [.plain (.call x)] it) :
    AdminsOk s C [.ref (.func a), .callRefType fi.type] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, rfl⟩ := inv_call h; rfl) h
  obtain ⟨d, ps, rs, hd, he, rfl⟩ := inv_call h0
  obtain ⟨a', ha', hxa⟩ := CtxOk.func' hc hd
  rw [hx] at ha'; cases ha'
  have hdok : TyOk C.toTypeCtx d := hC.funcs d (List.mem_of_getElem? hd)
  have hpr := Expand.func_ok hdok he
  refine hrep hpr.1 hpr.2 s _ ?_
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨ps', rs', he', hp, hr⟩ := func_sub_data (externAddr_func hxa rfl hf rfl) hfit he
  have hpr' := Expand.func_ok (TyOk.of_empty C.toTypeCtx hfit) he'
  have h1 : AdminsOk s C [.ref (.func a)] ⟨ps'.toList, [], ps'.toList ++
      [.refv (.ref false (Ty.defHeap fi.type))]⟩ := by
    simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.func hf))) hpr'.1
  have h2 : AdminsOk s C [.callRefType fi.type]
      ⟨ps'.toList ++ [.refv (.ref false (Ty.defHeap fi.type))], [], rs'.toList⟩ :=
    subk (.single (.callRefType hfit he'))
      (ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNull .heapRefl)) .nil))
      (ResultSub.refl _ _)
      (ResultOk.append hpr'.1 (rok1 (refT_def_ok (TyOk.of_empty C.toTypeCtx hfit) false))) hpr'.2
  exact subk (seqk h1 h2) (resultSub_weaken hp) (resultSub_weaken hr) hpr.1 hpr.2

/-- `Step/call_ref-null`. -/
theorem pres_callRefNull {s : Store H} {C : Context} {it : InstrType} {c : Admin}
    (hC : C.Wf) (hcr : c.IsCallRef) (h : AdminsOk s C [.ref .null, c] it) :
    AdminsOk s C [.trap] it := by
  have h' : AdminsOk s C (vals [.ref .null] ++ [c]) it := h
  obtain ⟨tvs, it₀, M, ts, hc0, -, -, -, hts, -, hP, hrep⟩ := redex_rep hC (callRef_inits hcr) h'
  obtain ⟨d, ps, rs, he, rfl, h1, h2⟩ := inv_callRef hcr hc0
  have hrs := (Expand.func_ok (inv_callRef_tyOk hC hcr h1 h2) he).2
  exact hrep hrs s _ (.single (.trap ⟨hP, ResultOk.append hts hrs, by simp⟩))

/-- `Step/call_ref-hostfunc-div` (a stutter). -/
theorem pres_callRefHostDiv {s : Store H} {C : Context} {it : InstrType} {as : List Admin}
    (h : AdminsOk s C as it) : AdminsOk s C as it := h

/-- `Step_read/return_call`. -/
theorem pres_returnCall {s : Store H} {f : Frame} {C : Context} {it : InstrType} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} (hs : StoreOk s) (hc : CtxOk s f C) (hC : C.Wf)
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : AdminsOk s C [.plain (.returnCall x)] it) :
    AdminsOk s C [.ref (.func a), .returnCallRefType fi.type] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := inv_returnCall h; rfl) h
  obtain ⟨d, ps, rs, rs', t₃, t₄, hd, he, hret, hrs, hok, rfl⟩ := inv_returnCall h0
  obtain ⟨a', ha', hxa⟩ := CtxOk.func' hc hd
  rw [hx] at ha'; cases ha'
  have hdok : TyOk C.toTypeCtx d := hC.funcs d (List.mem_of_getElem? hd)
  have hpr := Expand.func_ok hdok he
  refine hrep (ResultOk.append hok.1 hpr.1) hok.2.1 s _ ?_
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨ps', rs'', he', hp, hr⟩ := func_sub_data (externAddr_func hxa rfl hf rfl) hfit he
  have hpr' := Expand.func_ok (TyOk.of_empty C.toTypeCtx hfit) he'
  have hrc : TyOk C.toTypeCtx (Ty.refT false (Ty.defHeap fi.type)) :=
    refT_def_ok (TyOk.of_empty C.toTypeCtx hfit) false
  have h1 : AdminsOk s C [.ref (.func a)] ⟨t₃ ++ ps'.toList, [], t₃ ++ ps'.toList ++
      [.refv (.ref false (Ty.defHeap fi.type))]⟩ := by
    simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.func hf)))
      (ResultOk.append hok.1 hpr'.1)
  have h2 : AdminsOk s C [.returnCallRefType fi.type]
      ⟨t₃ ++ ps'.toList ++ [.refv (.ref false (Ty.defHeap fi.type))], [], t₄⟩ :=
    subk (.single (.returnCallRefType hfit he' hret
        (ResultSub.trans hC.types hpr.2 (resultSub_weaken hr) hrs) hok))
      (ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNull .heapRefl)) .nil))
      (ResultSub.refl _ _)
      (ResultOk.append (ResultOk.append hok.1 hpr'.1) (rok1 hrc)) hok.2.1
  exact subk (seqk h1 h2) (ResultSub.append (ResultSub.refl _ _) (resultSub_weaken hp))
    (ResultSub.refl _ _) (ResultOk.append hok.1 hpr.1) hok.2.1

theorem frame_inits {s : Store H} {k : Nat} {fr : Frame} {body : List Admin} :
    ∀ C' it₀, AdminOk s C' (.frame k fr body) it₀ → it₀.inits = [] := by
  intro C' it₀ h; cases h; rfl

theorem label_inits {s : Store H} {k : Nat} {cont : List Instr} {body : List Admin} :
    ∀ C' it₀, AdminOk s C' (.label k cont body) it₀ → it₀.inits = [] := by
  intro C' it₀ h; cases h; rfl

theorem handler_inits {s : Store H} {k : Nat} {cs : List Catch} {body : List Admin} :
    ∀ C' it₀, AdminOk s C' (.handler k cs body) it₀ → it₀.inits = [] := by
  intro C' it₀ h; cases h; rfl

/-- `Step_read/return_call_ref-frame-null`. -/
theorem pres_returnCallRefFrameNull {s : Store H} {C : Context} {it : InstrType} {k : Nat}
    {fr : Frame} {body : List Admin} (hC : C.Wf) (h : AdminsOk s C [.frame k fr body] it) :
    AdminsOk s C [.trap] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC frame_inits h
  cases h0 with
  | frame _ _ _ hok =>
    exact hrep (by simp) (resultOk_weaken hok) s _
      (.single (.trap ⟨by simp, resultOk_weaken hok, by simp⟩))

/-! ## `call_indirect`, `return_call_indirect` -/

theorem tableGet_refCast {s : Store H} {C : Context} (hC : C.Wf) {x : TableIdx} {y : TypeIdx}
    {a : AddrType} {l : Limits} {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
    (ht : C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub C.toTypeCtx rt Ty.funcref)
    (hd : C.type? y = some d) (he : Expand d (.func ps rs)) {Q : List CValType}
    (hQ : ResultOk C.toTypeCtx Q) :
    AdminsOk s C [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩)]
      ⟨Q ++ [a.valType], [], Q ++ [Ty.refT true (Ty.defHeap d)]⟩ := by
  have hrt : TyOk C.toTypeCtx rt := hC.tables _ (List.mem_of_getElem? ht)
  have hcl := closeRef_typeIdx hd
  have hdok := hC.type hd
  have hfr : TyOk C.toTypeCtx Ty.funcref := .ref (.abs _)
  have h1 : AdminsOk s C [.plain (.tableGet x)] ⟨Q ++ [a.valType], [], Q ++ [.refv rt]⟩ :=
    .frame (.single (.plain (.table (.tableGet ht)))) hQ
  have hci : InstrOk C (.refCast ⟨true, .typeIdx y⟩)
      (.plain [.refv Ty.funcref] [.refv (C.closeRef ⟨true, .typeIdx y⟩)]) :=
    .reference (.refCast (by rw [hcl]; exact .ref (.use (.dt hdok))) hfr
      (by rw [hcl]; exact .refNull (.defFunc he)))
  rw [hcl] at hci
  have h2 : AdminsOk s C [.plain (.refCast ⟨true, .typeIdx y⟩)]
      ⟨Q ++ [.refv rt], [], Q ++ [Ty.refT true (Ty.defHeap d)]⟩ :=
    .frame (subk (.single (.plain hci)) (.cons (.refv hs) .nil) (ResultSub.refl _ _)
      (rok1 (.refv hrt)) (rok1 (refT_def_ok hdok true))) hQ
  simpa using seqk h1 h2

/-- `Step_pure/call_indirect`. -/
theorem pres_callIndirect {s : Store H} {C : Context} {it : InstrType} {x : TableIdx}
    {y : TypeIdx} (hC : C.Wf) (h : AdminsOk s C [.plain (.callIndirect x y)] it) :
    AdminsOk s C [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.callRef y)] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := inv_callIndirect h; rfl) h
  obtain ⟨a, l, rt, d, ps, rs, ht, hs, hd, he, rfl⟩ := inv_callIndirect h0
  have hpr := Expand.func_ok (hC.type hd) he
  refine hrep (ResultOk.append hpr.1 (by simp)) hpr.2 s _ ?_
  have h3 : AdminsOk s C [.plain (.callRef y)]
      ⟨ps.toList ++ [Ty.refT true (Ty.defHeap d)], [], rs.toList⟩ :=
    .single (.plain (.callRef hd he))
  simpa using seqk (tableGet_refCast hC ht hs hd he hpr.1) h3

/-- `Step_pure/return_call_indirect`. -/
theorem pres_returnCallIndirect {s : Store H} {C : Context} {it : InstrType} {x : TableIdx}
    {y : TypeIdx} (hC : C.Wf) (h : AdminsOk s C [.plain (.returnCallIndirect x y)] it) :
    AdminsOk s C [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
      .plain (.returnCallRef y)] it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC (fun C' it₀ h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
      inv_returnCallIndirect h; rfl) h
  obtain ⟨a, l, rt, d, ps, rs, rs', t₃, t₄, ht, hs, hd, he, hret, hrs, hok, rfl⟩ :=
    inv_returnCallIndirect h0
  have hpr := Expand.func_ok (hC.type hd) he
  refine hrep (ResultOk.append (ResultOk.append hok.1 hpr.1) (by simp)) hok.2.1 s _ ?_
  have h3 : AdminsOk s C [.plain (.returnCallRef y)]
      ⟨t₃ ++ ps.toList ++ [Ty.refT true (Ty.defHeap d)], [], t₄⟩ :=
    .single (.plain (.returnCallRef hd he hret hrs hok))
  simpa using seqk (tableGet_refCast hC ht hs hd he (ResultOk.append hok.1 hpr.1)) h3

/-! ## Regularity of result types -/

theorem results_ok_gen {s : Store H} (P : Admin → Prop)
    (hP : ∀ C' a it', C'.Wf → P a → AdminOk s C' a it' → ResultOk C'.toTypeCtx it'.results) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → C.Wf →
      (∀ a ∈ as, P a) → ResultOk C.toTypeCtx it.results
  | _, _, _, .nil, _, _ => by simp
  | _, _, _, .single h, hC, hA => hP _ _ _ hC (hA _ (by simp)) h
  | _, _, _, .seq _ _ h₂, hC, hA => by
    have := results_ok_gen P hP h₂ (hC.initLocals _)
      (fun a ha => hA a (List.mem_append_right _ ha))
    simpa using this
  | _, _, _, .cons _ _ hs, hC, hA => by
    have := results_ok_gen P hP hs (hC.initLocals _)
      (fun a ha => hA a (List.mem_cons_of_mem _ ha))
    simpa using this
  | _, _, _, .sub _ _ hok, _, _ => hok.2.1
  | _, _, _, .frame h hok, hC, hA => ResultOk.append hok (results_ok_gen P hP h hC hA)

theorem results_ok_expr {s : Store H} {C : Context} {is : List Instr} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C (expression is) it) : ResultOk C.toTypeCtx it.results := by
  refine results_ok_gen (s := s) (fun a => ∃ i, a = .plain i) ?_ h hC ?_
  · rintro C' a it' hC' ⟨i, rfl⟩ ha
    cases ha with
    | plain hi => exact (hi.regular hC').2.1
    | throwRefInits hok => exact hok.2.1
  · intro a ha
    simp only [expression, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact ⟨i, rfl⟩

theorem refOk_tyOk {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {r : Ref}
    {rt : CRefType} (h : RefOk s r rt) : TyOk {} rt := by
  obtain ⟨rt₀, e, hrt, -⟩ := h.principal
  rcases hrt with rfl | ⟨hok, -⟩
  · by_cases hn : r = .null
    · subst hn
      simp only [Ref.type?, Option.some.injEq] at e
      subst e
      exact .ref .bot
    · exact (refI_principal hs hsT e hn).tyOk
  · exact hok

mutual
theorem admin_results_ok {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → C.Wf →
      ResultOk C.toTypeCtx it.results
  | _, _, _, .plain h, hC => (h.regular hC).2.1
  | _, _, _, .callRefType hok he, _ => (Expand.func_ok (TyOk.of_empty _ hok) he).2
  | _, _, _, .returnCallRefType _ _ _ _ hit, _ => hit.2.1
  | _, _, _, .ref h, _ => rok1 (.refv (TyOk.of_empty _ (refOk_tyOk hs hsT h)))
  | _, _, _, .label _ hc _, hC => by
    have := admins_results_ok hs hsT hc hC
    exact this
  | _, _, _, .frame _ _ _ hok, _ => resultOk_weaken hok
  | _, _, _, .handler _ hb, hC => by
    have := admins_results_ok hs hsT hb hC
    exact this
  | _, _, _, .trap hok, _ => hok.2.1
  | _, _, _, .throwRefInits hok, _ => hok.2.1

theorem admins_results_ok {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → C.Wf →
      ResultOk C.toTypeCtx it.results
  | _, _, _, .nil, _ => by simp
  | _, _, _, .single h, hC => admin_results_ok hs hsT h hC
  | _, _, _, .seq _ _ h₂, hC => by
    simpa using admins_results_ok hs hsT h₂ (hC.initLocals _)
  | _, _, _, .cons _ _ h', hC => by
    simpa using admins_results_ok hs hsT h' (hC.initLocals _)
  | _, _, _, .sub _ _ hok, _ => hok.2.1
  | _, _, _, .frame h hok, hC => ResultOk.append hok (admins_results_ok hs hsT h hC)
end

/-! ## `return_call_ref` under a label or handler -/

theorem Context.Wf.withLabel' {C : Context} (hC : C.Wf) {t : List CValType}
    (ht : ResultOk C.toTypeCtx t) : (C.withLabel t).Wf := by
  refine ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, ?_, hC.return_, hC.elems⟩
  intro ts h
  simp only [Context.withLabel, List.mem_cons] at h
  rcases h with rfl | h
  · exact ht
  · exact hC.labels _ h

/-- Values typed by subtypes of a well-formed stack. -/
theorem of_vals_sub {s : Store H} {C : Context} {vs : List Val} {tvs : List CValType}
    (hv : List.Forall₂ (ValOk s) vs tvs) :
    ∀ {M : List CValType}, ResultSub C.toTypeCtx tvs M → ResultOk C.toTypeCtx M →
      AdminsOk s C (vals vs) ⟨[], [], M⟩ := by
  induction hv with
  | nil => intro M h _; cases h; exact .nil
  | @cons v tv vs tvs hv _ ih =>
    intro M h hM
    cases h with
    | @cons _ m _ M' hs hl =>
      have hm : TyOk C.toTypeCtx m := hM m (by simp)
      have hM' : ResultOk C.toTypeCtx M' := fun t ht => hM t (by simp [ht])
      have h1 : AdminsOk s C [v.toAdmin] ⟨[], [], [m]⟩ :=
        subk (.single (AdminOk.toAdmin_ok hv)) .nil (.cons hs .nil) (by simp) (rok1 hm)
      have h2 : AdminsOk s C (vals vs) ⟨[m], [], [m] ++ M'⟩ := by
        simpa using AdminsOk.frame (ih hl hM') (rok1 hm)
      simpa [vals] using seqk h1 h2

/-- Split a subtyping `M ≤ A ++ B` at the right. -/
theorem resultSub_split_right {Δ : TypeCtx} {M A B : List CValType}
    (h : ResultSub Δ M (A ++ B)) : ∃ M₁ M₂, M = M₁ ++ M₂ ∧ ResultSub Δ M₁ A ∧ ResultSub Δ M₂ B :=
  forall₂_split h

/-- The typing of a redex `vals vs ++ [c]` with a tail call, re-typed in a context
with the same types and return type, with result `ts`. -/
theorem retcall_retype {s : Store H} {C C' : Context} (hC' : C'.Wf) {vs : List Val} {c : Admin}
    (hcr : c.IsReturnCallRef) {m : List CValType} {ys : List Nat}
    (hpre : AdminsOk s C' (vals vs ++ [c]) ⟨[], ys, m⟩)
    (hΔ : C.toTypeCtx = C'.toTypeCtx) (hret : C.return_ = C'.return_) (htypes : C.types = C'.types)
    {ts : List CValType} (hts : ResultOk C.toTypeCtx ts) :
    AdminsOk s C (vals vs ++ [c]) ⟨[], [], ts⟩ := by
  obtain ⟨tvs, it₁, M, T, hc1, hvs, hsub, hM, hT, hMs, -, -⟩ :=
    redex_rep hC' (returnCallRef_inits hcr) hpre
  obtain ⟨d, ps, rs, rs', t₃, t₄, he, hr, hrs, hok, rfl, h1, h2⟩ := inv_returnCallRef hcr hc1
  simp only [List.nil_append] at hsub
  have hMs' : ResultSub C'.toTypeCtx M ((T ++ t₃) ++ (ps.toList ++
      [Ty.refT true (Ty.defHeap d)])) := by simpa using hMs
  obtain ⟨M₁, M₂, rfl, hM₁, hM₂⟩ := resultSub_split_right hMs'
  rw [← hΔ] at hM hsub hM₂ hrs
  have hM1ok : ResultOk C.toTypeCtx M₁ := ResultOk.left hM
  have hv : AdminsOk s C (vals vs) ⟨[], [], M₁ ++ M₂⟩ := of_vals_sub hvs hsub hM
  have hc' : AdminOk s C c (.plain (M₁ ++ ps.toList ++ [Ty.refT true (Ty.defHeap d)]) ts) :=
    returnCallRef_mk hcr he (hret ▸ hr) hrs ⟨hM1ok, hts, by simp⟩
      (fun y hy => by
        have := h1 y hy
        simpa [Context.type?, htypes] using this)
      (fun d' hd' => by
        obtain ⟨e, hd⟩ := h2 d' hd'
        exact ⟨e, hd⟩)
  have hc'' : AdminsOk s C [c] ⟨M₁ ++ M₂, [], ts⟩ :=
    subk (.single hc') (by simpa using ResultSub.append (ResultSub.refl _ M₁) hM₂)
      (ResultSub.refl _ _) hM hts
  exact seqk hv hc''

/-- `Step_read/return_call_ref-label`. -/
theorem pres_returnCallRefLabel {s : Store H} {C : Context} {it : InstrType} {k : Nat}
    {cont : List Instr} {vs : List Val} {c : Admin} {rest : List Admin} (hC : C.Wf)
    (hcr : c.IsReturnCallRef) (h : AdminsOk s C [.label k cont (vals vs ++ [c] ++ rest)] it) :
    AdminsOk s C (vals vs ++ [c]) it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC label_inits h
  cases h0 with
  | @label _ _ _ _ t' ts xs' xs _ hc hb =>
    have hts : ResultOk C.toTypeCtx ts := by simpa using results_ok_expr hC hc
    have ht' : ResultOk C.toTypeCtx t' := by simpa using (AdminsOk.params_ok hC hc).1
    have hCl := Context.Wf.withLabel' hC ht'
    obtain ⟨m, ys₁, ys₂, hpre, -, -⟩ := AdminsOk.append_inv hCl (.inr (by simpa using hts)) hb
    exact hrep (by simp) hts s _ (retcall_retype (C := C) hCl hcr hpre rfl rfl rfl hts)

/-- `Step_read/return_call_ref-handler`. (Needs `StoreTypesOk` for the regularity of
the handler's result type.) -/
theorem pres_returnCallRefHandler {s : Store H} {C : Context} {it : InstrType} {k : Nat}
    {cs : List Catch} {vs : List Val} {c : Admin} {rest : List Admin} (hs : StoreOk s)
    (hsT : StoreTypesOk s) (hC : C.Wf) (hcr : c.IsReturnCallRef)
    (h : AdminsOk s C [.handler k cs (vals vs ++ [c] ++ rest)] it) :
    AdminsOk s C (vals vs ++ [c]) it := by
  obtain ⟨it₀, h0, hrep⟩ := single_rep hC handler_inits h
  cases h0 with
  | @handler _ _ _ _ ts xs _ hb =>
    have hts : ResultOk C.toTypeCtx ts := by simpa using admins_results_ok hs hsT hb hC
    obtain ⟨m, ys₁, ys₂, hpre, -, -⟩ := AdminsOk.append_inv hC (.inr (by simpa using hts)) hb
    exact hrep (by simp) hts s _ (retcall_retype (C := C) hC hcr hpre rfl rfl rfl hts)

/-! ## `call_ref` on a function address -/

theorem forall₂_split_left {α β : Type} {R : α → β → Prop} :
    ∀ {a b : List α} {m : List β}, List.Forall₂ R (a ++ b) m →
      ∃ m₁ m₂, m = m₁ ++ m₂ ∧ List.Forall₂ R a m₁ ∧ List.Forall₂ R b m₂
  | [], _, m, h => ⟨[], m, rfl, .nil, h⟩
  | _ :: _, _, _, h => by
    cases h with
    | cons hx ht =>
      obtain ⟨m₁, m₂, rfl, h1, h2⟩ := forall₂_split_left ht
      exact ⟨_ :: m₁, m₂, rfl, .cons hx h1, h2⟩

theorem forall₂_append_eq_len {α β : Type} {R : α → β → Prop} {a b : List α} {c d : List β}
    (h : List.Forall₂ R (a ++ b) (c ++ d)) (hl : b.length = d.length) :
    List.Forall₂ R a c ∧ List.Forall₂ R b d := by
  obtain ⟨l₁, l₂, e, h1, h2⟩ := forall₂_split h
  have hl₂ := h2.length_eq
  have hlen := congrArg List.length e
  simp only [List.length_append] at hlen
  obtain ⟨rfl, rfl⟩ := List.append_inj e (by omega)
  exact ⟨h1, h2⟩

/-- The common part of the `call_ref` rules on a function address: the arguments
have the callee's parameter types, and code producing the callee's results replaces
the redex. -/
theorem callRef_front {s : Store H} {f : Frame} {C : Context} {it : InstrType} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hs : StoreOk s) (hsT : StoreTypesOk s) (hc : CtxOk s f C) (hC : C.Wf)
    (hcr : c.IsCallRef) (hcd : ∀ d, c = .callRefType d → TyOk {} d)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (h : AdminsOk s C (vals vs ++ [.ref (.func a), c]) it) :
    ∃ P T rsc, ResultOk C.toTypeCtx P ∧ ResultOk C.toTypeCtx T ∧ ResultOk {} rsc ∧
      ResultSub C.toTypeCtx P T ∧ ResultSub {} rs.toList rsc ∧
      List.Forall₂ (ValOk s) vs ps.toList ∧
      ∀ (s' : Store H) (new : List Admin), AdminsOk s' C new ⟨P, [], T ++ rsc⟩ →
        AdminsOk s' C new it := by
  have hΔ := CtxOk.typesOk' hc
  have e0 : vals (vs ++ [.ref (.func a)]) ++ [c] = vals vs ++ [.ref (.func a), c] := by
    simp [vals, Val.toAdmin]
  have h' : AdminsOk s C (vals (vs ++ [.ref (.func a)]) ++ [c]) it := by rw [e0]; exact h
  obtain ⟨tvs', it₀, M, T, hc0, hvs', hsub, hM, hT, hMs, hP, hrep⟩ :=
    redex_rep hC (callRef_inits hcr) h'
  obtain ⟨dc, psc, rsc, hec, rfl, h1, h2⟩ := inv_callRef hcr hc0
  have hdc : TyOk {} dc := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsCallRef] at hcr
      exact hΔ.get (h1 _ rfl)
    | callRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      exact hcd _ rfl
    | _ => simp [Admin.IsCallRef] at hcr
  have hpc := Expand.func_ok hdc hec
  obtain ⟨tvs, trtl, rfl, hvs, htr⟩ := forall₂_split_left hvs'
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub C.toTypeCtx ((it.params ++ tvs) ++ [trt])
      ((T ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hC.types hM hsub hMs
    simpa using this
  obtain ⟨hX, htrs⟩ := forall₂_append_eq_len hall rfl
  have htrc : Sub C.toTypeCtx trt (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub C.toTypeCtx rt (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : RefI (.ref false (Ty.defHeap fi.type)) := by
    simpa [RefI, HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fi.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok, hs0⟩
    · exact (ref_toEmpty hΔ hsubrt hI₀ hdcok).1
    · have hIrt := (ref_toEmpty typesOk_empty hs0 hI₀ hok).2
      exact Sub.trans TypeCtx.ok_empty hok hs0 (ref_toEmpty hΔ hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fi.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, hrsub⟩ := ds_func hfit hdc hheap he hec
  have hlen : tvs.length = psc.toList.length := by
    have e1 := hvs.length_eq
    have e2 := hpsub.length_eq
    simp only [Ty.length] at hn
    omega
  obtain ⟨hPT, htv⟩ := forall₂_append_eq_len hX hlen
  have hargs : List.Forall₂ (ValOk s) vs ps.toList :=
    valsOk_transfer hs hsT typesOk_empty (valsOk_transfer hs hsT hΔ hvs htv hpc.1) hpsub
      (Expand.func_ok hfit he).1
  exact ⟨it.params, T, rsc.toList, hP, hT, hpc.2, hPT, hrsub, hargs,
    fun s' new hnew => hrep (resultOk_weaken hpc.2) s' new hnew⟩

theorem closeVal_ok {C : Context} (hΔ : TypesOk C.toTypeCtx) {t : ValType}
    (h : TyOk C.toTypeCtx (C.closeVal t)) : TyOk {} (C.closeVal t) := by
  rcases t with n | v | ⟨nb, ht⟩
  · exact .num n
  · exact .vec v
  · cases ht with
    | abstract a =>
      simp only [Context.closeVal, liftVal, liftRef, liftHeap, Ty.substAll, Ty.subst] at h ⊢
      exact .refv (.ref (.abs a))
    | typeIdx x =>
      simp only [Context.closeVal, liftVal, liftRef, liftHeap, liftTypeIdx, Ty.substAll,
        Ty.subst, Subst.all] at h ⊢
      cases hx : C.types[x.toNat]? with
      | none =>
        simp only [List.getElem?_map, hx, Option.map_none, Option.getD_none] at h
        cases h with | refv h => cases h with | ref h => cases h with | use h =>
          cases h with | idx h => simp [hx] at h
      | some d =>
        simp only [List.getElem?_map, hx, Option.map_some, Option.getD_some]
        exact .refv (.ref (.use (.dt (hΔ.get hx))))

theorem local_default_ok {s : Store H} {C : Context} (hΔ : TypesOk C.toTypeCtx) {t : ValType}
    {lt : LocalType} (h : LocalOk C t lt) : LocalValOk s (defaultVal? (C.closeVal t)) lt := by
  cases h with
  | set hok hd =>
    have hok0 := closeVal_ok hΔ hok
    generalize C.closeVal t = u at hok0 hd ⊢
    cases u with
    | num n =>
      cases n with
      | int t => exact .set (.num ⟨.int t, 0⟩)
      | float t => exact .set (.num ⟨.float t, 0⟩)
    | vec v => cases v; exact .set (.vec 0)
    | refv r =>
      cases r with
      | ref n hh =>
        simp only [Defaultable] at hd
        subst hd
        exact .set (.ref (.sub .null hok0.refv_inv (.refNull .bot)))
    | botv => simp [Defaultable] at hd
  | unset hok hd =>
    have hn : defaultVal? (C.closeVal t) = none := by
      cases h' : defaultVal? (C.closeVal t) with
      | none => rfl
      | some v =>
        have := (defaultVal?_isSome_iff (C.closeVal t)).1 (by simp [h'])
        exact absurd this hd
    rw [hn]
    exact .unset (closeVal_ok hΔ hok)

theorem locals_set_ok {s : Store H} {vs : List Val} {ts : List CValType}
    (h : List.Forall₂ (ValOk s) vs ts) :
    List.Forall₂ (LocalValOk s) (vs.map some) (ts.map fun t => (⟨.set, t⟩ : LocalType)) := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (.set hv) ih

theorem locals_default_ok {s : Store H} {C : Context} (hΔ : TypesOk C.toTypeCtx)
    {ls : List ValType} {lts : List LocalType} (h : List.Forall₂ (LocalOk C) ls lts) :
    List.Forall₂ (LocalValOk s) (ls.map fun t => defaultVal? (C.closeVal t)) lts := by
  induction h with
  | nil => exact .nil
  | cons hl _ ih => exact .cons (local_default_ok hΔ hl) ih

/-- `Step/call_ref-func`: the new frame is typed by the callee's module context
(`Funcinst_ok`), its locals by the arguments and the declared locals' defaults. -/
theorem pres_callRefFunc {s : Store H} {f : Frame} {C : Context} {it : InstrType} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (hs : StoreOk s) (hsT : StoreTypesOk s) (hc : CtxOk s f C) (hC : C.Wf)
    (hcr : c.IsCallRef) (hcd : ∀ d, c = .callRefType d → TyOk {} d)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code)
    (h : AdminsOk s C (vals vs ++ [.ref (.func a), c]) it) :
    AdminsOk s C [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]] it := by
  obtain ⟨P, T, rsc, hP, hT, hrsc, hPT, hrsub, hargs, hrep⟩ :=
    callRef_front hs hsT hc hC hcr hcd hf he hn h
  have hfit := StoreOk.func_tyOk hs hf
  have hpr := Expand.func_ok hfit he
  have hfo := hs.funcs fi (List.mem_of_getElem? hf)
  cases hfo with
  | host _ _ hcode' => rw [hcode] at hcode'; cases hcode'
  | @wasm C₁ code' d' _ hm hcode' hfo hsd =>
    rw [hcode] at hcode'; cases hcode'
    cases hfo with
    | @mk ps' rs' lts hd' he' hl hb =>
      have hΔ₁ := ModuleInstOk.typesOk' hm
      obtain ⟨hloc0, hlab0, -, htypes⟩ := ModuleInstOk.ctx_fields hm
      have hd'ok : TyOk {} d' := hΔ₁.get hd'
      have hh := heap_toEmpty hΔ₁ (.defDef hsd) (a := Ty.use (.dt d')) hd'ok (.use (.dt hfit))
      obtain ⟨hps', hrs'⟩ := ds_func hd'ok hfit hh.1 he' he
      have hpr' := Expand.func_ok hd'ok he'
      have hargs' := valsOk_transfer hs hsT typesOk_empty hargs hps' hpr'.1
      -- the frame
      let L : List LocalType := ps'.toList.map (fun t => (⟨.set, t⟩ : LocalType)) ++ lts
      have hloc : List.Forall₂ (LocalValOk s) (Frame.forCall fi.module vs code.locals).locals L := by
        simp only [Frame.forCall, L]
        refine forall₂_append (locals_set_ok hargs') ?_
        have := locals_default_ok (s := s) hΔ₁ hl
        simpa [Context.closeVal, htypes] using this
      have hFr : FrameOk s (Frame.forCall fi.module vs code.locals)
          { C₁ with locals := C₁.locals ++ L } := ⟨C₁, L, hm, hloc, rfl⟩
      have hn' : rs'.toList.length = rs.length := by
        simpa [Ty.length] using hrs'.length_eq
      have hctx : ({ { C₁ with locals := C₁.locals ++ L } with return_ := some rs'.toList }).withLabel
          rs'.toList = C₁.funcBody ps'.toList rs'.toList lts := by
        simp [Context.withLabel, Context.funcBody, hloc0, hlab0, L]
      have hbody : AdminsOk s (C₁.funcBody ps'.toList rs'.toList lts) (expression code.body)
          (.plain [] rs'.toList) := AdminsOk.of_instrsOk hb
      rw [← hctx] at hbody
      have hlab : AdminOk s { { C₁ with locals := C₁.locals ++ L } with return_ := some rs'.toList }
          (.label rs.length [] (expression code.body)) (.plain [] rs'.toList) :=
        .label hn' (AdminsOk.id (resultOk_weaken hpr'.2)) hbody
      have hframe : AdminOk s C (.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]) (.plain [] rs'.toList) :=
        .frame hFr hn' (.single hlab) hpr'.2
      have hnew : AdminsOk s C [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]] ⟨P, [], P ++ rs'.toList⟩ := by
        simpa using AdminsOk.frame (AdminsOk.single hframe) hP
      exact hrep s _ (subk hnew (ResultSub.refl _ _)
        (ResultSub.append hPT (resultSub_weaken (ResultSub.trans TypeCtx.ok_empty hpr.2 hrs' hrsub)))
        hP (ResultOk.append hT (resultOk_weaken hrsc)))

/-- `Step/call_ref-hostfunc-res`, using the host contract `HostOk`. -/
theorem pres_callRefHost {host : HostSemantics H} {s s' : Store H} {f : Frame} {C : Context}
    {it : InstrType} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
    {ps rs : Ty (.list .val)} {hh : H} {r : Result}
    (hhost : HostOk host) (hs : StoreOk s) (hsT : StoreTypesOk s) (hc : CtxOk s f C) (hC : C.Wf)
    (hcr : c.IsCallRef) (hcd : ∀ d, c = .callRefType d → TyOk {} d)
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host hh)
    (hres : host hh s vs (.returned s' r))
    (h : AdminsOk s C (vals vs ++ [.ref (.func a), c]) it) :
    StoreOk s' ∧ Extend s s' ∧ AdminsOk s' C r.toAdmin it := by
  obtain ⟨P, T, rsc, hP, hT, hrsc, hPT, hrsub, hargs, hrep⟩ :=
    callRef_front hs hsT hc hC hcr hcd hf he hn h
  have hfit := StoreOk.func_tyOk hs hf
  have hpr := Expand.func_ok hfit he
  obtain ⟨-, hout⟩ := hhost s fi hh vs ps rs hs (List.mem_of_getElem? hf) hcode he hargs
  obtain ⟨hs', hext, hrt⟩ := hout _ hres
  refine ⟨hs', hext, hrep s' _ ?_⟩
  have hRes : ResultSub C.toTypeCtx (P ++ rs.toList) (T ++ rsc) :=
    ResultSub.append hPT (resultSub_weaken hrsub)
  have hInst : InstrTypeOk C (.plain P (T ++ rsc)) :=
    ⟨hP, ResultOk.append hT (resultOk_weaken hrsc), by simp⟩
  cases r with
  | values vs' =>
    have hv : AdminsOk s' C (vals vs') ⟨[], [], rs.toList⟩ :=
      AdminsOk.of_vals hrt (resultOk_weaken hpr.2)
    show AdminsOk s' C (vals vs') _
    exact subk (by simpa using AdminsOk.frame hv hP) (ResultSub.refl _ _) hRes hP hInst.2.1
  | throw a' =>
    obtain ⟨e, he'⟩ := hrt
    show AdminsOk s' C [.ref (.exn a'), .plain .throwRef] _
    have h1 : AdminsOk s' C [.ref (.exn a')] ⟨P, [], P ++ [.refv (.ref false (.abs .exn))]⟩ := by
      simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.exn he'))) hP
    have h2 : AdminsOk s' C [.plain .throwRef]
        ⟨P ++ [.refv (.ref false (.abs .exn))], [], T ++ rsc⟩ :=
      subk (.single (.plain (.throwRef hInst)))
        (ResultSub.append (ResultSub.refl _ _) (.cons (.refv (.refNull .heapRefl)) .nil))
        (ResultSub.refl _ _) (ResultOk.append hP (rok1 (.refv (.ref (.abs _))))) hInst.2.1
    exact seqk h1 h2
  | trap => exact .single (.trap hInst)

/-! ## Frame contexts are well-formed -/

theorem externAddr_typeOk {s : Store H} (hs : StoreOk s) {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) :
    match xt with
    | .tag d => TyOk {} d
    | .global g => TyOk {} g.type
    | .table t => TyOk {} t.element
    | .func d => TyOk {} d
    | .mem _ => True := by
  induction h with
  | tag h => exact (hs.tags _ (List.mem_of_getElem? h)).1
  | global h => exact (hs.globals _ (List.mem_of_getElem? h)).1
  | mem _ => trivial
  | table h => exact (hs.tables _ (List.mem_of_getElem? h)).1.2
  | func h => exact StoreOk.func_tyOk hs h
  | sub _ hok _ _ =>
    cases hok with
    | tag h => exact h.1
    | global h => exact h
    | mem _ => trivial
    | table h => exact h.2
    | func h _ => exact h

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {b : β} (hb : b ∈ m) : ∃ a ∈ l, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, by simp [ha], h⟩

theorem valOk_tyOk {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {v : Val}
    {t : CValType} (h : ValOk s v t) : TyOk {} t := by
  cases h with
  | num v => exact .num _
  | vec b => exact .vec _
  | ref h => exact .refv (refOk_tyOk hs hsT h)

theorem frame_ctx_wf {s : Store H} (hs : StoreOk s) (hsT : StoreTypesOk s) {fr : Frame}
    {C' : Context} (hf : FrameOk s fr C') {ts : List CValType} (hts : ResultOk {} ts) :
    ({ C' with return_ := some ts } : Context).Wf := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  have hΔ := ModuleInstOk.typesOk' hm
  cases hm with
  | mk _ htags hglobals hfuncs _ htables _ helems =>
    refine ⟨hΔ.ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨a, -, hx⟩ := forall₂_mem_right htags hd
      exact TyOk.of_empty _ (externAddr_typeOk hs hx)
    · intro g hg
      obtain ⟨a, -, hx⟩ := forall₂_mem_right hglobals hg
      exact TyOk.of_empty _ (externAddr_typeOk hs hx)
    · intro t ht
      obtain ⟨a, -, hx⟩ := forall₂_mem_right htables ht
      exact TyOk.of_empty _ (externAddr_typeOk hs hx)
    · intro d hd
      obtain ⟨a, -, hx⟩ := forall₂_mem_right hfuncs hd
      exact TyOk.of_empty _ (externAddr_typeOk hs hx)
    · intro lt hlt
      simp only [List.nil_append] at hlt
      obtain ⟨v, -, hv⟩ := forall₂_mem_right hl hlt
      cases hv with
      | set h => exact TyOk.of_empty _ (valOk_tyOk hs hsT h)
      | unset h => exact TyOk.of_empty _ h
    · intro ts' h; simp at h
    · intro ts' h
      simp only [Option.some.injEq] at h
      subst h
      exact resultOk_weaken hts
    · intro rt hrt
      obtain ⟨a, -, ei, -, hei, rfl⟩ := forall₂_mem_right helems hrt
      exact TyOk.of_empty _ hei.1

/-! ## The checker does not depend on a context for valid closed types -/

theorem reach_indep {Δ : TypeCtx} {P Q : DefType → Bool}
    (hPQ : ∀ e, TyOk {} e → P e = Q e) :
    ∀ (n : Nat) (d : DefType), TyOk {} d → Δ.reach P n d = ({} : TypeCtx).reach Q n d
  | 0, d, hd => by simp only [TypeCtx.reach]; exact hPQ d hd
  | n + 1, d, hd => by
    simp only [TypeCtx.reach]
    rw [hPQ d hd]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    have key : ∀ u ∈ supersOf d, ∃ e, u = .dt e ∧ TyOk {} e := by
      intro u hu
      cases hun : unrolldt d with
      | none => simp [supersOf, hun] at hu
      | some st =>
        cases st with
        | sub fin sups ct =>
          simp only [supersOf, hun, Ty.supers] at hu
          exact use_dt_of_empty (TyOk.unroll_super hd hun hu)
    constructor
    · rintro ⟨u, hu, h⟩
      obtain ⟨e, rfl, he⟩ := key u hu
      refine ⟨_, hu, ?_⟩
      simp only [TypeCtx.resolve] at h ⊢
      rw [← reach_indep hPQ n e he]; exact h
    · rintro ⟨u, hu, h⟩
      obtain ⟨e, rfl, he⟩ := key u hu
      refine ⟨_, hu, ?_⟩
      simp only [TypeCtx.resolve] at h ⊢
      rw [reach_indep hPQ n e he]; exact h

theorem clos_of_empty {k : TKind} {t : Ty k} (h : TyOk {} t) (T : List DefType) :
    t.clos T = t :=
  Ty.substAll_closed (freeIdx_of_empty h) _

theorem checkDef_indep {Δ : TypeCtx} {d₁ d₂ : DefType} (h1 : TyOk {} d₁) (h2 : TyOk {} d₂) :
    Δ.checkDef d₁ d₂ = ({} : TypeCtx).checkDef d₁ d₂ := by
  simp only [TypeCtx.checkDef]
  have hf : Δ.fuel d₁ = ({} : TypeCtx).fuel d₁ := by
    simp [TypeCtx.fuel, freeIdx_of_empty h1]
  rw [hf]
  refine reach_indep (fun e he => ?_) _ _ h1
  simp [clos_of_empty he, clos_of_empty h2]

theorem checkHeap_indep {Δ : TypeCtx} {a b : CHeapType} (ha : TyOk {} a) (hb : TyOk {} b) :
    Δ.checkHeap a b = ({} : TypeCtx).checkHeap a b := by
  cases a with
  | bot => cases b <;> rfl
  | abs x =>
    cases b with
    | abs y => rfl
    | bot => rfl
    | use u =>
      obtain ⟨e, rfl, -⟩ := use_dt_of_empty hb
      rfl
  | use u =>
    obtain ⟨e, rfl, he⟩ := use_dt_of_empty ha
    cases b with
    | abs y => rfl
    | bot => rfl
    | use u' =>
      obtain ⟨e', rfl, he'⟩ := use_dt_of_empty hb
      simp only [TypeCtx.checkHeap, TypeCtx.resolve]
      exact checkDef_indep he he'

theorem checkVal_indep {Δ : TypeCtx} {a b : CValType} (ha : TyOk {} a) (hb : TyOk {} b) :
    Δ.checkVal a b = ({} : TypeCtx).checkVal a b := by
  cases a <;> cases b <;> try rfl
  rename_i r₁ r₂
  cases r₁ with
  | ref n₁ h₁ =>
    cases r₂ with
    | ref n₂ h₂ =>
      simp only [TypeCtx.checkVal, TypeCtx.checkRef]
      rw [checkHeap_indep ha.refv_inv.ref_inv hb.refv_inv.ref_inv]

/-- In a context with valid types and no `RECS`, subtyping between types valid in `{}`
holds in `{}`. -/
theorem val_sub_toEmpty_norecs {Δ : TypeCtx} (hΔ : TypesOk Δ) (hr : Δ.recs = [])
    {a b : CValType} (ha : TyOk {} a) (hb : TyOk {} b) (h : Sub Δ a b) : Sub {} a b := by
  have hc := Sub.complete hΔ.ok hr h (TyOk.of_empty Δ ha) (TyOk.of_empty Δ hb)
  simp only [Sub.checkK] at hc
  rw [checkVal_indep ha hb] at hc
  exact Sub.check_sound (k := .val) hc

theorem results_sub_toEmpty_norecs {Δ : TypeCtx} (hΔ : TypesOk Δ) (hr : Δ.recs = [])
    {a b : List CValType} (ha : ResultOk {} a) (hb : ResultOk {} b) (h : ResultSub Δ a b) :
    ResultSub {} a b := by
  induction h with
  | nil => exact .nil
  | cons h _ ih =>
    exact .cons (val_sub_toEmpty_norecs hΔ hr (ha _ (by simp)) (hb _ (by simp)) h)
      (ih (fun t ht => ha t (by simp [ht])) (fun t ht => hb t (by simp [ht])))

/-! ## `return_call_ref` out of a frame -/

/-- `Step_read/return_call_ref-frame-addr`, for the principal typing of the frame.

Stated for the components of a frame typing (`Instr_ok2/frame`) whose frame context
has no `RECS` (`hR`, see `FrameOk.recs_nil`). An index-annotated `RETURN_CALL_REF y`
is resolved against the exited frame's module (`Admin.retToCallIn`); a runtime
annotation must be valid in `{}` (`hcd`). -/
theorem pres_returnCallRefFrameAddr {s : Store H} {f : Frame} {C : Context} {fr : Frame}
    {C' : Context} {ts : List CValType} {vs' vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
    (hs : StoreOk s) (hsT : StoreTypesOk s) (hc : CtxOk s f C) (_hC : C.Wf)
    (hcr : c.IsReturnCallRef) (hcd : ∀ d, c = .returnCallRefType d → TyOk {} d)
    (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length)
    (hfr : FrameOk s fr C') (hR : C'.recs = []) (hts : ResultOk {} ts)
    (hb : AdminsOk s { C' with return_ := some ts }
      (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) (.plain [] ts)) :
    AdminsOk s C (vals vs ++ [.ref (.func a), c.retToCallIn fr.module]) (.plain [] ts) := by
  have hW := frame_ctx_wf hs hsT hfr hts
  have hΔ3 : TypesOk ({ C' with return_ := some ts } : Context).toTypeCtx := by
    show TypesOk C'.toTypeCtx
    exact FrameOk.typesOk' hfr
  have hΔ := CtxOk.typesOk' hc
  have e0 : vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      (vals (vs' ++ vs ++ [.ref (.func a)]) ++ [c]) ++ rest := by
    simp [vals, Val.toAdmin]
  rw [e0] at hb
  obtain ⟨m, ys₁, ys₂, hpre, -, -⟩ := AdminsOk.append_inv hW (.inr (resultOk_weaken hts)) hb
  obtain ⟨tvs'', it₁, M, T, hc1, hvs'', hsub, hM, hT, hMs, -, -⟩ :=
    redex_rep hW (returnCallRef_inits hcr) hpre
  obtain ⟨dc, psc, rsc, rs', t₃, t₄, hec, hret, hrs, hok, rfl, h1, h2⟩ :=
    inv_returnCallRef hcr hc1
  simp only [Option.some.injEq] at hret
  subst hret
  have hdc : TyOk {} dc := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsReturnCallRef] at hcr
      exact hΔ3.get (h1 _ rfl)
    | returnCallRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      exact hcd _ rfl
    | _ => simp [Admin.IsReturnCallRef] at hcr
  have hpc := Expand.func_ok hdc hec
  obtain ⟨tvsA, trtl, rfl, hvsA, htr⟩ := forall₂_split_left hvs''
  obtain ⟨tvsP, tvs, rfl, hvsP, hvs⟩ := forall₂_split_left hvsA
  obtain ⟨trt, rfl, htr1⟩ : ∃ trt, trtl = [trt] ∧ ValOk s (.ref (.func a)) trt := by
    cases htr with | cons h hnil => cases hnil; exact ⟨_, rfl, h⟩
  have hall : ResultSub ({ C' with return_ := some ts } : Context).toTypeCtx
      ((tvsP ++ tvs) ++ [trt]) (((T ++ t₃) ++ psc.toList) ++ [Ty.refT true (Ty.defHeap dc)]) := by
    have := ResultSub.trans hW.types hM hsub hMs
    simpa using this
  obtain ⟨hX, htrs⟩ := forall₂_append_eq_len hall rfl
  have htrc : Sub ({ C' with return_ := some ts } : Context).toTypeCtx trt
      (Ty.refT true (Ty.defHeap dc)) := by
    cases htrs with | cons h _ => exact h
  obtain ⟨rt, rfl, hrt⟩ : ∃ rt, trt = .refv rt ∧ RefOk s (.func a) rt := by
    cases htr1 with | ref h => exact ⟨_, rfl, h⟩
  have hsubrt : Sub ({ C' with return_ := some ts } : Context).toTypeCtx rt
      (.ref true (Ty.defHeap dc)) := by
    cases htrc with | refv h => exact h
  have hfit := StoreOk.func_tyOk hs hf
  obtain ⟨rt₀, e, hrt0, -⟩ := hrt.principal
  simp only [Ref.type?, hf, Option.map_some, Option.some.injEq] at e
  subst e
  have hI₀ : RefI (.ref false (Ty.defHeap fn.type)) := by
    simpa [RefI, HeapI, Ty.defHeap] using hfit
  have hdcok : TyOk {} (Ty.ref true (Ty.defHeap dc)) := .ref (.use (.dt hdc))
  have hsub0 : Sub {} (Ty.ref false (Ty.defHeap fn.type)) (.ref true (Ty.defHeap dc)) := by
    rcases hrt0 with rfl | ⟨hok', hs0⟩
    · exact (ref_toEmpty hΔ3 hsubrt hI₀ hdcok).1
    · have hIrt := (ref_toEmpty typesOk_empty hs0 hI₀ hok').2
      exact Sub.trans TypeCtx.ok_empty hok' hs0 (ref_toEmpty hΔ3 hsubrt hIrt hdcok).1
  have hheap : Sub {} (Ty.defHeap fn.type) (Ty.defHeap dc) := by
    cases hsub0 with | refNull h => exact h
  obtain ⟨hpsub, -⟩ := ds_func hfit hdc hheap he hec
  have hlen : tvs.length = psc.toList.length := by
    have e1 := hvs.length_eq
    have e2 := hpsub.length_eq
    simp only [Ty.length] at hn
    omega
  obtain ⟨-, htv⟩ := forall₂_append_eq_len hX hlen
  -- the reduct, in the caller's context
  have hpcC := Expand.func_ok (TyOk.of_empty C.toTypeCtx hdc) hec
  have hvsc : List.Forall₂ (ValOk s) vs psc.toList := valsOk_transfer hs hsT hΔ3 hvs htv hpc.1
  have hv : AdminsOk s C (vals vs) ⟨[], [], psc.toList⟩ := AdminsOk.of_vals hvsc hpcC.1
  have hr1 : AdminsOk s C [.ref (.func a)] ⟨psc.toList, [], psc.toList ++
      [.refv (.ref false (Ty.defHeap fn.type))]⟩ := by
    simpa using AdminsOk.frame (AdminsOk.single (AdminOk.ref (C := C) (RefOk.func hf))) hpcC.1
  have hcall : AdminOk s C (c.retToCallIn fr.module)
      (.plain (psc.toList ++ [Ty.refT true (Ty.defHeap dc)]) rsc.toList) := by
    cases c with
    | plain i =>
      cases i <;> simp [Admin.IsReturnCallRef] at hcr
      rename_i y
      have hy := h1 y rfl
      have hC3 : ({ C' with return_ := some ts } : Context).types = fr.module.types := by
        obtain ⟨C₀, lts, hm, -, rfl⟩ := hfr
        exact (ModuleInstOk.ctx_fields hm).2.2.2
      have hyF : fr.module.types[y.toNat]? = some dc := by
        simp only [Context.type?] at hy
        rw [← hC3]; exact hy
      simp only [Admin.retToCallIn, hyF]
      exact .callRefType hdc hec
    | returnCallRefType d =>
      obtain ⟨rfl, -⟩ := h2 _ rfl
      exact .callRefType hdc hec
    | _ => simp [Admin.IsReturnCallRef] at hcr
  have hc2 : AdminsOk s C [c.retToCallIn fr.module]
      ⟨psc.toList ++ [.refv (.ref false (Ty.defHeap fn.type))], [], rsc.toList⟩ :=
    subk (.single hcall)
      (ResultSub.append (ResultSub.refl _ _)
        (.cons (.refv (.refNull (Sub.weakenE hheap _ rfl fun _ _ h => by simp at h))) .nil))
      (ResultSub.refl _ _)
      (ResultOk.append hpcC.1 (rok1 (.refv (.ref (.use (.dt (TyOk.of_empty _ hfit))))))) hpcC.2
  have hrts : ResultSub {} rsc.toList ts :=
    results_sub_toEmpty_norecs hΔ3 hR hpc.2 hts hrs
  have hall' := seqk hv (seqk hr1 hc2)
  exact subk hall' (ResultSub.refl _ _) (resultSub_weaken hrts) (by simp) (resultOk_weaken hts)

end Silmaril.Wasm.Execution.Core.PC
