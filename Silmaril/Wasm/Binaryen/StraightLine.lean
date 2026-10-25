module

public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.SeqTyping
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Soundness.PresVariable
public import Silmaril.Wasm.Execution.Core.Soundness.AggregatePres
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux

@[expose] public section

/-! # Straight-line code runs to completion

The fragment `slInstr`: no loops, calls, returns, exceptions, memories or tables;
blocks, `if`, branches to enclosing labels, locals and globals are allowed. Typed
code of the fragment, run from a typed state, **reaches** values (of the result
type, in a typed state), a trap, or a branch to one of its free labels
(`sl_eval`). The proof constructs the run by induction on the size of the code;
it never inverts `Step`.

The run is typed loosely: a stack value is typed *below* its static type
(`ValLe`), and the frame's locals are typed below the context's (`StOk`), so
subsumption is free; stores into globals use the runtime strengthening
`ValOk.ctxSubAgg` of the Core soundness proof.

This is what the `trapsNeverHappen` trimming of `Vacuum` (code before an
`unreachable` traps or reaches it) and `block_unwrap` (a body without branches to
its block finishes or traps) need.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

/-! ## The fragment -/

/-- Instructions of the straight-line fragment, recursively. -/
def slInstr : Instr → Prop
  | .nop | .unreachable | .drop | .select _ | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _ | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .br _ | .brIf _ | .brTable _ _ => True
  | .block _ body => ∀ i ∈ body.attach, slInstr i.val
  | .if_ _ b₁ b₂ => (∀ i ∈ b₁.attach, slInstr i.val) ∧ ∀ i ∈ b₂.attach, slInstr i.val
  | _ => False
termination_by i => sizeOf i
decreasing_by
  all_goals simp_wf
  all_goals have h := List.sizeOf_lt_of_mem i.property
  all_goals omega

theorem slInstr_block {bt : BlockType} {body : List Instr} :
    slInstr (.block bt body) ↔ ∀ i ∈ body, slInstr i := by
  rw [slInstr]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_attach _ _), fun h i _ => h i.1 i.2⟩

theorem slInstr_if {bt : BlockType} {b₁ b₂ : List Instr} :
    slInstr (.if_ bt b₁ b₂) ↔ (∀ i ∈ b₁, slInstr i) ∧ ∀ i ∈ b₂, slInstr i := by
  rw [slInstr]
  exact ⟨fun h => ⟨fun i hi => h.1 ⟨i, hi⟩ (List.mem_attach _ _),
    fun i hi => h.2 ⟨i, hi⟩ (List.mem_attach _ _)⟩,
    fun h => ⟨fun i _ => h.1 i.1 i.2, fun i _ => h.2 i.1 i.2⟩⟩

theorem mem_instrLabels_block {bt : BlockType} {body : List Instr} {l : Nat}
    (h : l ∈ instrsLabels body) (hl : l ≠ 0) : l - 1 ∈ instrLabels (.block bt body) := by
  rw [instrLabels]
  simp only [unbind, List.mem_filterMap]
  refine ⟨l, ?_, by simp [hl]⟩
  obtain ⟨j, hj, hl'⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_attach _ _, hl'⟩

theorem mem_instrLabels_if {bt : BlockType} {b₁ b₂ : List Instr} {l : Nat}
    (h : l ∈ instrsLabels b₁ ∨ l ∈ instrsLabels b₂) (hl : l ≠ 0) :
    l - 1 ∈ instrLabels (.if_ bt b₁ b₂) := by
  rw [instrLabels]
  simp only [unbind, List.mem_filterMap]
  refine ⟨l, ?_, by simp [hl]⟩
  rcases h with h | h
  · obtain ⟨j, hj, hl'⟩ := List.mem_flatMap.mp h
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_attach _ _, hl'⟩)
  · obtain ⟨j, hj, hl'⟩ := List.mem_flatMap.mp h
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨j, hj⟩, List.mem_attach _ _, hl'⟩)

/-! ## Loose runtime typing -/

variable {H : Type}

/-- A runtime value typed below a static type. -/
def ValLe (s : Store H) (Δ : TypeCtx) (v : Val) (t : CValType) : Prop :=
  ∃ t₀, ValOk s v t₀ ∧ Sub Δ t₀ t

theorem ValLe.of_valOk {s : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (h : ValOk s v t) :
    ValLe s Δ v t := ⟨t, h, Sub.refl Δ (k := .val) trivial t⟩

theorem ValLe.sub {s : Store H} {Δ : TypeCtx} {v : Val} {t t' : CValType} (hΔ : Δ.Ok)
    (ht : TyOk Δ t) (h : ValLe s Δ v t) (hs : Sub Δ t t') : ValLe s Δ v t' := by
  obtain ⟨t₀, hv, h₀⟩ := h
  exact ⟨t₀, hv, Sub.trans hΔ ht h₀ hs⟩

theorem ValLe.extend {s s' : Store H} {Δ : TypeCtx} {v : Val} {t : CValType} (he : Extend s s')
    (h : ValLe s Δ v t) : ValLe s' Δ v t := by
  obtain ⟨t₀, hv, h₀⟩ := h
  exact ⟨t₀, hv.extend he, h₀⟩

theorem ValLe.int_inv {s : Store H} {Δ : TypeCtx} {v : Val} {T : IntType}
    (h : ValLe s Δ v (.num (.int T))) : ∃ x : BitVec T.width, v = Val.num ⟨.int T, x⟩ := by
  obtain ⟨t₀, hv, hs⟩ := h
  cases hv with
  | num n =>
    obtain ⟨ty, b⟩ := n
    cases hs
    exact ⟨b, rfl⟩
  | vec b => cases hs
  | ref h => cases hs

theorem ValLe.i32_inv {s : Store H} {Δ : TypeCtx} {v : Val} (h : ValLe s Δ v .i32) :
    ∃ c, v = Val.i32 c := ValLe.int_inv (T := .i32) h

theorem forall₂_valLe_extend {s s' : Store H} {Δ : TypeCtx} {vs : List Val} {ts : List CValType}
    (he : Extend s s') (h : List.Forall₂ (ValLe s Δ) vs ts) : List.Forall₂ (ValLe s' Δ) vs ts :=
  h.imp fun _ _ h => h.extend he

theorem forall₂_valLe_sub {s : Store H} {Δ : TypeCtx} (hΔ : Δ.Ok) :
    ∀ {vs : List Val} {ts ts' : List CValType}, ResultOk Δ ts →
      List.Forall₂ (ValLe s Δ) vs ts → ResultSub Δ ts ts' → List.Forall₂ (ValLe s Δ) vs ts'
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, hok, .cons h t, .cons hs ts =>
    .cons (h.sub hΔ (hok _ (by simp)) hs)
      (forall₂_valLe_sub hΔ (fun t' ht' => hok t' (by simp [ht'])) t ts)

theorem forall₂_split {α β : Type _} {R : α → β → Prop} {vs : List α} {ts₁ ts₂ : List β}
    (h : List.Forall₂ R vs (ts₁ ++ ts₂)) :
    ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ List.Forall₂ R vs₁ ts₁ ∧ List.Forall₂ R vs₂ ts₂ := by
  induction ts₁ generalizing vs with
  | nil => exact ⟨[], vs, rfl, .nil, h⟩
  | cons t ts₁ ih =>
    cases h with
    | cons hv h' =>
      obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := ih h'
      exact ⟨_ :: vs₁, vs₂, rfl, .cons hv h₁, h₂⟩

theorem forall₂_append {α β : Type _} {R : α → β → Prop} {a b : List α} {c d : List β}
    (h₁ : List.Forall₂ R a c) (h₂ : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) :=
  List.rel_append h₁ h₂

/-- The runtime state fits context `C` loosely: a valid store, and a frame typed by
`C` (without labels or return) with local types below `C`'s and at least as
initialised. -/
def StOk (C : Context) (s : Store H) (f : Frame) : Prop :=
  StoreOk s ∧ ∃ lts : List LocalType,
    FrameOk s f { C with labels := [], return_ := none, locals := lts } ∧
    lts.length = C.locals.length ∧
    ∀ (y : Nat) (a : LocalType), C.locals[y]? = some a → ∃ b : LocalType, lts[y]? = some b ∧
      Sub C.toTypeCtx b.type a.type ∧ (a.init = .set → b.init = .set)

theorem StOk.of_frameOk {C : Context} {s : Store H} {f : Frame} (hs : StoreOk s)
    (hf : FrameOk s f { C with labels := [], return_ := none }) : StOk C s f :=
  ⟨hs, C.locals, hf, rfl, fun _ a h => ⟨a, h, Sub.refl _ (k := .val) trivial _, id⟩⟩

theorem StOk.withLabel {C : Context} {s : Store H} {f : Frame} (h : StOk C s f)
    (t : List CValType) : StOk (C.withLabel t) s f := h

theorem StOk.extend {C : Context} {s s' : Store H} {f : Frame} (h : StOk C s f)
    (hs' : StoreOk s') (he : Extend s s') : StOk C s' f := by
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  exact ⟨hs', lts, FrameOk.extend_of_storeOk hs he hf, hl, hle⟩

theorem length_eq_of_isSome {α : Type _} {l₁ l₂ : List α}
    (h : ∀ y : Nat, (l₁[y]?).isSome = (l₂[y]?).isSome) : l₁.length = l₂.length := by
  have key : ∀ y : Nat, y < l₁.length ↔ y < l₂.length := by
    intro y
    have hy := h y
    by_cases h₁ : y < l₁.length <;> by_cases h₂ : y < l₂.length
    · exact ⟨fun _ => h₂, fun _ => h₁⟩
    · rw [List.getElem?_eq_getElem h₁, List.getElem?_eq_none (Nat.le_of_not_lt h₂)] at hy
      simp at hy
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt h₁), List.getElem?_eq_getElem h₂] at hy
      simp at hy
    · exact ⟨fun h => absurd h h₁, fun h => absurd h h₂⟩
  rcases Nat.lt_trichotomy l₁.length l₂.length with hlt | heq | hlt
  · exact absurd ((key _).mpr hlt) (Nat.lt_irrefl _)
  · exact heq
  · exact absurd ((key _).mp hlt) (Nat.lt_irrefl _)

theorem initLocals_length (C : Context) (xs : List Nat) :
    (C.initLocals xs).locals.length = C.locals.length :=
  length_eq_of_isSome fun _ => Context.initLocals_isSome

/-- Forgetting initialisations (and changing labels or return). -/
theorem StOk.weaken {D D' : Context} {s : Store H} {f : Frame} (h : StOk D s f)
    (hagree : ({ D' with labels := [], return_ := none, locals := [] } : Context) =
      { D with labels := [], return_ := none, locals := [] })
    (hlen : D'.locals.length = D.locals.length) (hL : LocalsLe D'.locals D.locals) :
    StOk D' s f := by
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  have hT : D'.toTypeCtx = D.toTypeCtx := by
    have := congrArg Context.toTypeCtx hagree
    simpa using this
  refine ⟨hs, lts, ?_, by omega, fun y a hy => ?_⟩
  · have e : ({ D' with labels := [], return_ := none, locals := lts } : Context) =
        { D with labels := [], return_ := none, locals := lts } := by
      have := congrArg (fun E : Context => ({ E with locals := lts } : Context)) hagree
      simpa using this
    rw [e]; exact hf
  · obtain ⟨i, hi, hset⟩ := hL y a hy
    obtain ⟨b, hb, hsub, hb'⟩ := hle y _ hi
    refine ⟨b, hb, by rw [hT]; exact hsub, fun ha => hb' (hset ha)⟩

theorem StOk.weaken_initLocals {C : Context} {xs ys : List Nat} {s : Store H} {f : Frame}
    (h : StOk (C.initLocals xs) s f)
    (hL : LocalsLe (C.initLocals ys).locals (C.initLocals xs).locals) :
    StOk (C.initLocals ys) s f := by
  refine h.weaken ?_ (by rw [initLocals_length, initLocals_length]) hL
  rw [C.initLocals_eq_with ys, C.initLocals_eq_with xs]
  try rfl

theorem StOk.forget_initLocals {C : Context} {xs : List Nat} {s : Store H} {f : Frame}
    (h : StOk (C.initLocals xs) s f) : StOk C s f := by
  refine h.weaken (D' := C) ?_ (by rw [initLocals_length]) ?_
  · rw [C.initLocals_eq_with xs]
    try rfl
  · intro y a hy
    rw [Context.initLocals_locals]
    split
    · exact ⟨.set, by simp [hy], fun _ => rfl⟩
    · exact ⟨a.init, by rw [hy], id⟩

theorem StOk.frame_ctx {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) :
    ∃ Cf, StateOk s f Cf ∧ Cf.toTypeCtx = C.toTypeCtx ∧ Cf.globals = C.globals ∧
      Cf.types = C.types := by
  obtain ⟨hs, lts, hf, -, -⟩ := h
  exact ⟨_, ⟨hs, hf⟩, rfl, rfl, rfl⟩

theorem StOk.types {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) :
    C.types = f.module.types := by
  obtain ⟨Cf, hst, -, -, hT⟩ := h.frame_ctx
  rw [← hT]; exact StateOk.types hst

theorem StOk.local_get {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) {x : Nat}
    {t : CValType} (hx : C.locals[x]? = some ⟨.set, t⟩) :
    ∃ v, f.locals[x]? = some (some v) ∧ ValLe s C.toTypeCtx v t := by
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  obtain ⟨b, hb, hsub, hset⟩ := hle x _ hx
  obtain ⟨C₀, -, hloc, hC⟩ := hf.invVar
  obtain ⟨ov, hov, hlv⟩ := forall₂_getVar hloc (i := x) (b := b) (by simpa using hb)
  obtain ⟨bi, bt⟩ := b
  simp only at hset hsub
  have hbi := hset (by simp)
  subst hbi
  cases hlv with
  | set hv => exact ⟨_, hov, _, hv, hsub⟩

theorem StOk.local_bound {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) {x : Nat}
    {lt : LocalType} (hx : C.locals[x]? = some lt) : x < f.locals.length := by
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  obtain ⟨C₀, -, hloc, -⟩ := hf.invVar
  have h₁ := List.Forall₂.length_eq hloc
  have h₂ : x < C.locals.length := (List.getElem?_eq_some_iff.mp hx).1
  simp only at h₁
  omega

theorem StOk.local_set {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) {x : LocalIdx}
    {i : Init} {t t₀ : CValType} {v : Val} (hx : C.locals[x.toNat]? = some ⟨i, t⟩)
    (hv : ValOk s v t₀) (hsub : Sub C.toTypeCtx t₀ t) :
    StOk (C.initLocals [x.toNat]) s (f.setLocal x v) := by
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  obtain ⟨C₀, hm, hloc, hC⟩ := hf.invVar
  refine ⟨hs, lts.set x.toNat ⟨.set, t₀⟩, ?_, by rw [List.length_set, initLocals_length, hl], ?_⟩
  · refine ⟨C₀, lts.set x.toNat ⟨.set, t₀⟩, hm, ?_, ?_⟩
    · exact forall₂_setVar hloc x.toNat (.set hv)
    · rw [hm.locals_nilVar, List.nil_append]
      have e1 : ({ (C.initLocals [x.toNat]) with
            labels := [], return_ := none, locals := lts.set x.toNat ⟨.set, t₀⟩ } : Context) =
          { C with labels := [], return_ := none, locals := lts.set x.toNat ⟨.set, t₀⟩ } := by
        rw [C.initLocals_eq_with [x.toNat]]
        try rfl
      rw [e1]
      have := congrArg (fun E : Context => ({ E with locals := lts.set x.toNat ⟨.set, t₀⟩ } :
        Context)) hC
      simpa using this
  · intro y a hy
    rw [Context.initLocals_locals] at hy
    by_cases hyx : y = x.toNat
    · subst hyx
      simp [hx] at hy
      subst hy
      have hlt : x.toNat < lts.length := by
        have := (List.getElem?_eq_some_iff.mp hx).1
        omega
      refine ⟨⟨.set, t₀⟩, by simp [hlt], ?_, fun _ => rfl⟩
      simpa [Context.initLocals_toTypeCtx] using hsub
    · simp [hyx] at hy
      obtain ⟨b, hb, hsub', hset⟩ := hle y a hy
      refine ⟨b, ?_, by simpa using hsub', hset⟩
      rw [List.getElem?_set]
      simp [Ne.symm hyx, hb]

/-- Locals are untouched by store changes. -/
theorem StOk.global_get {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) {x : GlobalIdx}
    {gt : CGlobalType} (hx : C.globals[x.toNat]? = some gt) :
    ∃ a g, s.global? f x = some (a, g) ∧ ValLe s C.toTypeCtx g.value gt.type := by
  obtain ⟨hs, lts, hf, -, -⟩ := h
  obtain ⟨a, ha, hxa⟩ := hf.globalVar (C := { C with labels := [], return_ := none, locals := lts })
    hx
  obtain ⟨gi, hgi, -, -, hfw, -⟩ := hxa.global_invVar hs a _ rfl rfl
  refine ⟨a, gi, by simp [Store.global?, ha, hgi], .of_valOk ?_⟩
  exact hfw _ (hs.globals gi (List.mem_of_getElem? hgi)).2

theorem StOk.global_set {C : Context} {s : Store H} {f : Frame} (h : StOk C s f) {x : GlobalIdx}
    {t : CValType} {v : Val} (hx : C.globals[x.toNat]? = some ⟨.var, t⟩)
    (hv : ValLe s C.toTypeCtx v t) :
    ∃ a g, s.global? f x = some (a, g) ∧ StoreOk (s.setGlobal a v) ∧
      Extend s (s.setGlobal a v) ∧ StOk C (s.setGlobal a v) f := by
  have hst := h
  obtain ⟨hs, lts, hf, hl, hle⟩ := h
  obtain ⟨a, ha, hxa⟩ := hf.globalVar (C := { C with labels := [], return_ := none, locals := lts })
    hx
  obtain ⟨gi, hgi, htok, hmut, -, hbw⟩ := hxa.global_invVar hs a _ rfl rfl
  obtain ⟨t₀, hv₀, hsub⟩ := hv
  have hvt : ValOk s v t :=
    ValOk.ctxSubAgg (C := { C with labels := [], return_ := none, locals := lts }) ⟨hs, hf⟩
      ⟨hs.structsClosed, hs.arraysClosed⟩ hv₀ hsub htok
  have hvg : ValOk s v gi.type.type := hbw rfl v hvt
  obtain ⟨hs', he⟩ := StoreOk.setGlobalVar hs hgi (by simpa using hmut) hvg
  exact ⟨a, gi, by simp [Store.global?, ha, hgi], hs', he, hst.extend hs' he⟩

/-! ## Outcomes -/

/-- How a run of typed straight-line code at `it` in `C` ends (`s` is the initial
store; `Lab` holds of the labels a branch may leave by). -/
def Outcome (C : Context) (it : InstrType) (Lab : Nat → Prop) (s s' : Store H) (f' : Frame)
    (code : List Admin) : Prop :=
  Extend s s' ∧
  ((∃ ws, code = vals ws ∧ List.Forall₂ (ValLe s' C.toTypeCtx) ws it.results ∧
      StOk (C.initLocals it.inits) s' f') ∨
   code = [.trap] ∨
   (∃ (l : LabelIdx) (ws₀ ws : List Val) (junk : List Admin) (lt : List CValType),
      code = vals ws₀ ++ vals ws ++ .plain (.br l) :: junk ∧ Lab l.toNat ∧
      C.labels[l.toNat]? = some lt ∧ List.Forall₂ (ValLe s' C.toTypeCtx) ws lt ∧ StOk C s' f'))

theorem Outcome.mono {C : Context} {it : InstrType} {Lab Lab' : Nat → Prop} {s s' : Store H}
    {f' : Frame} {code : List Admin} (h : Outcome C it Lab s s' f' code)
    (hL : ∀ l, Lab l → Lab' l) : Outcome C it Lab' s s' f' code := by
  obtain ⟨he, hv | ht | ⟨l, ws₀, ws, junk, lt, hc, hl, hlt, hws, hst⟩⟩ := h
  · exact ⟨he, .inl hv⟩
  · exact ⟨he, .inr (.inl ht)⟩
  · exact ⟨he, .inr (.inr ⟨l, ws₀, ws, junk, lt, hc, hL _ hl, hlt, hws, hst⟩)⟩

/-- Typed straight-line code runs to an `Outcome`. -/
def EvalSpec (P : Profile) (L : List Instr) : Prop :=
  ∀ (C : Context) (it : InstrType), C.Wf → InstrsOk C L it →
  ∀ {H : Type} (s : Store H) (f : Frame) (vs : List Val), StOk C s f →
    List.Forall₂ (ValLe s C.toTypeCtx) vs it.params →
    ∃ s' f' code, Steps P closedHost ⟨s, f, vals vs ++ expression L⟩ ⟨s', f', code⟩ ∧
      Outcome C it (· ∈ instrsLabels L) s s' f' code

/-- One instruction run from its own typing. -/
def HeadSpec (P : Profile) (C : Context) (i : Instr) (it : InstrType) : Prop :=
  ∀ {H : Type} (s : Store H) (f : Frame) (vs : List Val), StOk C s f →
    List.Forall₂ (ValLe s C.toTypeCtx) vs it.params →
    ∃ s' f' code, Steps P closedHost ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f', code⟩ ∧
      Outcome C it (· ∈ instrLabels i) s s' f' code

section Run

variable {P : Profile}

theorem steps_mid' {s s' : Store H} {f f' : Frame} (vs : List Val) {is is' : List Admin}
    (rest : List Admin) (h : Steps P closedHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P closedHost ⟨s, f, vals vs ++ (is ++ rest)⟩ ⟨s', f', vals vs ++ (is' ++ rest)⟩ := by
  simpa [List.append_assoc] using Steps.ctxtInstrs (vs := vs) (rest := rest) h

theorem steps_app {s s' : Store H} {f f' : Frame} {is is' : List Admin} (rest : List Admin)
    (h : Steps P closedHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P closedHost ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  simpa [vals] using Steps.ctxtInstrs (vs := []) (rest := rest) h

theorem steps_trap' (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin) :
    Steps P closedHost ⟨s, f, vals vs ++ (.trap :: rest)⟩ ⟨s, f, [.trap]⟩ := by
  by_cases h : vs ≠ [] ∨ rest ≠ []
  · have := Step.trapInstrs (P := P) (host := closedHost) (s := s) (f := f) h
    simp only [List.append_assoc, List.singleton_append] at this
    exact this.steps
  · simp only [ne_eq, not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl

/-- A value outcome of a pure step from typed operands. -/
theorem pure_val {C : Context} {s : Store H} {f : Frame} {vs ws : List Val} {it : InstrType}
    {i : Instr} (hst : StOk C s f) (hinits : it.inits = [])
    (hstep : Steps P closedHost ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s, f, vals ws⟩)
    (hws : List.Forall₂ (ValLe s C.toTypeCtx) ws it.results) :
    ∃ s' f' code, Steps P closedHost ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f', code⟩ ∧
      Outcome C it (· ∈ instrLabels i) s s' f' code :=
  ⟨s, f, vals ws, hstep, Extend.refl hst.1, .inl ⟨ws, rfl, hws, by rw [hinits]; exact hst⟩⟩

theorem trap_out {C : Context} {s : Store H} {f : Frame} {vs : List Val} {it : InstrType}
    {i : Instr} (hst : StOk C s f)
    (hstep : Steps P closedHost ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s, f, [.trap]⟩) :
    ∃ s' f' code, Steps P closedHost ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s', f', code⟩ ∧
      Outcome C it (· ∈ instrLabels i) s s' f' code :=
  ⟨s, f, [.trap], hstep, Extend.refl hst.1, .inr (.inl rfl)⟩

theorem single_step {s s' : Store H} {f f' : Frame} {is is' : List Admin}
    (h : Step P closedHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Steps P closedHost ⟨s, f, is⟩ ⟨s', f', is'⟩ := h.steps

end Run

/-! ## One instruction -/

section Head

variable {P : Profile}

theorem forall₂_singleton_inv {α β : Type _} {R : α → β → Prop} {vs : List α} {t : β}
    (h : List.Forall₂ R vs [t]) : ∃ v, vs = [v] ∧ R v t := by
  rcases h with _ | ⟨hv, _ | _⟩
  exact ⟨_, rfl, hv⟩

theorem forall₂_triple_inv {α β : Type _} {R : α → β → Prop} {vs : List α} {a b c : β}
    (h : List.Forall₂ R vs [a, b, c]) :
    ∃ x y z, vs = [x, y, z] ∧ R x a ∧ R y b ∧ R z c := by
  rcases h with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
  exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

theorem forall₂_nil_inv {α β : Type _} {R : α → β → Prop} {vs : List α}
    (h : List.Forall₂ R vs ([] : List β)) : vs = [] := by
  cases h; rfl

theorem head_parametric {C : Context} {i : Instr} {it : InstrType}
    (hi : ParametricInstrOk C i it) : HeadSpec P C i it := by
  intro H s f vs hst hvs
  cases hi with
  | nop =>
    rw [forall₂_nil_inv hvs]
    exact pure_val (ws := []) hst rfl
      (by simpa [vals] using (Step.parametric (P := P) (host := closedHost) (s := s) (f := f)
        ParametricStep.nop).steps) .nil
  | unreachable h =>
    refine trap_out hst ?_
    have h₁ : Steps P closedHost ⟨s, f, vals vs ++ [.plain .unreachable]⟩
        ⟨s, f, vals vs ++ [.trap]⟩ := by
      simpa using steps_mid' (P := P) vs [] (Step.parametric (host := closedHost) (s := s)
        (f := f) ParametricStep.unreachable).steps
    exact h₁.trans (by simpa using steps_trap' (P := P) s f vs [])
  | drop ht =>
    obtain ⟨v, rfl, -⟩ := forall₂_singleton_inv hvs
    exact pure_val (ws := []) hst rfl
      (by simpa [vals] using (Step.parametric (P := P) (host := closedHost) (s := s) (f := f)
        (ParametricStep.drop v)).steps) .nil
  | @selectExpl t ht =>
    obtain ⟨v₁, v₂, cv, rfl, h₁, h₂, h₃⟩ := forall₂_triple_inv hvs
    obtain ⟨b, rfl⟩ := ValLe.i32_inv h₃
    by_cases hb : b = 0
    · subst hb
      exact pure_val (ws := [v₂]) hst rfl
        (by simpa [vals, constI32] using (Step.parametric (P := P) (host := closedHost) (s := s)
          (f := f) (ParametricStep.selectFalse v₁ v₂ (some [t]))).steps) (.cons h₂ .nil)
    · exact pure_val (ws := [v₁]) hst rfl
        (by simpa [vals, constI32] using (Step.parametric (P := P) (host := closedHost) (s := s)
          (f := f) (ParametricStep.selectTrue (v₁ := v₁) (v₂ := v₂) (ts := some [t]) hb)).steps)
        (.cons h₁ .nil)
  | selectImpl ht hs hnv =>
    obtain ⟨v₁, v₂, cv, rfl, h₁, h₂, h₃⟩ := forall₂_triple_inv hvs
    obtain ⟨b, rfl⟩ := ValLe.i32_inv h₃
    by_cases hb : b = 0
    · subst hb
      exact pure_val (ws := [v₂]) hst rfl
        (by simpa [vals, constI32] using (Step.parametric (P := P) (host := closedHost) (s := s)
          (f := f) (ParametricStep.selectFalse v₁ v₂ none)).steps) (.cons h₂ .nil)
    · exact pure_val (ws := [v₁]) hst rfl
        (by simpa [vals, constI32] using (Step.parametric (P := P) (host := closedHost) (s := s)
          (f := f) (ParametricStep.selectTrue (v₁ := v₁) (v₂ := v₂) (ts := none) hb)).steps)
        (.cons h₁ .nil)

theorem head_numeric {C : Context} {i : Instr} {it : InstrType} (hsl : slInstr i)
    (hi : NumericInstrOk C i it) : HeadSpec P C i it := by
  intro H s f vs hst hvs
  cases hi with
  | intConst t b =>
    rw [forall₂_nil_inv hvs]
    exact pure_val (ws := [Val.num ⟨.int t, b⟩]) hst rfl (by simpa [vals, Val.toAdmin] using .refl)
      (.cons (.of_valOk (.num _)) .nil)
  | intUnOp h =>
    rename_i t op
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hvs
    obtain ⟨x, rfl⟩ := ValLe.int_inv hv
    exact pure_val (ws := [Val.num ⟨.int t, intUnOp t op x⟩]) hst rfl
      (by simpa [vals, Val.toAdmin] using (Step.numeric (P := P) (host := closedHost) (s := s)
        (f := f) (NumericStep.intUnOp (t := t) (op := op) (x := x))).steps)
      (.cons (.of_valOk (.num _)) .nil)
  | intBinOp t op =>
    rcases hvs with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValLe.int_inv h₁
    obtain ⟨y, rfl⟩ := ValLe.int_inv h₂
    cases hz : intBinOp t op x y with
    | ok z =>
      exact pure_val (ws := [Val.num ⟨.int t, z⟩]) hst rfl
        (by simpa [vals, Val.toAdmin] using (Step.numeric (P := P) (host := closedHost) (s := s)
          (f := f) (NumericStep.intBinOp hz)).steps)
        (.cons (.of_valOk (.num _)) .nil)
    | error e =>
      exact trap_out hst
        (by simpa [vals, Val.toAdmin] using (Step.numeric (P := P) (host := closedHost) (s := s)
          (f := f) (NumericStep.intBinOpTrap hz)).steps)
  | intTestOp t op =>
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hvs
    obtain ⟨x, rfl⟩ := ValLe.int_inv hv
    exact pure_val (ws := [Val.i32 (intTestOp t op x)]) hst rfl
      (by simpa [vals, Val.toAdmin, constI32] using (Step.numeric (P := P) (host := closedHost)
        (s := s) (f := f) (NumericStep.intTestOp (t := t) (op := op) (x := x))).steps)
      (.cons (.of_valOk (.num _)) .nil)
  | intRelOp t op =>
    rcases hvs with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨x, rfl⟩ := ValLe.int_inv h₁
    obtain ⟨y, rfl⟩ := ValLe.int_inv h₂
    exact pure_val (ws := [Val.i32 (intRelOp t op x y)]) hst rfl
      (by simpa [vals, Val.toAdmin, constI32] using (Step.numeric (P := P) (host := closedHost)
        (s := s) (f := f) (NumericStep.intRelOp (t := t) (op := op) (x := x) (y := y))).steps)
      (.cons (.of_valOk (.num _)) .nil)
  | _ => simp [slInstr] at hsl

theorem head_variable {C : Context} {i : Instr} {it : InstrType}
    (hi : VariableInstrOk C i it) : HeadSpec P C i it := by
  intro H s f vs hst hvs
  cases hi with
  | @localGet x t h =>
    rw [forall₂_nil_inv hvs]
    obtain ⟨v, hv, hle⟩ := hst.local_get h
    exact pure_val (ws := [v]) hst rfl
      (by simpa [vals] using (Step.variable (P := P) (host := closedHost)
        (VariableStep.localGet (s := s) (f := f) (x := x) hv)).steps) (.cons hle .nil)
  | @localSet x i t h =>
    obtain ⟨v, rfl, t₀, hv, hsub⟩ := forall₂_singleton_inv hvs
    have hb := hst.local_bound h
    refine ⟨s, f.setLocal x v, [], ?_, Extend.refl hst.1, .inl ⟨[], rfl, .nil, ?_⟩⟩
    · simpa [vals] using (Step.variable (P := P) (host := closedHost)
        (VariableStep.localSet (s := s) (f := f) (x := x) (v := v) hb)).steps
    · exact hst.local_set h hv hsub
  | @localTee x i t h =>
    obtain ⟨v, rfl, t₀, hv, hsub⟩ := forall₂_singleton_inv hvs
    have hb := hst.local_bound h
    refine ⟨s, f.setLocal x v, vals [v], ?_, Extend.refl hst.1,
      .inl ⟨[v], rfl, .cons ⟨t₀, hv, hsub⟩ .nil, hst.local_set h hv hsub⟩⟩
    have h₁ := (Step.variable (P := P) (host := closedHost)
        (VariableStep.localTee (s := s) (f := f) (x := x) (v := v))).steps
    have h₂ := steps_mid' (P := P) [v] [] (Step.variable (P := P) (host := closedHost)
        (VariableStep.localSet (s := s) (f := f) (x := x) (v := v) hb)).steps
    have h₁' : Steps P closedHost ⟨s, f, vals [v] ++ [.plain (.localTee x)]⟩
        ⟨s, f, vals [v] ++ ([v.toAdmin, .plain (.localSet x)] ++ [])⟩ := by
      simpa [vals] using h₁
    exact h₁'.trans (by simpa [vals] using h₂)
  | @globalGet x m t h =>
    rw [forall₂_nil_inv hvs]
    obtain ⟨a, g, hg, hle⟩ := hst.global_get h
    exact pure_val (ws := [g.value]) hst rfl
      (by simpa [vals] using (Step.variable (P := P) (host := closedHost)
        (VariableStep.globalGet (s := s) (f := f) (x := x) hg)).steps) (.cons hle .nil)
  | @globalSet x t h =>
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hvs
    obtain ⟨a, g, hg, hs', he, hst'⟩ := hst.global_set h hv
    refine ⟨s.setGlobal a v, f, [], ?_, he, .inl ⟨[], rfl, .nil, hst'⟩⟩
    simpa [vals] using (Step.variable (P := P) (host := closedHost)
      (VariableStep.globalSet (s := s) (f := f) (x := x) (v := v) hg)).steps

/-- A block: its body runs inside the label; values, a trap or a branch come out. -/
theorem block_run {C : Context} (hC : C.Wf) {bt : BlockType} {body : List Instr}
    {t₁ t₂ : List CValType} {xs : List Nat} (ihb : EvalSpec P body) (hbt : BlockTypeOk C bt t₁ t₂)
    (hb : InstrsOk (C.withLabel t₂) body ⟨t₁, xs, t₂⟩) {s : Store H} {f : Frame} {vs : List Val}
    (hst : StOk C s f) (hvs : List.Forall₂ (ValLe s C.toTypeCtx) vs t₁) :
    ∃ s' f' code, Steps P closedHost ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ ⟨s', f', code⟩ ∧
      Outcome C (.plain t₁ t₂) (fun l => l + 1 ∈ instrsLabels body) s s' f' code := by
  obtain ⟨t₁', t₂', hbt', hl₁, hl₂⟩ := blockType_of_types hst.types hbt
  have hm : vs.length = t₁'.length := by rw [hl₁]; exact List.Forall₂.length_eq hvs
  have h₁ := (Step.block (P := P) (host := closedHost) (s := s) (f := f) (body := body) hbt'
    hm).steps
  obtain ⟨s', f', code, hrun, he, hout⟩ := ihb (C.withLabel t₂) ⟨t₁, xs, t₂⟩
    (wf_withLabel hC (hbt.regular hC).2) hb s f vs (hst.withLabel t₂) hvs
  have h₂ := Steps.label (n := t₂'.length) (cont := []) hrun
  rcases hout with ⟨ws, rfl, hws, hst'⟩ | rfl | ⟨l, ws₀, ws, junk, lt, rfl, hlab, hlt, hws, hst'⟩
  · refine ⟨s', f', vals ws,
      h₁.trans (h₂.trans (Step.labelVals (P := P) (host := closedHost)).steps),
      he, .inl ⟨ws, rfl, hws, ?_⟩⟩
    exact (hst'.forget_initLocals : StOk (C.withLabel t₂) s' f')
  · exact ⟨s', f', [.trap],
      h₁.trans (h₂.trans (Step.trapLabel (P := P) (host := closedHost)).steps),
      he, .inr (.inl rfl)⟩
  · by_cases hl0 : l.toNat = 0
    · have hlt' : lt = t₂ := by
        simp only [Context.withLabel, hl0, List.getElem?_cons_zero, Option.some.injEq] at hlt
        exact hlt.symm
      subst hlt'
      have hn : ws.length = t₂'.length := by rw [hl₂]; exact List.Forall₂.length_eq hws
      have h₃ := (Step.brLabelZero (P := P) (host := closedHost) (s := s') (f := f')
        (cont := []) (vs' := ws₀) (rest := junk) hl0 hn).steps
      refine ⟨s', f', vals ws, h₁.trans (h₂.trans ?_), he, .inl ⟨ws, rfl, hws, ?_⟩⟩
      · simpa [expression] using h₃
      · exact (hst' : StOk C s' f')
    · have hpos : 0 < l.toNat := Nat.pos_of_ne_zero hl0
      have h₃ := (Step.brLabelSucc (P := P) (host := closedHost) (s := s') (f := f')
        (n := t₂'.length) (cont := []) (vs := ws₀ ++ ws) (rest := junk) hpos).steps
      refine ⟨s', f', vals (ws₀ ++ ws) ++ [.plain (.br (labelPred l))], h₁.trans (h₂.trans ?_), he,
        .inr (.inr ⟨labelPred l, ws₀, ws, [], lt, by simp, ?_, ?_, hws, hst'⟩)⟩
      · simpa using h₃
      · show (labelPred l).toNat + 1 ∈ instrsLabels body
        have : (labelPred l).toNat = l.toNat - 1 := rfl
        rw [this, Nat.sub_add_cancel hpos]; exact hlab
      · have : (labelPred l).toNat = l.toNat - 1 := rfl
        rw [this]
        obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨l.toNat - 1, by omega⟩
        simp only [Context.withLabel, hk, List.getElem?_cons_succ] at hlt
        simpa [hk] using hlt

/-- The structured cases of one instruction. -/
theorem head_control {C : Context} (hC : C.Wf) {i : Instr} {it : InstrType} (hsl : slInstr i)
    (ih : ∀ body : List Instr, sizeOf body < sizeOf i → (∀ j ∈ body, slInstr j) →
      EvalSpec P body)
    (hi : InstrOk C i it) : HeadSpec P C i it := by
  intro H s f vs hst hvs
  cases hi with
  | parametric h => exact head_parametric h s f vs hst hvs
  | numeric h => exact head_numeric hsl h s f vs hst hvs
  | «variable» h => exact head_variable h s f vs hst hvs
  | @block _ bt body t₁ t₂ xs hbt hb =>
    have hsl' := slInstr_block.mp hsl
    obtain ⟨s', f', code, hrun, hout⟩ := block_run hC
      (ih body (by simp) hsl') hbt hb hst hvs
    exact ⟨s', f', code, hrun, hout.mono fun l hl => by
      simpa using mem_instrLabels_block (bt := bt) hl (by omega)⟩
  | @if_ _ bt b₁ b₂ t₁ t₂ xs₁ xs₂ hbt h₁ h₂ =>
    obtain ⟨hsl₁, hsl₂⟩ := slInstr_if.mp hsl
    obtain ⟨args, cs, rfl, hargs, hcs⟩ := forall₂_split hvs
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hcs
    obtain ⟨c, rfl⟩ := ValLe.i32_inv hv
    by_cases hc0 : c = 0
    · subst hc0
      obtain ⟨s', f', code, hrun, hout⟩ := block_run hC
        (ih b₂ (by simp) hsl₂) hbt h₂ hst hargs
      have h₀ := steps_mid' (P := P) args [] (Step.ifFalse (P := P) (host := closedHost) (s := s)
        (f := f) (bt := bt) (b₁ := b₁) (b₂ := b₂)).steps
      refine ⟨s', f', code, Relation.ReflTransGen.trans (by simpa [vals, constI32] using h₀) hrun,
        hout.mono ?_⟩
      intro l hl
      simpa using mem_instrLabels_if (bt := bt) (b₁ := b₁) (.inr hl) (by omega)
    · obtain ⟨s', f', code, hrun, hout⟩ := block_run hC
        (ih b₁ (by simp; omega) hsl₁) hbt h₁ hst hargs
      have h₀ := steps_mid' (P := P) args [] (Step.ifTrue (P := P) (host := closedHost) (s := s)
        (f := f) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc0).steps
      refine ⟨s', f', code, Relation.ReflTransGen.trans (by simpa [vals, constI32] using h₀) hrun,
        hout.mono ?_⟩
      intro l hl
      simpa using mem_instrLabels_if (bt := bt) (b₂ := b₂) (.inl hl) (by omega)
  | @br _ l ts t₁ t₂ hl hok =>
    obtain ⟨vs₁, ws, rfl, -, hws⟩ := forall₂_split hvs
    refine ⟨s, f, vals vs₁ ++ vals ws ++ .plain (.br l) :: [], by simpa using .refl,
      Extend.refl hst.1, .inr (.inr ⟨l, vs₁, ws, [], ts, rfl, ?_, hl, hws, hst⟩)⟩
    simp
  | @brIf _ l ts hl =>
    obtain ⟨ws, cs, rfl, hws, hcs⟩ := forall₂_split hvs
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hcs
    obtain ⟨c, rfl⟩ := ValLe.i32_inv hv
    by_cases hc0 : c = 0
    · subst hc0
      refine ⟨s, f, vals ws, ?_, Extend.refl hst.1, .inl ⟨ws, rfl, hws, hst⟩⟩
      simpa [vals, constI32] using steps_mid' (P := P) ws [] (Step.brIfFalse (P := P)
        (host := closedHost) (s := s) (f := f) (l := l)).steps
    · refine ⟨s, f, vals [] ++ vals ws ++ .plain (.br l) :: [], ?_, Extend.refl hst.1,
        .inr (.inr ⟨l, [], ws, [], ts, rfl, by simp, hl, hws, hst⟩)⟩
      simpa [vals, constI32] using steps_mid' (P := P) ws [] (Step.brIfTrue (P := P)
        (host := closedHost) (s := s) (f := f) (l := l) hc0).steps
  | @brTable _ ls l' ts t₁ t₂ hls hl' hok =>
    obtain ⟨vs₁₂, cs, rfl, h₁₂, hcs⟩ := forall₂_split (ts₁ := t₁ ++ ts) hvs
    obtain ⟨vs₁, ws, rfl, -, hws⟩ := forall₂_split h₁₂
    obtain ⟨v, rfl, hv⟩ := forall₂_singleton_inv hcs
    obtain ⟨c, rfl⟩ := ValLe.i32_inv hv
    have hts : ResultOk C.toTypeCtx ts := fun t ht => hok.1 t (by simp [ht])
    have hgo : ∀ l : LabelIdx, l.toNat ∈ instrLabels (.brTable ls l') →
        (∃ lt, C.labels[l.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt) →
        Steps P closedHost ⟨s, f, vals (vs₁ ++ ws ++ [Val.i32 c]) ++ [.plain (.brTable ls l')]⟩
          ⟨s, f, vals vs₁ ++ vals ws ++ [.plain (.br l)]⟩ →
        ∃ s' f' code, Steps P closedHost
            ⟨s, f, vals (vs₁ ++ ws ++ [Val.i32 c]) ++ [.plain (.brTable ls l')]⟩ ⟨s', f', code⟩ ∧
          Outcome C (.plain (t₁ ++ ts ++ [.i32]) t₂) (· ∈ instrLabels (.brTable ls l')) s s' f'
            code := by
      intro l hmem ⟨lt, hlt, hsub⟩ hrun
      exact ⟨s, f, _, hrun, Extend.refl hst.1, .inr (.inr ⟨l, vs₁, ws, [], lt, by simp, hmem, hlt,
        forall₂_valLe_sub hC.types hts hws hsub, hst⟩)⟩
    cases hlk : ls[c.toNat]? with
    | some l =>
      refine hgo l ?_ (hls l (List.mem_of_getElem? hlk)) ?_
      · simp only [instrLabels, List.mem_cons, List.mem_map]
        exact .inr ⟨l, List.mem_of_getElem? hlk, rfl⟩
      · simpa [vals, constI32, List.append_assoc] using steps_mid' (P := P) (vs₁ ++ ws) []
          (Step.brTableLt (P := P) (host := closedHost) (s := s) (f := f) (l' := l') hlk).steps
    | none =>
      have hge : ls.length ≤ c.toNat := by simpa using hlk
      refine hgo l' (by simp) hl' ?_
      simpa [vals, constI32, List.append_assoc] using steps_mid' (P := P) (vs₁ ++ ws) []
        (Step.brTableGe (P := P) (host := closedHost) (s := s) (f := f) (ls := ls) (l' := l')
          hge).steps
  | vector h => cases h <;> simp [slInstr] at hsl
  | memory h => cases h <;> simp [slInstr] at hsl
  | table h => cases h <;> simp [slInstr] at hsl
  | reference h => cases h <;> simp [slInstr] at hsl
  | _ => simp [slInstr] at hsl

end Head

/-! ## Sequences -/

section Seq

variable {P : Profile}

theorem sl_nil : EvalSpec P [] := by
  intro C it hC h H s f vs hst hvs
  obtain ⟨hsub, hinit⟩ := InstrsOk.nil_inv hC h
  have hreg := InstrsOk.regular hC h
  refine ⟨s, f, vals vs, by simpa [expression] using .refl, Extend.refl hst.1,
    .inl ⟨vs, rfl, forall₂_valLe_sub hC.types hreg.1 hvs hsub, ?_⟩⟩
  rw [Context.initLocals_of_set hinit]
  exact hst

/-- One instruction at any typing, from its own typings. -/
theorem sl_one {i : Instr} (hh : ∀ C it, C.Wf → InstrOk C i it → HeadSpec P C i it) :
    EvalSpec P [i] := by
  intro C it hC h H s f vs hst hvs
  obtain ⟨ts, it₀, hts, hi, hsub⟩ := single_inv' hC h
  have hreg := InstrsOk.regular hC h
  have hreg₀ := InstrOk.regular hC hi
  have hvs' := forall₂_valLe_sub hC.types hreg.1 hvs hsub.1
  obtain ⟨vs₁, vs₂, rfl, h₁, h₂⟩ := forall₂_split hvs'
  obtain ⟨s', f', code, hrun, he, hout⟩ := hh C it₀ hC hi s f vs₂ hst h₂
  have hrun' : Steps P closedHost ⟨s, f, vals (vs₁ ++ vs₂) ++ expression [i]⟩
      ⟨s', f', vals vs₁ ++ (code ++ [])⟩ := by
    simpa [expression, List.append_assoc] using steps_mid' (P := P) vs₁ [] hrun
  rcases hout with ⟨ws, rfl, hws, hst'⟩ | rfl | ⟨l, ws₀, ws, junk, lt, rfl, hlab, hlt, hws, hst'⟩
  · refine ⟨s', f', vals (vs₁ ++ ws), by simpa using hrun', he, .inl ⟨vs₁ ++ ws, rfl, ?_, ?_⟩⟩
    · have := forall₂_append (forall₂_valLe_extend he h₁) hws
      exact forall₂_valLe_sub hC.types (Validation.ResultOk.append hts hreg₀.2.1) this hsub.2.1
    · refine hst'.weaken_initLocals ?_
      exact LocalsLe.initLocals_of_sub hsub.2.2
  · exact ⟨s', f', [.trap], hrun'.trans (by simpa using steps_trap' (P := P) s' f' vs₁ []), he,
      .inr (.inl rfl)⟩
  · refine ⟨s', f', vals (vs₁ ++ ws₀) ++ vals ws ++ .plain (.br l) :: junk, by simpa using hrun',
      he, .inr (.inr ⟨l, vs₁ ++ ws₀, ws, junk, lt, rfl, by simpa [instrsLabels] using hlab, hlt,
        hws, hst'⟩)⟩

theorem sl_cons {i : Instr} {rest : List Instr} (h₁ : EvalSpec P [i]) (h₂ : EvalSpec P rest) :
    EvalSpec P (i :: rest) := by
  intro C it hC h H s f vs hst hvs
  obtain ⟨m, xs₁, xs₂, hi, hr, hL⟩ := InstrsOk.split (is₁ := [i]) (is₂ := rest) hC h rfl
  obtain ⟨s₁, f₁, code₁, hrun₁, he₁, hout₁⟩ := h₁ C ⟨it.params, xs₁, m⟩ hC hi s f vs hst hvs
  have hlift : Steps P closedHost ⟨s, f, vals vs ++ expression (i :: rest)⟩
      ⟨s₁, f₁, code₁ ++ expression rest⟩ := by
    simpa [expression, List.append_assoc] using steps_app (P := P) (expression rest) hrun₁
  have hlab₁ : ∀ l, l ∈ instrsLabels [i] → l ∈ instrsLabels (i :: rest) := by
    intro l hl; simp only [instrsLabels, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hl ⊢; exact .inl hl
  rcases hout₁ with ⟨ws, rfl, hws, hst₁⟩ | rfl | ⟨l, ws₀, ws, junk, lt, rfl, hlab, hlt, hws', hst₁⟩
  · obtain ⟨s₂, f₂, code₂, hrun₂, he₂, hout₂⟩ := h₂ (C.initLocals xs₁) ⟨m, xs₂, it.results⟩
      (hC.initLocals _) hr s₁ f₁ ws hst₁ (by simpa using hws)
    refine ⟨s₂, f₂, code₂, hlift.trans hrun₂, he₁.trans he₂, ?_⟩
    rcases hout₂ with ⟨ws', rfl, hws₂, hst₂⟩ | rfl |
      ⟨l, ws₀, ws', junk, lt, rfl, hlab, hlt, hws₂, hst₂⟩
    · refine .inl ⟨ws', rfl, by simpa using hws₂, ?_⟩
      have := hst₂
      rw [← Context.initLocals_append] at this
      exact this.weaken_initLocals hL
    · exact .inr (.inl rfl)
    · refine .inr (.inr ⟨l, ws₀, ws', junk, lt, rfl, ?_, by simpa using hlt, by simpa using hws₂,
        hst₂.forget_initLocals⟩)
      simp only [instrsLabels, List.flatMap_cons, List.mem_append] at hlab ⊢
      exact .inr hlab
  · refine ⟨s₁, f₁, [.trap], hlift.trans ?_, he₁, .inr (.inl rfl)⟩
    simpa [vals] using steps_trap' (P := P) s₁ f₁ [] (expression rest)
  · refine ⟨s₁, f₁, vals ws₀ ++ vals ws ++ .plain (.br l) :: (junk ++ expression rest),
      by simpa using hlift, he₁, .inr (.inr ⟨l, ws₀, ws, junk ++ expression rest, lt, rfl,
        hlab₁ _ hlab, hlt, hws', hst₁⟩)⟩

/-- **Straight-line code runs to an outcome.** -/
theorem sl_eval : ∀ (n : Nat) (L : List Instr), sizeOf L ≤ n → (∀ i ∈ L, slInstr i) →
    EvalSpec P L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn hsl
    cases L with
    | nil => exact sl_nil
    | cons i rest =>
      simp only [List.cons.sizeOf_spec] at hn
      refine sl_cons (sl_one fun C it hC hi => head_control hC (hsl i (by simp)) ?_ hi)
        (ih (sizeOf rest) (by omega) rest le_rfl (fun j hj => hsl j (by simp [hj])))
      intro body hbody hslb
      exact ih (sizeOf body) (by omega) body le_rfl hslb

theorem sl_eval' (L : List Instr) (hsl : ∀ i ∈ L, slInstr i) : EvalSpec P L :=
  sl_eval (sizeOf L) L le_rfl hsl

end Seq

/-! ## The fragment on layer D -/

theorem mem_unbind_exists {m : Nat} {ns : List Nat} :
    m ∈ unbind ns ↔ ∃ n ∈ ns, n ≠ 0 ∧ n - 1 = m := by
  simp only [unbind, List.mem_filterMap]
  constructor
  · rintro ⟨n, hn, h⟩
    by_cases h0 : n = 0
    · simp [h0] at h
    · simp only [h0, ite_false, Option.some.injEq] at h
      exact ⟨n, hn, h0, h⟩
  · rintro ⟨n, hn, h0, rfl⟩
    exact ⟨n, hn, by simp [h0]⟩

theorem mem_attach_flatMap {n : Nat} {L : List Instr} :
    n ∈ (L.attach.flatMap fun i => instrLabels i.val) ↔ n ∈ instrsLabels L := by
  simp only [instrsLabels, List.mem_flatMap]
  constructor
  · rintro ⟨⟨j, hj⟩, -, h⟩
    exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj⟩, List.mem_attach _ _, h⟩

mutual
/-- Code in the analysed fragment without loops, calls or returns is straight-line. -/
theorem lower_sl : ∀ (e : BExpr), (effects e).any = false → (effects e).calls = false →
    (effects e).mayNotReturn = false → (effects e).branchesOut = false →
    ∀ i ∈ e.lower, slInstr i
  | .op i args, ha, hc, hm, hb => by
      simp only [effects, Effects.merge, Bool.or_eq_false_iff] at ha hc hm hb
      intro j hj
      simp only [BExpr.lower_op, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact lowerList_sl args ha.1 hc.1 hm.1 hb.1 j hj
      · have ha' := ha.2
        have hc' := hc.2
        have hb' := hb.2
        cases j <;> simp_all [instrEffects, Effects.top, slInstr]
  | .block _ body, ha, hc, hm, hb => by
      simp only [effects, Effects.unbindLabel] at ha hc hm hb
      intro j hj
      simp only [BExpr.lower, List.mem_singleton] at hj
      subst hj
      exact slInstr_block.mpr (lowerList_sl body ha hc hm hb)
  | .loop _ _, _, _, hm, _ => by simp [effects] at hm
  | .if_ _ c t e, ha, hc, hm, hb => by
      simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff] at ha hc hm hb
      intro j hj
      simp only [BExpr.lower, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact lowerList_sl c ha.1 hc.1 hm.1 hb.1 j hj
      · exact slInstr_if.mpr ⟨lowerList_sl t ha.2.1 hc.2.1 hm.2.1 hb.2.1,
          lowerList_sl e ha.2.2 hc.2.2 hm.2.2 hb.2.2⟩
  | .tryTable _ _ _, ha, _, _, _ => by simp [effects, Effects.top] at ha
theorem lowerList_sl : ∀ (es : List BExpr), (effectsList es).any = false →
    (effectsList es).calls = false → (effectsList es).mayNotReturn = false →
    (effectsList es).branchesOut = false → ∀ i ∈ BExpr.lowerList es, slInstr i
  | [], _, _, _, _ => by simp
  | e :: es, ha, hc, hm, hb => by
      simp only [effectsList, Effects.merge, Bool.or_eq_false_iff] at ha hc hm hb
      intro j hj
      simp only [BExpr.lowerList_cons, List.mem_append] at hj
      rcases hj with hj | hj
      · exact lower_sl e ha.1 hc.1 hm.1 hb.1 j hj
      · exact lowerList_sl es ha.2 hc.2 hm.2 hb.2 j hj
end

mutual
/-- The free labels of the lowering are break targets. -/
theorem lower_labels : ∀ (e : BExpr), (effects e).any = false →
    ∀ l ∈ instrsLabels e.lower, l ∈ (effects e).breakTargets
  | .op i args, ha => by
      simp only [effects, Effects.merge, Bool.or_eq_false_iff] at ha
      intro l hl
      simp only [BExpr.lower_op, instrsLabels, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append] at hl
      simp only [effects, Effects.merge, List.mem_append]
      rcases hl with hl | hl
      · exact .inl (lowerList_labels args ha.1 l hl)
      · right
        have ha' := ha.2
        cases i <;> simp_all [instrEffects, Effects.top, instrLabels]
  | .block _ body, ha => by
      simp only [effects, Effects.unbindLabel] at ha ⊢
      intro l hl
      simp only [BExpr.lower, instrsLabels, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at hl
      rw [instrLabels, mem_unbind_exists] at hl
      obtain ⟨n, hn, h0, rfl⟩ := hl
      exact mem_unbind_exists.mpr
        ⟨n, lowerList_labels body ha n (mem_attach_flatMap.mp hn), h0, rfl⟩
  | .loop _ body, ha => by
      simp only [effects, Effects.unbindLabel] at ha ⊢
      intro l hl
      simp only [BExpr.lower, instrsLabels, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at hl
      rw [instrLabels, mem_unbind_exists] at hl
      obtain ⟨n, hn, h0, rfl⟩ := hl
      exact mem_unbind_exists.mpr
        ⟨n, lowerList_labels body ha n (mem_attach_flatMap.mp hn), h0, rfl⟩
  | .if_ _ c t e, ha => by
      simp only [effects, Effects.merge, Effects.unbindLabel, Bool.or_eq_false_iff] at ha
      simp only [effects, Effects.merge, Effects.unbindLabel, List.mem_append]
      intro l hl
      simp only [BExpr.lower, instrsLabels, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append] at hl
      rcases hl with hl | hl
      · exact .inl (lowerList_labels c ha.1 l hl)
      · right
        rw [instrLabels, mem_unbind_exists] at hl
        obtain ⟨n, hn, h0, rfl⟩ := hl
        refine mem_unbind_exists.mpr ⟨n, ?_, h0, rfl⟩
        rcases List.mem_append.mp hn with hn | hn
        · exact List.mem_append_left _ (lowerList_labels t ha.2.1 n (mem_attach_flatMap.mp hn))
        · exact List.mem_append_right _ (lowerList_labels e ha.2.2 n (mem_attach_flatMap.mp hn))
  | .tryTable _ _ _, ha => by simp [effects, Effects.top] at ha
theorem lowerList_labels : ∀ (es : List BExpr), (effectsList es).any = false →
    ∀ l ∈ instrsLabels (BExpr.lowerList es), l ∈ (effectsList es).breakTargets
  | [], _ => by simp [instrsLabels]
  | e :: es, ha => by
      simp only [effectsList, Effects.merge, Bool.or_eq_false_iff] at ha
      simp only [effectsList, Effects.merge, List.mem_append]
      intro l hl
      simp only [BExpr.lowerList_cons, instrsLabels, List.flatMap_append, List.mem_append] at hl
      rcases hl with hl | hl
      · exact .inl (lower_labels e ha.1 l hl)
      · exact .inr (lowerList_labels es ha.2 l hl)
end

end Silmaril.Wasm.Binaryen
