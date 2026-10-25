module

public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.Pass.RewriteTyping

@[expose] public section

/-! # Local rewrite passes: from per-node equivalence to the pass

Infrastructure shared by the local rewrite passes (`Pass/Precompute.lean`,
a separate general peephole optimizer (not included in this package)):

* everything in `SeqRefines` depends on code only through its lowering
  (`SeqRefines.congr_lower`), so a node may be replaced by any tree with the same
  lowering (e.g. its flat form) for free;
* typing implications (`RTy.PresL`) lift through one-hole contexts
  (`presL_plug`) and to module validity (`BModule.withBody_ok`), which discharges
  the validity side condition of `SeqRefines.trans`;
* `star_seqEquiv`: a rewrite relation whose single contextual steps are
  equivalences and preserve typing yields an equivalence along any rewrite
  sequence (`SeqRefines.Star`), in both directions;
* small-step helpers: stepping under a value prefix, and reading the operand
  stack and the frame off `Fits`.

**Scope.** This module does not establish the legacy general results `mapBodies_exportEquiv`. The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics RTy

/-! ## Lowering congruence -/

@[simp] theorem BExpr.lower_block_eq (bt : BlockType) (b : List BExpr) :
    (BExpr.block bt b).lower = [.block bt (BExpr.lowerList b)] := by
  simp [BExpr.lower]

@[simp] theorem BExpr.lower_loop_eq (bt : BlockType) (b : List BExpr) :
    (BExpr.loop bt b).lower = [.loop bt (BExpr.lowerList b)] := by
  simp [BExpr.lower]

@[simp] theorem BExpr.lower_if_eq (bt : BlockType) (c t e : List BExpr) :
    (BExpr.if_ bt c t e).lower =
      BExpr.lowerList c ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)] := by
  simp [BExpr.lower]

@[simp] theorem BExpr.lower_tryTable_eq (bt : BlockType) (cs : List Catch) (b : List BExpr) :
    (BExpr.tryTable bt cs b).lower = [.tryTable bt cs (BExpr.lowerList b)] := by
  simp [BExpr.lower]

theorem BCtx.lowerList_plug_congr (K : BCtx) {a b : List BExpr}
    (h : BExpr.lowerList a = BExpr.lowerList b) :
    BExpr.lowerList (K.plug a) = BExpr.lowerList (K.plug b) := by
  induction K <;> simp_all [BCtx.plug]

theorem map_modifyAt_body {a b : List BExpr} (h : BExpr.lowerList a = BExpr.lowerList b) :
    ∀ (g : Nat) (fs : List BFunc),
      (modifyAt (fun f : BFunc => { f with body := a }) g fs).map
          (Declaration.Func.mapBody BExpr.lowerList) =
        (modifyAt (fun f : BFunc => { f with body := b }) g fs).map
          (Declaration.Func.mapBody BExpr.lowerList)
  | g, [] => by cases g <;> rfl
  | 0, x :: fs => by simp [modifyAt, Declaration.Func.mapBody, h]
  | n + 1, x :: fs => by simp [modifyAt, map_modifyAt_body h n fs]

theorem BModule.withBody_lower_congr (m : BModule) (g : Nat) {a b : List BExpr}
    (h : BExpr.lowerList a = BExpr.lowerList b) :
    (m.withBody g a).lower = (m.withBody g b).lower := by
  simp only [BModule.lower, BModule.withBody, map_modifyAt_body h]

/-- `SeqRefines` only sees lowerings. -/
theorem SeqRefines.congr_lower {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {C : Context} {it : InstrType} {a a' b b' : List BExpr}
    (ha : BExpr.lowerList a = BExpr.lowerList a') (hb : BExpr.lowerList b = BExpr.lowerList b')
    (h : SeqRefines R P C it a b) : SeqRefines R P C it a' b' := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨by unfold SeqOk; rw [← ha]; exact h₁, by unfold SeqOk; rw [← hb]; exact h₂, ?_⟩
  intro H host m g K hh ok₁ ok₂
  have e₁ := m.withBody_lower_congr g (K.lowerList_plug_congr ha)
  have e₂ := m.withBody_lower_congr g (K.lowerList_plug_congr hb)
  have ok₁' : (m.withBody g (K.plug a)).Ok := by unfold BModule.Ok; rw [e₁]; exact ok₁
  have ok₂' : (m.withBody g (K.plug b)).Ok := by unfold BModule.Ok; rw [e₂]; exact ok₂
  rw [← e₁, ← e₂]
  exact h₃ host m g K hh ok₁' ok₂'

theorem SeqEquiv.congr_lower {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {C : Context} {it : InstrType} {a a' b b' : List BExpr}
    (ha : BExpr.lowerList a = BExpr.lowerList a') (hb : BExpr.lowerList b = BExpr.lowerList b')
    (h : SeqEquiv R P C it a b) : SeqEquiv R P C it a' b' :=
  ⟨h.1.congr_lower ha hb, h.2.congr_lower hb ha⟩

theorem SeqEquiv.congr {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {C : Context} {it : InstrType} {a b : List BExpr} (h : SeqEquiv R P C it a b) (K : BCtx)
    {C' : Context} {it' : InstrType} (hK : SeqOk C' (K.plug a) it')
    (hK' : SeqOk C' (K.plug b) it') : SeqEquiv R P C' it' (K.plug a) (K.plug b) :=
  ⟨h.1.congr K hK hK', h.2.congr K hK' hK⟩

/-! ## Rewrite sequences -/

namespace SeqRefines.Star

variable {rule : List BExpr → List BExpr → Prop}

theorem trans' {a b c : List BExpr} (h₁ : Star rule a b) (h₂ : Star rule b c) :
    Star rule a c := by
  revert h₂
  induction h₁ with
  | refl => exact id
  | step h _ ih => exact fun h₂ => Star.step h (ih h₂)

theorem lift (K : BCtx) {a b : List BExpr} (h : Star rule a b) :
    Star rule (K.plug a) (K.plug b) := by
  induction h with
  | refl => exact Star.refl _
  | @step K' a' b' es h t ih =>
    rw [← BCtx.plug_comp]
    exact Star.step (K := K.comp K') h (by rw [BCtx.plug_comp]; exact ih)

theorem single {a b : List BExpr} (h : rule a b) : Star rule a b :=
  Star.step (K := .hole) h (Star.refl b)

end SeqRefines.Star

/-! ## Typing implications through contexts and modules -/

theorem presL_plug {a b : List BExpr} (h : PresL (BExpr.lowerList a) (BExpr.lowerList b)) :
    ∀ K : BCtx, PresL (BExpr.lowerList (K.plug a)) (BExpr.lowerList (K.plug b))
  | .hole => h
  | .seq pre k post => by
    simpa [BCtx.plug, List.append_assoc] using
      (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
  | .op i pre k post => by
    simpa [BCtx.plug, List.append_assoc] using
      (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post ++ [i])
  | .block bt pre k post => by
    have hb := (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_block_eq,
      BExpr.lowerList_append]
    exact PresL.instr (instrOk_block fun _ _ h' => hb.apply h')
  | .loop bt pre k post => by
    have hb := (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_loop_eq,
      BExpr.lowerList_append]
    exact PresL.instr (instrOk_loop fun _ _ h' => hb.apply h')
  | .ifCond bt pre k post t e => by
    simpa [BCtx.plug, List.append_assoc] using
      (presL_plug h k).ctx (BExpr.lowerList pre)
        (BExpr.lowerList post ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)])
  | .ifThen bt c pre k post e => by
    have hb := (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_if_eq, BExpr.lowerList_append]
    have := (PresL.instr (instrOk_if (bt := bt) (b₂ := BExpr.lowerList e)
      (fun _ _ h' => hb.apply h') (fun _ _ h' => h'))).ctx (BExpr.lowerList c) []
    simpa using this
  | .ifElse bt c t pre k post => by
    have hb := (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_if_eq, BExpr.lowerList_append]
    have := (PresL.instr (instrOk_if (bt := bt) (b₁ := BExpr.lowerList t)
      (fun _ _ h' => h') (fun _ _ h' => hb.apply h'))).ctx (BExpr.lowerList c) []
    simpa using this
  | .tryTable bt cs pre k post => by
    have hb := (presL_plug h k).ctx (BExpr.lowerList pre) (BExpr.lowerList post)
    simp only [BCtx.plug, BExpr.lowerList_singleton, BExpr.lower_tryTable_eq,
      BExpr.lowerList_append]
    exact PresL.instr (instrOk_tryTable fun _ _ h' => hb.apply h')

theorem presL_star {rule : List BExpr → List BExpr → Prop}
    (hpres : ∀ a b, rule a b → PresL (BExpr.lowerList a) (BExpr.lowerList b))
    {es es' : List BExpr} (h : SeqRefines.Star rule es es') :
    PresL (BExpr.lowerList es) (BExpr.lowerList es') := by
  induction h with
  | refl => exact PresL.refl _
  | @step K a b es h _ ih => exact (presL_plug (hpres a b h) K).trans ih

/-- The relation between a function and its rewritten version. -/
def BodyPres (f f' : BFunc) : Prop :=
  f.type = f'.type ∧ f.locals = f'.locals ∧
    ∀ C it, InstrsOk C (BExpr.lowerList f.body) it → InstrsOk C (BExpr.lowerList f'.body) it

theorem funcOk_of_pres {C : Context} {f f' : Func} {d : DefType} (h : FuncOk C f d)
    (ht : f.type = f'.type) (hl : f.locals = f'.locals)
    (hb : ∀ C it, InstrsOk C f.body it → InstrsOk C f'.body it) : FuncOk C f' d := by
  cases h with
  | mk hd he hloc hbody =>
    exact FuncOk.mk (by rw [← ht]; exact hd) he (by rw [← hl]; exact hloc) (hb _ _ hbody)

theorem funcs_ok_of_pres {C : Context} :
    ∀ {l fs : List Func} {fdts : List DefType}, List.Forall₂ (FuncOk C) l fdts →
      List.Forall₂ (fun f f' : Func => f.type = f'.type ∧ f.locals = f'.locals ∧
        ∀ C it, InstrsOk C f.body it → InstrsOk C f'.body it) l fs →
      List.Forall₂ (FuncOk C) fs fdts
  | _, _, _, .nil, .nil => List.Forall₂.nil
  | _, _, _, .cons h t, .cons ⟨ht, hl, hb⟩ tr =>
    List.Forall₂.cons (funcOk_of_pres h ht hl hb) (funcs_ok_of_pres t tr)

theorem ModuleOk.replace_funcs {M : Module} {t : CModuleType} (h : ModuleOk M t) {fs : List Func}
    (hf : List.Forall₂ (fun f f' : Func => f.type = f'.type ∧ f.locals = f'.locals ∧
        ∀ C it, InstrsOk C f.body it → InstrsOk C f'.body it) M.funcs fs) :
    ModuleOk { M with funcs := fs } t := by
  cases h with
  | mk htypes himports hC' hC htags hglobals hmems htables hfuncs hdata helems hstart hexports
      hdisjoint =>
    exact ModuleOk.mk htypes himports hC' hC htags hglobals hmems htables
      (funcs_ok_of_pres hfuncs hf) hdata helems hstart hexports hdisjoint

theorem forall₂_map_mapBody {l l' : List BFunc} (h : List.Forall₂ BodyPres l l') :
    List.Forall₂ (fun f f' : Func => f.type = f'.type ∧ f.locals = f'.locals ∧
      ∀ C it, InstrsOk C f.body it → InstrsOk C f'.body it)
      (l.map (Declaration.Func.mapBody BExpr.lowerList))
      (l'.map (Declaration.Func.mapBody BExpr.lowerList)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hx _ ih => exact List.Forall₂.cons hx ih

theorem BModule.ok_of_funcs {m m' : BModule} (hm : m.Ok) (hb : m'.base = m.base)
    (hf : List.Forall₂ BodyPres m.funcs m'.funcs) : m'.Ok := by
  obtain ⟨t, h⟩ := hm
  refine ⟨t, ?_⟩
  have := ModuleOk.replace_funcs h (forall₂_map_mapBody hf)
  have e : m'.lower = { m.lower with funcs := m'.funcs.map (Declaration.Func.mapBody BExpr.lowerList) } := by
    unfold BModule.lower; rw [hb]
  rw [e]; exact this

theorem BodyPres.refl (f : BFunc) : BodyPres f f := ⟨rfl, rfl, fun _ _ h => h⟩

theorem forall₂_modifyAt {a b : List BExpr}
    (h : ∀ C it, InstrsOk C (BExpr.lowerList a) it → InstrsOk C (BExpr.lowerList b) it) :
    ∀ (g : Nat) (fs : List BFunc), List.Forall₂ BodyPres
      (modifyAt (fun f : BFunc => { f with body := a }) g fs)
      (modifyAt (fun f : BFunc => { f with body := b }) g fs)
  | g, [] => by cases g <;> exact List.Forall₂.nil
  | 0, x :: fs => List.Forall₂.cons ⟨rfl, rfl, h⟩ (f2_refl BodyPres.refl fs)
  | n + 1, x :: fs => List.Forall₂.cons (BodyPres.refl x) (forall₂_modifyAt h n fs)

theorem BModule.withBody_ok {m : BModule} {g : Nat} {a b : List BExpr}
    (h : PresL (BExpr.lowerList a) (BExpr.lowerList b)) (hm : (m.withBody g a).Ok) :
    (m.withBody g b).Ok := by
  refine BModule.ok_of_funcs hm rfl ?_
  exact forall₂_modifyAt (fun _ _ h' => h.apply h') g m.funcs

/-! ## From per-step equivalences to rewrite sequences -/

theorem star_seqEquiv {o : GrowKind → Nat → Nat → Nat → Bool}
    {rule : List BExpr → List BExpr → Prop}
    (hstep : ∀ (K : BCtx) a b, rule a b → ∀ C it, SeqOk C (K.plug a) it → SeqOk C (K.plug b) it →
      SeqEquiv (· = ·) (Profile.deterministic o) C it (K.plug b) (K.plug a))
    (hpres : ∀ a b, rule a b → PresL (BExpr.lowerList a) (BExpr.lowerList b))
    {es es' : List BExpr} (h : SeqRefines.Star rule es es') :
    ∀ {C : Context} {it : InstrType}, SeqOk C es it →
      SeqEquiv (· = ·) (Profile.deterministic o) C it es' es := by
  induction h with
  | refl es =>
    intro C it hok
    exact ⟨SeqRefines.refl (fun _ => rfl) hok,
      SeqRefines.refl (R := fun b b' => b' = b) (fun _ => rfl) hok⟩
  | @step K a b es' hr _ ih =>
    intro C it hok
    have hokb : SeqOk C (K.plug b) it := (presL_plug (hpres a b hr) K).apply hok
    have E₁ := ih hokb
    have E₂ := hstep K a b hr C it hok hokb
    have hval : ∀ (m : BModule) (g : Nat) (K' : BCtx), (m.withBody g (K'.plug (K.plug a))).Ok →
        (m.withBody g (K'.plug (K.plug b))).Ok :=
      fun m g K' h' => BModule.withBody_ok (presL_plug (presL_plug (hpres a b hr) K) K') h'
    exact ⟨SeqRefines.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) E₁.1 E₂.1
        (fun m g K' _ h' => hval m g K' h'),
      SeqRefines.trans (fun _ _ _ h₁ h₂ => h₂.trans h₁) E₂.2 E₁.2
        (fun m g K' h' _ => hval m g K' h')⟩

/-! ## Small-step helpers -/

theorem step_vals {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {is is' : List Admin} (vs : List Val)
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Step P host ⟨s, f, vals vs ++ is⟩ ⟨s', f', vals vs ++ is'⟩ := by
  cases vs with
  | nil => simpa [vals] using h
  | cons v vs =>
    have := Step.ctxtInstrs (vs := v :: vs) (rest := []) h (Or.inl (List.cons_ne_nil _ _))
    simpa using this

theorem step_rest {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {is is' : List Admin} (vs : List Val) (rest : List Admin)
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Step P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  by_cases hr : rest = []
  · subst hr; simpa using step_vals vs h
  · exact Step.ctxtInstrs h (Or.inr hr)

theorem valOk_int {H : Type} {s : Store H} {v : Val} {t : IntType}
    (h : ValOk s v (.num (.int t))) : ∃ b : BitVec t.width, v = .num ⟨.int t, b⟩ := by
  generalize hT : (Ty.num (.int t) : CValType) = T at h
  cases h with
  | num nv =>
    obtain ⟨ty, b⟩ := nv
    simp only [Ty.num.injEq] at hT
    subst hT
    exact ⟨b, rfl⟩
  | vec b => cases hT
  | ref _ => cases hT

theorem fits_nil {H : Type} {C : Context} {it : InstrType} {s : Store H} {f : Frame}
    {vs : List Val} (hf : Fits C it s f vs) (hp : it.params = []) : vs = [] := by
  obtain ⟨-, -, h⟩ := hf
  rw [hp] at h
  cases h
  rfl

theorem fits_one {H : Type} {C : Context} {it : InstrType} {s : Store H} {f : Frame}
    {vs : List Val} {t : IntType} (hf : Fits C it s f vs) (hp : it.params = [.num (.int t)]) :
    ∃ b : BitVec t.width, vs = [.num ⟨.int t, b⟩] := by
  obtain ⟨-, -, h⟩ := hf
  rw [hp] at h
  cases h with
  | cons hv hnil =>
    cases hnil
    obtain ⟨b, rfl⟩ := valOk_int hv
    exact ⟨b, rfl⟩

/-- A context whose locals `0..k` all have type `t` and are set. -/
def localsCtx (k : Nat) (t : IntType) : Context :=
  { locals := List.replicate (k + 1) ⟨.set, .num (.int t)⟩ }

theorem fits_local {H : Type} {k : Nat} {t : IntType} {it : InstrType} {s : Store H}
    {f : Frame} {vs : List Val} (hf : Fits (localsCtx k t) it s f vs) :
    ∃ b : BitVec t.width, f.locals[k]? = some (some (.num ⟨.int t, b⟩)) := by
  obtain ⟨-, ⟨C₁, lts, hmi, hloc, hC⟩, -⟩ := hf
  cases hmi
  have hl := congrArg Context.locals hC
  simp only [localsCtx, List.nil_append] at hl
  subst hl
  obtain ⟨x, hx, hxv⟩ := f2_getElem? hloc (k := k) (y := ⟨.set, .num (.int t)⟩) (by simp)
  cases hxv with
  | set hv =>
    obtain ⟨b, rfl⟩ := valOk_int hv
    exact ⟨b, hx⟩

/-! ## Typing in the concrete contexts -/

theorem SeqOk.ofList {C : Context} {es : List BExpr} {is : List Instr} {it : InstrType}
    (he : BExpr.lowerList es = is) (h : InstrsOk C is it) : SeqOk C es it := by
  unfold SeqOk; rw [he]; exact h

/-- An operator applied to constants, typed by framing and sequencing. -/
theorem instrs_const {C : Context} {t : IntType} {b : BitVec t.width} (ts : List CValType)
    (hts : ResultOk C.toTypeCtx ts) :
    InstrsOk C [.intConst t b] ⟨ts, [], ts ++ [.num (.int t)]⟩ := by
  simpa using InstrsOk.frame (ts := ts)
    (InstrsOk.instr (InstrOk.numeric (NumericInstrOk.intConst (C := C) t b))) hts

theorem instrs_seq {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
    (h₁ : InstrsOk C is₁ ⟨t₁, [], t₂⟩) (h₂ : InstrsOk C is₂ ⟨t₂, [], t₃⟩) :
    InstrsOk C (is₁ ++ is₂) ⟨t₁, [], t₃⟩ := by
  simpa using InstrsOk.seq h₁ (by simp) h₂

/-- A constant followed by a unary operator. -/
theorem instrs_c_op {C : Context} {t : IntType} {x : BitVec t.width} {i : Instr}
    {r : List CValType} (hi : InstrOk C i ⟨[.num (.int t)], [], r⟩) :
    InstrsOk C [.intConst t x, i] ⟨[], [], r⟩ := by
  have a : InstrsOk C [.intConst t x] ⟨[], [], [.num (.int t)]⟩ :=
    InstrsOk.instr (InstrOk.numeric (NumericInstrOk.intConst t x))
  exact instrs_seq a (InstrsOk.instr hi)

/-- A value-pushing instruction, a constant, and a binary operator. -/
theorem instrs_x_c_op {C : Context} {t : IntType} {y : BitVec t.width} {i₁ i : Instr}
    {r : List CValType} (h₁ : InstrOk C i₁ ⟨[], [], [.num (.int t)]⟩)
    (hi : InstrOk C i ⟨[.num (.int t), .num (.int t)], [], r⟩) :
    InstrsOk C [i₁, .intConst t y, i] ⟨[], [], r⟩ := by
  have a : InstrsOk C [i₁] ⟨[], [], [.num (.int t)]⟩ := InstrsOk.instr h₁
  have b : InstrsOk C [.intConst t y] ⟨[.num (.int t)], [], [.num (.int t), .num (.int t)]⟩ :=
    instrs_const [.num (.int t)] (by simp)
  exact instrs_seq (instrs_seq a b) (InstrsOk.instr hi)

/-- Two value-pushing instructions and a binary operator. -/
theorem instrs_x_y_op {C : Context} {t : IntType} {i₁ i₂ i : Instr}
    {r : List CValType} (h₁ : InstrOk C i₁ ⟨[], [], [.num (.int t)]⟩)
    (h₂ : InstrOk C i₂ ⟨[], [], [.num (.int t)]⟩)
    (hi : InstrOk C i ⟨[.num (.int t), .num (.int t)], [], r⟩) :
    InstrsOk C [i₁, i₂, i] ⟨[], [], r⟩ := by
  have a : InstrsOk C [i₁] ⟨[], [], [.num (.int t)]⟩ := InstrsOk.instr h₁
  have b : InstrsOk C [i₂] ⟨[.num (.int t)], [], [.num (.int t), .num (.int t)]⟩ := by
    simpa using InstrsOk.frame (ts := [.num (.int t)]) (InstrsOk.instr h₂) (by simp)
  exact instrs_seq (instrs_seq a b) (InstrsOk.instr hi)

/-- Two constants followed by a binary operator. -/
theorem instrs_c_c_op {C : Context} {t : IntType} {x y : BitVec t.width} {i : Instr}
    {r : List CValType} (hi : InstrOk C i ⟨[.num (.int t), .num (.int t)], [], r⟩) :
    InstrsOk C [.intConst t x, .intConst t y, i] ⟨[], [], r⟩ := by
  have a : InstrsOk C [.intConst t x] ⟨[], [], [.num (.int t)]⟩ :=
    InstrsOk.instr (InstrOk.numeric (NumericInstrOk.intConst t x))
  have b : InstrsOk C [.intConst t y] ⟨[.num (.int t)], [], [.num (.int t), .num (.int t)]⟩ :=
    instrs_const [.num (.int t)] (by simp)
  exact instrs_seq (instrs_seq a b) (InstrsOk.instr hi)

/-- Realise a typing summarised by `Eff` for code typable at every framing of
the stack effect. -/
theorem realize_eff {C : Context} {B : List Instr} {e : StackEff} {it : InstrType}
    (hE : Eff C e it)
    (hB : ∀ ts, ResultOk C.toTypeCtx ts → InstrsOk C B ⟨ts ++ e.1, [], ts ++ e.2⟩)
    (h₁ : ResultOk C.toTypeCtx e.1) (h₂ : ResultOk C.toTypeCtx e.2) : InstrsOk C B it := by
  obtain ⟨p, xs, r⟩ := it
  obtain ⟨hp, hi, ts, hts, hpp, hrr⟩ := hE
  exact realize (hB ts hts) (ResultOk.append hts h₁) (ResultOk.append hts h₂) hp hpp hrr hi

/-- A redex is also a redex for the empty replacement when it leaves the stack
unchanged. -/
theorem realize_eff_nil {C : Context} {e : StackEff} {it : InstrType} (hE : Eff C e it)
    (he : e.1 = e.2) (h₁ : ResultOk C.toTypeCtx e.1) : InstrsOk C [] it := by
  refine realize_eff (B := []) (e := ([], [])) ?_ (fun ts hts => by simpa using InstrsOk.id hts)
    (by simp) (by simp)
  obtain ⟨hp, hi, ts, hts, hpp, hrr⟩ := hE
  refine ⟨hp, hi, ts ++ e.1, ResultOk.append hts h₁, by simpa using hpp, ?_⟩
  rw [he]
  simpa using hrr

/-! ## Instructions occurring in typed code are typed -/

/-- Deep membership: an instruction occurs in the code, possibly inside a body. -/
inductive DMem (i : Instr) : List Instr → Prop where
  | here {is : List Instr} (h : i ∈ is) : DMem i is
  | block {is : List Instr} {bt : BlockType} {b : List Instr} (h : Instr.block bt b ∈ is)
      (hd : DMem i b) : DMem i is
  | loop {is : List Instr} {bt : BlockType} {b : List Instr} (h : Instr.loop bt b ∈ is)
      (hd : DMem i b) : DMem i is
  | ifT {is : List Instr} {bt : BlockType} {b₁ b₂ : List Instr} (h : Instr.if_ bt b₁ b₂ ∈ is)
      (hd : DMem i b₁) : DMem i is
  | ifE {is : List Instr} {bt : BlockType} {b₁ b₂ : List Instr} (h : Instr.if_ bt b₁ b₂ ∈ is)
      (hd : DMem i b₂) : DMem i is
  | tryTable {is : List Instr} {bt : BlockType} {cs : List Catch} {b : List Instr}
      (h : Instr.tryTable bt cs b ∈ is) (hd : DMem i b) : DMem i is

theorem DMem.mono {i : Instr} {is is' : List Instr} (h : DMem i is) (hs : ∀ x ∈ is, x ∈ is') :
    DMem i is' := by
  cases h with
  | here h => exact DMem.here (hs _ h)
  | block h hd => exact DMem.block (hs _ h) hd
  | loop h hd => exact DMem.loop (hs _ h) hd
  | ifT h hd => exact DMem.ifT (hs _ h) hd
  | ifE h hd => exact DMem.ifE (hs _ h) hd
  | tryTable h hd => exact DMem.tryTable (hs _ h) hd

theorem typed_mem {C : Context} {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ j ∈ is, ∃ C' it', InstrOk C' j it' := by
  induction h using InstrsOk.ind with
  | nil => intro j hj; simp at hj
  | instr hi =>
    intro j hj
    simp only [List.mem_singleton] at hj
    subst hj
    exact ⟨_, _, hi⟩
  | seq _ _ _ ih₁ ih₂ =>
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact ih₁ j hj
    · exact ih₂ j hj
  | cons hi _ _ ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ⟨_, _, hi⟩
    · exact ih j hj
  | sub _ _ _ ih => exact ih
  | frame _ _ ih => exact ih

theorem block_body_typed {C : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk C (.block bt b) it) : ∃ C' it', InstrsOk C' b it' := by
  cases h with
  | block _ hb => exact ⟨_, _, hb⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem loop_body_typed {C : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk C (.loop bt b) it) : ∃ C' it', InstrsOk C' b it' := by
  cases h with
  | loop _ hb => exact ⟨_, _, hb⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem if_bodies_typed {C : Context} {bt : BlockType} {b₁ b₂ : List Instr} {it : InstrType}
    (h : InstrOk C (.if_ bt b₁ b₂) it) :
    (∃ C' it', InstrsOk C' b₁ it') ∧ ∃ C' it', InstrsOk C' b₂ it' := by
  cases h with
  | if_ _ h₁ h₂ => exact ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem tryTable_body_typed {C : Context} {bt : BlockType} {cs : List Catch} {b : List Instr}
    {it : InstrType} (h : InstrOk C (.tryTable bt cs b) it) : ∃ C' it', InstrsOk C' b it' := by
  cases h with
  | tryTable _ hb _ => exact ⟨_, _, hb⟩
  | parametric h => cases h
  | numeric h => cases h
  | vector h => cases h
  | «variable» h => cases h
  | memory h => cases h
  | table h => cases h
  | reference h => cases h

theorem DMem.typed {i : Instr} {is : List Instr} (h : DMem i is) :
    ∀ {C : Context} {it : InstrType}, InstrsOk C is it → ∃ C' it', InstrOk C' i it' := by
  induction h with
  | here h => exact fun hc => typed_mem hc _ h
  | block h _ ih =>
    intro C it hc
    obtain ⟨C', it', hb⟩ := typed_mem hc _ h
    obtain ⟨C'', it'', hb'⟩ := block_body_typed hb
    exact ih hb'
  | loop h _ ih =>
    intro C it hc
    obtain ⟨C', it', hb⟩ := typed_mem hc _ h
    obtain ⟨C'', it'', hb'⟩ := loop_body_typed hb
    exact ih hb'
  | ifT h _ ih =>
    intro C it hc
    obtain ⟨C', it', hb⟩ := typed_mem hc _ h
    obtain ⟨C'', it'', hb'⟩ := (if_bodies_typed hb).1
    exact ih hb'
  | ifE h _ ih =>
    intro C it hc
    obtain ⟨C', it', hb⟩ := typed_mem hc _ h
    obtain ⟨C'', it'', hb'⟩ := (if_bodies_typed hb).2
    exact ih hb'
  | tryTable h _ ih =>
    intro C it hc
    obtain ⟨C', it', hb⟩ := typed_mem hc _ h
    obtain ⟨C'', it'', hb'⟩ := tryTable_body_typed hb
    exact ih hb'

theorem DMem.plug {i : Instr} {a : List BExpr} (h : i ∈ BExpr.lowerList a) :
    ∀ K : BCtx, DMem i (BExpr.lowerList (K.plug a))
  | .hole => DMem.here h
  | .seq pre k post =>
    (DMem.plug h k).mono (fun x hx => by simp [BCtx.plug, hx])
  | .op _ pre k post =>
    (DMem.plug h k).mono (fun x hx => by simp [BCtx.plug, hx])
  | .block bt pre k post =>
    DMem.block (bt := bt) (b := BExpr.lowerList (pre ++ k.plug a ++ post)) (by simp [BCtx.plug])
      ((DMem.plug h k).mono (fun x hx => by simp [hx]))
  | .loop bt pre k post =>
    DMem.loop (bt := bt) (b := BExpr.lowerList (pre ++ k.plug a ++ post)) (by simp [BCtx.plug])
      ((DMem.plug h k).mono (fun x hx => by simp [hx]))
  | .ifCond _ pre k post _ _ =>
    (DMem.plug h k).mono (fun x hx => by simp [BCtx.plug, hx])
  | .ifThen bt c pre k post e =>
    DMem.ifT (bt := bt) (b₁ := BExpr.lowerList (pre ++ k.plug a ++ post))
      (b₂ := BExpr.lowerList e) (by simp [BCtx.plug])
      ((DMem.plug h k).mono (fun x hx => by simp [hx]))
  | .ifElse bt c t pre k post =>
    DMem.ifE (bt := bt) (b₁ := BExpr.lowerList t) (b₂ := BExpr.lowerList (pre ++ k.plug a ++ post))
      (by simp [BCtx.plug]) ((DMem.plug h k).mono (fun x hx => by simp [hx]))
  | .tryTable bt cs pre k post =>
    DMem.tryTable (bt := bt) (cs := cs) (b := BExpr.lowerList (pre ++ k.plug a ++ post))
      (by simp [BCtx.plug]) ((DMem.plug h k).mono (fun x hx => by simp [hx]))

/-- An instruction occurring in plugged code that is typed has a typing. -/
theorem typed_of_plug {i : Instr} {a : List BExpr} (h : i ∈ BExpr.lowerList a) (K : BCtx)
    {C : Context} {it : InstrType} (hok : SeqOk C (K.plug a) it) : ∃ C' it', InstrOk C' i it' :=
  (DMem.plug h K).typed hok

/-! ## Whole modules -/

theorem f2_getElem?_left {α β : Type _} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → ∀ {k : Nat} {x : α}, a[k]? = some x →
      ∃ y, b[k]? = some y ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hxy t, 0, _, h => by simp at h; subst h; exact ⟨_, rfl, hxy⟩
  | _, _, .cons _ t, k + 1, _, h => by simpa using f2_getElem?_left t (k := k) (by simpa using h)

theorem f2_of_getElem {α β : Type _} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, a.length = b.length →
      (∀ (i : Nat) (h₁ : i < a.length) (h₂ : i < b.length), R a[i] b[i]) → List.Forall₂ R a b
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: a, y :: b, hl, h =>
    List.Forall₂.cons (h 0 (by simp) (by simp))
      (f2_of_getElem (by simpa using hl) (fun i h₁ h₂ => h (i + 1) (by simpa using h₁)
        (by simpa using h₂)))

/-- The body of every defined function of a valid module is typed somewhere. -/
theorem body_typed {m : BModule} (hm : m.Ok) {g : Nat} (hg : g < m.funcs.length) :
    ∃ C it, SeqOk C m.funcs[g].body it := by
  obtain ⟨t, h⟩ := hm
  cases h with
  | mk _ _ _ _ _ _ _ _ hfuncs _ _ _ _ _ =>
    have hx : (m.funcs.map (Declaration.Func.mapBody BExpr.lowerList))[g]? =
        some (Declaration.Func.mapBody BExpr.lowerList m.funcs[g]) := by simp [hg]
    obtain ⟨d, -, hf⟩ := f2_getElem?_left hfuncs hx
    cases hf with
    | mk _ _ _ hb => exact ⟨_, _, hb⟩

theorem mapBodies_ok {T : List BExpr → List BExpr}
    (hty : ∀ C it es, InstrsOk C (BExpr.lowerList es) it →
      InstrsOk C (BExpr.lowerList (T es)) it) {m : BModule} (hm : m.Ok) :
    (m.mapBodies T).Ok := by
  refine BModule.ok_of_funcs hm rfl ?_
  refine f2_of_getElem ?_ ?_
  · simp [BModule.mapBodies]
  intro i h₁ h₂
  simp only [BModule.mapBodies, List.getElem_map]
  exact ⟨rfl, rfl, fun C it => hty C it _⟩

end Silmaril.Wasm.Binaryen
