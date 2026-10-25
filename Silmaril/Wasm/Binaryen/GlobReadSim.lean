module

public import Silmaril.Wasm.Binaryen.GlobReadRel

@[expose] public section

/-! # Reading an immutable global: one step

Every host-free step of the left configuration (the module with `global.get x`) is matched
by at least one step of the right configuration (the module with the literal), or the
right side stays and the size `aszs` of the left code decreases (`sim`), provided the left
store satisfies the invariant `GInv`. The only stutter is the site itself: under a frame of
`mi`, `global.get x` reads the literal in one step (`head_plain`). The step decomposition
follows `Binaryen/InlUnwrapSim.lean`.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The fixed data: the function whose code differs, at address `ag`. -/
structure Prm where
  /-- The literal of each resolvable global. -/
  lk : GlobalIdx → Option Instr
  /-- The instance of the module. -/
  mi : ModuleInst
  /-- The type of the function. -/
  dg : DefType
  /-- Its address. -/
  ag : Nat
  /-- Its code with the global reads (left). -/
  cL : Func
  /-- Its code with the literals (right). -/
  cR : Func

/-- The facts the simulation needs. -/
structure PrmOk (p : Prm) : Prop where
  locals : p.cR.locals = p.cL.locals
  body : GIL p.lk p.mi p.mi p.cL.body p.cR.body

/-- The left function instance. -/
def gL (p : Prm) : FuncInst H := ⟨p.dg, p.mi, .wasm p.cL⟩
/-- The right function instance. -/
def gR (p : Prm) : FuncInst H := ⟨p.dg, p.mi, .wasm p.cR⟩

/-- The stores of the two runs: the right one has the right code at `ag`. -/
structure SR (p : Prm) (s t : Store H) : Prop where
  hg : s.funcs[p.ag]? = some (gL p)
  ht : t = withFuncs s (s.funcs.set p.ag (gR p))

theorem sameTypes_set {p : Prm} {s : Store H} (h : s.funcs[p.ag]? = some (gL p)) :
    SameTypes (s.funcs.set p.ag (gR p)) s.funcs := by
  unfold SameTypes
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hj : p.ag = j
  · subst hj
    rw [List.getElem?_set_self hlt, h]
    rfl
  · rw [List.getElem?_set_ne hj]

theorem SR.sameTypes {p : Prm} {s t : Store H} (h : SR p s t) :
    SameTypes (s.funcs.set p.ag (gR p)) s.funcs :=
  sameTypes_set h.hg

theorem SR.mono {p : Prm} {s t s' : Store H} (h : SR p s t) (hs : s'.funcs = s.funcs) :
    SR p s' (withFuncs s' (s.funcs.set p.ag (gR p))) :=
  ⟨by rw [hs]; exact h.hg, by rw [hs]⟩

theorem SR.get {p : Prm} {s t : Store H} (h : SR p s t) (a : Nat) :
    t.funcs[a]? = if a = p.ag then some (gR p) else s.funcs[a]? := by
  rw [h.ht]
  simp only [withFuncs_funcs, List.getElem?_set]
  by_cases ha : a = p.ag
  · subst ha
    simp [(List.getElem?_eq_some_iff.mp h.hg).1]
  · simp [ha, Ne.symm ha]

/-- Related configurations: equal frames, code related at the frame's instance. -/
def MR (p : Prm) (c d : Config H) : Prop :=
  c.frame = d.frame ∧ GL p.lk p.mi c.frame.module c.code d.code

/-- The shape of one simulation step. -/
def Res (p : Prm) (P : Numerics.Profile) (c' d : Config H) (w : Nat) : Prop :=
  ∃ d' : Config H, MR p c' d' ∧ SR p c'.store d'.store ∧
    (Relation.TransGen (Step P Det.noHost) d d' ∨ (d' = d ∧ aszs c'.code < w))

/-- The induction hypothesis: steps of smaller code from invariant stores are simulated. -/
def SimIH (p : Prm) (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (c c' d : Config H), sizeOf c.code < k → Step P Det.noHost c c' → MR p c d →
    SR p c.store d.store → GInv p.lk p.mi c.store → Res p P c' d (aszs c.code)

theorem SimIH.mono {p : Prm} {P : Numerics.Profile} {k k' : Nat} (h : SimIH p P H k)
    (hk : k' ≤ k) : SimIH p P H k' :=
  fun c c' d hsz => h c c' d (by omega)

/-- The result of a head step of `e` against the right code `e'` (one element), with the
code related at the instance of the starting frame. -/
def HRes (p : Prm) (P : Numerics.Profile) (t : Store H) (f : Frame) (args : List Val)
    (e : Admin) (Y : List Admin) (c₀ : Config H) : Prop :=
  ∃ c₀' : Config H, (Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ Y⟩ c₀' ∨
      (c₀' = ⟨t, f, vals args ++ Y⟩ ∧ aszs c₀.code < aszs (vals args ++ [e]))) ∧
    SR p c₀.store c₀'.store ∧ c₀'.frame = c₀.frame ∧ GL p.lk p.mi f.module c₀.code c₀'.code

/-- A head step keeps the frame's instance. -/
theorem head_module {P : Numerics.Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hh : Det.Head P s f args e c₀) : c₀.frame.module = f.module :=
  step_frame_module hh.toStep

/-- The head step of `global.get`. -/
theorem head_globalGet {P : Numerics.Profile} {s : Store H} {f : Frame} {args : List Val}
    {x : GlobalIdx} {c₀ : Config H} (hh : Det.Head P s f args (.plain (.globalGet x)) c₀) :
    args = [] ∧ ∃ a g, s.global? f x = some (a, g) ∧ c₀ = ⟨s, f, [g.value.toAdmin]⟩ := by
  cases hh with
  | «variable» h =>
    generalize hc : (⟨s, f, vals args ++ [.plain (.globalGet x)]⟩ : Config H) = c at h
    cases h with
    | globalGet hg =>
      simp only [Config.mk.injEq] at hc
      obtain ⟨rfl, rfl, hcode⟩ := hc
      have hl := congrArg List.length hcode
      simp only [List.length_append, vals, List.length_map, List.length_singleton] at hl
      have ha : args = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst ha
      simp only [vals, List.map_nil, List.nil_append, List.cons.injEq, Admin.plain.injEq,
        Instr.globalGet.injEq, and_true] at hcode
      subst hcode
      exact ⟨rfl, _, _, hg, rfl⟩
    | localGet _ =>
      simp only [Config.mk.injEq] at hc
      have := congrArg List.getLast? hc.2.2
      simp at this
    | localSet _ =>
      simp only [Config.mk.injEq] at hc
      have := congrArg List.getLast? hc.2.2
      simp at this
    | localTee =>
      simp only [Config.mk.injEq] at hc
      have := congrArg List.getLast? hc.2.2
      simp at this
    | globalSet _ =>
      simp only [Config.mk.injEq] at hc
      have := congrArg List.getLast? hc.2.2
      simp at this
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-! ## Calls -/

theorem call_rel {p : Prm} (hok : PrmOk p) {s t : Store H} (hSR : SR p s t) {a : Nat}
    {fi : FuncInst H} {code : Func} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    ∃ (fi' : FuncInst H) (code' : Func), t.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
      fi'.module = fi.module ∧ fi'.code = .wasm code' ∧ code'.locals = code.locals ∧
      GIL p.lk p.mi fi.module code.body code'.body := by
  rw [hSR.get a]
  by_cases hag : a = p.ag
  · subst hag
    rw [hSR.hg] at hf
    cases hf
    simp only [gL, FuncCode.wasm.injEq] at hcode
    subst hcode
    exact ⟨gR p, p.cR, by simp, rfl, rfl, rfl, hok.locals, hok.body⟩
  · simp only [hag, ↓reduceIte]
    exact ⟨fi, code, hf, rfl, rfl, hcode, rfl, GIL.refl _⟩

theorem head_callData {p : Prm} {P : Numerics.Profile} (hok : PrmOk p) {s t : Store H}
    {f : Frame} {args : List Val} {e : Admin} {c₀ : Config H} (hSR : SR p s t)
    (hcd : CallData s f args e c₀) : HRes p P t f args e [e] c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hm, hcode', hl, hb⟩ := call_rel hok hSR hf hcode
  refine ⟨_, .inl (tg_head (.callRefFunc rfl hc hf' (ht ▸ he) hn hcode')), hSR, rfl, ?_⟩
  rw [hm, hl]
  exact .cons (.frame (.cons (.label .nil (GL.of_GIL hb)) (.nil _))) (.nil _)

/-! ## Atomic heads -/

/-- Plain non-structured instructions and call annotations: the same head step. -/
theorem head_flat {p : Prm} {P : Numerics.Profile} (hok : PrmOk p) {s t : Store H} {f : Frame}
    {args : List Val} {e : Admin} {c₀ : Config H} (hh : Det.Head P s f args e c₀)
    (hSR : SR p s t) (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : HRes p P t f args e [e] c₀ := by
  have hmod := head_module hh
  by_cases hS : SimpleE e
  · rcases head_simple hh hS hSR.sameTypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · exact head_callData hok hSR hcd
    · obtain ⟨hg, rfl⟩ := hSR
      exact ⟨⟨withFuncs c₀.store (s.funcs.set p.ag (gR p)), f, c₀.code⟩, .inl (tg_head hN),
        SR.mono ⟨hg, rfl⟩ hfs, hfr.symm, GL.refl _⟩
  · obtain ⟨hg, rfl⟩ := hSR
    obtain ⟨s₀, f₀, is₀⟩ := c₀
    have hloc : ∃ x, e = .plain (.localGet x) ∨ e = .plain (.localSet x) ∨
        e = .plain (.localTee x) := by
      refine Classical.byContradiction fun hne => hS ⟨hL, hH, hF, ?_, ?_, ?_⟩
      · intro x hx; exact hne ⟨x, .inl hx⟩
      · intro x hx; exact hne ⟨x, .inr (.inl hx)⟩
      · intro x hx; exact hne ⟨x, .inr (.inr hx)⟩
    obtain ⟨x, hx⟩ := hloc
    have hfam : Det.famOf e = .variable := by rcases hx with rfl | rfl | rfl <;> rfl
    cases hh with
    | «variable» h =>
      obtain ⟨hfs, h'⟩ := variableStep_withFuncs h (s.funcs.set p.ag (gR p))
      exact ⟨⟨withFuncs s₀ (s.funcs.set p.ag (gR p)), f₀, is₀⟩, .inl (tg_head (.variable h')),
        SR.mono ⟨hg, rfl⟩ hfs, rfl, GL.refl _⟩
    | parametric h =>
      exact absurd ((Det.famOf_of_shape (Det.ParametricStep.shape h)).2.symm.trans hfam)
        (by decide)
    | numeric h =>
      exact absurd ((Det.famOf_of_shape (Det.NumericStep.shape h)).2.symm.trans hfam)
        (by decide)
    | vector h =>
      exact absurd ((Det.famOf_of_shape (Det.VectorStep.shape h)).2.symm.trans hfam) (by decide)
    | table h =>
      exact absurd ((Det.famOf_of_shape (Det.TableStep.shape h)).2.symm.trans hfam) (by decide)
    | memory h =>
      exact absurd ((Det.famOf_of_shape (Det.MemoryStep.shape h)).2.symm.trans hfam) (by decide)
    | reference h =>
      exact absurd ((Det.famOf_of_shape (Det.RefStep.shape h)).2.symm.trans hfam) (by decide)
    | aggregate h =>
      exact absurd ((Det.famOf_of_shape (Det.AggregateStep.shape h)).2.symm.trans hfam)
        (by decide)
    | _ => rcases hx with h | h | h <;> (try cases h) <;> simp_all [Admin.IsCallRef]

/-! ## Structured plain heads -/

theorem structured_cases {i : Instr} (hs : structuredInstr i = true) :
    (∃ bt b, i = .block bt b) ∨ (∃ bt b, i = .loop bt b) ∨ (∃ bt t e, i = .if_ bt t e) ∨
      ∃ bt cs b, i = .tryTable bt cs b := by
  cases i <;> simp_all [structuredInstr]

section heads

variable {p : Prm} {P : Numerics.Profile} {s t : Store H} {f : Frame} {args : List Val}
  {c₀ : Config H}

theorem head_block {bt : BlockType} {b b' : List Instr} (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P s f args (.plain (.block bt b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.block bt b)) [.plain (.block bt b')] c₀ := by
  cases hh with
  | block hbt hm =>
    exact ⟨_, .inl (tg_head (.block hbt hm)), hSR, rfl,
      .cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_loop {bt : BlockType} {b b' : List Instr} (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P s f args (.plain (.loop bt b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.loop bt b)) [.plain (.loop bt b')] c₀ := by
  cases hh with
  | loop hbt hm =>
    exact ⟨_, .inl (tg_head (.loop hbt hm)), hSR, rfl,
      .cons (.label (.cons (.loop hb) .nil) (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : GIL p.lk p.mi f.module b₁ b₁')
    (h₂ : GIL p.lk p.mi f.module b₂ b₂') (hh : Det.Head P s f args (.plain (.if_ bt b₁ b₂)) c₀)
    (hSR : SR p s t) :
    HRes p P t f args (.plain (.if_ bt b₁ b₂)) [.plain (.if_ bt b₁' b₂')] c₀ := by
  cases hh with
  | ifTrue hc =>
    exact ⟨_, .inl (tg_head (.ifTrue hc)), hSR, rfl, .cons (.plain (.block h₁)) (.nil _)⟩
  | ifFalse hc =>
    exact ⟨_, .inl (tg_head (.ifFalse hc)), hSR, rfl, .cons (.plain (.block h₂)) (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

theorem head_tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr}
    (hb : GIL p.lk p.mi f.module b b')
    (hh : Det.Head P s f args (.plain (.tryTable bt cs b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.tryTable bt cs b)) [.plain (.tryTable bt cs b')] c₀ := by
  cases hh with
  | tryTable hbt hm =>
    exact ⟨_, .inl (tg_head (.tryTable hbt hm)), hSR, rfl,
      .cons (.handler (.cons (.label .nil (GL.append (GL.of_vals _) (GL.of_GIL hb))) (.nil _)))
        (.nil _)⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-- **The site**: under a frame of `mi` and the invariant, `global.get x` reads the literal
in one step while the right side, already at the literal, stutters. -/
theorem head_site {x : GlobalIdx} {ty : IntType} {b : BitVec ty.width} (hq : f.module = p.mi)
    (hx : p.lk x = some (.intConst ty b)) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args (.plain (.globalGet x)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.globalGet x)) [.plain (.intConst ty b)] c₀ := by
  obtain ⟨rfl, a, g, hg, rfl⟩ := head_globalGet hh
  have hv := hinv.global? hq hx hg
  refine ⟨⟨t, f, vals [] ++ [.plain (.intConst ty b)]⟩, .inr ⟨rfl, ?_⟩, hSR, rfl, ?_⟩
  · simp [hv, Val.toAdmin, isz]
  · simpa [hv, Val.toAdmin, vals] using (GL.refl (lk := p.lk) (mi := p.mi) (cur := f.module)
      [Admin.plain (.intConst ty b)])

theorem head_plain (hok : PrmOk p) (hinv : GInv p.lk p.mi s) {i i' : Instr}
    (hi : GI p.lk p.mi f.module i i') (hh : Det.Head P s f args (.plain i) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain i) [.plain i'] c₀ := by
  cases hi with
  | flat i =>
    by_cases hs : structuredInstr i = true
    · rcases structured_cases hs with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
        ⟨bt, cs, b, rfl⟩
      · exact head_block (GIL.refl b) hh hSR
      · exact head_loop (GIL.refl b) hh hSR
      · exact head_if (GIL.refl b₁) (GIL.refl b₂) hh hSR
      · exact head_tryTable (GIL.refl b) hh hSR
    · exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
  | site hq hx => exact head_site hq hx hinv hh hSR
  | block h => exact head_block h hh hSR
  | loop h => exact head_loop h hh hSR
  | if_ h₁ h₂ => exact head_if h₁ h₂ hh hSR
  | tryTable h => exact head_tryTable h hh hSR

/-! ## Labels, handlers and activations -/

theorem flat_of {cur : ModuleInst} {b b' : List Admin} (hb : GL p.lk p.mi cur b b') {vs : List Val}
    {y : Admin} {rest : List Admin} (h1 : ∀ n c b, y ≠ Admin.label n c b)
    (h2 : ∀ n cs b, y ≠ .handler n cs b) (h3 : ∀ n F b, y ≠ .frame n F b)
    (h4 : ∀ i, y = .plain i → Rigid i)
    (hb' : b = vals vs ++ y :: rest) : ∃ rest', b' = vals vs ++ y :: rest' := by
  subst hb'
  obtain ⟨rest', rfl, -⟩ := GL.flat_inv h1 h2 h3 h4 hb
  exact ⟨rest', rfl⟩

theorem throw_of {cur : ModuleInst} {b b' : List Admin} (hb : GL p.lk p.mi cur b b') {a : Nat}
    (h : b = throwing a) : b' = throwing a := by
  subst h
  exact GL.result_inv (r := .throw a) hb

theorem trap_of {cur : ModuleInst} {b b' : List Admin} (hb : GL p.lk p.mi cur b b')
    (h : b = [.trap]) : b' = [.trap] := by
  subst h
  exact GL.result_inv (r := .trap) hb

theorem retCall_rigid {c : Admin} (hc : c.IsReturnCallRef) :
    ∀ i, c = .plain i → Rigid i := by
  intro i h
  subst h
  refine ⟨?_, fun x hx => ?_⟩
  · cases i <;> simp_all [Admin.IsReturnCallRef, structuredInstr]
  · subst hx; simp [Admin.IsReturnCallRef] at hc

theorem rigid_br (l : LabelIdx) : ∀ i, Admin.plain (.br l) = .plain i → Rigid i := by
  intro i h; cases h; exact ⟨rfl, fun _ h => by cases h⟩

theorem rigid_return : ∀ i, Admin.plain .return_ = .plain i → Rigid i := by
  intro i h; cases h; exact ⟨rfl, fun _ h => by cases h⟩

/-- Labels with related continuations and bodies. -/
theorem head_label {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.label n c b))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args (.label n c b) c₀) (hc : GIL p.lk p.mi f.module c c')
    (hb : GL p.lk p.mi f.module b b')
    (hSR : SR p s t) : HRes p P t f args (.label n c b) [.label n c' b'] c₀ := by
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := step_frame_module h
    simp only at hrel
    rw [hm] at hrel
    refine ⟨⟨d₁.store, d₁.frame, [.label n c' d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.label hc hrel) (.nil _)⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n c')
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.labelVals rfl)), hSR, rfl, GL.refl _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (rigid_br l) hb'
    exact ⟨_, .inl (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp) hl hn)),
      hSR, rfl, GL.append (GL.of_vals _) (GL.of_GIL hc)⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (rigid_br l) hb'
    exact ⟨_, .inl (tg_head (.brLabelSucc (rest := rest') (by simp) hl)), hSR, rfl, GL.refl _⟩
  | returnCallRefLabel hb' hc' =>
    rename_i vs c'' rest
    have e : vals vs ++ [c''] ++ rest = vals vs ++ c'' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc')
      (fun _ _ _ h => by subst h; exact hc') (fun _ _ _ h => by subst h; exact hc')
      (retCall_rigid hc') hb'
    exact ⟨_, .inl (tg_head (.returnCallRefLabel (rest := rest') (by simp) hc')), hSR, rfl,
      GL.refl _⟩
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) rigid_return hb'
    exact ⟨_, .inl (tg_head (.returnLabel (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | throwRefLabel =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefLabel), hSR, rfl, GL.refl _⟩
  | trapLabel =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapLabel), hSR, rfl, GL.refl _⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-- Handlers with related bodies. -/
theorem head_handler {n : Nat} {cs : List Catch} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args (.handler n cs b) c₀) (hb : GL p.lk p.mi f.module b b')
    (hSR : SR p s t) : HRes p P t f args (.handler n cs b) [.handler n cs b'] c₀ := by
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have hm : f'.module = f.module := step_frame_module h
    simp only at hrel
    rw [hm] at hrel
    refine ⟨⟨d₁.store, d₁.frame, [.handler n cs d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.handler hrel) (.nil _)⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (rigid_br l) hb'
    exact ⟨_, .inl (tg_head (.brHandler (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | returnCallRefHandler hb' hc =>
    rename_i vs c' rest
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_rigid hc) hb'
    exact ⟨_, .inl (tg_head (.returnCallRefHandler (rest := rest') (by simp) hc)), hSR, rfl,
      GL.refl _⟩
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) rigid_return hb'
    exact ⟨_, .inl (tg_head (.returnHandler (rest := rest') (by simp))), hSR, rfl, GL.refl _⟩
  | throwRefHandlerEmpty =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerEmpty), hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatch he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatch he ht)), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | throwRefHandlerCatchRef he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatchRef he ht)), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | throwRefHandlerCatchAll =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAll), hSR, rfl, GL.refl _⟩
  | throwRefHandlerCatchAllRef =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAllRef), hSR, rfl, GL.refl _⟩
  | throwRefHandlerNext h =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerNext h)), ⟨hg, rfl⟩, rfl, GL.refl _⟩
  | handlerVals hb' =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.handlerVals rfl)), hSR, rfl, GL.refl _⟩
  | trapHandler =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapHandler), hSR, rfl, GL.refl _⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-- Activations with related bodies (equal frames), related at the activation's instance. -/
theorem head_frame {k : Nat} {F : Frame} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.frame k F b))) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args (.frame k F b) c₀) (hb : GL p.lk p.mi F.module b b')
    (hSR : SR p s t) : HRes p P t f args (.frame k F b) [.frame k F b'] c₀ := by
  cases hh with
  | ctxtFrame h =>
    rename_i s' F₁ b₁
    have hsz : sizeOf b < sizeOf (Admin.frame k F b) := Exec.Drv.sizeOf_frame_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, F, b⟩ ⟨s', F₁, b₁⟩ ⟨t, F, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR hinv
    have e : F₁ = d₁.frame := hfr₁
    refine ⟨⟨d₁.store, f, [.frame k d₁.frame d₁.code]⟩, ?_, hsr, rfl, ?_⟩
    · rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl (tg_frame hp k f)
      · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
    · rw [← e]
      exact .cons (.frame hrel) (.nil _)
  | frameVals hb' hn =>
    subst hb'
    rw [GL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.frameVals rfl hn)), hSR, rfl, GL.refl _⟩
  | returnFrame hb' hn =>
    rename_i vs' vs rest
    have e : vals vs' ++ vals vs ++ [Admin.plain .return_] ++ rest =
        vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) rigid_return hb'
    exact ⟨_, .inl (tg_head (.returnFrame (vs' := vs') (rest := rest') (by simp) hn)), hSR, rfl,
      GL.refl _⟩
  | returnCallRefFrameNull hb' hc =>
    rename_i vs c rest
    have e : vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_rigid hc) hb'
    have e' : vals (vs ++ [.ref .null]) ++ c :: rest' = vals vs ++ [Admin.ref .null, c] ++ rest' :=
      by simp [vals, Val.toAdmin]
    rw [e']
    exact ⟨_, .inl (tg_head (.returnCallRefFrameNull rfl hc)), hSR, rfl, GL.refl _⟩
  | returnCallRefFrameAddr hb' hc hf he hn =>
    rename_i vs' vs a c rest fi ps rs
    have e : vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_rigid hc) hb'
    have e' : vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest' =
        vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest' := by
      simp [vals, Val.toAdmin]
    rw [e']
    obtain ⟨fi', hf', ht⟩ := hSR.sameTypes.get hf
    have hN := Det.Head.returnCallRefFrameAddr (P := P) (s := t) (f := f) (fi := F) (k := k)
      (vs' := vs') (vs := vs) (rest := rest') rfl hc (by rw [hSR.ht]; exact hf') (ht ▸ he) hn
    exact ⟨_, .inl (tg_head hN), hSR, rfl, GL.refl _⟩
  | throwRefFrame =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefFrame), hSR, rfl, GL.refl _⟩
  | trapFrame =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapFrame), hSR, rfl, GL.refl _⟩
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

/-- **Related head steps.** -/
theorem head_rel (hok : PrmOk p) {e e' : Admin} (IH : SimIH p P H (sizeOf e))
    (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args e c₀) (he : GA p.lk p.mi f.module e e') (hSR : SR p s t) :
    HRes p P t f args e [e'] c₀ := by
  have hgood := hh.good
  cases he with
  | plain hi => exact head_plain hok hinv hi hh hSR
  | ref _ r => exact absurd hgood.val_none (by simp)
  | callRef _ d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | retCallRef _ d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | label hc hb => exact head_label IH hinv hh hc hb hSR
  | handler hb => exact head_handler IH hinv hh hb hSR
  | frame hb => exact head_frame IH hinv hh hb hSR
  | trap _ => exact absurd rfl hgood.ne_trap

end heads

/-! ## The simulation -/

section main

variable {p : Prm} {P : Numerics.Profile}

theorem lift_tg {t t' : Store H} {f f' : Frame} {vs args : List Val} {Y code' rest' : List Admin}
    (h : Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ Y⟩ ⟨t', f', code'⟩) :
    Relation.TransGen (Step P Det.noHost) ⟨t, f, vals (vs ++ args) ++ (Y ++ rest')⟩
      ⟨t', f', vals vs ++ code' ++ rest'⟩ := by
  have := tg_instrs h vs rest'
  simpa using this

theorem sim_head (hok : PrmOk p) {k : Nat} (IH : SimIH p P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1) (hinv : GInv p.lk p.mi s)
    (hh : Det.Head P s f args e c₀)
    (hrel : GL p.lk p.mi f.module (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR p s t) :
    Res p P ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ ⟨t, f, ns⟩
      (aszs (vals vs ++ (vals args ++ e :: rest))) := by
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  have hmod := head_module hh
  rw [headDec_code] at hrel
  obtain ⟨nB, rfl, hB⟩ := GL.vals_append_inv hrel
  cases hB with
  | cons he hr =>
    rename_i e' rest'
    obtain ⟨c₀', hprog, hsr, hfr, hrel'⟩ := head_rel hok (IH.mono (by omega)) hinv hh he hSR
    refine ⟨⟨c₀'.store, c₀'.frame, vals vs ++ c₀'.code ++ rest'⟩,
      ⟨hfr.symm, ?_⟩, hsr, ?_⟩
    · simp only
      rw [hmod]
      exact GL.append (GL.append (GL.of_vals vs) hrel') hr
    · rcases hprog with hp | ⟨rfl, hw⟩
      · left
        exact lift_tg (Y := [e']) hp
      · right
        refine ⟨by simp, ?_⟩
        simp only [aszs_append, aszs_cons, aszs_nil] at hw ⊢
        omega

theorem sim_bubble {s t : Store H} {f : Frame} {pp q : List Val} {X u r ns : List Admin}
    (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : GL p.lk p.mi f.module (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR p s t) :
    Res p P ⟨s, f, vals pp ++ X ++ r⟩ ⟨t, f, ns⟩ (aszs (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := GL.append_inv hrel
  obtain ⟨n₃, n₄, rfl, h₃, h₄⟩ := GL.append_inv h₁
  obtain ⟨n₅, n₆, rfl, h₅, h₆⟩ := GL.append_inv h₂
  rw [GL.vals_inv h₃]
  have hX' : n₄ = X := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact GL.result_inv (r := .trap) h₄
    · exact GL.result_inv (r := .throw a) h₄
  subst hX'
  by_cases hq : q ≠ [] ∨ n₅ ≠ []
  · refine ⟨⟨t, f, vals pp ++ n₄ ++ n₆⟩, ⟨rfl, GL.append (GL.append (GL.of_vals pp)
      (GL.refl n₄)) h₆⟩, hSR, .inl (.single (Det.Bubble.toStep ⟨pp, q, n₄, n₅, n₆, rfl, hX, hq,
      rfl⟩))⟩
  · simp only [ne_eq, not_or, not_not] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hu : u ≠ [] := by
      rcases hqu with h | h
      · exact absurd rfl h
      · exact h
    have hpos := aszs_pos hu
    refine ⟨⟨t, f, vals (pp ++ []) ++ n₄ ++ ([] ++ n₆)⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
    · simpa using GL.append (GL.append (GL.of_vals pp) (GL.refl n₄)) h₆
    · simp only [aszs_append, List.append_nil] at hpos ⊢
      omega

/-- **One step.** Every host-free step of the left configuration from an invariant store is
simulated. -/
theorem sim (hok : PrmOk p) : ∀ k : Nat, SimIH p P H k
  | 0 => fun _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun c c' d hsz hstep hMR hSR hinv => by
    have IH := sim hok k
    obtain ⟨s, f, code⟩ := c
    obtain ⟨t, fn, ns⟩ := d
    obtain ⟨hfr, hrel⟩ := hMR
    simp only at hfr hrel hSR hinv
    subst hfr
    rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
        ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
    · simp only at hcode
      subst hcode
      exact sim_head hok IH hsz hinv hh hrel hSR
    · simp only at hcode
      subst hcode
      exact sim_bubble hX hqu hrel hSR

end main

end Silmaril.Wasm.Binaryen.GlobRead
