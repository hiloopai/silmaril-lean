module

public import Silmaril.Wasm.Binaryen.InlUnwrapRel

@[expose] public section

/-! # Unwrapping a branch-free block: one step

Every host-free step of the left configuration (the module with `block bt R`) is matched
by at least one step of the right configuration (the module with `R`), or the right side
stays and the size `aszs` of the left code decreases (`sim`). The step is decomposed
(`Det.Step.decomp`) into a head step under a value prefix and a suffix, or the bubbling of a
trap or exception; nested labels, handlers and activations use the induction hypothesis on
smaller code.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- The fixed data: the function whose code differs, at address `ag`. -/
structure Prm where
  /-- The region of the site. -/
  R : List Instr
  /-- The instance of the module. -/
  mi : ModuleInst
  /-- The type of the function. -/
  dg : DefType
  /-- Its address. -/
  ag : Nat
  /-- Its code with the block (left). -/
  cL : Func
  /-- Its code with the bare region (right). -/
  cR : Func

/-- The facts the simulation needs. -/
structure PrmOk (p : Prm) : Prop where
  locals : p.cR.locals = p.cL.locals
  body : UIL p.R p.cL.body p.cR.body
  bud : ∃ S, ∀ j ∈ p.R, InstrB budU S j
  labels : instrsLabels p.R = []

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

/-- Related configurations: equal frames, related code. -/
def MR (p : Prm) (c d : Config H) : Prop := c.frame = d.frame ∧ UL p.R c.code d.code

/-- The shape of one simulation step. -/
def Res (p : Prm) (P : Numerics.Profile) (c' d : Config H) (w : Nat) : Prop :=
  ∃ d' : Config H, MR p c' d' ∧ SR p c'.store d'.store ∧
    (Relation.TransGen (Step P Det.noHost) d d' ∨ (d' = d ∧ aszs c'.code < w))

/-- The induction hypothesis: steps of smaller code are simulated. -/
def SimIH (p : Prm) (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (c c' d : Config H), sizeOf c.code < k → Step P Det.noHost c c' → MR p c d →
    SR p c.store d.store → Res p P c' d (aszs c.code)

theorem SimIH.mono {p : Prm} {P : Numerics.Profile} {k k' : Nat} (h : SimIH p P H k)
    (hk : k' ≤ k) : SimIH p P H k' :=
  fun c c' d hsz => h c c' d (by omega)

/-- The result of a head step of `e` against the right code `e'` (one element). -/
def HRes (p : Prm) (P : Numerics.Profile) (t : Store H) (f : Frame) (args : List Val)
    (e : Admin) (Y : List Admin) (c₀ : Config H) : Prop :=
  ∃ c₀' : Config H, (Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ Y⟩ c₀' ∨
      (c₀' = ⟨t, f, vals args ++ Y⟩ ∧ aszs c₀.code < aszs (vals args ++ [e]))) ∧
    SR p c₀.store c₀'.store ∧ c₀'.frame = c₀.frame ∧ UL p.R c₀.code c₀'.code

/-! ## Calls -/

theorem call_rel {p : Prm} (hok : PrmOk p) {s t : Store H} (hSR : SR p s t) {a : Nat}
    {fi : FuncInst H} {code : Func} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) :
    ∃ (fi' : FuncInst H) (code' : Func), t.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
      fi'.module = fi.module ∧ fi'.code = .wasm code' ∧ code'.locals = code.locals ∧
      UIL p.R code.body code'.body := by
  rw [hSR.get a]
  by_cases hag : a = p.ag
  · subst hag
    rw [hSR.hg] at hf
    cases hf
    simp only [gL, FuncCode.wasm.injEq] at hcode
    subst hcode
    exact ⟨gR p, p.cR, by simp, rfl, rfl, rfl, hok.locals, hok.body⟩
  · simp only [hag, ↓reduceIte]
    exact ⟨fi, code, hf, rfl, rfl, hcode, rfl, UIL.refl _⟩

theorem head_callData {p : Prm} {P : Numerics.Profile} (hok : PrmOk p) {s t : Store H}
    {f : Frame} {args : List Val} {e : Admin} {c₀ : Config H} (hSR : SR p s t)
    (hcd : CallData s f args e c₀) : HRes p P t f args e [e] c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hm, hcode', hl, hb⟩ := call_rel hok hSR hf hcode
  refine ⟨_, .inl (tg_head (.callRefFunc rfl hc hf' (ht ▸ he) hn hcode')), hSR, rfl, ?_⟩
  rw [hm, hl]
  exact .cons (.frame (.cons (.label .nil (UL.of_UIL hb)) .nil)) .nil

/-! ## Atomic heads -/

/-- Plain non-structured instructions and call annotations: the same head step. -/
theorem head_flat {p : Prm} {P : Numerics.Profile} (hok : PrmOk p) {s t : Store H} {f : Frame}
    {args : List Val} {e : Admin} {c₀ : Config H} (hh : Det.Head P s f args e c₀)
    (hSR : SR p s t) (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : HRes p P t f args e [e] c₀ := by
  by_cases hS : SimpleE e
  · rcases head_simple hh hS hSR.sameTypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · exact head_callData hok hSR hcd
    · obtain ⟨hg, rfl⟩ := hSR
      exact ⟨⟨withFuncs c₀.store (s.funcs.set p.ag (gR p)), f, c₀.code⟩, .inl (tg_head hN),
        SR.mono ⟨hg, rfl⟩ hfs, hfr.symm, UL.refl _⟩
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
        SR.mono ⟨hg, rfl⟩ hfs, rfl, UL.refl _⟩
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

theorem head_block {bt : BlockType} {b b' : List Instr} (hb : UIL p.R b b')
    (hh : Det.Head P s f args (.plain (.block bt b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.block bt b)) [.plain (.block bt b')] c₀ := by
  cases hh with
  | block hbt hm =>
    exact ⟨_, .inl (tg_head (.block hbt hm)), hSR, rfl,
      .cons (.label .nil (UL.append (UL.of_vals _) (UL.of_UIL hb))) .nil⟩
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

theorem head_loop {bt : BlockType} {b b' : List Instr} (hb : UIL p.R b b')
    (hh : Det.Head P s f args (.plain (.loop bt b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.loop bt b)) [.plain (.loop bt b')] c₀ := by
  cases hh with
  | loop hbt hm =>
    exact ⟨_, .inl (tg_head (.loop hbt hm)), hSR, rfl,
      .cons (.label (.cons (.loop hb) .nil) (UL.append (UL.of_vals _) (UL.of_UIL hb))) .nil⟩
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

theorem head_if {bt : BlockType} {b₁ b₁' b₂ b₂' : List Instr} (h₁ : UIL p.R b₁ b₁')
    (h₂ : UIL p.R b₂ b₂') (hh : Det.Head P s f args (.plain (.if_ bt b₁ b₂)) c₀)
    (hSR : SR p s t) :
    HRes p P t f args (.plain (.if_ bt b₁ b₂)) [.plain (.if_ bt b₁' b₂')] c₀ := by
  cases hh with
  | ifTrue hc =>
    exact ⟨_, .inl (tg_head (.ifTrue hc)), hSR, rfl, .cons (.plain (.block h₁)) .nil⟩
  | ifFalse hc =>
    exact ⟨_, .inl (tg_head (.ifFalse hc)), hSR, rfl, .cons (.plain (.block h₂)) .nil⟩
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

theorem head_tryTable {bt : BlockType} {cs : List Catch} {b b' : List Instr} (hb : UIL p.R b b')
    (hh : Det.Head P s f args (.plain (.tryTable bt cs b)) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain (.tryTable bt cs b)) [.plain (.tryTable bt cs b')] c₀ := by
  cases hh with
  | tryTable hbt hm =>
    exact ⟨_, .inl (tg_head (.tryTable hbt hm)), hSR, rfl,
      .cons (.handler (.cons (.label .nil (UL.append (UL.of_vals _) (UL.of_UIL hb))) .nil)) .nil⟩
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

theorem head_plain (hok : PrmOk p) {i i' : Instr} (hi : UI p.R i i')
    (hh : Det.Head P s f args (.plain i) c₀) (hSR : SR p s t) :
    HRes p P t f args (.plain i) [.plain i'] c₀ := by
  cases hi with
  | flat i =>
    by_cases hs : structuredInstr i = true
    · rcases structured_cases hs with ⟨bt, b, rfl⟩ | ⟨bt, b, rfl⟩ | ⟨bt, b₁, b₂, rfl⟩ |
        ⟨bt, cs, b, rfl⟩
      · exact head_block (UIL.refl b) hh hSR
      · exact head_loop (UIL.refl b) hh hSR
      · exact head_if (UIL.refl b₁) (UIL.refl b₂) hh hSR
      · exact head_tryTable (UIL.refl b) hh hSR
    · exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
  | block h => exact head_block h hh hSR
  | loop h => exact head_loop h hh hSR
  | if_ h₁ h₂ => exact head_if h₁ h₂ hh hSR
  | tryTable h => exact head_tryTable h hh hSR

/-! ## Labels, handlers and activations -/

theorem flat_of {b b' : List Admin} (hb : UL p.R b b') {vs : List Val} {y : Admin}
    {rest : List Admin} (h1 : ∀ n c b, y ≠ Admin.label n c b) (h2 : ∀ n cs b, y ≠ .handler n cs b)
    (h3 : ∀ n F b, y ≠ .frame n F b) (h4 : ∀ i, y = .plain i → structuredInstr i = false)
    (hb' : b = vals vs ++ y :: rest) : ∃ rest', b' = vals vs ++ y :: rest' := by
  subst hb'
  obtain ⟨rest', rfl, -⟩ := UL.flat_inv h1 h2 h3 h4 hb
  exact ⟨rest', rfl⟩

theorem throw_of {b b' : List Admin} (hb : UL p.R b b') {a : Nat} (h : b = throwing a) :
    b' = throwing a := by
  subst h
  exact UL.result_inv (r := .throw a) hb

theorem trap_of {b b' : List Admin} (hb : UL p.R b b') (h : b = [.trap]) : b' = [.trap] := by
  subst h
  exact UL.result_inv (r := .trap) hb

theorem retCall_flat {c : Admin} (hc : c.IsReturnCallRef) :
    ∀ i, c = .plain i → structuredInstr i = false := by
  intro i h
  subst h
  cases i <;> simp_all [Admin.IsReturnCallRef, structuredInstr]

/-- Labels with related continuations and bodies. -/
theorem head_label {n : Nat} {c c' : List Instr} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.label n c b)))
    (hh : Det.Head P s f args (.label n c b) c₀) (hc : UIL p.R c c') (hb : UL p.R b b')
    (hSR : SR p s t) : HRes p P t f args (.label n c b) [.label n c' b'] c₀ := by
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR
    refine ⟨⟨d₁.store, d₁.frame, [.label n c' d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.label hc hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n c')
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [UL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.labelVals rfl)), hSR, rfl, UL.refl _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp) hl hn)),
      hSR, rfl, UL.append (UL.of_vals _) (UL.of_UIL hc)⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.brLabelSucc (rest := rest') (by simp) hl)), hSR, rfl, UL.refl _⟩
  | returnCallRefLabel hb' hc' =>
    rename_i vs c'' rest
    have e : vals vs ++ [c''] ++ rest = vals vs ++ c'' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc')
      (fun _ _ _ h => by subst h; exact hc') (fun _ _ _ h => by subst h; exact hc')
      (retCall_flat hc') hb'
    exact ⟨_, .inl (tg_head (.returnCallRefLabel (rest := rest') (by simp) hc')), hSR, rfl,
      UL.refl _⟩
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.returnLabel (rest := rest') (by simp))), hSR, rfl, UL.refl _⟩
  | throwRefLabel =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefLabel), hSR, rfl, UL.refl _⟩
  | trapLabel =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapLabel), hSR, rfl, UL.refl _⟩
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
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b)))
    (hh : Det.Head P s f args (.handler n cs b) c₀) (hb : UL p.R b b') (hSR : SR p s t) :
    HRes p P t f args (.handler n cs b) [.handler n cs b'] c₀ := by
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR
    refine ⟨⟨d₁.store, d₁.frame, [.handler n cs d₁.code]⟩, ?_, hsr, hfr₁.symm,
      .cons (.handler hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.brHandler (rest := rest') (by simp))), hSR, rfl, UL.refl _⟩
  | returnCallRefHandler hb' hc =>
    rename_i vs c' rest
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_flat hc) hb'
    exact ⟨_, .inl (tg_head (.returnCallRefHandler (rest := rest') (by simp) hc)), hSR, rfl,
      UL.refl _⟩
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.returnHandler (rest := rest') (by simp))), hSR, rfl, UL.refl _⟩
  | throwRefHandlerEmpty =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerEmpty), hSR, rfl, UL.refl _⟩
  | throwRefHandlerCatch he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatch he ht)), ⟨hg, rfl⟩, rfl, UL.refl _⟩
  | throwRefHandlerCatchRef he ht =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatchRef he ht)), ⟨hg, rfl⟩, rfl, UL.refl _⟩
  | throwRefHandlerCatchAll =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAll), hSR, rfl, UL.refl _⟩
  | throwRefHandlerCatchAllRef =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAllRef), hSR, rfl, UL.refl _⟩
  | throwRefHandlerNext h =>
    obtain ⟨hg, rfl⟩ := hSR
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerNext h)), ⟨hg, rfl⟩, rfl, UL.refl _⟩
  | handlerVals hb' =>
    subst hb'
    rw [UL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.handlerVals rfl)), hSR, rfl, UL.refl _⟩
  | trapHandler =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapHandler), hSR, rfl, UL.refl _⟩
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

/-- Activations with related bodies (equal frames). -/
theorem head_frame {k : Nat} {F : Frame} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.frame k F b)))
    (hh : Det.Head P s f args (.frame k F b) c₀) (hb : UL p.R b b') (hSR : SR p s t) :
    HRes p P t f args (.frame k F b) [.frame k F b'] c₀ := by
  cases hh with
  | ctxtFrame h =>
    rename_i s' F₁ b₁
    have hsz : sizeOf b < sizeOf (Admin.frame k F b) := Exec.Drv.sizeOf_frame_body
    obtain ⟨d₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH ⟨s, F, b⟩ ⟨s', F₁, b₁⟩ ⟨t, F, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR
    have e : F₁ = d₁.frame := hfr₁
    refine ⟨⟨d₁.store, f, [.frame k d₁.frame d₁.code]⟩, ?_, hsr, rfl, ?_⟩
    · rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl (tg_frame hp k f)
      · exact .inr ⟨rfl, by simp [asz] at hw ⊢; omega⟩
    · rw [← e]
      exact .cons (.frame hrel) .nil
  | frameVals hb' hn =>
    subst hb'
    rw [UL.vals_inv hb]
    exact ⟨_, .inl (tg_head (.frameVals rfl hn)), hSR, rfl, UL.refl _⟩
  | returnFrame hb' hn =>
    rename_i vs' vs rest
    have e : vals vs' ++ vals vs ++ [Admin.plain .return_] ++ rest =
        vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ h => by cases h; rfl) hb'
    exact ⟨_, .inl (tg_head (.returnFrame (vs' := vs') (rest := rest') (by simp) hn)), hSR, rfl,
      UL.refl _⟩
  | returnCallRefFrameNull hb' hc =>
    rename_i vs c rest
    have e : vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_flat hc) hb'
    have e' : vals (vs ++ [.ref .null]) ++ c :: rest' = vals vs ++ [Admin.ref .null, c] ++ rest' :=
      by simp [vals, Val.toAdmin]
    rw [e']
    exact ⟨_, .inl (tg_head (.returnCallRefFrameNull rfl hc)), hSR, rfl, UL.refl _⟩
  | returnCallRefFrameAddr hb' hc hf he hn =>
    rename_i vs' vs a c rest fi ps rs
    have e : vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
        vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
      simp [vals, Val.toAdmin]
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := flat_of hb (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc)
      (retCall_flat hc) hb'
    have e' : vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest' =
        vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest' := by
      simp [vals, Val.toAdmin]
    rw [e']
    obtain ⟨fi', hf', ht⟩ := hSR.sameTypes.get hf
    have hN := Det.Head.returnCallRefFrameAddr (P := P) (s := t) (f := f) (fi := F) (k := k)
      (vs' := vs') (vs := vs) (rest := rest') rfl hc (by rw [hSR.ht]; exact hf') (ht ▸ he) hn
    exact ⟨_, .inl (tg_head hN), hSR, rfl, UL.refl _⟩
  | throwRefFrame =>
    rw [throw_of hb rfl]
    exact ⟨_, .inl (tg_head .throwRefFrame), hSR, rfl, UL.refl _⟩
  | trapFrame =>
    rw [trap_of hb rfl]
    exact ⟨_, .inl (tg_head .trapFrame), hSR, rfl, UL.refl _⟩
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
    (hh : Det.Head P s f args e c₀) (he : UA p.R e e') (hSR : SR p s t) :
    HRes p P t f args e [e'] c₀ := by
  have hgood := hh.good
  cases he with
  | plain hi => exact head_plain hok hi hh hSR
  | ref r => exact absurd hgood.val_none (by simp)
  | callRef d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | retCallRef d =>
    exact head_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | label hc hb => exact head_label IH hh hc hb hSR
  | handler hb => exact head_handler IH hh hb hSR
  | frame hb => exact head_frame IH hh hb hSR
  | trap => exact absurd rfl hgood.ne_trap

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

theorem noEsc_entry (hok : PrmOk p) (args : List Val) : NoEsc (vals args ++ expression p.R) := by
  obtain ⟨S, hS⟩ := hok.bud
  refine ⟨⟨S, ?_⟩, ?_⟩
  · simp only [AdmsB_append, AdmsB_vals, AdmsB_expression, true_and]
    exact hS
  · simp [AdmsLab_append, hok.labels]

/-! ## Code folding: helpers -/

theorem sizeOf_append_left (l₁ l₂ : List Admin) : sizeOf l₁ ≤ sizeOf (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    cases l₂ with
    | nil => simp
    | cons => simp; omega
  | cons a l ih => simp; omega

theorem all_vals : ∀ V : List Val, (vals V).all Admin.isVal = true
  | [] => rfl
  | v :: V => by
    simp only [Det.vals_cons, List.all_cons, all_vals V, Bool.and_true]
    simp [Admin.isVal, Det.val?_eq_some.mpr rfl]

theorem exists_vals_all : ∀ {l : List Admin}, l.all Admin.isVal = true → ∃ V, l = vals V
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ha, hl⟩ := h
    obtain ⟨v, hv⟩ : ∃ v, a.val? = some v := by
      cases hv : a.val? with
      | none => simp [Admin.isVal, hv] at ha
      | some v => exact ⟨v, rfl⟩
    obtain ⟨V, rfl⟩ := exists_vals_all hl
    exact ⟨v :: V, by rw [Det.val?_eq_some.mp hv]; rfl⟩

theorem exists_first_nonval : ∀ {l : List Admin}, l.all Admin.isVal = false →
    ∃ V e R, e.val? = none ∧ l = vals V ++ e :: R
  | [], h => by simp at h
  | a :: l, h => by
    cases ha : a.val? with
    | none => exact ⟨[], a, l, ha, rfl⟩
    | some v =>
      have hl : l.all Admin.isVal = false := by simpa [List.all_cons, Admin.isVal, ha] using h
      obtain ⟨V, e, R, he, rfl⟩ := exists_first_nonval hl
      refine ⟨v :: V, e, R, he, ?_⟩
      rw [Det.val?_eq_some.mp ha]
      rfl

theorem noEsc_fold {L : List Instr} (h : FoldOk L) (args : List Val) :
    NoEsc (vals args ++ expression L) := by
  obtain ⟨⟨S, hS⟩, hl⟩ := h
  refine ⟨⟨S, ?_⟩, ?_⟩
  · simp only [AdmsB_append, AdmsB_vals, AdmsB_expression, true_and]
    exact hS
  · simp [AdmsLab_append, hl]

/-- The first non-value of a concatenation whose left part is not all values. -/
theorem split_nonval {l₁ l₂ : List Admin} {V : List Val} {e : Admin} {R : List Admin}
    (h : l₁ ++ l₂ = vals V ++ e :: R) (he : e.val? = none) (hv : l₁.all Admin.isVal = false) :
    ∃ R₁, l₁ = vals V ++ e :: R₁ ∧ R = R₁ ++ l₂ := by
  obtain ⟨V₁, e₁, R₁, he₁, rfl⟩ := exists_first_nonval hv
  have h' : vals V₁ ++ e₁ :: (R₁ ++ l₂) = vals V ++ e :: R := by rw [← h]; simp
  obtain ⟨rfl, rfl, rfl⟩ := Det.vals_append_cons_inj h' he₁ he
  exact ⟨R₁, rfl, rfl⟩

theorem bubble_not_all {ws : List Val} {K J : List Admin} (hK : Det.IsBubble K) :
    (vals ws ++ K ++ J).all Admin.isVal = false := by
  rcases hK with rfl | ⟨a, rfl⟩ <;> simp [List.all_append, Admin.isVal, Admin.val?]

/-- The first non-value of a bubble kernel after values. -/
theorem bubble_head {ws V : List Val} {K J R : List Admin} {e : Admin} (hK : Det.IsBubble K)
    (he : e.val? = none) (h : vals ws ++ K ++ J = vals V ++ e :: R) :
    (e = .trap ∧ K = [.trap] ∧ V = ws ∧ R = J) ∨
      ∃ a, e = .plain .throwRef ∧ K = [.ref (.exn a), .plain .throwRef] ∧
        V = ws ++ [.ref (.exn a)] ∧ R = J := by
  rcases hK with rfl | ⟨a, rfl⟩
  · have h' : vals ws ++ Admin.trap :: J = vals V ++ e :: R := by simpa using h
    obtain ⟨rfl, rfl, rfl⟩ := Det.vals_append_cons_inj h' rfl he
    exact .inl ⟨rfl, rfl, rfl, rfl⟩
  · have h' : vals (ws ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: J = vals V ++ e :: R := by
      rw [← h]; simp [vals, Val.toAdmin]
    obtain ⟨rfl, rfl, rfl⟩ := Det.vals_append_cons_inj h' rfl he
    exact .inr ⟨a, rfl, rfl, rfl, rfl⟩

/-- Two bubble decompositions of the same code agree. -/
theorem bubble_eq {P₁ P₂ : List Val} {K₁ K₂ R₁ R₂ : List Admin} (h₁ : Det.IsBubble K₁)
    (h₂ : Det.IsBubble K₂) (h : vals P₁ ++ K₁ ++ R₁ = vals P₂ ++ K₂ ++ R₂) :
    K₁ = K₂ ∧ P₁ = P₂ ∧ R₁ = R₂ := by
  rcases h₂ with rfl | ⟨b, rfl⟩
  · rcases bubble_head h₁ (V := P₂) (R := R₂) (e := .trap) rfl (by simpa using h) with
      ⟨-, rfl, rfl, rfl⟩ | ⟨a, h, -⟩
    · exact ⟨rfl, rfl, rfl⟩
    · cases h
  · have h' : vals P₁ ++ K₁ ++ R₁ = vals (P₂ ++ [.ref (.exn b)]) ++ Admin.plain .throwRef :: R₂ := by
      rw [h]; simp [vals, Val.toAdmin]
    rcases bubble_head h₁ rfl h' with ⟨h, -⟩ | ⟨a, -, rfl, hP, rfl⟩
    · cases h
    · obtain ⟨rfl, hab⟩ := List.append_inj' hP.symm rfl
      simp at hab
      subst hab
      exact ⟨rfl, rfl, rfl⟩

/-- No head step starts at a bubble kernel. -/
theorem head_not_bubble {P : Numerics.Profile} {s : Store H} {f : Frame} {args : List Val}
    {e : Admin} {c₀ : Config H} (hh : Det.Head P s f args e c₀) {V ws : List Val}
    {R K J : List Admin} (hK : Det.IsBubble K)
    (h : vals ws ++ K ++ J = vals V ++ (vals args ++ e :: R)) : False := by
  have hg := hh.good
  rcases bubble_head hK hg.val_none (V := V ++ args) (R := R) (by rw [h]; simp) with
    ⟨rfl, -⟩ | ⟨a, rfl, -, hV, -⟩
  · exact hg.ne_trap rfl
  · have := hg.throwRef rfl
    subst this
    have := (List.append_inj' hV rfl).2
    simp at this

/-- **A step of a folded arm `C ++ Xa`** with `C` not done is a step of `C`, or a trap or
exception bubbling out of `C` through a nonempty prefix of `Xa`. -/
theorem step_left {P : Numerics.Profile} {s s' : Store H} {f f' : Frame} {C Xa b₁ : List Admin}
    (h : Step P Det.noHost ⟨s, f, C ++ Xa⟩ ⟨s', f', b₁⟩) (hv : C.all Admin.isVal = false) :
    (∃ C₁, b₁ = C₁ ++ Xa ∧ Step P Det.noHost ⟨s, f, C⟩ ⟨s', f', C₁⟩) ∨
    (s' = s ∧ f' = f ∧ ∃ (pp q : List Val) (K restC u₂ r : List Admin), Det.IsBubble K ∧
      (q ≠ [] ∨ restC ++ u₂ ≠ []) ∧
      C = vals (pp ++ q) ++ K ++ restC ∧ Xa = u₂ ++ r ∧ u₂ ≠ [] ∧ b₁ = vals pp ++ K ++ r) := by
  rcases Det.Step.decomp h with ⟨vs, args, e, rest, c₀, hcode, hh, hc'⟩ |
      ⟨pp, q, K, u, r, hcode, hK, hqu, hc'⟩
  · simp only at hcode
    have hcode' : C ++ Xa = vals (vs ++ args) ++ e :: rest := by rw [hcode]; simp
    obtain ⟨R₁, rfl, rfl⟩ := split_nonval hcode' hh.good.val_none hv
    simp only [Config.mk.injEq] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := hc'
    left
    refine ⟨vals vs ++ c₀.code ++ R₁, by simp, ?_⟩
    have := Det.lift_instrs vs R₁ ⟨s, f, vals args ++ [e]⟩ c₀ hh.toStep
    simpa using this
  · simp only at hcode
    simp only [Config.mk.injEq] at hc'
    obtain ⟨rfl, rfl, rfl⟩ := hc'
    have hfirst : ∃ U e, K = vals U ++ [e] ∧ e.val? = none := by
      rcases hK with rfl | ⟨a, rfl⟩
      · exact ⟨[], .trap, rfl, rfl⟩
      · exact ⟨[.ref (.exn a)], .plain .throwRef, by simp [vals, Val.toAdmin], rfl⟩
    obtain ⟨U, e, hKe, he⟩ := hfirst
    have hcode' : C ++ Xa = vals (pp ++ q ++ U) ++ e :: (u ++ r) := by rw [hcode, hKe]; simp
    obtain ⟨R₁, hC, hR⟩ := split_nonval hcode' he hv
    have hC' : C = vals (pp ++ q) ++ K ++ R₁ := by rw [hC, hKe]; simp
    rcases List.append_eq_append_iff.mp hR with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · left
      refine ⟨vals pp ++ K ++ a', by simp, ?_⟩
      rw [hC']
      exact Det.Bubble.toStep ⟨pp, q, K, u, a', by simp, hK, hqu, rfl⟩
    · by_cases hc : c' = []
      · subst hc
        left
        refine ⟨vals pp ++ K ++ [], by simp, ?_⟩
        rw [hC']
        exact Det.Bubble.toStep ⟨pp, q, K, R₁, [], by simp, hK, by simpa using hqu, rfl⟩
      · right
        refine ⟨rfl, rfl, pp, q, K, R₁, c', r, hK, ?_, hC', rfl, hc, rfl⟩
        rcases hqu with h | h
        · exact .inl h
        · exact .inr h

theorem sim_head (hok : PrmOk p) {k : Nat} (IH : SimIH p P H k) {s t : Store H} {f : Frame}
    {vs args : List Val} {e : Admin} {rest ns : List Admin} {c₀ : Config H}
    (hsz : sizeOf (vals vs ++ (vals args ++ e :: rest)) < k + 1)
    (hh : Det.Head P s f args e c₀) (hrel : UL p.R (vals vs ++ (vals args ++ e :: rest)) ns)
    (hSR : SR p s t) :
    Res p P ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ ⟨t, f, ns⟩
      (aszs (vals vs ++ (vals args ++ e :: rest))) := by
  have hlt := sizeOf_head_lt (vs := vs) (args := args) (e := e) (rest := rest)
  rw [headDec_code] at hrel
  obtain ⟨nB, rfl, hB⟩ := UL.vals_append_inv hrel
  cases hB with
  | cons he hr =>
    rename_i e' rest'
    obtain ⟨c₀', hprog, hsr, hfr, hrel'⟩ := head_rel hok (IH.mono (by omega)) hh he hSR
    refine ⟨⟨c₀'.store, c₀'.frame, vals vs ++ c₀'.code ++ rest'⟩,
      ⟨hfr.symm, UL.append (UL.append (UL.of_vals vs) hrel') hr⟩, hsr, ?_⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · left
      exact lift_tg (Y := [e']) hp
    · right
      refine ⟨by simp, ?_⟩
      simp only [aszs_append, aszs_cons, aszs_nil] at hw ⊢
      omega
  | site bt hr =>
    rename_i rest'
    cases hh with
    | @block _ _ _ _ t₁ t₂ hbt hm =>
      refine ⟨⟨t, f, vals (vs ++ args) ++ (expression p.R ++ rest')⟩, ⟨rfl, ?_⟩, hSR,
        .inr ⟨rfl, ?_⟩⟩
      · have e : vals (vs ++ args) ++ (expression p.R ++ rest') =
            vals vs ++ ((vals args ++ expression p.R) ++ rest') := by simp
        rw [e]
        have := UL.append (UL.of_vals vs) (UL.run (n := t₂.length) (UL.refl _)
          (noEsc_entry hok args) hr)
        simpa using this
      · simp [aszs_append]
        omega
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
  | run hX' hX hr =>
    rename_i n X X' rest'
    cases hh with
    | ctxtLabel h =>
      rename_i s' f' X₁
      have hsz' : sizeOf X < k := by
        have := Exec.Drv.sizeOf_label_body (n := n) (cont := []) (is := X)
        omega
      obtain ⟨d₁, ⟨hfr₁, hrel₁⟩, hsr, hprog⟩ := IH ⟨s, f, X⟩ ⟨s', f', X₁⟩ ⟨t, f, X'⟩ hsz' h
        ⟨rfl, hX'⟩ hSR
      refine ⟨⟨d₁.store, d₁.frame, vals vs ++ d₁.code ++ rest'⟩,
        ⟨hfr₁, ?_⟩, hsr, ?_⟩
      · have := UL.append (UL.of_vals vs) (UL.run (n := n) hrel₁ (NoEsc.step h hX) hr)
        simpa using this
      · rcases hprog with hp | ⟨rfl, hw⟩
        · left
          have := tg_instrs hp vs rest'
          simpa using this
        · right
          refine ⟨by simp, ?_⟩
          simp only [aszs_append, aszs_cons, asz_label] at hw ⊢
          simp
          omega
    | labelVals hb =>
      rename_i ws
      subst hb
      rw [UL.vals_inv hX']
      refine ⟨⟨t, f, vals (vs ++ []) ++ (vals ws ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
      · simpa using UL.append (UL.of_vals (vs ++ ws)) hr
      · simp [aszs_append]
    | trapLabel =>
      rw [trap_of hX' rfl]
      refine ⟨⟨t, f, vals (vs ++ []) ++ ([.trap] ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
      · simpa using UL.append (UL.of_vals vs) (.cons .trap hr)
      · simp [aszs_append]
    | throwRefLabel =>
      rename_i a
      rw [throw_of hX' rfl]
      refine ⟨⟨t, f, vals (vs ++ []) ++ (throwing a ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
      · simpa [throwing] using UL.append (UL.of_vals vs) (UL.append (UL.refl (throwing a)) hr)
      · simp [aszs_append, isz, vals]
        omega
    | brLabelZero hb hl hn =>
      rename_i vs₁ vs₂ l rest₁
      exact (hX.no_br (vs := vs₁ ++ vs₂) (l := l) (rest := rest₁) (by rw [hb]; simp)).elim
    | brLabelSucc hb hl =>
      rename_i vs₁ l rest₁
      exact (hX.no_br (vs := vs₁) (l := l) (rest := rest₁) (by rw [hb]; simp)).elim
    | returnCallRefLabel hb hc =>
      rename_i vs₁ c rest₁
      exact (hX.no_retCall (vs := vs₁) (rest := rest₁) hc (by rw [hb]; simp)).elim
    | returnLabel hb =>
      rename_i vs₁ rest₁
      exact (hX.no_return (vs := vs₁) (rest := rest₁) (by rw [hb]; simp)).elim
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

  | foldIf bt h₁ h₂ hT hE hr =>
    rename_i T T' E E' X rest'
    cases hh with
    | ifTrue hc =>
      refine ⟨⟨t, f, vals vs ++ [.plain (.block bt T')] ++ (expression X ++ rest')⟩,
        ⟨rfl, ?_⟩, hSR, .inl (lift_tg (Y := [.plain (.if_ bt T' E')]) (tg_head (.ifTrue hc)))⟩
      simpa using UL.append (UL.of_vals vs) (UL.foldBlock bt h₁ hT hr)
    | ifFalse hc =>
      refine ⟨⟨t, f, vals vs ++ [.plain (.block bt E')] ++ (expression X ++ rest')⟩,
        ⟨rfl, ?_⟩, hSR, .inl (lift_tg (Y := [.plain (.if_ bt T' E')]) (tg_head (.ifFalse hc)))⟩
      simpa using UL.append (UL.of_vals vs) (UL.foldBlock bt h₂ hE hr)
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
  | foldBlock bt hT' hT hr =>
    rename_i T T' X rest'
    cases hh with
    | @block _ _ _ _ t₁ t₂ hbt hm =>
      have hN : NoEsc (vals args ++ expression T ++ expression X) := by
        simpa [Execution.Core.expression] using noEsc_fold hT args
      have hstep := tg_head (P := P) (Det.Head.block (s := t) (f := f) (body := T') hbt hm)
      have hTT : UL p.R (vals args ++ expression T) (vals args ++ expression T') :=
        UL.append (UL.of_vals args) (UL.of_UIL hT')
      by_cases hv : (vals args ++ expression T).all Admin.isVal = true
      · obtain ⟨cT, hcT⟩ := exists_vals_all hv
        have hT'v : vals args ++ expression T' = vals cT := UL.vals_inv (hcT ▸ hTT)
        refine ⟨⟨t, f, vals vs ++ vals cT ++ (expression X ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inl ?_⟩
        · have hR : UL p.R (vals args ++ expression T ++ expression X) (vals cT ++ expression X) := by
            rw [hcT]; exact UL.refl _
          have := UL.append (UL.of_vals vs) (UL.run (n := t₂.length) hR hN hr)
          simpa [Execution.Core.expression] using this
        · have h2 := Det.lift_instrs (P := P) vs (expression X ++ rest')
            ⟨t, f, vals [] ++ [.label t₂.length [] (vals args ++ expression T')]⟩ ⟨t, f, vals cT⟩
            (Det.Head.labelVals hT'v).toStep
          refine (lift_tg (Y := [.plain (.block bt T')]) hstep).tail ?_
          simpa using h2
      · refine ⟨⟨t, f, vals vs ++ [.label t₂.length [] (vals args ++ expression T')] ++
          (expression X ++ rest')⟩, ⟨rfl, ?_⟩, hSR,
          .inl (lift_tg (Y := [.plain (.block bt T')]) hstep)⟩
        have := UL.append (UL.of_vals vs)
          (UL.foldLabel (n := t₂.length) (Xa := expression X) hTT hN (by simpa using hv) hr)
        simpa [Execution.Core.expression] using this
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
  | foldLabel hC hX hv hr =>
    rename_i n C C' Xa rest'
    generalize hB' : C ++ Xa = B at hh
    cases hh with
    | ctxtLabel h =>
      rename_i s' f' b₁
      subst hB'
      have hszC : sizeOf C < k := by
        have h1 := Exec.Drv.sizeOf_label_body (n := n) (cont := []) (is := C ++ Xa)
        have h2 := sizeOf_append_left C Xa
        omega
      rcases step_left h hv with ⟨C₁, rfl, hC₁⟩ |
          ⟨hs', hf', pp, q, K, restC, u₂, r, hK, hne, rfl, rfl, hu₂, rfl⟩
      · obtain ⟨d₁, ⟨hfr₁, hrel₁⟩, hsr, hprog⟩ := IH ⟨s, f, C⟩ ⟨s', f', C₁⟩ ⟨t, f, C'⟩ hszC hC₁
          ⟨rfl, hC⟩ hSR
        have hX₁ : NoEsc (C₁ ++ Xa) := NoEsc.step h hX
        have hpre : Steps P Det.noHost ⟨t, f, vals (vs ++ []) ++ (.label n [] C' :: (Xa ++ rest'))⟩
            ⟨d₁.store, d₁.frame, vals vs ++ [.label n [] d₁.code] ++ (Xa ++ rest')⟩ := by
          rcases hprog with hp | ⟨rfl, -⟩
          · have := tg_instrs (tg_label hp n []) vs (Xa ++ rest')
            exact Relation.TransGen.to_reflTransGen (by simpa using this)
          · simpa using (Relation.ReflTransGen.refl :
              Steps P Det.noHost ⟨t, f, vals vs ++ [.label n [] C'] ++ (Xa ++ rest')⟩ _)
        by_cases hv₁ : C₁.all Admin.isVal = true
        · obtain ⟨c₁, rfl⟩ := exists_vals_all hv₁
          have hd : d₁.code = vals c₁ := UL.vals_inv hrel₁
          refine ⟨⟨d₁.store, d₁.frame, vals vs ++ vals c₁ ++ (Xa ++ rest')⟩, ⟨hfr₁, ?_⟩, hsr,
            .inl ?_⟩
          · simpa using UL.append (UL.of_vals vs) (UL.run (n := n) (UL.refl _) hX₁ hr)
          · have h2 := Det.lift_instrs (P := P) vs (Xa ++ rest')
              ⟨d₁.store, d₁.frame, vals [] ++ [.label n [] d₁.code]⟩ ⟨d₁.store, d₁.frame, vals c₁⟩
              (Det.Head.labelVals hd).toStep
            exact Relation.TransGen.tail' hpre (by simpa using h2)
        · refine ⟨⟨d₁.store, d₁.frame, vals vs ++ [.label n [] d₁.code] ++ (Xa ++ rest')⟩,
            ⟨hfr₁, ?_⟩, hsr, ?_⟩
          · simpa using UL.append (UL.of_vals vs) (UL.foldLabel hrel₁ hX₁ (by simpa using hv₁) hr)
          · rcases hprog with hp | ⟨rfl, hw⟩
            · left
              have := tg_instrs (tg_label hp n []) vs (Xa ++ rest')
              simpa using this
            · right
              refine ⟨by simp, ?_⟩
              simp only [aszs_append, aszs_cons, asz_label, aszs_nil] at hw ⊢
              simp
              omega
      · -- a trap or exception bubbles through part of `Xa`
        subst s' f'
        obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv hC
        obtain ⟨n₃, n₄, rfl, h₃, h₄⟩ := UL.append_inv h₁
        rw [UL.vals_inv h₃] at *
        have hK' : n₄ = K := by
          rcases hK with rfl | ⟨a, rfl⟩
          · exact UL.result_inv (r := .trap) h₄
          · exact UL.result_inv (r := .throw a) h₄
        subst hK'
        refine ⟨⟨t, f, vals vs ++ n₄ ++ rest'⟩, ⟨rfl, ?_⟩, hSR, .inl ?_⟩
        · simpa using UL.append (UL.of_vals vs) (UL.foldExit (ws := pp) (J := r) hK hr)
        · -- inside the label: run the arm to the kernel, leave the label, drop `Xa`
          have hlab : Step P Det.noHost ⟨t, f, vals [] ++ [.label n [] n₄]⟩ ⟨t, f, n₄⟩ := by
            rcases hK with rfl | ⟨a, rfl⟩
            · exact (Det.Head.trapLabel (P := P) (s := t) (f := f) (n := n) (cont := [])).toStep
            · exact (Det.Head.throwRefLabel (P := P) (s := t) (f := f) (n := n) (cont := [])
                (a := a)).toStep
          have hdrop : Step P Det.noHost ⟨t, f, n₄ ++ (u₂ ++ r) ++ rest'⟩ ⟨t, f, n₄ ++ rest'⟩ :=
            Det.Bubble.toStep ⟨[], [], n₄, u₂ ++ r, rest', by simp, hK, by simp [hu₂], by simp⟩
          have h2 := Det.lift_instrs (P := P) vs ((u₂ ++ r) ++ rest') _ _ hlab
          have h3 := Det.lift_instrs (P := P) vs [] _ _ hdrop
          have htail : Relation.TransGen (Step P Det.noHost)
              ⟨t, f, vals vs ++ [.label n [] n₄] ++ ((u₂ ++ r) ++ rest')⟩
              ⟨t, f, vals vs ++ n₄ ++ rest'⟩ :=
            (Relation.TransGen.single (by simpa using h2)).tail (by simpa using h3)
          by_cases hqn : pp ++ q ≠ [] ∨ n₂ ≠ []
          · have hb := Det.lift_instrs (P := P) vs ((u₂ ++ r) ++ rest') _ _
              (Det.lift_label (P := P) n [] ⟨t, f, vals (pp ++ q) ++ n₄ ++ n₂⟩ ⟨t, f, n₄⟩
                (Det.Bubble.toStep ⟨[], pp ++ q, n₄, n₂, [], by simp, hK, by simpa using hqn,
                  by simp⟩))
            exact Relation.TransGen.head (by simpa using hb) htail
          · simp only [ne_eq, not_or, not_not] at hqn
            rw [List.append_eq_nil_iff.mp hqn.1 |>.1, List.append_eq_nil_iff.mp hqn.1 |>.2,
              hqn.2]
            simpa using htail
    | labelVals hb =>
      have := congrArg (List.all · Admin.isVal) (hB'.trans hb)
      simp [List.all_append, hv] at this
    | trapLabel =>
      obtain ⟨R₁, rfl, hR⟩ := split_nonval (V := []) (e := .trap) (R := []) (by simpa using hB')
        rfl hv
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hR.symm
      rw [trap_of hC rfl]
      refine ⟨⟨t, f, vals (vs ++ []) ++ ([.trap] ++ rest')⟩, ⟨rfl, ?_⟩, hSR,
        .inl (by simpa using lift_tg (vs := vs) (rest' := rest') (tg_head (P := P) (s := t) (f := f)
          (Det.Head.trapLabel (n := n) (cont := []))))⟩
      simpa using UL.append (UL.of_vals vs) (.cons .trap hr)
    | throwRefLabel =>
      rename_i a
      obtain ⟨R₁, rfl, hR⟩ := split_nonval (V := [.ref (.exn a)]) (e := .plain .throwRef) (R := [])
        (by rw [hB']; simp [vals, Val.toAdmin]) rfl hv
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hR.symm
      rw [throw_of hC (a := a) (by simp [vals, Val.toAdmin])]
      have hp := lift_tg (vs := vs) (args := []) (Y := [Admin.label n [] (throwing a)])
        (rest' := rest') (tg_head (P := P) (Det.Head.throwRefLabel (s := t) (f := f) (n := n)
          (cont := []) (a := a)))
      refine ⟨⟨t, f, vals (vs ++ []) ++ (throwing a ++ rest')⟩, ⟨rfl, ?_⟩, hSR,
        .inl (by simpa [vals, Val.toAdmin] using hp)⟩
      simpa [throwing, vals, Val.toAdmin] using
        UL.append (UL.of_vals vs) (UL.append (UL.refl (R := p.R) (throwing a)) hr)
    | brLabelZero hb hl hn =>
      rename_i vs₁ vs₂ l rest₁
      exact (hX.no_br (vs := vs₁ ++ vs₂) (l := l) (rest := rest₁) (by rw [hB', hb]; simp)).elim
    | brLabelSucc hb hl =>
      rename_i vs₁ l rest₁
      exact (hX.no_br (vs := vs₁) (l := l) (rest := rest₁) (by rw [hB', hb]; simp)).elim
    | returnCallRefLabel hb hc =>
      rename_i vs₁ c rest₁
      exact (hX.no_retCall (vs := vs₁) (rest := rest₁) hc (by rw [hB', hb]; simp)).elim
    | returnLabel hb =>
      rename_i vs₁ rest₁
      exact (hX.no_return (vs := vs₁) (rest := rest₁) (by rw [hB', hb]; simp)).elim
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
  | foldExit hK hr =>
    rename_i n ws K J rest'
    generalize hB' : vals ws ++ K ++ J = B at hh
    cases hh with
    | ctxtLabel h =>
      rename_i s' f' b₁
      subst hB'
      rcases Det.Step.decomp h with ⟨V, args₁, e₁, R, c₁, hcode, hh₁, -⟩ |
          ⟨pp, q, K', u, r, hcode, hK', hqu, hc'⟩
      · exact (head_not_bubble hh₁ hK hcode).elim
      · simp only at hcode
        simp only [Config.mk.injEq] at hc'
        obtain ⟨hs', hf', rfl⟩ := hc'
        subst s' f'
        obtain ⟨rfl, rfl, rfl⟩ := bubble_eq hK' hK hcode.symm
        refine ⟨⟨t, f, vals (vs ++ []) ++ (K' ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
        · simpa using UL.append (UL.of_vals vs) (UL.foldExit (ws := pp) (J := r) hK hr)
        · have hpos : 0 < aszs (vals q) + aszs u := by
            rcases hqu with h | h
            · have := aszs_pos (l := vals q) (by simpa using h); omega
            · have := aszs_pos h; omega
          simp only [aszs_append, aszs_cons, asz_label, aszs_nil, aszs_vals] at hpos ⊢
          simp
          omega
    | labelVals hb =>
      have h2 := bubble_not_all (ws := ws) (J := J) hK
      rw [hB', hb, all_vals] at h2
      cases h2
    | trapLabel =>
      obtain ⟨rfl, rfl, rfl⟩ := bubble_eq hK (.inl rfl) (P₂ := []) (R₂ := []) (by simpa using hB')
      refine ⟨⟨t, f, vals (vs ++ []) ++ ([.trap] ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
      · simpa using UL.append (UL.of_vals vs) (.cons .trap hr)
      · simp
    | throwRefLabel =>
      rename_i a
      obtain ⟨rfl, rfl, rfl⟩ := bubble_eq hK (.inr ⟨a, rfl⟩) (P₂ := []) (R₂ := [])
        (by simpa using hB')
      refine ⟨⟨t, f, vals (vs ++ []) ++ (throwing a ++ rest')⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
      · simpa [throwing] using UL.append (UL.of_vals vs) (UL.append (UL.refl (throwing a)) hr)
      · simp [isz]
        omega
    | brLabelZero hb hl hn =>
      rename_i vs₁ vs₂ l rest₁
      rcases bubble_head hK (ws := ws) (J := J) (e := .plain (.br l)) rfl (V := vs₁ ++ vs₂)
        (R := rest₁) (by rw [hB', hb]; simp) with
        ⟨h, -⟩ | ⟨a, h, -⟩ <;> cases h
    | brLabelSucc hb hl =>
      rename_i vs₁ l rest₁
      rcases bubble_head hK (ws := ws) (J := J) (e := .plain (.br l)) rfl (V := vs₁) (R := rest₁)
        (by rw [hB', hb]; simp) with
        ⟨h, -⟩ | ⟨a, h, -⟩ <;> cases h
    | returnCallRefLabel hb hc =>
      rename_i vs₁ c rest₁
      have hcv : c.val? = none := by
        rcases isReturnCallRef_cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> rfl
      rcases bubble_head hK (ws := ws) (J := J) hcv (V := vs₁) (R := rest₁)
        (by rw [hB', hb]; simp) with
        ⟨rfl, -⟩ | ⟨a, rfl, -⟩
      · exact absurd hc (by simp [Admin.IsReturnCallRef])
      · exact absurd hc (by simp [Admin.IsReturnCallRef])
    | returnLabel hb =>
      rename_i vs₁ rest₁
      rcases bubble_head hK (ws := ws) (J := J) (e := .plain .return_) rfl (V := vs₁) (R := rest₁)
        (by rw [hB', hb]; simp) with
        ⟨h, -⟩ | ⟨a, h, -⟩ <;> cases h
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

theorem sim_bubble {s t : Store H} {f : Frame} {pp q : List Val} {X u r ns : List Admin}
    (hX : Det.IsBubble X) (hqu : q ≠ [] ∨ u ≠ [])
    (hrel : UL p.R (vals (pp ++ q) ++ X ++ (u ++ r)) ns) (hSR : SR p s t) :
    Res p P ⟨s, f, vals pp ++ X ++ r⟩ ⟨t, f, ns⟩ (aszs (vals (pp ++ q) ++ X ++ (u ++ r))) := by
  obtain ⟨n₁, n₂, rfl, h₁, h₂⟩ := UL.append_inv hrel
  obtain ⟨n₃, n₄, rfl, h₃, h₄⟩ := UL.append_inv h₁
  obtain ⟨n₅, n₆, rfl, h₅, h₆⟩ := UL.append_inv h₂
  rw [UL.vals_inv h₃]
  have hX' : n₄ = X := by
    rcases hX with rfl | ⟨a, rfl⟩
    · exact UL.result_inv (r := .trap) h₄
    · exact UL.result_inv (r := .throw a) h₄
  subst hX'
  by_cases hq : q ≠ [] ∨ n₅ ≠ []
  · refine ⟨⟨t, f, vals pp ++ n₄ ++ n₆⟩, ⟨rfl, UL.append (UL.append (UL.of_vals pp)
      (UL.refl n₄)) h₆⟩, hSR, .inl (.single (Det.Bubble.toStep ⟨pp, q, n₄, n₅, n₆, rfl, hX, hq,
      rfl⟩))⟩
  · simp only [ne_eq, not_or, not_not] at hq
    obtain ⟨rfl, rfl⟩ := hq
    have hu : u ≠ [] := by
      rcases hqu with h | h
      · exact absurd rfl h
      · exact h
    have hpos := aszs_pos hu
    refine ⟨⟨t, f, vals (pp ++ []) ++ n₄ ++ ([] ++ n₆)⟩, ⟨rfl, ?_⟩, hSR, .inr ⟨rfl, ?_⟩⟩
    · simpa using UL.append (UL.append (UL.of_vals pp) (UL.refl n₄)) h₆
    · simp only [aszs_append, List.append_nil] at hpos ⊢
      omega

/-- **One step.** Every host-free step of the left configuration is simulated. -/
theorem sim (hok : PrmOk p) : ∀ k : Nat, SimIH p P H k
  | 0 => fun _ _ _ hsz => absurd hsz (Nat.not_lt_zero _)
  | k + 1 => fun c c' d hsz hstep hMR hSR => by
    have IH := sim hok k
    obtain ⟨s, f, code⟩ := c
    obtain ⟨t, fn, ns⟩ := d
    obtain ⟨hfr, hrel⟩ := hMR
    simp only at hfr hrel hSR
    subst hfr
    rcases Det.Step.decomp hstep with ⟨vs, args, e, rest, c₀, hcode, hh, rfl⟩ |
        ⟨pp, q, X, u, r, hcode, hX, hqu, rfl⟩
    · simp only at hcode
      subst hcode
      exact sim_head hok IH hsz hh hrel hSR
    · simp only at hcode
      subst hcode
      exact sim_bubble hX hqu hrel hSR

end main

end Silmaril.Wasm.Binaryen.Unwrap
