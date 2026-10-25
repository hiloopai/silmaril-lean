module

public import Silmaril.Wasm.Binaryen.InlSim
public import Silmaril.Wasm.Binaryen.InlOut

@[expose] public section

/-! # The inlining simulation, generic mode

A head step of generic code (`AN`) is matched by the same head step on the right, except
inside nested activations, which are handled by the induction hypothesis `IH` (in the
generic mode for the same frame, in the caller mode for an activation of the caller).
`call_rel` relates the activations that a call creates: an activation of the caller is a
caller-mode activation (`FR.g`), any other a generic one.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The facts about the caller that the simulation needs. -/
structure PrmOk (p : Prm) : Prop where
  locals : ∃ xs : List ValType, p.cg'.locals = p.cg.locals ++ xs ∧ xs.length = p.ext
  base : ∀ ps rs, Expand p.dg (.func ps rs) → ps.length + p.cg.locals.length = p.base
  body : IRL p p.cg.body p.cg'.body
  bound : p.ext = 0 ∨ p.base + p.ext ≤ 2 ^ 32

/-- Dismiss a family head step whose head belongs to another family. -/
macro "fam_dismiss" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf]))

/-- **Calls.** The activations created by a call in the two stores are related. -/
theorem call_rel (hok : PrmOk p) {s t : Store H} (hSR : SR p s t) {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} {vs : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : vs.length = ps.length)
    (hcode : fi.code = .wasm code) :
    ∃ (fi' : FuncInst H) (code' : Func), t.funcs[a]? = some fi' ∧ fi'.type = fi.type ∧
      fi'.code = .wasm code' ∧
      FR p (Frame.forCall fi.module vs code.locals) (Frame.forCall fi'.module vs code'.locals)
        [.label rs.length [] (expression code.body)]
        [.label rs.length [] (expression code'.body)] := by
  rw [hSR.get a]
  by_cases hag : a = p.ag
  · subst hag
    rw [hSR.hg] at hf
    cases hf
    simp only [gO, FuncCode.wasm.injEq] at hcode
    subst hcode
    refine ⟨gN p, p.cg', by simp, rfl, rfl, ?_⟩
    obtain ⟨xs, hxs, hlen⟩ := hok.locals
    have hb := hok.base ps rs he
    have e : Frame.forCall (gN (H := H) p).module vs p.cg'.locals =
        ⟨(Frame.forCall (gO (H := H) p).module vs p.cg.locals).locals ++
          xs.map (fun t => defaultVal? ((liftVal t).substAll (p.mi.types.map .dt))), p.mi⟩ := by
      simp [Frame.forCall, gN, gO, hxs, List.append_assoc]
    rw [e]
    have hl : (Frame.forCall (gO (H := H) p).module vs p.cg.locals).locals.length = p.base := by
      simp only [Frame.forCall, gO, List.length_append, List.length_map]
      omega
    refine .g (by simp [Frame.forCall, gO]) hl (by simp [hlen])
      (.head (.label .nil (.plain (LGq.of_IRL hok.body))) .nil)
  · simp only [hag, ↓reduceIte]
    exact ⟨fi, code, hf, rfl, hcode, .gen (LN.refl p _)⟩

/-- The result of a generic head step. -/
def GenRes (p : Prm) (P : Numerics.Profile) (t : Store H) (f : Frame) (args : List Val)
    (e e' : Admin) (c₀ : Config H) : Prop :=
  ∃ c₀' : Config H, (Relation.TransGen (Step P Det.noHost) ⟨t, f, vals args ++ [e']⟩ c₀' ∨
      (c₀' = ⟨t, f, vals args ++ [e']⟩ ∧ wL c₀.code < wL (vals args ++ [e]))) ∧
    SR p c₀.store c₀'.store ∧ c₀'.frame = c₀.frame ∧ LN p c₀.code c₀'.code

/-- The induction hypothesis: steps of smaller code are simulated in every mode. -/
def SimIH (p : Prm) (P : Numerics.Profile) (H : Type) (k : Nat) : Prop :=
  ∀ (μ : Mode) (o o' n : Config H), sizeOf o.code < k → Step P Det.noHost o o' → MR p μ o n →
    SR p o.store n.store → Res p P μ o' n (wL o.code)

theorem gen_callData (hok : PrmOk p) {s t : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hSR : SR p s t) (hcd : CallData s f args e c₀) :
    GenRes p P t f args e e c₀ := by
  obtain ⟨vs, a, fi, ps, rs, code, rfl, hc, hf, he, hn, hcode, rfl⟩ := hcd
  obtain ⟨fi', code', hf', ht, hcode', hfr⟩ := call_rel hok hSR hf he hn hcode
  refine ⟨_, .inl (tg_head (.callRefFunc rfl hc hf' (ht ▸ he) hn hcode')), hSR, rfl,
    .cons (.frame hfr) .nil⟩

/-- Plain and call-annotation heads. -/
theorem gen_flat (hok : PrmOk p) {s t : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hh : Det.Head P s f args e c₀) (hSR : SR p s t)
    (hL : ∀ n c b, e ≠ .label n c b) (hH : ∀ n cs b, e ≠ .handler n cs b)
    (hF : ∀ n F b, e ≠ .frame n F b) : GenRes p P t f args e e c₀ := by
  by_cases hS : SimpleE e
  · rcases head_simple hh hS hSR.sameTypes f.locals with hcd | ⟨hfr, hfs, hN⟩
    · exact gen_callData hok hSR hcd
    · obtain ⟨hg, hf, rfl⟩ := hSR
      exact ⟨⟨withFuncs c₀.store (newFuncs p s.funcs), f, c₀.code⟩, .inl (tg_head hN),
        SR.mono ⟨hg, hf, rfl⟩ hfs, hfr.symm, LN.refl p _⟩
  · -- a local access: the frames are equal, so the variable step transfers
    obtain ⟨hg, hf, rfl⟩ := hSR
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
      obtain ⟨hfs, h'⟩ := variableStep_withFuncs h (newFuncs p s.funcs)
      exact ⟨⟨withFuncs s₀ (newFuncs p s.funcs), f₀, is₀⟩, .inl (tg_head (.variable h')),
        SR.mono ⟨hg, hf, rfl⟩ hfs, rfl, LN.refl p _⟩
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

/-! ## Inversion of generic code -/

theorem AN.eq_of_flat {a b : Admin} (h : AN p a b) (hL : ∀ n c b, a ≠ .label n c b)
    (hH : ∀ n cs b, a ≠ .handler n cs b) (hF : ∀ n F b, a ≠ .frame n F b) : b = a := by
  cases h with
  | label _ => exact absurd rfl (hL _ _ _)
  | handler _ => exact absurd rfl (hH _ _ _)
  | frame _ => exact absurd rfl (hF _ _ _)
  | _ => rfl

theorem LN.flat_inv {vs : List Val} {y : Admin} {rest ns : List Admin}
    (hL : ∀ n c b, y ≠ .label n c b) (hH : ∀ n cs b, y ≠ .handler n cs b)
    (hF : ∀ n F b, y ≠ .frame n F b) (h : LN p (vals vs ++ y :: rest) ns) :
    ∃ rest', ns = vals vs ++ y :: rest' ∧ LN p rest rest' := by
  obtain ⟨b, rest', rfl, hb, hr⟩ := LN.vals_cons_inv h
  rw [AN.eq_of_flat hb hL hH hF]
  exact ⟨rest', rfl, hr⟩

/-- Results of a step out of an activation, the same on both sides. -/
def FlatRes (c : List Admin) : Prop :=
  (∃ vs, c = vals vs) ∨ c = [.trap] ∨ (∃ a, c = throwing a) ∨
    ∃ vs a c', c = vals vs ++ [.ref (.func a), c'] ∧
      ((∃ d, c' = .callRefType d) ∨ ∃ y, c' = .plain (.callRef y))

/-- Results of a step of an activation. -/
def FrameRes (p : Prm) (k : Nat) (c c' : List Admin) : Prop :=
  (∃ F₁ F₁' b₁ b₁', c = [.frame k F₁ b₁] ∧ c' = [.frame k F₁' b₁'] ∧ FR p F₁ F₁' b₁ b₁') ∨
    (c' = c ∧ FlatRes c)

theorem retToCallIn_cases {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst) :
    (∃ d, c.retToCallIn m = .callRefType d) ∨ ∃ y, c.retToCallIn m = .plain (.callRef y) := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · rename_i x
    simp only [Admin.retToCallIn]
    split
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact hc.elim

theorem AG.eq_of_ret {E : List (Option Val)} {c y : Admin} (hc : c.IsReturnCallRef)
    (h : AG p E c y) : y = c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · cases h with
    | plain h => cases h; rfl
  · cases h; rfl
  · exact hc.elim

theorem AG.eq_of_plain {E : List (Option Val)} {i : Instr} {y : Admin}
    (hi : ∀ x, i ≠ .call x) (hs : structuredInstr i = false) (h : AG p E (.plain i) y) :
    y = .plain i := by
  cases h with
  | plain h =>
    cases h with
    | flat => rfl
    | site => exact absurd rfl (hi _)
    | block _ => simp [structuredInstr] at hs
    | loop _ => simp [structuredInstr] at hs
    | if_ _ _ => simp [structuredInstr] at hs
    | tryTable _ => simp [structuredInstr] at hs

theorem LGq.nil_inv {ns : List Admin} (h : LGq p [] ns) : ns = [] := by cases h; rfl

/-- Caller code `vals vs ++ y :: rest` with a plain or return-call head `y` that is not a
call, a structured instruction, a trap or `throw_ref`. -/
theorem LG.flat_inv {E : List (Option Val)} {vs : List Val} {y : Admin} {rest ns : List Admin}
    (hy : y.val? = none) (hT : y ≠ .trap) (hR : y ≠ .plain .throwRef)
    (hC : y ≠ .callRefType p.df)
    (hy' : ∀ y', AG p E y y' → y' = y) (h : LG p E (vals vs ++ y :: rest) ns) :
    ∃ rest', ns = vals vs ++ y :: rest' ∧ LGq p rest rest' := by
  rcases LG.vals_cons_inv hy h with ⟨y', rest', rfl, hb, hr⟩ | ⟨vs₀, rest', -, rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [hy' _ hb]; exact ⟨rest', rfl, hr⟩
  · exact absurd rfl hC
  · exact absurd rfl hT
  · exact absurd rfl hR

/-! ## Bubbling a pending trap or throw out of an activation or a label -/

section bubble

variable {s : Store H} {f F : Frame} {k : Nat}

theorem bubble_frame_throw {a : Nat} {Y : List Admin} :
    Relation.TransGen (Step P Det.noHost) ⟨s, f, [.frame k F (throwing a ++ Y)]⟩
      ⟨s, f, throwing a⟩ := by
  rcases Y with _ | ⟨y, Y⟩
  · exact tg_head .throwRefFrame
  · refine .head (.ctxtFrame (fi' := F) ?_) (tg_head .throwRefFrame)
    have := Step.throwRefInstrs (P := P) (host := Det.noHost) (s := s) (f := F) (vs := [])
      (a := a) (rest := y :: Y) (.inr (by simp))
    simpa [throwing, vals] using this

theorem bubble_frame_trap {Y : List Admin} :
    Relation.TransGen (Step P Det.noHost) ⟨s, f, [.frame k F (.trap :: Y)]⟩ ⟨s, f, [.trap]⟩ := by
  rcases Y with _ | ⟨y, Y⟩
  · exact tg_head .trapFrame
  · refine .head (.ctxtFrame (fi' := F) ?_) (tg_head .trapFrame)
    have := Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := F) (vs := [])
      (rest := y :: Y) (.inr (by simp))
    simpa [vals] using this

theorem bubble_label_throw {c : List Instr} {a : Nat} {Y : List Admin} :
    Relation.TransGen (Step P Det.noHost) ⟨s, f, [.label k c (throwing a ++ Y)]⟩
      ⟨s, f, throwing a⟩ := by
  rcases Y with _ | ⟨y, Y⟩
  · exact tg_head .throwRefLabel
  · refine .head (.ctxtLabel (f' := f) (s' := s) ?_) (tg_head .throwRefLabel)
    have := Step.throwRefInstrs (P := P) (host := Det.noHost) (s := s) (f := f) (vs := [])
      (a := a) (rest := y :: Y) (.inr (by simp))
    simpa [throwing, vals] using this

theorem bubble_label_trap {c : List Instr} {Y : List Admin} :
    Relation.TransGen (Step P Det.noHost) ⟨s, f, [.label k c (.trap :: Y)]⟩ ⟨s, f, [.trap]⟩ := by
  rcases Y with _ | ⟨y, Y⟩
  · exact tg_head .trapLabel
  · refine .head (.ctxtLabel (f' := f) (s' := s) ?_) (tg_head .trapLabel)
    have := Step.trapInstrs (P := P) (host := Det.noHost) (s := s) (f := f) (vs := [])
      (rest := y :: Y) (.inr (by simp))
    simpa [vals] using this

end bubble

/-- **Steps of an activation**, in any mode. -/
theorem frame_case {k : Nat} {F F' : Frame} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.frame k F b))) {s t : Store H} {f fn : Frame}
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s f args (.frame k F b) c₀)
    (hfr : FR p F F' b b') (hSR : SR p s t) :
    ∃ c₀' : Config H,
      (Relation.TransGen (Step P Det.noHost) ⟨t, fn, vals args ++ [.frame k F' b']⟩ c₀' ∨
        (c₀' = ⟨t, fn, vals args ++ [.frame k F' b']⟩ ∧
          wL c₀.code < wL (vals args ++ [.frame k F b]))) ∧
      SR p c₀.store c₀'.store ∧ c₀.frame = f ∧ c₀'.frame = fn ∧ FrameRes p k c₀.code c₀'.code := by
  have hmod : F'.module = F.module := by cases hfr with | gen _ => rfl | g hm _ _ _ => exact hm.symm
  cases hh with
  | ctxtFrame h =>
    rename_i s' F₁ b₁
    have hsz : sizeOf b < sizeOf (Admin.frame k F b) := Exec.Drv.sizeOf_frame_body
    cases hfr with
    | gen hb =>
      obtain ⟨n₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ :=
        IH .gen ⟨s, F, b⟩ ⟨s', F₁, b₁⟩ ⟨t, F, b'⟩ hsz h ⟨rfl, hb⟩ hSR
      refine ⟨⟨n₁.store, fn, [.frame k n₁.frame n₁.code]⟩, ?_, hsr, rfl, rfl,
        .inl ⟨F₁, n₁.frame, b₁, n₁.code, rfl, rfl, by rw [hfr₁]; exact .gen hrel⟩⟩
      rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl (tg_frame hp k fn)
      · exact .inr ⟨rfl, by simp only [wL_cons, wL_nil, wA_frame]; simp at hw ⊢; omega⟩
    | g hm hl he hb =>
      rename_i E
      obtain ⟨n₁, ⟨hm₁, hl₁, E₁, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
        IH .g ⟨s, F, b⟩ ⟨s', F₁, b₁⟩ ⟨t, ⟨F.locals ++ E, p.mi⟩, b'⟩ hsz h
          ⟨hm, hl, E, he, rfl, hb⟩ hSR
      refine ⟨⟨n₁.store, fn, [.frame k n₁.frame n₁.code]⟩, ?_, hsr, rfl, rfl,
        .inl ⟨F₁, n₁.frame, b₁, n₁.code, rfl, rfl, by rw [hfr₁]; exact .g hm₁ hl₁ he₁ hrel⟩⟩
      rcases hprog with hp | ⟨rfl, hw⟩
      · exact .inl (tg_frame hp k fn)
      · exact .inr ⟨rfl, by simp only [wL_cons, wL_nil, wA_frame]; simp at hw ⊢; omega⟩
  | frameVals hb hn =>
    rename_i vs
    subst hb
    have hb' : b' = vals vs := by
      cases hfr with
      | gen h => exact LN.vals_inv h
      | g _ _ _ h => exact LG.vals_inv h
    subst hb'
    exact ⟨⟨t, fn, vals vs⟩, .inl (tg_head (.frameVals rfl hn)), hSR, rfl, rfl,
      .inr ⟨rfl, .inl ⟨_, rfl⟩⟩⟩
  | returnFrame hb hn =>
    rename_i vs' vs rest
    subst hb
    have hb' : ∃ rest', b' = vals vs' ++ vals vs ++ [.plain .return_] ++ rest' := by
      have e : vals vs' ++ vals vs ++ [Admin.plain .return_] ++ rest =
          vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
      cases hfr with
      | gen h =>
        rw [e] at h
        obtain ⟨rest', rfl, -⟩ := LN.flat_inv (fun _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) h
        exact ⟨rest', by simp⟩
      | g _ _ _ h =>
        rw [e] at h
        obtain ⟨rest', rfl, -⟩ := LG.flat_inv rfl (by simp) (by simp) (by simp)
          (fun y hy => AG.eq_of_plain (fun _ h => by cases h) rfl hy) h
        exact ⟨rest', by simp⟩
    obtain ⟨rest', rfl⟩ := hb'
    exact ⟨⟨t, fn, vals vs⟩, .inl (tg_head (.returnFrame rfl hn)), hSR, rfl, rfl,
      .inr ⟨rfl, .inl ⟨_, rfl⟩⟩⟩
  | returnCallRefFrameNull hb hc =>
    rename_i vs c rest
    subst hb
    have hb' : ∃ rest', b' = vals vs ++ [.ref .null, c] ++ rest' := by
      have e : vals vs ++ [Admin.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
        simp [vals, Val.toAdmin]
      have hcv : c.val? = none := Det.IsReturnCallRef.val_none hc
      cases hfr with
      | gen h =>
        rw [e] at h
        have hc' : ∀ n cs b, c ≠ .handler n cs b := by
          intro n cs b h'; subst h'; exact hc
        obtain ⟨rest', rfl, -⟩ := LN.flat_inv (fun n c' b h' => by subst h'; exact hc) hc'
          (fun n F b h' => by subst h'; exact hc) h
        exact ⟨rest', by simp [vals, Val.toAdmin]⟩
      | g _ _ _ h =>
        rw [e] at h
        obtain ⟨rest', rfl, -⟩ := LG.flat_inv hcv (fun h' => by subst h'; exact hc)
          (fun h' => by subst h'; exact hc) (fun h' => by subst h'; exact hc)
          (fun y hy => AG.eq_of_ret hc hy) h
        exact ⟨rest', by simp [vals, Val.toAdmin]⟩
    obtain ⟨rest', rfl⟩ := hb'
    exact ⟨⟨t, fn, [.trap]⟩, .inl (tg_head (.returnCallRefFrameNull rfl hc)), hSR, rfl, rfl,
      .inr ⟨rfl, .inr (.inl rfl)⟩⟩
  | returnCallRefFrameAddr hb hc hf he hn =>
    rename_i vs' vs a c rest fi ps rs
    subst hb
    have hb' : ∃ rest', b' = vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest' := by
      have e : vals vs' ++ vals vs ++ [Admin.ref (.func a), c] ++ rest =
          vals (vs' ++ vs ++ [.ref (.func a)]) ++ c :: rest := by
        simp [vals, Val.toAdmin]
      have hcv : c.val? = none := Det.IsReturnCallRef.val_none hc
      cases hfr with
      | gen h =>
        rw [e] at h
        obtain ⟨rest', rfl, -⟩ := LN.flat_inv (fun n c' b h' => by subst h'; exact hc)
          (fun n cs b h' => by subst h'; exact hc) (fun n F b h' => by subst h'; exact hc) h
        exact ⟨rest', by simp [vals, Val.toAdmin]⟩
      | g _ _ _ h =>
        rw [e] at h
        obtain ⟨rest', rfl, -⟩ := LG.flat_inv hcv (fun h' => by subst h'; exact hc)
          (fun h' => by subst h'; exact hc) (fun h' => by subst h'; exact hc)
          (fun y hy => AG.eq_of_ret hc hy) h
        exact ⟨rest', by simp [vals, Val.toAdmin]⟩
    obtain ⟨rest', rfl⟩ := hb'
    obtain ⟨fi', hf', ht⟩ := hSR.sameTypes.get hf
    have hN := Det.Head.returnCallRefFrameAddr (P := P) (s := t) (f := fn) (fi := F') (k := k)
      (vs' := vs') (vs := vs) (rest := rest') rfl hc (by rw [hSR.ht]; exact hf') (ht ▸ he) hn
    rw [hmod] at hN
    exact ⟨_, .inl (tg_head hN), hSR, rfl, rfl,
      .inr ⟨rfl, .inr (.inr (.inr ⟨vs, a, _, rfl, retToCallIn_cases hc F.module⟩))⟩⟩
  | throwRefFrame =>
    rename_i a
    cases hfr with
    | gen h =>
      obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := [.ref (.exn a)]) (y := .plain .throwRef)
        (rest := []) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) h
      cases hr
      exact ⟨⟨t, fn, throwing a⟩, .inl (tg_head .throwRefFrame), hSR, rfl, rfl,
        .inr ⟨rfl, .inr (.inr (.inl ⟨a, rfl⟩))⟩⟩
    | g _ _ _ h =>
      rcases LG.vals_cons_inv (vs := [.ref (.exn a)]) (x := .plain .throwRef) (rest := []) rfl h
        with ⟨y, rest', rfl, hy, hr⟩ | ⟨vs₀, rest', -, h', -⟩ | ⟨h', -⟩ | ⟨-, Y, rfl⟩
      · rw [AG.eq_of_plain (fun _ h => by cases h) rfl hy, LGq.nil_inv hr]
        exact ⟨⟨t, fn, throwing a⟩, .inl (tg_head .throwRefFrame), hSR, rfl, rfl,
          .inr ⟨rfl, .inr (.inr (.inl ⟨a, rfl⟩))⟩⟩
      · cases h'
      · cases h'
      · refine ⟨⟨t, fn, throwing a⟩, .inl ?_, hSR, rfl, rfl,
          .inr ⟨rfl, .inr (.inr (.inl ⟨a, rfl⟩))⟩⟩
        exact bubble_frame_throw
  | trapFrame =>
    cases hfr with
    | gen h =>
      obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := []) (y := .trap) (rest := [])
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) h
      cases hr
      exact ⟨⟨t, fn, [.trap]⟩, .inl (tg_head .trapFrame), hSR, rfl, rfl,
        .inr ⟨rfl, .inr (.inl rfl)⟩⟩
    | g _ _ _ h =>
      rcases LG.vals_cons_inv (vs := []) (x := .trap) (rest := []) rfl h
        with ⟨y, rest', rfl, hy, hr⟩ | ⟨vs₀, rest', -, h', -⟩ | ⟨-, Y, rfl⟩ | ⟨h', -⟩
      · cases hy
        rw [LGq.nil_inv hr]
        exact ⟨⟨t, fn, [.trap]⟩, .inl (tg_head .trapFrame), hSR, rfl, rfl,
          .inr ⟨rfl, .inr (.inl rfl)⟩⟩
      · cases h'
      · refine ⟨⟨t, fn, [.trap]⟩, .inl ?_, hSR, rfl, rfl, .inr ⟨rfl, .inr (.inl rfl)⟩⟩
        exact bubble_frame_trap
      · cases h'
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

/-! ## Reflexivity on reducts -/

theorem LGq.of_okA : ∀ {c : List Admin}, c.all okA = true → LGq p c c
  | [], _ => .nil
  | .plain i :: c, h => .cons (.flat i)
      (LGq.of_okA (by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2))
  | .ref r :: c, h => .ref r
      (LGq.of_okA (by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2))
  | .label _ _ _ :: _, h => by simp [okA] at h
  | .handler _ _ _ :: _, h => by simp [okA] at h
  | .frame _ _ _ :: _, h => by simp [okA] at h
  | .callRefType _ :: _, h => by simp [okA] at h
  | .returnCallRefType _ :: _, h => by simp [okA] at h
  | .trap :: _, h => by simp [okA] at h

theorem LG.of_out {E : List (Option Val)} {c : List Admin} (h : Out c) : LG p E c c := by
  rcases h with rfl | h | ⟨a, d, rfl⟩
  · exact .head .trap .nil
  · exact .plain (LGq.of_okA h)
  · exact .val rfl (.head (.callRef d) .nil)

theorem LG.of_outT {E : List (Option Val)} {c : List Admin} (h : OutT c) : LG p E c c := by
  rcases h with ⟨a, d, rfl⟩ | ⟨x, y, rfl⟩
  · exact .val rfl (.head (.retCallRef d) .nil)
  · exact .plain (.cons (.flat _) (.cons (.flat _) (.cons (.flat _) .nil)))

theorem okI_xform {i : Instr} (h : okI i = true) (base d : Nat) :
    InlineTy.xform base d i = i := by
  cases i <;> simp_all [okI, structuredInstr, IsLocalI, IsTailI, InlineTy.xform]

theorem okI_retGood {i : Instr} (h : okI i = true) (d : Nat) : InlineTy.retGood d i := by
  cases i <;> simp_all [okI, structuredInstr, IsLocalI, IsTailI, InlineTy.retGood]

theorem AI.of_okI {d : Nat} {i : Instr} (h : okI i = true) : AI p d (.plain i) (.plain i) := by
  have := AI.plain (p := p) (okI_retGood h d)
  rwa [okI_xform h] at this

theorem LI.of_okA {d : Nat} : ∀ {c : List Admin}, c.all okA = true → LI p d c c
  | [], _ => .nil
  | .plain i :: c, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact .cons (AI.of_okI h.1) (LI.of_okA h.2)
  | .ref r :: c, h => .cons (.ref r)
      (LI.of_okA (by simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2))
  | .label _ _ _ :: _, h => by simp [okA] at h
  | .handler _ _ _ :: _, h => by simp [okA] at h
  | .frame _ _ _ :: _, h => by simp [okA] at h
  | .callRefType _ :: _, h => by simp [okA] at h
  | .returnCallRefType _ :: _, h => by simp [okA] at h
  | .trap :: _, h => by simp [okA] at h

theorem LI.of_out {d : Nat} {c : List Admin} (h : Out c) : LI p d c c := by
  rcases h with rfl | h | ⟨a, d', rfl⟩
  · exact .cons .trap .nil
  · exact LI.of_okA h
  · exact .cons (.ref _) (.cons (.callRef d') .nil)

/-! ## Generic labels and handlers -/

/-- Labels of generic code. -/
theorem gen_label {n : Nat} {c : List Instr} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.label n c b))) {s t : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s f args (.label n c b) c₀)
    (hb : LN p b b') (hSR : SR p s t) : GenRes p P t f args (.label n c b) (.label n c b') c₀ := by
  have hfl : ∀ {vs y rest}, (∀ n c b, y ≠ Admin.label n c b) → (∀ n cs b, y ≠ .handler n cs b) →
      (∀ n F b, y ≠ .frame n F b) → b = vals vs ++ y :: rest →
      ∃ rest', b' = vals vs ++ y :: rest' := fun h1 h2 h3 hb' => by
    subst hb'
    obtain ⟨rest', rfl, -⟩ := LN.flat_inv h1 h2 h3 hb
    exact ⟨rest', rfl⟩
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.label n c b) := Exec.Drv.sizeOf_label_body
    obtain ⟨n₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH .gen ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨t, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR
    refine ⟨⟨n₁.store, n₁.frame, [.label n c n₁.code]⟩, ?_, hsr, hfr₁, .cons (.label hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp n c)
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    subst hb'
    rw [LN.vals_inv hb]
    exact ⟨_, .inl (tg_head (.labelVals rfl)), hSR, rfl, LN.refl p _⟩
  | brLabelZero hb' hl hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb'
    exact ⟨_, .inl (tg_head (.brLabelZero (vs' := vs') (vs := vs) (rest := rest') (by simp) hl hn)),
      hSR, rfl, LN.refl p _⟩
  | brLabelSucc hb' hl =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb'
    exact ⟨_, .inl (tg_head (.brLabelSucc (rest := rest') (by simp) hl)), hSR, rfl, LN.refl p _⟩
  | returnCallRefLabel hb' hc =>
    rename_i vs c' rest
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc) hb'
    exact ⟨_, .inl (tg_head (.returnCallRefLabel (rest := rest') (by simp) hc)), hSR, rfl,
      LN.refl p _⟩
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb'
    exact ⟨_, .inl (tg_head (.returnLabel (rest := rest') (by simp))), hSR, rfl, LN.refl p _⟩
  | throwRefLabel =>
    rename_i a
    obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := [.ref (.exn a)]) (y := .plain .throwRef)
      (rest := []) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb
    cases hr
    exact ⟨_, .inl (tg_head .throwRefLabel), hSR, rfl, LN.refl p _⟩
  | trapLabel =>
    obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := []) (y := .trap) (rest := [])
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hb
    cases hr
    exact ⟨_, .inl (tg_head .trapLabel), hSR, rfl, LN.refl p _⟩
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

/-- Handlers of generic code. -/
theorem gen_handler {n : Nat} {cs : List Catch} {b b' : List Admin}
    (IH : SimIH p P H (sizeOf (Admin.handler n cs b))) {s t : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (hh : Det.Head P s f args (.handler n cs b) c₀)
    (hb : LN p b b') (hSR : SR p s t) :
    GenRes p P t f args (.handler n cs b) (.handler n cs b') c₀ := by
  have hfl : ∀ {vs y rest}, (∀ n c b, y ≠ Admin.label n c b) → (∀ n cs b, y ≠ .handler n cs b) →
      (∀ n F b, y ≠ .frame n F b) → b = vals vs ++ y :: rest →
      ∃ rest', b' = vals vs ++ y :: rest' := fun h1 h2 h3 hb' => by
    subst hb'
    obtain ⟨rest', rfl, -⟩ := LN.flat_inv h1 h2 h3 hb
    exact ⟨rest', rfl⟩
  have hthrow : ∀ a, b = throwing a → b' = throwing a := fun a hb' => by
    subst hb'
    obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := [.ref (.exn a)]) (y := .plain .throwRef)
      (rest := []) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb
    cases hr
    rfl
  obtain ⟨hg, hf, rfl⟩ := hSR
  have hSR : SR p s (withFuncs s (newFuncs p s.funcs)) := ⟨hg, hf, rfl⟩
  cases hh with
  | ctxtHandler h =>
    rename_i s' f' b₁
    have hsz : sizeOf b < sizeOf (Admin.handler n cs b) := Exec.Drv.sizeOf_handler_body
    obtain ⟨n₁, ⟨hfr₁, hrel⟩, hsr, hprog⟩ := IH .gen ⟨s, f, b⟩ ⟨s', f', b₁⟩ ⟨_, f, b'⟩ hsz h
      ⟨rfl, hb⟩ hSR
    refine ⟨⟨n₁.store, n₁.frame, [.handler n cs n₁.code]⟩, ?_, hsr, hfr₁,
      .cons (.handler hrel) .nil⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_handler hp n cs)
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | brHandler hb' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb'
    exact ⟨_, .inl (tg_head (.brHandler (rest := rest') (by simp))), hSR, rfl, LN.refl p _⟩
  | returnCallRefHandler hb' hc =>
    rename_i vs c' rest
    have e : vals vs ++ [c'] ++ rest = vals vs ++ c' :: rest := by simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by subst h; exact hc)
      (fun _ _ _ h => by subst h; exact hc) (fun _ _ _ h => by subst h; exact hc) hb'
    exact ⟨_, .inl (tg_head (.returnCallRefHandler (rest := rest') (by simp) hc)), hSR, rfl,
      LN.refl p _⟩
  | returnHandler hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨rest', rfl⟩ := hfl (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) hb'
    exact ⟨_, .inl (tg_head (.returnHandler (rest := rest') (by simp))), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerEmpty =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerEmpty), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerCatch he ht =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatch he ht)), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerCatchRef he ht =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerCatchRef he ht)), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerCatchAll =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAll), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerCatchAllRef =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head .throwRefHandlerCatchAllRef), hSR, rfl, LN.refl p _⟩
  | throwRefHandlerNext h =>
    rw [hthrow _ rfl]
    exact ⟨_, .inl (tg_head (.throwRefHandlerNext h)), hSR, rfl, LN.refl p _⟩
  | handlerVals hb' =>
    subst hb'
    rw [LN.vals_inv hb]
    exact ⟨_, .inl (tg_head (.handlerVals rfl)), hSR, rfl, LN.refl p _⟩
  | trapHandler =>
    obtain ⟨rest', rfl, hr⟩ := LN.flat_inv (vs := []) (y := .trap) (rest := [])
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) hb
    cases hr
    exact ⟨_, .inl (tg_head .trapHandler), hSR, rfl, LN.refl p _⟩
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

/-- **Generic head steps.** -/
theorem gen_head (hok : PrmOk p) {e e' : Admin} (IH : SimIH p P H (sizeOf e)) {s t : Store H}
    {f : Frame} {args : List Val} {c₀ : Config H} (hh : Det.Head P s f args e c₀)
    (he : AN p e e') (hSR : SR p s t) : GenRes p P t f args e e' c₀ := by
  have hgood := hh.good
  have h1 : ∀ {a : Admin}, (∀ n c b, a ≠ .label n c b) → (∀ n cs b, a ≠ .handler n cs b) →
      (∀ n F b, a ≠ .frame n F b) → (∀ e', AN p a e' → e' = a) := fun h1 h2 h3 _ h =>
    AN.eq_of_flat h h1 h2 h3
  cases he with
  | plain i =>
    exact gen_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | ref r => exact absurd hgood.val_none (by simp)
  | callRef d =>
    exact gen_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | retCallRef d =>
    exact gen_flat hok hh hSR (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  | label hb => exact gen_label IH hh hb hSR
  | handler hb => exact gen_handler IH hh hb hSR
  | frame hfr =>
    obtain ⟨c₀', hprog, hsr, hf₀, hf₀', hres⟩ := frame_case (fn := f) IH hh hfr hSR
    refine ⟨c₀', hprog, hsr, hf₀'.trans hf₀.symm, ?_⟩
    rcases hres with ⟨F₁, F₁', b₁, b₁', h₁, h₂, hfr₁⟩ | ⟨h₁, -⟩
    · rw [h₁, h₂]; exact .cons (.frame hfr₁) .nil
    · rw [h₁]; exact LN.refl p _
  | trap => exact absurd rfl hgood.ne_trap

end Silmaril.Wasm.Binaryen.InlR
