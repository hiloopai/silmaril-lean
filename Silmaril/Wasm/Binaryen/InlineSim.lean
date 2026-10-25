module

public import Silmaril.Wasm.Binaryen.OperandRun

@[expose] public section

/-! # Binaryen's inlined block against the D-level site: the operand phase

Binaryen's shape evaluates each operand inside the inlined block and stores it at
once (`local.set x_j`); the D-level site evaluates all operands first, outside the
block. `ops_phase` runs both in lockstep, operand by operand: the D-level operand run
is classified (`operand_classify`: it diverges or reaches one value), and the same
run, transported to the frame of Binaryen's shape (`LocSim.steps_low`, which only
needs the frames to agree below `base`), is followed there by the store. The
relation `Rel` between the two frames records the stores done so far.
-/

namespace Silmaril.Wasm.Binaryen.InlSim

open Silmaril.Wasm Execution.Core Validation Numerics SingleThreaded OpRun

variable {H : Type} {P : Profile} {host : HostSemantics H}

@[simp] theorem vals_nil' : vals ([] : List Val) = [] := rfl

/-! ## Lifting runs into contexts -/

theorem steps_ctx {c c' : Config H} (h : Steps P host c c') (pre : List Val) (rest : List Admin) :
    Steps P host ⟨c.store, c.frame, vals pre ++ c.code ++ rest⟩
      ⟨c'.store, c'.frame, vals pre ++ c'.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hst ih =>
    refine ih.tail ?_
    rcases b with ⟨s₁, f₁, is₁⟩
    rcases d with ⟨s₂, f₂, is₂⟩
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .ctxtInstrs hst hne
    · simp only [ne_eq, not_or, not_not] at hne
      obtain ⟨rfl, rfl⟩ := hne
      simpa using hst

theorem steps_label {c c' : Config H} (h : Steps P host c c') (n : Nat) (cont : List Instr) :
    Steps P host ⟨c.store, c.frame, [.label n cont c.code]⟩
      ⟨c'.store, c'.frame, [.label n cont c'.code]⟩ := by
  induction h with
  | refl => exact .refl
  | @tail b d _ hst ih =>
    refine ih.tail ?_
    rcases b with ⟨s₁, f₁, is₁⟩
    rcases d with ⟨s₂, f₂, is₂⟩
    exact .ctxtLabel hst

theorem diverges_label {s : Store H} {f : Frame} {is : List Admin} (n : Nat) (cont : List Instr)
    (h : Diverges P host ⟨s, f, is⟩) : Diverges P host ⟨s, f, [.label n cont is]⟩ := by
  refine InfiniteTrace.coinduct
    (fun d => ∃ (c : Config H), Diverges P host c ∧ d = ⟨c.store, c.frame, [.label n cont c.code]⟩)
    ?_ ⟨_, h, rfl⟩
  rintro d ⟨⟨s, f, is⟩, hc, rfl⟩
  obtain ⟨⟨s₁, f₁, is₁⟩, hs, hc₁⟩ := InfiniteTrace.unfold hc
  exact ⟨_, .ctxtLabel hs, ⟨s₁, f₁, is₁⟩, hc₁, rfl⟩

/-! ## Steps keep the frame's module -/

theorem step_module {c c' : Config H} (h : Step P host c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

theorem steps_module {c c' : Config H} (h : Steps P host c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [step_module hst, ih]

/-! ## The relation between the frames -/

/-- `gl` is `fl` with the values `V` stored at `base ..`. -/
structure Rel (base : Nat) (fl gl : List (Option Val)) (V : List Val) : Prop where
  len : fl.length = gl.length
  low : ∀ i < base, gl[i]? = fl[i]?
  mid : ∀ j < V.length, gl[base + j]? = some V[j]?
  high : ∀ i, base + V.length ≤ i → gl[i]? = fl[i]?

theorem Rel.nil (base : Nat) (fl : List (Option Val)) : Rel base fl fl [] :=
  ⟨rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ _ => rfl⟩

theorem Rel.agree {base : Nat} {fl gl : List (Option Val)} {V : List Val} (h : Rel base fl gl V) :
    LocSim.Agree base fl gl :=
  ⟨h.len, fun i hi => (h.low i hi).symm⟩

/-- Typed frames, without code. -/
def TypedCtx (C₀ : Context) (s : Store H) (f : Frame) : Prop :=
  StoreOk s ∧ ∃ Cf Ct, FrameOk s f Cf ∧ CtxUnder Ct Cf ∧ CtxLe C₀ Ct ∧ Ct.Wf

theorem TypedAt.ctx {C₀ : Context} {c : Config H} {it : InstrType} (h : TypedAt C₀ c it) :
    TypedCtx C₀ c.store c.frame :=
  let ⟨hS, Cf, Ct, hf, hu, hle, hwf, _⟩ := h
  ⟨hS, Cf, Ct, hf, hu, hle, hwf⟩

theorem typedAt_of_ctx {C₀ : Context} {s : Store H} {f : Frame} {bs : List BExpr}
    {it : InstrType} (hT : TypedCtx C₀ s f) (hty : InstrsOk C₀ (BExpr.lowerList bs) it) :
    TypedAt C₀ (codeConfig s f [] bs) it := by
  obtain ⟨hS, Cf, Ct, hf, hu, hle, hwf⟩ := hT
  refine ⟨hS, Cf, Ct, hf, hu, hle, hwf, ?_⟩
  have hm := InstrsOk.mono hty hle.le (r := C₀.return_) (Or.inr rfl)
  have e := hle.eq
  show AdminsOk s Ct (vals [] ++ expression (BExpr.lowerList bs)) it
  rw [e]
  exact AdminsOk.of_instrsOk hm

/-! ## Operands -/

/-- An operand: the local it is stored to, and its code. -/
structure Opd where
  x : LocalIdx
  bs : List BExpr

/-- The hypotheses on an operand: typed `[] → [t]` in `C₀`, the effect conditions, and
writes below `base` only. -/
def Opd.ok (C₀ : Context) (base : Nat) (op : Opd) : Prop :=
  (∃ inits t, InstrsOk C₀ (BExpr.lowerList op.bs) ⟨[], inits, [t]⟩) ∧ OpEff base op.bs ∧
    ∀ x ∈ (effectsList op.bs).localsWritten, x < base

/-- The D-level operand code. -/
def dCode (ops : List Opd) : List Admin := expression (BExpr.lowerList (ops.flatMap (·.bs)))

/-- Binaryen's operand stores. -/
def nCode (ops : List Opd) : List Admin :=
  expression (BExpr.lowerList (ops.map fun op => BExpr.op (.localSet op.x) op.bs))

theorem dCode_cons (op : Opd) (ops : List Opd) :
    dCode (op :: ops) = expression (BExpr.lowerList op.bs) ++ dCode ops := by
  simp [dCode, expression]

theorem nCode_cons (op : Opd) (ops : List Opd) :
    nCode (op :: ops) =
      expression (BExpr.lowerList op.bs) ++ [.plain (.localSet op.x)] ++ nCode ops := by
  simp [nCode, expression]

/-! ## The operand phase -/

theorem ops_phase {C₀ : Context} (hC₀ : C₀.Wf) (hR : C₀.return_ = none) {base r : Nat}
    {restD restN : List Admin} {pre : List Val} :
    ∀ (ops : List Opd) (V : List Val) (s : Store H) (fD : Frame) (gl : List (Option Val)),
    (∀ k op, ops[k]? = some op → op.x.toNat = base + V.length + k) →
    (∀ op ∈ ops, op.ok C₀ base) →
    (∀ k < ops.length, base + V.length + k < fD.locals.length) →
    C₀.locals.length = fD.locals.length →
    TypedCtx C₀ s fD → Rel base fD.locals gl V →
    (Diverges P closedHost ⟨s, fD, vals pre ++ vals V ++ dCode ops ++ restD⟩ ∧
      Diverges P closedHost ⟨s, ⟨gl, fD.module⟩, vals pre ++ [.label r [] (nCode ops ++ restN)]⟩) ∨
    ∃ s' fD' gl' V', V'.length = ops.length ∧
      Steps P closedHost ⟨s, fD, vals pre ++ vals V ++ dCode ops ++ restD⟩
        ⟨s', fD', vals pre ++ vals (V ++ V') ++ restD⟩ ∧
      Steps P closedHost ⟨s, ⟨gl, fD.module⟩, vals pre ++ [.label r [] (nCode ops ++ restN)]⟩
        ⟨s', ⟨gl', fD.module⟩, vals pre ++ [.label r [] restN]⟩ ∧
      fD'.module = fD.module ∧ fD'.locals.length = fD.locals.length ∧ TypedCtx C₀ s' fD' ∧
      Rel base fD'.locals gl' (V ++ V')
  | [], V, s, fD, gl, _, _, _, _, hT, hrel => by
    refine Or.inr ⟨s, fD, gl, [], rfl, ?_, ?_, rfl, rfl, hT, by simpa using hrel⟩
    · have e : vals pre ++ vals V ++ dCode [] ++ restD = vals pre ++ vals (V ++ []) ++ restD := by
        simp [dCode, expression]
      rw [e]
    · have e : nCode [] ++ restN = restN := by simp [nCode, expression]
      rw [e]
  | op :: ops, V, s, fD, gl, hx, hok, hb, hlen, hT, hrel => by
    obtain ⟨⟨inits, t, hty⟩, heff, hw⟩ := hok op (.head _)
    have hT0 : TypedAt C₀ (codeConfig s fD [] op.bs) ⟨[], inits, [t]⟩ :=
      typedAt_of_ctx hT hty
    have hx0 : op.x.toNat = base + V.length := by simpa using hx 0 op rfl
    have hlow0 : LocSim.lowAs base (codeConfig s fD [] op.bs).code = true := by
      show LocSim.lowAs base (vals [] ++ expression (BExpr.lowerList op.bs)) = true
      rw [LocSim.lowAs_append, LocSim.lowAs_vals, LocSim.lowAs_expression, heff.low]
      rfl
    -- the code, decomposed around the current operand
    have eD : vals pre ++ vals V ++ dCode (op :: ops) ++ restD =
        vals (pre ++ V) ++ (codeConfig s fD [] op.bs).code ++ (dCode ops ++ restD) := by
      simp [dCode_cons, codeConfig, List.append_assoc]
    have eN : nCode (op :: ops) ++ restN =
        vals [] ++ (codeConfig s fD [] op.bs).code ++
          ([.plain (.localSet op.x)] ++ nCode ops ++ restN) := by
      simp [nCode_cons, codeConfig, List.append_assoc]
    rcases operand_classify (P := P) hC₀ hR heff hT0 hlen with hdiv | ⟨c', v, hrun, hcode, hT', hext⟩
    · -- the operand diverges, in both shapes
      left
      constructor
      · rw [eD]
        exact LocSim.diverges_ctxtInstrs hdiv
      · have hd₁ := LocSim.diverges_low hdiv hlow0 hrel.agree
        have hd₂ := LocSim.diverges_ctxtInstrs (vs := [])
          (rest := [.plain (.localSet op.x)] ++ nCode ops ++ restN) hd₁
        have hd₃ := diverges_label r [] hd₂
        have hd₄ := LocSim.diverges_ctxtInstrs (vs := pre) (rest := []) hd₃
        rw [eN]
        simpa [codeConfig] using hd₄
    · -- the operand returns `v`
      obtain ⟨s₁, f₁, code₁⟩ := c'
      simp only at hcode
      subst hcode
      have hmod₁ : f₁.module = fD.module := steps_module hrun
      have hlen₁ : f₁.locals.length = fD.locals.length := steps_locals_length hrun
      obtain ⟨gl₁, hrunN, hag₁, -⟩ := LocSim.steps_low hrun hlow0 hrel.agree
      simp only [hmod₁] at hrunN
      -- the locals at and above `base` are not written by the operand
      have hD_hi : ∀ i, base ≤ i → f₁.locals[i]? = fD.locals[i]? := fun i hi =>
        effects_frame_local heff.any (fun hm => absurd (hw i hm) (by omega)) hrun
      have hN_hi : ∀ i, base ≤ i → gl₁[i]? = gl[i]? := fun i hi =>
        effects_frame_local (f := ⟨gl, fD.module⟩) heff.any
          (fun hm => absurd (hw i hm) (by omega)) hrunN
      have hgl : gl.length = fD.locals.length := hrel.len.symm
      have hgl₁ : gl₁.length = gl.length := by rw [← hag₁.1, hlen₁, hgl]
      have hxlt : op.x.toNat < gl₁.length := by
        have := hb 0 (by simp)
        rw [hgl₁, hgl, hx0]; omega
      -- the store in Binaryen's shape
      have hset : Step P closedHost ⟨s₁, ⟨gl₁, fD.module⟩, [v.toAdmin, .plain (.localSet op.x)]⟩
          ⟨s₁, ⟨gl₁.set op.x.toNat (some v), fD.module⟩, []⟩ :=
        .variable (.localSet hxlt)
      have hrel₁ : Rel base f₁.locals (gl₁.set op.x.toNat (some v)) (V ++ [v]) := by
        refine ⟨by rw [List.length_set, ← hag₁.1], fun i hi => ?_, fun j hj => ?_, fun i hi => ?_⟩
        · rw [List.getElem?_set_ne (by omega)]
          exact (hag₁.2 i hi).symm
        · simp only [List.length_append, List.length_singleton] at hj
          rcases Nat.lt_or_ge j V.length with hj' | hj'
          · rw [List.getElem?_set_ne (by omega), hN_hi _ (by omega), hrel.mid j hj',
              List.getElem?_append_left hj']
          · have hjv : j = V.length := by omega
            subst hjv
            rw [hx0, List.getElem?_set_self (by omega)]
            simp
        · simp only [List.length_append, List.length_singleton] at hi
          rw [List.getElem?_set_ne (by omega), hN_hi _ (by omega), hrel.high _ (by omega),
            hD_hi _ (by omega)]
      -- the D-level run so far
      have hD₁ : Steps P closedHost ⟨s, fD, vals pre ++ vals V ++ dCode (op :: ops) ++ restD⟩
          ⟨s₁, f₁, vals pre ++ vals (V ++ [v]) ++ dCode ops ++ restD⟩ := by
        rw [eD]
        have := steps_ctx hrun (pre ++ V) (dCode ops ++ restD)
        simpa [codeConfig, List.append_assoc] using this
      -- Binaryen's run so far
      have hN₁ : Steps P closedHost
          ⟨s, ⟨gl, fD.module⟩, vals pre ++ [.label r [] (nCode (op :: ops) ++ restN)]⟩
          ⟨s₁, ⟨gl₁.set op.x.toNat (some v), fD.module⟩,
            vals pre ++ [.label r [] (nCode ops ++ restN)]⟩ := by
        rw [eN]
        have h₁ := steps_ctx hrunN [] ([.plain (.localSet op.x)] ++ nCode ops ++ restN)
        have h₂ : Step P closedHost
            ⟨s₁, ⟨gl₁, fD.module⟩, vals [] ++ vals [v] ++
              ([.plain (.localSet op.x)] ++ nCode ops ++ restN)⟩
            ⟨s₁, ⟨gl₁.set op.x.toNat (some v), fD.module⟩, vals [] ++ [] ++ (nCode ops ++ restN)⟩ := by
          have e₁ : vals [] ++ vals [v] ++ ([.plain (.localSet op.x)] ++ nCode ops ++ restN) =
              vals [] ++ [v.toAdmin, .plain (.localSet op.x)] ++ (nCode ops ++ restN) := by
            simp [vals]
          rw [e₁]
          by_cases he : nCode ops ++ restN = []
          · rw [he]
            simpa using hset
          · exact Step.ctxtInstrs (vs := []) hset (Or.inr he)
        have h₃ := steps_label (h₁.tail h₂) r []
        have h₄ := steps_ctx h₃ pre []
        simpa [codeConfig] using h₄
      rcases ops_phase hC₀ hR ops (V ++ [v]) s₁ f₁ (gl₁.set op.x.toNat (some v))
          (fun k o hk => by
            have := hx (k + 1) o (by simpa using hk)
            simp only [List.length_append, List.length_singleton]
            omega)
          (fun o ho => hok o (.tail _ ho))
          (fun k hk => by
            have := hb (k + 1) (by simp; omega)
            rw [List.length_append, List.length_singleton, hlen₁]
            omega)
          (by rw [hlen₁]; exact hlen) (TypedAt.ctx hT') hrel₁ with
        ⟨hdD, hdN⟩ | ⟨s', fD', gl', V', hl', hD', hN', hm', hlen', hT'', hrel'⟩
      · left
        refine ⟨InfiniteTrace.of_steps hD₁ hdD, InfiniteTrace.of_steps hN₁ ?_⟩
        rw [hmod₁] at hdN
        exact hdN
      · right
        refine ⟨s', fD', gl', [v] ++ V', by simp [hl'], ?_, ?_, ?_, ?_, hT'', ?_⟩
        · simpa [List.append_assoc] using hD₁.trans hD'
        · rw [hmod₁] at hN'
          exact hN₁.trans hN'
        · rw [hm', hmod₁]
        · rw [hlen', hlen₁]
        · simpa [List.append_assoc] using hrel'

/-! ## The stores of the D-level block -/

/-- The D-level block stores its parameters from the stack, last first. -/
theorem sets_run {s : Store H} {M : ModuleInst} {k base : Nat} {R : List Admin} :
    ∀ (V : List Val) (xs : List LocalIdx) (fl : List (Option Val)),
    V.length = xs.length → (∀ j x, xs[j]? = some x → x.toNat = base + j) →
    (∀ j < xs.length, base + j < fl.length) →
    ∃ fl', Steps P host
        ⟨s, ⟨fl, M⟩, [.label k [] (vals V ++ expression (xs.reverse.map .localSet) ++ R)]⟩
        ⟨s, ⟨fl', M⟩, [.label k [] R]⟩ ∧ fl'.length = fl.length ∧
      (∀ j < V.length, fl'[base + j]? = some V[j]?) ∧
      (∀ i, (i < base ∨ base + V.length ≤ i) → fl'[i]? = fl[i]?)
  | V, xs, fl, hl, hx, hb => by
    induction V using List.reverseRecOn generalizing xs fl with
    | nil =>
      have : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst this
      exact ⟨fl, by simpa [expression] using
        (Relation.ReflTransGen.refl : Steps P host ⟨s, ⟨fl, M⟩, [.label k [] R]⟩ _),
        rfl, fun j hj => by simp at hj,
        fun _ _ => rfl⟩
    | append_singleton V v ih =>
      obtain ⟨xs', x, rfl⟩ : ∃ xs' x, xs = xs' ++ [x] := by
        have hne : xs ≠ [] := by
          rintro rfl
          simp at hl
        exact ⟨xs.dropLast, xs.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
      have hxv : x.toNat = base + V.length := by
        have := hx xs'.length x (by simp)
        rw [this, hl]
      have hx' : ∀ j y, xs'[j]? = some y → y.toNat = base + j := fun j y hj =>
        hx j y (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj)
      have hxlt : x.toNat < fl.length := by
        have := hb xs'.length (by simp)
        omega
      -- the first store
      have hst : Step P host
          ⟨s, ⟨fl, M⟩, [.label k [] (vals (V ++ [v]) ++
            expression ((xs' ++ [x]).reverse.map .localSet) ++ R)]⟩
          ⟨s, ⟨fl.set x.toNat (some v), M⟩, [.label k [] (vals V ++
            expression (xs'.reverse.map .localSet) ++ R)]⟩ := by
        have h₀ : Step P host ⟨s, ⟨fl, M⟩, [v.toAdmin, .plain (.localSet x)]⟩
            ⟨s, ⟨fl.set x.toNat (some v), M⟩, []⟩ := .variable (.localSet hxlt)
        have e₁ : vals (V ++ [v]) ++ expression ((xs' ++ [x]).reverse.map .localSet) ++ R =
            vals V ++ [v.toAdmin, .plain (.localSet x)] ++
              (expression (xs'.reverse.map .localSet) ++ R) := by
          simp [vals, expression, List.append_assoc]
        have e₂ : vals V ++ expression (xs'.reverse.map .localSet) ++ R =
            vals V ++ [] ++ (expression (xs'.reverse.map .localSet) ++ R) := by
          simp [List.append_assoc]
        rw [e₁, e₂]
        refine .ctxtLabel ?_
        by_cases hne : V ≠ [] ∨ expression (xs'.reverse.map Instr.localSet) ++ R ≠ []
        · exact .ctxtInstrs h₀ hne
        · simp only [ne_eq, not_or, not_not] at hne
          rw [hne.1, hne.2]
          simpa using h₀
      obtain ⟨fl', hsteps, hlen, hmid, hout⟩ := ih xs' (fl.set x.toNat (some v)) hl hx'
        (fun j hj => by
          have := hb j (by simp; omega)
          rw [List.length_set]; exact this)
      refine ⟨fl', Relation.ReflTransGen.head hst hsteps, by rw [hlen, List.length_set],
        fun j hj => ?_, fun i hi => ?_⟩
      · simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_or_ge j V.length with hj' | hj'
        · rw [hmid j hj', List.getElem?_append_left hj']
        · have : j = V.length := by omega
          subst this
          rw [hout _ (.inr (by omega)), ← hxv, List.getElem?_set_self hxlt]
          simp
      · simp only [List.length_append, List.length_singleton] at hi
        rw [hout i (by omega), List.getElem?_set_ne (by omega)]

/-! ## Both shapes from a fitting configuration -/

theorem steps_congr {c₁ c₁' c₂ c₂' : Config H} (h₁ : c₁ = c₁') (h₂ : c₂ = c₂')
    (h : Steps P host c₁ c₂) : Steps P host c₁' c₂' := h₁ ▸ h₂ ▸ h

theorem expression_append (a b : List Instr) :
    expression (a ++ b) = expression a ++ expression b := List.map_append

theorem lowerList_sets (xs : List LocalIdx) :
    BExpr.lowerList (xs.map fun x => BExpr.op (.localSet x) []) = xs.map .localSet := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem lowerList_sets_rev (xs : List LocalIdx) :
    BExpr.lowerList (xs.map fun x => BExpr.op (.localSet x) []).reverse =
      (xs.map Instr.localSet).reverse := by
  rw [← List.map_reverse, lowerList_sets, List.map_reverse]

/-- **Joinability of the two shapes.** Binaryen's shape `block btN (stores ++ R)` and the
D-level site `operands ++ [block (typeIdx ty) (sets ++ R)]` either reach a common
configuration or both diverge. -/
theorem shapes_joinableBot {C : Context} {it : InstrType} {base : Nat} {ops : List Opd}
    {ty : TypeIdx} {btN : BlockType} {R : List BExpr} {xsD : List LocalIdx}
    {ps rs : List CValType}
    (hops : ∀ op ∈ ops, op.ok { C with labels := [], return_ := none } base)
    (hx : ∀ k op, ops[k]? = some op → op.x.toNat = base + k)
    (hxsD : xsD.length = ops.length) (hxsD' : ∀ j x, xsD[j]? = some x → x.toNat = base + j)
    (hbound : ∀ k < ops.length, base + k < C.locals.length)
    (hty : (C.type? ty >>= DefType.funcType?) = some (ps, rs)) (hps : ps.length = ops.length)
    (hbtN : ∀ m : ModuleInst, ∃ t₂, m.blockType? btN = some ([], t₂) ∧ t₂.length = rs.length) :
    JoinableBot P C it [BExpr.block btN (ops.map (fun op => .op (.localSet op.x) op.bs) ++ R)]
      (ops.flatMap (·.bs) ++
        [BExpr.block (.typeIdx ty) (xsD.reverse.map (fun x => .op (.localSet x) []) ++ R)]) := by
  intro H s f vs hfit
  obtain ⟨hs, hf, -⟩ := hfit
  have hwf : ({ C with labels := [], return_ := none } : Context).Wf :=
    FrameOk.ctxWf hs (storeTypesOk_of hs) hf
  have hlen : ({ C with labels := [], return_ := none } : Context).locals.length =
      f.locals.length := (FrameOk.ctx_fields hf).2.2
  have hlen0 : C.locals.length = f.locals.length := hlen
  have hT : TypedCtx { C with labels := [], return_ := none } s f :=
    ⟨hs, _, _, hf, CtxUnder.refl _, CtxLe.refl _, hwf⟩
  have htypes : C.types = f.module.types :=
    CtxOk.types (C := { C with labels := [], return_ := none }) (CtxOk.ofFrame₀ hf)
  obtain ⟨t₂N, hbtN', ht₂N⟩ := hbtN f.module
  -- Binaryen's shape enters its block
  have hN₀ : Steps P closedHost
      (codeConfig s f vs [BExpr.block btN (ops.map (fun op => .op (.localSet op.x) op.bs) ++ R)])
      ⟨s, ⟨f.locals, f.module⟩, vals vs ++
        [.label t₂N.length [] (nCode ops ++ expression (BExpr.lowerList R))]⟩ := by
    have h₀ : Step P closedHost
        ⟨s, f, vals [] ++ [.plain (.block btN (BExpr.lowerList (ops.map
          (fun op => .op (.localSet op.x) op.bs)) ++ BExpr.lowerList R))]⟩
        ⟨s, f, [.label t₂N.length [] (vals [] ++ expression (BExpr.lowerList (ops.map
          (fun op => .op (.localSet op.x) op.bs)) ++ BExpr.lowerList R))]⟩ :=
      .block hbtN' rfl
    refine steps_congr ?_ ?_ (steps_ctx (Relation.ReflTransGen.single h₀) vs [])
    · simp [codeConfig, expression, BExpr.lower]
    · simp [nCode, expression_append]
  -- the operand phase
  have eD : codeConfig s f vs (ops.flatMap (·.bs) ++
        [BExpr.block (.typeIdx ty) (xsD.reverse.map (fun x => .op (.localSet x) []) ++ R)]) =
      ⟨s, f, vals vs ++ vals [] ++ dCode ops ++
        [.plain (.block (.typeIdx ty) (xsD.reverse.map .localSet ++ BExpr.lowerList R))]⟩ := by
    simp [codeConfig, dCode, expression, BExpr.lower, lowerList_sets_rev]
  rcases ops_phase (P := P) hwf rfl (r := t₂N.length)
      (restD := [.plain (.block (.typeIdx ty) (xsD.reverse.map .localSet ++ BExpr.lowerList R))])
      (restN := expression (BExpr.lowerList R)) (pre := vs) ops [] s f f.locals
      (by simpa using hx) hops (fun k hk => by have := hbound k hk; simp; omega) hlen hT
      (Rel.nil base f.locals) with
    ⟨hdD, hdN⟩ | ⟨s', fD', gl', V', hl', hD', hN', hm', hlen', hT', hrel'⟩
  · -- both diverge
    right; right
    exact ⟨InfiniteTrace.of_steps hN₀ hdN, by rw [eD]; exact hdD⟩
  · -- the D-level block, then its stores
    left
    have hbt : fD'.module.blockType? (.typeIdx ty) = some (ps, rs) := by
      rw [hm']
      show f.module.types[ty.toNat]? >>= DefType.funcType? = _
      rw [← htypes]
      exact hty
    have hV : V'.length = ps.length := by rw [hl', hps]
    have hD₁ : Step P closedHost
        ⟨s', fD', vals V' ++ [.plain (.block (.typeIdx ty)
          (xsD.reverse.map .localSet ++ BExpr.lowerList R))]⟩
        ⟨s', fD', [.label rs.length [] (vals V' ++ expression
          (xsD.reverse.map .localSet ++ BExpr.lowerList R))]⟩ :=
      .block hbt hV
    obtain ⟨fl', hsets, hfl, hmid, hout⟩ := sets_run (P := P) (host := closedHost) (s := s')
      (M := fD'.module) (k := rs.length) (base := base) (R := expression (BExpr.lowerList R))
      V' xsD fD'.locals (by rw [hl', hxsD]) hxsD'
      (fun j hj => by have := hbound j (by omega); rw [hlen']; omega)
    refine ⟨⟨s', ⟨gl', f.module⟩, vals vs ++ [.label t₂N.length [] (expression
      (BExpr.lowerList R))]⟩, ?_, ?_⟩
    · exact hN₀.trans hN'
    · rw [eD]
      have h₂ := steps_ctx (Relation.ReflTransGen.single hD₁) vs []
      have h₃ := steps_ctx hsets vs []
      have hfl' : fl' = gl' := by
        apply List.ext_getElem?
        intro i
        rcases Nat.lt_or_ge i base with hi | hi
        · rw [hout i (.inl hi), hrel'.low i hi]
        rcases Nat.lt_or_ge i (base + V'.length) with hi' | hi'
        · obtain ⟨j, rfl⟩ : ∃ j, i = base + j := ⟨i - base, by omega⟩
          rw [hmid j (by omega), hrel'.mid j (by simpa using (show j < V'.length by omega))]
          simp
        · rw [hout i (.inr hi'), hrel'.high i (by simpa using hi')]
      refine hD'.trans (steps_congr ?_ ?_ (h₂.trans (steps_congr ?_ rfl h₃)))
      · simp
      · simp [hfl', hm', ht₂N]
      · simp [expression_append, List.append_assoc]

end Silmaril.Wasm.Binaryen.InlSim
