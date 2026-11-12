module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveNum
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveRef

/-!
# The backward recursion under a code invariant, and the live rules it discharges

`WholeBwd` assembles the backward half from obligations at **every** V2 code. Those obligations are
false at the spec's builtins (`WholeCvtEdge`), so this module runs the same recursion under an
invariant `Q` of the active code that passes to the bodies of labels and frames (`CodeInv`), and
asks the obligations only at code satisfying `Q` (`BwdPartsQ`, `BwdLiveQ`).

With `Q = CvtOkL` (`Sim20.Whole.Defs`: every active `cvtop` is one V2 defines) and builtins interpreting the integer and
float primitives, the 18 live control, numeric, reference and `local.tee` rules of `Step_pure` are
discharged (`bwdLiveQ_of_rest`). What is left is `BwdRestQ`: the remaining live `Step_pure` rules
(the vector rules), the live `Step_read` rules and the `Step` rules from `local.set` on.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (Fires SStep dderives_iff_fires cfgV stV)
open Silmaril.Wasm.SpecTec.Sim.Bwd (cfgV_inj stV_inj)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (IntB)
open Silmaril.Wasm.SpecTec.Sim.Floats (FloatB)

set_option maxRecDepth 100000

variable {H : Type}

/-! ## Invariants and obligations -/

/-- A predicate on active code that holds of the body of a label or frame it holds of. -/
structure CodeInv (Q : List Admin → Prop) : Prop where
  label : ∀ n cont body, Q [.label n cont body] → Q body
  frame : ∀ n fi body, Q [.frame n fi body] → Q body

/-- `BwdParts20`, asked only at code satisfying `Q`. -/
structure BwdPartsQ (Q : List Admin → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`. -/
  pure : ∀ (i : Nat) (code : List Admin) (w : List Value), Q code →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P code code'
  /-- `Step_read`. -/
  read : ∀ (i : Nat) (c : Config H) (w : List Value), Q c.code →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value), Q c.code →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-! ## The recursion -/

section Rec

variable {Q : List Admin → Prop} {B : Builtins} {hn : H → String} {P : Profile}
  {host : HostSemantics H}

/-- The induction hypothesis under `Q`. -/
def IHQ (Q : List Admin → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), Q c.code → codeSize20 c.code < n →
    SStep (simEnv20 B) (configV hn c) w → BwdAt B hn P host c w

/-- `Step/pure` backwards, under `Q`. -/
theorem bwdQ_pure (Bk : BwdPartsQ Q B hn P host) {c : Config H} {w : Value} (hq : Q c.code)
    (hf : Fires (simEnv20 B) "Step" 0 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_pure20 (hasRuleAt_stepPure B) hf
  obtain ⟨t, rules, hrel⟩ : ∃ t rules,
      (simEnv20 B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := ⟨_, _, rfl⟩
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [e₁.2] at ti hi
  obtain ⟨code', rfl, hst⟩ := Bk.pure i c.code js hq ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .pure hst⟩

/-- `Step/read` backwards, under `Q`. -/
theorem bwdQ_read (Bk : BwdPartsQ Q B hn P host) {c : Config H} {w : Value} (hq : Q c.code)
    (hf : Fires (simEnv20 B) "Step" 1 (.tuple [configV hn c, w])) : BwdAt B hn P host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_read20 (hasRuleAt_stepRead B) hf
  obtain ⟨t, rules, hrel⟩ := findRel_read20 B
  have e₁ := configV_cfgV h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [← h₁] at hi
  rw [e₁.2] at ti
  obtain ⟨code', rfl, hst⟩ := Bk.read i c js hq ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .read hst⟩

/-- `Step/ctxt-label` backwards, under `Q`. -/
theorem bwdQ_ctxtLabel (I : CodeInv Q) {n : Nat} (ih : IHQ Q B hn P host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hq : Q code) (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 2 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ := inv_ctxtLabel20 (hasRuleAt_ctxtLabel B) hf
  have e₁ := configV_cfgV h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := adminToV_label_inv ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.label _ _ _ hq)
      (Nat.lt_of_lt_of_le (codeSize20_label k cont₀ body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ?_, .ctxtLabel hst⟩
  rw [h₂, e₃.1, e₃.2, ← hp.1, ← hp.2.1]
  rfl

/-- `Step/ctxt-frame` backwards, under `Q`. -/
theorem bwdQ_ctxtFrame (I : CodeInv Q) {n : Nat} (ih : IHQ Q B hn P host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hq : Q code) (hlt : codeSize20 code < n + 1)
    (hf : Fires (simEnv20 B) "Step" 3 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt B hn P host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, m, is, is', h₁, h₂, hs⟩ := inv_ctxtFrame20 (hasRuleAt_ctxtFrame B) hf
  have e₁ := configV_cfgV h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := adminToV_frame_inv ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.frame _ _ _ hq)
      (Nat.lt_of_lt_of_le (codeSize20_frame k fi body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := cfgV_inj (hw.trans (configV_eq hn _))
  have e₄ : sv' = storeV hn s₂ ∧ fr = frameV f₂ := stV_inj e₃.1
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ?_, .ctxtFrame hst⟩
  rw [h₂, e₄.1, e₃.2, e₀.2, ← hp.1, e₄.2]
  rfl

/-- The backward recursion under `Q`, on the size of the code. -/
theorem bwdQ_all (Bk : BwdPartsQ Q B hn P host) (I : CodeInv Q) : ∀ n, IHQ Q B hn P host n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨s, f, code⟩ w hq hlt hs => by
    obtain ⟨ps, t, rules, hrel, rfl, -⟩ := hasRuleAt_stepPure B
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    match i, hf with
    | 0, hf => exact bwdQ_pure Bk hq hf
    | 1, hf => exact bwdQ_read Bk hq hf
    | 2, hf => exact bwdQ_ctxtLabel I (bwdQ_all Bk I n) hq hlt hf
    | 3, hf => exact bwdQ_ctxtFrame I (bwdQ_all Bk I n) hq hlt hf
    | k + 4, hf => exact Bk.step (k + 4) (by omega) _ w hq hf

end Rec

/-- **The backward half under `Q`, from the per-rule obligations under `Q`.** -/
theorem backward20Q_of_parts {Q : List Admin → Prop} {B : Builtins} {hn : H → String}
    {P : Profile} {host : HostSemantics H} (Bk : BwdPartsQ Q B hn P host) (I : CodeInv Q)
    (c : Config H) (w : Value) (hq : Q c.code) (hs : SStepB (simEnv20 B) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step P host c c' :=
  bwdQ_all Bk I (codeSize20 c.code + 1) c w hq (Nat.lt_succ_self _) ((sstepB20_iff B).1 hs)

/-! ## Dead rules, and the live obligations -/

/-- `BwdLive20`, asked only at code satisfying `Q`. -/
structure BwdLiveQ (Q : List Admin → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∉ deadPure20 → ∀ (code : List Admin) (w : List Value), Q code →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P code code'
  read : ∀ (i : Nat), i ∉ deadRead20 → ∀ (c : Config H) (w : List Value), Q c.code →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value), Q c.code →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- The dead rules discharge themselves under any `Q`. -/
theorem bwdPartsQ_of_live {Q : List Admin → Prop} {B : Builtins} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (L : BwdLiveQ Q B hn P host) : BwdPartsQ Q B hn P host where
  pure i code w hq hc hw hf := by
    by_cases hi : i ∈ deadPure20
    · exact absurd hf (not_firesPure_dead hi hc hw)
    · exact L.pure i hi code w hq hc hw hf
  read i c w hq hc hw hf := by
    by_cases hi : i ∈ deadRead20
    · exact absurd hf (not_firesRead_dead hi hc hw)
    · exact L.read i hi c w hq hc hw hf
  step := L.step

/-! ## The `cvtop` invariant -/


/-- `CvtOkL` is an invariant: it passes to the bodies of labels and frames. -/
theorem codeInv_cvtOk : CodeInv CvtOkL where
  label _ _ _ h := by simpa [CvtOkL, CvtOkA] using h
  frame _ _ _ h := by simpa [CvtOkL, CvtOkA] using h

/-- Under `CvtOkL`, every top-level conversion is one V2 defines. -/
theorem cvtOk_mem : ∀ {code : List Admin}, CvtOkL code → ∀ t₁ t₂ op,
    Admin.plain (.cvtOp t₁ t₂ op) ∈ code → (V2.CvtOp.toShared t₁ t₂ op).isSome
  | [], _, _, _, _, hm => absurd hm (List.not_mem_nil)
  | a :: l, h, t₁, t₂, op, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · simpa [CvtOkL, CvtOkA] using h.1
    · exact cvtOk_mem h.2 t₁ t₂ op hm

/-! ## The live rules discharged, and what is left -/

/-- The live control, reference and `local.tee` rules of `Step_pure` discharged here. -/
def pureCtrl20 : List Nat := [1, 2, 3, 4, 5, 6, 10, 11, 12, 13, 28, 29, 55]

/-- The live numeric rules of `Step_pure` discharged here. -/
def pureNum20 : List Nat := [20, 22, 24, 25, 26]

/-- The live `Step_pure` rules discharged here: `nop`, `drop`, `select-*`, `if-*`, `br_if-*`,
`br_table-*`, `ref.is_null-*`, `local.tee`, `unop-val`, `binop-val`, `testop`, `relop`,
`cvtop-val`. -/
def pureDone20 : List Nat := pureCtrl20 ++ pureNum20

/-- **What is left of the backward obligations under `Q`**: the live `Step_pure` rules not in
`pureDone20` (the vector rules 30–34, 36, 38–54), every live `Step_read` rule and every `Step`
rule from `local.set` on. -/
structure BwdRestQ (Q : List Admin → Prop) (B : Builtins) (hn : H → String) (P : Profile)
    (host : HostSemantics H) : Prop where
  pure : ∀ (i : Nat), i ∉ deadPure20 → i ∉ pureDone20 → ∀ (code : List Admin) (w : List Value),
    Q code → TypedSome (simEnv20 B) instrsT20 (.list (adminsToV code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P code code'
  read : ∀ (i : Nat), i ∉ deadRead20 → ∀ (c : Config H) (w : List Value), Q c.code →
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value), Q c.code →
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- The discharged control, reference and `local.tee` rules, at any code. -/
theorem pureCtrl_bwd {B : Builtins} (P : Profile) {i : Nat} (hi : i ∈ pureCtrl20)
    {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  simp only [pureCtrl20, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bwdPure_nop P hf
  · exact bwdPure_drop P hf
  · exact bwdPure_selectTrue P hf
  · exact bwdPure_selectFalse P hf
  · exact bwdPure_ifTrue P hf
  · exact bwdPure_ifFalse P hf
  · exact bwdPure_brIfTrue P hf
  · exact bwdPure_brIfFalse P hf
  · exact bwdPure_brTableLt P hf
  · exact bwdPure_brTableGe P hf
  · exact bwdPure_refIsNullTrue P hf
  · exact bwdPure_refIsNullFalse P hf
  · exact bwdPure_localTee P hf

/-- The discharged numeric rules, at any code satisfying `CvtOkL`. -/
theorem pureNum_bwd {B : Builtins} {P : Profile} (hI : IntB B) (hF : FloatB P B) {i : Nat}
    (hi : i ∈ pureNum20) {code : List Admin} {w : List Value} (hq : CvtOkL code)
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  simp only [pureNum20, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact bwdPure_unop hI hF hf
  · exact bwdPure_binop hI hF hf
  · exact bwdPure_testop hI hF hf
  · exact bwdPure_relop hI hF hf
  · exact bwdPure_cvtop hF (cvtOk_mem hq) hf

/-- **The 18 discharged `Step_pure` rules**, at any code satisfying `CvtOkL`. -/
theorem pureDone_bwd {B : Builtins} {P : Profile} (hI : IntB B) (hF : FloatB P B) {i : Nat}
    (hi : i ∈ pureDone20) {code : List Admin} {w : List Value} (hq : CvtOkL code)
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w :=
  (List.mem_append.1 hi).elim (fun h => pureCtrl_bwd P h hf) (fun h => pureNum_bwd hI hF h hq hf)

/-- **The live obligations under `CvtOkL`, from what is left.** -/
theorem bwdLiveQ_of_rest {B : Builtins} {hn : H → String} {P : Profile} {host : HostSemantics H}
    (hI : IntB B) (hF : FloatB P B) (R : BwdRestQ CvtOkL B hn P host) :
    BwdLiveQ CvtOkL B hn P host where
  pure i hd code w hq hc hw hf := by
    by_cases hi : i ∈ pureDone20
    · exact pureDone_bwd hI hF hi hq hf
    · exact R.pure i hd hi code w hq hc hw hf
  read := R.read
  step := R.step

/-- **`Task.wholeStepBwdV` from what is left** (`BwdRestQ` at the spec's builtins): the
structural rules of `Step`, the dead rules and the 18 live control, numeric, reference and
`local.tee` rules of `Step_pure` are discharged. -/
theorem wholeStepBwdV_of_rest
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice),
        BwdRestQ CvtOkL (Sim.Floats.floatIntB (Profile.spec nd r)) hn (Profile.spec nd r) host) :
    Task.wholeStepBwdV := fun H hn hinj host nd r c w _ hq hs =>
  backward20Q_of_parts (bwdPartsQ_of_live (bwdLiveQ_of_rest (Sim.Floats.intB_floatIntB _)
    (Sim.Floats.floatB_floatIntB _) (h H hn hinj host nd r))) codeInv_cvtOk c w hq hs

end Silmaril.Wasm.SpecTec.Sim20.Whole
