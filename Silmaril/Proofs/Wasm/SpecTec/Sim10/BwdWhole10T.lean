module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.BwdSpecial10T

/-!
# The 1.0 backward whole step with stores, in `simEnv10T` (track v10)

Round 4's `wholeStepBwd10B` reads steps of `simEnv10 (fwdB10 nd r)`, where no `STORE` is typed. It
therefore runs under `GoodT10` (a typed code image), which keeps stores out of the code, and the two
successful store rules hold only vacuously. This module proves the backward half in `simEnv10T`,
the environment with the `STORE` erratum, at every `GoodV1` configuration: code and stored functions
may contain stores, and no typing of the configuration is assumed.

* `BwdParts10T G B hn host`: the per-rule obligations, for firings in `simEnv10T B`.
* `backward10T_of_parts`: round 2's recursion (`backward10_of_parts`) for `simEnv10T`. The five
  structural rules are read back with the same generic inversions (`inv_pure10` …), at
  `hasRuleAtT`; the `val*` prefix of `ctxt-instrs` is typed in `simEnv10T`, and `val*` is off
  `tbad10`, so it is a V1 value sequence as before.
* `bwdParts10T_bytesB10`: every leaf rule, at `GoodV1`. The `Step_pure` rules whose quantifiers
  avoid `tbad10` move back as firings (`fires_back10T`) and reuse the round 2–4 lemmas; the others
  are `BwdLeaf10T` and `BwdSpecial10T`; the four store rules are an earlier `bwd10T_store`.
* **`wholeStepBwd10S`**: at `fwdB10 nd r`, every step of the 1.0 script in `simEnv10T` from the
  image of a `GoodV1` configuration is the image of a V1 step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim (SStep Fires dderives_iff_fires cfgV stV)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20 (TypedSome)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T sstepB10T_iff)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (hasRuleAtT findRel?_simEnv10T hasTyp_vals10T)

set_option maxRecDepth 100000

variable {H : Type}

/-! ## The per-rule obligations and the recursion -/

/-- **The per-rule obligations of the 1.0 backward half in `simEnv10T`** (round 2's
`BwdParts10`, for firings in `simEnv10T B`). -/
structure BwdParts10T (G : Config H → Prop) (B : Builtins) (hn : H → String)
    (host : HostSemantics H) : Prop where
  /-- `Step_pure`. -/
  pure : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv10T B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10T B) adminsT (.list w) →
    Fires (simEnv10T B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep c.code code'
  /-- `Step_read`: a V1 step that keeps the state. -/
  read : ∀ (i : Nat) (c : Config H) (w : List Value), G c →
    TypedSome (simEnv10T B) adminsT (.list (adminsToV c.code)) →
    TypedSome (simEnv10T B) adminsT (.list w) →
    Fires (simEnv10T B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 5 ≤ i → ∀ (c : Config H) (w : Value), G c →
    Fires (simEnv10T B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step host c c'

section Rec

variable {G : Config H → Prop} {B : Builtins} {hn : H → String} {host : HostSemantics H}

theorem findRel_pure10T :
    ∃ t rules, (simEnv10T B).findRel? "Step_pure" = some ([], "%~>%", t, rules) := by
  obtain ⟨t, rules, h⟩ := findRel_pure10 B
  exact ⟨t, rules, (findRel?_simEnv10T B _).trans h⟩

theorem findRel_read10T :
    ∃ t rules, (simEnv10T B).findRel? "Step_read" = some ([], "%~>%", t, rules) := by
  obtain ⟨t, rules, h⟩ := findRel_read10 B
  exact ⟨t, rules, (findRel?_simEnv10T B _).trans h⟩

theorem findRel_step10T :
    ∃ t rules, (simEnv10T B).findRel? "Step" = some ([], "%~>%", t, rules) := by
  obtain ⟨t, rules, h⟩ := findRel_step10 B
  exact ⟨t, rules, (findRel?_simEnv10T B _).trans h⟩

/-- The induction hypothesis: the backward conclusion for code smaller than `n`. -/
def IH10T (G : Config H → Prop) (B : Builtins) (hn : H → String) (host : HostSemantics H)
    (n : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), G c → codeSize10 c.code < n →
    SStep (simEnv10T B) (configV hn c) w → BwdAt10 hn host c w

/-- `Step/pure` backwards. -/
theorem bwd_pure10T (Bk : BwdParts10T G B hn host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv10T B) "Step" 0 (.tuple [configV hn c, w])) : BwdAt10 hn host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_pure10 (hasRuleAtT (hasRuleAt_pure10 B)) hf
  obtain ⟨t, rules, hrel⟩ := findRel_pure10T (B := B)
  have e₁ := configV_cfgV10 h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [e₁.2] at ti hi
  obtain ⟨code', rfl, hst⟩ := Bk.pure i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, .pure _ _ hst⟩

/-- `Step/read` backwards. -/
theorem bwd_read10T (Bk : BwdParts10T G B hn host) {c : Config H} {w : Value} (hg : G c)
    (hf : Fires (simEnv10T B) "Step" 1 (.tuple [configV hn c, w])) : BwdAt10 hn host c w := by
  obtain ⟨z, is, js, h₁, h₂, ti, tj, hp⟩ := inv_read10 (hasRuleAtT (hasRuleAt_read10 B)) hf
  obtain ⟨t, rules, hrel⟩ := findRel_read10T (B := B)
  have e₁ := configV_cfgV10 h₁
  obtain ⟨i, hi⟩ := (dderives_iff_fires hrel).1 hp
  rw [← h₁] at hi
  rw [e₁.2] at ti
  obtain ⟨code', rfl, hst⟩ := Bk.read i c js hg ti tj hi
  exact ⟨⟨c.store, c.frame, code'⟩, by rw [h₂, e₁.1]; rfl, hst⟩

/-- `Step/ctxt-label` backwards. -/
theorem bwd_ctxtLabel10T (I : CfgInv10 G) {n : Nat} (ih : IH10T G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10T B) "Step" 2 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', m, cont, is, is', h₁, h₂, hs⟩ :=
    inv_ctxtLabel10 (hasRuleAtT (hasRuleAt_ctxtLabel10 B)) hf
  have e₁ := configV_cfgV10 h₁
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 e₁.2.symm
  obtain ⟨k, cont₀, body, rfl⟩ := adminToV_label_inv10 ha
  have hp : Value.num (.natN k) = m ∧ instrsToV cont₀ = cont ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV z is = configV hn ⟨s, f, body⟩ := by rw [configV_eq10, e₁.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.label _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_label k cont₀ body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := Sim.Bwd.cfgV_inj (hw.trans (configV_eq10 hn _))
  refine ⟨⟨s₂, f₂, [.label k cont₀ K]⟩, ?_, .label hst k cont₀⟩
  rw [h₂, e₃.1, e₃.2, ← hp.1, ← hp.2.1]
  rfl

/-- `Step/ctxt-frame` backwards. -/
theorem bwd_ctxtFrame10T (I : CfgInv10 G) {n : Nat} (ih : IH10T G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10T B) "Step" 3 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨sv, sv', fv, fr, fr', m, is, is', h₁, h₂, hs⟩ :=
    inv_ctxtFrame10 (hasRuleAtT (hasRuleAt_ctxtFrame10 B)) hf
  have e₁ := configV_cfgV10 h₁
  have e₀ : sv = storeV hn s ∧ fv = frameV f := Sim.Bwd.stV_inj e₁.1
  obtain ⟨a, rfl, ha⟩ := adminsToV_eq_single10 e₁.2.symm
  obtain ⟨k, fi, body, rfl⟩ := adminToV_frame_inv10 ha
  have hp : Value.num (.natN k) = m ∧ frameV fi = fr ∧ adminsToV body = is := by
    simpa only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
      Value.list.injEq, and_true, true_and] using ha
  have e₂ : cfgV (stV sv fr) is = configV hn ⟨s, fi, body⟩ := by
    rw [configV_eq10, e₀.1, ← hp.2.1, hp.2.2]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.frame _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_frame k fi body) (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := Sim.Bwd.cfgV_inj (hw.trans (configV_eq10 hn _))
  have e₄ : sv' = storeV hn s₂ ∧ fr' = frameV f₂ := Sim.Bwd.stV_inj e₃.1
  refine ⟨⟨s₂, f, [.frame k f₂ K]⟩, ?_, .frame hst k f⟩
  rw [h₂, e₄.1, e₃.2, e₀.2, ← hp.1, e₄.2]
  rfl

/-- `Step/ctxt-instrs` backwards: V1's `context`. The `val*` prefix is typed in `simEnv10T`,
hence in `simEnv10` (`val*` is off `tbad10`). -/
theorem bwd_ctxtInstrs10T (I : CfgInv10 G) {n : Nat} (ih : IH10T G B hn host n) {s : Store H}
    {f : Frame} {code : List Admin} {w : Value} (hg : G ⟨s, f, code⟩)
    (hlt : codeSize10 code < n + 1)
    (hf : Fires (simEnv10T B) "Step" 4 (.tuple [configV hn ⟨s, f, code⟩, w])) :
    BwdAt10 hn host ⟨s, f, code⟩ w := by
  obtain ⟨z, z', vs, is, is', rest, ⟨ρ, hρ, tv⟩, hne, h₁, h₂, hs⟩ :=
    inv_ctxtInstrs10 (hasRuleAtT (hasRuleAt_ctxtInstrs10 B)) hf
  have tv' := (hasTyp_vals10T B hρ.1).1 tv
  have e₁ := configV_cfgV10 h₁
  obtain ⟨l₁, l₂, l₃, rfl, hl₁, hl₂, hl₃⟩ := adminsToV_eq_append3 e₁.2.symm
  rw [← hl₁] at tv'
  obtain ⟨us, rfl⟩ := values_of_typed10 hρ tv'
  have hne' : values us ≠ [] ∨ l₃ ≠ [] := by
    rcases hne with h | h
    · left; rintro he; rw [he] at hl₁; exact h hl₁.symm
    · right; rintro he; rw [he] at hl₃; exact h hl₃.symm
  have e₂ : cfgV z is = configV hn ⟨s, f, l₂⟩ := by rw [configV_eq10, e₁.1, hl₂]
  obtain ⟨⟨s₂, f₂, K⟩, hw, hst⟩ :=
    ih _ _ (I.mid _ _ _ _ _ hg)
      (Nat.lt_of_lt_of_le (codeSize10_infix hne') (Nat.le_of_lt_succ hlt)) (e₂ ▸ hs)
  have e₃ := Sim.Bwd.cfgV_inj (hw.trans (configV_eq10 hn _))
  refine ⟨⟨s₂, f₂, values us ++ K ++ l₃⟩, ?_, .context hst us l₃⟩
  rw [h₂, e₃.1, e₃.2, ← hl₁, ← hl₃, configV_eq10]
  simp only [adminsToV_map10, List.map_append]

/-- The recursion on `codeSize10`, in `simEnv10T`. -/
theorem bwd_all10T (Bk : BwdParts10T G B hn host) (I : CfgInv10 G) : ∀ n, IH10T G B hn host n
  | 0 => fun _ _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => fun ⟨s, f, code⟩ w hg hlt hs => by
    obtain ⟨t, rules, hrel⟩ := findRel_step10T (B := B)
    obtain ⟨i, hf⟩ := (dderives_iff_fires hrel).1 hs
    match i, hf with
    | 0, hf => exact bwd_pure10T Bk hg hf
    | 1, hf => exact bwd_read10T Bk hg hf
    | 2, hf => exact bwd_ctxtLabel10T I (bwd_all10T Bk I n) hg hlt hf
    | 3, hf => exact bwd_ctxtFrame10T I (bwd_all10T Bk I n) hg hlt hf
    | 4, hf => exact bwd_ctxtInstrs10T I (bwd_all10T Bk I n) hg hlt hf
    | k + 5, hf => exact Bk.step (k + 5) (by omega) _ w hg hf

end Rec

/-- **The 1.0 backward half in `simEnv10T` under `G`, from the per-rule obligations under
`G`.** -/
theorem backward10T_of_parts {G : Config H → Prop} {B : Builtins} {hn : H → String}
    {host : HostSemantics H} (Bk : BwdParts10T G B hn host) (I : CfgInv10 G)
    (c : Config H) (w : Value) (hg : G c) (hs : SStepB (simEnv10T B) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step host c c' :=
  bwd_all10T Bk I (codeSize10 c.code + 1) c w hg (Nat.lt_succ_self _) ((sstepB10T_iff B).1 hs)

/-! ## The leaf rules at `fwdB10` -/

section Leaves

variable {nd : Bool} {r : RelaxedChoice} {hn : H → String} {host : HostSemantics H}

/-- The numeric `Step_pure` rules (20–27) of `simEnv10T`, moved back. -/
theorem fires_backNum10T {B : Builtins} {i : Nat} (hi : i ∈ pureOpen10f) {v : Value}
    (hf : Fires (simEnv10T B) "Step_pure" i v) : Fires (simEnv10 B) "Step_pure" i v := by
  simp only [pureOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [fires_back10T (hasRuleAt10_unopVal B) hf, fires_back10T (hasRuleAt10_unopTrap B) hf,
    fires_back10T (hasRuleAt10_binopVal B) hf, fires_back10T (hasRuleAt10_binopTrap B) hf,
    fires_back10T (hasRuleAt10_testop B) hf, fires_back10T (hasRuleAt10_relop B) hf,
    fires_back10T (hasRuleAt10_cvtopVal B) hf, fires_back10T (hasRuleAt10_cvtopTrap B) hf]

/-- The `Step_pure` rules 0–9 of `simEnv10T`, at `GoodV1` code. -/
theorem bwdPureLo10T {B : Builtins} (i : Nat) (hi : i ≤ 9) (c : Config H) (w : List Value)
    (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    PureBwd10 c.code w := by
  match i, hi, hf with
  | 0, _, hf => exact bwd10_unreachable (fires_back10T (hasRuleAt10_unreachable B) hf)
  | 1, _, hf => exact bwd10_nop (fires_back10T (hasRuleAt10_nop B) hf)
  | 2, _, hf => exact bwd10_drop (fires_back10T (hasRuleAt10_drop B) hf)
  | 3, _, hf => exact bwd10_selectTrue hg.2.2.1 (fires_back10T (hasRuleAt10_selectTrue B) hf)
  | 4, _, hf => exact bwd10_selectFalse hg.2.2.1 (fires_back10T (hasRuleAt10_selectFalse B) hf)
  | 5, _, hf => exact bwd10T_ifTrue hf
  | 6, _, hf => exact bwd10T_ifFalse hf
  | 7, _, hf => exact bwd10T_labelVals hf
  | 8, _, hf => exact bwd10T_brZero hf
  | 9, _, hf => exact bwd10T_brSucc hf

/-- The `Step_pure` rules 10–19 and 28 of `simEnv10T`. -/
theorem bwdPureHi10T {B : Builtins} (i : Nat) (hi : (10 ≤ i ∧ i ≤ 19) ∨ i = 28)
    (c : Config H) (w : List Value)
    (hf : Fires (simEnv10T B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    PureBwd10 c.code w := by
  match i, hi, hf with
  | 10, _, hf => exact bwd10_brIfTrue (fires_back10T (hasRuleAt10_brIfTrue B) hf)
  | 11, _, hf => exact bwd10_brIfFalse (fires_back10T (hasRuleAt10_brIfFalse B) hf)
  | 12, _, hf => exact bwd10_brTableLt (fires_back10T (hasRuleAt10_brTableLt B) hf)
  | 13, _, hf => exact bwd10_brTableGe (fires_back10T (hasRuleAt10_brTableGe B) hf)
  | 14, _, hf => exact bwd10_frameVals (fires_back10T (hasRuleAt10_frameVals B) hf)
  | 15, _, hf => exact bwd10T_returnFrame hf
  | 16, _, hf => exact bwd10T_returnLabel hf
  | 17, _, hf => exact bwd10T_trapVals hf
  | 18, _, hf => exact bwd10T_trapLabel hf
  | 19, _, hf => exact bwd10_trapFrame (fires_back10T (hasRuleAt10_trapFrame B) hf)
  | 28, _, hf => exact bwd10_localTee (fires_back10T (hasRuleAt10_localTee B) hf)

/-- The `Step_pure` rules 0–19 and 28 of `simEnv10T`, at `GoodV1` code. -/
theorem bwdPureCtl10T {B : Builtins} (i : Nat) (hi : i < 29) (ho : i ∉ pureOpen10f)
    (c : Config H) (w : List Value) (hg : GoodV1 c)
    (hf : Fires (simEnv10T B) "Step_pure" i (.tuple [.list (adminsToV c.code), .list w])) :
    PureBwd10 c.code w := by
  simp only [pureOpen10f, List.mem_cons, List.mem_nil_iff, or_false] at ho
  by_cases hlo : i ≤ 9
  · exact bwdPureLo10T i hlo c w hg hf
  · exact bwdPureHi10T i (by omega) c w hf

/-- **The `Step_pure` obligations in `simEnv10T` at `fwdB10`.** -/
theorem bwdPure10T_bytesB10 (i : Nat) (c : Config H) (w : List Value) (hg : GoodV1 c)
    (hf : Fires (simEnv10T (fwdB10 nd r)) "Step_pure" i
      (.tuple [.list (adminsToV c.code), .list w])) :
    ∃ code', w = adminsToV code' ∧ PureStep c.code code' := by
  by_cases hlt : i < 29
  · by_cases ho : i ∈ pureOpen10f
    · exact bwd10_num (numAgree10_bytesB10 _) ho (fires_backNum10T ho hf)
    · exact bwdPureCtl10T i hlt ho c w hg hf
  · exact absurd hf (not_firesPure10T_ge (by omega))

/-- **The `Step_read` obligations in `simEnv10T` at `fwdB10`.** -/
theorem bwdRead10T_bytesB10 (i : Nat) (c : Config H) (w : List Value) (hg : GoodV1 c)
    (hw : TypedSome (simEnv10T (fwdB10 nd r)) adminsT (.list w))
    (hf : Fires (simEnv10T (fwdB10 nd r)) "Step_read" i (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  by_cases hlt : i < 13
  · match i, hlt, hf with
    | 0, _, hf => exact bwd10T_block hf
    | 1, _, hf => exact bwd10T_loop hf
    | 2, _, hf => exact bwd10T_call hg hf
    | 3, _, hf => exact bwd10T_callIndirect hg hf
    | 4, _, hf => exact bwd10T_callIndirectTrap hg hf
    | 5, _, hf => exact bwd10T_callAddr hg hf
    | 6, _, hf => exact bwd10T_localGet hg hf
    | 7, _, hf => exact bwd10T_globalGet hg hf
    | 8, _, hf => exact bwd10T_loadNumTrap hg hf
    | 9, _, hf => exact bwd10T_loadNumVal hg hf
    | 10, _, hf => exact bwd10T_loadPackTrap hg hf
    | 11, _, hf => exact bwd10T_loadPackVal hg hf
    | 12, _, hf => exact bwd10T_memorySize hg hw hf
  · exact absurd hf (not_firesRead10T_ge (by omega))

/-- **The `Step` obligations (rules 5–12) in `simEnv10T` at `fwdB10`**, the four store rules
included. -/
theorem bwdStep10T_bytesB10 (i : Nat) (hi : 5 ≤ i) (c : Config H) (w : Value) (hg : GoodV1 c)
    (hf : Fires (simEnv10T (fwdB10 nd r)) "Step" i (.tuple [configV hn c, w])) :
    ∃ c', w = configV hn c' ∧ Step host c c' := by
  by_cases hlt : i < 13
  · match i, hi, hlt, hf with
    | 5, _, _, hf => exact bwd10T_localSet hg hf
    | 6, _, _, hf => exact bwd10T_globalSet hg hf
    | 7, _, _, hf => exact StoreAgree.bwd10T_store ⟨le_refl _, by omega⟩ hg hf
    | 8, _, _, hf => exact StoreAgree.bwd10T_store ⟨by omega, by omega⟩ hg hf
    | 9, _, _, hf => exact StoreAgree.bwd10T_store ⟨by omega, by omega⟩ hg hf
    | 10, _, _, hf => exact StoreAgree.bwd10T_store ⟨by omega, le_refl _⟩ hg hf
    | 11, _, _, hf => exact bwd10T_memGrowSucceed hg hf
    | 12, _, _, hf => exact bwd10T_memGrowFail hg hf
  · exact absurd hf (not_firesStep10T_ge (by omega))

/-- **The per-rule obligations of the 1.0 backward half in `simEnv10T` at `fwdB10`**, under
`GoodV1` alone. -/
theorem bwdParts10T_bytesB10 (nd : Bool) (r : RelaxedChoice) (hn : H → String)
    (host : HostSemantics H) : BwdParts10T GoodV1 (fwdB10 nd r) hn host where
  pure i c w hg _ _ hf := bwdPure10T_bytesB10 i c w hg hf
  read i c w hg _ hw hf := bwdRead10T_bytesB10 i c w hg hw hf
  step i hi c w hg hf := bwdStep10T_bytesB10 i hi c w hg hf

end Leaves

/-! ## The target -/

/-- **The 1.0 backward whole step with stores**: at `fwdB10 nd r`, every step of the 1.0 script
with the `STORE` erratum (`simEnv10T`) from the image of a `GoodV1` configuration is the image of
a V1 step. No typing of the configuration is assumed, and code and stored functions may contain
stores. -/
theorem wholeStepBwd10S {hn : H → String} {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} {c : Config H} {w : Value} (hg : GoodV1 c)
    (hs : SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) w) :
    ∃ c', w = configV hn c' ∧ Step host c c' :=
  backward10T_of_parts (bwdParts10T_bytesB10 nd r hn host) cfgInv_goodV1 c w hg hs

end Silmaril.Wasm.SpecTec.Sim10.Whole
