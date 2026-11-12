module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FloatSimd.Assembly
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Family V: backward, SpecTec → Core, for the vector rules

`Backward.pure i`, for vector rules `i` of `Step_pure`: whatever the rule derives from the image of
a typed configuration is the image of a Core `VectorStep`. The proofs invert the rule's conclusion
(`inv_*`), decode the instruction sequence back to Core (`VecDecode`, syntactic facts about the
encoding that family E is to discharge, plus `vecInstrV?`'s own inversions proved here), and read
the operator call through `VecAgree`, whose fields are stated so that `Applies.unique` turns them
around.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules vconstV)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV trapV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core

/-! ## Decoding -/

/-- The SIMD tags `vecInstrV?` produces. -/
def vecTags : List MixopS :=
  ["VVUNOP", "VVBINOP", "VVTERNOP", "VVTESTOP", "VUNOP", "VBINOP", "VTERNOP", "VTESTOP",
    "VRELOP", "VSHIFTOP", "VBITMASK", "VSWIZZLOP", "VSHUFFLE", "VEXTUNOP", "VEXTBINOP",
    "VEXTTERNOP", "VNARROW", "VCVTOP", "VSPLAT", "VEXTRACT_LANE", "VREPLACE_LANE"]

/-- Syntactic facts about the encoding, for family E: a `VCONST` image comes from a vector
constant, and an image with a SIMD tag comes from the instruction `vecInstrV?` encodes. Both hold
by inspection of `adminToV` (no other clause produces these tags); they are stated, not proved,
here. -/
structure VecDecode : Prop where
  /-- `VCONST V128 c` is the image of `v128.const`. -/
  vconst : ∀ (a : Admin) (c : Value), adminToV a = vconstV c → ∃ b, a = vconst b ∧ c = vecV b
  /-- `CONST I32 c` is the image of `i32.const`. -/
  i32const : ∀ (a : Admin) (c : Value), adminToV a = Equiv.Execution.constV
    Equiv.Execution.i32V c → ∃ n, a = constI32 n ∧ c = i32NV n
  /-- An image with a SIMD tag is the image of a SIMD instruction. -/
  vinstr : ∀ (a : Admin) (tag : MixopS) (x : Value), tag ∈ vecTags → adminToV a = .case tag x →
    ∃ i, a = .plain i ∧ vecInstrV? i = some (.case tag x)

/-- `vecInstrV?` at `VVUNOP`. -/
theorem vecInstrV?_vvunop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VVUNOP" x)) :
    ∃ op, i = .vecUnOp op ∧ x = .tuple [vecTypeV, vvunopV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VUNOP`: an integer or a float shape. -/
theorem vecInstrV?_vunop {i : Instr} {x : Value} (h : vecInstrV? i = some (.case "VUNOP" x)) :
    (∃ s op, i = .vecIntUnOp s op ∧ x = .tuple [ishV s, vIntUnOpV op]) ∨
      (∃ s op, i = .vecFloatUnOp s op ∧ x = .tuple [fshV s, vFloatUnOpV op]) := by
  cases i <;> simp [vecInstrV?] at h
  · exact .inl ⟨_, _, rfl, h.symm⟩
  · exact .inr ⟨_, _, rfl, h.symm⟩

/-- Two images decode to two Core instructions. -/
theorem adminsToV_eq_two {is : List Admin} {x y : Value} (h : adminsToV is = [x, y]) :
    ∃ a b, is = [a, b] ∧ adminToV a = x ∧ adminToV b = y := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a, b], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
      exact ⟨a, b, rfl, h.1, h.2.1⟩

/-! ## Inverting a rule instance -/

/-- A rule that fires is the rule the environment has at that index. -/
theorem fires_body {env : Env} {x : IL.Id} {i : Nat} {r : Rule} {v : Value}
    (hr : HasRuleAt env x "%~>%" i r) (hf : Fires env x i v) :
    RuleBody env (DDerives env (otherwise env)) (otherwise env x [] i v) [] [] "%~>%" r v := by
  obtain ⟨t, rules, r', hrel, hi, hb⟩ := hf
  obtain ⟨ps, t', rules', hrel', -, hi'⟩ := hr
  have hrules : rules' = rules := by
    rw [hrel] at hrel'
    simp only [Option.some.injEq, Prod.mk.injEq] at hrel'
    exact hrel'.2.2.2.symm
  have hrr : r' = r := by
    rw [hrules, hi] at hi'
    exact Option.some.inj hi'
  exact hrr ▸ hb

/-- A two-component tuple, inverted. -/
theorem inv_tup2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) v) :
    ∃ v₁ v₂, v = .tuple [v₁, v₂] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain rfl := evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, rfl, h₁, h₂⟩

/-- A one-element list, inverted. -/
theorem inv_list1 {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e]) v) : ∃ w, v = .list [w] ∧ EvalExp env ρ e w := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain rfl := evalExps_nil_iff.1 hws
  exact ⟨w, rfl, hw⟩

/-- A two-element list, inverted. -/
theorem inv_list2 {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂]) v) :
    ∃ v₁ v₂, v = .list [v₁, v₂] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w₁, ws, h₁, hws, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws', h₂, hws', rfl⟩ := evalExps_cons_iff.1 hws
  obtain rfl := evalExps_nil_iff.1 hws'
  exact ⟨w₁, w₂, rfl, h₁, h₂⟩

/-- A nullary case, inverted. -/
theorem inv_nil {env : Env} {ρ : VarEnv} {mo : MixopS} {v : Value}
    (h : EvalExp env ρ (.caseE mo (.tupE [])) v) : v = caseNilV mo := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain rfl := evalExps_nil_iff.1 hvs
  rfl

/-- `VCONST V128 x`, inverted. -/
theorem inv_vconst {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE x])) v) :
    ∃ c, v = vconstV c ∧ ρ.findVal? x = some c := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨v₁, c, rfl, h₁, h₂⟩ := inv_tup2 hw
  obtain rfl := inv_nil h₁
  exact ⟨c, rfl, evalExp_varE_iff.1 h₂⟩

/-- `OP (x, y)`, inverted. -/
theorem inv_op2 {env : Env} {ρ : VarEnv} {mo : MixopS} {x y : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE mo (.tupE [.varE x, .varE y])) v) :
    ∃ a b, v = .case mo (.tuple [a, b]) ∧ ρ.findVal? x = some a ∧ ρ.findVal? y = some b := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨a, b, rfl, h₁, h₂⟩ := inv_tup2 hw
  exact ⟨a, b, rfl, evalExp_varE_iff.1 h₁, evalExp_varE_iff.1 h₂⟩

/-- A call of a definition the scope does not rebind, inverted. -/
theorem inv_call {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg} {ws : List ArgV}
    {v : Value} (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (h : EvalExp env ρ (.callE f args) v) : Applies env f ws v :=
  (applies_iff_callDef hd hx).2 (evalExp_callE_iff.1 h)

/-- An `if` premise, inverted. -/
theorem inv_if {env : Env} {D : Interp} {els : Prop} {ρ : VarEnv} {e : Exp}
    (h : PremW env D els ρ (.ifPr e)) : EvalExp env ρ e (.bool true) := by
  cases h with
  | ifPr h => exact h

/-- `c <- $f(args)`, inverted: `c` is in the call's result list. -/
theorem inv_mem_call {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} {L : List Value} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (ha : Applies env f ws (.list L))
    (h : EvalExp env ρ (.memE (.varE c) (.callE f args)) (.bool true)) : cv ∈ L := by
  obtain ⟨v₁, v₂, h₁, h₂, hm⟩ := evalExp_memE_iff.1 h
  have e₁ : v₁ = cv := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans hc)
  have e₂ : v₂ = .list L := Equiv.ExecNumeric.Applies.unique (inv_call hd hx h₂) ha
  rw [e₁, e₂] at hm
  simpa [memValue] using hm

/-- `$f(args) = []`, inverted. -/
theorem inv_call_nil {env : Env} {ρ : VarEnv} {f : IL.Id} {args : List Arg} {ws : List ArgV}
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.listE [])) (.bool true)) :
    Applies env f ws (.list []) := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h₂
  obtain rfl := evalExps_nil_iff.1 hvs
  have hv₁ : v₁ = .list [] := by
    simp only [cmpValues] at hcmp
    simpa using hcmp
  exact hv₁ ▸ inv_call hd hx h₁

/-- Three images decode to three Core instructions. -/
theorem adminsToV_eq_three {is : List Admin} {x y z : Value} (h : adminsToV is = [x, y, z]) :
    ∃ a b c, is = [a, b, c] ∧ adminToV a = x ∧ adminToV b = y ∧ adminToV c = z := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a, b, c], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
      exact ⟨a, b, c, rfl, h.1, h.2.1, h.2.2.1⟩

/-- Four images decode to four Core instructions. -/
theorem adminsToV_eq_four {is : List Admin} {x y z u : Value}
    (h : adminsToV is = [x, y, z, u]) :
    ∃ a b c d, is = [a, b, c, d] ∧ adminToV a = x ∧ adminToV b = y ∧ adminToV c = z ∧
      adminToV d = u := by
  rw [adminsToV_eq_map] at h
  match is, h with
  | [a, b, c, d], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
      exact ⟨a, b, c, d, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- `[VCONST c_1, OP x]` decodes to `[v128.const b, i]`. -/
theorem decode_c1 (D : VecDecode) {is : List Admin} {c₁ x : Value} {tag : MixopS}
    (ht : tag ∈ vecTags) (h : adminsToV is = [vconstV c₁, .case tag x]) :
    ∃ b i, is = [vconst b, .plain i] ∧ c₁ = vecV b ∧ vecInstrV? i = some (.case tag x) := by
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := adminsToV_eq_two h
  obtain ⟨b, rfl, hb⟩ := D.vconst a₁ c₁ h₁
  obtain ⟨i, rfl, hi⟩ := D.vinstr a₂ tag x ht h₂
  exact ⟨b, i, rfl, hb, hi⟩

/-- `[VCONST c_1, VCONST c_2, OP x]` decodes. -/
theorem decode_c2 (D : VecDecode) {is : List Admin} {c₁ c₂ x : Value} {tag : MixopS}
    (ht : tag ∈ vecTags) (h : adminsToV is = [vconstV c₁, vconstV c₂, .case tag x]) :
    ∃ b₁ b₂ i, is = [vconst b₁, vconst b₂, .plain i] ∧ c₁ = vecV b₁ ∧ c₂ = vecV b₂ ∧
      vecInstrV? i = some (.case tag x) := by
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := adminsToV_eq_three h
  obtain ⟨b₁, rfl, hb₁⟩ := D.vconst a₁ c₁ h₁
  obtain ⟨b₂, rfl, hb₂⟩ := D.vconst a₂ c₂ h₂
  obtain ⟨i, rfl, hi⟩ := D.vinstr a₃ tag x ht h₃
  exact ⟨b₁, b₂, i, rfl, hb₁, hb₂, hi⟩

/-- `[VCONST c_1, VCONST c_2, VCONST c_3, OP x]` decodes. -/
theorem decode_c3 (D : VecDecode) {is : List Admin} {c₁ c₂ c₃ x : Value} {tag : MixopS}
    (ht : tag ∈ vecTags)
    (h : adminsToV is = [vconstV c₁, vconstV c₂, vconstV c₃, .case tag x]) :
    ∃ b₁ b₂ b₃ i, is = [vconst b₁, vconst b₂, vconst b₃, .plain i] ∧ c₁ = vecV b₁ ∧
      c₂ = vecV b₂ ∧ c₃ = vecV b₃ ∧ vecInstrV? i = some (.case tag x) := by
  obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := adminsToV_eq_four h
  obtain ⟨b₁, rfl, hb₁⟩ := D.vconst a₁ c₁ h₁
  obtain ⟨b₂, rfl, hb₂⟩ := D.vconst a₂ c₂ h₂
  obtain ⟨b₃, rfl, hb₃⟩ := D.vconst a₃ c₃ h₃
  obtain ⟨i, rfl, hi⟩ := D.vinstr a₄ tag x ht h₄
  exact ⟨b₁, b₂, b₃, i, rfl, hb₁, hb₂, hb₃, hi⟩

/-- A rule with a single `if` premise: some instance evaluates the conclusion and the test. -/
theorem fires_if1 {env : Env} {x : IL.Id} {i : Nat} {nm : IL.Id} {qs : List Param} {e p : Exp}
    {v : Value} (hr : HasRuleAt env x "%~>%" i (.ruleD nm qs "%~>%" e [.ifPr p]))
    (hf : Fires env x i v) :
    ∃ σ, EvalExp env (VarEnv.empty.bindVals σ) e v ∧
      EvalExp env (VarEnv.empty.bindVals σ) p (.bool true) := by
  have hb := fires_body hr hf
  obtain ⟨-, ρ₀, σ, hps, -, he, hp⟩ := hb
  have h0 : ρ₀ = VarEnv.empty := (Option.some.inj hps).symm
  exact ⟨σ, h0 ▸ he, h0 ▸ inv_if (hp _ List.mem_cons_self)⟩

/-- `c = $f(args)`, inverted. -/
theorem inv_eq_call {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} {u : Value} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws) (ha : Applies env f ws u)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.varE c) (.callE f args)) (.bool true)) : cv = u := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₁ = cv := Option.some.inj ((evalExp_varE_iff.1 h₁).symm.trans hc)
  have e₂ : v₂ = u := Equiv.ExecNumeric.Applies.unique (inv_call hd hx h₂) ha
  have e₃ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  rw [← e₁, e₃, e₂]

/-- `$f(args) = c`, inverted. -/
theorem inv_call_eq {env : Env} {ρ : VarEnv} {c : IL.Id} {cv : Value} {f : IL.Id}
    {args : List Arg} {ws : List ArgV} {u : Value} (hc : ρ.findVal? c = some cv)
    (hd : ρ.findDef? f = none) (hx : EvalArgs env ρ args ws) (ha : Applies env f ws u)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.callE f args) (.varE c)) (.bool true)) : cv = u := by
  obtain ⟨v₁, v₂, h₁, h₂, hcmp⟩ := evalExp_cmpE_iff.1 h
  have e₁ : v₂ = cv := Option.some.inj ((evalExp_varE_iff.1 h₂).symm.trans hc)
  have e₂ : v₁ = u := Equiv.ExecNumeric.Applies.unique (inv_call hd hx h₁) ha
  have e₃ : v₁ = v₂ := by simpa [cmpValues] using hcmp
  rw [← e₁, ← e₃, e₂]

/-- `OP (x, y, z)`, inverted. -/
theorem inv_op3 {env : Env} {ρ : VarEnv} {mo : MixopS} {x y z : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE mo (.tupE [.varE x, .varE y, .varE z])) v) :
    ∃ a b c, v = .case mo (.tuple [a, b, c]) ∧ ρ.findVal? x = some a ∧ ρ.findVal? y = some b ∧
      ρ.findVal? z = some c := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨a, vs₁, ha, hvs₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨b, vs₂, hb, hvs₂, rfl⟩ := evalExps_cons_iff.1 hvs₁
  obtain ⟨c, vs₃, hc, hvs₃, rfl⟩ := evalExps_cons_iff.1 hvs₂
  obtain rfl := evalExps_nil_iff.1 hvs₃
  exact ⟨a, b, c, rfl, evalExp_varE_iff.1 ha, evalExp_varE_iff.1 hb, evalExp_varE_iff.1 hc⟩

/-- `OP (V128, x)`, inverted. -/
theorem inv_vvop {env : Env} {ρ : VarEnv} {mo : MixopS} {x : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE mo (.tupE [.caseE "V128" (.tupE []), .varE x])) v) :
    ∃ a, v = .case mo (.tuple [vecTypeV, a]) ∧ ρ.findVal? x = some a := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨t, a, rfl, ht, ha⟩ := inv_tup2 hw
  obtain rfl := inv_nil ht
  exact ⟨a, rfl, evalExp_varE_iff.1 ha⟩

/-- A three-element list, inverted. -/
theorem inv_list3 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂, e₃]) v) :
    ∃ v₁ v₂ v₃, v = .list [v₁, v₂, v₃] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧
      EvalExp env ρ e₃ v₃ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w₁, ws₁, h₁, hws₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws₂, h₂, hws₂, rfl⟩ := evalExps_cons_iff.1 hws₁
  obtain ⟨w₃, ws₃, h₃, hws₃, rfl⟩ := evalExps_cons_iff.1 hws₂
  obtain rfl := evalExps_nil_iff.1 hws₃
  exact ⟨w₁, w₂, w₃, rfl, h₁, h₂, h₃⟩

/-- A four-element list, inverted. -/
theorem inv_list4 {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ e₄ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂, e₃, e₄]) v) :
    ∃ v₁ v₂ v₃ v₄, v = .list [v₁, v₂, v₃, v₄] ∧ EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧
      EvalExp env ρ e₃ v₃ ∧ EvalExp env ρ e₄ v₄ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_listE_iff.1 h
  obtain ⟨w₁, ws₁, h₁, hws₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, ws₂, h₂, hws₂, rfl⟩ := evalExps_cons_iff.1 hws₁
  obtain ⟨w₃, ws₃, h₃, hws₃, rfl⟩ := evalExps_cons_iff.1 hws₂
  obtain ⟨w₄, ws₄, h₄, hws₄, rfl⟩ := evalExps_cons_iff.1 hws₃
  obtain rfl := evalExps_nil_iff.1 hws₄
  exact ⟨w₁, w₂, w₃, w₄, rfl, h₁, h₂, h₃, h₄⟩

/-- A two-component tuple, separated. -/
theorem tuple2_inj {a b c d : Value} (h : Value.tuple [a, b] = .tuple [c, d]) :
    a = c ∧ b = d := by
  simpa using h

/-- A three-component tuple, separated. -/
theorem tuple3_inj {a b c d e f : Value} (h : Value.tuple [a, b, c] = .tuple [d, e, f]) :
    a = d ∧ b = e ∧ c = f := by
  simpa using h

/-- `vecInstrV?` at `VVBINOP`. -/
theorem vecInstrV?_vvbinop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VVBINOP" x)) :
    ∃ op, i = .vecBinOp op ∧ x = .tuple [vecTypeV, vvbinopV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VVTERNOP`. -/
theorem vecInstrV?_vvternop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VVTERNOP" x)) :
    ∃ op, i = .vecTernOp op ∧ x = .tuple [vecTypeV, vvternopV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VBINOP`. -/
theorem vecInstrV?_vbinop {i : Instr} {x : Value} (h : vecInstrV? i = some (.case "VBINOP" x)) :
    (∃ s op, i = .vecIntBinOp s op ∧ x = .tuple [ishV s, vIntBinOpV op]) ∨
      (∃ s op, i = .vecFloatBinOp s op ∧ x = .tuple [fshV s, vFloatBinOpV op]) := by
  cases i <;> simp [vecInstrV?] at h
  · exact .inl ⟨_, _, rfl, h.symm⟩
  · exact .inr ⟨_, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VTERNOP`. -/
theorem vecInstrV?_vternop {i : Instr} {x : Value} (h : vecInstrV? i = some (.case "VTERNOP" x)) :
    (∃ s op, i = .vecIntTernOp s op ∧ x = .tuple [ishV s, vIntTernOpV op]) ∨
      (∃ s op, i = .vecFloatTernOp s op ∧ x = .tuple [fshV s, vFloatTernOpV op]) := by
  cases i <;> simp [vecInstrV?] at h
  · exact .inl ⟨_, _, rfl, h.symm⟩
  · exact .inr ⟨_, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VRELOP`. -/
theorem vecInstrV?_vrelop {i : Instr} {x : Value} (h : vecInstrV? i = some (.case "VRELOP" x)) :
    (∃ s op, i = .vecIntRelOp s op ∧ x = .tuple [ishV s, vIntRelOpV op]) ∨
      (∃ s op, i = .vecFloatRelOp s op ∧ x = .tuple [fshV s, vFloatRelOpV op]) := by
  cases i <;> simp [vecInstrV?] at h
  · exact .inl ⟨_, _, rfl, h.symm⟩
  · exact .inr ⟨_, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VSWIZZLOP`. -/
theorem vecInstrV?_vswizzlop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VSWIZZLOP" x)) :
    ∃ op, i = .vecSwizzle op ∧ x = .tuple [bshapeV, vSwizzleOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VEXTUNOP`. -/
theorem vecInstrV?_vextunop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VEXTUNOP" x)) :
    ∃ s t op, i = .vecExtUnOp s t op ∧ x = .tuple [ishapeV t, ishapeV s, vExtUnOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VEXTBINOP`. -/
theorem vecInstrV?_vextbinop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VEXTBINOP" x)) :
    ∃ s t op, i = .vecExtBinOp s t op ∧ x = .tuple [ishapeV t, ishapeV s, vExtBinOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VEXTTERNOP`. -/
theorem vecInstrV?_vextternop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VEXTTERNOP" x)) :
    ∃ s t op, i = .vecExtTernOp s t op ∧ x = .tuple [ishapeV t, ishapeV s, vExtTernOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VCVTOP`. -/
theorem vecInstrV?_vcvtop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VCVTOP" x)) :
    ∃ s t op, i = .vecConvert s t op ∧ x = .tuple [shapeV t, shapeV s, vConvertOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- A rule instance `[VCONST c_1, op] ~> [rhs]`, inverted. -/
theorem inst_c1 {env : Env} {ρ : VarEnv} {eop erhs : Exp} {xs : List Value} {w : Value}
    (he : EvalExp env ρ (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []),
      .varE "c_1"]), eop], .listE [erhs]]) (.tuple [.list xs, w])) :
    ∃ c₁ y z, xs = [vconstV c₁, y] ∧ w = .list [z] ∧ ρ.findVal? "c_1" = some c₁ ∧
      EvalExp env ρ eop y ∧ EvalExp env ρ erhs z := by
  obtain ⟨l, r, hv, hl, hr⟩ := inv_tup2 he
  obtain ⟨x₁, y, rfl, h₁, hy⟩ := inv_list2 hl
  obtain ⟨c₁, rfl, f₁⟩ := inv_vconst h₁
  obtain ⟨z, rfl, hz⟩ := inv_list1 hr
  obtain ⟨hxs, hw⟩ := tuple2_inj hv
  exact ⟨c₁, y, z, (Value.list.inj hxs.symm).symm ▸ rfl, hw, f₁, hy, hz⟩

/-- A rule instance `[VCONST c_1, VCONST c_2, op] ~> [rhs]`, inverted. -/
theorem inst_c2 {env : Env} {ρ : VarEnv} {eop erhs : Exp} {xs : List Value} {w : Value}
    (he : EvalExp env ρ (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []),
      .varE "c_1"]), .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_2"]), eop],
      .listE [erhs]]) (.tuple [.list xs, w])) :
    ∃ c₁ c₂ y z, xs = [vconstV c₁, vconstV c₂, y] ∧ w = .list [z] ∧
      ρ.findVal? "c_1" = some c₁ ∧ ρ.findVal? "c_2" = some c₂ ∧
      EvalExp env ρ eop y ∧ EvalExp env ρ erhs z := by
  obtain ⟨l, r, hv, hl, hr⟩ := inv_tup2 he
  obtain ⟨x₁, x₂, y, rfl, h₁, h₂, hy⟩ := inv_list3 hl
  obtain ⟨c₁, rfl, f₁⟩ := inv_vconst h₁
  obtain ⟨c₂, rfl, f₂⟩ := inv_vconst h₂
  obtain ⟨z, rfl, hz⟩ := inv_list1 hr
  obtain ⟨hxs, hw⟩ := tuple2_inj hv
  exact ⟨c₁, c₂, y, z, (Value.list.inj hxs.symm).symm ▸ rfl, hw, f₁, f₂, hy, hz⟩

/-- A rule instance `[VCONST c_1, VCONST c_2, VCONST c_3, op] ~> [rhs]`, inverted. -/
theorem inst_c3 {env : Env} {ρ : VarEnv} {eop erhs : Exp} {xs : List Value} {w : Value}
    (he : EvalExp env ρ (.tupE [.listE [.caseE "VCONST" (.tupE [.caseE "V128" (.tupE []),
      .varE "c_1"]), .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_2"]),
      .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_3"]), eop],
      .listE [erhs]]) (.tuple [.list xs, w])) :
    ∃ c₁ c₂ c₃ y z, xs = [vconstV c₁, vconstV c₂, vconstV c₃, y] ∧ w = .list [z] ∧
      ρ.findVal? "c_1" = some c₁ ∧ ρ.findVal? "c_2" = some c₂ ∧ ρ.findVal? "c_3" = some c₃ ∧
      EvalExp env ρ eop y ∧ EvalExp env ρ erhs z := by
  obtain ⟨l, r, hv, hl, hr⟩ := inv_tup2 he
  obtain ⟨x₁, x₂, x₃, y, rfl, h₁, h₂, h₃, hy⟩ := inv_list4 hl
  obtain ⟨c₁, rfl, f₁⟩ := inv_vconst h₁
  obtain ⟨c₂, rfl, f₂⟩ := inv_vconst h₂
  obtain ⟨c₃, rfl, f₃⟩ := inv_vconst h₃
  obtain ⟨z, rfl, hz⟩ := inv_list1 hr
  obtain ⟨hxs, hw⟩ := tuple2_inj hv
  exact ⟨c₁, c₂, c₃, y, z, (Value.list.inj hxs.symm).symm ▸ rfl, hw, f₁, f₂, f₃, hy, hz⟩

/-- `vecInstrV?` at `VVTESTOP`. -/
theorem vecInstrV?_vvtestop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VVTESTOP" x)) :
    ∃ op, i = .vecTestOp op ∧ x = .tuple [vecTypeV, vvtestopV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VBITMASK`. -/
theorem vecInstrV?_vbitmask {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VBITMASK" x)) : ∃ s, i = .vecBitmask s ∧ x = ishapeV s := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VSHIFTOP`. -/
theorem vecInstrV?_vshiftop {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VSHIFTOP" x)) :
    ∃ s op, i = .vecShiftOp s op ∧ x = .tuple [ishapeV s, vShiftOpV op] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, rfl, h.symm⟩

/-- `vecInstrV?` at `VSHUFFLE`. -/
theorem vecInstrV?_vshuffle {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VSHUFFLE" x)) :
    ∃ ls, i = .vecShuffle ls ∧ x = .tuple [bshapeV, .list (ls.map laneIdxV)] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, rfl, h.symm⟩

/-- `vecInstrV?` at `VNARROW`. -/
theorem vecInstrV?_vnarrow {i : Instr} {x : Value}
    (h : vecInstrV? i = some (.case "VNARROW" x)) :
    ∃ s t sx, i = .vecNarrow s t sx ∧ x = .tuple [ishapeV t, ishapeV s, sxV sx] := by
  cases i <;> simp [vecInstrV?] at h
  exact ⟨_, _, _, rfl, h.symm⟩

/-- `CONST I32 x`, inverted. -/
theorem inv_constI32 {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x])) v) :
    ∃ c, v = Equiv.Execution.constV Equiv.Execution.i32V c ∧ ρ.findVal? x = some c := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨v₁, c, rfl, h₁, h₂⟩ := inv_tup2 hw
  obtain rfl := inv_nil h₁
  exact ⟨c, rfl, evalExp_varE_iff.1 h₂⟩

/-- `OP x` with a bare payload, inverted. -/
theorem inv_op1 {env : Env} {ρ : VarEnv} {mo : MixopS} {x : IL.Id} {v : Value}
    (h : EvalExp env ρ (.caseE mo (.varE x)) v) : ∃ a, v = .case mo a ∧ ρ.findVal? x = some a := by
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 h
  exact ⟨w, rfl, evalExp_varE_iff.1 hw⟩

/-- `[VCONST c_1, CONST I32 i, OP x]` decodes. -/
theorem decode_c1i (D : VecDecode) {is : List Admin} {c₁ n x : Value} {tag : MixopS}
    (ht : tag ∈ vecTags)
    (h : adminsToV is = [vconstV c₁, Equiv.Execution.constV Equiv.Execution.i32V n, .case tag x]) :
    ∃ b k i, is = [vconst b, constI32 k, .plain i] ∧ c₁ = vecV b ∧ n = i32NV k ∧
      vecInstrV? i = some (.case tag x) := by
  obtain ⟨a₁, a₂, a₃, rfl, h₁, h₂, h₃⟩ := adminsToV_eq_three h
  obtain ⟨b, rfl, hb⟩ := D.vconst a₁ c₁ h₁
  obtain ⟨k, rfl, hk⟩ := D.i32const a₂ n h₂
  obtain ⟨i, rfl, hi⟩ := D.vinstr a₃ tag x ht h₃
  exact ⟨b, k, i, rfl, hb, hk, hi⟩

end Silmaril.Wasm.SpecTec.Sim.Vec
