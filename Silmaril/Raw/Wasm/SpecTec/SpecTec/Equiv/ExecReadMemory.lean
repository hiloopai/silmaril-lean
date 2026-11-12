module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The load and memory rules of `Step_read`, characterised

Twenty-five rules of `Step_read` — the ten `load`/`vload` `-oob`/`-val`
pairs, `memory.size`, and the `memory.fill` / `memory.copy` / `memory.init`
families — each pinned down by an exact `iff`, or shown to fire at nothing.

`Equiv/ExecRead.lean` transcribes the rules and ties them to the pinned
stream; this file says what each one *does*.  The state stays abstract
throughout: `$mem`, `$data`, `$size`, `$vsize`, `$nbytes_`, `$vbytes_`,
`$ibytes_` and `$memarg0` are named through `ExecNumeric.Applies` and never
unfolded into our runtime structures.

All twenty-five are settled: nineteen by an exact `ruleFires_*_iff`, six by a
`not_ruleFires_*` saying the rule derives nothing at all.

Four findings came out of it; each is a theorem below.

* **`memory.size` fires at nothing.**  Its second premise reads
  `$mem(z, x).TYPE = at PAGE lim`, and `lim` occurs nowhere in the
  conclusion.  A `.ifPr` is a side condition, not a unification, so `lim` is
  evaluated unbound and has no value.
* **Five of the ten `-val` load rules fire at nothing**, for the same
  reason: `load-pack-val`, `vload-pack-val`, `vload-splat-val`,
  `vload-zero-val` and `vload_lane-val` each name a result variable
  (`c`, `j*`, `j`, `k`, `Jnn`, `M`) that only a premise would solve for.
  Only `load-num-val` and `vload-num-val` are executable as written.
* **The surviving `-oob`/`-val` pairs are exclusive and, with the corrected
  slice bound, exhaustive.**  `eval.ml:284` bounds `Value.slice?` with a
  *strict* `<`, which left an access ending exactly at the end of the memory
  with no step; this port uses `≤` (upstream item U2), so `-val` needs
  `a + k ≤ |bytes|` and `-oob` needs `|bytes| < a + k` (`boundary_slice`).
* **The `else` overlap is here too.**  `memory.fill-succ`, `memory.copy-gt`
  and `memory.init-succ` have `else` as their *only* premise, which
  `Sem/Eval.lean` discharges unconditionally, so each fires on every
  configuration of its shape — including the out-of-bounds and zero-length
  ones its siblings are meant to claim.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecReadMemory

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecRead

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## Vocabulary

Every rule below reads a configuration `(z; instr*)` and keeps the state `z`
abstract: `$mem`, `$data`, `$memarg0`, `$size`, `$vsize`, `$nbytes_`,
`$vbytes_` and `$ibytes_` are named through `ExecNumeric.Applies`, never
unfolded. -/

/-- `(z; instr*) ~> instr'*`, the value a `Step_read` rule derives. -/
def readV (z : Value) (is js : List Value) : Value :=
  .tuple [ExecStep.configV z is, .list js]

/-- `v` is `(% a …)`: a `%` injection of a tuple whose first component is the
numeral `a`.  Every address, offset and page count in these rules is read
through `!%.0`, which is exactly this; nothing forces the tuple to be a
singleton, and nothing constrains its later components. -/
def Imm (v : Value) (a : Nat) : Prop :=
  ∃ us, v = .case "%" (.tuple (.num (.natN a) :: us))

/-- `$f(z, x).BYTES` is `bs`.  Used at `f = "mem"` and `f = "data"`. -/
def CallBytes (env : Env) (f : IL.Id) (z x : Value) (bs : List Value) : Prop :=
  ∃ inst, ExecNumeric.Applies env f [.val z, .val x] inst ∧
    inst.field? "BYTES" = some (.list bs)

/-- The effective address `i!%.0 + ao.OFFSET!%.0` of a `memarg` access. -/
def EffAddr (i ao : Value) (a : Nat) : Prop :=
  ∃ b o off, Imm i b ∧ ao.field? "OFFSET" = some o ∧ Imm o off ∧ a = b + off

/-- `N/8`: coerce the bit width to `rat`, divide by `8`, coerce back to
`nat`.  The IL writes exactly that, and `Num.cvt .natT` of a non-integral
rational is `none`, so the division has to come out exact. -/
def BitsToBytes (m : Num) (k : Nat) : Prop :=
  ∃ m' q, Num.cvt .ratT m = some m' ∧ Num.bin .divOp m' (.ratN 8) = some q ∧
    Num.cvt .natT q = some (.natN k)

/-- The side condition every `-oob` load rule carries, with the bit width
abstracted away: the `k` bytes at the effective address run past the end of
`$mem(z, x).BYTES`. -/
def LoadOob (env : Env) (z x i ao : Value) (k : Nat) : Prop :=
  ∃ a bs, EffAddr i ao a ∧ CallBytes env "mem" z x bs ∧ bs.length < a + k

/-- The side condition a `-val` load rule carries: the `k` bytes at the
effective address are exactly `sl`.  `Value.slice?` bounds with the
corrected `≤` (upstream item U2), so this and `LoadOob` are complementary. -/
def LoadSlice (env : Env) (z x i ao : Value) (k : Nat) (sl : Value) : Prop :=
  ∃ a bs, EffAddr i ao a ∧ CallBytes env "mem" z x bs ∧
    Value.slice? (.list bs) a k = some sl

/-! ## Two shapes every rule shares -/

/-- `(z; instr*) ~> instr'*`, as a pattern: `z` is a fresh variable and the
two instruction sequences are explicit pattern lists. -/
theorem matchExp_readConcl_iff {env : Env} {ρ' : VarEnv} {es fs : List Exp}
    {v : Value} :
    MatchExp env VarEnv.empty
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), .listE fs]) v ρ' ↔
      ∃ z vs ws σ, v = readV z vs ws ∧
        MatchExps env (VarEnv.empty.bindVal "z" z) es vs σ ∧
        MatchExps env σ fs ws ρ' := by
  rw [matchExp_concl_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, hl, hr⟩
    obtain ⟨av, rfl, hav⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hav
    obtain ⟨zv, lv, τ, rfl, hz, hlv⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨vs, rfl, hvs⟩ := Validation.matchExp_list_iff.1 hlv
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_list_iff.1 hr
    exact ⟨zv, vs, ws, σ, rfl, hvs, hws⟩
  · rintro ⟨z, vs, ws, σ, rfl, hvs, hws⟩
    exact ⟨_, _, σ, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl, hvs⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl, hws⟩⟩

/-- `e!%.0` for an arbitrary `e`, the generalisation of
`Equiv/Execution.lean`'s `evalExp_imm_iff` that `ao.OFFSET!%.0` needs. -/
theorem evalExp_immE_iff {env : Env} {ρ : VarEnv} {e : Exp} {w : Value} :
    EvalExp env ρ (.projE (.uncaseE e "%") 0) w ↔
      ∃ us, EvalExp env ρ e (.case "%" (.tuple (w :: us))) := by
  rw [evalExp_projE_iff]
  constructor
  · rintro ⟨vs, hv, -, hidx⟩
    rw [evalExp_uncaseE_iff] at hv
    cases vs with
    | nil => simp at hidx
    | cons u us =>
        simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hidx
        subst hidx
        exact ⟨us, hv⟩
  · rintro ⟨us, h⟩
    exact ⟨w :: us, by rw [evalExp_uncaseE_iff]; exact h, by simp, by simp⟩

/-! ## The arithmetic these rules do

`eval.ml` evaluates `BinE`, `CmpE` and `CvtE` on *values*, so each of the
side conditions below is a chain of `Num.bin` / `Num.cmp` / `Num.cvt` facts.
The six lemmas here invert that chain once and for all. -/

/-- `boolShort` never short-circuits an arithmetic operator. -/
theorem boolShort_add (u : Value) : boolShort .addOp u = none := by cases u <;> rfl

/-- `boolShort` never short-circuits a subtraction. -/
theorem boolShort_sub (u : Value) : boolShort .subOp u = none := by cases u <;> rfl

/-- `boolShort` never short-circuits a multiplication. -/
theorem boolShort_mul (u : Value) : boolShort .mulOp u = none := by cases u <;> rfl

/-- `boolShort` never short-circuits a division. -/
theorem boolShort_div (u : Value) : boolShort .divOp u = none := by cases u <;> rfl

/-- A `binValues` that lands on a numeral had two numerals for operands. -/
theorem binValues_eq_num_iff {op : BinOp} {u₁ u₂ : Value} {m : Num} :
    binValues op u₁ u₂ = .ok (.num m) ↔
      ∃ m₁ m₂, u₁ = .num m₁ ∧ u₂ = .num m₂ ∧ Num.bin op m₁ m₂ = some m := by
  constructor
  · intro h
    cases u₁ <;> cases u₂ <;>
      simp_all [binValues, Res.ofOption_eq_ok, Option.map_eq_some_iff]
  · rintro ⟨m₁, m₂, rfl, rfl, h⟩
    simp [binValues, Res.ofOption, h]

/-- A `nat`-typed sum of two expressions, inverted. -/
theorem evalExp_addNat_iff {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {a : Nat} :
    EvalExp env ρ (.binE .addOp (.numT .natT) e₁ e₂) (.num (.natN a)) ↔
      ∃ b c, EvalExp env ρ e₁ (.num (.natN b)) ∧ EvalExp env ρ e₂ (.num (.natN c)) ∧
        a = b + c := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs⟩
    rw [boolShort_add] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hb⟩ := hs
    obtain ⟨m₁, m₂, rfl, rfl, hnum⟩ := binValues_eq_num_iff.1 hb
    cases m₁ with
    | natN b =>
        cases m₂ with
        | natN c => exact ⟨b, c, hv₁, hv₂, (Num.natN.inj (Option.some.inj hnum)).symm⟩
        | intN _ => simp [Num.bin] at hnum
        | ratN _ => simp [Num.bin] at hnum
        | realN _ => simp [Num.bin] at hnum
    | intN _ => cases m₂ <;> simp [Num.bin] at hnum
    | ratN _ => cases m₂ <;> simp [Num.bin] at hnum
    | realN _ => cases m₂ <;> simp [Num.bin] at hnum
  · rintro ⟨b, c, hb, hc, rfl⟩
    exact ⟨_, hb, Or.inr ⟨boolShort_add _, _, hc,
      binValues_eq_num_iff.2 ⟨_, _, rfl, rfl, rfl⟩⟩⟩

/-- `cmpValues` at `>` against a `nat`: both sides must be `nat`s. -/
theorem cmpValues_gt_natN_iff {u : Value} {n : Nat} :
    cmpValues .gtOp u (.num (.natN n)) = .ok (.bool true) ↔
      ∃ a, u = .num (.natN a) ∧ n < a := by
  constructor
  · intro h
    cases u with
    | num m =>
        cases m with
        | natN a => exact ⟨a, rfl, by simpa [cmpValues, Num.cmp, Res.ofOption] using h⟩
        | intN _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
        | ratN _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
        | realN _ => simp [cmpValues, Num.cmp, Res.ofOption] at h
    | bool _ => simp [cmpValues] at h
    | text _ => simp [cmpValues] at h
    | tuple _ => simp [cmpValues] at h
    | case _ _ => simp [cmpValues] at h
    | struct _ => simp [cmpValues] at h
    | list _ => simp [cmpValues] at h
    | opt _ => simp [cmpValues] at h
  · rintro ⟨a, rfl, h⟩
    simpa [cmpValues, Num.cmp, Res.ofOption] using h

/-- `cmpValues` at `≤` on two `nat`s. -/
theorem cmpValues_le_natN_iff {a b : Nat} :
    cmpValues .leOp (.num (.natN a)) (.num (.natN b)) = .ok (.bool true) ↔ a ≤ b := by
  simp [cmpValues, Num.cmp, Res.ofOption]

/-- `e/8`, the IL's bit-width-to-byte-width idiom, inverted. -/
theorem evalExp_bytesOf_iff {env : Env} {ρ : VarEnv} {e : Exp} {w : Value} :
    EvalExp env ρ
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) w ↔
      ∃ m k, EvalExp env ρ e (.num m) ∧ BitsToBytes m k ∧ w = .num (.natN k) := by
  rw [evalExp_cvtE_iff]
  constructor
  · rintro ⟨q, q', hq, hcvt, rfl⟩
    rw [evalExp_binE_iff] at hq
    obtain ⟨v₁, hv₁, hs⟩ := hq
    rw [boolShort_div] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hbv⟩ := hs
    obtain ⟨m₁, m₂, rfl, rfl, hb⟩ := binValues_eq_num_iff.1 hbv
    obtain ⟨m, m', hm, hcm, hv⟩ := evalExp_cvtE_iff.1 hv₁
    obtain ⟨e₈, e₈', h₈, hc₈, hv₈⟩ := evalExp_cvtE_iff.1 hv₂
    rw [evalExp_numE_iff] at h₈
    obtain rfl := Value.num.inj h₈
    have hc₈' : e₈' = .ratN 8 := by
      simpa [Num.cvt, eq_comm] using hc₈
    subst hc₈'
    obtain rfl := Value.num.inj hv
    obtain rfl := Value.num.inj hv₈
    cases q' with
    | natN k => exact ⟨m, k, hm, ⟨_, _, hcm, hb, hcvt⟩, rfl⟩
    | intN _ => cases q <;> simp [Num.cvt] at hcvt
    | ratN _ => cases q <;> simp [Num.cvt] at hcvt
    | realN _ => cases q <;> simp [Num.cvt] at hcvt
  · rintro ⟨m, k, hm, ⟨m', q, hcm, hb, hcvt⟩, rfl⟩
    refine ⟨q, .natN k, ?_, hcvt, rfl⟩
    rw [evalExp_binE_iff]
    exact ⟨.num m', evalExp_cvtE_iff.2 ⟨m, m', hm, hcm, rfl⟩,
      Or.inr ⟨boolShort_div _, .num (.ratN 8),
        evalExp_cvtE_iff.2 ⟨.natN 8, .ratN 8, evalExp_numE_iff.2 rfl, rfl, rfl⟩,
        binValues_eq_num_iff.2 ⟨_, _, rfl, rfl, hb⟩⟩⟩

/-- `$f(e₁, e₂).BYTES`, with the arguments' denotations fixed. -/
theorem evalExp_callBytes_iff {env : Env} {ρ : VarEnv} {f : IL.Id} {e₁ e₂ : Exp}
    {zv xv w : Value} (h₁ : EvalExp env ρ e₁ zv) (h₂ : EvalExp env ρ e₂ xv)
    (hd : ρ.findDef? f = none) :
    EvalExp env ρ (.dotE (.callE f [.expA e₁, .expA e₂]) "BYTES") w ↔
      ∃ inst, ExecNumeric.Applies env f [.val zv, .val xv] inst ∧
        inst.field? "BYTES" = some w := by
  rw [evalExp_dotE_iff]
  have hargs : EvalArgs env ρ [.expA e₁, .expA e₂] [.val zv, .val xv] :=
    evalArgs_cons h₁ (evalArgs_cons h₂ evalArgs_nil)
  constructor
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, (ExecNumeric.applies_iff_callDef hd hargs).2 (evalExp_callE_iff.1 hu), hf⟩
  · rintro ⟨inst, happ, hf⟩
    exact ⟨inst, evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef hd hargs).1 happ),
      hf⟩

/-- `i!%.0 + ao.OFFSET!%.0`, the effective address of a `memarg` access. -/
theorem evalExp_effAddr_iff {env : Env} {ρ : VarEnv} {iv aov : Value} {a : Nat}
    (hi : ρ.findVal? "i" = some iv) (hao : ρ.findVal? "ao" = some aov) :
    EvalExp env ρ
      (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
        (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0)) (.num (.natN a)) ↔
      EffAddr iv aov a := by
  rw [evalExp_addNat_iff]
  constructor
  · rintro ⟨b, c, hb, hc, rfl⟩
    rw [evalExp_imm_iff hi] at hb
    rw [evalExp_immE_iff] at hc
    obtain ⟨us, hus⟩ := hc
    obtain ⟨o, ho, hof⟩ := evalExp_dotE_iff.1 hus
    rw [evalExp_varE_iff, hao] at ho
    obtain rfl := Option.some.inj ho
    exact ⟨b, _, c, hb, hof, ⟨us, rfl⟩, rfl⟩
  · rintro ⟨b, o, off, hb, hof, ⟨us, rfl⟩, rfl⟩
    exact ⟨b, off, (evalExp_imm_iff hi).2 hb,
      evalExp_immE_iff.2 ⟨us, evalExp_dotE_iff.2 ⟨aov, evalExp_varE_iff.2 hao, hof⟩⟩, rfl⟩

/-- **The `-oob` side condition, once.**
`(i!%.0 + ao.OFFSET!%.0) + e/8 > |$mem(z, x).BYTES|` — `e` is the bit width,
the only thing that differs between the ten `-oob` load rules. -/
theorem evalExp_loadOob_iff {env : Env} {ρ : VarEnv} {e : Exp} {iv aov zv xv : Value}
    (hi : ρ.findVal? "i" = some iv) (hao : ρ.findVal? "ao" = some aov)
    (hz : ρ.findVal? "z" = some zv) (hx : ρ.findVal? "x" = some xv)
    (hd : ρ.findDef? "mem" = none) :
    EvalExp env ρ
      (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT)
          (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
            (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
          (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
            (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
        (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")))
      (.bool true) ↔
      ∃ m k, EvalExp env ρ e (.num m) ∧ BitsToBytes m k ∧ LoadOob env zv xv iv aov k := by
  have hzv : EvalExp env ρ (.varE "z") zv := evalExp_varE_iff.2 hz
  have hxv : EvalExp env ρ (.varE "x") xv := evalExp_varE_iff.2 hx
  rw [evalExp_cmpE_iff]
  constructor
  · rintro ⟨u₁, u₂, hu₁, hu₂, hcmp⟩
    obtain ⟨bs, hbs, rfl⟩ := evalExp_lenE_iff.1 hu₂
    obtain ⟨t, rfl, hlt⟩ := cmpValues_gt_natN_iff.1 hcmp
    obtain ⟨a, k, ha, hk, rfl⟩ := evalExp_addNat_iff.1 hu₁
    obtain ⟨m, k', hm, hbtb, hk'⟩ := evalExp_bytesOf_iff.1 hk
    obtain rfl := Num.natN.inj (Value.num.inj hk')
    rw [evalExp_effAddr_iff hi hao] at ha
    exact ⟨m, _, hm, hbtb, a, bs, ha,
      (evalExp_callBytes_iff hzv hxv hd).1 hbs, hlt⟩
  · rintro ⟨m, k, hm, hbtb, a, bs, ha, hcb, hlt⟩
    refine ⟨.num (.natN (a + k)), .num (.natN bs.length), ?_, ?_, ?_⟩
    · exact evalExp_addNat_iff.2 ⟨a, k, (evalExp_effAddr_iff hi hao).2 ha,
        evalExp_bytesOf_iff.2 ⟨m, k, hm, hbtb, rfl⟩, rfl⟩
    · exact evalExp_lenE_iff.2 ⟨bs, (evalExp_callBytes_iff hzv hxv hd).2 hcb, rfl⟩
    · exact cmpValues_gt_natN_iff.2 ⟨a + k, rfl, hlt⟩

/-- `Value.slice?` is defined on lists only, and bounds with the corrected `≤`
(`eval.ml:284` has `<`; upstream item U2). -/
theorem slice?_eq_some_iff {v : Value} {i k : Nat} {w : Value} :
    v.slice? i k = some w ↔
      ∃ bs, v = .list bs ∧ i + k ≤ bs.length ∧ w = .list ((bs.drop i).take k) := by
  cases v with
  | list bs =>
      simp only [Value.slice?]
      constructor
      · intro h
        split at h
        · exact ⟨bs, rfl, by assumption, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)
      · rintro ⟨bs', hbs, hlt, rfl⟩
        obtain rfl := Value.list.inj hbs
        simp [hlt]
  | bool _ => simp [Value.slice?]
  | num _ => simp [Value.slice?]
  | text _ => simp [Value.slice?]
  | tuple _ => simp [Value.slice?]
  | case _ _ => simp [Value.slice?]
  | struct _ => simp [Value.slice?]
  | opt _ => simp [Value.slice?]

/-- **The `-val` side condition, once.**
`$mem(z, x).BYTES[(i!%.0 + ao.OFFSET!%.0) : e/8]`, the slice the two
executable `-val` rules compare against. -/
theorem evalExp_loadSlice_iff {env : Env} {ρ : VarEnv} {e : Exp}
    {iv aov zv xv w : Value}
    (hi : ρ.findVal? "i" = some iv) (hao : ρ.findVal? "ao" = some aov)
    (hz : ρ.findVal? "z" = some zv) (hx : ρ.findVal? "x" = some xv)
    (hd : ρ.findDef? "mem" = none) :
    EvalExp env ρ
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT) (.cvtE e .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT)) w ↔
      ∃ m k, EvalExp env ρ e (.num m) ∧ BitsToBytes m k ∧
        LoadSlice env zv xv iv aov k w := by
  have hzv : EvalExp env ρ (.varE "z") zv := evalExp_varE_iff.2 hz
  have hxv : EvalExp env ρ (.varE "x") xv := evalExp_varE_iff.2 hx
  rw [evalExp_sliceE_iff]
  constructor
  · rintro ⟨u, a, k, hu, ha, hk, hsl⟩
    obtain ⟨bs, rfl, hlt, rfl⟩ := slice?_eq_some_iff.1 hsl
    obtain ⟨m, k', hm, hbtb, hk'⟩ := evalExp_bytesOf_iff.1 hk
    obtain rfl := Num.natN.inj (Value.num.inj hk')
    rw [evalExp_effAddr_iff hi hao] at ha
    exact ⟨m, _, hm, hbtb, a, bs, ha, (evalExp_callBytes_iff hzv hxv hd).1 hu,
      slice?_eq_some_iff.2 ⟨bs, rfl, hlt, rfl⟩⟩
  · rintro ⟨m, k, hm, hbtb, a, bs, ha, hcb, hsl⟩
    exact ⟨.list bs, a, k, (evalExp_callBytes_iff hzv hxv hd).2 hcb,
      (evalExp_effAddr_iff hi hao).2 ha,
      evalExp_bytesOf_iff.2 ⟨m, k, hm, hbtb, rfl⟩, hsl⟩

/-- `Imm` pins down its natural. -/
theorem Imm.unique {v : Value} {a a' : Nat} (h : Imm v a) (h' : Imm v a') : a = a' := by
  obtain ⟨us, rfl⟩ := h
  obtain ⟨us', h'⟩ := h'
  injection h' with _ h'
  injection h' with h'
  simpa using (List.cons.inj h').1

/-- So does `EffAddr`. -/
theorem effAddr_unique {i ao : Value} {a a' : Nat}
    (h : EffAddr i ao a) (h' : EffAddr i ao a') : a = a' := by
  obtain ⟨b, o, off, hb, ho, hoff, rfl⟩ := h
  obtain ⟨b', o', off', hb', ho', hoff', rfl⟩ := h'
  obtain rfl := Imm.unique hb hb'
  obtain rfl := Option.some.inj (ho.symm.trans ho')
  obtain rfl := Imm.unique hoff hoff'
  rfl

/-- **The gap, at the arithmetic.**  `-oob` asks for `|bytes| < a + k`;
`-val` asks, through `Value.slice?`, for `a + k ≤ |bytes|`.  Exclusive. -/
theorem not_oob_and_slice {a k : Nat} {bs : List Value} {sl : Value}
    (h₁ : bs.length < a + k) (h₂ : Value.slice? (.list bs) a k = some sl) : False := by
  obtain ⟨cs, hcs, hlt, -⟩ := slice?_eq_some_iff.1 h₂
  obtain rfl := Value.list.inj hcs
  omega

/-- **And exhaustive.**  Every access either runs past the end (`-oob`) or has
its slice (`-val`). -/
theorem oob_or_slice (a k : Nat) (bs : List Value) :
    bs.length < a + k ∨ Value.slice? (.list bs) a k = some (.list ((bs.drop a).take k)) := by
  by_cases h : bs.length < a + k
  · exact .inl h
  · exact .inr (slice?_eq_some_iff.2 ⟨bs, rfl, by omega, rfl⟩)

/-- **The boundary.**  An access whose last byte is the memory's last byte is
in bounds and has its slice, the last `k` elements.  (With `eval.ml:284`'s
strict `<` it had neither: `Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?_boundary`.) -/
theorem boundary_slice {a k : Nat} {bs : List Value} (h : a + k = bs.length) :
    ¬ bs.length < a + k ∧ Value.slice? (.list bs) a k = some (.list (bs.drop a)) := by
  refine ⟨by omega, slice?_eq_some_iff.2 ⟨bs, rfl, by omega, ?_⟩⟩
  rw [List.take_of_length_le (by simp; omega)]

/-- **The gap, at the rules.**  Given that `$mem(z, x).BYTES` is a function of
the state — which the runtime bridge will give — the two side conditions of a
load pair cannot both hold. -/
theorem not_loadOob_and_loadSlice {env : Env} {z x i ao : Value} {k : Nat}
    {sl : Value} (hbs : ∀ bs bs', CallBytes env "mem" z x bs →
      CallBytes env "mem" z x bs' → bs = bs')
    (h₁ : LoadOob env z x i ao k) (h₂ : LoadSlice env z x i ao k sl) : False := by
  obtain ⟨a₁, bs₁, ha₁, hc₁, hlt₁⟩ := h₁
  obtain ⟨a₂, bs₂, ha₂, hc₂, hsl⟩ := h₂
  obtain rfl := effAddr_unique ha₁ ha₂
  obtain rfl := hbs _ _ hc₁ hc₂
  exact not_oob_and_slice hlt₁ hsl

/-! ## `memory.size` fires at nothing

`memory.size` is the shortest rule of the family and the first finding.  Its
conclusion binds `z`, `x`, `at` and `n`; its second premise is

```
if $mem(z, x).TYPE = at PAGE lim
```

and `lim` is bound by nothing.  In `spectec`'s source that premise reads as a
pattern and *solves* for `lim`; `Sem/Eval.lean` transcribes `eval.ml`, where
an `IfPr` is a side condition — `premHolds` evaluates it and asserts `true` —
so `lim` is looked up, is absent, and the premise has no value.  The rule
therefore derives nothing, at any environment whatsoever. -/

/-- **`Step_read/memory.size` fires at nothing.**  Its second premise names
`lim`, which no pattern of the rule binds. -/
theorem not_ruleFires_memorySize {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v memorySizeRule := by
  unfold memorySizeRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨iv, rfl, hiv⟩ := matchExps_one_iff.1 hvs
  obtain ⟨x, rfl, hx⟩ := Validation.matchExp_case_iff.1 hiv
  rw [matchExp_freshVar_iff (by simp)] at hx
  subst hx
  obtain ⟨rv, rfl, hrv⟩ := matchExps_one_iff.1 hws
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_case_iff.1 hrv
  obtain ⟨rvs', rfl, hrvs'⟩ := Validation.matchExp_tup_iff.1 hrvs
  obtain ⟨atv, nv, τ, rfl, hat, hn⟩ := matchExps_two_iff.1 hrvs'
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hat
  subst hat
  obtain ⟨nvv, rfl, hnvv⟩ := Validation.matchExp_case_iff.1 hn
  obtain ⟨nvs, rfl, hnvs⟩ := Validation.matchExp_tup_iff.1 hnvv
  obtain ⟨nval, rfl, hnval⟩ := matchExps_one_iff.1 hnvs
  rw [matchExp_freshVar_iff (by simp)] at hnval
  subst hnval
  obtain ⟨κ, hpr₁, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨rfl, -⟩ := Validation.premHolds_if_iff.1 hpr₁
  obtain ⟨κ₂, hpr₂, -⟩ := Validation.premsHold_cons_iff.1 hrest
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr₂
  obtain ⟨v₁, v₂, -, hv₂, -⟩ := evalExp_cmpE_iff.1 hev
  obtain ⟨w, hw, rfl⟩ := evalExp_caseE_iff.1 hv₂
  obtain ⟨wvs, hwvs, rfl⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨p, ps, rfl, -, hq⟩ := Validation.evalExps_cons_iff.1 hwvs
  obtain ⟨q, qs, rfl, hlim, -⟩ := Validation.evalExps_cons_iff.1 hq
  rw [evalExp_varE_iff] at hlim
  simp at hlim

/-! ## `load-num`, the pair that sets the pattern

`load-num-oob` and `load-num-val` are the only `load`/`vload` pair both of
whose rules are executable, and between them they fix the shape of the other
nine: an address operand `(CONST (at <: numtype) i)`, an access instruction
carrying `x` and `ao`, a `-oob` rule whose premise is the arithmetic side
condition and a `-val` rule whose premise is an `Applies` against a slice. -/

/-- `(LOAD nt o x ao)`. -/
def loadV (nt o x ao : Value) : Value := .case "LOAD" (.tuple [nt, o, x, ao])

/-- `(CONST (y <: numtype) c)`, with `y` and `c` both fresh pattern
variables: the address operand every memory instruction starts with. -/
theorem matchExp_constPat_iff {env : Env} {ρ ρ' : VarEnv} {y w : IL.Id} {t₁ t₂ : Typ}
    {v : Value} (hy : ρ.findVal? y = none)
    (hw : ∀ u, (ρ.bindVal y u).findVal? w = none) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.subE (.varE y) t₁ t₂, .varE w])) v ρ' ↔
      ∃ a c, v = constV a c ∧ ρ' = (ρ.bindVal y a).bindVal w c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨a, c, σ, rfl, ha, hc⟩ := matchExps_two_iff.1 hus
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff hy] at ha
    subst ha
    rw [matchExp_freshVar_iff (hw a)] at hc
    exact ⟨a, c, rfl, hc⟩
  · rintro ⟨a, c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff hy).2 rfl),
        (matchExp_freshVar_iff (hw a)).2 rfl⟩⟩⟩

/-- The left-hand side both `load-num` rules read. -/
theorem matchExps_loadNumLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "LOAD" (.tupE [.varE "nt", .optE none, .varE "x", .varE "ao"])] vs ρ' ↔
      ∃ atv i nt x ao, vs = [constV atv i, loadV nt (.opt none) x ao] ∧
        ρ' = (((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "nt" nt).bindVal "x" x).bindVal "ao" ao := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨nt, o, x, ao, τ, υ, φ, rfl, hnt, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [matchExp_freshVar_iff (by simp)] at hnt
    subst hnt
    rw [Validation.matchExp_optNone_iff] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, nt, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, nt, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_optNone_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/load-num-oob`, characterised exactly.**  It traps exactly
when the `$size(nt)/8` bytes at the effective address run past the end of
`$mem(z, x).BYTES`.  Nothing constrains `at`, and nothing relates it to
`nt`: the address operand's type and the loaded type are independent here. -/
theorem ruleFires_loadNumOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v loadNumOobRule ↔
      ∃ z atv i nt x ao m k,
        v = readV z [constV atv i, loadV nt (.opt none) x ao] [Execution.trapV] ∧
        ExecNumeric.Applies env "size" [.val nt] (.num m) ∧ BitsToBytes m k ∧
        LoadOob env z x i ao k := by
  unfold loadNumOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, nt, x, ao, rfl, rfl⟩ := matchExps_loadNumLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hsz, hbtb, hoob⟩ := hev
    refine ⟨z, atv, i, nt, x, ao, m, k, rfl, ?_, hbtb, hoob⟩
    exact (ExecNumeric.applies_iff_callDef rfl
      (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).2
      (evalExp_callE_iff.1 hsz)
  · rintro ⟨z, atv, i, nt, x, ao, m, k, rfl, hsz, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_loadNumLhs_iff.2 ⟨atv, i, nt, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2 ⟨m, k, ?_, hbtb, hoob⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hsz)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil

/-- **`Step_read/load-num-val`, characterised exactly.**  It loads `c`
exactly when `$nbytes_(nt, c)` is the `$size(nt)/8`-byte slice of
`$mem(z, x).BYTES` at the effective address. -/
theorem ruleFires_loadNumVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v loadNumValRule ↔
      ∃ z atv i nt x ao c m k sl,
        v = readV z [constV atv i, loadV nt (.opt none) x ao] [constV nt c] ∧
        ExecNumeric.Applies env "size" [.val nt] (.num m) ∧ BitsToBytes m k ∧
        LoadSlice env z x i ao k sl ∧
        ExecNumeric.Applies env "nbytes_" [.val nt, .val c] sl := by
  unfold loadNumValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, nt, x, ao, rfl, rfl⟩ := matchExps_loadNumLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
    obtain ⟨ntv, c, τ, rfl, hnt, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_boundVar_iff (w := nt) (by simp)] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_loadSlice_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hu₂
    obtain ⟨m, k, hsz, hbtb, hsl⟩ := hu₂
    refine ⟨z, atv, i, ntv, x, ao, c, m, k, u₁, rfl, ?_, hbtb, hsl, ?_⟩
    · exact (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)).2
        (evalExp_callE_iff.1 hsz)
    · exact (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons (evalExp_varE_iff.2 (by simp))
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))).2
        (evalExp_callE_iff.1 hu₁)
  · rintro ⟨z, atv, i, nt, x, ao, c, m, k, sl, rfl, hsz, hbtb, hsl, hnb⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_loadNumLhs_iff.2 ⟨atv, i, nt, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_boundVar_iff (w := nt) (by simp)).2 ⟨rfl, rfl⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine evalExp_cmpE_iff.2 ⟨sl, sl, ?_, ?_, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    · refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hnb)
      exact evalArgs_cons (evalExp_varE_iff.2 (by simp))
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
    · refine (evalExp_loadSlice_iff (iv := i) (aov := ao) (zv := z) (xv := x)
        (by simp) (by simp) (by simp) (by simp) rfl).2 ⟨m, k, ?_, hbtb, hsl⟩
      refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hsz)
      exact evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil

/-! ## `load-pack`: the first rule that cannot fire

`load-pack-oob` is `load-num-oob` with the width read off the instruction
instead of out of `$size`.  `load-pack-val` is the first of five rules whose
conclusion or premises evaluate a variable that nothing binds: its
right-hand side is `(CONST (Inn <: numtype) $extend__(n, $size(Inn), sx, c))`
and `c` occurs *only* there, as a call argument.  `spectec` would read the
premise `$ibytes_(n, c) = …` as a pattern and solve for `c`; `eval.ml` — and
so `Sem/Eval.lean` — evaluates it, so `c` is looked up and is absent. -/

/-- `?((% n) sx)`, the packing annotation of a packed load. -/
def packV (n sx : Value) : Value :=
  .opt (some (.case "%_%" (.tuple [.case "%" (.tuple [n]), sx])))

/-- The left-hand side both `load-pack` rules read. -/
theorem matchExps_loadPackLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "LOAD" (.tupE [.subE (.varE "Inn") (.varT "Inn" []) (.varT "numtype" []),
          .optE (some (.caseE "%_%" (.tupE [.caseE "%" (.tupE [.varE "n"]),
            .varE "sx"]))), .varE "x", .varE "ao"])] vs ρ' ↔
      ∃ atv i inn n sx x ao, vs = [constV atv i, loadV inn (packV n sx) x ao] ∧
        ρ' = ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "Inn" inn).bindVal "n" n).bindVal "sx" sx).bindVal "x" x).bindVal "ao" ao) := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨inn, o, x, ao, τ, υ, φ, rfl, hinn, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hinn
    subst hinn
    obtain ⟨ov, rfl, hov⟩ := Validation.matchExp_optSome_iff.1 ho
    obtain ⟨ovs, rfl, hovs⟩ := Validation.matchExp_case_iff.1 hov
    obtain ⟨ovs', rfl, hovs'⟩ := Validation.matchExp_tup_iff.1 hovs
    obtain ⟨nn, sx, ψ, rfl, hnn, hsx⟩ := matchExps_two_iff.1 hovs'
    obtain ⟨nv, rfl, hnv⟩ := Validation.matchExp_case_iff.1 hnn
    obtain ⟨nvs, rfl, hnvs⟩ := Validation.matchExp_tup_iff.1 hnv
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hnvs
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hsx
    subst hsx
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, inn, n, sx, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, inn, n, sx, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
            Validation.matchExp_optSome_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_two_iff.2 ⟨_, _, _, rfl,
                    Validation.matchExp_case_iff.2 ⟨_, rfl,
                      Validation.matchExp_tup_iff.2 ⟨_, rfl,
                        matchExps_one_iff.2 ⟨_, rfl,
                          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/load-pack-oob`, characterised exactly.**  The width is the
instruction's own `n`, so the premise constrains `n` to be a numeral. -/
theorem ruleFires_loadPackOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v loadPackOobRule ↔
      ∃ z atv i inn m sx x ao k,
        v = readV z [constV atv i, loadV inn (packV (.num m) sx) x ao]
          [Execution.trapV] ∧
        BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold loadPackOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, inn, n, sx, x, ao, rfl, rfl⟩ := matchExps_loadPackLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hn, hbtb, hoob⟩ := hev
    rw [evalExp_varE_iff] at hn
    simp at hn
    subst hn
    exact ⟨z, atv, i, inn, m, sx, x, ao, k, rfl, hbtb, hoob⟩
  · rintro ⟨z, atv, i, inn, m, sx, x, ao, k, rfl, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_loadPackLhs_iff.2 ⟨atv, i, inn, .num m, sx, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2
      ⟨m, k, evalExp_varE_iff.2 (by simp), hbtb, hoob⟩

/-- **`Step_read/load-pack-val` fires at nothing.**  Its conclusion evaluates
`$extend__(n, $size(Inn), sx, c)`, and `c` is bound by nothing. -/
theorem not_ruleFires_loadPackVal {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v loadPackValRule := by
  unfold loadPackValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨atv, i, inn, n, sx, x, ao, rfl, rfl⟩ := matchExps_loadPackLhs_iff.1 hvs
  obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
  obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
  obtain ⟨iv, cv, τ, rfl, hinn, hc⟩ := matchExps_two_iff.1 hrvs
  rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := inn) (by simp)] at hinn
  obtain ⟨rfl, rfl⟩ := hinn
  obtain ⟨hcall, -⟩ := ExecDefault.matchExp_callE_iff.1 hc
  obtain ⟨wsv, ps, t, cs, hargs, -, -⟩ := ExecNumeric.callDef_iff.1 hcall
  obtain ⟨_, _, rfl, -, h₂⟩ := evalArgs_expA_cons_iff.1 hargs
  obtain ⟨_, _, rfl, -, h₃⟩ := evalArgs_expA_cons_iff.1 h₂
  obtain ⟨_, _, rfl, -, h₄⟩ := evalArgs_expA_cons_iff.1 h₃
  obtain ⟨_, _, rfl, hcv, -⟩ := evalArgs_expA_cons_iff.1 h₄
  rw [evalExp_varE_iff] at hcv
  simp at hcv

/-! ## The four `vload` families

`vload-num`, `vload-pack`, `vload-splat` and `vload-zero` share a left-hand
side `(CONST (at<:) i) (VLOAD V128 o x ao)` and differ only in the annotation
`o` and in the bit width their `-oob` premise divides by `8`. -/

/-- `(VLOAD V128 o x ao)`. -/
def vloadV (o x ao : Value) : Value :=
  .case "VLOAD" (.tuple [ExecVector.v128V, o, x, ao])

/-- `(VCONST V128 c)`. -/
def vconstV (c : Value) : Value := .case "VCONST" (.tuple [ExecVector.v128V, c])

/-- The left-hand side both `vload-num` rules read. -/
theorem matchExps_vloadNumLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []), .optE none, .varE "x",
          .varE "ao"])] vs ρ' ↔
      ∃ atv i x ao, vs = [constV atv i, vloadV (.opt none) x ao] ∧
        ρ' = ((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "x" x).bindVal "ao" ao := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, o, x, ao, τ, υ, φ, rfl, htv, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [Validation.matchExp_optNone_iff] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_optNone_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/vload-num-oob`, characterised exactly.** -/
theorem ruleFires_vloadNumOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadNumOobRule ↔
      ∃ z atv i x ao m k,
        v = readV z [constV atv i, vloadV (.opt none) x ao] [Execution.trapV] ∧
        ExecNumeric.Applies env "vsize" [.val ExecVector.v128V] (.num m) ∧
        BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold vloadNumOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, x, ao, rfl, rfl⟩ := matchExps_vloadNumLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hsz, hbtb, hoob⟩ := hev
    exact ⟨z, atv, i, x, ao, m, k, rfl,
      (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons ExecVector.evalExp_v128 evalArgs_nil)).2
        (evalExp_callE_iff.1 hsz), hbtb, hoob⟩
  · rintro ⟨z, atv, i, x, ao, m, k, rfl, hsz, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadNumLhs_iff.2 ⟨atv, i, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2 ⟨m, k, ?_, hbtb, hoob⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hsz)
    exact evalArgs_cons ExecVector.evalExp_v128 evalArgs_nil

/-- **`Step_read/vload-num-val`, characterised exactly.**  The second of the
two executable `-val` rules. -/
theorem ruleFires_vloadNumVal_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadNumValRule ↔
      ∃ z atv i x ao c m k sl,
        v = readV z [constV atv i, vloadV (.opt none) x ao] [vconstV c] ∧
        ExecNumeric.Applies env "vsize" [.val ExecVector.v128V] (.num m) ∧
        BitsToBytes m k ∧ LoadSlice env z x i ao k sl ∧
        ExecNumeric.Applies env "vbytes_" [.val ExecVector.v128V, .val c] sl := by
  unfold vloadNumValRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, x, ao, rfl, rfl⟩ := matchExps_vloadNumLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
    obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
    obtain ⟨tv, c, τ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc
    subst hc
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    rw [evalExp_loadSlice_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hu₂
    obtain ⟨m, k, hsz, hbtb, hsl⟩ := hu₂
    refine ⟨z, atv, i, x, ao, c, m, k, u₁, rfl, ?_, hbtb, hsl, ?_⟩
    · exact (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons ExecVector.evalExp_v128 evalArgs_nil)).2
        (evalExp_callE_iff.1 hsz)
    · exact (ExecNumeric.applies_iff_callDef rfl
        (evalArgs_cons ExecVector.evalExp_v128
          (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil))).2
        (evalExp_callE_iff.1 hu₁)
  · rintro ⟨z, atv, i, x, ao, c, m, k, sl, rfl, hsz, hbtb, hsl, hvb⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadNumLhs_iff.2 ⟨atv, i, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine evalExp_cmpE_iff.2 ⟨sl, sl, ?_, ?_, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩
    · refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hvb)
      exact evalArgs_cons ExecVector.evalExp_v128
        (evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil)
    · refine (evalExp_loadSlice_iff (iv := i) (aov := ao) (zv := z) (xv := x)
        (by simp) (by simp) (by simp) (by simp) rfl).2 ⟨m, k, ?_, hbtb, hsl⟩
      refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := _) rfl ?_).1 hsz)
      exact evalArgs_cons ExecVector.evalExp_v128 evalArgs_nil

/-- A five-element pattern list; `Equiv/Execution.lean` stops at four. -/
theorem matchExps_five_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ e₅ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅] vs ρ' ↔
      ∃ a b c d e σ τ υ φ, vs = [a, b, c, d, e] ∧ MatchExp env ρ e₁ a σ ∧
        MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧ MatchExp env υ e₄ d φ ∧
        MatchExp env φ e₅ e ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, τ, υ, φ, rfl, hb, hc, hd, he⟩ := matchExps_four_iff.1 h₂
    exact ⟨w, b, c, d, e, σ, τ, υ, φ, rfl, h₁, hb, hc, hd, he⟩
  · rintro ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨a, [b, c, d, e], σ, rfl, h₁,
      matchExps_four_iff.2 ⟨b, c, d, e, τ, υ, φ, rfl, h₂, h₃, h₄, h₅⟩⟩

/-- A `nat`-typed product, inverted. -/
theorem evalExp_mulNum_iff {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {m : Num} :
    EvalExp env ρ (.binE .mulOp (.numT .natT) e₁ e₂) (.num m) ↔
      ∃ m₁ m₂, EvalExp env ρ e₁ (.num m₁) ∧ EvalExp env ρ e₂ (.num m₂) ∧
        Num.bin .mulOp m₁ m₂ = some m := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs⟩
    rw [boolShort_mul] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hbv⟩ := hs
    obtain ⟨m₁, m₂, rfl, rfl, hb⟩ := binValues_eq_num_iff.1 hbv
    exact ⟨m₁, m₂, hv₁, hv₂, hb⟩
  · rintro ⟨m₁, m₂, h₁, h₂, hb⟩
    exact ⟨_, h₁, Or.inr ⟨boolShort_mul _, _, h₂,
      binValues_eq_num_iff.2 ⟨_, _, rfl, rfl, hb⟩⟩⟩

/-- `?(SHAPE (% K) X M _ sx)`, a packed vector load's annotation. -/
def shapeV (k mm sx : Value) : Value :=
  .opt (some (.case "SHAPE%X%_%" (.tuple [.case "%" (.tuple [k]), mm, sx])))

/-- The left-hand side both `vload-pack` rules read. -/
theorem matchExps_vloadPackLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []),
          .optE (some (.caseE "SHAPE%X%_%" (.tupE [.caseE "%" (.tupE [.varE "K"]),
            .varE "M", .varE "sx"]))), .varE "x", .varE "ao"])] vs ρ' ↔
      ∃ atv i kk mm sx x ao, vs = [constV atv i, vloadV (shapeV kk mm sx) x ao] ∧
        ρ' = ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "K" kk).bindVal "M" mm).bindVal "sx" sx).bindVal "x" x).bindVal "ao" ao) := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, o, x, ao, τ, υ, φ, rfl, htv, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨ov, rfl, hov⟩ := Validation.matchExp_optSome_iff.1 ho
    obtain ⟨ovs, rfl, hovs⟩ := Validation.matchExp_case_iff.1 hov
    obtain ⟨ovs', rfl, hovs'⟩ := Validation.matchExp_tup_iff.1 hovs
    obtain ⟨kv, mm, sx, ψ, ω, rfl, hkv, hmm, hsx⟩ := matchExps_three_iff.1 hovs'
    obtain ⟨kvs, rfl, hkvs⟩ := Validation.matchExp_case_iff.1 hkv
    obtain ⟨kvs', rfl, hkvs'⟩ := Validation.matchExp_tup_iff.1 hkvs
    obtain ⟨kk, rfl, hkk⟩ := matchExps_one_iff.1 hkvs'
    rw [matchExp_freshVar_iff (by simp)] at hkk
    subst hkk
    rw [matchExp_freshVar_iff (by simp)] at hmm
    subst hmm
    rw [matchExp_freshVar_iff (by simp)] at hsx
    subst hsx
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, kk, mm, sx, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, kk, mm, sx, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_optSome_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
                    Validation.matchExp_case_iff.2 ⟨_, rfl,
                      Validation.matchExp_tup_iff.2 ⟨_, rfl,
                        matchExps_one_iff.2 ⟨_, rfl,
                          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
                    (matchExp_freshVar_iff (by simp)).2 rfl,
                    (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/vload-pack-oob`, characterised exactly.**  The width is
`K * M!%.0`, so both the lane width and the lane count must be numerals. -/
theorem ruleFires_vloadPackOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadPackOobRule ↔
      ∃ z atv i mK mM us sx x ao m k,
        v = readV z [constV atv i,
            vloadV (shapeV (.num mK) (.case "%" (.tuple (.num mM :: us))) sx) x ao]
          [Execution.trapV] ∧
        Num.bin .mulOp mK mM = some m ∧ BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold vloadPackOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, kk, mm, sx, x, ao, rfl, rfl⟩ := matchExps_vloadPackLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hw, hbtb, hoob⟩ := hev
    obtain ⟨mK, mM, hK, hM, hb⟩ := evalExp_mulNum_iff.1 hw
    rw [evalExp_varE_iff] at hK
    simp at hK
    subst hK
    rw [evalExp_imm_iff (c := mm) (by simp)] at hM
    obtain ⟨us, rfl⟩ := hM
    exact ⟨z, atv, i, mK, mM, us, sx, x, ao, m, k, rfl, hb, hbtb, hoob⟩
  · rintro ⟨z, atv, i, mK, mM, us, sx, x, ao, m, k, rfl, hb, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadPackLhs_iff.2 ⟨atv, i, .num mK, _, sx, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2
      ⟨m, k, evalExp_mulNum_iff.2 ⟨mK, mM, evalExp_varE_iff.2 (by simp),
        (evalExp_imm_iff (c := .case "%" (.tuple (.num mM :: us))) (by simp)).2 ⟨us, rfl⟩,
        hb⟩, hbtb, hoob⟩

/-- `?(SPLAT (% N))`. -/
def splatV (n : Value) : Value := .opt (some (.case "SPLAT" (.case "%" (.tuple [n]))))

/-- `?(ZERO (% N))`. -/
def zeroAnnV (n : Value) : Value :=
  .opt (some (.case "ZERO" (.tuple [.case "%" (.tuple [n])])))

/-- The left-hand side both `vload-splat` rules read. -/
theorem matchExps_vloadSplatLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []),
          .optE (some (.caseE "SPLAT" (.caseE "%" (.tupE [.varE "N"])))),
          .varE "x", .varE "ao"])] vs ρ' ↔
      ∃ atv i n x ao, vs = [constV atv i, vloadV (splatV n) x ao] ∧
        ρ' = ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "N" n).bindVal "x" x).bindVal "ao" ao) := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, o, x, ao, τ, υ, φ, rfl, htv, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨ov, rfl, hov⟩ := Validation.matchExp_optSome_iff.1 ho
    obtain ⟨ovs, rfl, hovs⟩ := Validation.matchExp_case_iff.1 hov
    obtain ⟨ovs', rfl, hovs'⟩ := Validation.matchExp_case_iff.1 hovs
    obtain ⟨ovs'', rfl, hovs''⟩ := Validation.matchExp_tup_iff.1 hovs'
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hovs''
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, n, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, n, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_optSome_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/vload-splat-oob`, characterised exactly.** -/
theorem ruleFires_vloadSplatOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadSplatOobRule ↔
      ∃ z atv i x ao m k,
        v = readV z [constV atv i, vloadV (splatV (.num m)) x ao] [Execution.trapV] ∧
        BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold vloadSplatOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, n, x, ao, rfl, rfl⟩ := matchExps_vloadSplatLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hn, hbtb, hoob⟩ := hev
    rw [evalExp_varE_iff] at hn
    simp at hn
    subst hn
    exact ⟨z, atv, i, x, ao, m, k, rfl, hbtb, hoob⟩
  · rintro ⟨z, atv, i, x, ao, m, k, rfl, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadSplatLhs_iff.2 ⟨atv, i, .num m, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2
      ⟨m, k, evalExp_varE_iff.2 (by simp), hbtb, hoob⟩

/-- **`Step_read/vload-splat-val` fires at nothing.**  Its first premise reads
`$ibytes_(N, j)`, and `j` is bound by nothing — as are `Jnn` and `M`. -/
theorem not_ruleFires_vloadSplatVal {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vloadSplatValRule := by
  unfold vloadSplatValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨atv, i, n, x, ao, rfl, rfl⟩ := matchExps_vloadSplatLhs_iff.1 hvs
  obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
  obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
  obtain ⟨tv, c, τ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
  rw [matchExp_caseNil_iff] at htv
  obtain ⟨rfl, rfl⟩ := htv
  rw [matchExp_freshVar_iff (by simp)] at hc
  subst hc
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨u₁, u₂, hu₁, -, -⟩ := evalExp_cmpE_iff.1 hev
  obtain ⟨wsv, ps, t, cs, hargs, -, -⟩ :=
    ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hu₁)
  obtain ⟨_, _, rfl, -, h₂⟩ := evalArgs_expA_cons_iff.1 hargs
  obtain ⟨_, _, rfl, hjv, -⟩ := evalArgs_expA_cons_iff.1 h₂
  rw [evalExp_varE_iff] at hjv
  simp at hjv

/-- The left-hand side both `vload-zero` rules read. -/
theorem matchExps_vloadZeroLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "VLOAD" (.tupE [.caseE "V128" (.tupE []),
          .optE (some (.caseE "ZERO" (.tupE [.caseE "%" (.tupE [.varE "N"])]))),
          .varE "x", .varE "ao"])] vs ρ' ↔
      ∃ atv i n x ao, vs = [constV atv i, vloadV (zeroAnnV n) x ao] ∧
        ρ' = ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "N" n).bindVal "x" x).bindVal "ao" ao) := by
  rw [matchExps_two_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, ha, hb⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, o, x, ao, τ, υ, φ, rfl, htv, ho, hx, hao⟩ := matchExps_four_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨ov, rfl, hov⟩ := Validation.matchExp_optSome_iff.1 ho
    obtain ⟨ovs, rfl, hovs⟩ := Validation.matchExp_case_iff.1 hov
    obtain ⟨ovs', rfl, hovs'⟩ := Validation.matchExp_tup_iff.1 hovs
    obtain ⟨pv, rfl, hpv⟩ := matchExps_one_iff.1 hovs'
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_case_iff.1 hpv
    obtain ⟨pvs', rfl, hpvs'⟩ := Validation.matchExp_tup_iff.1 hpvs
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpvs'
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    exact ⟨atv, i, n, x, ao, rfl, hao⟩
  · rintro ⟨atv, i, n, x, ao, rfl, rfl⟩
    exact ⟨_, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_optSome_iff.2 ⟨_, rfl,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    Validation.matchExp_case_iff.2 ⟨_, rfl,
                      Validation.matchExp_tup_iff.2 ⟨_, rfl,
                        matchExps_one_iff.2 ⟨_, rfl,
                          (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/vload-zero-oob`, characterised exactly.** -/
theorem ruleFires_vloadZeroOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadZeroOobRule ↔
      ∃ z atv i x ao m k,
        v = readV z [constV atv i, vloadV (zeroAnnV (.num m)) x ao] [Execution.trapV] ∧
        BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold vloadZeroOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, n, x, ao, rfl, rfl⟩ := matchExps_vloadZeroLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hn, hbtb, hoob⟩ := hev
    rw [evalExp_varE_iff] at hn
    simp at hn
    subst hn
    exact ⟨z, atv, i, x, ao, m, k, rfl, hbtb, hoob⟩
  · rintro ⟨z, atv, i, x, ao, m, k, rfl, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadZeroLhs_iff.2 ⟨atv, i, .num m, x, ao, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2
      ⟨m, k, evalExp_varE_iff.2 (by simp), hbtb, hoob⟩

/-- **`Step_read/vload-zero-val` fires at nothing**, for the same reason:
`$ibytes_(N, j)` with `j` unbound. -/
theorem not_ruleFires_vloadZeroVal {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vloadZeroValRule := by
  unfold vloadZeroValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨atv, i, n, x, ao, rfl, rfl⟩ := matchExps_vloadZeroLhs_iff.1 hvs
  obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
  obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
  obtain ⟨tv, c, τ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
  rw [matchExp_caseNil_iff] at htv
  obtain ⟨rfl, rfl⟩ := htv
  rw [matchExp_freshVar_iff (by simp)] at hc
  subst hc
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨u₁, u₂, hu₁, -, -⟩ := evalExp_cmpE_iff.1 hev
  obtain ⟨wsv, ps, t, cs, hargs, -, -⟩ :=
    ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hu₁)
  obtain ⟨_, _, rfl, -, h₂⟩ := evalArgs_expA_cons_iff.1 hargs
  obtain ⟨_, _, rfl, hjv, -⟩ := evalArgs_expA_cons_iff.1 h₂
  rw [evalExp_varE_iff] at hjv
  simp at hjv

/-- `(VLOAD_LANE V128 (% N) x ao j)`. -/
def vloadLaneInstrV (n x ao j : Value) : Value :=
  .case "VLOAD_LANE" (.tuple [ExecVector.v128V, .case "%" (.tuple [n]), x, ao, j])

/-- The left-hand side both `vload_lane` rules read: three instructions, not
two — the lane is written into an existing vector. -/
theorem matchExps_vloadLaneLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c_1"]),
       .caseE "VLOAD_LANE" (.tupE [.caseE "V128" (.tupE []),
          .caseE "%" (.tupE [.varE "N"]), .varE "x", .varE "ao", .varE "j"])] vs ρ' ↔
      ∃ atv i c₁ n x ao j,
        vs = [constV atv i, vconstV c₁, vloadLaneInstrV n x ao j] ∧
        ρ' = ((((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "c_1" c₁).bindVal "N" n).bindVal "x" x).bindVal "ao" ao).bindVal "j" j) := by
  rw [matchExps_three_iff]
  constructor
  · rintro ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, c₁, ψ, rfl, htv, hc₁⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hc₁
    subst hc₁
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨tv', nv, x, ao, j, ω, ζ, ξ, η, rfl, htv', hnv, hx, hao, hj⟩ :=
      matchExps_five_iff.1 hcvs
    rw [matchExp_caseNil_iff] at htv'
    obtain ⟨rfl, rfl⟩ := htv'
    obtain ⟨nvs, rfl, hnvs⟩ := Validation.matchExp_case_iff.1 hnv
    obtain ⟨nvs', rfl, hnvs'⟩ := Validation.matchExp_tup_iff.1 hnvs
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hnvs'
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hao
    subst hao
    rw [matchExp_freshVar_iff (by simp)] at hj
    exact ⟨atv, i, c₁, n, x, ao, j, rfl, hj⟩
  · rintro ⟨atv, i, c₁, n, x, ao, j, rfl, rfl⟩
    exact ⟨_, _, _, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
            matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_one_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/vload_lane-oob`, characterised exactly.** -/
theorem ruleFires_vloadLaneOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v vloadLaneOobRule ↔
      ∃ z atv i c₁ x ao j m k,
        v = readV z [constV atv i, vconstV c₁, vloadLaneInstrV (.num m) x ao j]
          [Execution.trapV] ∧
        BitsToBytes m k ∧ LoadOob env z x i ao k := by
  unfold vloadLaneOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, c₁, n, x, ao, j, rfl, rfl⟩ := matchExps_vloadLaneLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl] at hev
    obtain ⟨m, k, hn, hbtb, hoob⟩ := hev
    rw [evalExp_varE_iff] at hn
    simp at hn
    subst hn
    exact ⟨z, atv, i, c₁, x, ao, j, m, k, rfl, hbtb, hoob⟩
  · rintro ⟨z, atv, i, c₁, x, ao, j, m, k, rfl, hbtb, hoob⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_vloadLaneLhs_iff.2 ⟨atv, i, c₁, .num m, x, ao, j, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_loadOob_iff (iv := i) (aov := ao) (zv := z) (xv := x)
      (by simp) (by simp) (by simp) (by simp) rfl).2
      ⟨m, k, evalExp_varE_iff.2 (by simp), hbtb, hoob⟩

/-- **`Step_read/vload_lane-val` fires at nothing.**  Its first premise reads
`$ibytes_(N, k)` with `k` unbound. -/
theorem not_ruleFires_vloadLaneVal {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vloadLaneValRule := by
  unfold vloadLaneValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨atv, i, c₁, n, x, ao, j, rfl, rfl⟩ := matchExps_vloadLaneLhs_iff.1 hvs
  obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
  obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
  obtain ⟨tv, c, τ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
  rw [matchExp_caseNil_iff] at htv
  obtain ⟨rfl, rfl⟩ := htv
  rw [matchExp_freshVar_iff (by simp)] at hc
  subst hc
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
  obtain ⟨u₁, u₂, hu₁, -, -⟩ := evalExp_cmpE_iff.1 hev
  obtain ⟨wsv, ps, t, cs, hargs, -, -⟩ :=
    ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hu₁)
  obtain ⟨_, _, rfl, -, h₂⟩ := evalArgs_expA_cons_iff.1 hargs
  obtain ⟨_, _, rfl, hkv, -⟩ := evalArgs_expA_cons_iff.1 h₂
  rw [evalExp_varE_iff] at hkv
  simp at hkv

/-! ## More of the `matchExp` and `evalExp` library

The `memory.*` rules need three things the library did not have: `BinE` and
`CvtE` *as patterns* in both directions, and the left-biased `\/`. -/

/-- `matchExp` at a `BinE` is the default match — `Equiv/Execution.lean`'s
`matchExp_binE_of_eval`, in both directions. -/
theorem matchExp_binE_iff {env : Env} {ρ ρ' : VarEnv} {op : BinOp} {t : OpTyp}
    {e₁ e₂ : Exp} {v : Value} :
    MatchExp env ρ (.binE op t e₁ e₂) v ρ' ↔
      EvalExp env ρ (.binE op t e₁ e₂) v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.binE op t e₁ e₂) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.binE op t e₁ e₂) v = .ok ρ' from ?_,
    ExecDefault.matchDefault_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `matchExp` at a `CvtE` converts the value *back* along the **source**
type and matches underneath (`eval.ml`'s `CvtE` clause). -/
theorem matchExp_cvtE_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : NumTyp}
    {v : Value} :
    MatchExp env ρ (.cvtE e t₁ t₂) v ρ' ↔
      ∃ m m', v = .num m ∧ Num.cvt t₁ m = some m' ∧ MatchExp env ρ e (.num m') ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ p =>
        cases v with
        | num mm =>
            rw [matchExp] at hn
            simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
            obtain ⟨m', hc, hm⟩ := hn
            exact ⟨mm, m', rfl, hc, ⟨p, hm⟩⟩
        | bool _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
            rw [matchExp] at hn
            · obtain ⟨hev, -⟩ := ExecDefault.matchDefault_iff.1 ⟨p, hn⟩
              simp [evalExp_cvtE_iff] at hev
            · simp
  · rintro ⟨m, m', rfl, hc, hm⟩
    exact Execution.matchExp_cvtE_num hc hm

/-- The left-biased `\/` of `eval.ml:240-255`: the second disjunct is
evaluated only when the first is `false`. -/
theorem evalExp_orE_true_iff {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} :
    EvalExp env ρ (.binE .orOp .boolT e₁ e₂) (.bool true) ↔
      EvalExp env ρ e₁ (.bool true) ∨
        (EvalExp env ρ e₁ (.bool false) ∧ EvalExp env ρ e₂ (.bool true)) := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs | ⟨hs, v₂, hv₂, hb⟩⟩
    · refine Or.inl ?_
      cases v₁ with
      | bool b =>
          cases b with
          | true => exact hv₁
          | false => simp [boolShort] at hs
      | num _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
          simp [boolShort] at hs
    · refine Or.inr ?_
      cases v₁ with
      | bool b =>
          cases b with
          | true => simp [boolShort] at hs
          | false =>
              cases v₂ with
              | bool b₂ =>
                  cases b₂ with
                  | true => exact ⟨hv₁, hv₂⟩
                  | false => simp [binValues, boolBin, Res.ofOption] at hb
              | num _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
                  simp [binValues] at hb
      | num _ =>
          cases v₂ with
          | num _ => simp [binValues, Num.bin, Res.ofOption] at hb
          | bool _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
              simp [binValues] at hb
      | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
          cases v₂ <;> simp [binValues] at hb
  · rintro (h | ⟨h₁, h₂⟩)
    · exact ⟨_, h, Or.inl rfl⟩
    · exact ⟨_, h₁, Or.inr ⟨rfl, _, h₂, by simp [binValues, boolBin, Res.ofOption]⟩⟩

/-- `e_i!%.0 + e_n > |$f(e_z, e_x).BYTES|`, the comparison every `memory.*`
`-oob` rule is built from.  `b` is the comparison's *value*, so the lemma
serves both the short-circuited and the evaluated disjunct of
`memory.copy-oob` and `memory.init-oob`. -/
theorem evalExp_memGt_iff {env : Env} {ρ : VarEnv} {f : IL.Id}
    {ei en ez ex : Exp} {iv nv zv xv : Value} {b : Bool}
    (hi : EvalExp env ρ ei iv) (hn : EvalExp env ρ en nv)
    (hz : EvalExp env ρ ez zv) (hx : EvalExp env ρ ex xv)
    (hd : ρ.findDef? f = none) :
    EvalExp env ρ
      (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT) (.projE (.uncaseE ei "%") 0) en)
        (.lenE (.dotE (.callE f [.expA ez, .expA ex]) "BYTES"))) (.bool b) ↔
      ∃ a nn bs, Imm iv a ∧ nv = .num (.natN nn) ∧ CallBytes env f zv xv bs ∧
        b = decide (bs.length < a + nn) := by
  rw [evalExp_cmpE_iff]
  constructor
  · rintro ⟨u₁, u₂, hu₁, hu₂, hcmp⟩
    obtain ⟨bs, hbs, rfl⟩ := evalExp_lenE_iff.1 hu₂
    cases u₁ with
    | num m =>
        cases m with
        | natN t =>
            obtain ⟨a, nn, ha, hnn, rfl⟩ := evalExp_addNat_iff.1 hu₁
            obtain ⟨us, hus⟩ := evalExp_immE_iff.1 ha
            obtain rfl := EvalExp.unique hi hus
            obtain rfl := EvalExp.unique hn hnn
            refine ⟨a, nn, bs, ⟨us, rfl⟩, rfl, (evalExp_callBytes_iff hz hx hd).1 hbs, ?_⟩
            simpa [cmpValues, Num.cmp, Res.ofOption, eq_comm] using hcmp
        | intN _ => simp [cmpValues, Num.cmp, Res.ofOption] at hcmp
        | ratN _ => simp [cmpValues, Num.cmp, Res.ofOption] at hcmp
        | realN _ => simp [cmpValues, Num.cmp, Res.ofOption] at hcmp
    | bool _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
        simp [cmpValues] at hcmp
  · rintro ⟨a, nn, bs, ha, rfl, hcb, rfl⟩
    refine ⟨.num (.natN (a + nn)), .num (.natN bs.length), ?_, ?_, ?_⟩
    · refine evalExp_addNat_iff.2 ⟨a, nn, ?_, hn, rfl⟩
      obtain ⟨us, rfl⟩ := ha
      exact evalExp_immE_iff.2 ⟨us, hi⟩
    · exact evalExp_lenE_iff.2 ⟨bs, (evalExp_callBytes_iff hz hx hd).2 hcb, rfl⟩
    · simp [cmpValues, Num.cmp, Res.ofOption]

/-! ## `memory.fill`

Three rules over one left-hand side
`(CONST (at<:) i) val (CONST (at<:) (% n)) (MEMORY.FILL x)`.  Note that the
*same* `at` pattern occurs twice: the address and the count must carry the
same address type, which `matchExp` enforces as an equality test.

`-oob` and `-zero` are guarded; `-succ` has `else` as its only premise and so
fires on **every** configuration of this shape, out-of-bounds and
zero-length ones included.  That is the `Step_pure` overlap again. -/

/-- `(CONST (y <: numtype) (% w))` with `y` already **bound** and `w` fresh:
the count operand of `memory.fill`, `memory.copy` and `memory.init`. -/
theorem matchExp_constCount_iff {env : Env} {ρ ρ' : VarEnv} {y w : IL.Id}
    {t₁ t₂ : Typ} {a v : Value} (hy : ρ.findVal? y = some a)
    (hw : ρ.findVal? w = none) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.subE (.varE y) t₁ t₂,
        .caseE "%" (.tupE [.varE w])])) v ρ' ↔
      ∃ c, v = constV a (.case "%" (.tuple [c])) ∧ ρ' = ρ.bindVal w c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨av, cv, σ, rfl, ha, hc⟩ := matchExps_two_iff.1 hus
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hy] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs', rfl, hcvs'⟩ := Validation.matchExp_tup_iff.1 hcvs
    obtain ⟨c, rfl, hcc⟩ := matchExps_one_iff.1 hcvs'
    rw [matchExp_freshVar_iff hw] at hcc
    exact ⟨c, rfl, hcc⟩
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩),
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl, (matchExp_freshVar_iff hw).2 rfl⟩⟩⟩⟩⟩⟩

/-- The left-hand side all three `memory.fill` rules read. -/
theorem matchExps_memoryFillLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .subE (.varE "val") (.varT "val" []) (.varT "instr" []),
       .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .caseE "%" (.tupE [.varE "n"])]),
       .caseE "MEMORY.FILL" (.varE "x")] vs ρ' ↔
      ∃ atv i val n x,
        vs = [constV atv i, val, constV atv (.case "%" (.tuple [n])),
              .case "MEMORY.FILL" x] ∧
        ρ' = ((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "val" val).bindVal "n" n).bindVal "x" x) := by
  rw [matchExps_four_iff]
  constructor
  · rintro ⟨a, b, c, d, σ, τ, υ, rfl, ha, hb, hc, hd⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff (by simp)] at hb
    subst hb
    obtain ⟨n, rfl, rfl⟩ := (matchExp_constCount_iff (a := atv) (by simp) (by simp)).1 hc
    obtain ⟨xv, rfl, hxv⟩ := Validation.matchExp_case_iff.1 hd
    rw [matchExp_freshVar_iff (by simp)] at hxv
    exact ⟨atv, i, b, n, xv, rfl, hxv⟩
  · rintro ⟨atv, i, val, n, x, rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff (by simp)).2 rfl),
      (matchExp_constCount_iff (a := atv) (by simp) (by simp)).2 ⟨n, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩

/-- **`Step_read/memory.fill-oob`, characterised exactly.** -/
theorem ruleFires_memoryFillOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryFillOobRule ↔
      ∃ z atv i val nn x a bs,
        v = readV z [constV atv i, val,
            constV atv (.case "%" (.tuple [.num (.natN nn)])), .case "MEMORY.FILL" x]
          [Execution.trapV] ∧
        Imm i a ∧ CallBytes env "mem" z x bs ∧ bs.length < a + nn := by
  unfold memoryFillOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, val, n, x, rfl, rfl⟩ := matchExps_memoryFillLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_memGt_iff (iv := i) (nv := n) (zv := z) (xv := x)
      (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
      (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at hev
    obtain ⟨a, nn, bs, ha, rfl, hcb, hlt⟩ := hev
    exact ⟨z, atv, i, val, nn, x, a, bs, rfl, ha, hcb, by simpa [eq_comm] using hlt⟩
  · rintro ⟨z, atv, i, val, nn, x, a, bs, rfl, ha, hcb, hlt⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryFillLhs_iff.2 ⟨atv, i, val, .num (.natN nn), x, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    exact (evalExp_memGt_iff (iv := i) (nv := .num (.natN nn)) (zv := z) (xv := x)
      (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
      (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
      ⟨a, nn, bs, ha, rfl, hcb, by simp [hlt]⟩

/-- **`Step_read/memory.fill-zero`, characterised exactly.**  The count must
be the numeral `0` itself — `n` is matched, not `n!%.0`, so a `(% 0)` with a
non-numeral payload does not qualify. -/
theorem ruleFires_memoryFillZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryFillZeroRule ↔
      ∃ z atv i val x,
        v = readV z [constV atv i, val,
            constV atv (.case "%" (.tuple [.num (.natN 0)])), .case "MEMORY.FILL" x]
          [] := by
  unfold memoryFillZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, val, n, x, rfl, rfl⟩ := matchExps_memoryFillLhs_iff.1 hvs
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hws
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    simp at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hu₁
    exact ⟨z, atv, i, val, x, rfl⟩
  · rintro ⟨z, atv, i, val, x, rfl⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryFillLhs_iff.2 ⟨atv, i, val, .num (.natN 0), x, rfl, rfl⟩,
      Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩,
      ExecRef.premsHold_elseIf_iff.2 ⟨rfl,
        evalExp_cmpE_iff.2 ⟨_, _, evalExp_varE_iff.2 (by simp),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩⟩

/-- `v` reads as the integer `k` under the IL's `nat`-to-`int` coercion.  The
IL writes a decrement as `(((n : int) - 1) : nat)`, and *as a pattern* that
coerces the matched value back along `int` — so the slot need not be a `nat`
at all, only something `Num.cvt .intT` accepts. -/
def AsInt (v : Value) (k : Int) : Prop :=
  ∃ m, v = .num m ∧ Num.cvt .intT m = some (.intN k)

/-- `(STORE I32 ?((% (% 8))) x ao)`, the byte store the three expanding
rules emit. -/
def store8V (x ao : Value) : Value :=
  .case "STORE" (.tuple [Execution.i32V,
    .opt (some (.case "%" (.tuple [.case "%" (.tuple [.num (.natN 8)])]))), x, ao])

/-- `(CONST (y <: numtype) w)` with both names already bound: a pure
equality test. -/
theorem matchExp_constBound_iff {env : Env} {ρ ρ' : VarEnv} {y w : IL.Id}
    {t₁ t₂ : Typ} {a c v : Value} (hy : ρ.findVal? y = some a)
    (hw : ρ.findVal? w = some c) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.subE (.varE y) t₁ t₂, .varE w])) v ρ' ↔
      v = constV a c ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨av, cv, σ, rfl, ha, hc⟩ := matchExps_two_iff.1 hus
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hy] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_boundVar_iff hw] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hy).2 ⟨rfl, rfl⟩),
        (matchExp_boundVar_iff hw).2 ⟨rfl, rfl⟩⟩⟩⟩

/-- `e + 1` at `nat`. -/
theorem evalExp_succE_iff {env : Env} {ρ : VarEnv} {e : Exp} {w : Value} :
    EvalExp env ρ (.binE .addOp (.numT .natT) e (.numE (.natN 1))) w ↔
      ∃ a, EvalExp env ρ e (.num (.natN a)) ∧ w = .num (.natN (a + 1)) := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs⟩
    rw [boolShort_add] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hb⟩ := hs
    rw [evalExp_numE_iff] at hv₂
    subst hv₂
    cases v₁ with
    | num m =>
        cases m with
        | natN a =>
            exact ⟨a, hv₁, by simpa [binValues, Num.bin, Res.ofOption, eq_comm] using hb⟩
        | intN _ => simp [binValues, Num.bin, Res.ofOption] at hb
        | ratN _ => simp [binValues, Num.bin, Res.ofOption] at hb
        | realN _ => simp [binValues, Num.bin, Res.ofOption] at hb
    | bool _ | text _ | tuple _ | case _ _ | struct _ | list _ | opt _ =>
        simp [binValues] at hb
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ha, Or.inr ⟨boolShort_add _, _, evalExp_numE_iff.2 rfl,
      by simp [binValues, Num.bin, Res.ofOption]⟩⟩

/-- `(e : int) - 1`, the IL's decrement. -/
theorem evalExp_predE_iff {env : Env} {ρ : VarEnv} {e : Exp} {m' : Num} :
    EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num m') ↔
      ∃ mn k, EvalExp env ρ e (.num mn) ∧ Num.cvt .intT mn = some (.intN k) ∧
        m' = .intN (k - 1) := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs⟩
    rw [boolShort_sub] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hb⟩ := hs
    obtain ⟨m₁, m₂, rfl, rfl, hbn⟩ := binValues_eq_num_iff.1 hb
    obtain ⟨mn, mm, hmn, hc, hv⟩ := evalExp_cvtE_iff.1 hv₁
    obtain ⟨o, o', ho, hco, hvo⟩ := evalExp_cvtE_iff.1 hv₂
    rw [evalExp_numE_iff] at ho
    obtain rfl := Value.num.inj ho
    simp only [Num.cvt, Option.some.injEq] at hco
    subst hco
    obtain rfl := Value.num.inj hv
    obtain rfl := Value.num.inj hvo
    cases m₁ with
    | intN k => exact ⟨mn, k, hmn, hc, by simpa [Num.bin, eq_comm] using hbn⟩
    | natN _ => simp [Num.bin] at hbn
    | ratN _ => simp [Num.bin] at hbn
    | realN _ => simp [Num.bin] at hbn
  · rintro ⟨mn, k, hmn, hc, rfl⟩
    refine ⟨.num (.intN k), evalExp_cvtE_iff.2 ⟨mn, .intN k, hmn, hc, rfl⟩,
      Or.inr ⟨boolShort_sub _, _,
        evalExp_cvtE_iff.2 ⟨.natN 1, _, evalExp_numE_iff.2 rfl, rfl, rfl⟩,
        binValues_eq_num_iff.2 ⟨_, _, rfl, rfl, ?_⟩⟩⟩
    simp [Num.bin]

/-- **`Step_read/memory.fill-succ`, characterised exactly.**  Its only
premise is `else`, which `Sem/Eval.lean` discharges unconditionally, so the
only condition is that the conclusion matches — the rule fires out of bounds
and at zero length too. -/
theorem ruleFires_memoryFillSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryFillSuccRule ↔
      ∃ z atv i val mn x a k ma w,
        v = readV z
            [constV atv i, val, constV atv (.case "%" (.tuple [.num mn])),
              .case "MEMORY.FILL" x]
            [constV atv i, val, store8V x ma,
              constV atv (.case "%" (.tuple [.num (.natN (a + 1))])), val,
              constV atv (.case "%" (.tuple [w])), .case "MEMORY.FILL" x] ∧
        Imm i a ∧ Num.cvt .intT mn = some (.intN k) ∧ AsInt w (k - 1) ∧
        ExecNumeric.Applies env "memarg0" [] ma := by
  unfold memoryFillSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, val, n, x, rfl, rfl⟩ := matchExps_memoryFillLhs_iff.1 hvs
    obtain rfl := ExecRef.premsHold_else_iff.1 hp
    obtain ⟨w₁, r₁, σ₁, rfl, h₁, hr1⟩ := Validation.matchExps_cons_iff.1 hws
    rw [matchExp_constBound_iff (a := atv) (c := i) (by simp) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨w₂, r₂, σ₂, rfl, h₂, hr2⟩ := Validation.matchExps_cons_iff.1 hr1
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := val) (by simp)] at h₂
    obtain ⟨heq₂, rfl⟩ := h₂
    subst w₂
    obtain ⟨w₃, r₃, σ₃, rfl, h₃, hr3⟩ := Validation.matchExps_cons_iff.1 hr2
    obtain ⟨sv, rfl, hsv⟩ := Validation.matchExp_case_iff.1 h₃
    obtain ⟨svs, rfl, hsvs⟩ := Validation.matchExp_tup_iff.1 hsv
    obtain ⟨tv, ov, xv, mav, α, β, γ, rfl, htv, hov, hxv, hmav⟩ :=
      matchExps_four_iff.1 hsvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    obtain ⟨ov', rfl, hov'⟩ := Validation.matchExp_optSome_iff.1 hov
    obtain ⟨ov₂, rfl, hov₂⟩ := Validation.matchExp_case_iff.1 hov'
    obtain ⟨ov₃, rfl, hov₃⟩ := Validation.matchExp_tup_iff.1 hov₂
    obtain ⟨ov₄, rfl, hov₄⟩ := matchExps_one_iff.1 hov₃
    obtain ⟨ov₅, rfl, hov₅⟩ := Validation.matchExp_case_iff.1 hov₄
    obtain ⟨ov₆, rfl, hov₆⟩ := Validation.matchExp_tup_iff.1 hov₅
    obtain ⟨ov₇, rfl, hov₇⟩ := matchExps_one_iff.1 hov₆
    rw [ExecRef.matchExp_numE_iff] at hov₇
    obtain ⟨rfl, rfl⟩ := hov₇
    rw [matchExp_boundVar_iff (w := x) (by simp)] at hxv
    obtain ⟨heqx, rfl⟩ := hxv
    subst xv
    obtain ⟨hma, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hmav
    obtain ⟨w₄, r₄, σ₄, rfl, h₄, hr4⟩ := Validation.matchExps_cons_iff.1 hr3
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 h₄
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨av, pv, δ, rfl, hav, hpv⟩ := matchExps_two_iff.1 hcvs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := atv) (by simp)] at hav
    obtain ⟨heqa, rfl⟩ := hav
    subst av
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_case_iff.1 hpv
    obtain ⟨pvs', rfl, hpvs'⟩ := Validation.matchExp_tup_iff.1 hpvs
    obtain ⟨sv', rfl, hsv'⟩ := matchExps_one_iff.1 hpvs'
    rw [matchExp_binE_iff, evalExp_succE_iff] at hsv'
    obtain ⟨⟨a, ha, rfl⟩, rfl⟩ := hsv'
    rw [evalExp_imm_iff (c := i) (by simp)] at ha
    obtain ⟨w₅, r₅, σ₅, rfl, h₅, hr5⟩ := Validation.matchExps_cons_iff.1 hr4
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := val) (by simp)] at h₅
    obtain ⟨heq₅, rfl⟩ := h₅
    subst w₅
    obtain ⟨w₆, r₆, σ₆, rfl, h₆, hr6⟩ := Validation.matchExps_cons_iff.1 hr5
    obtain ⟨dv, rfl, hdv⟩ := Validation.matchExp_case_iff.1 h₆
    obtain ⟨dvs, rfl, hdvs⟩ := Validation.matchExp_tup_iff.1 hdv
    obtain ⟨av', qv, ε, rfl, hav', hqv⟩ := matchExps_two_iff.1 hdvs
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := atv) (by simp)] at hav'
    obtain ⟨heqa', rfl⟩ := hav'
    subst av'
    obtain ⟨qvs, rfl, hqvs⟩ := Validation.matchExp_case_iff.1 hqv
    obtain ⟨qvs', rfl, hqvs'⟩ := Validation.matchExp_tup_iff.1 hqvs
    obtain ⟨tv', rfl, htv'⟩ := matchExps_one_iff.1 hqvs'
    rw [matchExp_cvtE_iff] at htv'
    obtain ⟨mw, mw', rfl, hcw, hbw⟩ := htv'
    rw [matchExp_binE_iff, evalExp_predE_iff] at hbw
    obtain ⟨⟨mnn, kk, hmnn, hck, rfl⟩, rfl⟩ := hbw
    rw [evalExp_varE_iff] at hmnn
    simp at hmnn
    obtain ⟨w₇, r₇, σ₇, rfl, h₇, hnil⟩ := Validation.matchExps_cons_iff.1 hr6
    obtain ⟨xv', rfl, hxv'⟩ := Validation.matchExp_case_iff.1 h₇
    rw [matchExp_boundVar_iff (w := x) (by simp)] at hxv'
    obtain ⟨heqx', rfl⟩ := hxv'
    subst xv'
    obtain ⟨rfl, -⟩ := Validation.matchExps_nil_iff.1 hnil
    subst hmnn
    exact ⟨z, atv, i, val, mnn, x, a, kk, mav, .num mw, rfl, ha, hck,
      ⟨mw, rfl, hcw⟩,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma⟩
  · rintro ⟨z, atv, i, val, mn, x, a, k, ma, w, rfl, ha, hck, ⟨mw, rfl, hcw⟩, hma⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryFillLhs_iff.2 ⟨atv, i, val, .num mn, x, rfl, rfl⟩,
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        (matchExp_constBound_iff (a := atv) (c := i) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2
          ((matchExp_boundVar_iff (w := val) (by simp)).2 ⟨rfl, rfl⟩),
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma,
                  rfl⟩⟩⟩⟩,
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := atv) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_binE_iff.2 ⟨evalExp_succE_iff.2
                      ⟨a, (evalExp_imm_iff (c := i) (by simp)).2 ha, rfl⟩, rfl⟩⟩⟩⟩⟩⟩⟩,
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2
          ((matchExp_boundVar_iff (w := val) (by simp)).2 ⟨rfl, rfl⟩),
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := atv) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_cvtE_iff.2 ⟨mw, .intN (k - 1), rfl, hcw,
                      matchExp_binE_iff.2 ⟨evalExp_predE_iff.2
                        ⟨mn, k, evalExp_varE_iff.2 (by simp), hck, rfl⟩,
                        rfl⟩⟩⟩⟩⟩⟩⟩⟩,
      Validation.matchExps_cons_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩⟩,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩

/-- **The `else` overlap, at `memory.fill`.**  Take the count to be `0`: the
configuration `memory.fill-zero` sends to `eps` *also* expands by
`memory.fill-succ`, which is supposed to be the inductive case.  Nothing in
the three rules orders them, so both steps are derivable. -/
theorem ruleFires_memoryFillSucc_atZeroCount {env : Env} (z atv i val x ma : Value)
    (a : Nat) (ha : Imm i a) (hma : ExecNumeric.Applies env "memarg0" [] ma) :
    RuleFires env "%~>%" [] []
      (readV z
        [constV atv i, val, constV atv (.case "%" (.tuple [.num (.natN 0)])),
          .case "MEMORY.FILL" x]
        [constV atv i, val, store8V x ma,
          constV atv (.case "%" (.tuple [.num (.natN (a + 1))])), val,
          constV atv (.case "%" (.tuple [.num (.intN (-1))])), .case "MEMORY.FILL" x])
      memoryFillSuccRule :=
  ruleFires_memoryFillSucc_iff.2
    ⟨z, atv, i, val, .natN 0, x, a, 0, ma, .num (.intN (-1)), rfl, ha, rfl,
      ⟨.intN (-1), rfl, by decide⟩, hma⟩

/-! ## `memory.copy` and `memory.init`

Both check two ranges, and both write the check as a single `\/`.
`eval.ml:240-255` short-circuits `\/` on its *left* operand, so the second
range is consulted only when the first is in bounds: `OobDisj` records a
disjunct's value rather than its truth, which is what makes the
characterisation exact. -/

/-- One disjunct of a `memory.copy` / `memory.init` bound check, together
with its **value**: `b` is `true` exactly when the range runs past the end. -/
def OobDisj (env : Env) (f : IL.Id) (z x i : Value) (nn : Nat) (b : Bool) : Prop :=
  ∃ a bs, Imm i a ∧ CallBytes env f z x bs ∧ b = decide (bs.length < a + nn)

/-- `(CONST (y <: numtype) (% w))` with `y` **fresh**: `memory.copy`'s count
carries its own address type `at'`, unrelated to either operand's. -/
theorem matchExp_constFreshCount_iff {env : Env} {ρ ρ' : VarEnv} {y w : IL.Id}
    {t₁ t₂ : Typ} {v : Value} (hy : ρ.findVal? y = none)
    (hw : ∀ u, (ρ.bindVal y u).findVal? w = none) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.subE (.varE y) t₁ t₂,
        .caseE "%" (.tupE [.varE w])])) v ρ' ↔
      ∃ a c, v = constV a (.case "%" (.tuple [c])) ∧
        ρ' = (ρ.bindVal y a).bindVal w c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨av, cv, σ, rfl, ha, hc⟩ := matchExps_two_iff.1 hus
    rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff hy] at ha
    subst ha
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs', rfl, hcvs'⟩ := Validation.matchExp_tup_iff.1 hcvs
    obtain ⟨c, rfl, hcc⟩ := matchExps_one_iff.1 hcvs'
    rw [matchExp_freshVar_iff (hw av)] at hcc
    exact ⟨av, c, rfl, hcc⟩
  · rintro ⟨a, c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl,
        Validation.matchExp_sub_iff.2 ((matchExp_freshVar_iff hy).2 rfl),
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl, (matchExp_freshVar_iff (hw a)).2 rfl⟩⟩⟩⟩⟩⟩

/-- The left-hand side all four `memory.copy` rules read. -/
theorem matchExps_memoryCopyLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at_1") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i_1"]),
       .caseE "CONST" (.tupE [.subE (.varE "at_2") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i_2"]),
       .caseE "CONST" (.tupE [.subE (.varE "at'") (.varT "addrtype" [])
          (.varT "numtype" []), .caseE "%" (.tupE [.varE "n"])]),
       .caseE "MEMORY.COPY" (.tupE [.varE "x_1", .varE "x_2"])] vs ρ' ↔
      ∃ at₁ i₁ at₂ i₂ at' n x₁ x₂,
        vs = [constV at₁ i₁, constV at₂ i₂, constV at' (.case "%" (.tuple [n])),
              .case "MEMORY.COPY" (.tuple [x₁, x₂])] ∧
        ρ' = (((((((((VarEnv.empty.bindVal "z" z).bindVal "at_1" at₁).bindVal
          "i_1" i₁).bindVal "at_2" at₂).bindVal "i_2" i₂).bindVal "at'" at').bindVal
          "n" n).bindVal "x_1" x₁).bindVal "x_2" x₂) := by
  rw [matchExps_four_iff]
  constructor
  · rintro ⟨a, b, c, d, σ, τ, υ, rfl, ha, hb, hc, hd⟩
    obtain ⟨at₁, i₁, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨at₂, i₂, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 hb
    obtain ⟨at', n, rfl, rfl⟩ :=
      (matchExp_constFreshCount_iff (by simp) (fun _ => by simp)).1 hc
    obtain ⟨dv, rfl, hdv⟩ := Validation.matchExp_case_iff.1 hd
    obtain ⟨dvs, rfl, hdvs⟩ := Validation.matchExp_tup_iff.1 hdv
    obtain ⟨x₁, x₂, ψ, rfl, hx₁, hx₂⟩ := matchExps_two_iff.1 hdvs
    rw [matchExp_freshVar_iff (by simp)] at hx₁
    subst hx₁
    rw [matchExp_freshVar_iff (by simp)] at hx₂
    exact ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, hx₂⟩
  · rintro ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨at₁, i₁, rfl, rfl⟩,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨at₂, i₂, rfl, rfl⟩,
      (matchExp_constFreshCount_iff (by simp) (fun _ => by simp)).2 ⟨at', n, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/memory.copy-oob`, characterised exactly.**  Note that the
three address types `at_1`, `at_2` and `at'` are *independent* pattern
variables: nothing in the rule relates them. -/
theorem ruleFires_memoryCopyOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryCopyOobRule ↔
      ∃ z at₁ i₁ at₂ i₂ at' nn x₁ x₂,
        v = readV z [constV at₁ i₁, constV at₂ i₂,
            constV at' (.case "%" (.tuple [.num (.natN nn)])),
            .case "MEMORY.COPY" (.tuple [x₁, x₂])] [Execution.trapV] ∧
        (OobDisj env "mem" z x₁ i₁ nn true ∨
          (OobDisj env "mem" z x₁ i₁ nn false ∧ OobDisj env "mem" z x₂ i₂ nn true)) := by
  unfold memoryCopyOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, rfl⟩ :=
      matchExps_memoryCopyLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_orE_true_iff] at hev
    rcases hev with h | ⟨h₁, h₂⟩
    · rw [evalExp_memGt_iff (iv := i₁) (nv := n) (zv := z) (xv := x₁)
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h
      obtain ⟨a, nn, bs, ha, rfl, hcb, hb⟩ := h
      exact ⟨z, at₁, i₁, at₂, i₂, at', nn, x₁, x₂, rfl, Or.inl ⟨a, bs, ha, hcb, hb⟩⟩
    · rw [evalExp_memGt_iff (iv := i₁) (nv := n) (zv := z) (xv := x₁)
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h₁
      obtain ⟨a, nn, bs, ha, rfl, hcb, hb⟩ := h₁
      rw [evalExp_memGt_iff (iv := i₂) (nv := .num (.natN nn)) (zv := z) (xv := x₂)
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h₂
      obtain ⟨a', nn', bs', ha', hnn, hcb', hb'⟩ := h₂
      obtain rfl : nn = nn' := by simpa using hnn
      exact ⟨z, at₁, i₁, at₂, i₂, at', nn, x₁, x₂, rfl,
        Or.inr ⟨⟨a, bs, ha, hcb, hb⟩, ⟨a', bs', ha', hcb', hb'⟩⟩⟩
  · rintro ⟨z, at₁, i₁, at₂, i₂, at', nn, x₁, x₂, rfl, hd⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryCopyLhs_iff.2
        ⟨at₁, i₁, at₂, i₂, at', .num (.natN nn), x₁, x₂, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine evalExp_orE_true_iff.2 ?_
    rcases hd with ⟨a, bs, ha, hcb, hb⟩ |
      ⟨⟨a, bs, ha, hcb, hb⟩, ⟨a', bs', ha', hcb', hb'⟩⟩
    · exact Or.inl ((evalExp_memGt_iff (iv := i₁) (nv := .num (.natN nn)) (zv := z)
        (xv := x₁) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a, nn, bs, ha, rfl, hcb, hb⟩)
    · exact Or.inr ⟨(evalExp_memGt_iff (iv := i₁) (nv := .num (.natN nn)) (zv := z)
        (xv := x₁) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a, nn, bs, ha, rfl, hcb, hb⟩,
        (evalExp_memGt_iff (iv := i₂) (nv := .num (.natN nn)) (zv := z)
        (xv := x₂) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a', nn, bs', ha', rfl, hcb', hb'⟩⟩

/-- **`Step_read/memory.copy-zero`, characterised exactly.** -/
theorem ruleFires_memoryCopyZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryCopyZeroRule ↔
      ∃ z at₁ i₁ at₂ i₂ at' x₁ x₂,
        v = readV z [constV at₁ i₁, constV at₂ i₂,
            constV at' (.case "%" (.tuple [.num (.natN 0)])),
            .case "MEMORY.COPY" (.tuple [x₁, x₂])] [] := by
  unfold memoryCopyZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, rfl⟩ :=
      matchExps_memoryCopyLhs_iff.1 hvs
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hws
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    simp at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hu₁
    exact ⟨z, at₁, i₁, at₂, i₂, at', x₁, x₂, rfl⟩
  · rintro ⟨z, at₁, i₁, at₂, i₂, at', x₁, x₂, rfl⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryCopyLhs_iff.2
        ⟨at₁, i₁, at₂, i₂, at', .num (.natN 0), x₁, x₂, rfl, rfl⟩,
      Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩,
      ExecRef.premsHold_elseIf_iff.2 ⟨rfl,
        evalExp_cmpE_iff.2 ⟨_, _, evalExp_varE_iff.2 (by simp),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩⟩

/-- The left-hand side all three `memory.init` rules read.  Both the data
offset and the count are `I32` here, not `at`: only the memory address
carries an address type. -/
theorem matchExps_memoryInitLhs_iff {env : Env} {ρ' : VarEnv} {z : Value}
    {vs : List Value} :
    MatchExps env (VarEnv.empty.bindVal "z" z)
      [.caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" [])
          (.varT "numtype" []), .varE "i"]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "j"]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
          .caseE "%" (.tupE [.varE "n"])]),
       .caseE "MEMORY.INIT" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ atv i j n x y,
        vs = [constV atv i, constV Execution.i32V j,
              constV Execution.i32V (.case "%" (.tuple [n])),
              .case "MEMORY.INIT" (.tuple [x, y])] ∧
        ρ' = (((((((VarEnv.empty.bindVal "z" z).bindVal "at" atv).bindVal "i" i).bindVal
          "j" j).bindVal "n" n).bindVal "x" x).bindVal "y" y) := by
  rw [matchExps_four_iff]
  constructor
  · rintro ⟨a, b, c, d, σ, τ, υ, rfl, ha, hb, hc, hd⟩
    obtain ⟨atv, i, rfl, rfl⟩ :=
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).1 ha
    obtain ⟨bv, rfl, hbv⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_tup_iff.1 hbv
    obtain ⟨tv, j, ψ, rfl, htv, hj⟩ := matchExps_two_iff.1 hbvs
    rw [matchExp_caseNil_iff] at htv
    obtain ⟨rfl, rfl⟩ := htv
    rw [matchExp_freshVar_iff (by simp)] at hj
    subst hj
    obtain ⟨cv, rfl, hcv⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨cvs, rfl, hcvs⟩ := Validation.matchExp_tup_iff.1 hcv
    obtain ⟨tv', pv, ω, rfl, htv', hpv⟩ := matchExps_two_iff.1 hcvs
    rw [matchExp_caseNil_iff] at htv'
    obtain ⟨rfl, rfl⟩ := htv'
    obtain ⟨pvs, rfl, hpvs⟩ := Validation.matchExp_case_iff.1 hpv
    obtain ⟨pvs', rfl, hpvs'⟩ := Validation.matchExp_tup_iff.1 hpvs
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hpvs'
    rw [matchExp_freshVar_iff (by simp)] at hn
    subst hn
    obtain ⟨dv, rfl, hdv⟩ := Validation.matchExp_case_iff.1 hd
    obtain ⟨dvs, rfl, hdvs⟩ := Validation.matchExp_tup_iff.1 hdv
    obtain ⟨x, y, ζ, rfl, hx, hy⟩ := matchExps_two_iff.1 hdvs
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    rw [matchExp_freshVar_iff (by simp)] at hy
    exact ⟨atv, i, j, n, x, y, rfl, hy⟩
  · rintro ⟨atv, i, j, n, x, y, rfl, rfl⟩
    exact ⟨_, _, _, _, _, _, _, rfl,
      (matchExp_constPat_iff (by simp) (fun _ => by simp)).2 ⟨atv, i, rfl, rfl⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
            Validation.matchExp_case_iff.2 ⟨_, rfl,
              Validation.matchExp_tup_iff.2 ⟨_, rfl,
                matchExps_one_iff.2 ⟨_, rfl,
                  (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩⟩,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩

/-- **`Step_read/memory.init-oob`, characterised exactly.**  The second
disjunct reads `$data(z, y).BYTES`, and is consulted only when the first is
in bounds. -/
theorem ruleFires_memoryInitOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryInitOobRule ↔
      ∃ z atv i j nn x y,
        v = readV z [constV atv i, constV Execution.i32V j,
            constV Execution.i32V (.case "%" (.tuple [.num (.natN nn)])),
            .case "MEMORY.INIT" (.tuple [x, y])] [Execution.trapV] ∧
        (OobDisj env "mem" z x i nn true ∨
          (OobDisj env "mem" z x i nn false ∧ OobDisj env "data" z y j nn true)) := by
  unfold memoryInitOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, j, n, x, y, rfl, rfl⟩ := matchExps_memoryInitLhs_iff.1 hvs
    obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
    rw [matchExp_caseNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨κ, hpr, hrest⟩ := Validation.premsHold_cons_iff.1 hp
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr
    rw [evalExp_orE_true_iff] at hev
    rcases hev with h | ⟨h₁, h₂⟩
    · rw [evalExp_memGt_iff (iv := i) (nv := n) (zv := z) (xv := x)
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h
      obtain ⟨a, nn, bs, ha, rfl, hcb, hb⟩ := h
      exact ⟨z, atv, i, j, nn, x, y, rfl, Or.inl ⟨a, bs, ha, hcb, hb⟩⟩
    · rw [evalExp_memGt_iff (iv := i) (nv := n) (zv := z) (xv := x)
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h₁
      obtain ⟨a, nn, bs, ha, rfl, hcb, hb⟩ := h₁
      rw [evalExp_memGt_iff (f := "data") (iv := j) (nv := .num (.natN nn)) (zv := z)
        (xv := y) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl] at h₂
      obtain ⟨a', nn', bs', ha', hnn, hcb', hb'⟩ := h₂
      obtain rfl : nn = nn' := by simpa using hnn
      exact ⟨z, atv, i, j, _, x, y, rfl,
        Or.inr ⟨⟨a, bs, ha, hcb, hb⟩, ⟨a', bs', ha', hcb', hb'⟩⟩⟩
  · rintro ⟨z, atv, i, j, nn, x, y, rfl, hd⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryInitLhs_iff.2 ⟨atv, i, j, .num (.natN nn), x, y, rfl, rfl⟩,
      matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_cons_iff.2 ⟨_, Validation.premHolds_if_iff.2 ⟨rfl, ?_⟩,
        Validation.premsHold_nil_iff.2 rfl⟩⟩
    refine evalExp_orE_true_iff.2 ?_
    rcases hd with ⟨a, bs, ha, hcb, hb⟩ |
      ⟨⟨a, bs, ha, hcb, hb⟩, ⟨a', bs', ha', hcb', hb'⟩⟩
    · exact Or.inl ((evalExp_memGt_iff (iv := i) (nv := .num (.natN nn)) (zv := z)
        (xv := x) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a, nn, bs, ha, rfl, hcb, hb⟩)
    · exact Or.inr ⟨(evalExp_memGt_iff (iv := i) (nv := .num (.natN nn)) (zv := z)
        (xv := x) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a, nn, bs, ha, rfl, hcb, hb⟩,
        (evalExp_memGt_iff (f := "data") (iv := j) (nv := .num (.natN nn)) (zv := z)
        (xv := y) (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp))
        (evalExp_varE_iff.2 (by simp)) (evalExp_varE_iff.2 (by simp)) rfl).2
        ⟨a', nn, bs', ha', rfl, hcb', hb'⟩⟩

/-- **`Step_read/memory.init-zero`, characterised exactly.** -/
theorem ruleFires_memoryInitZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryInitZeroRule ↔
      ∃ z atv i j x y,
        v = readV z [constV atv i, constV Execution.i32V j,
            constV Execution.i32V (.case "%" (.tuple [.num (.natN 0)])),
            .case "MEMORY.INIT" (.tuple [x, y])] [] := by
  unfold memoryInitZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, j, n, x, y, rfl, rfl⟩ := matchExps_memoryInitLhs_iff.1 hvs
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 hws
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨u₁, u₂, hu₁, hu₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at hu₁
    simp at hu₁
    rw [evalExp_numE_iff] at hu₂
    subst hu₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hcmp
    subst hu₁
    exact ⟨z, atv, i, j, x, y, rfl⟩
  · rintro ⟨z, atv, i, j, x, y, rfl⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryInitLhs_iff.2 ⟨atv, i, j, .num (.natN 0), x, y, rfl, rfl⟩,
      Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩,
      ExecRef.premsHold_elseIf_iff.2 ⟨rfl,
        evalExp_cmpE_iff.2 ⟨_, _, evalExp_varE_iff.2 (by simp),
          evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩⟩

/-! ## The three expanding rules

`memory.init-succ`, `memory.copy-le` and `memory.copy-gt` rewrite one step of
the loop into a seven- or eight-instruction sequence.  Their right-hand sides
are the longest patterns in `Step_read`, so they need pattern lists of six,
seven and eight, and `ProjE 0` / `UncaseE` *as patterns* — `eval.ml` treats
`e!%.0` as a pattern, not as an evaluation, when it appears on the right. -/

/-- A six-element pattern list. -/
theorem matchExps_six_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ e₅ e₆ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅, e₆] vs ρ' ↔
      ∃ a b c d e f σ τ υ φ χ, vs = [a, b, c, d, e, f] ∧
        MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧
        MatchExp env υ e₄ d φ ∧ MatchExp env φ e₅ e χ ∧ MatchExp env χ e₆ f ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, f, τ, υ, φ, χ, rfl, hb, hc, hd, he, hf⟩ := matchExps_five_iff.1 h₂
    exact ⟨w, b, c, d, e, f, σ, τ, υ, φ, χ, rfl, h₁, hb, hc, hd, he, hf⟩
  · rintro ⟨a, b, c, d, e, f, σ, τ, υ, φ, χ, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨a, [b, c, d, e, f], σ, rfl, h₁,
      matchExps_five_iff.2 ⟨b, c, d, e, f, τ, υ, φ, χ, rfl, h₂, h₃, h₄, h₅, h₆⟩⟩

/-- A seven-element pattern list. -/
theorem matchExps_seven_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ e₅ e₆ e₇ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅, e₆, e₇] vs ρ' ↔
      ∃ a b c d e f g σ τ υ φ χ ψ, vs = [a, b, c, d, e, f, g] ∧
        MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧
        MatchExp env υ e₄ d φ ∧ MatchExp env φ e₅ e χ ∧ MatchExp env χ e₆ f ψ ∧
        MatchExp env ψ e₇ g ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, f, g, τ, υ, φ, χ, ψ, rfl, hb, hc, hd, he, hf, hg⟩ :=
      matchExps_six_iff.1 h₂
    exact ⟨w, b, c, d, e, f, g, σ, τ, υ, φ, χ, ψ, rfl, h₁, hb, hc, hd, he, hf, hg⟩
  · rintro ⟨a, b, c, d, e, f, g, σ, τ, υ, φ, χ, ψ, rfl, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
    exact ⟨a, [b, c, d, e, f, g], σ, rfl, h₁,
      matchExps_six_iff.2 ⟨b, c, d, e, f, g, τ, υ, φ, χ, ψ, rfl, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩

/-- An eight-element pattern list. -/
theorem matchExps_eight_iff {env : Env} {ρ ρ' : VarEnv}
    {e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : Exp} {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈] vs ρ' ↔
      ∃ a b c d e f g h σ τ υ φ χ ψ ω, vs = [a, b, c, d, e, f, g, h] ∧
        MatchExp env ρ e₁ a σ ∧ MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧
        MatchExp env υ e₄ d φ ∧ MatchExp env φ e₅ e χ ∧ MatchExp env χ e₆ f ψ ∧
        MatchExp env ψ e₇ g ω ∧ MatchExp env ω e₈ h ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, f, g, h, τ, υ, φ, χ, ψ, ω, rfl, hb, hc, hd, he, hf, hg, hh⟩ :=
      matchExps_seven_iff.1 h₂
    exact ⟨w, b, c, d, e, f, g, h, σ, τ, υ, φ, χ, ψ, ω, rfl,
      h₁, hb, hc, hd, he, hf, hg, hh⟩
  · rintro ⟨a, b, c, d, e, f, g, h, σ, τ, υ, φ, χ, ψ, ω, rfl,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
    exact ⟨a, [b, c, d, e, f, g, h], σ, rfl, h₁,
      matchExps_seven_iff.2
        ⟨b, c, d, e, f, g, h, τ, υ, φ, χ, ψ, ω, rfl, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩⟩

/-- `matchExp` at `ProjE 0` is a *pattern*, not an evaluation: it matches
underneath a one-component tuple. -/
theorem matchExp_projE0_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.projE e 0) v ρ' ↔ MatchExp env ρ e (.tuple [v]) ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ p => exact ⟨p, by simpa [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa [matchExp] using hn⟩

/-- `matchExp` at an `UncaseE` is a pattern too. -/
theorem matchExp_uncaseE_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {op : MixopS}
    {v : Value} :
    MatchExp env ρ (.uncaseE e op) v ρ' ↔ MatchExp env ρ e (.case op v) ρ' := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ p => exact ⟨p, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `(LOAD I32 ?((% 8) U) x ao)`, the byte load `memory.copy` expands to. -/
def loadU8V (x ao : Value) : Value :=
  .case "LOAD" (.tuple [Execution.i32V,
    .opt (some (.case "%_%" (.tuple [.case "%" (.tuple [.num (.natN 8)]),
      Execution.caseNilV "U"]))), x, ao])

/-- `Value.idx?` is defined on lists only. -/
theorem idx?_eq_some_iff {v : Value} {i : Nat} {w : Value} :
    v.idx? i = some w ↔ ∃ bs, v = .list bs ∧ bs[i]? = some w := by
  cases v with
  | list bs => simp [Value.idx?]
  | bool _ => simp [Value.idx?]
  | num _ => simp [Value.idx?]
  | text _ => simp [Value.idx?]
  | tuple _ => simp [Value.idx?]
  | case _ _ => simp [Value.idx?]
  | struct _ => simp [Value.idx?]
  | opt _ => simp [Value.idx?]

/-- `$data(z, y).BYTES[j!%.0]` is `(% byt)`: the byte `memory.init-succ`
copies, read through the `%` injection that `byte` is. -/
def DataByteAt (env : Env) (z y j : Value) (b : Nat) (byt : Value) : Prop :=
  ∃ bs, Imm j b ∧ CallBytes env "data" z y bs ∧
    bs[b]? = some (.case "%" (.tuple [byt]))

/-- **`Step_read/memory.init-succ`, characterised exactly.**  Only premise:
`else`.  So, like `memory.fill-succ`, it fires on every configuration of its
shape — zero-length and out-of-bounds ones included — provided only that the
byte it copies is actually there. -/
theorem ruleFires_memoryInitSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryInitSuccRule ↔
      ∃ z atv i j mn x y a b k ma byt w,
        v = readV z
            [constV atv i, constV Execution.i32V j,
              constV Execution.i32V (.case "%" (.tuple [.num mn])),
              .case "MEMORY.INIT" (.tuple [x, y])]
            [constV atv i, constV Execution.i32V (.case "%" (.tuple [byt])),
              store8V x ma,
              constV atv (.case "%" (.tuple [.num (.natN (a + 1))])),
              constV Execution.i32V (.case "%" (.tuple [.num (.natN (b + 1))])),
              constV Execution.i32V (.case "%" (.tuple [w])),
              .case "MEMORY.INIT" (.tuple [x, y])] ∧
        Imm i a ∧ DataByteAt env z y j b byt ∧
        Num.cvt .intT mn = some (.intN k) ∧ AsInt w (k - 1) ∧
        ExecNumeric.Applies env "memarg0" [] ma := by
  unfold memoryInitSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨atv, i, j, n, x, y, rfl, rfl⟩ := matchExps_memoryInitLhs_iff.1 hvs
    obtain rfl := ExecRef.premsHold_else_iff.1 hp
    obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, u₇, σ₁, σ₂, σ₃, σ₄, σ₅, σ₆, rfl,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := matchExps_seven_iff.1 hws
    rw [matchExp_constBound_iff (a := atv) (c := i) (by simp) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨b₂, rfl, hb₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨b₂s, rfl, hb₂s⟩ := Validation.matchExp_tup_iff.1 hb₂
    obtain ⟨t₂, p₂, π₂, rfl, ht₂, hp₂⟩ := matchExps_two_iff.1 hb₂s
    rw [matchExp_caseNil_iff] at ht₂
    obtain ⟨rfl, rfl⟩ := ht₂
    obtain ⟨p₂s, rfl, hp₂s⟩ := Validation.matchExp_case_iff.1 hp₂
    obtain ⟨p₂t, rfl, hp₂t⟩ := Validation.matchExp_tup_iff.1 hp₂s
    obtain ⟨byt, rfl, hbyt⟩ := matchExps_one_iff.1 hp₂t
    rw [matchExp_projE0_iff, matchExp_uncaseE_iff, ExecDefault.matchExp_idxE_iff] at hbyt
    obtain ⟨hidx, rfl⟩ := hbyt
    obtain ⟨dw, bj, hdw, hbj, hsel⟩ := evalExp_idxE_iff.1 hidx
    rw [evalExp_callBytes_iff (zv := z) (xv := y) (evalExp_varE_iff.2 (by simp))
      (evalExp_varE_iff.2 (by simp)) rfl] at hdw
    rw [evalExp_imm_iff (c := j) (by simp)] at hbj
    obtain ⟨dbs, rfl, hdsel⟩ := idx?_eq_some_iff.1 hsel
    obtain ⟨b₃, rfl, hb₃⟩ := Validation.matchExp_case_iff.1 h₃
    obtain ⟨b₃s, rfl, hb₃s⟩ := Validation.matchExp_tup_iff.1 hb₃
    obtain ⟨t₃, o₃, x₃, m₃, α, β, γ, rfl, ht₃, ho₃, hx₃, hm₃⟩ := matchExps_four_iff.1 hb₃s
    rw [matchExp_caseNil_iff] at ht₃
    obtain ⟨rfl, rfl⟩ := ht₃
    obtain ⟨o₃', rfl, ho₃'⟩ := Validation.matchExp_optSome_iff.1 ho₃
    obtain ⟨o₃a, rfl, ho₃a⟩ := Validation.matchExp_case_iff.1 ho₃'
    obtain ⟨o₃b, rfl, ho₃b⟩ := Validation.matchExp_tup_iff.1 ho₃a
    obtain ⟨o₃c, rfl, ho₃c⟩ := matchExps_one_iff.1 ho₃b
    obtain ⟨o₃d, rfl, ho₃d⟩ := Validation.matchExp_case_iff.1 ho₃c
    obtain ⟨o₃e, rfl, ho₃e⟩ := Validation.matchExp_tup_iff.1 ho₃d
    obtain ⟨o₃f, rfl, ho₃f⟩ := matchExps_one_iff.1 ho₃e
    rw [ExecRef.matchExp_numE_iff] at ho₃f
    obtain ⟨rfl, rfl⟩ := ho₃f
    rw [matchExp_boundVar_iff (w := x) (by simp)] at hx₃
    obtain ⟨heqx₃, rfl⟩ := hx₃
    subst x₃
    obtain ⟨hma, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm₃
    obtain ⟨b₄, rfl, hb₄⟩ := Validation.matchExp_case_iff.1 h₄
    obtain ⟨b₄s, rfl, hb₄s⟩ := Validation.matchExp_tup_iff.1 hb₄
    obtain ⟨a₄, p₄, δ, rfl, ha₄, hp₄⟩ := matchExps_two_iff.1 hb₄s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := atv) (by simp)] at ha₄
    obtain ⟨heqa₄, rfl⟩ := ha₄
    subst a₄
    obtain ⟨p₄s, rfl, hp₄s⟩ := Validation.matchExp_case_iff.1 hp₄
    obtain ⟨p₄t, rfl, hp₄t⟩ := Validation.matchExp_tup_iff.1 hp₄s
    obtain ⟨s₄, rfl, hs₄⟩ := matchExps_one_iff.1 hp₄t
    rw [matchExp_binE_iff, evalExp_succE_iff] at hs₄
    obtain ⟨⟨a, ha, rfl⟩, rfl⟩ := hs₄
    rw [evalExp_imm_iff (c := i) (by simp)] at ha
    obtain ⟨b₅, rfl, hb₅⟩ := Validation.matchExp_case_iff.1 h₅
    obtain ⟨b₅s, rfl, hb₅s⟩ := Validation.matchExp_tup_iff.1 hb₅
    obtain ⟨t₅, p₅, ε, rfl, ht₅, hp₅⟩ := matchExps_two_iff.1 hb₅s
    rw [matchExp_caseNil_iff] at ht₅
    obtain ⟨rfl, rfl⟩ := ht₅
    obtain ⟨p₅s, rfl, hp₅s⟩ := Validation.matchExp_case_iff.1 hp₅
    obtain ⟨p₅t, rfl, hp₅t⟩ := Validation.matchExp_tup_iff.1 hp₅s
    obtain ⟨s₅, rfl, hs₅⟩ := matchExps_one_iff.1 hp₅t
    rw [matchExp_binE_iff, evalExp_succE_iff] at hs₅
    obtain ⟨⟨bb, hbb, rfl⟩, rfl⟩ := hs₅
    rw [evalExp_imm_iff (c := j) (by simp)] at hbb
    obtain ⟨b₆, rfl, hb₆⟩ := Validation.matchExp_case_iff.1 h₆
    obtain ⟨b₆s, rfl, hb₆s⟩ := Validation.matchExp_tup_iff.1 hb₆
    obtain ⟨t₆, p₆, ζ, rfl, ht₆, hp₆⟩ := matchExps_two_iff.1 hb₆s
    rw [matchExp_caseNil_iff] at ht₆
    obtain ⟨rfl, rfl⟩ := ht₆
    obtain ⟨p₆s, rfl, hp₆s⟩ := Validation.matchExp_case_iff.1 hp₆
    obtain ⟨p₆t, rfl, hp₆t⟩ := Validation.matchExp_tup_iff.1 hp₆s
    obtain ⟨s₆, rfl, hs₆⟩ := matchExps_one_iff.1 hp₆t
    rw [matchExp_cvtE_iff] at hs₆
    obtain ⟨mw, mw', rfl, hcw, hbw⟩ := hs₆
    rw [matchExp_binE_iff, evalExp_predE_iff] at hbw
    obtain ⟨⟨mnn, kk, hmnn, hck, rfl⟩, rfl⟩ := hbw
    rw [evalExp_varE_iff] at hmnn
    simp at hmnn
    obtain ⟨b₇, rfl, hb₇⟩ := Validation.matchExp_case_iff.1 h₇
    obtain ⟨b₇s, rfl, hb₇s⟩ := Validation.matchExp_tup_iff.1 hb₇
    obtain ⟨x₇, y₇, η, rfl, hx₇, hy₇⟩ := matchExps_two_iff.1 hb₇s
    rw [matchExp_boundVar_iff (w := x) (by simp)] at hx₇
    obtain ⟨heqx₇, rfl⟩ := hx₇
    subst x₇
    rw [matchExp_boundVar_iff (w := y) (by simp)] at hy₇
    obtain ⟨heqy₇, rfl⟩ := hy₇
    subst y₇
    subst hmnn
    obtain rfl : bj = bb := Imm.unique hbj hbb
    exact ⟨z, atv, i, j, mnn, x, y, a, _, kk, m₃, byt, .num mw, rfl, ha,
      ⟨dbs, hbb, hdw, hdsel⟩, hck, ⟨mw, rfl, hcw⟩,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma⟩
  · rintro ⟨z, atv, i, j, mn, x, y, a, b, k, ma, byt, w, rfl, ha,
      ⟨dbs, hj, hcb, hdsel⟩, hck, ⟨mw, rfl, hcw⟩, hma⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryInitLhs_iff.2 ⟨atv, i, j, .num mn, x, y, rfl, rfl⟩,
      matchExps_seven_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_constBound_iff (a := atv) (c := i) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_projE0_iff.2 (matchExp_uncaseE_iff.2
                      (ExecDefault.matchExp_idxE_iff.2 ⟨evalExp_idxE_iff.2
                        ⟨.list dbs, b,
                          (evalExp_callBytes_iff (zv := z) (xv := y)
                            (evalExp_varE_iff.2 (by simp))
                            (evalExp_varE_iff.2 (by simp)) rfl).2 hcb,
                          (evalExp_imm_iff (c := j) (by simp)).2 hj,
                          idx?_eq_some_iff.2 ⟨dbs, rfl, hdsel⟩⟩, rfl⟩))⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma,
                  rfl⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := atv) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_binE_iff.2 ⟨evalExp_succE_iff.2
                      ⟨a, (evalExp_imm_iff (c := i) (by simp)).2 ha, rfl⟩,
                      rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_binE_iff.2 ⟨evalExp_succE_iff.2
                      ⟨b, (evalExp_imm_iff (c := j) (by simp)).2 hj, rfl⟩,
                      rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_cvtE_iff.2 ⟨mw, .intN (k - 1), rfl, hcw,
                      matchExp_binE_iff.2 ⟨evalExp_predE_iff.2
                        ⟨mn, k, evalExp_varE_iff.2 (by simp), hck, rfl⟩,
                        rfl⟩⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_boundVar_iff (w := x) (by simp)).2 ⟨rfl, rfl⟩,
              (matchExp_boundVar_iff (w := y) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩

/-- **`Step_read/memory.copy-le`, characterised exactly.**  The guard is
`i_1!%.0 <= i_2!%.0`: the forward copy.  The two `$memarg0()` calls are
matched independently — nothing in the rule forces them to agree. -/
theorem ruleFires_memoryCopyLe_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryCopyLeRule ↔
      ∃ z at₁ i₁ at₂ i₂ at' mn x₁ x₂ a₁ a₂ k ma₁ ma₂ w,
        v = readV z
            [constV at₁ i₁, constV at₂ i₂,
              constV at' (.case "%" (.tuple [.num mn])),
              .case "MEMORY.COPY" (.tuple [x₁, x₂])]
            [constV at₁ i₁, constV at₂ i₂, loadU8V x₂ ma₁, store8V x₁ ma₂,
              constV at₁ (.case "%" (.tuple [.num (.natN (a₁ + 1))])),
              constV at₂ (.case "%" (.tuple [.num (.natN (a₂ + 1))])),
              constV at' (.case "%" (.tuple [w])),
              .case "MEMORY.COPY" (.tuple [x₁, x₂])] ∧
        Imm i₁ a₁ ∧ Imm i₂ a₂ ∧ a₁ ≤ a₂ ∧
        Num.cvt .intT mn = some (.intN k) ∧ AsInt w (k - 1) ∧
        ExecNumeric.Applies env "memarg0" [] ma₁ ∧
        ExecNumeric.Applies env "memarg0" [] ma₂ := by
  unfold memoryCopyLeRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, rfl⟩ :=
      matchExps_memoryCopyLhs_iff.1 hvs
    obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, σ₁, σ₂, σ₃, σ₄, σ₅, σ₆, σ₇, rfl,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := matchExps_eight_iff.1 hws
    rw [matchExp_constBound_iff (a := at₁) (c := i₁) (by simp) (by simp)] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    rw [matchExp_constBound_iff (a := at₂) (c := i₂) (by simp) (by simp)] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨b₃, rfl, hb₃⟩ := Validation.matchExp_case_iff.1 h₃
    obtain ⟨b₃s, rfl, hb₃s⟩ := Validation.matchExp_tup_iff.1 hb₃
    obtain ⟨t₃, o₃, y₃, m₃, α, β, γ, rfl, ht₃, ho₃, hy₃, hm₃⟩ :=
      matchExps_four_iff.1 hb₃s
    rw [matchExp_caseNil_iff] at ht₃
    obtain ⟨rfl, rfl⟩ := ht₃
    obtain ⟨o₃a, rfl, ho₃a⟩ := Validation.matchExp_optSome_iff.1 ho₃
    obtain ⟨o₃b, rfl, ho₃b⟩ := Validation.matchExp_case_iff.1 ho₃a
    obtain ⟨o₃c, rfl, ho₃c⟩ := Validation.matchExp_tup_iff.1 ho₃b
    obtain ⟨o₃d, o₃e, θ, rfl, ho₃d, ho₃e⟩ := matchExps_two_iff.1 ho₃c
    obtain ⟨o₃f, rfl, ho₃f⟩ := Validation.matchExp_case_iff.1 ho₃d
    obtain ⟨o₃g, rfl, ho₃g⟩ := Validation.matchExp_tup_iff.1 ho₃f
    obtain ⟨o₃h, rfl, ho₃h⟩ := matchExps_one_iff.1 ho₃g
    rw [ExecRef.matchExp_numE_iff] at ho₃h
    obtain ⟨rfl, rfl⟩ := ho₃h
    rw [matchExp_caseNil_iff] at ho₃e
    obtain ⟨rfl, rfl⟩ := ho₃e
    rw [matchExp_boundVar_iff (w := x₂) (by simp)] at hy₃
    obtain ⟨heqy₃, rfl⟩ := hy₃
    subst y₃
    obtain ⟨hma₁, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm₃
    obtain ⟨b₄, rfl, hb₄⟩ := Validation.matchExp_case_iff.1 h₄
    obtain ⟨b₄s, rfl, hb₄s⟩ := Validation.matchExp_tup_iff.1 hb₄
    obtain ⟨t₄, o₄, y₄, m₄, α₄, β₄, γ₄, rfl, ht₄, ho₄, hy₄, hm₄⟩ :=
      matchExps_four_iff.1 hb₄s
    rw [matchExp_caseNil_iff] at ht₄
    obtain ⟨rfl, rfl⟩ := ht₄
    obtain ⟨o₄a, rfl, ho₄a⟩ := Validation.matchExp_optSome_iff.1 ho₄
    obtain ⟨o₄b, rfl, ho₄b⟩ := Validation.matchExp_case_iff.1 ho₄a
    obtain ⟨o₄c, rfl, ho₄c⟩ := Validation.matchExp_tup_iff.1 ho₄b
    obtain ⟨o₄d, rfl, ho₄d⟩ := matchExps_one_iff.1 ho₄c
    obtain ⟨o₄e, rfl, ho₄e⟩ := Validation.matchExp_case_iff.1 ho₄d
    obtain ⟨o₄f, rfl, ho₄f⟩ := Validation.matchExp_tup_iff.1 ho₄e
    obtain ⟨o₄g, rfl, ho₄g⟩ := matchExps_one_iff.1 ho₄f
    rw [ExecRef.matchExp_numE_iff] at ho₄g
    obtain ⟨rfl, rfl⟩ := ho₄g
    rw [matchExp_boundVar_iff (w := x₁) (by simp)] at hy₄
    obtain ⟨heqy₄, rfl⟩ := hy₄
    subst y₄
    obtain ⟨hma₂, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm₄
    obtain ⟨b₅, rfl, hb₅⟩ := Validation.matchExp_case_iff.1 h₅
    obtain ⟨b₅s, rfl, hb₅s⟩ := Validation.matchExp_tup_iff.1 hb₅
    obtain ⟨a₅, p₅, δ₅, rfl, ha₅, hp₅⟩ := matchExps_two_iff.1 hb₅s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at₁) (by simp)] at ha₅
    obtain ⟨heqa₅, rfl⟩ := ha₅
    subst a₅
    obtain ⟨p₅s, rfl, hp₅s⟩ := Validation.matchExp_case_iff.1 hp₅
    obtain ⟨p₅t, rfl, hp₅t⟩ := Validation.matchExp_tup_iff.1 hp₅s
    obtain ⟨s₅, rfl, hs₅⟩ := matchExps_one_iff.1 hp₅t
    rw [matchExp_binE_iff, evalExp_succE_iff] at hs₅
    obtain ⟨⟨a₁, ha₁, rfl⟩, rfl⟩ := hs₅
    obtain ⟨b₆, rfl, hb₆⟩ := Validation.matchExp_case_iff.1 h₆
    obtain ⟨b₆s, rfl, hb₆s⟩ := Validation.matchExp_tup_iff.1 hb₆
    obtain ⟨a₆, p₆, δ₆, rfl, ha₆, hp₆⟩ := matchExps_two_iff.1 hb₆s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at₂) (by simp)] at ha₆
    obtain ⟨heqa₆, rfl⟩ := ha₆
    subst a₆
    obtain ⟨p₆s, rfl, hp₆s⟩ := Validation.matchExp_case_iff.1 hp₆
    obtain ⟨p₆t, rfl, hp₆t⟩ := Validation.matchExp_tup_iff.1 hp₆s
    obtain ⟨s₆, rfl, hs₆⟩ := matchExps_one_iff.1 hp₆t
    rw [matchExp_binE_iff, evalExp_succE_iff] at hs₆
    obtain ⟨⟨a₂, ha₂, rfl⟩, rfl⟩ := hs₆
    obtain ⟨b₇, rfl, hb₇⟩ := Validation.matchExp_case_iff.1 h₇
    obtain ⟨b₇s, rfl, hb₇s⟩ := Validation.matchExp_tup_iff.1 hb₇
    obtain ⟨a₇, p₇, δ₇, rfl, ha₇, hp₇⟩ := matchExps_two_iff.1 hb₇s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at') (by simp)] at ha₇
    obtain ⟨heqa₇, rfl⟩ := ha₇
    subst a₇
    obtain ⟨p₇s, rfl, hp₇s⟩ := Validation.matchExp_case_iff.1 hp₇
    obtain ⟨p₇t, rfl, hp₇t⟩ := Validation.matchExp_tup_iff.1 hp₇s
    obtain ⟨s₇, rfl, hs₇⟩ := matchExps_one_iff.1 hp₇t
    rw [matchExp_cvtE_iff] at hs₇
    obtain ⟨mw, mw', rfl, hcw, hbw⟩ := hs₇
    rw [matchExp_binE_iff, evalExp_predE_iff] at hbw
    obtain ⟨⟨mnn, kk, hmnn, hck, rfl⟩, rfl⟩ := hbw
    rw [evalExp_varE_iff] at hmnn
    simp at hmnn
    obtain ⟨b₈, rfl, hb₈⟩ := Validation.matchExp_case_iff.1 h₈
    obtain ⟨b₈s, rfl, hb₈s⟩ := Validation.matchExp_tup_iff.1 hb₈
    obtain ⟨y₈, z₈, η, rfl, hy₈, hz₈⟩ := matchExps_two_iff.1 hb₈s
    rw [matchExp_boundVar_iff (w := x₁) (by simp)] at hy₈
    obtain ⟨heqy₈, rfl⟩ := hy₈
    subst y₈
    rw [matchExp_boundVar_iff (w := x₂) (by simp)] at hz₈
    obtain ⟨heqz₈, rfl⟩ := hz₈
    subst z₈
    subst hmnn
    obtain ⟨-, hev⟩ := ExecRef.premsHold_elseIf_iff.1 hp
    obtain ⟨c₁, c₂, hc₁, hc₂, hcmp⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_imm_iff (c := i₁) (by simp)] at hc₁ ha₁
    rw [evalExp_imm_iff (c := i₂) (by simp)] at hc₂ ha₂
    obtain ⟨us₁, hs₁⟩ := ha₁
    obtain ⟨us₂, hs₂⟩ := ha₂
    obtain ⟨vs₁, hv₁⟩ := hc₁
    obtain ⟨vs₂, hv₂⟩ := hc₂
    rw [hs₁] at hv₁
    rw [hs₂] at hv₂
    obtain rfl : c₁ = .num (.natN a₁) := by
      injection hv₁ with _ hv₁
      injection hv₁ with hv₁
      simpa using (List.cons.inj hv₁).1.symm
    obtain rfl : c₂ = .num (.natN a₂) := by
      injection hv₂ with _ hv₂
      injection hv₂ with hv₂
      simpa using (List.cons.inj hv₂).1.symm
    exact ⟨z, at₁, i₁, at₂, i₂, at', mnn, x₁, x₂, a₁, a₂, kk, m₃, m₄, .num mw, rfl,
      ⟨us₁, hs₁⟩, ⟨us₂, hs₂⟩, cmpValues_le_natN_iff.1 hcmp, hck, ⟨mw, rfl, hcw⟩,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma₁,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma₂⟩
  · rintro ⟨z, at₁, i₁, at₂, i₂, at', mn, x₁, x₂, a₁, a₂, k, ma₁, ma₂, w, rfl,
      hi₁, hi₂, hle, hck, ⟨mw, rfl, hcw⟩, hma₁, hma₂⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryCopyLhs_iff.2
        ⟨at₁, i₁, at₂, i₂, at', .num mn, x₁, x₂, rfl, rfl⟩,
      matchExps_eight_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_constBound_iff (a := at₁) (c := i₁) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
        (matchExp_constBound_iff (a := at₂) (c := i₂) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_two_iff.2 ⟨_, _, _, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
                      matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x₂) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma₁,
                  rfl⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x₁) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma₂,
                  rfl⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at₁) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_binE_iff.2 ⟨evalExp_succE_iff.2
                      ⟨a₁, (evalExp_imm_iff (c := i₁) (by simp)).2 hi₁, rfl⟩,
                      rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at₂) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_binE_iff.2 ⟨evalExp_succE_iff.2
                      ⟨a₂, (evalExp_imm_iff (c := i₂) (by simp)).2 hi₂, rfl⟩,
                      rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at') (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_cvtE_iff.2 ⟨mw, .intN (k - 1), rfl, hcw,
                      matchExp_binE_iff.2 ⟨evalExp_predE_iff.2
                        ⟨mn, k, evalExp_varE_iff.2 (by simp), hck, rfl⟩,
                        rfl⟩⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_boundVar_iff (w := x₁) (by simp)).2 ⟨rfl, rfl⟩,
              (matchExp_boundVar_iff (w := x₂) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩,
      ExecRef.premsHold_elseIf_iff.2 ⟨rfl,
        evalExp_cmpE_iff.2 ⟨.num (.natN a₁), .num (.natN a₂),
          (evalExp_imm_iff (c := i₁) (by simp)).2 hi₁,
          (evalExp_imm_iff (c := i₂) (by simp)).2 hi₂,
          cmpValues_le_natN_iff.2 hle⟩⟩⟩

/-- `v` is `(% m …)` for an arbitrary numeral — the weaker `Imm` that
`memory.copy-gt` needs, since nothing there forces a `nat`. -/
def ImmNum (v : Value) (m : Num) : Prop :=
  ∃ us, v = .case "%" (.tuple (.num m :: us))

/-- `((e + n : int) - 1 : nat)` as a *pattern*: the slot `w` reads back,
through `int`, to one less than `e + n`. -/
def PredOfSum (m mn : Num) (w : Value) : Prop :=
  ∃ s k, Num.bin .addOp m mn = some s ∧ Num.cvt .intT s = some (.intN k) ∧
    AsInt w (k - 1)

/-- `e₁ + e₂` at `nat`, with no constraint on the result's constructor. -/
theorem evalExp_addE_iff {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {m : Num} :
    EvalExp env ρ (.binE .addOp (.numT .natT) e₁ e₂) (.num m) ↔
      ∃ m₁ m₂, EvalExp env ρ e₁ (.num m₁) ∧ EvalExp env ρ e₂ (.num m₂) ∧
        Num.bin .addOp m₁ m₂ = some m := by
  rw [evalExp_binE_iff]
  constructor
  · rintro ⟨v₁, hv₁, hs⟩
    rw [boolShort_add] at hs
    simp only [reduceCtorEq, false_or, true_and] at hs
    obtain ⟨v₂, hv₂, hbv⟩ := hs
    obtain ⟨m₁, m₂, rfl, rfl, hb⟩ := binValues_eq_num_iff.1 hbv
    exact ⟨m₁, m₂, hv₁, hv₂, hb⟩
  · rintro ⟨m₁, m₂, h₁, h₂, hb⟩
    exact ⟨_, h₁, Or.inr ⟨boolShort_add _, _, h₂,
      binValues_eq_num_iff.2 ⟨_, _, rfl, rfl, hb⟩⟩⟩

/-- `((y!%.0 + n : int) - 1 : nat)` as a pattern, inverted. -/
theorem matchExp_predOfSum_iff {env : Env} {ρ ρ' : VarEnv} {y : IL.Id}
    {iv nv w : Value} (hy : ρ.findVal? y = some iv) (hn : ρ.findVal? "n" = some nv) :
    MatchExp env ρ
      (.cvtE (.binE .subOp (.numT .intT)
        (.cvtE (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE y) "%") 0)
          (.varE "n")) .natT .intT)
        (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) w ρ' ↔
      ∃ m mn, ImmNum iv m ∧ nv = .num mn ∧ PredOfSum m mn w ∧ ρ' = ρ := by
  rw [matchExp_cvtE_iff]
  constructor
  · rintro ⟨mm, mm', rfl, hcm, hb⟩
    rw [matchExp_binE_iff, evalExp_predE_iff] at hb
    obtain ⟨⟨madd, kk, hadd, hck, rfl⟩, rfl⟩ := hb
    rw [evalExp_addE_iff] at hadd
    obtain ⟨m₁, m₂, h₁, h₂, hbn⟩ := hadd
    rw [evalExp_imm_iff hy] at h₁
    rw [evalExp_varE_iff, hn] at h₂
    exact ⟨m₁, m₂, h₁, Option.some.inj h₂, ⟨madd, kk, hbn, hck, ⟨mm, rfl, hcm⟩⟩, rfl⟩
  · rintro ⟨m, mn, him, rfl, ⟨s, k, hbn, hck, ⟨mm, rfl, hcm⟩⟩, rfl⟩
    exact ⟨mm, .intN (k - 1), rfl, hcm,
      matchExp_binE_iff.2 ⟨evalExp_predE_iff.2 ⟨s, k,
        evalExp_addE_iff.2 ⟨m, mn, (evalExp_imm_iff hy).2 him,
          evalExp_varE_iff.2 hn, hbn⟩, hck, rfl⟩, rfl⟩⟩

/-- **`Step_read/memory.copy-gt`, characterised exactly.**  Its only premise
is `else`, so — exactly as with `memory.fill-succ` and `memory.init-succ` —
it fires on *every* configuration of its shape, including the ones
`memory.copy-oob`, `memory.copy-zero` and `memory.copy-le` claim. -/
theorem ruleFires_memoryCopyGt_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v memoryCopyGtRule ↔
      ∃ z at₁ i₁ at₂ i₂ at' mn x₁ x₂ m₁ m₂ k ma₁ ma₂ w₁ w₂ w,
        v = readV z
            [constV at₁ i₁, constV at₂ i₂,
              constV at' (.case "%" (.tuple [.num mn])),
              .case "MEMORY.COPY" (.tuple [x₁, x₂])]
            [constV at₁ (.case "%" (.tuple [w₁])),
              constV at₂ (.case "%" (.tuple [w₂])),
              loadU8V x₂ ma₁, store8V x₁ ma₂,
              constV at₁ i₁, constV at₂ i₂,
              constV at' (.case "%" (.tuple [w])),
              .case "MEMORY.COPY" (.tuple [x₁, x₂])] ∧
        ImmNum i₁ m₁ ∧ ImmNum i₂ m₂ ∧
        PredOfSum m₁ mn w₁ ∧ PredOfSum m₂ mn w₂ ∧
        Num.cvt .intT mn = some (.intN k) ∧ AsInt w (k - 1) ∧
        ExecNumeric.Applies env "memarg0" [] ma₁ ∧
        ExecNumeric.Applies env "memarg0" [] ma₂ := by
  unfold memoryCopyGtRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨at₁, i₁, at₂, i₂, at', n, x₁, x₂, rfl, rfl⟩ :=
      matchExps_memoryCopyLhs_iff.1 hvs
    obtain rfl := ExecRef.premsHold_else_iff.1 hp
    obtain ⟨u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈, σ₁, σ₂, σ₃, σ₄, σ₅, σ₆, σ₇, rfl,
      h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := matchExps_eight_iff.1 hws
    obtain ⟨b₁, rfl, hb₁⟩ := Validation.matchExp_case_iff.1 h₁
    obtain ⟨b₁s, rfl, hb₁s⟩ := Validation.matchExp_tup_iff.1 hb₁
    obtain ⟨a₁v, p₁, δ₁, rfl, ha₁v, hp₁⟩ := matchExps_two_iff.1 hb₁s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at₁) (by simp)] at ha₁v
    obtain ⟨heqa₁, rfl⟩ := ha₁v
    subst a₁v
    obtain ⟨p₁s, rfl, hp₁s⟩ := Validation.matchExp_case_iff.1 hp₁
    obtain ⟨p₁t, rfl, hp₁t⟩ := Validation.matchExp_tup_iff.1 hp₁s
    obtain ⟨w₁, rfl, hw₁⟩ := matchExps_one_iff.1 hp₁t
    rw [matchExp_predOfSum_iff (iv := i₁) (nv := n) (by simp) (by simp)] at hw₁
    obtain ⟨m₁, mn₁, him₁, hn₁, hps₁, rfl⟩ := hw₁
    obtain ⟨b₂, rfl, hb₂⟩ := Validation.matchExp_case_iff.1 h₂
    obtain ⟨b₂s, rfl, hb₂s⟩ := Validation.matchExp_tup_iff.1 hb₂
    obtain ⟨a₂v, p₂, δ₂, rfl, ha₂v, hp₂⟩ := matchExps_two_iff.1 hb₂s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at₂) (by simp)] at ha₂v
    obtain ⟨heqa₂, rfl⟩ := ha₂v
    subst a₂v
    obtain ⟨p₂s, rfl, hp₂s⟩ := Validation.matchExp_case_iff.1 hp₂
    obtain ⟨p₂t, rfl, hp₂t⟩ := Validation.matchExp_tup_iff.1 hp₂s
    obtain ⟨w₂, rfl, hw₂⟩ := matchExps_one_iff.1 hp₂t
    rw [matchExp_predOfSum_iff (iv := i₂) (nv := n) (by simp) (by simp)] at hw₂
    obtain ⟨m₂, mn₂, him₂, hn₂, hps₂, rfl⟩ := hw₂
    obtain ⟨b₃, rfl, hb₃⟩ := Validation.matchExp_case_iff.1 h₃
    obtain ⟨b₃s, rfl, hb₃s⟩ := Validation.matchExp_tup_iff.1 hb₃
    obtain ⟨t₃, o₃, y₃, m₃, α, β, γ, rfl, ht₃, ho₃, hy₃, hm₃⟩ :=
      matchExps_four_iff.1 hb₃s
    rw [matchExp_caseNil_iff] at ht₃
    obtain ⟨rfl, rfl⟩ := ht₃
    obtain ⟨o₃a, rfl, ho₃a⟩ := Validation.matchExp_optSome_iff.1 ho₃
    obtain ⟨o₃b, rfl, ho₃b⟩ := Validation.matchExp_case_iff.1 ho₃a
    obtain ⟨o₃c, rfl, ho₃c⟩ := Validation.matchExp_tup_iff.1 ho₃b
    obtain ⟨o₃d, o₃e, θ, rfl, ho₃d, ho₃e⟩ := matchExps_two_iff.1 ho₃c
    obtain ⟨o₃f, rfl, ho₃f⟩ := Validation.matchExp_case_iff.1 ho₃d
    obtain ⟨o₃g, rfl, ho₃g⟩ := Validation.matchExp_tup_iff.1 ho₃f
    obtain ⟨o₃h, rfl, ho₃h⟩ := matchExps_one_iff.1 ho₃g
    rw [ExecRef.matchExp_numE_iff] at ho₃h
    obtain ⟨rfl, rfl⟩ := ho₃h
    rw [matchExp_caseNil_iff] at ho₃e
    obtain ⟨rfl, rfl⟩ := ho₃e
    rw [matchExp_boundVar_iff (w := x₂) (by simp)] at hy₃
    obtain ⟨heqy₃, rfl⟩ := hy₃
    subst y₃
    obtain ⟨hma₁, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm₃
    obtain ⟨b₄, rfl, hb₄⟩ := Validation.matchExp_case_iff.1 h₄
    obtain ⟨b₄s, rfl, hb₄s⟩ := Validation.matchExp_tup_iff.1 hb₄
    obtain ⟨t₄, o₄, y₄, m₄, α₄, β₄, γ₄, rfl, ht₄, ho₄, hy₄, hm₄⟩ :=
      matchExps_four_iff.1 hb₄s
    rw [matchExp_caseNil_iff] at ht₄
    obtain ⟨rfl, rfl⟩ := ht₄
    obtain ⟨o₄a, rfl, ho₄a⟩ := Validation.matchExp_optSome_iff.1 ho₄
    obtain ⟨o₄b, rfl, ho₄b⟩ := Validation.matchExp_case_iff.1 ho₄a
    obtain ⟨o₄c, rfl, ho₄c⟩ := Validation.matchExp_tup_iff.1 ho₄b
    obtain ⟨o₄d, rfl, ho₄d⟩ := matchExps_one_iff.1 ho₄c
    obtain ⟨o₄e, rfl, ho₄e⟩ := Validation.matchExp_case_iff.1 ho₄d
    obtain ⟨o₄f, rfl, ho₄f⟩ := Validation.matchExp_tup_iff.1 ho₄e
    obtain ⟨o₄g, rfl, ho₄g⟩ := matchExps_one_iff.1 ho₄f
    rw [ExecRef.matchExp_numE_iff] at ho₄g
    obtain ⟨rfl, rfl⟩ := ho₄g
    rw [matchExp_boundVar_iff (w := x₁) (by simp)] at hy₄
    obtain ⟨heqy₄, rfl⟩ := hy₄
    subst y₄
    obtain ⟨hma₂, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm₄
    rw [matchExp_constBound_iff (a := at₁) (c := i₁) (by simp) (by simp)] at h₅
    obtain ⟨rfl, rfl⟩ := h₅
    rw [matchExp_constBound_iff (a := at₂) (c := i₂) (by simp) (by simp)] at h₆
    obtain ⟨rfl, rfl⟩ := h₆
    obtain ⟨b₇, rfl, hb₇⟩ := Validation.matchExp_case_iff.1 h₇
    obtain ⟨b₇s, rfl, hb₇s⟩ := Validation.matchExp_tup_iff.1 hb₇
    obtain ⟨a₇, p₇, δ₇, rfl, ha₇, hp₇⟩ := matchExps_two_iff.1 hb₇s
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff (w := at') (by simp)] at ha₇
    obtain ⟨heqa₇, rfl⟩ := ha₇
    subst a₇
    obtain ⟨p₇s, rfl, hp₇s⟩ := Validation.matchExp_case_iff.1 hp₇
    obtain ⟨p₇t, rfl, hp₇t⟩ := Validation.matchExp_tup_iff.1 hp₇s
    obtain ⟨s₇, rfl, hs₇⟩ := matchExps_one_iff.1 hp₇t
    rw [matchExp_cvtE_iff] at hs₇
    obtain ⟨mw, mw', rfl, hcw, hbw⟩ := hs₇
    rw [matchExp_binE_iff, evalExp_predE_iff] at hbw
    obtain ⟨⟨mnn, kk, hmnn, hck, rfl⟩, rfl⟩ := hbw
    rw [evalExp_varE_iff] at hmnn
    simp at hmnn
    obtain ⟨b₈, rfl, hb₈⟩ := Validation.matchExp_case_iff.1 h₈
    obtain ⟨b₈s, rfl, hb₈s⟩ := Validation.matchExp_tup_iff.1 hb₈
    obtain ⟨y₈, z₈, η, rfl, hy₈, hz₈⟩ := matchExps_two_iff.1 hb₈s
    rw [matchExp_boundVar_iff (w := x₁) (by simp)] at hy₈
    obtain ⟨heqy₈, rfl⟩ := hy₈
    subst y₈
    rw [matchExp_boundVar_iff (w := x₂) (by simp)] at hz₈
    obtain ⟨heqz₈, rfl⟩ := hz₈
    subst z₈
    subst hmnn
    obtain rfl : mnn = mn₁ := by simpa using hn₁
    obtain rfl : mnn = mn₂ := by simpa using hn₂
    exact ⟨z, at₁, i₁, at₂, i₂, at', _, x₁, x₂, m₁, m₂, kk, m₃, m₄, _, _, .num mw,
      rfl, him₁, him₂, hps₁, hps₂, hck, ⟨mw, rfl, hcw⟩,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma₁,
      (ExecNumeric.applies_iff_callDef rfl evalArgs_nil).2 hma₂⟩
  · rintro ⟨z, at₁, i₁, at₂, i₂, at', mn, x₁, x₂, m₁, m₂, k, ma₁, ma₂, w₁, w₂, w,
      rfl, him₁, him₂, hps₁, hps₂, hck, ⟨mw, rfl, hcw⟩, hma₁, hma₂⟩
    exact ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_memoryCopyLhs_iff.2
        ⟨at₁, i₁, at₂, i₂, at', .num mn, x₁, x₂, rfl, rfl⟩,
      matchExps_eight_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at₁) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    (matchExp_predOfSum_iff (iv := i₁) (nv := .num mn)
                      (by simp) (by simp)).2
                      ⟨m₁, mn, him₁, rfl, hps₁, rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at₂) (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    (matchExp_predOfSum_iff (iv := i₂) (nv := .num mn)
                      (by simp) (by simp)).2
                      ⟨m₂, mn, him₂, rfl, hps₂, rfl⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_two_iff.2 ⟨_, _, _, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩,
                      matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x₂) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma₁,
                  rfl⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_four_iff.2 ⟨_, _, _, _, _, _, _, rfl,
              matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_optSome_iff.2 ⟨_, rfl,
                Validation.matchExp_case_iff.2 ⟨_, rfl,
                  Validation.matchExp_tup_iff.2 ⟨_, rfl,
                    matchExps_one_iff.2 ⟨_, rfl,
                      Validation.matchExp_case_iff.2 ⟨_, rfl,
                        Validation.matchExp_tup_iff.2 ⟨_, rfl,
                          matchExps_one_iff.2 ⟨_, rfl,
                            ExecRef.matchExp_numE_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩,
              (matchExp_boundVar_iff (w := x₁) (by simp)).2 ⟨rfl, rfl⟩,
              ExecDefault.matchExp_callE_iff.2
                ⟨(ExecNumeric.applies_iff_callDef (ρ := _) rfl evalArgs_nil).1 hma₂,
                  rfl⟩⟩⟩⟩,
        (matchExp_constBound_iff (a := at₁) (c := i₁) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
        (matchExp_constBound_iff (a := at₂) (c := i₂) (by simp) (by simp)).2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              Validation.matchExp_sub_iff.2
                ((matchExp_boundVar_iff (w := at') (by simp)).2 ⟨rfl, rfl⟩),
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl,
                    matchExp_cvtE_iff.2 ⟨mw, .intN (k - 1), rfl, hcw,
                      matchExp_binE_iff.2 ⟨evalExp_predE_iff.2
                        ⟨mn, k, evalExp_varE_iff.2 (by simp), hck, rfl⟩,
                        rfl⟩⟩⟩⟩⟩⟩⟩⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_boundVar_iff (w := x₁) (by simp)).2 ⟨rfl, rfl⟩,
              (matchExp_boundVar_iff (w := x₂) (by simp)).2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩,
      ExecRef.premsHold_else_iff.2 rfl⟩

/-! ## `vload-pack-val`, the last rule that cannot fire

Its first premise is an **iterated** one, which is why it needed a detour:
`Sem/Eval.lean`'s `premIter` "returns the scope it was given" — binding
outwards from an iterated premise is not implemented, because `is_let_bound`
is identically false on the pinned corpus.  So whatever the iteration does,
the second premise is evaluated in the same scope, and it reads `Jnn`, which
nothing binds. -/

/-- `premRounds` returns the scope it was given. -/
theorem premRounds_scope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem}
    {xvs : List (IL.Id × Value)} {ido : Option IL.Id} {k : Nat}
    (h : premRounds n env ρ pr xvs ido k = .ok ρ') : ρ' = ρ := by
  cases n with
  | zero => simp [premRounds] at h
  | succ m =>
      simp only [premRounds, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨ds, -, -, w, -, heq⟩ := h
      exact (Validation.okInj heq).symm

/-- So does `premIter`: **an iterated premise binds nothing.** -/
theorem premIter_scope {n : Nat} {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {it : Iter}
    {ds : List Dom} (h : premIter n env ρ pr it ds = .ok ρ') : ρ' = ρ := by
  cases n with
  | zero => simp [premIter] at h
  | succ m =>
      cases it with
      | opt =>
          simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, -, -, os, -, h⟩ := h
          split at h
          · exact (Validation.okInj h).symm
          · split at h
            · simp only [Res.bind_eq_ok] at h
              obtain ⟨-, -, h⟩ := h
              exact (Validation.okInj h).symm
            · exact absurd h (by simp)
      | list =>
          simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, -, -, k, -, h⟩ := h
          exact premRounds_scope h
      | list1 =>
          simp only [premIter, Res.bind_eq_ok, Res.assert_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, -, -, k, -, -, h⟩ := h
          exact premRounds_scope h
      | listN e ido =>
          simp only [premIter, Res.bind_eq_ok, Res.ofOption_eq_ok] at h
          obtain ⟨xvs, -, kv, -, k, -, h⟩ := h
          exact premRounds_scope h

/-- An iterated premise leaves the scope alone. -/
theorem premHolds_iterPr_scope {env : Env} {ρ ρ' : VarEnv} {pr : Prem} {it : Iter}
    {ds : List Dom} (h : PremHolds env ρ (.iterPr pr (.mk it ds)) ρ') : ρ' = ρ := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [premHolds] at hn
  | succ m => exact premIter_scope (by simpa only [premHolds] using hn)

/-- **`Step_read/vload-pack-val` fires at nothing.**  Its second premise
reads `$jsizenn(Jnn)` and `$inv_lanes_((Jnn <: lanetype) X M, …)`, and `Jnn`
is bound by nothing; the iterated first premise cannot bind it either. -/
theorem not_ruleFires_vloadPackVal {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v vloadPackValRule := by
  unfold vloadPackValRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, vs, ws, σ, rfl, hvs, hws⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨atv, i, kk, mm, sx, x, ao, rfl, rfl⟩ := matchExps_vloadPackLhs_iff.1 hvs
  obtain ⟨r, rfl, hr⟩ := matchExps_one_iff.1 hws
  obtain ⟨rv, rfl, hrv⟩ := Validation.matchExp_case_iff.1 hr
  obtain ⟨rvs, rfl, hrvs⟩ := Validation.matchExp_tup_iff.1 hrv
  obtain ⟨tv, c, τ, rfl, htv, hc⟩ := matchExps_two_iff.1 hrvs
  rw [matchExp_caseNil_iff] at htv
  obtain ⟨rfl, rfl⟩ := htv
  rw [matchExp_freshVar_iff (by simp)] at hc
  subst hc
  obtain ⟨κ, hpr₁, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain rfl := premHolds_iterPr_scope hpr₁
  obtain ⟨κ₂, hpr₂, -⟩ := Validation.premsHold_cons_iff.1 hrest
  obtain ⟨-, hev⟩ := Validation.premHolds_if_iff.1 hpr₂
  rw [evalExp_binE_iff] at hev
  obtain ⟨v₁, hv₁, -⟩ := hev
  obtain ⟨u₁, u₂, -, hu₂, -⟩ := evalExp_cmpE_iff.1 hv₁
  obtain ⟨wsv, ps, t, cs, hargs, -, -⟩ :=
    ExecNumeric.callDef_iff.1 (evalExp_callE_iff.1 hu₂)
  obtain ⟨_, _, rfl, harg, -⟩ := evalArgs_expA_cons_iff.1 hargs
  obtain ⟨aw, haw, rfl⟩ := evalExp_caseE_iff.1 harg
  obtain ⟨aws, haws, rfl⟩ := evalExp_tupE_iff.1 haw
  obtain ⟨p, ps', rfl, hp₁, hq⟩ := Validation.evalExps_cons_iff.1 haws
  rw [evalExp_subE_iff, evalExp_varE_iff] at hp₁
  simp at hp₁

end Silmaril.SpecTec.Equiv.ExecReadMemory
