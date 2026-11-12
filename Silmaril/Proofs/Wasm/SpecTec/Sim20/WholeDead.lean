module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTyping

/-!
# The `Step_pure` and `Step_read` rules that `Step` cannot use

`Step/pure` and `Step/read` of the wasm-2.0 script give both sides of their premise the type
`instr*` (`inv_pure20`, `inv_read20`). A `Step_pure` or `Step_read` rule whose left-hand side
forces an administrative constructor (`LABEL_`, `FRAME_`, `TRAP`, `CALL_ADDR`), or whose
right-hand side forces one (`TRAP`, `LABEL_`, `FRAME_`, `CALL_ADDR`, `REF.FUNC_ADDR`), can
therefore never be used by `Step`: it is **dead** at the whole-step level.

* `deadPure20` (15 of 56 rules): `unreachable`, `label-vals`, `br-zero`, `br-succ`,
  `frame-vals`, `return-frame`, `return-label`, `trap-vals`, `trap-label`, `trap-frame`,
  `unop-trap`, `binop-trap`, `cvtop-trap`, `vunop-trap`, `vbinop-trap`.
* `deadRead20` (21 of 47 rules): `block`, `loop`, `call`, `call_indirect-call`,
  `call_indirect-trap`, `call_addr`, `ref.func`, and every `-trap`/`-oob` rule of tables and
  memories.

So in the wasm-2.0 script as written no block or loop is entered, no function is called and no
instruction traps through `Step`. `not_firesPure_dead`, `not_firesRead_dead` prove it, and
`bwdParts20_of_live` reduces the per-rule obligations `BwdParts20` to the live rules
(`BwdLive20`): 41 `Step_pure` rules, 26 `Step_read` rules and `Step` rules 4–21.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim (RuleBody Fires ValsOnly cfgV)
open Silmaril.Wasm.SpecTec.Sim.RefsGC (ruleTags relRules mustTags mustTags_sound TagsIn LhsIn
  not_ruleBody_of_tags)

set_option maxRecDepth 100000

/-! ## Forced constructors on the right -/

/-- The constructors the right-hand side of a conclusion `lhs ~> rhs` forces at top level. -/
def rhsOf : Exp → List MixopS
  | .tupE [_, r] => mustTags r
  | _ => []

/-- The constructors a rule's right-hand side forces at top level. -/
def rhsTags : Rule → List MixopS
  | .ruleD _ _ _ e _ => rhsOf e

/-- A conclusion whose right-hand side forces `op` is a pair. -/
theorem rhsOf_shape {e : Exp} {op : MixopS} (h : op ∈ rhsOf e) :
    ∃ l rr, e = .tupE [l, rr] ∧ op ∈ mustTags rr := by
  unfold rhsOf at h
  split at h
  · exact ⟨_, _, rfl, h⟩
  · simp at h

/-- A rule whose right-hand side forces `op` produces a list containing an injection `op`. -/
theorem rhs_has_tag {env : Env} {D : Silmaril.Wasm.SpecTec.Sim.Interp} {els : Prop} {r : Rule}
    {a : Value} {w : List Value} {op : MixopS}
    (hb : RuleBody env D els [] [] "%~>%" r (.tuple [a, .list w])) (hop : op ∈ rhsTags r) :
    ∃ u, Value.case op u ∈ w := by
  obtain ⟨nm, qs, op', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  obtain ⟨l, rr, rfl, hm⟩ := rhsOf_shape (e := e) hop
  obtain ⟨v₁, v₂, hv, -, h₂⟩ := evalExp_tup2_cases he
  have hv₂ : Value.list w = v₂ := by
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
    exact hv.2
  obtain ⟨l', hl', u, hu⟩ := mustTags_sound rr (hv₂ ▸ h₂) hm
  have hw : w = l' := Value.list.inj hl'
  exact ⟨u, hw ▸ hu⟩

/-! ## The constructors of `instr`, as a list -/

/-- The 68 constructors of wasm-2.0's `instr`, in order. -/
def instrHeads20 : List MixopS :=
  ["NOP", "UNREACHABLE", "DROP", "SELECT", "BLOCK", "LOOP", "IF%%ELSE%", "BR", "BR_IF",
   "BR_TABLE", "CALL", "CALL_INDIRECT", "RETURN", "CONST", "UNOP", "BINOP", "TESTOP", "RELOP",
   "CVTOP", "EXTEND", "VCONST", "VVUNOP", "VVBINOP", "VVTERNOP", "VVTESTOP", "VUNOP", "VBINOP",
   "VTESTOP", "VRELOP", "VSHIFTOP", "VBITMASK", "VSWIZZLE", "VSHUFFLE", "VSPLAT", "VEXTRACT_LANE",
   "VREPLACE_LANE", "VEXTUNOP", "VEXTBINOP", "VNARROW", "VCVTOP", "REF.NULL", "REF.FUNC",
   "REF.IS_NULL", "LOCAL.GET", "LOCAL.SET", "LOCAL.TEE", "GLOBAL.GET", "GLOBAL.SET", "TABLE.GET",
   "TABLE.SET", "TABLE.SIZE", "TABLE.GROW", "TABLE.FILL", "TABLE.COPY", "TABLE.INIT",
   "ELEM.DROP", "LOAD", "STORE", "VLOAD", "VLOAD_LANE", "VSTORE", "VSTORE_LANE", "MEMORY.SIZE",
   "MEMORY.GROW", "MEMORY.FILL", "MEMORY.COPY", "MEMORY.INIT", "DATA.DROP"]

set_option maxRecDepth 8000000 in
/-- `instrHeads20` is read off the script. -/
theorem instrHeads20_eq : instrCases20.map caseHead = instrHeads20 := by
  decide +kernel

/-- A typed `instr*` has its constructors among `instr`'s. -/
theorem tagsIn_of_typed {B : Builtins} {l : List Value}
    (h : TypedSome (simEnv20 B) instrsT20 (.list l)) : TagsIn instrHeads20 l := by
  intro x hx op w hxw
  obtain ⟨op', w', he, hop⟩ := instrHeads_of_typed h x hx
  have hop' : op = op' := (Value.case.inj (hxw.symm.trans he)).1
  rw [hop', ← instrHeads20_eq]
  exact hop

/-! ## Dead rules -/

/-- A rule is dead for `Step` when one of its sides forces a constructor that is not `instr`'s. -/
def deadAt (r : Rule) : Bool :=
  (ruleTags r ++ rhsTags r).any fun op => !instrHeads20.contains op

/-- The `Step_pure` rules `Step/pure` cannot use. -/
def deadPure20 : List Nat := [0, 7, 8, 9, 14, 15, 16, 17, 18, 19, 21, 23, 27, 35, 37]

/-- The `Step_read` rules `Step/read` cannot use. -/
def deadRead20 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 9, 12, 15, 19, 22, 24, 26, 28, 30, 32, 34, 37, 40, 44]

/-- Every listed rule of `x` is dead. -/
noncomputable def deadOk (x : IL.Id) (dead : List Nat) : Bool :=
  dead.all fun i =>
    match (relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x)[i]? with
    | some r => deadAt r
    | none => false

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- The listed `Step_pure` rules are dead (checked against the script). -/
theorem deadPure20_ok : deadOk "Step_pure" deadPure20 = true := by
  rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- The listed `Step_read` rules are dead (checked against the script). -/
theorem deadRead20_ok : deadOk "Step_read" deadRead20 = true := by
  rfl

/-- **A dead rule does not fire between `instr*` sequences.** -/
theorem not_fires_dead {B : Builtins} {x : IL.Id} {dead : List Nat}
    (hok : deadOk x dead = true) {i : Nat} (hi : i ∈ dead) {a : Value} {code w : List Value}
    (ha : a = .list code ∨ ∃ z, a = cfgV z code)
    (hcode : TypedSome (simEnv20 B) instrsT20 (.list code))
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w)) :
    ¬ Fires (simEnv20 B) x i (.tuple [a, .list w]) := by
  rintro ⟨t, rules, r, hrel, hr, hb⟩
  have hrules : relRules (envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm20.fixed) x = rules := by
    rw [← relRules_simEnv20 B]
    simp [relRules, hrel]
  have hdead : deadAt r = true := by
    have h₁ := List.all_eq_true.1 hok i hi
    rw [hrules, hr] at h₁
    exact h₁
  have hsides : (∃ op ∈ ruleTags r, op ∉ instrHeads20) ∨ ∃ op ∈ rhsTags r, op ∉ instrHeads20 := by
    simpa [deadAt] using hdead
  rcases hsides with ⟨op, hl, hS⟩ | ⟨op, hrhs, hS⟩
  · have hlhs : LhsIn instrHeads20 a := by
      rcases ha with rfl | ⟨z, rfl⟩
      · exact Or.inl ⟨code, rfl, tagsIn_of_typed hcode⟩
      · exact Or.inr ⟨z, code, rfl, tagsIn_of_typed hcode⟩
    exact not_ruleBody_of_tags hlhs hl hS hb
  · obtain ⟨u, hu⟩ := rhs_has_tag hb hrhs
    exact hS (tagsIn_of_typed hw _ hu op u rfl)

/-- The dead `Step_pure` rules do not fire between `instr*` sequences. -/
theorem not_firesPure_dead {B : Builtins} {i : Nat} (hi : i ∈ deadPure20) {code w : List Value}
    (hcode : TypedSome (simEnv20 B) instrsT20 (.list code))
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w)) :
    ¬ Fires (simEnv20 B) "Step_pure" i (.tuple [.list code, .list w]) :=
  not_fires_dead deadPure20_ok hi (Or.inl rfl) hcode hw

/-- The dead `Step_read` rules do not fire between `instr*` sequences. -/
theorem not_firesRead_dead {B : Builtins} {i : Nat} (hi : i ∈ deadRead20) {z : Value}
    {code w : List Value} (hcode : TypedSome (simEnv20 B) instrsT20 (.list code))
    (hw : TypedSome (simEnv20 B) instrsT20 (.list w)) :
    ¬ Fires (simEnv20 B) "Step_read" i (.tuple [cfgV z code, .list w]) :=
  not_fires_dead deadRead20_ok hi (Or.inr ⟨z, rfl⟩) hcode hw

/-! ## The obligations, reduced to the live rules -/

variable {H : Type}

/-- **The per-rule obligations on the live rules only**: `BwdParts20` with the `Step_pure` and
`Step_read` obligations restricted to the rules outside `deadPure20` and `deadRead20`. -/
structure BwdLive20 (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- The live `Step_pure` rules. -/
  pure : ∀ (i : Nat), i ∉ deadPure20 → ∀ (code : List Admin) (w : List Value),
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w]) →
    ∃ code', w = adminsToV code' ∧ PureStep P code code'
  /-- The live `Step_read` rules. -/
  read : ∀ (i : Nat), i ∉ deadRead20 → ∀ (c : Config H) (w : List Value),
    TypedSome (simEnv20 B) instrsT20 (.list (adminsToV c.code)) →
    TypedSome (simEnv20 B) instrsT20 (.list w) →
    Fires (simEnv20 B) "Step_read" i (.tuple [configV hn c, .list w]) →
    ∃ code', w = adminsToV code' ∧ ReadStep c.store c.frame c.code code'
  /-- The `Step` rules from `local.set` on. -/
  step : ∀ (i : Nat), 4 ≤ i → ∀ (c : Config H) (w : Value),
    Fires (simEnv20 B) "Step" i (.tuple [configV hn c, w]) →
    ∃ c', w = configV hn c' ∧ Step P host c c'

/-- **The dead rules discharge themselves**: the live obligations give `BwdParts20`. -/
theorem bwdParts20_of_live {B : Builtins} {hn : H → String} {P : Profile}
    {host : HostSemantics H} (L : BwdLive20 B hn P host) : BwdParts20 B hn P host where
  pure i code w hc hw hf := by
    by_cases hi : i ∈ deadPure20
    · exact absurd hf (not_firesPure_dead hi hc hw)
    · exact L.pure i hi code w hc hw hf
  read i c w hc hw hf := by
    by_cases hi : i ∈ deadRead20
    · exact absurd hf (not_firesRead_dead hi hc hw)
    · exact L.read i hi c w hc hw hf
  step := L.step

/-- **`Sim20.Task.wholeStepBwd` from the live obligations.** -/
theorem wholeStepBwd_of_live
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H) (nd : Bool) (r : RelaxedChoice), ∃ B : Builtins,
        BwdLive20 B hn (Profile.spec nd r) host) :
    Task.wholeStepBwd :=
  wholeStepBwd_of_parts fun H hn hinj host nd r => by
    obtain ⟨B, L⟩ := h H hn hinj host nd r
    exact ⟨B, bwdParts20_of_live L⟩

end Silmaril.Wasm.SpecTec.Sim20.Whole
