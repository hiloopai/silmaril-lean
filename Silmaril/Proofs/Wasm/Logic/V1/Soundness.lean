module

public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Structural
public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Basic
public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Variables
public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Memory
public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Control
public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Call

/-!
# Soundness of Wasm Logic

Theorem 2 of Watt et al., `inference_rules_sound`.

The proof is a strong induction on the derivation height of the execution,
inside which a structural induction on the `Triple` derivation applies the
per-rule lemmas of `Silmaril.Proofs.Wasm.Logic.V1.Sound`. The outer induction is what
`[loop]` and `[module]` need: a loop iteration and a function call each consume
height, and only the height gives a measure for the recursion.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*}

/-- The inner, structural induction of `Triple.sound`: every rule is discharged
by the matching `valid_*` lemma of `Silmaril.Proofs.Wasm.Logic.V1.Sound`, with `[loop]`
and `[call]` the only two that look outside the derivation. -/
private theorem sound_step (host : HostSemantics H) (n : Nat)
    (outer : ∀ (m : Nat), m < n → ∀ (Γ : Ctx) (P Q : Assert) (code : Silmaril.Wasm.V1.Expr),
      Triple Γ P code Q → ValidSpecs host m Γ.funcs Γ.assume →
      Valid host m Γ.funcs Γ.labels Γ.ret P code Q)
    {Γ : Ctx} {P Q : Assert} {code : Silmaril.Wasm.V1.Expr} (h : Triple Γ P code Q) :
    ValidSpecs host n Γ.funcs Γ.assume → Valid host n Γ.funcs Γ.labels Γ.ret P code Q := by
  induction h with
  -- Structural rules, Figure 10.
  | empty => exact fun _ => valid_empty
  | seq _ _ ih₁ ih₂ =>
    exact fun specs => valid_seq (ih₁ specs) (ih₂ specs)
  | consequence _ pre post labelLen labels return_ ih =>
    exact fun specs => valid_consequence (ih specs) pre post labelLen labels return_
  | frame _ _ indep ih =>
    exact fun specs => valid_frame _ (ih specs) indep
  | exists_ _ ih =>
    exact fun specs => valid_exists fun a => ih a specs
  | extension _ _ indep ih =>
    exact fun specs => valid_extension _ (ih specs) indep
  | context _ ih =>
    exact fun specs => valid_context (ih specs)
  | contextRet _ ih =>
    exact fun specs => valid_contextRet (ih specs)
  -- Basic instructions, Figure 6.
  | const => exact fun _ => valid_const _
  | unreachable => exact fun _ => valid_unreachable _
  | nop => exact fun _ => valid_nop
  | drop => exact fun _ => valid_drop _
  | select _ _ _ _ sameType =>
    exact fun _ => valid_select _ _ _ sameType
  | intUnOp => exact fun _ => valid_intUnOp _ _ _
  | intBinOp => exact fun _ => valid_intBinOp _ _ _ _ _
  | intTestOp => exact fun _ => valid_intTestOp _ _ _
  | intRelOp => exact fun _ => valid_intRelOp _ _ _ _
  | floatUnOp => exact fun _ => valid_floatUnOp _ _ _ _
  | floatBinOp => exact fun _ => valid_floatBinOp _ _ _ _ _
  | floatRelOp => exact fun _ => valid_floatRelOp _ _ _ _
  | convert => exact fun _ => valid_convert _ _ _
  -- Variable management, Figure 7.
  | localGet => exact fun _ => valid_localGet _
  | localSet => exact fun _ => valid_localSet _ _
  | localTee => exact fun _ => valid_localTee _ _
  | globalGet => exact fun _ => valid_globalGet _
  | globalSet => exact fun _ => valid_globalSet _ _
  -- Memory management, Figure 8.
  | intLoad => exact fun _ => valid_intLoad _ _ _ _
  | floatLoad => exact fun _ => valid_floatLoad _ _ _ _
  | intStore => exact fun _ => valid_intStore _ _ _ _
  | floatStore => exact fun _ => valid_floatStore _ _ _ _
  | memorySize => exact fun _ => valid_memorySize _
  | memoryGrow => exact fun _ => valid_memoryGrow _ _
  -- Control flow, Figure 9.
  | br _ _ _ target =>
    exact fun _ => valid_br _ target
  | return_ _ _ target =>
    exact fun _ => valid_return target
  | block _ _ pre post _ ih =>
    exact fun specs => valid_block _ _ pre post (ih specs)
  | loop bt body pre post inner ih =>
    refine fun specs => valid_loop bt body pre post (fun k hk => Valid.mono hk (ih specs))
      fun k hk => outer k hk _ _ _ _ (Triple.loop bt body pre post inner) ?_
    exact fun j P₁ Q₁ ha => Valid.mono (Nat.le_of_lt hk) (specs j P₁ Q₁ ha)
  | if_ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    exact fun specs => valid_if _ _ _ _ _ _ (ih₁ specs) (ih₂ specs)
  | brIf _ _ _ _ _ ih =>
    exact fun specs => valid_brIf _ _ _ _ (ih specs)
  | brTable _ _ _ _ _ _ _ ihCases ihDflt =>
    exact fun specs =>
      valid_brTable _ _ _ _ _ (fun k l hk => ihCases k l hk specs) (ihDflt specs)
  -- Function calls, Figure 11.
  | call _ _ _ assumed bound =>
    exact fun specs => valid_call _ specs assumed bound

/-- The outer, strong induction on the derivation height. -/
private theorem sound_forall (host : HostSemantics H) (n : Nat) :
    ∀ (Γ : Ctx) (P Q : Assert) (code : Silmaril.Wasm.V1.Expr), Triple Γ P code Q →
      ValidSpecs host n Γ.funcs Γ.assume → Valid host n Γ.funcs Γ.labels Γ.ret P code Q := by
  induction n using Nat.strong_induction_on with
  | _ n outer => exact fun _ _ _ _ h specs => sound_step host n outer h specs

/-- Every derivable triple is valid, relative to its assumed function
specifications. -/
theorem Triple.sound (host : HostSemantics H) (n : Nat) {Γ : Ctx} {P Q : Assert} {code : Silmaril.Wasm.V1.Expr}
    (h : Triple Γ P code Q) (specs : ValidSpecs host n Γ.funcs Γ.assume) :
    Valid host n Γ.funcs Γ.labels Γ.ret P code Q :=
  sound_forall host n Γ P Q code h specs

/-- The `[module]` rule is sound: a set of mutually recursive function
specifications, each established assuming all of them, holds outright. -/
theorem ModuleSpecs.sound (host : HostSemantics H) {F : List FuncDef} {specs : FuncSpecs}
    (hm : ModuleSpecs F specs) (n : Nat) : ValidSpecs host n F specs := by
  induction n with
  | zero =>
    -- Every `BigStepN` rule concludes at a successor height, so there is no
    -- execution at all of height `0`.
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ run
    cases run
  | succ n IH =>
    intro i P Q spec
    obtain ⟨d, found, rule⟩ := hm i P Q spec
    exact valid_funcRule i d found rule.pre rule.post rule.results
      rule.preLocals rule.postLocals fun k hk =>
        rule.body.sound host k fun j P₁ Q₁ hj =>
          Valid.mono (Nat.lt_succ_iff.mp hk) (IH j P₁ Q₁ hj)

/-- Theorem 2, against the unindexed big-step semantics: every specification of
a verified module holds of every execution of the corresponding call. -/
theorem ModuleSpecs.soundBig (host : HostSemantics H) {F : List FuncDef} {specs : FuncSpecs}
    (hm : ModuleSpecs F specs) {i : FuncIdx} {P Q : Assert} (spec : specs i P Q) :
    ValidBig host F [] none P [.call i] Q :=
  validBig_of_valid fun n => hm.sound host n i P Q spec

/-- Soundness of the triple against the unindexed big-step semantics. -/
theorem Triple.soundBig (host : HostSemantics H) {Γ : Ctx} {P Q : Assert} {code : Silmaril.Wasm.V1.Expr}
    (h : Triple Γ P code Q) (specs : ∀ n, ValidSpecs host n Γ.funcs Γ.assume) :
    ValidBig host Γ.funcs Γ.labels Γ.ret P code Q :=
  validBig_of_valid fun n => h.sound host n (specs n)

/-- A verified module's functions never trap and never get stuck in a state
violating their specification, stated directly against the small-step
semantics of `Silmaril.Wasm.V1.Execution`. -/
theorem ModuleSpecs.soundSteps (host : HostSemantics H) {F : List FuncDef} {specs : FuncSpecs}
    (hm : ModuleSpecs F specs) {i : FuncIdx} {P Q : Assert} (spec : specs i P Q)
    {s s' : Store H} {f f' : Frame} {ρ : Sto} {vs ws : List Value} {h hf : AHeap}
    (pre : P ρ vs h) (disj : AHeap.Disj h hf) (reify : Reifies F s f ρ (h ∪ hf))
    (run : Steps host ⟨s, f, values vs ++ [.source (.call i)]⟩ ⟨s', f', values ws⟩) :
    ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F s' f' ρ' (h' ∪ hf) ∧
      (∀ x, ¬ x.IsProgram → ρ' x = ρ x) ∧ Q ρ' ws h' := by
  have big : BigStep host s f ([] ++ vs) (expression [Silmaril.Wasm.V1.Instr.call i])
      ⟨s', f', .normal ws⟩ := bigStep_normal_iff_steps.mpr run
  obtain ⟨h', ρ', disj', reify', agree, sat⟩ :=
    hm.soundBig host spec s f ρ vs [] h hf _ pre disj reify big
  obtain ⟨ws', hws, hQ⟩ := sat
  rw [List.nil_append] at hws
  subst hws
  exact ⟨h', ρ', disj', reify', Sto.log_agree_of_modified agree, hQ⟩

/-- A verified module's functions do not trap. -/
theorem ModuleSpecs.not_trap (host : HostSemantics H) {F : List FuncDef} {specs : FuncSpecs}
    (hm : ModuleSpecs F specs) {i : FuncIdx} {P Q : Assert} (spec : specs i P Q)
    {s s' : Store H} {f f' : Frame} {ρ : Sto} {vs : List Value} {h hf : AHeap}
    (pre : P ρ vs h) (disj : AHeap.Disj h hf) (reify : Reifies F s f ρ (h ∪ hf)) :
    ¬ Steps host ⟨s, f, values vs ++ [.source (.call i)]⟩ ⟨s', f', [.trap]⟩ := by
  intro run
  have big : BigStep host s f ([] ++ vs) (expression [Silmaril.Wasm.V1.Instr.call i]) ⟨s', f', .trap⟩ :=
    bigStep_trap_iff_steps.mpr run
  obtain ⟨h', ρ', -, -, -, sat⟩ := hm.soundBig host spec s f ρ vs [] h hf _ pre disj reify big
  exact sat

end Silmaril.Wasm.Logic.V1
