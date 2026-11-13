module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping.Defs
/-! Static membership in the actual register scope implies the existing shape
judgment for actual projection/reference/pack/operation/let-chain/return syntax.
This does not yet prove membership for the actual native enter/view inputs. -/
@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping
open Silmaril.Isotope.LambdaSSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Machine.RTL.SSA (Scope)
open Admission

theorem proj_fits {context : List Shape} {term : Old.Tm} {width index : Nat}
    (inside : index < width) (typed : TmFits [] context term (.tuple width)) :
    TmFits [] context (Silmaril.Machine.RTL.SSA.proj index term) .word := by
  induction index generalizing context term width with
  | zero =>
    cases width with
    | zero => cases inside
    | succ width => exact .let₂ typed (.var rfl)
  | succ index ih =>
    cases width with
    | zero => cases inside
    | succ width => exact .let₂ typed (ih (Nat.lt_of_succ_lt_succ inside) (.var rfl))

/-- Actual scope membership rules out the junk-unit reference fallback. -/
theorem ref_fits (scope : Scope Nat) {register : Nat} (available : scope.HasReg register) :
    TmFits [] (scopeContext scope) (scope.ref (Φ := Old.Opcode) register) .word := by
  obtain ⟨⟨index, position⟩, found⟩ :=
    Option.isSome_iff_exists.mp (Scope.findReg_isSome_of_hasReg available)
  obtain ⟨_, registers, lookup, inside, _⟩ := Scope.findReg_spec found
  have tupleLookup : scope.vals[index]? = some registers := by
    simpa only [Nat.sub_zero] using lookup
  have typed : TmFits [] (scopeContext scope) (.var index) (.tuple registers.length) :=
    .var (by simp only [scopeContext, List.getElem?_map, tupleLookup, Option.map_some])
  unfold Scope.ref
  rw [found]
  exact proj_fits inside typed

theorem pack_fits (scope : Scope Nat) {registers : List Nat} (available : scope.Covers registers) :
    TmFits [] (scopeContext scope) (scope.pack (Φ := Old.Opcode) registers) (.tuple registers.length) := by
  induction registers with
  | nil => exact .unit
  | cons register rest ih =>
    exact .pair (ref_fits scope (available register List.mem_cons_self))
      (ih (fun register member => available register (List.mem_cons_of_mem _ member)))

/-- The actual arithmetic operation translation has the tuple of its actual
result registers, once every source operand is in the actual register scope. -/
theorem op_toTm_fits (scope : Scope Nat) {instruction : Old.Op}
    (admitted : ArithmeticOp instruction) (available : scope.Covers instruction.uses) :
    TmFits [] (scopeContext scope) (instruction.toTm [] scope) (.tuple instruction.defs.length) := by
  cases instruction with
  | const => exact .op (by intro impossible; cases impossible) .unit
  | move | unary | binary => exact .op (by intro impossible; cases impossible) (pack_fits scope available)
  | load | store | call => cases admitted

/-- The actual let chain retains its existing annotation. The scope premise
is static source-register membership at each actual instruction prefix. -/
theorem opsRegion_fits (scope : Scope Nat) (instructions : List Old.Op)
    (admitted : ∀ instruction ∈ instructions, ArithmeticOp instruction)
    (available : ∀ (previous : List Old.Op) (instruction : Old.Op) (rest : List Old.Op),
      instructions = previous ++ instruction :: rest → (scope.afterOps previous).Covers instruction.uses)
    {continuation : Old.Region} {annotation : Silmaril.Machine.RTL.SSA.Ann} {labels : List Nat}
    (typed : RegionFits [] (scopeContext (scope.afterOps instructions)) continuation annotation labels) :
    RegionFits [] (scopeContext scope) (Silmaril.Machine.RTL.SSA.opsRegion [] scope instructions continuation)
      (instructions.foldr (fun _ body => .let₁ body) annotation) labels := by
  induction instructions generalizing scope with
  | nil => exact typed
  | cons instruction rest ih =>
    apply RegionFits.let₁ (op_toTm_fits scope (admitted instruction List.mem_cons_self)
      (available [] instruction rest rfl))
    apply ih (scope.push instruction.defs)
      (fun candidate member => admitted candidate (List.mem_cons_of_mem _ member))
    · intro before candidate after same
      exact available (instruction :: before) candidate after (by rw [same]; rfl)
    · exact typed

theorem ret_fits (function : Old.Func) (scope : Scope Nat) {registers labels : List Nat}
    (available : scope.Covers registers) (declared : labels[scope.depth]? = some registers.length) :
    RegionFits [] (scopeContext scope)
      ((Silmaril.Machine.RTL.SSA.Term.ret registers).toRegion [] function scope) .br labels :=
  .br declared (pack_fits scope available)

end Silmaril.Compiler.Native.Optimize.LambdaSSA.ScopeTyping
