module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-!
# The wasm-3.0 text defect `$ieee_`, at the pin and on main

`$ieee_(N, rat) : fNmag(N)` is the function the text grammar `TfNmag` uses to round a decimal or
hexadecimal float literal to a float.  It is declared with no clauses and no `hint(builtin)`,
both at the pin (`608711107b`) and on main (`e7a9df7c`).  `IeeeUndefined` is the declaration
fact (kernel `rfl` on the generated scripts); `callUndef_of_noClauses` turns any such
declaration into the evaluator fact that every call has no value, at every fuel and every
argument, because the scripts install no builtins.
-/

public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Broken
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000

/-- **A function declared without clauses has no value at any call** in a script's own
environment (which has no builtins). -/
theorem callUndef_of_noClauses {s : Script} {f : IL.Id} (h : NoClauses s f) (args : List Arg) :
    CallUndef s f args := by
  obtain ⟨ps, t, hf⟩ := h
  intro N v hv
  cases N with
  | zero => simp [callDef] at hv
  | succ n =>
    rw [callDef_eq] at hv
    have hρ : (VarEnv.empty.findDef? f).getD f = f := rfl
    rw [hρ, hf] at hv
    cases hA : evalArgs n (envOfScript s) VarEnv.empty args with
    | error e => rw [hA] at hv; cases hv
    | ok argVs =>
      rw [hA] at hv
      cases n with
      | zero => simp [tryClauses, Res.elimUndef] at hv
      | succ m =>
        simp [tryClauses, Res.elimUndef, Res.ofOption, builtins_envOfScript, Builtins.none] at hv

theorem ieeeUndefined_original : IeeeUndefined Wasm30.original := ⟨_, _, by rfl⟩

theorem ieeeUndefined_main : IeeeUndefined Main.Wasm30.original := ⟨_, _, by rfl⟩

/-- **On main, `$ieee_(32, 1)` has no value**: so `TfNmag(32)` gives the literal `1.0` no
float. -/
theorem ieee_one_undef_main :
    CallUndef Main.Wasm30.original "ieee_" [.expA (.numE (.natN 32)), .expA (.numE (.ratN 1))] :=
  callUndef_of_noClauses ieeeUndefined_main _

end Silmaril.Wasm.SpecTec.Versions
