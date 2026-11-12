module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMRead.TryTable

/-!
# Round 9, rm: `throw_ref-handler-next` fires only at memory-SIMD-free code (unrefined)

`Step_read` 21 matches `HANDLER_n{catch catch'*} (REF.EXN_ADDR a) THROW_REF`: a handler whose
body is a thrown exception. Such code has no memory SIMD instruction (the catch clauses hold no
code), so the rule has no obligation at code holding one (`adminsMS_of_handlerNext`). Its
`otherwise` premise is not read.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD adminsToVD adminsToVD_eq_single)
open RMPure (handlerD_of)

variable {H : Type} {hn : H → String}

/-- **`throw_ref-handler-next` fires only at code without memory SIMD instructions.** -/
theorem adminsMS_of_handlerNext (B : Builtins) {c : Config H} {w : Value}
    (hf : Fires (simEnv B) "Step_read" 21 (.tuple [configVD hn c, w])) :
    Round6.MemSimd.AdminsMS c.code := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerNext hf
  obtain ⟨-, hce, -⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨x, hx, hxe⟩ := Exn.evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨x', y', body, rfl⟩ := ctxD_of ha (.inr (.inl rfl))
  obtain ⟨n, cs, body', rfl, -, -, hb'⟩ := handlerD_of ha
  obtain ⟨-, -, h₃⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨av, -, hbl⟩ := Exn.evalExp_throwExn_inv (hb' ▸ h₃)
  obtain ⟨k, rfl, -⟩ := throwingD_of hbl
  exact ⟨⟨trivial, rfl, trivial⟩, trivial⟩

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
