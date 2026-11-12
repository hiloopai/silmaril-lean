module

public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Bwd.Thms

/-!
# Typing of contexts, introduced

The converses of the typing track's inversions `TypingFacts.label`, `handler`, `frame`: a label,
handler or frame whose components are typed is a typed `instr` (`typedV_label`, `typedV_handler`,
`typedV_frame`), and `CALL_REF yy` is an `instr` when `yy` is a `typeuse`
(`callRefTyping_simEnv : Bwd.CallRefTyping (simEnv B)`, which the backward track assumed). All in
every `simEnv B`, from the script's `instr` definition (`Original.d271`).

The forward simulation up to call annotations (`Integrate`'s `forward_upTo`) needs them: its
SpecTec successor is not Core's, so its typing is rebuilt around the rewritten redex.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdMem

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d271)
open IntNumeric (findCase recCases quantFreeAt)

variable {B : Builtins}

/-- A case `op` of `instr`, with a typed payload and no premise, is a typed `instr`. -/
theorem typedV_instrCase {op : MixopS} {t : Typ} {w : Value}
    (hf : findCase (recCases Original.d271 0 0) op = some (t, []))
    (hq : quantFreeAt (recCases Original.d271 0 0) op = true)
    (h : HasTyp (simEnv B) VarEnv.empty t w) :
    TypedV (simEnv B) (.varT "instr" []) (.case op w) := fun ρ hρ => by
  have hl : localTyp? ρ "instr" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  exact hasTyp_varT_case hl (IntNumeric.findTyp_instr' B) Equiv.evalArgs_nil matchArgs_nil
    (IntNumeric.hasTypCase_of_findCase hf h premsOk_nil hq)

/-- A three-field `instr` case `n; τ; instr*` with typed components. -/
theorem typedV_admin3_intro {op : MixopS} {y : IL.Id} {τ : Typ} {k : Nat} {u : Value}
    {l : List Value}
    (hf : findCase (recCases Original.d271 0 0) op =
      some (.tupT [.mk "n" nT, .mk y τ, .mk "instr*" instrsT], []))
    (hq : quantFreeAt (recCases Original.d271 0 0) op = true)
    (h₁ : TypedV (simEnv B) nT (.num (.natN k))) (h₂ : TypedV (simEnv B) τ u)
    (h₃ : TypedV (simEnv B) instrsT (.list l)) :
    TypedV (simEnv B) instrsT (.list [.case op (.tuple [.num (.natN k), u, .list l])]) :=
  typedV_list_single.2 (typedV_instrCase hf hq (hasTyp_tupT_iff.2 ⟨_, rfl,
    hasTypTup_cons_iff.2 ⟨_, _, rfl, h₁ _ ⟨rfl, rfl, rfl⟩,
      hasTypTup_cons_iff.2 ⟨_, _, rfl, h₂ _ ⟨rfl, rfl, rfl⟩,
        hasTypTup_cons_iff.2 ⟨_, _, rfl, h₃ _ ⟨rfl, rfl, rfl⟩, hasTypTup_nil_iff.2 rfl⟩⟩⟩⟩))

set_option maxRecDepth 100000 in
/-- A label with typed components is typed. -/
theorem typedV_label {n : Nat} {cont : List Instr} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv B) instrsT (.list (instrsToV cont)))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToV body))) :
    TypedV (simEnv B) instrsT (.list [adminToV (.label n cont body)]) :=
  typedV_admin3_intro rfl rfl h₁ h₂ h₃

set_option maxRecDepth 100000 in
/-- A handler with typed components is typed. -/
theorem typedV_handler {n : Nat} {cs : List Catch} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n)))
    (h₂ : TypedV (simEnv B) catchesT (.list (cs.map Encode.toValue)))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToV body))) :
    TypedV (simEnv B) instrsT (.list [adminToV (.handler n cs body)]) :=
  typedV_admin3_intro rfl rfl h₁ h₂ h₃

set_option maxRecDepth 100000 in
/-- A frame with typed components is typed. -/
theorem typedV_frame {n : Nat} {f : Frame} {body : List Admin}
    (h₁ : TypedV (simEnv B) nT (.num (.natN n))) (h₂ : TypedV (simEnv B) frameT (frameV f))
    (h₃ : TypedV (simEnv B) instrsT (.list (adminsToV body))) :
    TypedV (simEnv B) instrsT (.list [adminToV (.frame n f body)]) :=
  typedV_admin3_intro rfl rfl h₁ h₂ h₃

set_option maxRecDepth 100000 in
/-- **`Bwd.CallRefTyping`, proved**: `CALL_REF yy` is an `instr` when `yy` is a `typeuse`. -/
theorem callRefTyping_simEnv (B : Builtins) : Bwd.CallRefTyping (simEnv B) :=
  ⟨fun _ hy => typedV_instrCase rfl rfl (hy _ ⟨rfl, rfl, rfl⟩)⟩

end Silmaril.Wasm.SpecTec.Sim.FwdMem
