module

public import Silmaril.Wasm.SpecTec.Sim.Round8.RMHost.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# Round 8, memory SIMD: Core steps at a store of host functions (unrefined)

`step_setF`: a Core step at the host with no outcome, from a configuration whose function
instances are all host functions (`F.map hostFI`), is a step at any host from the same
configuration with the function instances `F`, to the successor with `F`; and it keeps the
function instances. At such a store no rule reads a function body: `call_ref` to a Wasm function
cannot fire, and the host calls have no outcome. Every other rule reads function instances only
through their types (`call`, `return_call`, `return_call_ref`, reference typing). The delegated
families are handled by `*_setF`. Kept unrefined: it is one long case analysis, modelled on round
7's `exRel_step`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.RMHost

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Function types under `hostFI` -/

theorem types_hostFI {F : List (FuncInst H)} {G : List (FuncInst Unit)} (h : F.map hostFI = G)
    (a : Nat) : (F[a]?).map FuncInst.type = (G[a]?).map FuncInst.type := by
  subst h
  simp [hostFI, Option.map_map, Function.comp_def]

theorem get_hostFI {F : List (FuncInst H)} {G : List (FuncInst Unit)} (h : F.map hostFI = G)
    {a : Nat} {fi : FuncInst Unit} (hfi : G[a]? = some fi) :
    ∃ fi', F[a]? = some fi' ∧ fi'.type = fi.type ∧ fi.code = .host () := by
  subst h
  rw [List.getElem?_map] at hfi
  obtain ⟨fi', h₁, rfl⟩ := Option.map_eq_some_iff.mp hfi
  exact ⟨fi', h₁, rfl, rfl⟩

theorem refOk_setF₁ {u : Store Unit} {F : List (FuncInst H)} (hF : F.map hostFI = u.funcs)
    {r : Ref} {rt : CRefType} (h : RefOk u r rt) : RefOk (withFuncs u F) r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
      rename_i a fi
      obtain ⟨fi', hfi', hty, -⟩ := get_hostFI hF h
      exact hty ▸ .func hfi'
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_setF₂ {u : Store Unit} {F : List (FuncInst H)} (hF : F.map hostFI = u.funcs)
    {r : Ref} {rt : CRefType} (h : RefOk (withFuncs u F) r rt) : RefOk u r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
      rename_i a fi
      have ht := types_hostFI hF a
      simp only [withFuncs] at h
      rw [h] at ht
      obtain ⟨fi', hfi', hty⟩ := Option.map_eq_some_iff.mp ht.symm
      exact hty ▸ .func hfi'
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_setF_iff {u : Store Unit} {F : List (FuncInst H)} (hF : F.map hostFI = u.funcs)
    {r : Ref} {rt : CRefType} : RefOk (withFuncs u F) r rt ↔ RefOk u r rt :=
  ⟨refOk_setF₂ hF, refOk_setF₁ hF⟩

/-! ## The families -/

theorem variableStep_setF {c c' : Config Unit} (h : VariableStep c c') (F : List (FuncInst H)) :
    VariableStep (setF F c) (setF F c') := by
  cases h <;> simp only [setF] <;> constructor! <;> assumption

theorem tableStep_setF {P : Profile} {c c' : Config Unit} (h : TableStep P c c')
    (F : List (FuncInst H)) : TableStep P (setF F c) (setF F c') := by
  cases h <;> simp only [setF] <;> constructor! <;> assumption

theorem memoryStep_setF {P : Profile} {c c' : Config Unit} (h : MemoryStep P c c')
    (F : List (FuncInst H)) : MemoryStep P (setF F c) (setF F c') := by
  cases h <;> simp only [setF] <;> constructor! <;> assumption

theorem aggregateStep_setF {c c' : Config Unit} (h : AggregateStep c c')
    (F : List (FuncInst H)) : AggregateStep (setF F c) (setF F c') := by
  cases h <;> simp only [setF] <;>
    first
      | (constructor! <;> assumption)
      | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)

theorem refStep_setF {c c' : Config Unit} (h : RefStep c c') (F : List (FuncInst H))
    (hF : F.map hostFI = c.store.funcs) : RefStep (setF F c) (setF F c') := by
  cases h <;> simp only [setF] at hF ⊢ <;> constructor! <;>
    first
      | assumption
      | exact (refOk_setF_iff hF).mpr ‹_›
      | exact fun h' => ‹¬ _› ((refOk_setF_iff hF).mp h')

/-! ## The whole step -/

/-- **A step at a store of host functions, at the host with no outcome, is a step with any
function instances of the same types, at any host**; it keeps the function instances. -/
theorem step_setF {P : Profile} {host : HostSemantics H} {c c' : Config Unit}
    (h : Step P Round7.NullHost.nullHost c c') :
    ∀ F : List (FuncInst H), F.map hostFI = c.store.funcs →
      Step P host (setF F c) (setF F c') ∧ c'.store.funcs = c.store.funcs := by
  induction h with
  | parametric h => exact fun F _ => ⟨.parametric h, rfl⟩
  | numeric h => exact fun F _ => ⟨.numeric h, rfl⟩
  | vector h => exact fun F _ => ⟨.vector h, rfl⟩
  | «variable» h =>
      exact fun F _ => ⟨.variable (variableStep_setF h F), (Round7.variableStep_funcs h).1⟩
  | table h => exact fun F _ => ⟨.table (tableStep_setF h F), (Round7.tableStep_funcs h).1⟩
  | memory h => exact fun F _ => ⟨.memory (memoryStep_setF h F), (Round7.memoryStep_funcs h).1⟩
  | reference h =>
      exact fun F hF => ⟨.reference (refStep_setF h F hF), (Round7.refStep_funcs h).1⟩
  | aggregate h =>
      exact fun F _ => ⟨.aggregate (aggregateStep_setF h F), (Round7.aggregateStep_funcs h).1⟩
  | ctxtInstrs h hne ih =>
      intro F hF
      obtain ⟨h', he⟩ := ih F hF
      exact ⟨.ctxtInstrs h' hne, he⟩
  | ctxtLabel h ih =>
      intro F hF
      obtain ⟨h', he⟩ := ih F hF
      exact ⟨.ctxtLabel h', he⟩
  | ctxtHandler h ih =>
      intro F hF
      obtain ⟨h', he⟩ := ih F hF
      exact ⟨.ctxtHandler h', he⟩
  | ctxtFrame h ih =>
      intro F hF
      obtain ⟨h', he⟩ := ih F hF
      exact ⟨.ctxtFrame h', he⟩
  | block hbt hm => exact fun F _ => ⟨.block hbt hm, rfl⟩
  | loop hbt hm => exact fun F _ => ⟨.loop hbt hm, rfl⟩
  | ifTrue hc => exact fun F _ => ⟨.ifTrue hc, rfl⟩
  | ifFalse => exact fun F _ => ⟨.ifFalse, rfl⟩
  | labelVals => exact fun F _ => ⟨.labelVals, rfl⟩
  | brLabelZero hl hn => exact fun F _ => ⟨.brLabelZero hl hn, rfl⟩
  | brLabelSucc hl => exact fun F _ => ⟨.brLabelSucc hl, rfl⟩
  | brHandler => exact fun F _ => ⟨.brHandler, rfl⟩
  | brIfTrue hc => exact fun F _ => ⟨.brIfTrue hc, rfl⟩
  | brIfFalse => exact fun F _ => ⟨.brIfFalse, rfl⟩
  | brTableLt hi => exact fun F _ => ⟨.brTableLt hi, rfl⟩
  | brTableGe hi => exact fun F _ => ⟨.brTableGe hi, rfl⟩
  | brOnNullNull => exact fun F _ => ⟨.brOnNullNull, rfl⟩
  | brOnNullAddr hv => exact fun F _ => ⟨.brOnNullAddr hv, rfl⟩
  | brOnNonNullNull => exact fun F _ => ⟨.brOnNonNullNull, rfl⟩
  | brOnNonNullAddr hv => exact fun F _ => ⟨.brOnNonNullAddr hv, rfl⟩
  | brOnCastSucceed h =>
      exact fun F hF => ⟨.brOnCastSucceed ((refOk_setF_iff hF).mpr h), rfl⟩
  | brOnCastFail h =>
      exact fun F hF => ⟨.brOnCastFail fun h' => h ((refOk_setF_iff hF).mp h'), rfl⟩
  | brOnCastFailSucceed h =>
      exact fun F hF => ⟨.brOnCastFailSucceed ((refOk_setF_iff hF).mpr h), rfl⟩
  | brOnCastFailFail h =>
      exact fun F hF => ⟨.brOnCastFailFail fun h' => h ((refOk_setF_iff hF).mp h'), rfl⟩
  | call hx hf =>
      rename_i s f x a fi
      intro F hF
      obtain ⟨fi', hfi', hty, -⟩ := get_hostFI hF hf
      have h₁ := Step.call (P := P) (host := host) (s := withFuncs s F) hx hfi'
      rw [hty] at h₁
      exact ⟨h₁, rfl⟩
  | callRefNull hc => exact fun F _ => ⟨.callRefNull hc, rfl⟩
  | callRefFunc hc hf he hn hcode =>
      intro F hF
      obtain ⟨-, -, -, hh⟩ := get_hostFI hF hf
      rw [hcode] at hh
      cases hh
  | callRefHost hc hf he hn hcode hhost => exact hhost.elim
  | callRefHostDiv hc hf he hn hcode hhost => exact hhost.elim
  | returnCall hx hf =>
      rename_i s f x a fi
      intro F hF
      obtain ⟨fi', hfi', hty, -⟩ := get_hostFI hF hf
      have h₁ := Step.returnCall (P := P) (host := host) (s := withFuncs s F) hx hfi'
      rw [hty] at h₁
      exact ⟨h₁, rfl⟩
  | returnCallRefLabel hc => exact fun F _ => ⟨.returnCallRefLabel hc, rfl⟩
  | returnCallRefHandler hc => exact fun F _ => ⟨.returnCallRefHandler hc, rfl⟩
  | returnCallRefFrameNull hc => exact fun F _ => ⟨.returnCallRefFrameNull hc, rfl⟩
  | returnCallRefFrameAddr hc hf he hn =>
      intro F hF
      obtain ⟨fn', hfn', hty, -⟩ := get_hostFI hF hf
      exact ⟨.returnCallRefFrameAddr hc hfn' (hty ▸ he) hn, rfl⟩
  | callIndirect => exact fun F _ => ⟨.callIndirect, rfl⟩
  | returnCallIndirect => exact fun F _ => ⟨.returnCallIndirect, rfl⟩
  | frameVals hn => exact fun F _ => ⟨.frameVals hn, rfl⟩
  | returnFrame hn => exact fun F _ => ⟨.returnFrame hn, rfl⟩
  | returnLabel => exact fun F _ => ⟨.returnLabel, rfl⟩
  | returnHandler => exact fun F _ => ⟨.returnHandler, rfl⟩
  | throw ht he hn => exact fun F _ => ⟨.throw ht he hn, rfl⟩
  | throwRefNull => exact fun F _ => ⟨.throwRefNull, rfl⟩
  | throwRefInstrs hne => exact fun F _ => ⟨.throwRefInstrs hne, rfl⟩
  | throwRefLabel => exact fun F _ => ⟨.throwRefLabel, rfl⟩
  | throwRefFrame => exact fun F _ => ⟨.throwRefFrame, rfl⟩
  | throwRefHandlerEmpty => exact fun F _ => ⟨.throwRefHandlerEmpty, rfl⟩
  | throwRefHandlerCatch he ht => exact fun F _ => ⟨.throwRefHandlerCatch he ht, rfl⟩
  | throwRefHandlerCatchRef he ht => exact fun F _ => ⟨.throwRefHandlerCatchRef he ht, rfl⟩
  | throwRefHandlerCatchAll => exact fun F _ => ⟨.throwRefHandlerCatchAll, rfl⟩
  | throwRefHandlerCatchAllRef => exact fun F _ => ⟨.throwRefHandlerCatchAllRef, rfl⟩
  | throwRefHandlerNext h => exact fun F _ => ⟨.throwRefHandlerNext h, rfl⟩
  | tryTable hbt hm => exact fun F _ => ⟨.tryTable hbt hm, rfl⟩
  | handlerVals => exact fun F _ => ⟨.handlerVals, rfl⟩
  | trapInstrs hne => exact fun F _ => ⟨.trapInstrs hne, rfl⟩
  | trapLabel => exact fun F _ => ⟨.trapLabel, rfl⟩
  | trapHandler => exact fun F _ => ⟨.trapHandler, rfl⟩
  | trapFrame => exact fun F _ => ⟨.trapFrame, rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Round8.RMHost
