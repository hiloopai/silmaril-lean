module

public import Silmaril.Proofs.Wasm.Game.Linking.SetupTyping
public import Silmaril.Proofs.Wasm.Game.Linking.SharedExists
public import Silmaril.Wasm.Game.Linking.Defs
public import Silmaril.Proofs.Wasm.Game.Machine.Basic
public import Silmaril.Proofs.Wasm.Game.Adequacy.Termination
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

/-!
# The stores of a linking setup are the specification's instantiations (global-free modules)

For a module without globals, data and element segments, silmaril-lean's `instantiateOnce?`
(the single-allocation instantiation that the linking setup uses) *is* the specification's
instantiation: the configuration of `$instantiate` is `⟨s', f', []⟩` followed by the start call,
for every profile and host (`once_instantiate`): `instantiateOnce?` is then
`instantiateDirect?` (`instantiateOnce?_of_nil`), the code that `prepare?` builds is empty
(`prepare?_code`), and `prepare?_sound` applies.

`Setup.instantiate_spec`: if the provider and the consumer have no globals (the linker's
fragment `Recipe.Assembly` already excludes data and element segments), the provider store
`sp`, the shared store `sc`, the consumer store against host stubs `scs` and the linked store
`sl` of a linking setup are all the specification's instantiations (`Instantiate P host`), so
the linking theorems (M3, divergence-observing M3) are about the spec's instantiation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC Silmaril.Wasm.SingleThreaded

/-- **Single allocation is the specification's instantiation** for modules without globals and
segments. -/
theorem once_instantiate {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat}
    {s s' : Store Nat} {m : Module} {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx}
    (hg : m.globals = []) (hd : m.data = []) (he : m.elems = [])
    (h : instantiateOnce? s m xas = some (s', f', st))
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    Instantiate P host s m xas ((⟨s', f', []⟩ : Config Nat).withStart st) := by
  have h' : instantiateDirect? s m xas = some (s', f', st) := by
    rw [← instantiateOnce?_of_nil hg]; exact h
  obtain ⟨c, hp, hsteps⟩ := prepareDirect?_steps (P := P) (host := host) evalConst?_evalSound h'
  have hcode : c.code = [] := by
    rw [prepare?_code hp, hd, he]
    rfl
  have hc : c = ⟨s', f', []⟩ := by
    rcases Relation.ReflTransGen.cases_head hsteps with h₀ | ⟨c₁, hst, -⟩
    · exact h₀
    · exact absurd hst (Silmaril.Proofs.Wasm.Game.Step.not_result (r := .values []) hcode)
  rw [← hc]
  exact (prepare?_sound evalConst?_evalSound hp hvalid).2

/-- Typing of external addresses survives replacing function code by host stubs. -/
theorem externAddrOk_stubOut {s : Store Nat} {base : Nat} {stubs : List Nat} {xa : ExternAddr}
    {xt : CExternType} (h : ExternAddrOk s xa xt) : ExternAddrOk (stubOut base stubs s) xa xt := by
  induction h with
  | tag h => exact .tag h
  | global h => exact .global h
  | mem h => exact .mem h
  | table h => exact .table h
  | @func a fi h =>
    have h' : (stubOut base stubs s).funcs[a]? = some
        (if base ≤ a ∧ a - base ∈ stubs then { fi with code := .host (stubs.idxOf (a - base)) }
          else fi) := by
      simp only [stubOut, List.getElem?_mapIdx, h, Option.map_some]
    have ht := ExternAddrOk.func h'
    split at ht
    · exact ht
    · exact ht
  | sub _ hok hs ih => exact .sub ih hok hs

variable (S : Setup)

/-- **The stores of a linking setup are the specification's instantiations** when the provider
and the consumer have no globals: for every profile and host, the provider, the shared world,
the consumer against host stubs and the linked module are instantiated by `$instantiate`
(no start function, no segment code). -/
theorem Setup.instantiate_spec (hg : S.provider.globals = [] ∧ S.consumer.globals = [])
    (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics Nat) :
    Instantiate P host S.base S.provider (Preparation.imports []) ⟨S.sp, S.fp, []⟩ ∧
    Instantiate P host S.sp S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      ⟨S.sc, S.fc, []⟩ ∧
    Instantiate P host (stubOut S.base.funcs.length S.stubs S.sp) S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      ⟨S.scs, S.fcs, []⟩ ∧
    Instantiate P host S.base S.linked (Preparation.imports []) ⟨S.sl, S.fl, []⟩ := by
  obtain ⟨hpm, -, -, hpd, hpe, -⟩ := profile_sections' S.assembly.providerProfile
  obtain ⟨hcm, -, -, hcd, hce, -⟩ := profile_sections' S.assembly.consumerProfile
  have hpi : S.assembly.providerType.imports = [] := by
    have h := Recipe.validation_imports_length S.assembly.providerValidation
    rw [S.assembly.providerImports] at h
    exact List.length_eq_zero_iff.mp h
  have hvp : ∃ xtE xtI, ModuleOk S.provider ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk S.base) (Preparation.imports []) xtI :=
    ⟨S.assembly.providerType.exports, S.assembly.providerType.imports,
      validate?_sound S.assembly.providerValidation, by rw [hpi]; exact .nil⟩
  have hxc : List.Forall₂ (ExternAddrOk S.sp)
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      S.assembly.consumerType.imports := consumer_imports_ok S.assembly S.provInst
  have hvc : ∃ xtE xtI, ModuleOk S.consumer ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk S.sp)
        (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
        xtI :=
    ⟨_, _, validate?_sound S.assembly.consumerValidation, hxc⟩
  have hvs : ∃ xtE xtI, ModuleOk S.consumer ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk (stubOut S.base.funcs.length S.stubs S.sp))
        (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
        xtI :=
    ⟨_, _, validate?_sound S.assembly.consumerValidation, hxc.imp fun _ _ h => externAddrOk_stubOut h⟩
  obtain ⟨mt, hmt⟩ := link?_validate S.link
  have hout := S.assembly.output
  have hlg : S.linked.globals = [] := by
    have h1 : S.assembly.providerGlobals = [] := List.length_eq_zero_iff.mp
      (by rw [S.assembly.providerGlobals_length, hg.1]; rfl)
    have h2 : S.assembly.globals = [] := List.length_eq_zero_iff.mp
      (by rw [S.assembly.globals_length, hg.2]; rfl)
    rw [hout, h1, h2]
    rfl
  have hli : mt.imports = [] := by
    have h := Recipe.validation_imports_length hmt
    rw [hout] at h
    exact List.length_eq_zero_iff.mp h
  have hvl : ∃ xtE xtI, ModuleOk S.linked ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk S.base) (Preparation.imports []) xtI :=
    ⟨mt.exports, mt.imports, validate?_sound hmt, by rw [hli]; exact .nil⟩
  refine ⟨once_instantiate hg.1 hpd hpe S.provInst hvp, once_instantiate hg.2 hcd hce S.sharedInst hvc,
    once_instantiate hg.2 hcd hce S.stubInst hvs, ?_⟩
  have hld : S.linked.data = [] := by rw [hout]
  have hle : S.linked.elems = [] := by rw [hout]
  exact once_instantiate hlg hld hle S.linkedInst hvl

end Silmaril.Proofs.Wasm.Game.Linking
