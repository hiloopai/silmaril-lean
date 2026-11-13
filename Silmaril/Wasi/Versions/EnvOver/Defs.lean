module

public import Silmaril.Wasi.Versions.Cli3More.Defs
public import Silmaril.Wasi.Versions.FwdT.Defs

@[expose] public section

/-!
# Environment and exit across versions

`Cli3More.cli3Th E` says that the 0.3 environment functions answer the environment `E` and that
`exit`/`exit-with-code` never return. This module states the same theory for 0.2
(`specs/wasi/0.2.12/cli/{environment,exit}.wit`: `get-environment`, `get-arguments`,
`initial-cwd`, `exit`, `exit-with-code`), `env2Th E`, and the forwarders in both directions
(`Silmaril.Wasi.Versions.FwdT`): the signatures name no type that differs, so the answers pass
unchanged (`EnvOver.Thms.env3Over2_model`, `env2Over3_model`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.EnvOver

open Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions (fwdT)
open Silmaril.Wasi.Versions.Net (gated)
open Silmaril.Wasi.Versions.Cli3More

def getEnv2 : FnName := ⟨"wasi:cli/environment", "get-environment"⟩
def getArgs2 : FnName := ⟨"wasi:cli/environment", "get-arguments"⟩
def getCwd2 : FnName := ⟨"wasi:cli/environment", "initial-cwd"⟩
def exit2 : FnName := ⟨"wasi:cli/exit", "exit"⟩
def exitCode2 : FnName := ⟨"wasi:cli/exit", "exit-with-code"⟩

/-- The check of a 0.2 environment or exit answer. -/
def env2Ok (E : Env3) (_ : Unit) : WEv → Bool
  | .imp f _ r =>
    if f = getEnv2 then (one r).bind pairsOf == some E.vars
    else if f = getArgs2 then (one r).bind strsOf == some E.args
    else if f = getCwd2 then (one r).bind optStrOf == some E.cwd
    else if f = exit2 ∨ f = exitCode2 then r.isNone
    else true
  | _ => true

/-- **The 0.2 environment and exit theory** of the environment `E`. -/
def env2Th (E : Env3) : Protocol Unit WEv := gated () (fun _ _ => ()) (env2Ok E)

/-- The 0.3 functions. -/
def env3X : Set FnName := {getEnv3, getArgs3, getCwd3, exit3, exitCode3}

/-- The 0.2 functions. -/
def env2X : Set FnName := {getEnv2, getArgs2, getCwd2, exit2, exitCode2}

/-- The 0.2 function of a 0.3 one. -/
def to2 (f : FnName) : FnName :=
  if f = getEnv3 then getEnv2 else if f = getArgs3 then getArgs2
  else if f = getCwd3 then getCwd2 else if f = exit3 then exit2 else exitCode2

/-- The 0.3 function of a 0.2 one. -/
def to3 (f : FnName) : FnName :=
  if f = getEnv2 then getEnv3 else if f = getArgs2 then getArgs3
  else if f = getCwd2 then getCwd3 else if f = exit2 then exit3 else exitCode3

theorem to2_mem : ∀ f ∈ env3X, to2 f ∈ env2X := by
  intro f hf
  simp only [env3X, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [to2, env2X, getEnv3, getArgs3, getCwd3, exit3, exitCode3]

theorem to3_mem : ∀ f ∈ env2X, to3 f ∈ env3X := by
  intro f hf
  simp only [env2X, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [to3, env3X, getEnv2, getArgs2, getCwd2, exit2, exitCode2]

/-- **Environment and exit 0.3 over 0.2.** -/
def env3Over2 := fwdT env3X env2X to2 to2_mem fun _ r => r

/-- **Environment and exit 0.2 over 0.3.** -/
def env2Over3 := fwdT env2X env3X to3 to3_mem fun _ r => r

end Silmaril.Wasi.Versions.EnvOver
