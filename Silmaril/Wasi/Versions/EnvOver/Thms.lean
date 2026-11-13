module

public import Silmaril.Wasi.Versions.EnvOver.Defs
public import Silmaril.Wasi.Versions.FwdT.Thms

@[expose] public section

/-!
# Environment and exit across versions: theorems

PROVED (standard axioms):

* **`env3Over2_model`**: over every host of `env2Th E`, the forwarder `env3Over2` is a model
  of the 0.3 theory `cli3Th E` (whose clock clauses it never meets).
* **`env2Over3_model`**: over every host of `cli3Th E`, the forwarder `env2Over3` is a model of
  `env2Th E`.
-/

namespace Silmaril.Wasi.Versions.EnvOver

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Versions (FwdSim fwdT_model ofSBody)
open Silmaril.Wasi.Versions.Cli3More

/-- The 0.3 check of an environment or exit answer is the 0.2 check of the paired function. -/
theorem cli3Ok_env (E : Env3) (q : Clk3) (f : FnName) (hf : f ∈ env3X) (a : List Val)
    (r : Option (List Val)) : cli3Ok E q (.imp f a r) = env2Ok E () (.imp (to2 f) a r) := by
  simp only [env3X, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [cli3Ok, env2Ok, to2, getEnv3, getArgs3, getCwd3, exit3, exitCode3, getEnv2, getArgs2,
      getCwd2, exit2, exitCode2]

/-- The 0.3 clock state does not change on environment and exit answers. -/
theorem cli3Next_env (q : Clk3) (f : FnName) (hf : f ∈ env3X) (a : List Val)
    (r : Option (List Val)) : cli3Next q (.imp f a r) = q := by
  simp only [env3X, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [cli3Next, getEnv3, getArgs3, getCwd3, exit3, exitCode3, monoNow3, waitUntil3, waitFor3']

theorem to2_to3 (f : FnName) (hf : f ∈ env2X) : to2 (to3 f) = f ∧ to3 f ∈ env3X := by
  refine ⟨?_, to3_mem f hf⟩
  simp only [env2X, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    simp [to2, to3, getEnv3, getArgs3, getCwd3, exit3, exitCode3, getEnv2, getArgs2, getCwd2,
      exit2, exitCode2]

/-- **0.3 over 0.2.** -/
theorem env3Over2_model (E : Env3) {Y : Sig.{0}} {η : Host Y env2X}
    (hη : (hostSat (env2Th E).Accepts).holds η) :
    (hostSat (cli3Th E).Accepts).holds (link η (ofSBody env3Over2 ())) :=
  fwdT_model (R := fun _ qG => qG = ({} : Clk3))
    { init := rfl
      step := fun _ qG f a r hf hR hok =>
        ⟨by rw [cli3Ok_env E qG f hf]; exact hok, by rw [cli3Next_env qG f hf]; exact hR⟩ } hη

/-- **0.2 over 0.3.** -/
theorem env2Over3_model (E : Env3) {Y : Sig.{0}} {η : Host Y env3X}
    (hη : (hostSat (cli3Th E).Accepts).holds η) :
    (hostSat (env2Th E).Accepts).holds (link η (ofSBody env2Over3 ())) :=
  fwdT_model (R := fun qT _ => qT = ({} : Clk3))
    { init := rfl
      step := fun qT _ f a r hf hR hok => by
        have h := to2_to3 f hf
        have he : cli3Ok E qT (.imp (to3 f) a r) = env2Ok E () (.imp f a r) := by
          rw [cli3Ok_env E qT (to3 f) h.2, h.1]
        exact ⟨by rw [← he]; exact hok, by rw [cli3Next_env qT (to3 f) h.2]; exact hR⟩ } hη

end Silmaril.Wasi.Versions.EnvOver
