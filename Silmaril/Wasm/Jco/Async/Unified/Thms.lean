module

public import Silmaril.Wasm.Jco.Async.Unified.Defs
public import Silmaril.Wasm.Jco.Async.Frame.Thms
public import Silmaril.Wasm.Jco.Styles.Unified.Thms
import Silmaril.Proofs.Wasm.Jco.Async.Unified

/-!
# Async lifts in the unified wrapper: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Async.Unified`.

* **`awrapU_correct`**: for a module with a lawful memory that conforms to the C convention and
  to the multi-value style, and a world whose async functions take the plain path
  (`AMeta.AsyncPlain`), `awrapU md enc` behaves as `aspecU`. Synchronous functions follow the
  unified convention (spilling, wide results, encoding `enc`) next to the async store. Async
  functions follow `aspecCall`.
* `awrapU_sync_fn`, **`awrapU_async_fn`**: the same function by function. An async function is
  in closed form: the C convention over `M` alongside the runtime's update of the store
  (`aspecCall_async`).
* **`awrapU_awrap`**: with `utf8` and no spilled or wide signatures, `awrapU md .utf8` is
  `awrap md`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Async

variable (M : CoreInst)

/-- **The unified wrapper with async lifts behaves as `aspecU`.** -/
theorem awrapU_correct (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (hP : md.AsyncPlain) (enc : StrEnc) (name : String)
    (vs : List PVal) :
    (awrapU md enc).callExport M name vs = aspecU M md enc name vs :=
  Silmaril.Proofs.Wasm.Jco.Async.Unified.awrapU_correct M md hL hC hMV hP enc name vs

/-- A synchronous function of `awrapU`: the unified convention next to the store. -/
theorem awrapU_sync_fn (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (hP : md.AsyncPlain) (enc : StrEnc) (name : String)
    (sig : Sig) (hf : md.world.find? (·.sig.name == name) = some ⟨sig, none⟩) (vs : List PVal) :
    (awrapU md enc).callExport M name vs = md.sync.specCallU M.withStore enc sig vs := by
  rw [awrapU_correct M md hL hC hMV hP]
  unfold aspecU
  rw [hf]

/-- **An async function of `awrapU`, in closed form.** -/
theorem awrapU_async_fn (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (hP : md.AsyncPlain) (enc : StrEnc) (name : String)
    (sig : Sig) (st : Style) (hf : md.world.find? (·.sig.name == name) = some ⟨sig, some st⟩)
    (vs : List PVal) :
    (awrapU md enc).callExport M name vs = RM.alongside (md.sync.specCall M sig vs) asyncPost := by
  rw [awrapU_correct M md hL hC hMV hP]
  unfold aspecU
  rw [hf]
  exact aspecCall_async M md sig st vs

/-- Without spilled or wide signatures every async function takes the plain path. -/
theorem asyncPlain_of (md : AMeta) (h1 : md.sync.noSpill) (h2 : md.sync.narrow) : md.AsyncPlain :=
  fun _ hs _ => ⟨h1 _ (List.mem_map_of_mem hs), h2 _ (List.mem_map_of_mem hs)⟩

/-- **With `utf8` and no spilled or wide signatures, `awrapU` is `awrap`.** -/
theorem awrapU_awrap (md : AMeta) (hL : MemLawful M) (hC : md.sync.Conforms M)
    (hMV : md.sync.ConformsMV M) (h1 : md.sync.noSpill) (h2 : md.sync.narrow) :
    (awrapU md .utf8).callExport M = (awrap md).callExport M := by
  funext name vs
  rw [awrapU_correct M md hL hC hMV (asyncPlain_of md h1 h2),
    Silmaril.Proofs.Wasm.Jco.Async.Unified.aspecU_aspec M md h1 h2, awrap_correct M md hC]

end Silmaril.Wasm.Jco.Async
