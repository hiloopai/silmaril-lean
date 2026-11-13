module

public import Silmaril.Wasm.Jco.Resource.Merge.Defs
public import Silmaril.Wasm.Jco.Resource.Log.Thms
public import Silmaril.Proofs.Wasm.Jco.Resource.Merge.Inv

/-!
# Merging a resource manager: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Resource.Merge.{Basic,Lower,StepA,Post,Main,Inv}`.

Hypotheses throughout: `md.erase.Conforms M` (as in `wrap_correct`), `md.AllocTotal M` (the
allocator never diverges) and `md.MergeOk` (no export the glue calls has a manager name; resource
type numbers fit in an `i32`).

* **`merged_eq_specHost`**: the merged module `merged md` over `link M (mgr H)`, read at the
  world's types (`MetaR.hostView`; handles are `u32`s of the manager's table), **equals**
  `specHost`: the caller lifting its arguments from its own canonical table, `M` under the
  rep-passing convention, the caller lowering an `own` result into its table. It is an equation of
  relations, for every table implementation `H` (no lawfulness needed); the manager's table plays
  the caller's table, operation for operation. Totality of the allocator is needed because the
  caller lifts all arguments before the callee runs, while the merged module converts handles after
  lowering the other arguments: with a diverging allocator and a dead handle, the canonical caller
  traps and the merged module diverges.
* **`canonHost_sim`**: the canonical counterpart (`canonHost`: the caller with its own table
  calling `wrapR md`, whose instance has its own table) simulates `specHost`; the component's table
  ends interchangeable with its start (`wrapR_correct`). Needs `H` lawful, the invariant and room.
* **`merged_sim`**: hence the canonical counterpart simulates the merged module: the merged
  module with its resource manager has the same behaviour at the world as the canonical handle
  tables (the caller's and the component's).
* **`merged_protocol`**: with the recording tables `logTab` as the manager's tables, every
  returning call of the merged module from a table satisfying the invariant ends in one, and the
  manager's whole history is accepted by the handle protocol in both orientations.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Resource (handleProto Role tableEv)

/-- **The merged module is the caller's canonical table in front of `M`.** -/
theorem merged_eq_specHost (M : CoreInst) (H : HTab) (md : MetaR) (hC : md.erase.Conforms M)
    (hT : md.AllocTotal M) (hok : md.MergeOk) (name : String) (vs : List RVal) :
    md.hostView ((merged md).callExport (link M (mgr H))) name vs = specHost H M md name vs :=
  Silmaril.Proofs.Wasm.Jco.Res.merged_eq_specHost hC hT hok name vs

/-- **The canonical counterpart simulates `specHost`.** -/
theorem canonHost_sim (M : CoreInst) (H : HTab) (hH : H.Lawful) (md : MetaR)
    (hC : md.erase.Conforms M) (name : String) (vs : List RVal) {tc : H.T} (hI : H.Inv tc)
    (hR : md.Room H tc name) :
    Sim (canonHost H M md name vs) (specHost H M md name vs) tc
      fun a b t' => a = b ∧ H.Same tc t' :=
  Silmaril.Proofs.Wasm.Jco.Res.canonHost_sim hH hC name vs hI hR

/-- **The merged module behaves as the canonical handle tables.** -/
theorem merged_sim (M : CoreInst) (H : HTab) (hH : H.Lawful) (md : MetaR)
    (hC : md.erase.Conforms M) (hT : md.AllocTotal M) (hok : md.MergeOk) (name : String)
    (vs : List RVal) {tc : H.T} (hI : H.Inv tc) (hR : md.Room H tc name) :
    Sim (canonHost H M md name vs)
      (md.hostView ((merged md).callExport (link M (mgr H))) name vs) tc
      fun a b t' => a = b ∧ H.Same tc t' := by
  rw [merged_eq_specHost M H md hC hT hok]
  exact canonHost_sim M H hH md hC name vs hI hR

/-- **The merged module respects the resource protocol.** -/
theorem merged_protocol (M : CoreInst) (md : MetaR) (hC : md.erase.Conforms M)
    (hT : md.AllocTotal M) (hok : md.MergeOk) (name : String) (vs : List RVal)
    {s s' : M.St} {t t' : logTab.T} {a : Option RVal} (hI : logTab.Inv t)
    (h : md.hostView ((merged md).callExport (link M (mgr logTab))) name vs (s, t)
      (.ok a (s', t'))) :
    logTab.Inv t' ∧ ∀ r, (handleProto ℕ r).Accepts (t'.2.map tableEv) := by
  have hI' : logTab.Inv t' :=
    Silmaril.Proofs.Wasm.Jco.Res.keeps_merged M logTab_lawful md hC hT hok name vs s t a s' t' hI h
  exact ⟨hI', logTab_accepts hI'⟩

end Silmaril.Wasm.Jco.Res
