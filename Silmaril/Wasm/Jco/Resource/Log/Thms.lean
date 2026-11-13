module

public import Silmaril.Wasm.Jco.Resource.Log.Defs
public import Silmaril.Wasm.Jco.Resource.Wrap.Thms
public import Silmaril.Proofs.Wasm.Jco.Resource.Log

/-!
# Handle tables that record their history: results

Proofs in `Silmaril.Proofs.Wasm.Jco.Resource.Log`.

* `logTab_lawful`: the canonical handle tables with their history are lawful, so
  `wrapR_correct` applies to them.
* `logTab_accepts`: the history of a table satisfying the invariant is accepted by the handle
  protocol `handleProto ℕ r` of `Silmaril.Wasm.Resource.Handle`, for both roles (`r = provider`:
  `resource.new`/`lower_own` never return a live handle; `r = client`: no use or drop of a dead
  handle). This is `table_steps_accepts` of `Silmaril.Wasm.Resource.Table`.
* **`wrapR_protocol`**: after a call of `wrapR md` that returns, from a table satisfying the
  invariant (in particular `logEmpty`, or the table after earlier calls), the table's whole
  history (every `lower_own`, `resource.rep`, `resource.drop`, `resource.new` and `lift_own` so
  far) is accepted by the handle protocol in both orientations, and the invariant holds again.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Resource (handleProto Role tableEv)

theorem logTab_lawful : logTab.Lawful := Silmaril.Proofs.Wasm.Jco.Res.logTab_lawful

theorem logEmpty_inv : logTab.Inv logEmpty := Silmaril.Proofs.Wasm.Jco.Res.logEmpty_inv

theorem logTab_accepts {t : logTab.T} (hI : logTab.Inv t) (r : Role) :
    (handleProto ℕ r).Accepts (t.2.map tableEv) :=
  Silmaril.Proofs.Wasm.Jco.Res.logTab_accepts hI r

/-- **The wrapper respects the resource protocol.** -/
theorem wrapR_protocol (M : CoreInst) (md : MetaR) (hC : md.erase.Conforms M) (name : String)
    (vs : List RVal) {t : logTab.T} (hI : logTab.Inv t) (hR : md.Room logTab t name)
    {s s' : M.St} {a : Option RVal} {t' : logTab.T}
    (h : (wrapR md).callExport M logTab name vs (s, t) (.ok a (s', t'))) :
    logTab.Inv t' ∧ ∀ r, (handleProto ℕ r).Accepts (t'.2.map tableEv) := by
  obtain ⟨_, _, _, hS⟩ := (wrapR_correct M logTab logTab_lawful md hC name vs hI hR).fwd s a s' t' h
  exact ⟨hS.1, logTab_accepts hS.1⟩

end Silmaril.Wasm.Jco.Res
