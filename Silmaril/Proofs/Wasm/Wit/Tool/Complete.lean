module

public import Silmaril.Wasm.Wit.Tool.Defs
public import Silmaril.Proofs.Wasm.Wit.Tool
public import Silmaril.Wasm.Wit.Elab.Golden.Defs
public meta import Silmaril.Wasm.Wit.Elab.Golden.Defs
public meta import Silmaril.Wasm.Wit.Tool.Defs

/-!
# `wasm-wit check`: completeness relative to the environment a binary shows

`check` decodes the package `p` and the interfaces the binary shows
(`decodeEnv`), then decides `Package.Valid`, `NamesUnique`, `p.canon = p` and
whether `encodePackage (decodeEnv b) p` gives the bytes back.

* `check_ok_iff`: `check` passes **iff** the bytes decode to a valid, canonical
  package with distinct names whose encoding in the environment the bytes show
  is the bytes. This is soundness (`check_ok_sound`) and completeness relative to
  `decodeEnv`.
* `check_complete_of_env`: `check` passes on `encodePackage deps p` for every
  valid canonical `p` with distinct names, provided the environment the bytes show
  (`decodeEnv`) validates `p` and re-encodes it to the same bytes.
* `Task.check_complete` (open, frozen): the same without the two conditions on
  `decodeEnv`. It needs a simulation proof for `decodeEnv` (the interfaces a
  binary shows: full bodies of world imports/exports, types of `use`d
  interfaces) like the one `decodeItems_encodeItems` gives for the package. No
  counterexample is known: `check` passes on the encodings of the elaboration
  goldens (`#guard` below) and on the seven WASI 0.2.12 packages
  (`tests/wasm-wit/differential.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Tool

open Silmaril.Wasm.Wit.Binary (Package Env decodePackage decodeEnv encodePackage)

/-- **`check` passes iff** the bytes are the encoding, in the environment they
show, of a valid canonical package with distinct names that they decode to. -/
theorem check_ok_iff {b : ByteArray} :
    (∃ r, check b = .ok r ∧ r.ok = true) ↔
      ∃ (p : Binary.Package) (env : Env), decodePackage b = .ok p ∧ decodeEnv b = .ok env ∧ p.Valid env ∧ p.NamesUnique ∧
        p.canon = p ∧ encodePackage env p = .ok b := by
  constructor
  · rintro ⟨r, h, hok⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := check_ok_sound h hok
    exact ⟨_, _, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨p, env, h1, h2, h3, h4, h5, h6⟩
    have hd : decode b = .ok ⟨p, env⟩ := decode_eq_ok.2 ⟨h1, h2⟩
    cases hch : check b with
    | error e => unfold check at hch; rw [hd] at hch; cases hch
    | ok r =>
      refine ⟨r, rfl, ?_⟩
      obtain ⟨hd', hV, hU, hC, hR, hF⟩ := check_eq_ok hch
      rw [hd] at hd'
      have he : r.decoded = ⟨p, env⟩ := (Except.ok.inj hd').symm
      rw [he] at hV hU hC hR
      simp only [Report.ok, Bool.and_eq_true]
      exact ⟨⟨⟨hV.2 h3, hU.2 h4⟩, hC.2 h5⟩, hF.2 ((hR b).2 h6)⟩

/-- **Completeness of `check`**, given that the environment the bytes show
validates the package and re-encodes it to the same bytes. -/
theorem check_complete_of_env {deps : Env} {p : Binary.Package} {b : ByteArray} (hv : p.Valid deps)
    (hu : p.NamesUnique) (hc : p.canon = p) (hb : encodePackage deps p = .ok b) {env : Env}
    (he : decodeEnv b = .ok env) (hv' : p.Valid env) (hb' : encodePackage env p = .ok b) :
    ∃ r, check b = .ok r ∧ r.ok = true := by
  have hd : decodePackage b = .ok p := by
    rw [Binary.decodePackage_encodePackage_canon hv hu hb, hc]
  exact check_ok_iff.2 ⟨p, env, hd, he, hv', hu, hc, hb'⟩

/-- Open: `check` passes on the encoding of every valid canonical package with
distinct names, in any environment `deps` in which it encodes. What is missing is
that the environment the bytes show (`decodeEnv`) validates the package and
re-encodes it to the same bytes (`check_complete_of_env`). -/
def Task.check_complete : Prop :=
  ∀ (deps : Env) (p : Binary.Package) (b : ByteArray), p.Valid deps → p.NamesUnique → p.canon = p →
    encodePackage deps p = .ok b → ∃ r, check b = .ok r ∧ r.ok = true

/-! ## Evidence: `check` passes on the elaboration goldens -/

/-- `check` passes on bytes. -/
def checkPasses (b : ByteArray) : Bool :=
  match check b with
  | .ok r => r.ok
  | .error _ => false

#guard checkPasses Elab.Golden.ioBytes
#guard checkPasses Elab.Golden.appBytes
#guard checkPasses Elab.Golden.inclBytes

end Silmaril.Wasm.Wit.Tool
