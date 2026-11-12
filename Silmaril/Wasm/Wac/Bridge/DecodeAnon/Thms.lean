module

public import Silmaril.Wasm.Wac.Bridge.DecodeEnc.Thms
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnon

/-!
# WAC bridge: decoding inverts encoding on functions over anonymous value types

`Bridge.DecodeEnc.decode_encode` proves `decode ∘ encode = id` for packages of functions
over primitive value types. This module extends it to **anonymous value types**
(`DecodeAnon.Anon`): `list`, fixed-size `list`, `map`, `option`, `result`, `tuple`,
`future` and `stream`, nested arbitrarily over primitives. The encoder defines each
anonymous type once per scope (`defVal` and its cache) and refers to it by index; the
decoder reads the definitions back (`decDefVal`) and the references (`decVal`).

* `decode_encode_anon`: the declarations the encoder writes for the imports `is` and
  exports `es` (in a sharing scope, as for a package's component type) are read back by
  `pkgOfWorld` as exactly those imports and exports, with no nominal definitions;
* `anonFns_of_primFns`: the fragment contains that of `decode_encode`.

The simulation is in `Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnon`. **Not covered**: named
type references, handles (`own`/`borrow`, the cache `hcache`), records, variants, enums
and flags (the nominal table), type items, resources, instance and component items at
this level, and the byte level of `decodePkg` (`Component.Binary.parse`,
`Wit.Project.projectI`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)

namespace DecodeAnon

attribute [local simp] DecodeEnc.ok_bind DecodeEnc.pure_ok

/-- **Decoding inverts encoding** on packages of functions over anonymous value types. -/
theorem decode_encode_anon {is es : Externs} (his : AnonFns is) (hes : AnonFns es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := is, exports := es }, []) := by
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, -, hn1, hreads1⟩ := imports_sim is his _ _ matchA_empty
  obtain ⟨σ2, E2, δ2, hr2, hd2, -, -, hn2, hreads2⟩ := exports_sim es hes σ1 δ1 hm1
  refine ⟨σ2, by simp [hr1, hr2], ?_⟩
  have hdec : (decCDecls σ2.decls [] []).run {} = .ok ((is, es), δ2) := by
    have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
    rw [e, hreads1, hreads2.1]
    simp [decCDecls]
  have hnom : δ2.nom = [] := by rw [hn2, hn1]
  simp [pkgOfWorld, hdec, hnom]
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨s, e, -⟩ := hes (a, b) hab; rw [show b = .func s from e]
  · obtain ⟨s, e, -⟩ := hes (a, b) hab; rw [show b = .func s from e]

theorem anon_of_prim {t : Ty} (h : DecodeEnc.PrimTy t) : Anon t := by
  obtain ⟨p, rfl⟩ := h
  exact .prim p

/-- The fragment of `DecodeEnc.decode_encode` is contained in this one. -/
theorem anonFns_of_primFns {es : Externs} (h : DecodeEnc.PrimFns es) : AnonFns es := fun p hp => by
  obtain ⟨s, e, hs⟩ := h p hp
  exact ⟨s, e, fun q hq => anon_of_prim (hs.1 q hq), fun t ht => anon_of_prim (hs.2 t ht)⟩

end DecodeAnon

end Silmaril.Wasm.Wac.Bridge
