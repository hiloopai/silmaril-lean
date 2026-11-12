module

public import Silmaril.Wasm.Wac.Bridge.DecodeAnon.Thms
public import Silmaril.Wasm.Wac.Bridge.DecodeIface.Thms
public import Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnonIface

/-!
# WAC bridge: decoding inverts encoding on interfaces of functions over anonymous types

`Bridge.DecodeIface.decode_encode_iface` proves `decode ∘ encode = id` for packages of
functions over primitive value types and interfaces (instances) of such functions;
`Bridge.DecodeAnon.decode_encode_anon` for functions over anonymous value types. This
module combines the two:

* `decode_encode_anon_iface`: packages whose imports and exports are functions over
  anonymous value types (`list`, fixed-size `list`, `map`, `option`, `result`, `tuple`,
  `future`, `stream`, nested over primitives) and instances exporting such functions are
  read back by `pkgOfWorld` as the same items, an instance with the identifier its name
  carries (`DecodeIface.fixEx`), with no nominal definitions;
* `decode_encode_anon_iface_id`: exactly the same items when every instance already has
  the identifier of its name;
* `items2_of_items1`: the fragment contains that of `decode_encode_iface`.

Inside an instance type the encoder starts a fresh, non-sharing scope, and the decoder a
fresh nested scope; the anonymous types of the instance's functions are defined there.
The simulation is in `Silmaril.Proofs.Wasm.Wac.Bridge.DecodeAnonIface`. **Not covered**:
named type references, handles, records, variants, enums and flags, type items,
resources, nested instances inside instances, component items, and the byte level of
`decodePkg`.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Bridge

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Binary (Ty Sig)
open DecodeIface (fixK fixEx IdsOk fixEx_id)
open DecodeAnon

namespace DecodeAnonIface

attribute [local simp] DecodeEnc.ok_bind DecodeEnc.pure_ok

/-- **Decoding inverts encoding** on packages of functions over anonymous value types and
interfaces of them. -/
theorem decode_encode_anon_iface {is es : Externs} (his : Items2 is) (hes : Items2 es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := fixEx is, exports := fixEx es }, []) := by
  obtain ⟨σ1, E1, δ1, hr1, hd1, hm1, -, hn1, hreads1⟩ := imports3_run is his _ _ match3_empty
  obtain ⟨σ2, E2, δ2, hr2, hd2, -, -, hn2, hreads2⟩ := exports3_run es hes σ1 δ1 hm1
  refine ⟨σ2, by simp [hr1, hr2], ?_⟩
  have hdec : (decCDecls σ2.decls [] []).run {} = .ok ((fixEx is, fixEx es), δ2) := by
    have e : σ2.decls = E1 ++ (E2 ++ []) := by rw [hd2, hd1]; simp
    rw [e, hreads1, hreads2]
    simp [decCDecls]
  have hnom : δ2.nom = [] := by rw [hn2, hn1]
  simp [pkgOfWorld, hdec, hnom]
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  all_goals
    obtain ⟨⟨n, k⟩, hk, e⟩ := List.mem_map.1 hab
    have e2 : fixK n k = b := congrArg Prod.snd e
    rcases hes (n, k) hk with ⟨s, ek, -⟩ | ⟨i, fs, ek, -⟩
    · have ek' : k = .func s := ek
      rw [← e2, ek']; rfl
    · have ek' : k = .inst i fs := ek
      rw [← e2, ek']; rfl

/-- **`decode ∘ encode = id`** on such packages when every instance already has the
identifier of its name. -/
theorem decode_encode_anon_iface_id {is es : Externs} (his : Items2 is) (hes : Items2 es)
    (hi : IdsOk is) (he : IdsOk es) :
    ∃ σ : Scope, ((do importDecls is; exportDecls es : TM Unit)).run { share := true } = .ok ((), σ) ∧
      pkgOfWorld σ.decls = .ok ({ imports := is, exports := es }, []) := by
  obtain ⟨σ, h1, h2⟩ := decode_encode_anon_iface his hes
  exact ⟨σ, h1, by rw [h2, fixEx_id hi, fixEx_id he]⟩

theorem anonSig_of_primSig {s : Sig} (hs : DecodeEnc.PrimSig s) : AnonSig s :=
  ⟨fun q hq => anon_of_prim (hs.1 q hq), fun t ht => anon_of_prim (hs.2 t ht)⟩

/-- The fragment of `DecodeIface.decode_encode_iface` is contained in this one. -/
theorem items2_of_items1 {es : Externs} (h : DecodeIface.Items1 es) : Items2 es := fun p hp => by
  rcases h p hp with ⟨s, e, hs⟩ | ⟨i, fs, e, hfs⟩
  · exact Or.inl ⟨s, e, anonSig_of_primSig hs⟩
  · exact Or.inr ⟨i, fs, e, anonFns_of_primFns hfs⟩

end DecodeAnonIface

end Silmaril.Wasm.Wac.Bridge
