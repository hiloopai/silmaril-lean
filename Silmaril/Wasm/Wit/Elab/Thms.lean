module

public import Silmaril.Wasm.Wit.Elab.Defs
public import Silmaril.Proofs.Wasm.Wit.Elab.Sound
public import Silmaril.Proofs.Wasm.Wit.Elab.Bridge
public import Silmaril.Proofs.Wasm.Wit.Elab.Iface
public import Silmaril.Raw.Wasm.Wit.Elab.Complete
public import Silmaril.Raw.Wasm.Wit.Elab.Errors

/-!
# Elaboration: theorems

Proofs in `Silmaril.Proofs.Wasm.Wit.Elab`:

* `elaborate_sound : elaborate U p fs = .ok (P, deps) →
  Valid (Universe.gate fs U) ∧ P.Valid deps ∧ P.NamesUnique ∧ P.name = pkgName p`;
* `elaborate_decode`: the bytes `encodePackage deps P` of an elaborated package
  decode to `P.canon` (`decodePackage_encodePackage_canon` applies to surface
  packages); `elaborate_reencode`: encode ∘ decode = id on them when
  `P.canon = P`;
* `elaborate_world_projects`: Project ∘ encodePackage ∘ elaborate gives back
  each world (`Bridge.world_project_encodePackage`).

Completeness (`Silmaril.Raw.Wasm.Wit.Elab.Complete`):

* `elaborate_complete : ElaborateComplete`: on a valid gated universe whose
  package has an interface or a world, `elaborate` succeeds as soon as the worlds
  of the package elaborate; the binary checks of `elaborate` (`Package.validB`,
  `Package.namesUniqueB`) never fail on a valid universe. The pieces:
  `elabBody_good` (bodies), `elabWorldItems_good` and `elabWorld_good` (worlds,
  including `include` renaming), `elabEnv_good` and `elabEnv_ranked` (the `use`
  graph ranks interface ids, `ifaceName_id_inj`).

* `elaborate_error`, `elaborate_ok_or_worldError` (`Silmaril.Raw.Wasm.Wit.Elab.Errors`):
  the hypothesis that the worlds elaborate is exactly wit-parser's world conditions.
  On a valid gated universe `elaborate` fails only with a `WorldError` (an item
  defined twice, also after `include … with`; a stability mismatch; an interface
  both imported and exported by an export's dependencies; an interface exported
  twice). World scopes and inline interfaces are always sorted (`preItems_ok`) and
  the include fuel always suffices (`elabWorld_error`, `world_rank_bounded`).

Earlier steps:

* `toposort_perm` (the order is a permutation of the scope) and
  `toposort_complete` (`toposort` succeeds on ranked scopes);
* `elabTypes_isSome`: the types of a scope with distinct names, resolved
  references and an acyclic type graph have a topological order;
* `elabBody_iface_isSome`, `elabEnv_ok : Valid U → ∃ env, elabEnv c = .ok env`
  (with `c.U = U`): every interface of a valid universe is elaborated.

See `docs/projects/wasm-components.md` for what is open.
-/
