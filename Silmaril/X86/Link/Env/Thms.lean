module

public import Silmaril.X86.Link.Env.Defs
public import Silmaril.Proofs.X86.Link.Env.Compose

/-! # Link environments: theorems (header)

PROVED (standard axioms; proofs in `Silmaril.Proofs.X86.Link.Env.Compose`, namespace
`Silmaril.X86.Link.Env`), generic in the logic:
* `TU.Sat.toSatEnv`: `u.Sat L relocate → u.SatEnv L I Γ Own.empty relocate`, for every `I`
  and `Γ`. `TU.Sat.satAt` (the constant family satisfies `UnitFam.SatAt` everywhere) and
  `UnitFam.SatAt.toSatEnv` (no own entries).
* **`link_compose_env`**: the induction of `link_compose` on the step index with a code
  environment `Γ`. Hypotheses: a successful `link` of the families' objects;
  `AbiCompatible` and `ImportsClosed` of the instantiated units `UnitFam.inst`; each family's
  `UnitFam.SatEnv` **only** at `restrict layout slot` and `σ* = UnitFam.linkValuation`; every
  Γ entry an own entry (`ownAt owns slot` at the link) or an assumed external entry
  (`extEnv`, safe at every index); every own entry in Γ. Conclusion, for every `n`: every
  export at its `exportAddr` is `L.Safe n`, and `Env.Safe L I Γ n ctx`.
* `link_compose_at`: `link_compose_env` with `Γ = ∅`, for families with `UnitFam.SatAt`.
* `link_compose_of_at`: the original `Contract.link_compose`, re-derived from
  `link_compose_at` on constant families.
* Families: `UnitFam.object_eq`, `inst_getElem?`, `inst_getElem?_some`, `inst_map_object`,
  `inst_const`, `map_const_object`; `ownAt_nil`.
* Function pointers: `FnPtr.of_mem`, `FnPtr.safe` (a `FnPtr` for `S` is `L.Safe n` for `S`
  when Γ is), `FnPtr.sub` (for a transitive `Sub`), `Env.Safe.mono`, and `fnptr_dup`
  (`fnptr = fnptr ∗ fnptr`: pure, so persistent without a modality).

Assumed: nothing beyond the stated hypotheses. Not here: `icall_rule` and the indirect-call
step laws, the `FnSpec` instance of these environments, and any unit with a non-empty own
environment on real compiled code.
-/
