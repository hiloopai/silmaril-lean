module

public import Silmaril.Machine.Abi.OpenMachine.Rel.Defs
public import Silmaril.Proofs.Machine.Abi.OpenMachine.Rel
/-!
# The ABI call relation of a relational machine: what is proved (header)

`Silmaril/Proofs/Machine/Abi/OpenMachine/Rel.lean`, names in `Silmaril.Machine.Abi.OpenMachine`
(`Must.result_of_runsInR` in `Silmaril.X86.RelIsa`).

PROVED (standard axioms):

* `callModelR_ofIsa : callModelR (ofIsa Open.isa) = callModel` (with
  `runsInR_ofIsa_open_iff`, `returnedV_mstate_iff`, `firstReturnR_ofIsa_open_iff`);
* `RelIsa.Must.result_of_runsInR`: a demonic property bounds the end of *every* run that
  avoids a guard until it hits it;
* `callModelR_of_mustC`, `callModelR_of_must`: from a demonic contract `S.Must A`, on every
  `C` with `Le C A` and `Progress C`, an entry state has a `callModelR C` outcome and every
  outcome is a `Spec.ResultV`. This replaces the determinism argument
  (`callModel_subsingleton`) of `callModel_of_strict`;
* `sat_of_outcomes`: the System V satisfaction theorem for any call relation whose outcomes
  carry the FFI-only state and are call results; `sat_of_must`: the institution sentence
  `Contracts.Sat (callModelR C) (within ((sysv o).translate p c) room)` from `S.Must A`;
* rung 01 (`clamp_i32`, `sat_add_u32`): `clamp_must`, `sat_must` (on `ofIsa Open.isa`),
  `clamp_mustLoosen`, `sat_mustLoosen` (on `loosen Open.isa ⊤`); `clamp_i32_satR`,
  `sat_add_u32_satR` (for **every** `C ≤ loosen Open.isa ⊤` with `Progress`);
  `clamp_i32_sat_ofIsa`, `sat_add_u32_sat_ofIsa` (through `callModelR (ofIsa Open.isa)`);
  `clamp_i32_sat_viaR`, `sat_add_u32_sat_viaR` (`clamp_i32_sat`/`sat_add_u32_sat` re-derived
  through `callModelR_ofIsa`, without `callModel_subsingleton`); `clamp_i32_sat_open9`,
  `sat_add_u32_sat_open9` (on `ofIsa Open9.isa`, by `loosen_open9_le_open`);
  `clamp_i32_satR_nonvacuous` (an admitted entry with an outcome on every such `C`);
  `clamp_i32_rejects_idR` (the mutated contract is refuted on `ofIsa Open.isa`; this one
  rewrites the existing `clamp_i32_rejects_id`, so it does depend on the deterministic proof);
* `clamp_argsR`, `sat_argsR`: copies of the unexported `OpenMachine` proof lemmas
  `clamp_args`, `sat_args`;
* review additions: `runsInR_of_le`, `callModelR_mono` (fewer behaviours, fewer outcomes);
  `clamp_i32_sat_ofIsa_must` (directly from `clamp_must` on `ofIsa Open.isa`);
  `clamp_i32_sat_loosen`, `sat_add_u32_sat_loosen` (on `loosen Open.isa ⊤` itself, with
  `progress_loosen`); `clamp_i32_rejects_id_loosen` (the mutated contract refuted on
  `callModelR (loosen Open.isa ⊤)`; it goes through `clamp_i32_rejects_idR`, so it depends on
  the deterministic proof too).

Caveat: `callModelR` records only returned outcomes. `Contracts.Sat (callModelR C)` asks for
one outcome and that every *returned* outcome meets the post; runs of a nondeterministic `C`
that stop or diverge are invisible to it. Demonic termination is in the `Must` hypothesis of
`sat_of_must`, not in the conclusion.
-/
