module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecRefuteE20T

/-!
# The float-only vector operators are not typed in the 2.0 script

Round 3's executable check (`Sim20.EncodeCheck.knownRejectedInstrs`) finds that `hasTyp` rejects
some vector instructions at float shapes. This file proves it, for every `B`, in both
environments of the forward invariant (`simEnv20 B`, which reads `Good20B`'s typing, and
`simEnv20T B`, which reads its steps), for the float operators that have no integer namesake:

* `VUNOP` with `sqrt`, `ceil`, `floor`, `trunc`, `nearest`;
* `VBINOP` with `div`, `min`, `max`, `pmin`, `pmax`;
* `VRELOP` with `lt`, `gt`, `le`, `ge`,

each at `f32x4` and `f64x2` (`FloatOnly`). At fuel 200, `hasTyp` answers `false` (by evaluation),
and fuel monotonicity extends this to every fuel (`not_hasTyp_of_false`). Their integer-shared
namesakes `abs`, `neg` are typed (`hasTyp_abs_neg20`). Consequently:

* **`not_typedA_floatOnly20`**, **`not_typedA_floatOnly20T`**: no such instruction is an
  `admininstr` (or an `instr`) of `simEnv20 B` or `simEnv20T B`;
* **`not_good20B_floatOnly`**: no `Good20B` configuration has such an instruction at the top of
  its code. The forward invariant of rounds 5 and 6, as stated, cannot be extended to these
  vector rules: covering them needs an erratum to the vector operator families, as the `STORE`
  erratum (`StoreFix`) did for stores.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecRefute

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)

set_option maxRecDepth 100000

variable {B : Builtins}

/-- **No float-only vector instruction is an `admininstr` of `simEnv20 B`.** -/
theorem not_typedA_floatOnly20 {i : V2.Instr} (h : FloatOnly i) :
    ¬ TypedV (simEnv20 B) (.varT "admininstr" []) (instrToV i) := fun ht =>
  not_hasTyp_of_false (hasTyp_floatOnly20 h) (ht _ ⟨rfl, rfl, rfl⟩)

/-- Nor an `instr`. -/
theorem not_typedI_floatOnly20 {i : V2.Instr} (h : FloatOnly i) :
    ¬ TypedV (simEnv20 B) (.varT "instr" []) (instrToV i) := fun ht =>
  not_typedA_floatOnly20 h ((Whole.typedV_plain20_iff i).2 ht)

/-- **No float-only vector instruction is an `admininstr` of `simEnv20T B`.** -/
theorem not_typedA_floatOnly20T {i : V2.Instr} (h : FloatOnly i) :
    ¬ TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i) := fun ht =>
  not_hasTyp_of_false (hasTyp_floatOnly20T h) (ht _ ⟨rfl, rfl, rfl⟩)

/-- **No `Good20B` configuration has a float-only vector instruction in its code.** -/
theorem not_good20B_floatOnly {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
    {c : Config H} (hg : StoreBulk.Good20B hn P c) {i : V2.Instr} (h : FloatOnly i) :
    Admin.plain i ∉ c.code := by
  intro hm
  have hc := hg.typ.code
  have he : StoreDeep.eD i = i := by
    rcases i <;> simp only [FloatOnly] at h <;> rfl
  have hmem : instrToV i ∈ adminsToV (c.code.map StoreDeep.eDA) := by
    rw [Whole.adminsToV_map]
    refine List.mem_map.2 ⟨.plain i, List.mem_map.2 ⟨.plain i, hm, by simp [he]⟩, rfl⟩
  exact not_typedA_floatOnly20 h (Sim.typedV_list_iff.1 hc _ hmem)

end Silmaril.Wasm.SpecTec.Sim20.VecRefute
