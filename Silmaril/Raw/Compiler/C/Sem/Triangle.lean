module

public import Silmaril.Compiler.Core.Semantics.Defs
public import Silmaril.Compile.Category.Factor
public import Silmaril.Compiler.C.Sem.C0.Defs
public import Silmaril.Compiler.Target.Runtime.Defs
@[expose] public section

/-!
# The Ail → Core → Mir triangle, at the level of validity

`Core.cAC S ≫ Core.cCM cfg ctl = Core.cAM S cfg ctl` (`Core.cAC_comp_cCM`): going through Core
is going to Mir directly. This file instantiates the factorization theorem
(`Silmaril.Compile.Category.Factor`) on the triangle: if an elaboration `elaborate` of typed
Ail into Core preserves the behaviours of a C semantics `S` on a fragment `F` (Core *realises*
`S` there), then **every** valid direct lowering Ail → Mir of a program of `F` factors through
a valid Ail → Core and a valid Core → Mir (`factor`), and the two routes have the same valid
compilations (`valid_iff`).

For `S = C0.sem` and `F = C0.fragment` the hypothesis is the campaign target
`Targets.c0_core_realises` for the elaboration chosen (Cerberus's, trusted, or a C0-only Lean
elaboration that is proved).

`mirConfig` and `ctlAddress` are ccomp's (`Silmaril.Compile.Target.Runtime`): the control
block `__ccomp_ctl` is the first data object of every link, at `dataBase`.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category Silmaril.Compile.Core
open CategoryTheory

/-- ccomp's memory configuration of a link. -/
def mirConfig : Mir.Config := ⟨Target.layout, Target.memSize⟩

/-- The address of ccomp's control block (the first data object of every link). -/
def ctlAddress : Nat := Target.dataBase

/-- An elaboration realises a C semantics on a fragment when it preserves its behaviours. -/
theorem realises_of_beh {S : Semantics} {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) : Realises (cAC S) F elaborate := by
  refine ⟨fun _ _ => rfl, fun p hp => ?_⟩
  change Core.beh (elaborate p) = (cAC S).lift (S p)
  rw [h p hp]
  ext o
  exact ⟨fun ho => ⟨o, ho, rfl⟩, fun ⟨_, ho, e⟩ => e ▸ ho⟩

/-- **Factorization of direct lowerings through Core.** If the elaboration preserves `S` on
`F`, every valid lowering of a program of `F` to Mir factors through a valid Ail → Core and a
valid Core → Mir. -/
theorem factor {S : Semantics} {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) (cfg : Mir.Config) (ctl : Nat)
    {p : Silmaril.Cerberus.Ail.TypedProgram} (hp : p ∈ F) {m : Array Mir.Unit}
    (hv : Valid (cAM S cfg ctl) p m) :
    Valid (cAC S) p (elaborate p) ∧ Valid (cCM cfg ctl) (elaborate p) m :=
  (realises_of_beh h).factor hp (by rwa [cAC_comp_cCM])

/-- On the fragment, the valid direct lowerings are exactly the composites of valid
lowerings through Core. -/
theorem valid_iff {S : Semantics} {F : Set Silmaril.Cerberus.Ail.TypedProgram}
    {elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program}
    (h : ∀ p ∈ F, Core.beh (elaborate p) = S p) (cfg : Mir.Config) (ctl : Nat)
    {p : Silmaril.Cerberus.Ail.TypedProgram} (hp : p ∈ F) (m : Array Mir.Unit) :
    Relation.Comp (Valid (cAC S)) (Valid (cCM cfg ctl)) p m ↔ Valid (cAM S cfg ctl) p m := by
  have := (realises_of_beh h).valid_comp_iff (cCM cfg ctl) hp m
  rwa [cAC_comp_cCM] at this

/-! ## ccomp's front end, as a function -/

/-- ccomp's Mir units of a single typed-Ail translation unit, without the C library: the
runtime unit, then the definitions reachable from `main` (the `link` path of
`Silmaril.Compile.C.Main`). -/
def ccompMir (p : Silmaril.Cerberus.Ail.TypedProgram) : Option (Array Mir.Unit) :=
  match Silmaril.Compile.Forks.Csem.C.compileReachableUnits #[{ tag := "u1", prog := p }] ["main"] with
  | .ok units =>
    match (units.flatMap (·.funcs)).find? (·.name == "main") with
    | some main => some (#[Target.unit main.params.length main.results] ++ units)
    | none => none
  | .error _ => none

/-- The external functions a program calls from the functions reachable from `main`. -/
def C0.externals (p : Silmaril.Cerberus.Ail.TypedProgram) : List String :=
  let P := C0.prepare p
  match P.main with
  | none => []
  | some m =>
    let live := C0.reachable P [m]
    (live.flatMap fun f => match P.funcs[f]? with
      | some fd => C0.callsS fd.body
      | none => []).filterMap fun g =>
        if P.funcs.contains g then none else some ((P.names[g]?).getD "?")

end Silmaril.Compile.C.Sem
