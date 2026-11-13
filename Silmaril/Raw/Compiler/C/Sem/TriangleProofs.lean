module

public import Silmaril.Compiler.C.Sem.TargetsTriangle.Defs
public import Silmaril.Compiler.C.Sem.ElabC1Witness.Defs
@[expose] public section

/-!
# The C0 triangle: proofs

`Targets.ccomp_factors_through_core_c0` (`TargetsTriangle.lean`) has two clauses: a program
accepted by `elabC0`, and universal factorization.

* The universal clause (`ccomp_factors_through_core_c0_forall`) follows from `checkC0_sound`
  and `factor_elabC0`.
* `elabC0` accepts a program, by kernel evaluation of a minimal `main` (`elabC0_nonempty`, the
  technique of the C2 Core proofs: abstract HashMap laws, never the platform-dependent table
  internals).

`checkC0` cannot be evaluated in a proof: it runs ccomp (the `partial def`s of
`Silmaril.Compile.C.ToMir` and `Types.ofCtype`) on `main` and decodes `runtime/libc.ail` with the
`partial def` decoders of `Silmaril.Cerberus.Ail.Codec`, all opaque to the kernel. Its
non-vacuity is the evaluator's corpus gate, which is why the existence clause names `elabC0`
only.

The C1 triangle uses the checked C1 elaboration and its kernel-checked acceptance
witness (`ElabC1Witness.lean`), with the same generic factorization lemma.
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Compile.Category

/-- **The universal clause of the C0 triangle**: when `checkC0` accepts `p` and `elabC0`
answers `q`, ccomp's Mir for `p` linked with its C library has a behaviour and is the composite
of a valid Ail → Core step to `q` and a valid Core → Mir step from `q`. -/
theorem ccomp_factors_through_core_c0_forall {p : Silmaril.Cerberus.Ail.TypedProgram}
    {q : Silmaril.Cerberus.Core.Dynamics.Program} (hc : checkC0 p = true) (he : elabC0 p = some q) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAC C0.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
      (Mir.beh mirConfig us).Nonempty := by
  obtain ⟨us, hus, hv, hne⟩ := checkC0_sound hc
  obtain ⟨h₁, h₂⟩ := factor_elabC0 he mirConfig ctlAddress hv
  exact ⟨us, hus, h₁, h₂, hne⟩

namespace ElabC0

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- A minimal defined `main` (`int main(void) { return 0; }`'s shape, returning nothing). -/
private def witnessProgram : TypedProgram :=
  let main : Sym := ⟨⟨[]⟩, 1, .id "main"⟩
  (some main, {
    declarations := [], objectDefinitions := [],
    functionDefinitions := [(main,
      ⟨.unknown, 0, ⟨[]⟩, [], .mk .unknown ⟨false, none⟩ ⟨[]⟩ .returnVoid⟩)],
    staticAssertions := [], tagDefinitions := [], externIdmap := [],
    typedefAttributes := [], loopAttributes := [], cnFunctions := [],
    cnLemmata := [], cnPredicates := [], cnDatatypes := [],
    cnDeclSpecs := [], cnIdents := [] })

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity
  Std.HashMap.contains_emptyWithCapacity Std.HashMap.contains_insert
  Std.HashMap.getElem?_emptyWithCapacity
  Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.contains_emptyWithCapacity Std.HashSet.contains_insert
private theorem size_insert_bool {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.mem_iff_contains] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))
attribute [local cbv_eval] size_insert_bool
private theorem witness_accepted : (elabC0 witnessProgram).isSome = true := by
  cbv

/-- The C0 Core elaboration accepts at least one program, proved by the kernel. -/
theorem elabC0_nonempty : ∃ (p : TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC0 p = some q := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp witness_accepted
  exact ⟨witnessProgram, q, hq⟩

end ElabC0

end Silmaril.Compile.C.Sem

namespace Silmaril.Compile.Targets.Proofs

theorem ccomp_factors_through_core_c0 : Targets.ccomp_factors_through_core_c0 :=
  ⟨C.Sem.ElabC0.elabC0_nonempty, fun _ _ hc he => C.Sem.ccomp_factors_through_core_c0_forall hc he⟩

/-- The checked C1 elaboration supplies the same factorization as C0. -/
theorem ccomp_factors_through_core_c1 : Targets.ccomp_factors_through_core_c1 := by
  refine ⟨C.Sem.ElabC1.exists_accepted, ?_⟩
  intro p q hc he
  obtain ⟨us, hus, hv, hne⟩ := C.Sem.checkC1_sound hc
  have hf := C.Sem.factor (S := C.Sem.C1.sem) (F := {p}) (elaborate := fun _ => q)
    (fun p' hp => by
      have eq : p' = p := hp
      subst p'
      exact (C.Sem.ElabC1.elaborate_sound he).2)
    C.Sem.mirConfig C.Sem.ctlAddress (Set.mem_singleton p) hv
  exact ⟨us, hus, hf.1, hf.2, hne⟩

end Silmaril.Compile.Targets.Proofs
