module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.TyElim.SubOk2

/-!
# Round 6: `AgreeTy.okElim` on the concrete `B`

`coh_of_deftypeOk`: on the concrete `B`, a defined type for which `Deftype_ok` holds under
`DDerivesB` in a context `ctxR L` is **coherent** (`RefOkV.Coh`): every type reachable along its
declared supertypes has its kind. This is `RefOkV.coh_of_tyOkS` with SpecTec's derivation in
place of the transcription `TyOkS`: `Deftype_ok` checks the group in `ctxR (subtype* ++ L)`
(`deftypeOk_inv`), `Rectype_ok2` checks each member at its position (`rectypeOk2_get`), and
`Subtype_ok2` (`subtypeOk2_facts`) makes each declared supertype an earlier member (`$before`,
`C.RECS`) or a defined type that is itself `Deftype_ok` and smaller, of the same head
constructor (`Comptype_sub`).

`okElim_BI`: so `Reftype_ok {}` at the image of a reference type makes its heap type coherent.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV headV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Validation.DefInv (subst_def_u len_of_get subst_recv)
open Round6.Reading
open Round6.RefOkB (ctxR)
open Round6.RefOkV (Coh CohH refHeap defKind_member supersOf_member size_lt_of_super)

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type} {hn : H → String}
  {host : Silmaril.Wasm.Execution.Core.HostSemantics H}

/-- A subtype image `SUB eps typeuse* body'` with the head of `ct`'s image: a non-final subtype
whose body has `ct`'s kind. -/
theorem kind_of_subImg {st : CSubType} {ct : CCompType} {X c' : Value}
    (he : tyV st = .case "SUB" (.tuple [.opt none, X, c'])) (hh : headV (tyV ct) = headV c') :
    ∃ sups' ct', st = .sub false sups' ct' ∧ compAbs ct = compAbs ct' := by
  obtain ⟨fin, sups', ct', rfl⟩ : ∃ fin sups' ct', st = Ty.sub fin sups' ct' := by
    cases st; exact ⟨_, _, _, rfl⟩
  simp only [tyV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
    true_and] at he
  obtain ⟨hf, -, rfl⟩ := he
  have : fin = false := by cases fin <;> simp_all [Silmaril.SpecTec.Equiv.Validation.finalV]
  subst this
  exact ⟨sups', ct', rfl, compAbs_of_head hh⟩

/-- A defined type with no unrolling reaches only itself, so is coherent. -/
theorem coh_of_unroll_none {d : DefType} (h : unrolldt d = none) : Coh d := by
  intro e he
  cases he with
  | refl => rfl
  | step hu => simp [supersOf, h] at hu

/-- What one step along a declared supertype of member `j` gives: the target has the member's
kind, and is an earlier member or a smaller `Deftype_ok` defined type. -/
def MemberStep (B : Builtins) (O : ElseI) (L : List Value) (subs : Ty (.list .sub)) (j : Nat)
    (d' : DefType) : Prop :=
  defKind d' = defKind (.defn (.group subs) j) ∧
    ((∃ k, k < j ∧ d' = .defn (.group subs) k) ∨
      (d'.size < (Ty.defn (.group subs) j).size ∧
        DDerivesB (simEnv B) O "Deftype_ok" "%|-%:OK" []
          (.tuple [ctxR (subs.toList.map tyV ++ L), tyV d'])))

/-- The step to an earlier member `REC k`. -/
theorem member_step_recv {O : ElseI} {L : List Value} {subs : Ty (.list .sub)} {j k : Nat}
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hst : subs.toList[j]? = some (.sub fin sups ct)) (hj : j < subs.length)
    (hF : SupFact (Prims.builtins prof hn host) O (subs.toList.map tyV ++ L) j ct (.recv k)) :
    MemberStep (Prims.builtins prof hn host) O L subs j (.defn (.group subs) k) := by
  obtain ⟨hkj, X, c', hL, hh⟩ := hF
  have hks : k < subs.toList.length := by simpa [Ty.length] using Nat.lt_trans hkj hj
  obtain ⟨stk, hstk⟩ : ∃ stk, subs.toList[k]? = some stk := ⟨_, List.getElem?_eq_getElem hks⟩
  have hk : (subs.toList.map tyV ++ L)[k]? = some (tyV stk) := by
    rw [List.getElem?_append_left (by simpa using hks)]
    simp [hstk]
  have hL' : tyV stk = .case "SUB" (.tuple [.opt none, X, c']) :=
    Option.some.inj (hk.symm.trans hL)
  obtain ⟨sups', ct', rfl, hc⟩ := kind_of_subImg hL' hh
  refine ⟨?_, .inl ⟨k, hkj, rfl⟩⟩
  rw [defKind_member hstk, defKind_member hst, hc]

/-- The step to a defined type `d₀` of the member's supertype list. -/
theorem member_step_dt {O : ElseI} {L : List Value} {subs : Ty (.list .sub)} {j : Nat}
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType} {d₀ : DefType}
    (hst : subs.toList[j]? = some (.sub fin sups ct)) (hu₀ : Ty.dt d₀ ∈ sups.toList)
    (hF : SupFact (Prims.builtins prof hn host) O (subs.toList.map tyV ++ L) j ct (.dt d₀)) :
    MemberStep (Prims.builtins prof hn host) O L subs j d₀ := by
  obtain ⟨hD, st, X, c', hun, hst', hh⟩ := hF
  obtain ⟨sups', ct', rfl, hc⟩ := kind_of_subImg hst' hh
  refine ⟨?_, .inr ⟨size_lt_of_super hst hu₀, hD⟩⟩
  rw [defKind_of_unroll hun, defKind_member hst, hc]

/-- A member of a group, one step along a declared supertype: the facts `Subtype_ok2` gives. -/
theorem member_step {O : ElseI} {L : List Value} {subs : Ty (.list .sub)} {j : Nat}
    {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hst : subs.toList[j]? = some (.sub fin sups ct))
    (hj : j < subs.length) {u₀ : CTypeUse} (hu₀ : u₀ ∈ sups.toList)
    (hF : SupFact (Prims.builtins prof hn host) O (subs.toList.map tyV ++ L) j ct u₀)
    {d' : DefType} (hr : ({} : TypeCtx).resolve (u₀.subst (unrollSubst subs)) = some d') :
    MemberStep (Prims.builtins prof hn host) O L subs j d' := by
  cases u₀ with
  | idx x => simp [Ty.subst, DefInv.unrollSubst_idx, TypeCtx.resolve] at hr
  | recv k =>
    have hd' : Ty.defn (.group subs) k = d' := by simpa [subst_recv (Nat.lt_trans hF.1 hj)] using hr
    exact hd' ▸ member_step_recv hst hj hF
  | dt d₀ =>
    have hd' : d₀ = d' := by simpa [Ty.subst, subst_def_u] using hr
    exact hd' ▸ member_step_dt hst hu₀ hF

/-- What `Subtype_ok2` says of each member's declared supertypes, from `Rectype_ok2`. -/
theorem group_facts {O : ElseI} {L : List Value} {subs : Ty (.list .sub)}
    (hR : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxR (subs.toList.map tyV ++ L),
        .case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)])), .case "OK" (natV 0)]))
    {j : Nat} {fin : Bool} {sups : Ty (.list .use)} {ct : CCompType}
    (hst : subs.toList[j]? = some (.sub fin sups ct)) :
    ∀ u ∈ sups.toList, SupFact (Prims.builtins prof hn host) O (subs.toList.map tyV ++ L) j ct u :=
  have h := rectypeOk2_get (subs.toList.map tyV) 0 hR j (tyV (Ty.sub fin sups ct))
    (by simp [hst])
  subtypeOk2_facts (Nat.zero_add j ▸ h)

/-- **The members of a checked group are coherent**, given coherence of the smaller
`Deftype_ok` defined types. -/
theorem coh_members {O : ElseI} {L : List Value} {subs : Ty (.list .sub)}
    (hR : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Rectype_ok2" "%|-%:%" []
      (.tuple [ctxR (subs.toList.map tyV ++ L),
        .case "REC" (.case "%" (.tuple [.list (subs.toList.map tyV)])), .case "OK" (natV 0)]))
    (hsmall : ∀ d' : DefType, d'.size < (Ty.group subs).size + 1 →
      DDerivesB (simEnv (Prims.builtins prof hn host)) O "Deftype_ok" "%|-%:OK" []
        (.tuple [ctxR (subs.toList.map tyV ++ L), tyV d']) → Coh d') :
    ∀ j, j < subs.length → Coh (.defn (.group subs) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj e he
    cases he with
    | refl => rfl
    | @step _ d' _ u hu hr hrest =>
      obtain ⟨st, hst⟩ : ∃ st, subs.toList[j]? = some st :=
        ⟨_, List.getElem?_eq_getElem (by simpa [Ty.length] using hj)⟩
      obtain ⟨fin, sups, ct, rfl⟩ : ∃ fin sups ct, st = Ty.sub fin sups ct := by
        cases st; exact ⟨_, _, _, rfl⟩
      obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 (supersOf_member hst ▸ hu)
      obtain ⟨hk, hcase⟩ := member_step hst hj hu₀ (group_facts hR hst u₀ hu₀) hr
      show defKind e = defKind (.defn (.group subs) j)
      rcases hcase with ⟨k, hkj, rfl⟩ | ⟨hlt, hD⟩
      · exact (ih k hkj (by omega) e hrest).trans hk
      · exact (hsmall d' (by simpa only [Ty.size] using hlt) hD e hrest).trans hk

/-- **`Deftype_ok` makes a defined type coherent**, on the concrete `B`, in every context
`ctxR L`. -/
theorem coh_of_deftypeOk : ∀ (n : Nat) {O : ElseI} {L : List Value} {d : DefType}, d.size < n →
    DDerivesB (simEnv (Prims.builtins prof hn host)) O "Deftype_ok" "%|-%:OK" []
      (.tuple [ctxR L, tyV d]) → Coh d
  | 0, _, _, _, hsz, _ => absurd hsz (Nat.not_lt_zero _)
  | n + 1, O, L, d, hsz, hd => by
    obtain ⟨subs, i, rfl⟩ : ∃ subs i, d = Ty.defn (.group subs) i := by
      cases d with
      | defn g i => cases g with
        | group subs => exact ⟨subs, i, rfl⟩
    have hR := tyV_group subs ▸ deftypeOk_inv hd
    have hall := coh_members hR fun d' hlt hD =>
      coh_of_deftypeOk n (by simp only [Ty.size] at hsz hlt ⊢; omega) hD
    by_cases hi : i < subs.length
    · exact hall i hi
    · refine coh_of_unroll_none ?_
      rw [unrolldt_defn, List.getElem?_eq_none (by simpa [Ty.length] using hi)]
      rfl

/-- `{}` is `ctxR []`. -/
theorem ctxEmptyV_eq : RefOkV.ctxEmptyV = ctxR [] := rfl

/-- **`AgreeTy.okElim`, on the concrete `B`**: `Reftype_ok {}` at the image of a reference type
makes its heap type coherent. -/
theorem okElim_BI (O : ElseI) (rt : CRefType)
    (h : DDerivesB (simEnv (Prims.builtins prof hn host)) O "Reftype_ok" "%|-%:OK" []
      (.tuple [RefOkV.ctxEmptyV, tyV rt])) : CohH (refHeap rt) := by
  obtain ⟨nl, hp, rfl⟩ : ∃ nl hp, rt = Ty.ref nl hp := by cases rt; exact ⟨_, _, rfl⟩
  have hH := reftypeOk_heap h
  cases hp with
  | abs => trivial
  | bot => trivial
  | use u =>
    cases u with
    | idx => trivial
    | recv => trivial
    | dt d =>
      exact coh_of_deftypeOk _ (Nat.lt_succ_self _) (L := [])
        (typeuseOk_def (heaptypeOk_def (d := d) hH))

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
