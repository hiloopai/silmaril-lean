module

public import Silmaril.Wasm.Unified.Versions.Erratum.Thms
public import Silmaril.Wasm.Unified.Inst.Thms

/-!
# The `table.grow` erratum and models differing on one opcode

The erratum of `Silmaril.Wasm.Unified.Versions.Erratum` (`errR`: Core 3.0 reduction with the
`table.grow` steps dropped) changes the step relation, not the meaning of an opcode. This module
relates it to the institution-level notion of an erratum, `Model.update` (a model differing on
one opcode) and its locality theorem `sat_update_iff`.

* `errS`: **the static erratum**, `model30` updated at the `table.grow` opcode to mean nothing
  (`Model.update`);
* `errS_refines_core`: it refines Core 3.0 (the update only removes meanings,
  `evalCode_updEmpty_sub`); `errS_obs_grow`: code starting with `table.grow` has no
  observations in it;
* **`errS_sat_iff`**: by `sat_update_iff`, every sentence avoiding the opcode has the same truth
  value in `errS` and in Core 3.0;
* **`errR_sat_iff_core`**: the dynamic erratum `errR` has the same truth value as Core 3.0 for
  every sentence whose calls never reach a `table.grow` redex (`err_obs_eq`);
  **`errR_sat_iff_errS`**: so on sentences whose calls neither contain the opcode nor reach a
  redex, the dynamic erratum and the opcode update agree;
* **`errR_not_update`**: but `errR` is **not** an opcode update of Core 3.0: `Model.update`
  keeps the behaviours `run`, and `errR` changes them (at a `table.grow` redex Core 3.0 can
  return `-1`, `errR` has no behaviour). A step-relation erratum reaches code the sentence does
  not contain (store functions), which no opcode update can.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas
open Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

/-- The `table.grow` opcode of the 3.0 signature. -/
def growOp : sig30.Op := op30 (.tableGrow ⟨0⟩)

/-- The empty meaning. -/
def updEmpty : List Imm → List alg30.D → List Handler → alg30.I := fun _ _ _ => (∅ : Set Instr)

/-! ## Removing a meaning shrinks meanings -/

/-- The 3.0 meanings of blocks. -/
def ev30B (bs : List sig30.Code) : List (Set (List Instr)) := alg30.evalBlocks bs

/-- The meaning of an instruction with `o` removed. -/
def evUI (o : sig30.Op) (u : UInstr sig30.Op) : Set Instr := (alg30.update o updEmpty).evalInstr u

/-- The meaning of code with `o` removed. -/
def evU (o : sig30.Op) (c : sig30.Code) : Set (List Instr) := (alg30.update o updEmpty).evalCode c

/-- The meanings of blocks with `o` removed. -/
def evUB (o : sig30.Op) (bs : List sig30.Code) : List (Set (List Instr)) :=
  (alg30.update o updEmpty).evalBlocks bs

theorem forall₂_mem_mono {bodies : List (List Instr)} {Ds Ds' : List (Set (List Instr))}
    (h : List.Forall₂ (· ∈ ·) bodies Ds) (h' : List.Forall₂ (· ⊆ ·) Ds Ds') :
    List.Forall₂ (· ∈ ·) bodies Ds' := by
  induction h generalizing Ds' with
  | nil => cases h'; exact .nil
  | cons hb _ ih =>
    cases h' with
    | cons hD hDs => exact .cons (hD hb) (ih hDs)

mutual
theorem evalInstr_updEmpty_sub (o : sig30.Op) :
    (u : UInstr sig30.Op) → evUI o u ⊆ evalI30 u
  | .op o' imms bs hs => by
    intro i hi
    rw [evUI, Alg.evalInstr] at hi
    rw [evalI30, Alg.evalInstr]
    by_cases h : o' = o
    · subst h
      simp only [Alg.update, Function.update_self, updEmpty] at hi
      exact absurd hi (Set.notMem_empty i)
    · simp only [Alg.update, Function.update_of_ne h] at hi
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hi
      exact ⟨h₁, h₂, h₃, forall₂_mem_mono h₄ (evalBlocks_updEmpty_sub o bs)⟩
theorem evalCode_updEmpty_sub (o : sig30.Op) :
    (c : sig30.Code) → evU o c ⊆ evalC30 c
  | [] => by
    rw [evU, evalC30, Alg.evalCode, Alg.evalCode]
    exact subset_rfl
  | u :: c => by
    rw [evU, evalC30, Alg.evalCode, Alg.evalCode]
    rintro l ⟨i, t, rfl, hi, ht⟩
    exact ⟨i, t, rfl, evalInstr_updEmpty_sub o u hi, evalCode_updEmpty_sub o c ht⟩
theorem evalBlocks_updEmpty_sub (o : sig30.Op) :
    (bs : List sig30.Code) →
      List.Forall₂ (· ⊆ ·) (evUB o bs) (ev30B bs)
  | [] => by
    rw [evUB, ev30B, Alg.evalBlocks, Alg.evalBlocks]
    exact .nil
  | b :: bs => by
    rw [evUB, ev30B, Alg.evalBlocks, Alg.evalBlocks]
    exact .cons (evalCode_updEmpty_sub o b) (evalBlocks_updEmpty_sub o bs)
end

/-! ## The static erratum -/

variable {H : Type}

/-- **The static erratum**: Core 3.0 with `table.grow` meaning nothing. -/
def errS (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Model UIn UObs sig30 :=
  (model30 P host s f okc).update growOp updEmpty

theorem errS_refines_core (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Refines (errS P host s f okc) (model30 P host s f okc) := by
  rintro ⟨c, vs⟩ b ⟨⟨is, his, hok⟩, is', his', hok', hb⟩
  exact ⟨⟨is, evalCode_updEmpty_sub growOp c his, hok⟩,
    is', evalCode_updEmpty_sub growOp c his', hok', hb⟩

/-- Code starting with `table.grow` has no observations in the static erratum. -/
theorem errS_obs_grow (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (imms : List Imm) (bs : List sig30.Code) (hs : List Handler)
    (c : sig30.Code) (vs : UIn) :
    (errS P host s f okc).obs (.op growOp imms bs hs :: c, vs) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun b ⟨⟨is, his, _⟩, _⟩ => ?_
  obtain ⟨i, t, -, hi, -⟩ := his
  have hi' : i ∈ evUI growOp (.op growOp imms bs hs) := hi
  rw [evUI, Alg.evalInstr] at hi'
  simp only [Alg.update, Function.update_self, updEmpty] at hi'
  exact Set.notMem_empty i hi'

/-- **The static erratum satisfies the sentences avoiding `table.grow` that Core 3.0 does.** -/
theorem errS_sat_iff (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (φ : Sen UIn UObs sig30) (h : φ.Avoids growOp) :
    Sat (errS P host s f okc) φ ↔ Sat (model30 P host s f okc) φ :=
  sat_update_iff (model30 P host s f okc) growOp updEmpty φ h

/-! ## The dynamic erratum -/

/-- No run of a call reaches a `table.grow` redex. -/
def NoGrowRun (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (x : Call UIn sig30) : Prop :=
  ∀ is ∈ evalC30 x.1, ∀ c', Relation.ReflTransGen (Step P host) (cfgOf s f is x.2) c' →
    ¬ AtGrow c'

/-- **The dynamic erratum agrees with Core 3.0 on sentences whose calls never reach the
opcode.** -/
theorem errR_sat_iff_core (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (φ : Sen UIn UObs sig30) (h : callsIn (NoGrowRun P host s f) φ) :
    Sat (errR P host s f okc) φ ↔ Sat (model30 P host s f okc) φ :=
  sat_congr_calls (fun x hx => err_obs_eq P host s f okc x.1 x.2 hx) φ h

/-- **The dynamic erratum and the opcode update agree** on sentences whose calls neither contain
`table.grow` nor reach it. -/
theorem errR_sat_iff_errS (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (φ : Sen UIn UObs sig30)
    (h : callsIn (fun x => growOp ∉ UInstr.opsCode x.1 ∧ NoGrowRun P host s f x) φ) :
    Sat (errR P host s f okc) φ ↔ Sat (errS P host s f okc) φ := by
  refine sat_congr_calls (fun x hx => ?_) φ h
  rw [err_obs_eq P host s f okc x.1 x.2 hx.2]
  exact (Model.obs_update (model30 P host s f okc) growOp updEmpty x.1 x.2 hx.1).symm

/-- **The dynamic erratum is not an opcode update of Core 3.0**: at a `table.grow` redex whose
table exists (nondeterministic grow policy, the code validates), the behaviours differ, and
`Model.update` keeps the behaviours. -/
theorem errR_not_update {P : Profile} (hP : P.grow = .nondet) (host : HostSemantics H)
    {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (r : Ref) (a : AddrType) (n : BitVec a.intType.width)
    (okc : List Instr → Prop) (hok : okc [.intConst a.intType n, .tableGrow x])
    (o : sig30.Op) (v : List Imm → List alg30.D → List Handler → alg30.I) :
    errR P host s f okc ≠ (model30 P host s f okc).update o v := by
  intro h
  have hrun : (errR P host s f okc).run = (model30 P host s f okc).run := by
    unfold errR modelR Model.update model30 at h
    injection h
  have hcfg : cfgOf s f [.intConst a.intType n, .tableGrow x] [.ref r] = growCfg s f r a n x :=
    rfl
  have hD := congrFun (congrFun hrun
    ({[.intConst a.intType n, .tableGrow x]} : Set (List Instr))) [.ref r]
  have hcore : Behaviour.returns [.num ⟨.int a.intType, BitVec.allOnes _⟩] ∈
      (model30 P host s f okc).run
        ({[.intConst a.intType n, .tableGrow x]} : Set (List Instr)) [.ref r] :=
    ⟨_, rfl, hok, grow_core_returns hP host ht r a n⟩
  rw [← hD] at hcore
  obtain ⟨is, his, -, hb⟩ := hcore
  have his' : is = [.intConst a.intType n, .tableGrow x] := his
  subst his'
  change _ ∈ Variant.behavioursR (growErr P host)
    (cfgOf s f [.intConst a.intType n, .tableGrow x] [.ref r]) at hb
  rw [hcfg, grow_err_empty] at hb
  exact hb
