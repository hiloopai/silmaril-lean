module

public import Silmaril.Proofs.Wasm.Logic.V1.Sound.Single

/-!
# Soundness of the variable-management proof rules

Figure 7 of Watt et al. The paper's `isDeclaredLocal` and `isDeclaredGlobal`
side conditions are absent: an access to an undeclared variable has no execution
at all, so the triple holds vacuously. This is sound because `Valid` is partial
correctness over the executions that exist, exactly as Figure 17 is.

`valid_globalSet` is where `ReifiesGlobals.nodup` earns its place: without
distinct global addresses, assigning to `gᵢ` could silently change `gⱼ`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert}

/-- The index of a successful `getElem?` is in range. -/
private theorem lt_length_of_getElem? {α : Type*} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp h
  exact hi

/-- Writing local `i` re-establishes `ReifiesLocals` for the updated frame. -/
private theorem reifiesLocals_set {locals : List Value} {ρ : Sto} {i : Nat} {v : Value}
    (hi : i < locals.length) (hl : ReifiesLocals locals ρ) :
    ReifiesLocals (locals.set i v) (ρ.update (.loc i) v) := by
  intro j w hw
  rcases eq_or_ne j i with rfl | hj
  · rw [List.getElem?_set_self hi] at hw
    obtain rfl := Option.some.inj hw
    simp
  · rw [List.getElem?_set_ne (Ne.symm hj)] at hw
    rw [Sto.update_other _ _ (by simpa using hj), hl j w hw]

/-- Writing a local leaves the global variables of the abstract store alone. -/
private theorem reifiesGlobals_update_loc {s : Store H} {md : ModuleInst} {ρ : Sto} {i : Nat}
    {v : Value} (hg : ReifiesGlobals s md ρ) :
    ReifiesGlobals s md (ρ.update (.loc i) v) := by
  refine ⟨hg.nodup, fun j a g hj hf => ?_⟩
  rw [Sto.update_other _ _ (by simp), hg.agree j a g hj hf]

/-- The abstract store after an assignment to `x` agrees with the old one on
every variable other than `x`. -/
private theorem update_agree {ρ : Sto} {X : Set Var} {x : Var} {v : Value} (hx : x ∈ X) :
    ∀ y, y ∉ X → ρ.update x v y = ρ y := by
  intro y hy
  exact Sto.update_other _ _ (by rintro rfl; exact hy hx)

theorem valid_localGet (i : LocalIdx) :
    Valid host n F L R (Assert.stack []) [.localGet i]
      (Assert.stack [Term.local_ i.toNat]) := by
  refine valid_single (S := []) (Hp := HAssert.emp) trivial ?_ ?_ ?_ ?_
  · intro s s' f f' args rets step; cases step; rfl
  · intro s f args step; cases step
  · intro s f ρ hp hf _ _ _ step; cases step
  · intro s s' f f' ρ hp hf rets hemp disj reify step
    cases step
    rename_i w found
    exact ⟨hp, ρ, disj, reify, fun _ _ => rfl, by simp [Term.local_, reify.locals _ _ found],
      hemp⟩

theorem valid_localSet (i : LocalIdx) (v : Value) :
    Valid host n F L R (Assert.stack [Term.const v]) [.localSet i]
      (Assert.stackIf [] fun ρ => ρ (.loc i.toNat) = v) := by
  refine valid_single (S := [Term.const v]) (Hp := HAssert.emp) trivial ?_ ?_ ?_ ?_
  · intro s s' f f' args rets step; cases step; rfl
  · intro s f args step; cases step
  · intro s f ρ hp hf _ _ _ step; cases step
  · intro s s' f f' ρ hp hf rets hemp disj reify step
    cases step
    rename_i old found
    exact ⟨hp, ρ.update (.loc i.toNat) v, disj,
      ⟨reify.funcs, reifiesLocals_set (lt_length_of_getElem? found) reify.locals,
        reifiesGlobals_update_loc reify.globals, reify.mem⟩,
      update_agree (by simp [Instr.modified]), rfl, hemp, by simp [HAssert.pure]⟩

theorem valid_localTee (i : LocalIdx) (v : Value) :
    Valid host n F L R (Assert.stack [Term.const v]) [.localTee i]
      (Assert.stackIf [Term.const v] fun ρ => ρ (.loc i.toNat) = v) := by
  refine valid_single (S := [Term.const v]) (Hp := HAssert.emp) trivial ?_ ?_ ?_ ?_
  · intro s s' f f' args rets step; cases step; rfl
  · intro s f args step; cases step
  · intro s f ρ hp hf _ _ _ step; cases step
  · intro s s' f f' ρ hp hf rets hemp disj reify step
    cases step
    rename_i old found
    exact ⟨hp, ρ.update (.loc i.toNat) v, disj,
      ⟨reify.funcs, reifiesLocals_set (lt_length_of_getElem? found) reify.locals,
        reifiesGlobals_update_loc reify.globals, reify.mem⟩,
      update_agree (by simp [Instr.modified]), by simp [Term.const], hemp, by simp [HAssert.pure]⟩

theorem valid_globalGet (i : GlobalIdx) :
    Valid host n F L R (Assert.stack []) [.globalGet i]
      (Assert.stack [Term.global i.toNat]) := by
  refine valid_single (S := []) (Hp := HAssert.emp) trivial ?_ ?_ ?_ ?_
  · intro s s' f f' args rets step; cases step; rfl
  · intro s f args step; cases step
  · intro s f ρ hp hf _ _ _ step; cases step
  · intro s s' f f' ρ hp hf rets hemp disj reify step
    cases step
    rename_i a g found index
    exact ⟨hp, ρ, disj, reify, fun _ _ => rfl,
      by simp [Term.global, reify.globals.agree _ a g index found], hemp⟩

/-- Writing the global at address `a`, read back through the index `i` that names it. -/
private theorem setGlobal_same {s : Store H} {md : ModuleInst} {ρ : Sto} {i : Nat}
    {a b : GlobalAddr} {g g' : GlobalInst} {v : Value} (index : md.globals[i]? = some a)
    (found : s.globals[a.value]? = some g) (hj : md.globals[i]? = some b)
    (hg : (setGlobal s a {g with value := v}).globals[b.value]? = some g') :
    ρ.update (.glob i) v (.glob i) = g'.value := by
  obtain rfl : b = a := Option.some.inj (hj.symm.trans index)
  have hg' : some {g with value := v} = some g' := by
    simpa only [setGlobal, List.getElem?_set_self (lt_length_of_getElem? found)] using hg
  obtain rfl : {g with value := v} = g' := Option.some.inj hg'
  simp

/-- Writing the global at address `a` leaves every other global index unchanged, since
global addresses are distinct. -/
private theorem setGlobal_other {s : Store H} {md : ModuleInst} {ρ : Sto} {i j : Nat}
    {a b : GlobalAddr} {g g' : GlobalInst} {v : Value} (hr : ReifiesGlobals s md ρ)
    (index : md.globals[i]? = some a) (hji : j ≠ i) (hj : md.globals[j]? = some b)
    (hg : (setGlobal s a {g with value := v}).globals[b.value]? = some g') :
    ρ.update (.glob i) v (.glob j) = g'.value := by
  have hba : b.value ≠ a.value := by
    intro hv
    obtain rfl : b = a := congrArg Addr.mk hv
    exact hji ((hr.nodup.getElem?_inj (lt_length_of_getElem? hj)).mp (hj.trans index.symm))
  have hg' : s.globals[b.value]? = some g' := by
    simpa only [setGlobal, List.getElem?_set_ne (Ne.symm hba)] using hg
  rw [Sto.update_other _ _ (by simpa using hji)]
  exact hr.agree j b g' hj hg'

/-- `global.set` keeps the globals reified, with the abstract store updated. -/
private theorem reifiesGlobals_setGlobal {s : Store H} {md : ModuleInst} {ρ : Sto}
    (hr : ReifiesGlobals s md ρ) {i : Nat} {a : GlobalAddr} {g : GlobalInst}
    (index : md.globals[i]? = some a) (found : s.globals[a.value]? = some g) (v : Value) :
    ReifiesGlobals (setGlobal s a {g with value := v}) md (ρ.update (.glob i) v) := by
  refine ⟨hr.nodup, fun j b g' hj hg => ?_⟩
  rcases eq_or_ne j i with rfl | hji
  · exact setGlobal_same index found hj hg
  · exact setGlobal_other hr index hji hj hg

theorem valid_globalSet (i : GlobalIdx) (v : Value) :
    Valid host n F L R (Assert.stack [Term.const v]) [.globalSet i]
      (Assert.stackIf [] fun ρ => ρ (.glob i.toNat) = v) := by
  refine valid_single (S := [Term.const v]) (Hp := HAssert.emp) trivial ?_ ?_ ?_ ?_
  · intro s s' f f' args rets step; cases step; rfl
  · intro s f args step; cases step
  · intro s f ρ hp hf _ _ _ step; cases step
  · intro s s' f f' ρ hp hf rets hemp disj reify step
    cases step with
    | globalSet _ a g _ index found _ =>
      exact ⟨hp, ρ.update (.glob i.toNat) v, disj,
        ⟨reify.funcs, fun j w hw => by rw [Sto.update_other _ _ (by simp), reify.locals j w hw],
          reifiesGlobals_setGlobal reify.globals index found v, reify.mem⟩,
        update_agree (by simp [Instr.modified]), rfl, hemp, by simp [HAssert.pure]⟩

end Silmaril.Wasm.Logic.V1
