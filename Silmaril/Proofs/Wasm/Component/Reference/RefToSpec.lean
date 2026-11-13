module

public import Silmaril.Proofs.Wasm.Component.Reference.Phases

/-!
# The reference half from its two phases

`refToSpec_of_phases`: the instantiation phase (`InstPhase`) and the call phase (`CallPhase`)
give the statement of `RefToSpecAll` for components within the flat arities
(`Simple.Arity`). The export map `exportMap c` of the instance finds export `x` at its index,
because export names are distinct (`Simple.Good`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Numerics (Profile)

/-- Looking up the name of the `j`-th element of a list with distinct names, among the names
paired with their indices from `n`, finds `n + j`. -/
theorem lookup_mapIdx_name {α : Type} (name : α → String) :
    ∀ (n : Nat) (xs : List α) (j : Nat) (hj : j < xs.length), (xs.map name).Nodup →
      (xs.mapIdx fun i x => (name x, (⟨n + i⟩ : FuncId))).lookup (name xs[j]) = some ⟨n + j⟩
  | _, [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | n, x :: xs, 0, _, _ => by simp
  | n, x :: xs, j + 1, hj, hn => by
    have hn' : name x ∉ xs.map name ∧ (xs.map name).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hn
    have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
    have hne : (name xs[j] == name x) = false := by
      refine beq_false_of_ne fun e => hn'.1 ?_
      exact e ▸ List.mem_map_of_mem (List.getElem_mem hj')
    have ih := lookup_mapIdx_name name (n + 1) xs j hj' hn'.2
    have hf : (fun i x => (name x, (⟨n + (i + 1)⟩ : FuncId))) =
        fun i x => (name x, (⟨n + 1 + i⟩ : FuncId)) := by
      funext i x
      rw [Nat.add_right_comm, Nat.add_assoc]
    rw [List.mapIdx_cons, List.getElem_cons_succ, List.lookup_cons, hne, hf, ih,
      Nat.add_right_comm, Nat.add_assoc]

/-- The export map finds every export at its index. -/
theorem exportMap_lookup {c : Simple} (hc : c.Good) (j : Nat) (hj : j < c.exports.length) :
    (exportMap c).lookup c.exports[j].name = some ⟨j⟩ := by
  have h := lookup_mapIdx_name (·.name) 0 c.exports j hj hc.names
  simp only [Nat.zero_add] at h
  exact h

/-- **The reference half from its phases**, for components within the flat arities. -/
theorem refToSpec_of_phases (hA : InstPhase) (hB : CallPhase) (P : Profile)
    (prof : ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst)
    (ha : c.Arity) (x : SimpleExport) (hx : x ∈ c.exports) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) :
    exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆
      exportSpec P c x vs := by
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < c.exports.length, c.exports[j] = x :=
    List.getElem_of_mem hx
  obtain ⟨I, cs, hI, hcs, hinst⟩ := hA P prof c hc hi
  have hcall := hB P prof c hc hf ha I cs hI hcs j hj vs hvs
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he : InstResult.instance m₁ inst es = .instance (afterInst P cs
        (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩ (exportMap c) := hinst _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c) ∧
        inst = ⟨0⟩ ∧ es = exportMap c := by
      simpa only [InstResult.instance.injEq] using he
    have hf' : f = ⟨j⟩ := Option.some.inj (hl.symm.trans (exportMap_lookup hc j hj))
    exact hcall (hf' ▸ hb)
  · exact absurd (hinst _ hr) (by simp)
  · exact absurd (hinst _ hr) (by simp)

end Silmaril.Proofs.Wasm.Component.Reference
