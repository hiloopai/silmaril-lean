module

public import Silmaril.Proofs.Wasm.LimeCompile.Frag.Basic

/-!
# Respecting `select` erasure does not make a host code-parametric

`bodyHost` answers `0` when every Wasm function of the store has an empty body and `1`
otherwise. Erasing `select` annotations keeps body lengths, so the host respects erasure; but
a code-parametric host must answer the same on stores whose functions are related by *any*
reflexive relation, e.g. the total one, and a store with body `[]` and one with body `[nop]` are
so related.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Frag

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.LimeCompile.Select
open Silmaril.Proofs.Wasm.LimeCompile.Select (selL_eq_map)

/-- Every Wasm function of the store has an empty body. -/
def emptyBodies (s : Store Unit) : Bool :=
  s.funcs.all fun f => match f.code with
    | .wasm g => g.body.isEmpty
    | .host _ => true

/-- The host answering whether every body is empty. -/
def bodyHost : HostSemantics Unit := fun _ s _ o =>
  o = .returned s (.values [Val.i32 (if emptyBodies s then 0 else 1)])

theorem emptyBodies_sel (s : Store Unit) : emptyBodies (selS s) = emptyBodies s := by
  simp only [emptyBodies, selS, List.all_map]
  congr 1
  funext f
  rcases f with ⟨ty, mi, c⟩
  cases c with
  | wasm g => simp [selFI, selFn, selL_eq_map]
  | host h => rfl

theorem bodyHost_resp : HostResp bodyHost := by
  intro h s t vs o hst ho
  refine ⟨.returned t (.values [Val.i32 (if emptyBodies t then 0 else 1)]), rfl, ?_⟩
  subst ho
  have he : emptyBodies s = emptyBodies t := by
    rw [← emptyBodies_sel s, ← emptyBodies_sel t, hst]
  simp only [Silmaril.Wasm.Execution.Host.Outcome.Sim, he, id]
  exact ⟨hst, trivial⟩

/-- A function instance with the given body. -/
def fiBody (b : List Instr) : FuncInst Unit := ⟨default, {}, .wasm ⟨⟨0⟩, [], b⟩⟩

theorem bodyHost_not_parametric : ¬ Sim.HostParametric bodyHost := by
  intro hp
  have hrel : Sim.StoreRel (fun _ _ => True) ({ funcs := [fiBody []] } : Store Unit)
      ({ funcs := [fiBody [.nop]] } : Store Unit) :=
    ⟨rfl, rfl, .cons trivial .nil⟩
  obtain ⟨o', ho', hr⟩ := hp (fun _ _ => True) (fun _ => trivial) () _ _ [] _ hrel rfl
  subst ho'
  simp only [Sim.OutcomeRel, Silmaril.Wasm.Execution.Host.Outcome.Sim, emptyBodies, fiBody] at hr
  exact absurd hr.2 (by decide)

end Silmaril.Proofs.Wasm.LimeCompile.Frag
