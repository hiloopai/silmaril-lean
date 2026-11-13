module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Sim

/-!
# The Core call of a function enters the simulation relation

`crel_init`: the Core 3.0 call of a defined function, with the arguments as values, runs to the
Core frame of its body, which is `CRel`-related to the machine's entry frame (for a program that
checks, a store holding the program, the globals with `GInv`, and the memory).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

variable {H : Type} {Pf : Profile} {host : HostSemantics H} {cap : Nat} {E : Env}
  {mi : ModuleInst} {s : Store H}

theorem fidx_toNat {e : Nat} (h : e < 2 ^ 32) : (fidx e).toNat = e := by
  simp only [fidx, Idx.toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt h

theorem calleeFr_admin (fd : FnDef) (args : List W) :
    (calleeFr fd args).admin mi [] =
      frameA mi fd.nres (args ++ List.replicate fd.nlocals 0) (expression fd.body) := by
  simp only [CFr.admin, calleeFr, stackA, List.reverse_nil, List.map_nil, vals,
    List.nil_append, List.append_nil, wrapL]

theorem entry_rel (e : Nat) (fd : FnDef) (args : List W) :
    FrRel (entry e fd args) (calleeFr fd args) :=
  ⟨rfl, rfl, by simp [CFr.ops, calleeFr, entry], by simp [CFr.code, calleeFr, entry]⟩

/-- **The Core call of a defined function enters the relation.** -/
theorem crel_init (hE : EnvOk E) (hH : HoldsProg s mi E) {e : Nat} {fd : FnDef} {args : List W}
    {gs : List W} {mem : Nat → W} (he : E.imps.length ≤ e) (he32 : e < 2 ^ 32)
    (hfd : E.fns[e - E.imps.length]? = some fd) (ha : args.length = fd.nparams)
    (hg : GlobalsAre s ⟨[], mi⟩ gs) (hm : MemAre s ⟨[], mi⟩ mem cap) (hG : GInv gs) :
    Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, vals (args.map Val.i32) ++ [.plain (.call (fidx e))]⟩
        ⟨s, ⟨[], mi⟩, stackC mi [calleeFr fd args] []⟩ ∧
      CRel cap E mi ⟨[entry e fd args], gs, mem⟩ s (stackC mi [calleeFr fd args] []) := by
  have hrun := call_frame (Pf := Pf) (host := host) (f := ⟨[], mi⟩) hH rfl hfd (x := fidx e)
    (by rw [fidx_toNat he32]; omega) ha
  refine ⟨?_, [calleeFr fd args], .cons (entry_rel e fd args) .nil,
    ⟨callee_ok hE hfd ha, trivial⟩, rfl, hH, hg, hm, hG, hE⟩
  rw [stackC_cons, calleeFr_admin]
  exact hrun

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
