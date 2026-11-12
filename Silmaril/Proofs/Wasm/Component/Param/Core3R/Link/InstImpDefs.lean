module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstImpDefs` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstImpDefs` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

variable {E : CoreEngine} {σ : Type}

/-! ## The import pre-check of type definitions -/

section Pre

variable [∀ a b, Decidable (E.ExternSub a b)] (s : CStore E) (args : Exports E)

variable {s args}


end Pre

/-! ## The definitions of one import -/

section Imports

variable {Pf : Silmaril.Wasm.Numerics.Profile} {R : Recurse (core3R Pf V IR) σ} {inst : InstId}
  {outer : List (Frame (core3R Pf V IR))} {args : Exports (core3R Pf V IR)} {s : CStore (core3R Pf V IR)}

theorem importDefs_eq (p : String × FuncTy) (n : Nat) :
    (SimpleI.importDefs p n : List (Syntax.Definition (core3R Pf V IR).Module) × Nat) =
      ((emitTys (M := (core3R Pf V IR).Module) p.2.params n).2.1 ++
        (emitTys (M := (core3R Pf V IR).Module) p.2.results
          (emitTys (M := (core3R Pf V IR).Module) p.2.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) p.2.params n).1,
                        result := (emitTys (M := (core3R Pf V IR).Module) p.2.results
                          (emitTys (M := (core3R Pf V IR).Module) p.2.params n).2.2).1.head? }),
         .import_ { name := p.1 } (.func (emitTys (M := (core3R Pf V IR).Module) p.2.results
           (emitTys (M := (core3R Pf V IR).Module) p.2.params n).2.2).2.2)],
        (emitTys (M := (core3R Pf V IR).Module) p.2.results
          (emitTys (M := (core3R Pf V IR).Module) p.2.params n).2.2).2.2 + 1) := by
  simp only [SimpleI.importDefs]
  rfl

/-- The emitted function type of an import resolves to `witFt`. -/
theorem resolveFuncType_witFt {f : Frame (core3R Pf V IR)} {ft : FuncTy} {ps rs : List Syntax.VT}
    (hp : List.Forall₂ (Res f.types) ps (toClosedList ft.params))
    (hr : List.Forall₂ (Res f.types) rs (toClosedList ft.results)) :
    resolveFuncType? f { params := labels "a" ps, result := rs.head? } = some (witFt ft) :=
  resolveFuncType_lifted (x := ⟨"", ft, 0⟩) hp hr

/-- **A function import with the root argument `func k`**, whose host function has the
descriptor's type, pushes component function `k`. -/
theorem import_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ) {nm : String}
    {n : Nat} {k : FuncId} {t : Types.FuncType RtId} {fi : CFuncInst (core3R Pf V IR)}
    (hl : args.lookup nm = some (.func k)) (hf : sc.frame.types[n]? = some (.func t))
    (hs : ArenaField.funcs.get? cfg.store k = some fi) (ht : fi.ft = t) :
    TRuns (instantiateDef R inst outer args sc (.import_ { name := nm } (.func n))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [k] } } cfg := by
  have hc : importTypeCheck cfg.store sc.frame nm (.func n) (.func k) = .ok () :=
    importTypeCheck_func cfg.store sc.frame nm hf hs ht
  have hpush : (pushEntry sc.frame (Syntax.ExternDesc.func n).sort (.item (.func k)) :
      P (core3R Pf V IR) σ (Frame (core3R Pf V IR))) =
      Pure.pure { sc.frame with funcs := sc.frame.funcs ++ [k] } := by
    simp only [pushEntry, Syntax.ExternDesc.sort, Frame.push, need, orTrap]
  simp only [instantiateDef, hl, orTrap, pure_bind]
  refine (TRuns.getStore cfg).bind ((checkImport_run hc cfg).bind ?_)
  rw [hpush, pure_bind]
  exact TRuns.pure _ cfg

/-- **The definitions of one import run silently**, pushing component function `k`. -/
theorem importDef_run (p : String × FuncTy) (k : FuncId) (sc : Scope (core3R Pf V IR))
    (cfg : Machine.Config (core3R Pf V IR) σ) {fi : CFuncInst (core3R Pf V IR)}
    (hl : args.lookup p.1 = some (.func k)) (hs : ArenaField.funcs.get? cfg.store k = some fi)
    (ht : fi.ft = witFt p.2) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.importDefs p sc.frame.types.length).1) cfg sc' cfg ∧
      (∃ new, sc'.frame =
        { sc.frame with types := sc.frame.types ++ new, funcs := sc.frame.funcs ++ [k] }) ∧
      sc'.frame.types.length = (SimpleI.importDefs p sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    p.2.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    p.2.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) p.2.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) p.2.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [importDefs_eq, ← hl₁, ← hl₂]
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) p.2.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3R Pf V IR).Module) p.2.results
          sc₁.frame.types.length).1.head? } = some (witFt p.2) :=
    resolveFuncType_witFt (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hty : (sc₂.frame.types ++ [.func (witFt p.2)])[sc₂.frame.types.length]? =
      some (.func (witFt p.2)) := by simp
  have h₄ := import_run (R := R) (inst := inst) (outer := outer)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (witFt p.2)] } }
    cfg hl hty hs ht
  obtain ⟨new₁, hf₁⟩ := hP₁.2.1
  obtain ⟨new₂, hf₂⟩ := hP₂.2.1
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons h₄ (TRuns.foldlM_nil _ _))), ⟨new₁ ++ new₂ ++ [.func (witFt p.2)], ?_⟩,
    by simp, hP₂.2.2.2.1.trans hP₁.2.2.2.1⟩
  show { sc₂.frame with types := sc₂.frame.types ++ [Types.TypeDef.func (witFt p.2)],
                        funcs := sc₂.frame.funcs ++ [k] } = _
  rw [hf₂, hf₁]
  simp only [List.append_assoc]

end Imports

end Silmaril.Proofs.Wasm.Component.Param.Core3R
