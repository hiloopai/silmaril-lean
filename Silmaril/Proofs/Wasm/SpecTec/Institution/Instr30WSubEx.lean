module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30WSub

/-!
# Instruction typing of the wasm-3.0 script, non-vacuity of `frame` and `sub` under locals and globals

In the context `lgEx = {locals := [i32 (set)], globals := [mut f64]}`:

* `unreachableBotDef`: `unreachable` at `[] -> [BOT]` (a flat type), subsumed to
  `[] -> [ref dFn]`, a non-flat type (`dFn` is an earlier closed defined function type);
* `nopFrameDef`: `nop` framed under the non-flat `[ref dFn]`.

Both are `Instrs_ok` facts of `stepModel BI` in `ctxLGV`, and Core-valid. Core validity and
subtyping of the types are checked by Silmaril's checkers through `decide`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (instrtypeV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Instr30Y (ctxLoc ctxLGV CtxBnd gF64)
open Silmaril.Wasm.SpecTec.Institution.Instr30Z (dFn refDFn tyOk_refDFn)

/-- One set `i32` local. -/
def lI32 : List LocalType := [⟨.set, .num (.int .i32)⟩]

/-- `{locals := [i32], globals := [mut f64]}` is bounded. -/
theorem ctxBnd_ex : CtxBnd lI32 gF64 :=
  ⟨fun lt h => by
    obtain rfl := List.mem_singleton.1 h
    rfl,
   fun gt h => by
    obtain rfl := List.mem_singleton.1 h
    rfl⟩

/-- `BOT` is valid in `{}`. -/
theorem tyOk_bot : TyOk ({} : TypeCtx) (.botv : CValType) := TyOk.check_sound (by decide)

/-- `BOT <: ref dFn` in `{}`. -/
theorem sub_botDef : Sub ({} : TypeCtx) (.botv : CValType) refDFn := Sub.check_sound (by decide)

/-- `[] -> [t]` is valid in the context when `t` is valid in `{}`. -/
theorem itOk_one {t : CValType} (h : TyOk ({} : TypeCtx) t) :
    InstrTypeOk (ctxLoc lI32 gF64) (.plain [] [t]) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ hu => (List.mem_singleton.1 hu) ▸ h,
    fun _ h => absurd h List.not_mem_nil⟩

/-- `unreachable` at `[] -> [BOT]`, subsumed to `[] -> [ref dFn]`. -/
theorem fragOkW_unreachableBotDef : FragOkW lI32 gF64 [.unreachable] (.plain [] [refDFn]) := by
  have h₀ : FragOkW lI32 gF64 [.unreachable] (.plain [] [.botv]) :=
    .instr rfl ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ rfl⟩
      (fun _ => ⟨by simp [Instr30Y.Flat], fun _ h => nomatch h⟩)
      (.parametric (.unreachable (itOk_one tyOk_bot)))
  exact .sub h₀ ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ rfl⟩
    ⟨.nil, .cons sub_botDef .nil, fun _ h => absurd h List.not_mem_nil⟩ (itOk_one tyOk_bot)
    (itOk_one tyOk_refDFn) ⟨by decide, by decide⟩

/-- `nop`, framed under `[ref dFn]`. -/
theorem fragOkW_nopFrameDef : FragOkW lI32 gF64 [.nop] (.plain [refDFn] [refDFn]) :=
  .frame (ts := [refDFn]) (t₁ := []) (t₂ := []) (fun _ ht => (List.mem_singleton.1 ht) ▸ rfl)
    (fun _ ht => (List.mem_singleton.1 ht) ▸ tyOk_refDFn)
    (.instr rfl ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
      (fun _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => nomatch h⟩) (.parametric .nop))

/-- **Non-vacuity of `sub` at a non-flat type under locals and globals.** -/
theorem unreachableBotDef {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (Round4Int.BI P hn host)).D "Instrs_ok" "%|-%:%" []
        (.tuple [ctxLGV lI32 gF64, .list (instrsToV [.unreachable]), instrtypeV (.plain [] [refDFn])]) ∧
      InstrsOk (ctxLoc lI32 gF64) [.unreachable] (.plain [] [refDFn]) :=
  ⟨fragOkW_dd _ ctxBnd_ex fragOkW_unreachableBotDef, fragOkW_sound fragOkW_unreachableBotDef⟩

/-- **Non-vacuity of `frame` at a non-flat type under locals and globals.** -/
theorem nopFrameDef {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (Round4Int.BI P hn host)).D "Instrs_ok" "%|-%:%" []
        (.tuple [ctxLGV lI32 gF64, .list (instrsToV [.nop]), instrtypeV (.plain [refDFn] [refDFn])]) ∧
      InstrsOk (ctxLoc lI32 gF64) [.nop] (.plain [refDFn] [refDFn]) :=
  ⟨fragOkW_dd _ ctxBnd_ex fragOkW_nopFrameDef, fragOkW_sound fragOkW_nopFrameDef⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30W
