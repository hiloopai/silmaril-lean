module

public import Silmaril.Proofs.Wasm.Models.FXPresI.ProgCtx

/-!
# Progress for `envP`

* `progress_gen`: `TL`-typed code under typed values halts (`Halt`) or steps.
* **`progressI`**: a `ConfigOk` configuration of `envP m₀` is `Final` or steps under `StepFXS`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {s : Store H} {Γ : List TypeIdx}
  {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} {K : List (Option ContFX)}

/-- A Core instruction of the fragment. -/
theorem pg_core {a : Admin} {as : List AdminFX} {pre i₀ o₀ : List FTy} (hc : CtI s a i₀ o₀)
    (ih : PG P host fx m₀ s Γ K as (pre ++ o₀)) :
    PG P host fx m₀ s Γ K (.core a :: as) (pre ++ i₀) := by
  cases hc with
  | @intConst t x =>
    simpa [FVal.toAdmin, Val.toAdmin] using
      pg_push (v := .val (.num ⟨.int t, x⟩)) (m₀ := m₀) (t := intTy t) .intConst ih
  | @refExn a ha =>
    simpa [FVal.toAdmin, Val.toAdmin] using
      pg_push (v := .val (.ref (.exn a))) (m₀ := m₀) (.refExn ha) ih
  | intUnOp => exact pg_win fun _ _ _ h => step_unop h
  | intBinOp => exact pg_win fun _ _ _ h => step_binop h
  | intTestOp => exact pg_win fun _ _ _ h => step_testop h
  | intRelOp => exact pg_win fun _ _ _ h => step_relop h
  | nop =>
    exact pg_win fun _ _ _ h => by
      cases h
      exact ⟨_, .core (cs := [.plain .nop]) (.parametric .nop)⟩
  | drop => exact pg_win fun _ _ _ h => step_drop h
  | unreachable =>
    exact pg_alone fun _ => ⟨_, .core (cs := [.plain .unreachable]) (.parametric .unreachable)⟩
  | trap => exact pg_trap
  | throwRef => exact pg_throwRef

/-- **Progress for `TL`-typed code** under typed values. -/
theorem progress_gen (hK : SlotsOk Γ K) {Ls : List (List FTy)} {R : Option (List FTy)}
    {code : List AdminFX} {i o : List FTy} (h : TL (envP m₀) s Γ Ls R code i o) :
    PG P host fx m₀ s Γ K code i := by
  induction h with
  | nil => exact pg_nil
  | core hc _ _ ih => exact pg_core hc ih
  | br _ _ _ => exact pg_br
  | ret _ _ _ => exact pg_ret
  | contRef hk _ ih => exact pg_push (v := .cont _) ⟨_, hk, rfl⟩ ih
  | contNew _ _ _ => exact pg_contNew
  | contBind h h' _ _ => exact pg_contBind hK h h'
  | resume h hh _ _ => exact pg_resume hK h hh
  | resumeThrow _ hx ht htt hh _ _ => exact pg_resumeThrow hK hx ht htt hh
  | suspend hx ht htt _ _ => exact pg_suspend hx ht htt
  | block hb _ _ _ _ => exact pg_block hb
  | loop hb _ _ _ _ => exact pg_loop hb
  | if_ _ _ _ _ _ _ _ => exact pg_if
  | label hn _ hb _ _ ihb _ => exact pg_label hn hb ihb
  | frame hm hn hb _ ihb _ => exact pg_frame hm hn hb ihb
  | handler hh hb _ ihb _ => exact pg_handler hh hb ihb

/-- At the top level, halting code is final. -/
theorem final_of_halt {f : Frame} {code : List AdminFX} {ts : List FTy}
    (h : Halt s K f code) (hty : TL (envP m₀) s Γ [] none code [] ts) : Final s K f code := by
  cases h with
  | vals vs => exact .vals vs
  | trap => exact .trap
  | throw a => exact .throw a
  | br vs l rest =>
    obtain ⟨_, _, _, hl, -⟩ := br_inv hty
    simp at hl
  | ret vs rest =>
    obtain ⟨_, _, _, hR, -⟩ := ret_inv hty
    cases hR
  | suspend ht hE ha => exact .suspend ht hE ha
  | usedThrow hk => exact .usedThrow hk

/-- **Progress**: a typed configuration of `envP m₀` is final or steps. -/
theorem progressI {c : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (hc : ConfigOk (envP m₀) Γ c ts) :
    Final c.store c.conts c.frame c.code ∨ ∃ c', StepFXS P host fx c c' := by
  obtain ⟨hf, ⟨-, hK⟩, ht⟩ := hc
  have hS : SlotsOk Γ c.conts := fun k ct h =>
    (hK k ct h).imp id fun ⟨C, hC, _⟩ => ⟨C, hC⟩
  rcases progress_gen (P := P) (host := host) (fx := fx) hS ht c.frame [] hf .nil with hH | hst
  · exact .inl (final_of_halt (by simpa [fvals] using hH) ht)
  · exact .inr (by simpa [fvals] using hst)

end Silmaril.Proofs.Wasm.Models.FXPresI
