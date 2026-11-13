module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Control

/-!
# The invocation of the callback on Core 3.0

`invoke_run`: the Core invocation (`Execution.Core.invoke`, as the component machine calls an
export) of the callback of `P` at its address, on three `i32` arguments, runs, when `bexec CBL`
runs its body to a `return` of `code`, to the value `code`, in a store whose instance holds the
globals and memory `bexec` leaves and in the host state it leaves. The frame is Core's
(`Frame.forCall`: the arguments, then the defaults of the declared locals), the body runs in the
function's label and frame, and the `return` leaves both (`return-label`, `return-frame`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd locals FUEL Prog)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma : Nat}

theorem inst_of_rel {nl : Nat} {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) :
    InstR hb ma cs F.module s.g s.m :=
  ⟨h.glob, h.glt, h.mem, h.imp⟩

theorem rel_of_inst {cs : Store H} {F : Frame} {s : DSt} (hI : InstR hb ma cs F.module s.g s.m)
    (hloc : ∀ i, i < CBL → F.locals[i]? = some (some (Val.i32 (w (s.l i)))) ∧ s.l i < M32) :
    Rel hb CBL ma cs F s :=
  ⟨by decide, hloc, hI.glob, hI.glt, hI.mem, hI.imp⟩

theorem forCall_locals (mi : ModuleInst) (x y z : Nat) (hx : x < M32) (hy : y < M32) (hz : z < M32) :
    ∀ i, i < CBL → (Frame.forCall mi ([x, y, z].map (Val.i32 ∘ w)) cbLocals).locals[i]? =
      some (some (Val.i32 (w (locals [x, y, z] i)))) ∧ locals [x, y, z] i < M32 := by
  have h0 : (0 : Nat) < M32 := by decide
  intro i hi
  match i, hi with
  | 0, _ => exact ⟨rfl, hx⟩
  | 1, _ => exact ⟨rfl, hy⟩
  | 2, _ => exact ⟨rfl, hz⟩
  | 3, _ => exact ⟨rfl, h0⟩
  | 4, _ => exact ⟨rfl, h0⟩
  | 5, _ => exact ⟨rfl, h0⟩
  | 6, _ => exact ⟨rfl, h0⟩
  | n + 7, h => exact absurd h (by unfold CBL; omega)

/-- **The Core invocation of the callback** runs as `bexec` runs its body to `return code`. -/
theorem invoke_run (Pf : Profile) {cs : Store H} {mi : ModuleInst} {P : Prog} {a : Nat}
    {g m : Nat → Nat} {st : Silmaril.Wasm.Component.Streams.Drop.DStore} {rp : Option (Nat × Nat)}
    (hI : InstR hb ma cs mi g m) (hcb : CbAt cs mi P a) {x y z : Nat} (hx : x < M32) (hy : y < M32)
    (hz : z < M32) {code : Nat} {s' : DSt}
    (hrun : bexec CBL P.cb FUEL ⟨g, m, locals [x, y, z], st, rp⟩ = some (.ret code, s')) :
    code < M32 ∧ ∃ cs', InstR hb ma cs' mi s'.g s'.m ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((st, rp), invoke cs a ([x, y, z].map (Val.i32 ∘ w)))
        ((s'.st, s'.rp), ⟨cs', {}, vals [Val.i32 (w code)]⟩) := by
  obtain ⟨fi, ty, ps, rs, hf, hfm, hcode, hexp, hps, hrs⟩ := hcb
  let F' : Frame := Frame.forCall fi.module ([x, y, z].map (Val.i32 ∘ w)) cbLocals
  have hR : Rel hb CBL ma cs F' ⟨g, m, locals [x, y, z], st, rp⟩ :=
    rel_of_inst (by rw [show F'.module = mi from hfm]; exact hI) (forCall_locals _ x y z hx hy hz)
  obtain ⟨-, hv, hres⟩ := stmt_run (Pf := Pf) P.cb FUEL hrun hR
  obtain ⟨cs', F'', j, hR', hF'', hfs, -, r⟩ := hres [.plain .unreachable]
  have hcl : code < M32 := hv code rfl
  refine ⟨hcl, cs', ?_, hfs, ?_⟩
  · have := inst_of_rel hR'
    rwa [hF'', show F'.module = mi from hfm] at this
  · show HSteps Pf hb ma ((st, rp), invoke cs a ([x, y, z].map (Val.i32 ∘ w)))
      ((s'.st, s'.rp), ⟨cs', {}, vals [Val.i32 (w code)]⟩)
    have hinv : invoke cs a ([x, y, z].map (Val.i32 ∘ w)) =
        ⟨cs, {}, vals ([x, y, z].map (Val.i32 ∘ w)) ++ [.ref (.func a), .callRefType fi.type]⟩ := by
      simp [invoke, hf]
    have hn : ([x, y, z].map (Val.i32 ∘ w)).length = ps.length := by simp [hps]
    have r₀ : HSteps Pf hb ma ((st, rp), invoke cs a ([x, y, z].map (Val.i32 ∘ w)))
        ((st, rp), ⟨cs, {}, [.frame 1 F' [.label 1 [] ((sCode P.cb).map Admin.plain ++
          [.plain .unreachable])]]⟩) := by
      rw [hinv]
      have := Step.callRefFunc (P := Pf) (host := noHost) (s := cs) (f := {}) (c := .callRefType fi.type)
        trivial hf hexp hn hcode
      rw [hrs] at this
      simpa [expression, F'] using hcore (hb := hb) (ma := ma) (q := (st, rp)) this
    have r₁ : HSteps Pf hb ma ((st, rp), ⟨cs, {}, [.frame 1 F' [.label 1 [] ((sCode P.cb).map Admin.plain ++
          [.plain .unreachable])]]⟩)
        ((s'.st, s'.rp), ⟨cs', {}, [.frame 1 F'' [.label 1 [] (outCode (.ret code) ++ j ++
          [.plain .unreachable])]]⟩) :=
      hsteps_frame {} 1 (hsteps_label 1 [] r)
    have r₂ : HSteps Pf hb ma ((s'.st, s'.rp), ⟨cs', {}, [.frame 1 F'' [.label 1 [] (outCode (.ret code) ++ j ++
          [.plain .unreachable])]]⟩)
        ((s'.st, s'.rp), ⟨cs', {}, [.frame 1 F'' (vals [Val.i32 (w code)] ++ [.plain .return_])]⟩) := by
      have := Step.returnLabel (P := Pf) (host := noHost) (s := cs') (f := F'') (n := 1) (cont := [])
        (vs := [Val.i32 (w code)]) (rest := j ++ [.plain .unreachable])
      exact hsteps_frame {} 1 (hcore (by simpa [outCode, vals] using this))
    have r₃ : HSteps Pf hb ma ((s'.st, s'.rp), ⟨cs', {}, [.frame 1 F'' (vals [Val.i32 (w code)] ++
          [.plain .return_])]⟩) ((s'.st, s'.rp), ⟨cs', {}, vals [Val.i32 (w code)]⟩) := by
      have := Step.returnFrame (P := Pf) (host := noHost) (s := cs') (f := {}) (fi := F'') (n := 1)
        (vs' := []) (vs := [Val.i32 (w code)]) (rest := []) rfl
      exact hcore (by simpa [vals] using this)
    exact r₀.trans (r₁.trans (r₂.trans r₃))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
