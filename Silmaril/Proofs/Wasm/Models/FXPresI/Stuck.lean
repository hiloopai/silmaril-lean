module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Prog
public import Silmaril.Wasm.Execution.Core.Soundness.Preservation

/-!
# `resume_throw` of a consumed continuation is stuck

`StepFXS` (like `StepFX`, `StepFX'`, `StepFXT`, `StepFXR`) has rules for `resume_throw` on a
live continuation and on `ref.null`, but none on a consumed one; `resume` and `cont.bind` trap
there. So the `usedThrow` case of `Final` is a real stuck state, not a weakness of the progress
proof: `stuck_usedThrow` exhibits a typed configuration with no successor.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

theorem stepS_code_ne_nil {c c' : ConfigFX H} (h : StepFXS P host fx c c') : c.code ≠ [] := by
  induction h with
  | core h => simpa using h.code_ne_nil
  | seq _ _ ih => simp [ih]
  | _ => simp [fvals, cvals, cthrowing]

/-- Neither `ref.cont k` nor `resume_throw` steps on its own. -/
theorem stepS_not_single {c c' : ConfigFX H} (h : StepFXS P host fx c c') {k : Nat}
    {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} :
    c.code ≠ [.contRef k] ∧ c.code ≠ [.fx (.resumeThrow ct x hs)] := by
  induction h with
  | core h =>
    constructor <;> intro he <;> simp [List.map_eq_cons_iff] at he
  | @seq s s' K K' f f' vs es es' rest h hne _ =>
    have h₂ : 0 < es.length := List.length_pos_iff.2 (stepS_code_ne_nil h)
    have h₃ : 0 < vs.length + rest.length := by
      rcases hne with hv | hr
      · exact Nat.add_pos_left (List.length_pos_iff.2 hv) _
      · exact Nat.add_pos_right _ (List.length_pos_iff.2 hr)
    constructor <;> intro he <;> have hl := congrArg List.length he <;>
      simp [fvals] at hl <;> omega
  | _ =>
    constructor <;> intro he <;>
      simp [fvals, cvals, cthrowing, List.append_eq_cons_iff] at he

/-- The window of `seq` is a proper part of a two-instruction code. -/
theorem seq_pair {vs : List FVal} {es rest : List AdminFX} {p q : AdminFX} (hes : es ≠ [])
    (hne : vs ≠ [] ∨ rest ≠ []) (he : fvals vs ++ es ++ rest = [p, q]) : es = [p] ∨ es = [q] := by
  rcases vs with _ | ⟨v, vs'⟩
  · rcases es with _ | ⟨e, _ | ⟨e', es''⟩⟩
    · exact absurd rfl hes
    · simp at he
      exact .inl (by rw [he.1])
    · simp at he hne
      exact absurd he.2.2.2 hne
  · rcases vs' with _ | ⟨v', vs''⟩
    · rcases es with _ | ⟨e, es'⟩
      · exact absurd rfl hes
      · simp [fvals] at he
        exact .inr (by rw [he.2.1, he.2.2.1])
    · rcases es with _ | ⟨e, es'⟩
      · exact absurd rfl hes
      · simp [fvals] at he

theorem ne_of_mem {a : AdminFX} {l l' : List AdminFX} (ha : a ∈ l) (hn : a ∉ l') : l ≠ l' :=
  fun he => hn (he ▸ ha)

theorem resumeThrow_ne {K : List (Option ContFX)} {vs : List Val} {k k' : Nat} {C : ContFX}
    {ct ct' : TypeIdx} {x x' : TagIdx} {hs hs' : List OnClause} (hk' : K[k']? = some (some C))
    (hk : K[k]? = some none) :
    cvals vs ++ [.contRef k', .fx (.resumeThrow ct' x' hs')] ≠
      [.contRef k, .fx (.resumeThrow ct x hs)] := by
  intro he
  have he₂ := List.append_inj' (he.trans (List.nil_append _).symm) rfl
  have hkk : k' = k := by simpa using (List.cons.inj he₂.2).1
  rw [hkk, hk] at hk'
  cases hk'

/-- **`resume_throw` of a consumed continuation does not step.** -/
theorem stepS_not_usedThrow {c c' : ConfigFX H} (h : StepFXS P host fx c c') {k : Nat}
    {ct : TypeIdx} {x : TagIdx} {hs : List OnClause} (hk : c.conts[k]? = some none) :
    c.code ≠ [.contRef k, .fx (.resumeThrow ct x hs)] := by
  induction h with
  | core h => exact fun he => by simp [List.map_eq_cons_iff] at he
  | seq h hne _ =>
    exact fun he => (seq_pair (stepS_code_ne_nil h) hne he).elim
      (stepS_not_single h (ct := ct) (x := x) (hs := hs)).1 (stepS_not_single h (k := k)).2
  | resumeThrow hk' => exact resumeThrow_ne hk' hk
  | trapSeq => exact ne_of_mem (a := .core .trap) (by simp) (by simp)
  | throwSeq => exact ne_of_mem (a := .core (.plain .throwRef)) (by simp [cthrowing]) (by simp)
  | resumeThrowNull => exact ne_of_mem (a := .core (.ref .null)) (by simp [cvals, vals]) (by simp)
  | _ => exact fun he => by simpa [fvals, cvals, cthrowing] using congrArg List.getLast? he

/-- The stuck code. -/
def usedThrowCode (ct : TypeIdx) (x : TagIdx) : List AdminFX :=
  [.contRef 0, .fx (.resumeThrow ct x [])]

theorem configOk_usedThrow {m₀ : ModuleInst} {s : Store H} {f : Frame} {ct : TypeIdx}
    {x : TagIdx} {ps rs tr : List CValType} {ta : Nat} {ti : TagInst} (hf : f.module = m₀)
    (hct : contType? m₀ ct = some (ps, rs)) (hx : m₀.tags[x.toNat]? = some ta)
    (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some ([], tr)) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, usedThrowCode ct x⟩ (vtys rs) := by
  have hr : TL (envP m₀) s [ct] [] none [.fx (.resumeThrow ct x [])] [.cont ct] (vtys rs) := by
    exact TL.resumeThrow (E := envP m₀) (pre := []) (hs := []) (as := []) hct hx ht htt
      (by simp) .nil
  have hK : KOk (envP m₀) s [ct] [none] := by
    refine ⟨rfl, fun k ct' h => .inl ?_⟩
    cases k with
    | zero => rfl
    | succ k => simp at h
  exact ⟨hf, hK, TL.contRef (pre := []) (k := 0) rfl hr⟩

/-- **A typed, final configuration with no `StepFXS` step**: `resume_throw` of a consumed
continuation (the WasmFX semantics traps here). -/
theorem stuck_usedThrow {m₀ : ModuleInst} {s : Store H} {f : Frame} {ct : TypeIdx}
    {x : TagIdx} {ps rs tr : List CValType} {ta : Nat} {ti : TagInst} (hf : f.module = m₀)
    (hct : contType? m₀ ct = some (ps, rs)) (hx : m₀.tags[x.toNat]? = some ta)
    (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some ([], tr)) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, usedThrowCode ct x⟩ (vtys rs) ∧
      Final s [none] f (usedThrowCode ct x) ∧
      ¬ ∃ c', StepFXS P host fx ⟨s, [none], f, usedThrowCode ct x⟩ c' := by
  refine ⟨configOk_usedThrow hf hct hx ht htt, ?_, fun ⟨_, h⟩ => ?_⟩
  · simpa [usedThrowCode, cvals, vals, CtxV.plug] using
      Final.usedThrow (s := s) (f := f) (E := .hole) (ws := []) (ct := ct) (x := x) (hs := [])
        (K := [none]) (k := 0) rfl
  · exact stepS_not_usedThrow h (k := 0) rfl rfl

end Silmaril.Proofs.Wasm.Models.FXPresI
