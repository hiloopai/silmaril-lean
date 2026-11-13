module

public import Silmaril.Wasm.Models.FXBind.Defs
public import Silmaril.Wasm.Models.FXLower.Thms

/-!
# Inverting `cont.bind` (no host calls)

`step_contBind`: a step of `cvals W ++ ref.cont n :: cont.bind :: T` is `cont.bind` (or a trap on
a consumed continuation) with *some* split `W = W₁ ++ W₂`: `W₂` is bound into the new
continuation, `W₁` stays on the stack. The reduction is untyped, so every split occurs. The
proof follows `step_resume` (induction on `StepFX`, `seq` by `seq_split`, the other rules by
comparing first non-values).

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXBind
open Silmaril.Proofs.Wasm.Models.FXLower (seq_split no_step_cvals cvals_append_cons_inj
  core_ne_cvals_cons invoke_ne cvals_append)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The outcomes of a step of `cvals W ++ ref.cont n :: T` where `T` starts with `cont.bind`. -/
def BindRes (s : Store H) (K : List (Option ContFX)) (f : Frame) (ct ct' : TypeIdx)
    (W : List Val) (n : Nat) (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ T', T = .fx (.contBind ct ct') :: T' ∧ ∃ W₁ W₂, W = W₁ ++ W₂ ∧
    ((∃ C, K[n]? = some (some C) ∧
        y = ⟨s, K.set n none ++ [some (bindK C W₂)], f, cvals W₁ ++ .contRef K.length :: T'⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, cvals W₁ ++ .core .trap :: T'⟩))

/-- `BindRes` is closed under `ctxt-instrs`. -/
theorem bindRes_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {ct ct' : TypeIdx} {W : List Val} {n : Nat} {T es' : List AdminFX}
    (vs : List Val) (rest : List AdminFX) (h : BindRes s K f ct ct' W n T ⟨s', K', f', es'⟩) :
    BindRes s K f ct ct' (vs ++ W) n (T ++ rest) ⟨s', K', f', cvals vs ++ es' ++ rest⟩ := by
  obtain ⟨T', rfl, W₁, W₂, rfl, h⟩ := h
  refine ⟨T' ++ rest, rfl, vs ++ W₁, W₂, by simp, ?_⟩
  rcases h with ⟨C, hk, hy⟩ | ⟨hk, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨C, hk, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hk, by simp⟩

/-- The head condition of `step_contBind`. -/
abbrev HeadBind (ct ct' : TypeIdx) (T : List AdminFX) : Prop :=
  T.head? = none ∨ T.head? = some (.fx (.contBind ct ct'))

theorem headBind_prefix {ct ct' : TypeIdx} {T₁ rest : List AdminFX}
    (h : HeadBind ct ct' (T₁ ++ rest)) : HeadBind ct ct' T₁ := by
  cases T₁ with
  | nil => exact Or.inl rfl
  | cons a T₁ => simpa [HeadBind] using h

/-- The `contBind` and `contBindUsed` cases: the rule's operands are `W`. -/
theorem bind_inj {vs W : List Val} {k n : Nat} {ct ct' c₁ c₂ : TypeIdx} {T : List AdminFX}
    (hT : HeadBind ct ct' T)
    (hx : cvals vs ++ [.contRef k, .fx (.contBind c₁ c₂)] = cvals W ++ .contRef n :: T) :
    vs = W ∧ k = n ∧ c₁ = ct ∧ c₂ = ct' ∧ T = [.fx (.contBind ct ct')] := by
  obtain ⟨hW, hk, hT'⟩ := cvals_append_cons_inj hx rfl rfl
  have hk' : k = n := by simpa using hk
  rw [← hT'] at hT
  rcases hT with hT | hT
  · exact absurd hT (by simp)
  · simp only [List.head?_cons, Option.some.injEq, AdminFX.fx.injEq, FXInstr.contBind.injEq]
      at hT
    obtain ⟨rfl, rfl⟩ := hT
    exact ⟨hW, hk', rfl, rfl, hT'.symm⟩

/-- The other rules on `ref.cont`: the next instruction is not `cont.bind`. -/
theorem contRef_other {vs W : List Val} {k n : Nat} {ct ct' : TypeIdx} {T : List AdminFX}
    {i : FXInstr} (hT : HeadBind ct ct' T) (hi : ∀ c₁ c₂, i ≠ .contBind c₁ c₂)
    (hx : cvals vs ++ [.contRef k, .fx i] = cvals W ++ .contRef n :: T) : False := by
  obtain ⟨-, -, hT'⟩ := cvals_append_cons_inj hx rfl rfl
  have h1 : HeadBind ct ct' [.fx i] := hT'.symm ▸ hT
  rcases h1 with h1 | h1
  · exact absurd h1 (by simp)
  · exact hi ct ct' (by simpa using h1)

/-- **Inversion at `cont.bind`.** -/
theorem step_contBind {x y : ConfigFX H} (h : StepFX P noHost fx x y) :
    ∀ W n ct ct' T, HeadBind ct ct' T → x.code = cvals W ++ .contRef n :: T →
      BindRes x.store x.conts x.frame ct ct' W n T y := by
  induction h with
  | core _ => exact fun W n ct ct' T _ hx => absurd hx (core_ne_cvals_cons rfl)
  | seq h _ ih =>
    intro W n ct ct' T hT hx
    rcases seq_split rfl hx with ⟨V, hV⟩ | ⟨W₂, T₁, rfl, hes, rfl⟩
    · exact (no_step_cvals h V hV).elim
    · exact bindRes_seq _ _ (ih W₂ n ct ct' T₁ (headBind_prefix hT) hes)
  | @contBind s K f vs k C _ _ hk =>
    intro W n ct ct' T hT hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj hT hx
    exact ⟨[], rfl, [], vs, rfl, Or.inl ⟨C, hk, rfl⟩⟩
  | @contBindUsed s K f vs k _ _ hk =>
    intro W n ct ct' T hT hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj hT hx
    exact ⟨[], rfl, [], vs, rfl, Or.inr ⟨hk, rfl⟩⟩
  | resume | resumeUsed | resumeThrow =>
    exact fun W n ct ct' T hT hx => (contRef_other hT (by simp) hx).elim
  | invoke hc => exact fun W n ct ct' T _ hx => absurd hx (invoke_ne hc (by simp))
  | _ => intro W n ct ct' T _ hx; fnvX_absurd hx

end Silmaril.Proofs.Wasm.Models.FXBind
