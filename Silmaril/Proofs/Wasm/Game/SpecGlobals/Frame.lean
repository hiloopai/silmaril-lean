module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Step

/-!
# Host-free steps leave unnamed globals alone

A host-free Core step changes globals only through `global.set`, whose address is named by the
module instance of a frame in the configuration. So if every frame of `c` names only globals in
`G` (`CfgDom G c`), every global outside `G` is unchanged by the step:

* **`step_globals_out`**: `Step P noHost c c' → CfgDom G c → ¬ G b →
  c'.store.globals[b]? = c.store.globals[b]?`;
* `ImgD ρ D`: the image of `D` under `ρ`; `modDom_imgD`, `adminsDom_imgD`, `cfgDom_config`: the
  renamed configuration `config ρ t c` names only globals in `ImgD ρ D` when `c` names only
  globals in `D`.

Used by `StepHostOut` to keep track of the globals of an embedding's target that lie outside the
image of the source. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- The image of the domain `D` under `ρ`. -/
def ImgD (ρ : Nat → Nat) (D : Nat → Prop) : Nat → Prop := fun b => ∃ a, D a ∧ ρ a = b

theorem modDom_imgD {ρ : Nat → Nat} {D : Nat → Prop} {m : ModuleInst} (h : ModDom D m) :
    ModDom (ImgD ρ D) (moduleView ρ m) := by
  refine ⟨fun a ha => ?_, fun e he a ha => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact ⟨b, h.1 b hb, rfl⟩
  · obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    cases hx : e'.addr with
    | global b =>
      simp only [hx, external, ExternAddr.global.injEq] at ha
      exact ⟨b, h.2 e' he' b hx, ha⟩
    | _ => simp only [hx, external, reduceCtorEq] at ha

mutual
theorem adminDom_imgD {ρ : Nat → Nat} {D : Nat → Prop} :
    ∀ a : Admin, AdminDom D a → AdminDom (ImgD ρ D) (admin ρ a)
  | .label _ _ body, h => adminsDom_imgD body h
  | .handler _ _ body, h => adminsDom_imgD body h
  | .frame _ _ body, h => ⟨modDom_imgD h.1, adminsDom_imgD body h.2⟩
  | .plain _, _ => trivial
  | .ref _, _ => trivial
  | .callRefType _, _ => trivial
  | .returnCallRefType _, _ => trivial
  | .trap, _ => trivial

theorem adminsDom_imgD {ρ : Nat → Nat} {D : Nat → Prop} :
    ∀ l : List Admin, AdminsDom D l → AdminsDom (ImgD ρ D) (admins ρ l)
  | [], _ => trivial
  | a :: l, h => ⟨adminDom_imgD a h.1, adminsDom_imgD l h.2⟩
end

theorem cfgDom_config {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H} {c : Config H}
    (h : CfgDom D c) : CfgDom (ImgD ρ D) (config ρ t c) :=
  ⟨modDom_imgD h.1, adminsDom_imgD c.code h.2⟩

theorem variable_globals_out {G : Nat → Prop} {s s' : Store H} {f f' : Frame}
    {code out : List Admin} (hv : VariableStep ⟨s, f, code⟩ ⟨s', f', out⟩)
    (hm : ModDom G f.module) {b : Nat} (hb : ¬ G b) : s'.globals[b]? = s.globals[b]? := by
  cases hv with
  | globalSet hg =>
    rename_i x a g v
    simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
    obtain ⟨a', ha', g', -, he⟩ := hg
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have hne : b ≠ a' := fun hba => hb (hba ▸ hm.1 a' (List.mem_of_getElem? ha'))
    simp [Store.setGlobal, Ne.symm hne]
  | _ => rfl

/-- **A host-free step changes no global outside the globals its frames name.** -/
theorem step_globals_out {c c' : Config H} (h : Step P noHost c c') :
    ∀ {G : Nat → Prop}, CfgDom G c → ∀ {b : Nat}, ¬ G b →
      c'.store.globals[b]? = c.store.globals[b]? := by
  induction h
  all_goals intro G dom b hb
  case «variable» c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact variable_globals_out hv dom.1 hb
  case table hv => cases hv <;> rfl
  case memory hv => cases hv <;> rfl
  case reference hv => cases hv <;> rfl
  case aggregate hv => cases hv <;> rfl
  case ctxtInstrs ih =>
    have hd := dom.2
    simp only [adminsDom_append, adminsDom_vals, true_and] at hd
    exact ih ⟨dom.1, hd.1⟩ hb
  case ctxtLabel ih => exact ih ⟨dom.1, dom.2.1⟩ hb
  case ctxtHandler ih => exact ih ⟨dom.1, dom.2.1⟩ hb
  case ctxtFrame ih => exact ih dom.2.1 hb
  case callRefHost hhost => exact hhost.elim
  all_goals rfl

end Silmaril.Proofs.Wasm.Game.SpecGlobals
