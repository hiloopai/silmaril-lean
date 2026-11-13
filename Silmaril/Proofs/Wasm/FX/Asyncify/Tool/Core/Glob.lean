module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Pure

/-!
# `global.get` and `global.set` of the frame machine as Core 3.0 steps

`run_gget`, `run_gset`: from a store whose globals hold the machine's (`GlobalsAre`), Core runs
the instruction to the machine's result, and the new store holds the new globals.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool

variable {H : Type} {Pf : Profile} {host : HostSemantics H}

theorem gidx_val (g : GlobalIdx) : gidx g.value.val = g := by
  cases g with
  | mk v => exact congrArg Idx.mk (Fin.ext (Nat.mod_eq_of_lt v.isLt))

theorem global?_frame (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (ls : List W)
    (x : GlobalIdx) : s.global? (localsF f ls) x = s.global? f x := rfl

theorem globalsAre_frame {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {gs : List W}
    (ls : List W) (h : GlobalsAre s f gs) : GlobalsAre s (localsF f ls) gs := h

/-- The global of index `x` after `setGlobal a v`. -/
theorem global?_setGlobal (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (a : Nat)
    (v : Val) (x : GlobalIdx) :
    (s.setGlobal a v).global? f x =
      (s.global? f x).map fun p => (p.1, if p.1 = a then { p.2 with value := v } else p.2) := by
  unfold Store.global? Store.setGlobal
  cases hx : f.module.globals[x.toNat]? with
  | none => rfl
  | some b =>
    show (Option.bind ((s.globals.modify a fun g => { g with value := v })[b]?) fun gi =>
      some (b, gi)) = Option.map _ (Option.bind s.globals[b]? fun gi => some (b, gi))
    rw [List.getElem?_modify]
    by_cases hb : a = b
    · subst hb
      cases s.globals[a]? <;> simp
    · have hb' : b ≠ a := fun h => hb h.symm
      cases s.globals[b]? <;> simp [hb, hb']

theorem run_gget (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops gs : List W} (hg : GlobalsAre s f gs) (g : GlobalIdx) {v : W}
    (hv : gs[g.value.val]? = some v) :
    Execution.Core.Steps Pf host ⟨s, localsF f ls, stackA ops ++ .plain (.globalGet g) :: rest⟩
      ⟨s, localsF f ls, stackA (v :: ops) ++ rest⟩ := by
  obtain ⟨hlt, hv'⟩ := List.getElem?_eq_some_iff.1 hv
  obtain ⟨a, gi, hgl, hval, -⟩ := hg.2.1 g.value.val hlt
  rw [gidx_val] at hgl
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.variable (.globalGet (s := s) (f := localsF f ls) hgl))
  rw [hval, hv'] at hs
  rw [stackA_cons]
  exact one (by simpa [stackA] using hs)

/-- The global values after `global.set`. -/
theorem globalsAre_set_val {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {gs : List W}
    (hg : GlobalsAre s f gs) {g a : Nat} {gi : GlobalInst} (hgl : s.global? f (gidx g) = some (a, gi))
    (hlt : g < gs.length) (v : W) (g' : Nat) (hg' : g' < gs.length) :
    ∃ a' gi', (s.setGlobal a (Val.i32 v)).global? f (gidx g') = some (a', gi') ∧
      gi'.value = Val.i32 ((gs.set g v)[g']'(by simpa using hg')) ∧ gi'.type.mutability = .var := by
  obtain ⟨a', gi', hgl', hval', hmut'⟩ := hg.2.1 g' hg'
  by_cases he : a' = a
  · have hgg : g' = g := hg.2.2 g' g a' a gi' gi hgl' hgl hg' hlt he
    refine ⟨a', { gi' with value := Val.i32 v }, ?_, by simp [hgg], hmut'⟩
    rw [global?_setGlobal, hgl']
    simp [he]
  · have hne : g' ≠ g := fun h => he (by rw [h, hgl] at hgl'; cases hgl'; rfl)
    refine ⟨a', gi', ?_, ?_, hmut'⟩
    · rw [global?_setGlobal, hgl']
      simp [he]
    · rw [hval']
      simp [Ne.symm hne]

/-- The addresses of the globals after `global.set`. -/
theorem globalsAre_set_inj {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {gs : List W}
    (hg : GlobalsAre s f gs) (a : Nat) (v : Val) (g₁ g₂ a₁ a₂ : Nat) (gi₁ gi₂ : GlobalInst)
    (h₁ : (s.setGlobal a v).global? f (gidx g₁) = some (a₁, gi₁))
    (h₂ : (s.setGlobal a v).global? f (gidx g₂) = some (a₂, gi₂))
    (hl₁ : g₁ < gs.length) (hl₂ : g₂ < gs.length) (ha : a₁ = a₂) : g₁ = g₂ := by
  obtain ⟨⟨a₁', gi₁'⟩, h₁', he₁⟩ := Option.map_eq_some_iff.1 ((global?_setGlobal s f a v _).symm.trans h₁)
  obtain ⟨⟨a₂', gi₂'⟩, h₂', he₂⟩ := Option.map_eq_some_iff.1 ((global?_setGlobal s f a v _).symm.trans h₂)
  have e1 : a₁' = a₁ := congrArg Prod.fst he₁
  have e2 : a₂' = a₂ := congrArg Prod.fst he₂
  exact hg.2.2 g₁ g₂ a₁' a₂' gi₁' gi₂' h₁' h₂' hl₁ hl₂ (by rw [e1, e2, ha])

/-- The globals after `global.set`. -/
theorem globalsAre_set {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {gs : List W}
    (hg : GlobalsAre s f gs) {g a : Nat} {gi : GlobalInst} (hgl : s.global? f (gidx g) = some (a, gi))
    (hlt : g < gs.length) (v : W) : GlobalsAre (s.setGlobal a (Val.i32 v)) f (gs.set g v) :=
  ⟨by simpa using hg.1, fun g' hg' => globalsAre_set_val hg hgl hlt v g' (by simpa using hg'),
    fun g₁ g₂ a₁ a₂ gi₁ gi₂ h₁ h₂ hl₁ hl₂ ha =>
      globalsAre_set_inj hg a _ g₁ g₂ a₁ a₂ gi₁ gi₂ h₁ h₂ (by simpa using hl₁) (by simpa using hl₂) ha⟩

theorem run_gset (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops gs : List W} (hg : GlobalsAre s f gs) (g : GlobalIdx) (v : W)
    (hlt : g.value.val < gs.length) :
    ∃ a gi, s.global? f g = some (a, gi) ∧
      GlobalsAre (s.setGlobal a (Val.i32 v)) f (gs.set g.value.val v) ∧
      Execution.Core.Steps Pf host
        ⟨s, localsF f ls, stackA (v :: ops) ++ .plain (.globalSet g) :: rest⟩
        ⟨s.setGlobal a (Val.i32 v), localsF f ls, stackA ops ++ rest⟩ := by
  obtain ⟨a, gi, hgl, -, -⟩ := hg.2.1 g.value.val hlt
  rw [gidx_val] at hgl
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.variable (.globalSet (s := s) (f := localsF f ls) (v := Val.i32 v) hgl))
  refine ⟨a, gi, hgl, globalsAre_set hg (by rw [gidx_val]; exact hgl) hlt v, ?_⟩
  rw [stackA_cons]
  exact Relation.ReflTransGen.single (by simpa [stackA] using hs)

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core
