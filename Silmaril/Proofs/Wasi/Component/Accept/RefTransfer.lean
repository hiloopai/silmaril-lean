module

public import Silmaril.Wasi.Component.Accept.Ref.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Thms

/-! Proofs for `Silmaril.Wasi.Component.Accept.Ref.Transfer.Thms`: acceptance carries over from
`E.withStore I` to `E` given related dispatchers and a related instantiation program. -/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept.RefTransfer

open Silmaril.Wasi.Accept.Ref
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine.Transfer

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I)

theorem cfgRel_initCfg :
    CfgRel S (initCfg (E := E.withStore I)) (initCfg (E := E)) where
  store := by
    show (CStore.empty : CStore E) = mapStore S CStore.empty
    simp only [mapStore, CStore.empty, S.empty]
  host := rfl
  conts := .nil
  ctl := .nil
  pending := rfl
  results := rfl
  cancels := rfl

theorem envLabel_labelOf {es : List (String × FuncId)} {l : Label (E.withStore I) AcceptSt}
    (h : EnvLabel es l) : EnvLabel es (labelOf l : Label E AcceptSt) := by
  rcases l with _ | _ | ev | _ | _ | _
  · trivial
  · trivial
  · rcases ev with _ | _ | _ | _
    · exact h
    · trivial
    · trivial
    · exact h.elim
  · trivial
  · trivial
  · trivial

theorem accepted_of_withStore [∀ a b, Decidable (E.ExternSub a b)] {prof : ProfileKind}
    {c : Syntax.Component E.Module} {w : List UInt8}
    (hd : DispatchRel S (dispatch (E := E.withStore I)) (dispatch (E := E)))
    (hp : ProgRel S (acceptLinkedProg (E := E.withStore I) c) (acceptLinkedProg (E := E) c))
    (h : Accepted (E := E.withStore I) prof c w) : Accepted (E := E) prof c w := by
  obtain ⟨tr₀, m₁, inst, es, tr, m₂, h₁, hh, hobs, h₂, henv, hw⟩ := h
  have hnr₀ : ∀ p, Label.host (.run p) ∉ tr₀ := fun _ => hh _
  have hnr : ∀ p, Label.host (.run p) ∉ tr := fun _ hp => henv _ hp
  obtain ⟨n₁, hs₁, hm₁⟩ := steps_sim hd h₁ (cfgRel_initCfg S)
    (.cons (show LabelRel S (.host (.run (acceptLinkedProg (E := E.withStore I) c)))
      (.host (.run (acceptLinkedProg (E := E) c))) from hp) (forall₂_labelOf S hnr₀))
  obtain ⟨n₂, hs₂, hm₂⟩ := steps_sim hd h₂ hm₁ (forall₂_labelOf S hnr)
  refine ⟨tr₀.map labelOf, n₁, inst, es, tr.map labelOf, n₂, hs₁, ?_, ?_, hs₂, ?_, ?_⟩
  · intro ev hev
    obtain ⟨l, hl, he⟩ := List.mem_map.1 hev
    obtain ⟨ev', rfl⟩ := labelOf_host he
    exact hh ev' hl
  · rw [traceObs_map_labelOf]
    exact hobs
  · intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    exact envLabel_labelOf (henv l' hl')
  · rw [← hm₂.host]
    exact hw

end Silmaril.Proofs.Wasi.Component.Accept.RefTransfer
