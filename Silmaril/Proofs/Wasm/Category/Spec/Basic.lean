module

public import Silmaril.Wasm.Category.Spec.Defs

@[expose] public section

/-!
# Sessions, spec instantiation and closed games: proofs

* `denoteSpec_obs`: the closed game of a spec instance observes exactly its Core 3.0
  behaviours (from `IsSpecInstance.adequacy_inst` and `adequacy_after_inst`);
* `moduleObs_of_inst`, `moduleObs_of_call`: an instantiation behaviour of the spec's
  configuration of `$instantiate` is a session observation with the empty script, and a
  behaviour of an export call after instantiation is one with a one-call script (or, if the
  call is ill-typed in the session store, the session stops);
* `envSession_of_spec`: every spec observation of a module is matched by an
  environment-session observation of it.

Summary in `Silmaril.Wasm.Category.Spec.Thms`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game
  Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

/-- How an environment-session observation matches a spec observation: the instantiation
behaviour `b` is the session `[b]` with the empty script; the behaviour `b` of the call of the
export named `x` is the session `[returns [], b]` of the one-call script, or `[returns []]` if
the session stops there (ill-typed call). The store and imports of the session are not
recorded by the spec observation. -/
def SessionMatch (e : EnvObs) : SpecObs → Prop
  | .inst ts K b => ∃ s xas, e = ⟨ts, K, .session s xas [] [b]⟩
  | .call S K x f b => ∃ s xas,
      e = ⟨S.1, K, .session s xas [(x, f.2.1)] [.returns [], b]⟩ ∨
      e = ⟨S.1, K, .session s xas [(x, f.2.1)] [.returns []]⟩

/-- **Adequacy of the closed game of a spec instance**, every profile. -/
theorem denoteSpec_obs (P : Profile) {m : Module} {mt : CModuleType} {I : ScalarInstance}
    {c₀ : Config Nat} (h : IsSpecInstance m mt I c₀) :
    (denoteSpec P I c₀).obs = specObs P I c₀ := by
  ext o
  constructor
  · rintro (⟨K, b, rfl, hK, hb⟩ | ⟨K, x, f, b, rfl, hK, hx, hb⟩)
    · have e : Silmaril.Wasm.Game.instObs (I.closedSpec P c₀ K) =
          behavioursOf P (hostOf I.imports K) c₀ := h.adequacy_inst P K hK
      have hb' : b ∈ behavioursOf P (hostOf I.imports K) c₀ := e ▸ hb
      exact Or.inl ⟨K, b, rfl, hK, hb'⟩
    · have e := h.adequacy_after_inst P K hK f
      have hb' : b ∈ {b | ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' ∧
          b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1} := e ▸ hb
      exact Or.inr ⟨K, x, f, b, rfl, hK, hx, hb'⟩
  · rintro (⟨K, b, rfl, hK, hb⟩ | ⟨K, x, f, b, rfl, hK, hx, hb⟩)
    · have e : Silmaril.Wasm.Game.instObs (I.closedSpec P c₀ K) =
          behavioursOf P (hostOf I.imports K) c₀ := h.adequacy_inst P K hK
      have hb' : b ∈ Silmaril.Wasm.Game.instObs (I.closedSpec P c₀ K) := e ▸ hb
      exact Or.inl ⟨K, b, rfl, hK, hb'⟩
    · have e := h.adequacy_after_inst P K hK f
      have hb' : b ∈ obsAfterInst (I.closedSpec P c₀ K) f := e ▸ hb
      exact Or.inr ⟨K, x, f, b, rfl, hK, hx, hb'⟩

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {xas : List ExternAddr}
  {m : Module} {c₀ : Config Nat}

/-- An instantiation behaviour is a session observation with the empty script. -/
theorem moduleObs_of_inst (hc : Instantiate P host s m xas c₀) {b : Behaviour Val}
    (hb : b ∈ behavioursOf P host c₀) : [b] ∈ moduleObs P host s xas m [] := by
  rcases hb with ⟨c', r, hst, hcode, rfl⟩ | ⟨rfl, hd⟩
  · by_cases hr : r = .values []
    · subst hr
      have hcode' : c'.code = [] := hcode
      exact ⟨c₀, hc, Or.inl ⟨c', [], hst, hcode', .nil, rfl⟩⟩
    · exact ⟨c₀, hc, Or.inr (Or.inl ⟨c', r, hst, hcode, hr, rfl⟩)⟩
  · exact ⟨c₀, hc, Or.inr (Or.inr ⟨hd, rfl⟩)⟩

/-- A behaviour of an export call after instantiation is a session observation of the one-call
script, or the session stops at an ill-typed call. -/
theorem moduleObs_of_call (hc : Instantiate P host s m xas c₀) {s' : Store Nat}
    (hrun : InstantiatesTo P host c₀ s') {x : String} {a : Nat}
    (ha : exportFunc? c₀.frame.module x = some a) {vs : List Val} {b : Behaviour Val}
    (hb : b ∈ behaviours P host s' a vs) :
    [.returns [], b] ∈ moduleObs P host s xas m [(x, vs)] ∨
      [.returns []] ∈ moduleObs P host s xas m [(x, vs)] := by
  obtain ⟨c', hst, hcode, rfl⟩ := hrun
  have hcode' : c'.code = [] := hcode
  by_cases hok : InvokeOk c'.store a vs
  · left
    rcases hb with ⟨d, r, hd, hdc, rfl⟩ | ⟨rfl, hdv⟩
    · exact ⟨c₀, hc, Or.inl ⟨c', [r.toBehaviour], hst, hcode', .done ha hok hd hdc .nil, rfl⟩⟩
    · exact ⟨c₀, hc, Or.inl ⟨c', [.diverges], hst, hcode', .diverge ha hok hdv, rfl⟩⟩
  · right
    have hstop : ∀ a', exportFunc? c₀.frame.module x = some a' → ¬ InvokeOk c'.store a' vs := by
      intro a' ha'
      have e : a' = a := Option.some.inj (ha'.symm.trans ha)
      exact e ▸ hok
    exact ⟨c₀, hc, Or.inl ⟨c', [], hst, hcode', .stop hstop, rfl⟩⟩

/-- The export name resolved by `exportIndex?` resolves to the export's address. -/
theorem exportFunc?_of_exportIndex? {I : ScalarInstance} {mi : ModuleInst} {x : String}
    {j : Fin I.exports.length} (h : exportIndex? I mi x = some j) :
    exportFunc? mi x = some (I.addr j) := by
  unfold exportIndex? at h
  split at h
  · rename_i hex
    have e : hex.choose = j := Option.some.inj h
    exact e ▸ hex.choose_spec
  · exact absurd h (by simp)

/-- **Every spec observation is matched by an environment-session observation.** -/
theorem envSession_of_spec {mt : CModuleType} {I : ScalarInstance}
    (h : IsSpecInstance m mt I c₀) {o : SpecObs} (ho : o ∈ specObs P I c₀) :
    ∃ e ∈ (envSession P).beh m, SessionMatch e o := by
  have hs : StoreOk (importStore (CExternType.funcs mt.imports)) := h.toAt.storeOk
  rcases ho with ⟨K, b, rfl, -, hb⟩ | ⟨K, x, f, b, rfl, -, hx, s', hrun, hb⟩
  · have hc := h.instantiate P (hostOf I.imports K)
    have hm := moduleObs_of_inst hc hb
    exact ⟨⟨I.imports, K, .session _ _ [] [b]⟩, ⟨hs, hm⟩, _, _, rfl⟩
  · have hc := h.instantiate P (hostOf I.imports K)
    have ha := exportFunc?_of_exportIndex? hx
    rcases moduleObs_of_call hc hrun ha hb with hm | hm
    · exact ⟨⟨I.imports, K, .session _ _ [(x, f.2.1)] [.returns [], b]⟩, ⟨hs, hm⟩, _, _,
        Or.inl rfl⟩
    · exact ⟨⟨I.imports, K, .session _ _ [(x, f.2.1)] [.returns []]⟩, ⟨hs, hm⟩, _, _,
        Or.inr rfl⟩

end Silmaril.Wasm.Category
