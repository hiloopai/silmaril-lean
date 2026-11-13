module

public import Silmaril.Wasm.Component.Param.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR

/-!
# The IR half of soundness over any engine

`specToIRE`: for every engine `E` and every map `emb` of modules, every terminating outcome of
the canonical-ABI specification over the engine (`exportSpecE E emb c x vs`) is a two-move play
of the IR denotation of `c.toComp` over `engineSem E NumModule emb`. The outer layers (the export
handler, the environment, `atSizes`) are those of `Reference.specToIR`, which are stated for an
arbitrary core semantics. The core layer is `engineStrategy_two`: an export call whose engine
run returns (or traps) is a two-move play of the engine strategy (a call move, then an `oret`
or `otrap` move).

`Simple.soundG`: soundness of the IR over `engineSem E NumModule emb`, for an engine with the
reference-machine half `RefToSpecE`.
-/

public section

namespace Silmaril.Proofs.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Proofs.Wasm.Component.Reference (two den_of_denU denU_call denU_trap envS_of_sem
  irObs_of_answer lowered_types)
open Silmaril.Wasm.Component.Engine (CallResult Status)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)

variable {E : Engine}

/-- **A returned or trapped engine run of an export call is a two-move play** of the engine
strategy. -/
theorem engineStrategy_two {I : EInstance E} {imps exps : CoreIface}
    {q : (sigN exps.length).Op} {a : E.FuncAddr} {xs : List Flat}
    (hq : callee? I.addrs exps q = some (a, xs)) {s' : E.Store Nat} {t' : E.Thread Nat}
    (run : Steps E (I.store, E.invoke a xs) (s', t')) {R : Option Payload}
    (hR : (∃ ys, E.status s' t' = .returned (.values ys) ∧ R = some (.flat ys)) ∨
      (E.status s' t' = .returned .trap ∧ R = none)) :
    two (E := sigN imps.length) q R ∈ engineStrategy E I imps exps := by
  refine Strategy.mem_ofLTS_of_mem_traces ⟨.idle s', ?_⟩
    (Silmaril.Proofs.Wasm.Component.Reference.legal_two q R)
  refine .vis ⟨_, rfl, .call hq⟩ (.vis ⟨_, rfl, ?_⟩ (.nil _))
  rcases hR with ⟨ys, hs, rfl⟩ | ⟨hs, rfl⟩
  · exact .oret run hs
  · exact .otrap run hs

/-- The lowered arguments have the flat parameter types of the lifted core export. -/
theorem flatTyped_of_lower {ft : FuncTy} {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hl : checkLower ft.params vs = some xs) : FlatTyped ft.flat.params xs := by
  have h := lowered_types hl
  have h' : (xs.map (·.type)).map Silmaril.Wasm.Game.ScalarType.num =
      ft.flat.params.map Silmaril.Wasm.Game.ScalarType.num := by
    rw [List.map_map]
    exact h
  exact List.map_injective_iff.mpr (fun _ _ e => Silmaril.Wasm.Game.ScalarType.num.inj e) h'

/-- An engine outcome of export `j` is an IR play. -/
theorem irObs_of_engineOut {emb : NumModule → E.Module} {c : Simple} {j : Fin c.exports.length}
    {nm : String} (hcore : c.mod.exports[c.exports[j].core]? = some (nm, c.exports[j].ty.flat))
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {I : EInstance E}
    (hI : instOf E (emb c.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) = some I)
    {r : Option (List Flat)} (hr : r ∈ engineOut E I c.exports[j].core xs) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (engineSem E NumModule emb))
      ⟨j, by simp [Simple.toComp]⟩ vs (liftOutcome c.exports[j].ty r) := by
  obtain ⟨a, s', t', ha, run, hfin⟩ := hr
  have hlt : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  have hget : c.mod.exports[c.exports[j].core] = (nm, c.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hq : callee? (exps := CoreModule.exports c.mod) I.addrs
      (⟨c.exports[j].core, hlt⟩, .flat xs) = some (a, xs) := by
    have ht : FlatTyped (c.mod.exports[c.exports[j].core]).2.params xs := by
      rw [hget]
      exact flatTyped_of_lower hl
    exact (ite_eq_left ht).trans (by simp only [ha, Option.map_some])
  have h₁ : two (E := CoreIface.sig (CoreModule.imports c.mod))
      (F := CoreIface.sig (CoreModule.exports c.mod)) (⟨c.exports[j].core, hlt⟩, .flat xs)
      (r.map Payload.flat) ∈ (engineSem E NumModule emb).sem c.mod := by
    simp only [engineSem, hI]
    refine engineStrategy_two hq run ?_
    rcases hfin with ⟨ys, hs, rfl⟩ | ⟨hs, rfl⟩
    · exact .inl ⟨ys, hs, rfl⟩
    · exact .inr ⟨hs, rfl⟩
  have h₂ := envS_of_sem (engineSem E NumModule emb) c hlt _ h₁
  exact irObs_of_answer _ _ (den_of_denU (engineSem E NumModule emb) c.toComp _ _ _
    (denU_call (engineSem E NumModule emb) c j.isLt vs hlt hl h₂))

/-- **The IR half of soundness over any engine.** Every terminating outcome of the
canonical-ABI specification over `E` of an export call of a simple component is a play of its
IR denotation over `engineSem E NumModule emb`. -/
theorem specToIRE (emb : NumModule → E.Module) (c : Simple) (hc : c.Good)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (b : Outcome)
    (hb : b ∈ exportSpecE E emb c c.exports[j] vs) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (engineSem E NumModule emb))
      ⟨j, by simp [Simple.toComp]⟩ vs b := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hlt : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  unfold exportSpecE at hb
  split at hb
  next hl =>
    have hb' : b = .traps := hb
    rw [hb']
    exact den_of_denU _ c.toComp _ _ _ (denU_trap _ c j.isLt vs hlt hl)
  next xs hl =>
    rcases hb with ⟨I, hI, r, hr, rfl⟩ | ⟨rfl, _⟩
    · exact irObs_of_engineOut hcore hl hI hr
    · trivial

/-- **Soundness of the IR over the game semantics of an engine**, for an engine with the
reference-machine half against its own specification (`RefToSpecE`). -/
theorem Simple.soundG [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} {emb : NumModule → E.Module}
    (hR : RefToSpecE E ofCore emb) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (engineSem E NumModule emb))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  specToIRE emb c hc j vs b (hR prof c hc hf hi ha _ (List.getElem_mem j.isLt) vs hvs hb)

end Silmaril.Proofs.Wasm.Component.Param
