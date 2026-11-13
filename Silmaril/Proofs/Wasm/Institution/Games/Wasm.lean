module

public import Silmaril.Proofs.Wasm.Institution.Games.Basic

@[expose] public section

/-!
# Adequacy of the Wasm reduction for two-move plays

`wasmRed P host w` (`Silmaril.Wasm.Institution.Games.Defs`) runs one export invocation per
question with Core 3.0 `Step`. For a finite behaviour `b`, the play "invoke `x` on `vs`, answer
`b`" is in its strategy iff `b` is a behaviour of that invocation (`mem_wasmRed_iff`). Hence game
refinement of instantiated modules implies inclusion of their finite single-invocation behaviours
(`finite_beh_of_le`).
-/

namespace Silmaril.Wasm.Institution.Games

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)

theorem wasmRed_rtg_some {w : Inst H} {q} {d : Config H} {c : Option (Config H)}
    (h : Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w) q) (some d) c) :
    ∃ d', c = some d' ∧ Steps P host d d' := by
  induction h with
  | refl => exact ⟨d, rfl, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨d₁, rfl, hd₁⟩ := ih
    obtain ⟨e, e', he, rfl, hs⟩ := hstep
    cases he
    exact ⟨e', rfl, hd₁.tail hs⟩

theorem wasmRed_rtg_none {w : Inst H} {q} {c : Option (Config H)}
    (h : Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w) q) none c) :
    c = none := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨e, e', he, -, -⟩ := hstep
    subst ih
    cases he

theorem wasmRed_rtg_of_steps {w : Inst H} {q} {d d' : Config H} (h : Steps P host d d') :
    Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w) q) (some d)
      (some d') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨_, _, rfl, rfl, hs⟩

/-- A finite behaviour answered after reducing the start configuration of an invocation is a
behaviour of that invocation. -/
private theorem beh_of_reduces (w : Inst H) (x : String) (vs : List Val) {b : Behaviour Val}
    {c' : Option (Config H)}
    (hc' : Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w)
      ⟨(x, vs), trivial⟩) ((Binaryen.exportFunc? w.2 x).map fun a => invoke w.1 a vs) c')
    (hd : (wasmRed P host w).done (q := ⟨(x, vs), trivial⟩) c' b) :
    b ∈ (instEntry P host).beh w x vs := by
  obtain ⟨d, res, hcd, hcode, hb⟩ := hd
  cases ha : Binaryen.exportFunc? w.2 x with
  | none =>
    have hnone : Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w)
        ⟨(x, vs), trivial⟩) none c' := by simpa only [ha, Option.map_none] using hc'
    have hc'none : c' = none := wasmRed_rtg_none P host hnone
    exact nomatch hc'none.symm.trans hcd
  | some a =>
    have hsome : Relation.ReflTransGen (@Silmaril.Games.Reduction.step _ _ (wasmRed P host w)
        ⟨(x, vs), trivial⟩) (some (invoke w.1 a vs)) c' := by
      simpa only [ha, Option.map_some] using hc'
    obtain ⟨d', hd', hs⟩ := wasmRed_rtg_some P host hsome
    have hdd : d' = d := Option.some.inj (hd'.symm.trans hcd)
    have hmem : res.toBehaviour ∈ behaviours P host w.1 a vs :=
      mem_behavioursOf (hdd ▸ hs) hcode
    exact ⟨a, ha, hb ▸ hmem⟩

/-- **Two-move adequacy**: for a non-divergent behaviour `b`, the play "invoke `x` on `vs`,
answer `b`" belongs to the strategy of `wasmRed P host w` iff `b` is a behaviour of that
invocation in silmaril's Core semantics. -/
theorem mem_wasmRed_iff (w : Inst H) (x : String) (vs : List Val) {b : Behaviour Val}
    (hb : b ≠ .diverges) :
    [.inr (.ask ⟨(x, vs), trivial⟩), .inr (.ans ⟨(x, vs), trivial⟩ b)] ∈
        Silmaril.Games.Strategy.ofReduction (wasmRed P host w) ↔
      b ∈ (instEntry P host).beh w x vs := by
  refine (mem_ofReduction_ask_ans Silmaril.Games.Sig.empty).trans
    ⟨fun ⟨_, hc', hd⟩ => beh_of_reduces P host w x vs hc' hd, ?_⟩
  rintro ⟨a, ha, hmem⟩
  rcases hmem with ⟨c', res, hs, hcode, hres⟩ | ⟨hdiv, -⟩
  · refine ⟨some c', ?_, c', res, rfl, hcode, hres⟩
    show Relation.ReflTransGen _ ((Binaryen.exportFunc? w.2 x).map fun a => invoke w.1 a vs) _
    rw [ha]
    exact wasmRed_rtg_of_steps P host hs
  · exact absurd hdiv hb

/-- **Game refinement implies single-invocation refinement on finite behaviours**: if the
strategy of `w` refines that of `w'`, every non-divergent behaviour of every export invocation
of `w` is one of `w'`. (Divergence is not observed by the games of `Silmaril.Games`.) -/
theorem finite_beh_of_le {w w' : Inst H}
    (h : Silmaril.Games.Strategy.ofReduction (wasmRed P host w) ≤
      Silmaril.Games.Strategy.ofReduction (wasmRed P host w'))
    (x : String) (vs : List Val) {b : Behaviour Val} (hb : b ≠ .diverges)
    (hmem : b ∈ (instEntry P host).beh w x vs) : b ∈ (instEntry P host).beh w' x vs :=
  (mem_wasmRed_iff P host w' x vs hb).1 (h ((mem_wasmRed_iff P host w x vs hb).2 hmem))

end Silmaril.Wasm.Institution.Games
